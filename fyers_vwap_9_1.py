# -*- coding: utf-8 -*-
import pandas as pd
import numpy as np
import time
import logging
from datetime import datetime, timedelta
from typing import Dict, List, Tuple, Optional
import warnings
from fyers_apiv3 import fyersModel
from functools import wraps
import pytz
import os
import threading
import signal
warnings.filterwarnings('ignore')

# Configure logging
logging.basicConfig(
    level=logging.DEBUG,
    format='%(asctime)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s',
    handlers=[
        logging.FileHandler(f'nifty_trader_{datetime.now().strftime("%Y%m%d")}.log'),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Rate limiting decorator to prevent API rate limit violations
def rate_limit_api(calls_per_second=0.8):  # Conservative limit
    """Decorator to rate limit API calls"""
    def decorator(func):
        last_called = [0.0]
        
        @wraps(func)
        def wrapper(*args, **kwargs):
            elapsed = time.time() - last_called[0]
            left_to_wait = 1.0 / calls_per_second - elapsed
            if left_to_wait > 0:
                logger.debug(f"Rate limiting {func.__name__}: waiting {left_to_wait:.2f}s")
                time.sleep(left_to_wait)
            logger.debug(f"Executing rate-limited API call: {func.__name__}")
            ret = func(*args, **kwargs)
            last_called[0] = time.time()
            logger.debug(f"Rate-limited API call completed: {func.__name__}")
            return ret
        return wrapper
    return decorator

# Timeout decorator to prevent API calls from hanging indefinitely
def api_timeout(timeout_seconds=10):
    """Decorator to add timeout to API calls"""
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            result = [None]
            exception = [None]
            
            def target():
                try:
                    result[0] = func(*args, **kwargs)
                except Exception as e:
                    exception[0] = e
            
            thread = threading.Thread(target=target)
            thread.daemon = True
            thread.start()
            thread.join(timeout_seconds)
            
            if thread.is_alive():
                logger.error(f"API call {func.__name__} timed out after {timeout_seconds}s")
                # Force thread cleanup (not ideal but necessary for hanging API calls)
                return None
            
            if exception[0]:
                raise exception[0]
            
            return result[0]
        return wrapper
    return decorator

class NiftyOptionsTrader:
    def __init__(self, client_id: str = None, access_token: str = None, auto_load_config: bool = True):
        logger.info("Initializing NiftyOptionsTrader...")
        
        # Initialize timezone first (needed by _load_ui_overrides)
        self.ist_timezone = pytz.timezone('Asia/Kolkata')
        
        # Auto-load configuration from UI files if enabled
        if auto_load_config:
            logger.info("Auto-loading configuration from UI files...")
            config = self._load_ui_config()
            client_id = config.get('client_id')
            access_token = config.get('access_token')
            
            # Load other overrides from UI files
            self._load_ui_overrides(config)
        
        logger.info(f"Client ID provided: {'Yes' if client_id else 'No'}")
        logger.info(f"Access Token provided: {'Yes' if access_token else 'No'}")
        
        # Fyers API configuration
        self.client_id = client_id
        self.access_token = access_token
        self.fyers = None
        
        if client_id and access_token:
            self.fyers = fyersModel.FyersModel(client_id=client_id, token=access_token)
            logger.info("Fyers API connection established")
        
        self.current_nifty_price = None
        self.current_atm_strike = None
        self.vwap_data = []
        self.combined_premium_data = []
        self.current_vwap = None
        self.current_market_vwap = None  # For display purposes only - always calculated regardless of override
        self.last_candle_close = None
        self.positions = {"CE": None, "PE": None}
        self.long_positions = {"CE": None, "PE": None}  # Track long positions from enhanced strategy
        self.is_running = False
        
        # Trading safety flags
        self.trading_disabled = False  # Flag to disable trading after critical errors
        self.trading_disabled_reason = None  # Reason why trading was disabled
        
        # Stop-loss management - simplified to VWAP only
        self.sl_orders = {"CE": None, "PE": None}  # Track SL order IDs
        self.last_sl_management_time = None  # Track last SL management time
        
        # VWAP vs Current Price difference tracking
        self.max_vwap_diff_during_order = 0.0  # Maximum difference between VWAP and current price during order lifetime
        self.vwap_diff_threshold_percent = 1.5  # Exit threshold: if max VWAP diff > 1.5%, square off both legs
        self.order_start_time = None  # When the current order was placed
        self.vwap_diff_tracking_enabled = False  # Flag to enable/disable tracking
        
        # VWAP Override System - File-based control
        self.vwap_override_file = "vwap_override.txt"  # File to check for override values
        self.vwap_override_enabled = False  # Flag to enable manual VWAP override
        self.vwap_override_value = None     # Manually set VWAP value
        self.instrument_freeze_enabled = False  # Flag to freeze instrument updates (auto-managed)
        self.frozen_ce_symbol = None        # Preserved CE symbol when frozen
        self.frozen_pe_symbol = None        # Preserved PE symbol when frozen
        self.vwap_override_timestamp = None # When override was set
        
        # VWAP Override Cycle Management (prevents excessive order placement)
        self.vwap_override_cycle_state = "READY"  # READY, ACTIVE, COMPLETED
        self.vwap_override_cycle_started = False  # Track if cycle was started
        
        # Expiry date configuration
        self.expiry_date = None  # Will be loaded from UI config
        
        # Historical data caching to avoid rate limits
        self.historical_data_cache = {}
        self.last_historical_fetch_time = None

        # API call tracking for rate limit monitoring
        self.api_call_tracking = {
            "quote_calls": 0,
            "historical_calls": 0,
            "last_reset_time": self.get_ist_time()
        }
        
        # VWAP exit candle tracking - to prevent HA exits in same minute
        self.vwap_exit_candle_minute = None  # Track the minute when VWAP exit occurred
        self.vwap_exit_in_current_candle = False  # Flag to block HA exits in same candle

        # Order and portfolio tracking (works for both real and virtual trading)
        self.simulation_mode = False
        self.all_orders = []  # Renamed from virtual_orders - tracks all orders (real or virtual)
        
        # Comprehensive order tracking for UI display
        self.order_history = []  # Complete order history with success/failure details
        self.failed_orders = []  # Specific tracking for failed orders
        self.order_status_log = []  # Real-time order status updates
        
        self.trading_portfolio = {  # Renamed from virtual_portfolio - tracks P&L for all trading
            "cash": 100000,  # Starting with 1 lakh cash
            "total_pnl": 0,
            "total_trades": 0,
            "winning_trades": 0,
            "losing_trades": 0,
            # High Water Mark Tracking
            "max_profit_seen": 0,  # Highest unrealized profit ever reached
            "max_loss_seen": 0,    # Lowest unrealized loss ever reached (negative value)
            "current_session_max_profit": 0,  # Max profit in current session
            "current_session_max_loss": 0,    # Max loss in current session
            "peak_drawdown": 0,    # Maximum drawdown from peak profit
            "last_peak_time": None,  # When max profit was reached
            "last_trough_time": None  # When max loss was reached
        }
        
        # Excel export functionality
        self.excel_export_enabled = True
        self.excel_orders_file = f"nifty_orders_{datetime.now().strftime('%Y%m%d')}.xlsx"
        self.excel_trades_file = f"nifty_trades_{datetime.now().strftime('%Y%m%d')}.xlsx"
        self.excel_portfolio_file = f"nifty_portfolio_{datetime.now().strftime('%Y%m%d')}.xlsx"
        
        # Initialize Excel files
        self._initialize_excel_files()
        
        # Heikin Ashi data for trend analysis
        self.heikin_ashi_data = []
        self.heikin_ashi_ce_data = []  # Separate HA data for CE
        self.heikin_ashi_pe_data = []  # Separate HA data for PE
        
        # Tick-based Heikin Ashi for faster exits
        self.tick_ha_ce_data = None  # Current tick-based HA for CE
        self.tick_ha_pe_data = None  # Current tick-based HA for PE
        self.tick_ha_combined_data = None  # Current tick-based HA for combined
        
        # Upper wick detection parameters
        self.upper_wick_threshold_percent = 0 # Upper wick should be at least 5% of total range
        self.upper_wick_threshold_value = 0    # Upper wick should be at least 0.5 points above HA open
        self.lower_wick_threshold_value = 0    # Lower wick should be at least 0.5 points below HA open
        self.upper_wick_exit_enabled = True  # Enable/disable upper wick exits
        self.use_absolute_wick_thresholds = False  # Use absolute value thresholds instead of percentage
        
        # Dynamic interval configuration for decision-making
        self.decision_interval = "1minute"  # Can be: 1minute, 3minute, 5minute, 10minute, 15minute, 30minute
        self.decision_interval_minutes = self._parse_interval_to_minutes(self.decision_interval)
        
        # Interval-based data fetching control
        self.last_interval_fetch_time = None
        self.interval_candle_data = None
        self.individual_candle_data_ce = None  # Cache for CE individual candle data
        self.individual_candle_data_pe = None  # Cache for PE individual candle data
        self.should_fetch_historical = False
        
        # Nifty 50 symbol for Fyers
        self.nifty_symbol = "NSE:NIFTY50-INDEX"

        # Current minute candle tracking for real-time trend analysis
        self.current_minute_candles = {
            "CE": {
                "open": None,
                "high": None,
                "low": None,
                "close": None,
                "minute": None,
                "symbol": None
            },
            "PE": {
                "open": None,
                "high": None,
                "low": None,
                "close": None,
                "minute": None,
                "symbol": None
            }
        }

        # Market timing (Already initialized IST timezone above)
        now_ist = datetime.now(self.ist_timezone)
        
        self.market_start = now_ist.replace(hour=9, minute=15, second=0, microsecond=0)
        self.market_end = now_ist.replace(hour=15, minute=30, second=0, microsecond=0)
        # First order timing - 40 minutes after market opening
        self.first_order_time = self.market_start + timedelta(minutes=40)
        
        logger.info("Nifty Options Trader initialized")
        logger.info(f"Market hours: {self.market_start.strftime('%H:%M')} - {self.market_end.strftime('%H:%M')}")
        logger.info(f"First order allowed after: {self.first_order_time.strftime('%H:%M')}")
        
        print("Nifty Options Trader initialized")
        logger.info("Nifty Options Trader initialized")
        print(f"Market hours: {self.market_start.strftime('%H:%M')} - {self.market_end.strftime('%H:%M')}")
        logger.info(f"Market hours: {self.market_start.strftime('%H:%M')} - {self.market_end.strftime('%H:%M')}")
        print(f"First order allowed after: {self.first_order_time.strftime('%H:%M')}")
        logger.info(f"First order allowed after: {self.first_order_time.strftime('%H:%M')}")
        
        if not self.fyers:
            logger.error("Fyers API not configured. Cannot run production trading.")
            print("❌ Error: Fyers API not configured. Cannot run production trading.")
            print("   Please configure API credentials before starting.")
            raise Exception("Fyers API not configured for production trading")
        else:
            logger.info("✅ Fyers API configured for live trading")
            print("✅ Fyers API configured for live trading")

    def _load_ui_config(self) -> dict:
        """Load configuration from UI-generated files"""
        config = {
            'client_id': None,
            'access_token': None,
            'vwap_override': None,
            'expiry_override': None
        }
        
        # Get the directory where this script is located
        script_dir = os.path.dirname(os.path.abspath(__file__))
        
        try:
            # Load API credentials from config.txt
            config_file = os.path.join(script_dir, 'config.txt')
            if os.path.exists(config_file):
                logger.info("📄 Loading config.txt (API credentials)")
                with open(config_file, 'r') as f:
                    lines = f.readlines()
                    for line in lines:
                        if line.startswith('CLIENT_ID='):
                            config['client_id'] = line.split('=', 1)[1].strip()
                        elif line.startswith('client_secret='):
                            # We have client_secret but don't need it for this class
                            pass
                logger.info(f"✅ Config loaded - Client ID: {'Yes' if config['client_id'] else 'No'}")
            else:
                logger.warning(f"⚠️ config.txt not found at {config_file} - API credentials not loaded")
                
            # Load access token from access.txt
            access_file = os.path.join(script_dir, 'access.txt')
            if os.path.exists(access_file):
                logger.info("📄 Loading access.txt (Access Token)")
                with open(access_file, 'r') as f:
                    config['access_token'] = f.read().strip()
                logger.info("✅ Access token loaded from access.txt")
            else:
                logger.warning(f"⚠️ access.txt not found at {access_file} - Access token not loaded")
                
            # Load VWAP override from vwap_override.txt
            vwap_file = os.path.join(script_dir, 'vwap_override.txt')
            if os.path.exists(vwap_file):
                logger.info("📄 Loading vwap_override.txt")
                with open(vwap_file, 'r') as f:
                    content = f.read().strip()
                    if content and content != 'null' and content.lower() != 'n':
                        try:
                            config['vwap_override'] = float(content)
                            logger.info(f"✅ VWAP override loaded: {config['vwap_override']}")
                        except ValueError:
                            logger.warning(f"⚠️ Invalid VWAP override value: {content}")
                            
            # Load expiry override from expiry_override.txt
            expiry_file = os.path.join(script_dir, 'expiry_override.txt')
            if os.path.exists(expiry_file):
                logger.info("📄 Loading expiry_override.txt")
                with open(expiry_file, 'r') as f:
                    content = f.read().strip()
                    if content:
                        config['expiry_override'] = content
                        logger.info(f"✅ Expiry override loaded: {config['expiry_override']}")
                        
        except Exception as e:
            logger.error(f"❌ Error loading UI configuration: {e}")
            
        return config
    
    def _load_ui_overrides(self, config: dict):
        """Apply UI configuration overrides to the trader"""
        # Apply VWAP override if present
        if config.get('vwap_override'):
            self.vwap_override_enabled = True
            self.vwap_override_value = config['vwap_override']
            self.vwap_override_timestamp = datetime.now(self.ist_timezone)
            logger.info(f"🎯 VWAP override applied: {self.vwap_override_value}")
            print(f"🎯 VWAP override active: {self.vwap_override_value}")
            
        # Store expiry override for later use
        if config.get('expiry_override'):
            self.expiry_date = config['expiry_override']
            logger.info(f"📅 Expiry override applied: {self.expiry_date}")
            print(f"📅 Using expiry date: {self.expiry_date}")
            
        # Log configuration summary
        logger.info("📋 Configuration Summary:")
        logger.info(f"   🔑 Client ID: {'✅ Loaded' if config.get('client_id') else '❌ Missing'}")
        logger.info(f"   🎫 Access Token: {'✅ Loaded' if config.get('access_token') else '❌ Missing'}")
        logger.info(f"   📊 VWAP Override: {'✅ Active' if config.get('vwap_override') else '❌ Not Set'}")
        logger.info(f"   📅 Expiry Override: {'✅ Set' if config.get('expiry_override') else '❌ Not Set'}")
        
        print("\n📋 Configuration Summary:")
        print(f"   🔑 Client ID: {'✅ Loaded' if config.get('client_id') else '❌ Missing'}")
        print(f"   🎫 Access Token: {'✅ Loaded' if config.get('access_token') else '❌ Missing'}")
        print(f"   📊 VWAP Override: {'✅ Active' if config.get('vwap_override') else '❌ Not Set'}")
        print(f"   📅 Expiry Override: {'✅ Set' if config.get('expiry_override') else '❌ Not Set'}")
        print()
        
        if not config.get('client_id') or not config.get('access_token'):
            logger.error("PRODUCTION ERROR: Missing API credentials.")
            print("🚨 PRODUCTION ERROR: Missing API credentials!")
            print("   PRODUCTION SYSTEMS REQUIRE VALID API CREDENTIALS")
            print("   Configure via web interface:")
            print("   1. Open http://localhost:8000")
            print("   2. Fill in API credentials and access token")
            print("   3. Click 'Save API Config'")
            print("   4. Restart the trading bot")
            print()
            raise ValueError("PRODUCTION TRADING REQUIRES VALID API CREDENTIALS")
        else:
            logger.info("✅ API credentials configured. REAL TRADING MODE enabled.")
            print("💰 REAL TRADING MODE - Real orders will be placed!")
            self.simulation_mode = False
    
    def _parse_interval_to_minutes(self, interval: str) -> int:
        """Parse interval string to minutes"""
        interval_map = {
            "1minute": 1,
            "3minute": 3,
            "5minute": 5,
            "10minute": 10,
            "15minute": 15,
            "30minute": 30
        }
        return interval_map.get(interval, 5)  # Default to 5 minutes
    
    def get_ist_time(self) -> datetime:
        """Get current time in IST timezone"""
        if not hasattr(self, 'ist_timezone'):
            self.ist_timezone = pytz.timezone('Asia/Kolkata')
        return datetime.now(self.ist_timezone)
    
    def is_at_interval_boundary(self) -> bool:
        """Check if current time is at an interval boundary (e.g., 9:16, 9:17, 9:18 for 1-minute after candle close)"""
        current_time = self.get_ist_time()
        
        # Calculate minutes since market start (9:15)
        market_start = self.market_start
        time_diff = current_time - market_start
        total_minutes = time_diff.total_seconds() / 60
        
        # Check if we're at an interval boundary
        if total_minutes < 0:
            return False  # Before market start
        
        # For 1-minute: we want to fetch at 9:16:00-9:16:15 (after 9:15-9:16 candle closes)
        # For 3-minute: we want to fetch at 9:18:00-9:18:15 (after 9:15-9:18 candle closes)
        # For 5-minute: we want to fetch at 9:20:00-9:20:15 (after 9:15-9:20 candle closes)
        
        # Check if we just passed a complete interval boundary
        minutes_into_current_interval = total_minutes % self.decision_interval_minutes
        
        # We're at boundary if we're within the first 15 seconds of a new interval
        # This means the previous interval's candle has just closed
        is_at_boundary = minutes_into_current_interval < 0.25  # 15 seconds tolerance
        
        if is_at_boundary:
            # Calculate which interval boundary we just passed
            completed_intervals = int(total_minutes // self.decision_interval_minutes)
            boundary_time = market_start + timedelta(minutes=completed_intervals * self.decision_interval_minutes)
            logger.debug(f"At {self.decision_interval} interval boundary at {current_time.strftime('%H:%M:%S')} (candle {boundary_time.strftime('%H:%M')} just closed)")
        
        return is_at_boundary
    
    def should_fetch_interval_data(self) -> bool:
        """Determine if we should fetch new interval data"""
        current_time = self.get_ist_time()
        
        # Check if we're at an interval boundary for all intervals
        if not self.is_at_interval_boundary():
            return False
        
        # Check if we already fetched data for this interval
        if self.last_interval_fetch_time:
            time_since_last_fetch = (current_time - self.last_interval_fetch_time).total_seconds() / 60
            if time_since_last_fetch < self.decision_interval_minutes - 0.5:  # Allow 30s tolerance
                logger.debug(f"Already fetched data for this {self.decision_interval} interval")
                return False
        
        logger.info(f"Should fetch {self.decision_interval} interval data at {current_time.strftime('%H:%M:%S')}")
        return True
    
    def _get_next_boundary_info(self) -> Dict:
        """Get information about the next interval boundary"""
        current_time = self.get_ist_time()
        market_start = self.market_start
        time_diff = current_time - market_start
        total_minutes = time_diff.total_seconds() / 60
        
        if total_minutes < 0:
            return {
                "next_time": market_start.strftime('%H:%M'),
                "minutes": abs(total_minutes)
            }
        
        # Calculate next boundary
        intervals_passed = int(total_minutes // self.decision_interval_minutes)
        next_boundary_minutes = (intervals_passed + 1) * self.decision_interval_minutes
        next_boundary_time = market_start + timedelta(minutes=next_boundary_minutes)
        
        minutes_to_boundary = (next_boundary_time - current_time).total_seconds() / 60
        
        return {
            "next_time": next_boundary_time.strftime('%H:%M'),
            "minutes": minutes_to_boundary
        }
    
    def get_upper_wick_status(self) -> Dict:
        """Get current upper wick detection status"""
        status = {
            "enabled": self.upper_wick_exit_enabled,
            "threshold_percent": self.upper_wick_threshold_percent,
            "upper_wick_threshold_value": self.upper_wick_threshold_value,
            "lower_wick_threshold_value": self.lower_wick_threshold_value,
            "use_absolute_thresholds": self.use_absolute_wick_thresholds,
            "ce_tick_ha_available": self.tick_ha_ce_data is not None,
            "pe_tick_ha_available": self.tick_ha_pe_data is not None
        }
        
        if self.tick_ha_ce_data:
            ce_wick_result = self.check_upper_wick_exit_condition("CE")
            status["ce_upper_wick_size"] = ce_wick_result.get("upper_wick_size", 0)
            status["ce_exit_signal"] = ce_wick_result.get("exit_signal", False)
            status["ce_threshold_met"] = ce_wick_result.get("threshold_met", False)
        
        if self.tick_ha_pe_data:
            pe_wick_result = self.check_upper_wick_exit_condition("PE")
            status["pe_upper_wick_size"] = pe_wick_result.get("upper_wick_size", 0)
            status["pe_exit_signal"] = pe_wick_result.get("exit_signal", False)
            status["pe_threshold_met"] = pe_wick_result.get("threshold_met", False)
        
        return status
    
    def get_vwap_tracking_status(self) -> Dict:
        """Get current VWAP difference tracking status"""
        if not self.vwap_diff_tracking_enabled:
            return {
                "tracking_enabled": False,
                "message": "VWAP tracking not active"
            }
        
        current_diff = 0.0
        if self.current_vwap and self.combined_premium_data:
            latest_data = self.combined_premium_data[-1]
            current_combined_premium = latest_data['combined']
            current_diff = ((self.current_vwap - current_combined_premium) / current_combined_premium) * 100
        
        time_since_order = (self.get_ist_time() - self.order_start_time).total_seconds() / 60 if self.order_start_time else 0
        
        return {
            "tracking_enabled": True,
            "current_diff_percent": current_diff,
            "max_diff_percent": self.max_vwap_diff_during_order,
            "threshold_percent": self.vwap_diff_threshold_percent,
            "time_since_order_minutes": time_since_order,
            "order_start_time": self.order_start_time.strftime('%H:%M:%S') if self.order_start_time else None
        }
    
    def get_vwap_override_status(self) -> Dict:
        """Get current VWAP override status"""
        if not self.vwap_override_enabled:
            return {
                "override_active": False,
                "message": "VWAP override not active - using automatic calculation"
            }
        
        duration_minutes = (self.get_ist_time() - self.vwap_override_timestamp).total_seconds() / 60
        
        return {
            "override_active": True,
            "override_value": self.vwap_override_value,
            "set_timestamp": self.vwap_override_timestamp.strftime('%H:%M:%S'),
            "duration_minutes": duration_minutes,
            "instruments_frozen": self.instrument_freeze_enabled,
            "frozen_ce_symbol": self.frozen_ce_symbol,
            "frozen_pe_symbol": self.frozen_pe_symbol,
            "message": f"Manual VWAP: {self.vwap_override_value:.2f if self.vwap_override_value is not None else 'None'} (active for {duration_minutes:.1f} min)"
        }
    
    def print_vwap_override_status(self) -> None:
        """Print detailed VWAP override status"""
        logger.debug("Printing VWAP override status...")
        status = self.get_vwap_override_status()
        
        print(f"\n🎯 VWAP OVERRIDE STATUS")
        logger.info(f"VWAP Override Status: {'ACTIVE' if status['override_active'] else 'INACTIVE'}")
        
        if status["override_active"]:
            print(f"   Status: ACTIVE")
            override_value = status['override_value']
            if override_value is not None:
                print(f"   Override Value: {override_value:.2f}")
                logger.info(f"VWAP override active: Value={override_value:.2f}, Duration={status['duration_minutes']:.1f}min")
            else:
                print(f"   Override Value: None")
                logger.info(f"VWAP override active: Value=None, Duration={status['duration_minutes']:.1f}min")
            print(f"   Set At: {status['set_timestamp']}")
            print(f"   Duration: {status['duration_minutes']:.1f} minutes")
            print(f"   Instruments Frozen: {'Yes' if status['instruments_frozen'] else 'No'}")
            
            logger.debug(f"Override set at: {status['set_timestamp']}")
            
            if status['instruments_frozen']:
                print(f"   Frozen CE: {status['frozen_ce_symbol']}")
                print(f"   Frozen PE: {status['frozen_pe_symbol']}")
                logger.info(f"Instruments frozen - CE: {status['frozen_ce_symbol']}, PE: {status['frozen_pe_symbol']}")
        else:
            print(f"   Status: INACTIVE")
            current_vwap_display = f"{self.current_vwap:.2f}" if self.current_vwap is not None else "Not calculated"
            print(f"   Current VWAP: {current_vwap_display}")
            print(f"   Mode: Automatic calculation")
            
            logger.info("VWAP override inactive - using automatic calculation")
            current_vwap_log = f"{self.current_vwap:.2f}" if self.current_vwap is not None else "None"
            logger.debug(f"Current automatic VWAP: {current_vwap_log}")
    
    def _initialize_excel_files(self):
        """Initialize Excel files for data export"""
        if not self.excel_export_enabled:
            return
        
        try:
            # Initialize Orders Excel file
            orders_columns = [
                'Date', 'Time', 'Order_ID', 'Option_Type', 'Action', 'Strike', 
                'Entry_Price', 'Combined_Entry_Price', 'Quantity', 'Nifty_Price', 
                'VWAP', 'Status', 'Trading_Symbol', 'Expiry_Date', 'Expiry_Type'
            ]
            
            if not os.path.exists(self.excel_orders_file):
                orders_df = pd.DataFrame(columns=orders_columns)
                orders_df.to_excel(self.excel_orders_file, index=False)
                logger.info(f"Created orders Excel file: {self.excel_orders_file}")
            
            # Initialize Trades Excel file (for squared off positions)
            trades_columns = [
                'Date', 'Entry_Time', 'Exit_Time', 'Order_ID', 'Option_Type', 'Action',
                'Strike', 'Entry_Price', 'Exit_Price', 'Quantity', 'PnL', 'PnL_Percentage',
                'Duration_Minutes', 'Exit_Reason', 'Nifty_Entry', 'Nifty_Exit',
                'VWAP_Entry', 'VWAP_Exit', 'Combined_Entry', 'Combined_Exit',
                'Trading_Symbol', 'Expiry_Date', 'Max_Profit', 'Max_Loss', 'Drawdown'
            ]
            
            if not os.path.exists(self.excel_trades_file):
                trades_df = pd.DataFrame(columns=trades_columns)
                trades_df.to_excel(self.excel_trades_file, index=False)
                logger.info(f"Created trades Excel file: {self.excel_trades_file}")
            
            # Initialize Portfolio tracking Excel file
            portfolio_columns = [
                'Date', 'Time', 'Total_PnL', 'Total_Trades', 'Winning_Trades', 
                'Losing_Trades', 'Win_Rate', 'Avg_PnL_Per_Trade', 'Return_Percentage',
                'Max_Profit_Seen', 'Max_Loss_Seen', 'Current_Drawdown', 'Active_Positions',
                'Unrealized_PnL', 'Realized_PnL'
            ]
            
            if not os.path.exists(self.excel_portfolio_file):
                portfolio_df = pd.DataFrame(columns=portfolio_columns)
                portfolio_df.to_excel(self.excel_portfolio_file, index=False)
                logger.info(f"Created portfolio Excel file: {self.excel_portfolio_file}")
            
            print(f"📊 Excel export files initialized:")
            print(f"   Orders: {self.excel_orders_file}")
            print(f"   Trades: {self.excel_trades_file}")
            print(f"   Portfolio: {self.excel_portfolio_file}")
            
        except Exception as e:
            logger.error(f"Error initializing Excel files: {e}")
            print(f"⚠️ Warning: Excel export disabled due to error: {e}")
            self.excel_export_enabled = False
    
    def _export_order_to_excel(self, order_data: Dict):
        """Export order data to Excel file"""
        if not self.excel_export_enabled:
            return
        
        try:
            current_time = self.get_ist_time()
            
            # Prepare order data for Excel
            excel_row = {
                'Date': current_time.strftime('%Y-%m-%d'),
                'Time': current_time.strftime('%H:%M:%S'),
                'Order_ID': order_data.get('order_id', 'N/A'),
                'Option_Type': order_data.get('option_type', 'N/A'),
                'Action': order_data.get('action', 'N/A'),
                'Strike': order_data.get('strike', 0),
                'Entry_Price': order_data.get('entry_price', 0),
                'Combined_Entry_Price': order_data.get('combined_entry_price', 0),
                'Quantity': order_data.get('quantity', 75),
                'Nifty_Price': self.current_nifty_price or 0,
                'VWAP': self.current_vwap or 0,
                'Status': order_data.get('status', 'FILLED'),
                'Trading_Symbol': order_data.get('tradingsymbol', 'N/A'),
                'Expiry_Date': order_data.get('expiry_date', 'N/A'),
                'Expiry_Type': order_data.get('expiry_type', 'N/A')
            }
            
            # Read existing data and append new row
            if os.path.exists(self.excel_orders_file):
                existing_df = pd.read_excel(self.excel_orders_file)
                new_df = pd.concat([existing_df, pd.DataFrame([excel_row])], ignore_index=True)
            else:
                new_df = pd.DataFrame([excel_row])
            
            # Save to Excel
            new_df.to_excel(self.excel_orders_file, index=False)
            logger.info(f"Order data exported to Excel: {order_data.get('order_id')}")
            
        except Exception as e:
            logger.error(f"Error exporting order to Excel: {e}")
    
    def get_file_based_override_status(self) -> Dict:
        """Get current status of file-based VWAP override and auto-managed instrument freeze"""
        # Check current file state
        self.check_vwap_override_file()
        
        status = {
            "vwap_override_active": self.vwap_override_enabled,
            "vwap_override_value": self.vwap_override_value,
            "vwap_override_file_exists": os.path.exists(self.vwap_override_file),
            "instruments_frozen": self.instrument_freeze_enabled,
            "frozen_ce_symbol": self.frozen_ce_symbol,
            "frozen_pe_symbol": self.frozen_pe_symbol,
            "auto_freeze_mode": True  # Instruments are now auto-managed with VWAP override
        }
        
        if self.vwap_override_timestamp:
            duration = (self.get_ist_time() - self.vwap_override_timestamp).total_seconds() / 60
            status["override_duration_minutes"] = duration
        else:
            status["override_duration_minutes"] = 0
            
        return status
    
    def print_file_based_status(self):
        """Print current file-based override status"""
        status = self.get_file_based_override_status()
        
        print(f"\n📁 FILE-BASED VWAP CONTROL")
        print(f"   Override File: {self.vwap_override_file}")
        print(f"   File Exists: {'✅' if status['vwap_override_file_exists'] else '❌'}")
        
        if status["vwap_override_active"]:
            print(f"   VWAP Status: 🎯 OVERRIDE ACTIVE")
            override_value = status['vwap_override_value']
            if override_value is not None:
                print(f"   Override Value: {override_value:.2f}")
            else:
                print(f"   Override Value: None")
            print(f"   Duration: {status['override_duration_minutes']:.1f} minutes")
            print(f"   Instruments: 🔒 AUTO-FROZEN")
            if status['frozen_ce_symbol'] and status['frozen_pe_symbol']:
                print(f"   Frozen CE: {status['frozen_ce_symbol']}")
                print(f"   Frozen PE: {status['frozen_pe_symbol']}")
        else:
            print(f"   VWAP Status: ⚪ AUTOMATIC CALCULATION")
            current_vwap_display = f"{self.current_vwap:.2f}" if self.current_vwap is not None else "Not calculated"
            print(f"   Current VWAP: {current_vwap_display}")
            print(f"   Instruments: 🔓 AUTO-UPDATING")
        
        print(f"\n💡 How to use:")
        print(f"   * Edit {self.vwap_override_file} with desired VWAP value (e.g., 24500.50)")
        print(f"   * Put 0 or empty to disable override")
        print(f"   * Instruments freeze/unfreeze automatically with override")
        
        return status

    def _export_trade_to_excel(self, trade_data: Dict):
        """Export completed trade data to Excel file"""
        if not self.excel_export_enabled:
            return
        
        try:
            current_time = self.get_ist_time()
            
            # Calculate additional metrics
            entry_price = trade_data.get('entry_price', 0)
            exit_price = trade_data.get('exit_price', 0)
            pnl = trade_data.get('pnl', 0)
            quantity = trade_data.get('quantity', 75)
            
            # Calculate PnL percentage
            pnl_percentage = (pnl / (entry_price * quantity) * 100) if entry_price > 0 else 0
            
            # Get max profit and loss from session tracking
            vp = self.trading_portfolio
            max_profit = vp.get('current_session_max_profit', 0)
            max_loss = vp.get('current_session_max_loss', 0)
            drawdown = vp.get('peak_drawdown', 0)
            
            # Prepare trade data for Excel
            excel_row = {
                'Date': current_time.strftime('%Y-%m-%d'),
                'Entry_Time': trade_data.get('entry_time', current_time).strftime('%H:%M:%S'),
                'Exit_Time': trade_data.get('exit_time', current_time).strftime('%H:%M:%S'),
                'Order_ID': trade_data.get('original_order_id', 'N/A'),
                'Option_Type': trade_data.get('option_type', 'N/A'),
                'Action': trade_data.get('action', 'SELL'),
                'Strike': trade_data.get('strike', 0),
                'Entry_Price': entry_price,
                'Exit_Price': exit_price,
                'Quantity': quantity,
                'PnL': pnl,
                'PnL_Percentage': pnl_percentage,
                'Duration_Minutes': trade_data.get('duration_minutes', 0),
                'Exit_Reason': trade_data.get('reason', 'Manual'),
                'Nifty_Entry': trade_data.get('nifty_entry', self.current_nifty_price or 0),
                'Nifty_Exit': self.current_nifty_price or 0,
                'VWAP_Entry': trade_data.get('vwap_entry', 0),
                'VWAP_Exit': self.current_vwap or 0,
                'Combined_Entry': trade_data.get('combined_entry_price', 0),
                'Combined_Exit': self.combined_premium_data[-1]['combined'] if self.combined_premium_data else 0,
                'Trading_Symbol': trade_data.get('tradingsymbol', 'N/A'),
                'Expiry_Date': trade_data.get('expiry_date', 'N/A'),
                'Max_Profit': max_profit,
                'Max_Loss': max_loss,
                'Drawdown': drawdown
            }
            
            # Read existing data and append new row
            if os.path.exists(self.excel_trades_file):
                existing_df = pd.read_excel(self.excel_trades_file)
                new_df = pd.concat([existing_df, pd.DataFrame([excel_row])], ignore_index=True)
            else:
                new_df = pd.DataFrame([excel_row])
            
            # Save to Excel
            new_df.to_excel(self.excel_trades_file, index=False)
            logger.info(f"Trade data exported to Excel: {trade_data.get('original_order_id')}")
            print(f"   📊 Trade exported to Excel: P&L {pnl:.2f}")
            
        except Exception as e:
            logger.error(f"Error exporting trade to Excel: {e}")
    
    def _export_portfolio_to_excel(self):
        """Export current portfolio status to Excel file"""
        if not self.excel_export_enabled:
            return
        
        try:
            vp = self.trading_portfolio
            current_time = self.get_ist_time()
            
            # Calculate metrics
            win_rate = (vp['winning_trades'] / vp['total_trades'] * 100) if vp['total_trades'] > 0 else 0
            avg_pnl = vp['total_pnl'] / vp['total_trades'] if vp['total_trades'] > 0 else 0
            return_pct = (vp['total_pnl'] / vp['cash']) * 100
            
            # Get active positions
            active_positions = [k for k, v in self.positions.items() if v is not None]
            active_positions_str = ', '.join(active_positions) if active_positions else 'None'
            
            # Calculate unrealized P&L
            unrealized_pnl = self.calculate_unrealized_pnl()
            
            # Prepare portfolio data for Excel
            excel_row = {
                'Date': current_time.strftime('%Y-%m-%d'),
                'Time': current_time.strftime('%H:%M:%S'),
                'Total_PnL': vp['total_pnl'],
                'Total_Trades': vp['total_trades'],
                'Winning_Trades': vp['winning_trades'],
                'Losing_Trades': vp['losing_trades'],
                'Win_Rate': win_rate,
                'Avg_PnL_Per_Trade': avg_pnl,
                'Return_Percentage': return_pct,
                'Max_Profit_Seen': vp['max_profit_seen'],
                'Max_Loss_Seen': vp['max_loss_seen'],
                'Current_Drawdown': vp['peak_drawdown'],
                'Active_Positions': active_positions_str,
                'Unrealized_PnL': unrealized_pnl,
                'Realized_PnL': vp['total_pnl']
            }
            
            # Read existing data and append new row
            if os.path.exists(self.excel_portfolio_file):
                existing_df = pd.read_excel(self.excel_portfolio_file)
                new_df = pd.concat([existing_df, pd.DataFrame([excel_row])], ignore_index=True)
            else:
                new_df = pd.DataFrame([excel_row])
            
            # Save to Excel
            new_df.to_excel(self.excel_portfolio_file, index=False)
            logger.debug(f"Portfolio data exported to Excel")
            
        except Exception as e:
            logger.error(f"Error exporting portfolio to Excel: {e}")
    
    def _track_order_attempt(self, option_type: str, action: str, symbol: str, entry_price: float, order_params: dict):
        """Track an order attempt for UI display"""
        order_attempt = {
            "timestamp": self.get_ist_time(),
            "option_type": option_type,
            "action": action,
            "symbol": symbol,
            "entry_price": entry_price,
            "strike": self.current_atm_strike,
            "nifty_price": self.current_nifty_price,
            "vwap": self.current_vwap,
            "order_params": order_params.copy(),
            "status": "PENDING",
            "order_id": None,
            "error_message": None,
            "error_code": None
        }
        
        # Add to order history
        self.order_history.append(order_attempt)
        
        # Add to status log
        status_update = {
            "timestamp": self.get_ist_time(),
            "message": f"Order attempt: {action} {option_type} at {entry_price:.2f}",
            "type": "ORDER_ATTEMPT",
            "data": order_attempt
        }
        self.order_status_log.append(status_update)
        
        logger.info(f"Order attempt tracked: {action} {option_type} at strike {self.current_atm_strike}")
        return len(self.order_history) - 1  # Return index for updating
    
    def _track_order_success(self, order_index: int, order_id: str, response: dict):
        """Track successful order placement"""
        if order_index < len(self.order_history):
            self.order_history[order_index]["status"] = "SUCCESS"
            self.order_history[order_index]["order_id"] = order_id
            self.order_history[order_index]["api_response"] = response
            
            # Add success status update
            status_update = {
                "timestamp": self.get_ist_time(),
                "message": f"Order placed successfully: ID {order_id}",
                "type": "ORDER_SUCCESS",
                "order_id": order_id,
                "data": self.order_history[order_index]
            }
            self.order_status_log.append(status_update)
            
            logger.info(f"Order success tracked: ID {order_id}")
    
    def _track_order_failure(self, order_index: int, error_response: dict, error_message: str):
        """Track failed order placement with detailed error information"""
        if order_index < len(self.order_history):
            self.order_history[order_index]["status"] = "FAILED"
            self.order_history[order_index]["error_message"] = error_message
            self.order_history[order_index]["api_response"] = error_response
            
            # Extract error details
            if error_response:
                self.order_history[order_index]["error_code"] = error_response.get("code")
                self.order_history[order_index]["fyers_message"] = error_response.get("message", "")
            
            # Add to failed orders list for easy UI access
            failed_order = self.order_history[order_index].copy()
            self.failed_orders.append(failed_order)
            
            # Add failure status update
            status_update = {
                "timestamp": self.get_ist_time(),
                "message": f"Order failed: {error_message}",
                "type": "ORDER_FAILURE",
                "error_code": error_response.get("code") if error_response else None,
                "error_message": error_message,
                "data": failed_order
            }
            self.order_status_log.append(status_update)
            
            logger.error(f"Order failure tracked: {error_message}")
            print(f"📝 Order failure recorded for UI display")
    
    def get_order_history_for_ui(self):
        """Get formatted order history for UI display"""
        return {
            "total_orders": len(self.order_history),
            "successful_orders": len([o for o in self.order_history if o["status"] == "SUCCESS"]),
            "failed_orders": len([o for o in self.order_history if o["status"] == "FAILED"]),
            "pending_orders": len([o for o in self.order_history if o["status"] == "PENDING"]),
            "orders": self.order_history,
            "recent_failures": self.failed_orders[-5:] if self.failed_orders else [],  # Last 5 failures
            "status_log": self.order_status_log[-10:] if self.order_status_log else []  # Last 10 status updates
        }
    
    def get_latest_order_status(self):
        """Get the most recent order status for real-time UI updates"""
        if not self.order_status_log:
            return None
        
        return {
            "latest_status": self.order_status_log[-1],
            "failed_count_today": len(self.failed_orders),
            "last_failure": self.failed_orders[-1] if self.failed_orders else None
        }
    
    def _start_vwap_diff_tracking(self):
        """Start tracking VWAP vs current price difference when order is placed"""
        self.max_vwap_diff_during_order = 0.0
        self.order_start_time = self.get_ist_time()
        self.vwap_diff_tracking_enabled = False
        logger.info("VWAP difference tracking started")
        print(f"   📊 VWAP tracking: Max diff reset to 0.0%, threshold: {self.vwap_diff_threshold_percent}%")
    
    def _reset_vwap_diff_tracking(self):
        """Reset VWAP difference tracking after positions are squared off"""
        self.max_vwap_diff_during_order = 0.0
        self.order_start_time = None
        self.vwap_diff_tracking_enabled = False
        logger.info("VWAP difference tracking reset")
    
    def _reset_vwap_exit_candle_tracking(self):
        """Reset VWAP exit candle tracking for new minute candle"""
        current_minute = self.get_ist_time().replace(second=0, microsecond=0)
        if self.vwap_exit_candle_minute != current_minute:
            self.vwap_exit_candle_minute = None
            self.vwap_exit_in_current_candle = False
            logger.debug("VWAP exit candle tracking reset for new minute candle")
    
    def _mark_vwap_exit_candle(self):
        """Mark current minute candle as having VWAP exit - blocks HA exits for this candle"""
        current_minute = self.get_ist_time().replace(second=0, microsecond=0)
        self.vwap_exit_candle_minute = current_minute
        self.vwap_exit_in_current_candle = True
        logger.info(f"VWAP exit detected in candle {current_minute} - HA exits blocked for this candle")
        print(f"   🔒 HA exit checks blocked for current candle: {current_minute.strftime('%H:%M')}")
    
    def _is_vwap_exit_candle(self) -> bool:
        """Check if current candle has had a VWAP exit (blocks HA exits)"""
        current_minute = self.get_ist_time().replace(second=0, microsecond=0)
        return (self.vwap_exit_candle_minute == current_minute and self.vwap_exit_in_current_candle)
    
    def _update_vwap_diff_tracking(self):
        """Update maximum VWAP difference during order lifetime"""
        if not self.vwap_diff_tracking_enabled or not self.current_vwap or not self.current_nifty_price:
            return
        
        if not self.combined_premium_data:
            return
        
        # Calculate current difference between VWAP and combined premium
        latest_data = self.combined_premium_data[-1]
        current_combined_premium = latest_data['combined']
        
        # Calculate percentage difference: (VWAP - Current_Price) / Current_Price * 100
        vwap_diff_percent = ((self.current_vwap - current_combined_premium) / current_combined_premium) * 100
        
        # Track maximum absolute difference
        abs_vwap_diff = abs(vwap_diff_percent)
        
        if abs_vwap_diff > self.max_vwap_diff_during_order:
            self.max_vwap_diff_during_order = abs_vwap_diff
            logger.debug(f"New max VWAP diff: {self.max_vwap_diff_during_order:.3f}%")
        
        # Log current tracking status every 30 seconds
        if self.order_start_time:
            current_time = self.get_ist_time()
            time_since_order = (current_time - self.order_start_time).total_seconds()
            if int(time_since_order) % 30 == 0:  # Every 30 seconds
                logger.info(f"VWAP tracking: Current diff: {vwap_diff_percent:.3f}%, Max diff: {self.max_vwap_diff_during_order:.3f}%, Threshold: {self.vwap_diff_threshold_percent}%")
    
    def _check_vwap_exit_condition(self) -> bool:
        """Check if VWAP difference exit condition is met"""
        if not self.vwap_diff_tracking_enabled:
            return False
        
        # Check if max VWAP difference exceeds threshold
        if self.max_vwap_diff_during_order > self.vwap_diff_threshold_percent:
            logger.info(f"VWAP exit condition triggered: Max diff {self.max_vwap_diff_during_order:.3f}% > Threshold {self.vwap_diff_threshold_percent}%")
            print(f"🚨 VWAP EXIT TRIGGER: Max diff {self.max_vwap_diff_during_order:.3f}% > {self.vwap_diff_threshold_percent}%")
            return True
        
        return False
    
    def _square_off_both_legs_vwap_exit(self):
        """Square off both CE and PE positions due to VWAP exit condition"""
        logger.info("Squaring off both legs due to VWAP exit condition")
        print(f"\n🔄 VWAP EXIT: Squaring off both legs")
        
        # Square off both positions
        squared_off_count = 0
        for option_type in ["CE", "PE"]:
            if self.positions.get(option_type) and self.positions[option_type] is not None:
                self.square_off_real_order(option_type, reason=f"VWAP_EXIT_MAX_DIFF_{self.max_vwap_diff_during_order:.2f}%")
                squared_off_count += 1
        
        if squared_off_count > 0:
            print(f"   ✅ {squared_off_count} positions squared off due to VWAP gap exit condition")
            logger.info(f"{squared_off_count} positions squared off due to VWAP gap exit condition")
        else:
            print(f"   ⚠️ No active positions to square off")
            logger.warning("VWAP gap exit triggered but no active positions found")

    def reset_api_call_tracking(self):
        """Reset API call tracking counters (called every minute)"""
        current_time = self.get_ist_time()
        time_diff = (current_time - self.api_call_tracking["last_reset_time"]).total_seconds()
        
        # Reset counters every minute
        if time_diff >= 60:
            self.api_call_tracking["quote_calls"] = 0
            self.api_call_tracking["historical_calls"] = 0
            self.api_call_tracking["last_reset_time"] = current_time
            logger.debug("API call tracking counters reset")
    
    def track_api_call(self, call_type: str):
        """Track an API call for rate limit monitoring"""
        if call_type == "quote":
            self.api_call_tracking["quote_calls"] += 1
        elif call_type == "historical":
            self.api_call_tracking["historical_calls"] += 1
        logger.debug(f"API call tracked: {call_type}, Current counts: Quote={self.api_call_tracking['quote_calls']}, Historical={self.api_call_tracking['historical_calls']}")
    
    def get_api_usage_status(self):
        """Get current API usage statistics"""
        current_time = self.get_ist_time()
        time_since_reset = (current_time - self.api_call_tracking["last_reset_time"]).total_seconds()
        
        usage_stats = {
            "quote_calls": self.api_call_tracking["quote_calls"],
            "quote_limit": 200,  # 200 per minute (Fyers API v3)
            "quote_percentage": (self.api_call_tracking["quote_calls"] / 200) * 100,
            "historical_calls": self.api_call_tracking["historical_calls"],
            "historical_limit": 200,  # 200 per minute (Fyers API v3)
            "historical_percentage": (self.api_call_tracking["historical_calls"] / 200) * 100,
            "time_since_reset": time_since_reset
        }
        
        return usage_stats
    
    def print_api_usage_status(self):
        """Print current API usage in a readable format"""
        stats = self.get_api_usage_status()
        print(f"\n📊 API USAGE STATUS")
        print(f"   Quote calls: {stats['quote_calls']}/60 ({stats['quote_percentage']:.1f}%)")
        print(f"   Historical calls: {stats['historical_calls']}/120 ({stats['historical_percentage']:.1f}%)")
        print(f"   Time since reset: {stats['time_since_reset']:.1f}s")
        
        # Warn if approaching limits
        if stats['quote_percentage'] > 80:
            print(f"   ⚠️ Quote API usage high: {stats['quote_percentage']:.1f}%")
        if stats['historical_percentage'] > 80:
            print(f"   ⚠️ Historical API usage high: {stats['historical_percentage']:.1f}%")
    
    @api_timeout(timeout_seconds=8)
    def safe_api_call(self, api_method, *args, **kwargs):
        """Make a safe API call with timeout to prevent hanging"""
        logger.debug(f"Making safe API call: {api_method.__name__}")
        try:
            result = api_method(*args, **kwargs)
            logger.debug(f"Safe API call completed: {api_method.__name__}")
            return result
        except Exception as e:
            logger.error(f"Safe API call failed: {api_method.__name__} - {e}")
            return None
    
    def setup_fyers_api(self, client_id: str, client_secret: str, redirect_uri: str = "https://www.google.com/", totp_key: str = None):
        """Setup Fyers API authentication using APIv3"""
        logger.info("Setting up Fyers API v3 authentication...")
        try:
            from fyers_apiv3 import fyersModel
            
            # Create session model for login
            session = fyersModel.SessionModel(
                client_id=client_id,
                secret_key=client_secret,
                redirect_uri=redirect_uri,
                response_type="code"
            )
            
            # Generate auth code URL
            auth_url = session.generate_authcode()
            logger.info("Auth URL generated successfully")
            print(f"Auth URL: {auth_url}")
            print("Please visit the URL, login, and get the authorization code from the redirect URL")
            
            return session
            
        except Exception as e:
            logger.error(f"Error setting up Fyers API v3: {e}")
            print(f"Error setting up Fyers API v3: {e}")
            return None
    
    def set_authorization_code(self, auth_code: str, session_instance):
        """Set authorization code and generate access token for Fyers APIv3"""
        logger.info("Setting authorization code and generating access token...")
        try:
            # Create a new session for token generation with grant_type
            token_session = fyersModel.SessionModel(
                client_id=session_instance.client_id,
                secret_key=session_instance.secret_key,
                redirect_uri=session_instance.redirect_uri,
                response_type="code",
                grant_type="authorization_code"
            )
            
            # Set the authorization code
            token_session.set_token(auth_code)
            
            # Generate access token
            response = token_session.generate_token()
            
            if response and 'access_token' in response:
                self.access_token = response['access_token']
                self.client_id = session_instance.client_id
                self.fyers = fyersModel.FyersModel(client_id=self.client_id, token=self.access_token)
                
                logger.info("Fyers API v3 authentication successful!")
                print("✅ Fyers API v3 authentication successful!")
                print(f"Access Token: {self.access_token}")
                
                # Save access token to file
                try:
                    with open('access.txt', 'w') as f:
                        f.write(self.access_token)
                    print("💾 Access token saved to access.txt")
                except Exception as e:
                    logger.warning(f"Could not save access token to file: {e}")
                
                return True
            else:
                logger.error(f"Error generating session: {response}")
                print(f"Error generating session: {response}")
                return False
                
        except Exception as e:
            logger.error(f"Error setting authorization code: {e}")
            print(f"Error setting authorization code: {e}")
            return False
        
    def get_nifty_price(self) -> Optional[float]:
        """Get current Nifty 50 price using Fyers API"""
        logger.debug("Fetching Nifty 50 price...")
        try:
            if not self.fyers:
                logger.error("Fyers API not configured. Cannot fetch live data.")
                print("❌ Fyers API not configured. Cannot fetch live data.")
                return None
                
            # Track API call
            self.track_api_call("quote")
            
            # Get live quote from Fyers API with timeout protection
            data = {"symbols": self.nifty_symbol}
            quote_response = self.safe_api_call(self.fyers.quotes, data)
            
            if not quote_response:
                logger.error("Nifty price API call timed out or failed")
                return None
            
            if quote_response and quote_response.get('s') == 'ok':
                if quote_response.get('d') and len(quote_response['d']) > 0:
                    quote_data = quote_response['d'][0]
                    if 'v' in quote_data and 'lp' in quote_data['v']:
                        current_price = quote_data['v']['lp']  # Last traded price
                        self.current_nifty_price = float(current_price)
                        logger.info(f"Nifty 50 price fetched successfully: {self.current_nifty_price}")
                        return self.current_nifty_price
                    else:
                        logger.error("Invalid quote data structure - missing price data")
                        return None
                else:
                    logger.error("Empty quote response data")
                    return None
            else:
                error_msg = quote_response.get('message', 'Unknown error') if quote_response else 'No response'
                logger.error(f"Error in Fyers quote response: {error_msg}")
                print(f"Error in Fyers quote response: {error_msg}")
                return None
                
        except Exception as e:
            logger.error(f"Error fetching Nifty price from Fyers: {e}")
            print(f"Error fetching Nifty price from Fyers: {e}")
            return None
    
    def round_to_nearest_50(self, price: float) -> int:
        """Round price to nearest 50 to get ATM strike"""
        return int(round(price / 50) * 50)
    
    def get_expiry_string_from_file(self) -> str:
        """Get expiry string from expiry_override.txt file - MUST exist or program stops"""
        expiry_override_file = "expiry_override.txt"
        
        try:
            if os.path.exists(expiry_override_file):
                # Try reading with different encodings to handle BOM
                encodings_to_try = ['utf-8-sig', 'utf-8', 'latin-1', 'cp1252']
                file_content = ""
                
                for encoding in encodings_to_try:
                    try:
                        with open(expiry_override_file, 'r', encoding=encoding) as f:
                            file_content = f.read().strip()
                        break
                    except UnicodeDecodeError:
                        continue
                
                # Accept any non-empty content (numbers/characters allowed)
                if file_content:
                    logger.info(f"Expiry string from file: {file_content}")
                    print(f"📅 Using expiry from file: {file_content}")
                    return file_content
                else:
                    error_msg = f"❌ CRITICAL ERROR: Expiry file '{expiry_override_file}' is empty!"
                    logger.critical(error_msg)
                    print(error_msg)
                    print("Program cannot continue without valid expiry string.")
                    raise ValueError(f"Empty expiry file: {expiry_override_file}")
            else:
                error_msg = f"❌ CRITICAL ERROR: Expiry file '{expiry_override_file}' not found!"
                logger.critical(error_msg)
                print(error_msg)
                print("Program cannot continue without expiry file.")
                print(f"Please create '{expiry_override_file}' with your desired expiry string (e.g., '25812' or 'AUG2025')")
                raise FileNotFoundError(f"Missing required expiry file: {expiry_override_file}")
                    
        except (ValueError, FileNotFoundError):
            # Re-raise these specific errors to stop the program
            raise
        except Exception as e:
            error_msg = f"❌ CRITICAL ERROR: Cannot read expiry file '{expiry_override_file}': {e}"
            logger.critical(error_msg)
            print(error_msg)
            print("Program cannot continue without valid expiry string.")
            raise RuntimeError(f"Error reading expiry file: {e}")
    
    
    @rate_limit_api(calls_per_second=0.9)  # Conservative limit for quote API
    def get_options_data(self, strike: int) -> Optional[Dict]:
        """Get real options data for CE and PE using Fyers API"""
        logger.debug(f"Fetching options data for strike: {strike}")
        try:
            if not self.fyers:
                logger.error("Fyers API not configured. Cannot fetch options data.")
                print("❌ Fyers API not configured. Cannot fetch options data.")
                return None
                
            # Track API call
            self.track_api_call("quote")

            # Read expiry string from file instead of calculating
            try:
                expiry_str = self.get_expiry_string_from_file()
            except (ValueError, FileNotFoundError, RuntimeError) as e:
                logger.critical(f"Cannot proceed without valid expiry: {e}")
                print(f"❌ CRITICAL: Cannot proceed without valid expiry: {e}")
                return None
            
            # Create a generic expiry_date for metadata (since we're using file-based expiry)
            today = self.get_ist_time()
            expiry_date = today  # Use today as placeholder for metadata
            
            ce_symbol = f"NSE:NIFTY{expiry_str}{strike}CE"
            pe_symbol = f"NSE:NIFTY{expiry_str}{strike}PE"
            
            if self.instrument_freeze_enabled and self.frozen_ce_symbol and self.frozen_pe_symbol:
                ce_symbol = self.frozen_ce_symbol
                pe_symbol = self.frozen_pe_symbol
                logger.debug(f"Using FROZEN symbols: CE={ce_symbol}, PE={pe_symbol}")
                print(f"🔒 Using frozen instruments: CE={ce_symbol}, PE={pe_symbol}")
            
            logger.debug(f"Constructed symbols: CE={ce_symbol}, PE={pe_symbol}")
            
            # Get quotes for both options
            symbols = [ce_symbol, pe_symbol]
            logger.debug(f"Constructed symbols: {symbols}")
            quote_data = {"symbols": f"{ce_symbol},{pe_symbol}"}
            
            print(f"Fetching quotes for: {symbols}")
            logger.info(f"Fetching quotes for: {symbols}")
            
            quotes_response = self.safe_api_call(self.fyers.quotes, quote_data)
            
            if not quotes_response:
                logger.error("Options premium API call timed out or failed")
                return None
            
            if quotes_response and quotes_response.get('s') == 'ok':
                quotes = quotes_response.get('d', [])
                if not quotes:
                    logger.error("Empty quotes data received")
                    return None
                    
                ce_price = 0
                pe_price = 0
                ce_volume = 0
                pe_volume = 0
                for quote in quotes:
                    symbol = quote.get('n', '')
                    if symbol == ce_symbol and 'v' in quote:
                        ce_price = quote['v'].get('lp', 0)  # Last price
                        ce_volume = quote['v'].get('volume', 0)  # Volume
                    elif symbol == pe_symbol and 'v' in quote:
                        pe_price = quote['v'].get('lp', 0)  # Last price
                        pe_volume = quote['v'].get('volume', 0)  # Volume

                if ce_price == 0 or pe_price == 0:
                    logger.error(f"Invalid option prices - CE: {ce_price}, PE: {pe_price}")
                    return None

                # Update current minute candle tracking
                self._update_current_minute_candle("CE", ce_price, ce_symbol)
                self._update_current_minute_candle("PE", pe_price, pe_symbol)

                options_data = {
                    "CE": ce_price,
                    "PE": pe_price,
                    "combined": ce_price + pe_price,
                    "timestamp": self.get_ist_time(),
                    "ce_symbol": ce_symbol.replace("NSE:", ""),
                    "pe_symbol": pe_symbol.replace("NSE:", ""),
                    "ce_tradingsymbol": ce_symbol,
                    "pe_tradingsymbol": pe_symbol,
                    "volume_ce": ce_volume,
                    "volume_pe": pe_volume,
                    "expiry_date": expiry_date.strftime("%Y-%m-%d"),
                    "expiry_type": "file_based"  # Since we're using file-based expiry, mark it as such
                }
                logger.info(f"Options data fetched: CE={ce_price}, PE={pe_price}, Combined={ce_price + pe_price}")
                return options_data
            else:
                error_msg = quotes_response.get('message', 'Unknown error') if quotes_response else 'No response'
                logger.error(f"Error getting options quotes: {error_msg}")
                print(f"Error getting options quotes: {error_msg}")
                return None
                
        except Exception as e:
            logger.error(f"Error fetching options data from Fyers: {e}")
            print(f"Error fetching options data from Fyers: {e}")
            return None 

    def _update_current_minute_candle(self, option_type: str, price: float, symbol: str):
        """Update current minute candle data with new price"""
        try:
            current_time = self.get_ist_time()
            current_minute = current_time.replace(second=0, microsecond=0)
            
            candle = self.current_minute_candles[option_type]
            
            # Check if we need to start a new minute candle
            if candle["minute"] != current_minute:
                # New minute - reset candle data
                candle["minute"] = current_minute
                candle["symbol"] = symbol
                candle["open"] = price
                candle["high"] = price
                candle["low"] = price
                candle["close"] = price
                logger.debug(f"Started new minute candle for {option_type} at {current_minute}: O={price:.2f}")
            else:
                # Update existing minute candle
                candle["high"] = max(candle["high"], price)
                candle["low"] = min(candle["low"], price)
                candle["close"] = price
                logger.debug(f"Updated {option_type} minute candle: H={candle['high']:.2f}, L={candle['low']:.2f}, C={price:.2f}")
                
        except Exception as e:
            logger.error(f"Error updating current minute candle for {option_type}: {e}")

    def _get_current_minute_high(self, option_type: str) -> float:
        """Get current minute candle high for trend analysis"""
        try:
            candle = self.current_minute_candles[option_type]
            if candle["high"] is not None:
                logger.debug(f"Current minute high for {option_type}: {candle['high']:.2f}")
                return candle["high"]
            else:
                logger.warning(f"No current minute data available for {option_type}")
                return 0.0
        except Exception as e:
            logger.error(f"Error getting current minute high for {option_type}: {e}")
            return 0.0

    @rate_limit_api(calls_per_second=1.8)  # Conservative limit: 108 requests/minute (under 120 limit)
    def _get_historical_data_with_rate_limit(self, symbol, from_date, to_date, resolution):
        """Rate-limited wrapper for historical data API calls with retry logic for Fyers"""
        max_retries = 3
        retry_delay = 5  # seconds
        
        for attempt in range(max_retries):
            try:
                # Track API call
                self.track_api_call("historical")
                
                # Prepare data dict for Fyers API v3
                data = {
                    "symbol": symbol,
                    "resolution": resolution,
                    "date_format": "1",
                    "range_from": from_date.strftime("%Y-%m-%d"),
                    "range_to": to_date.strftime("%Y-%m-%d"),
                    "cont_flag": "1"
                }
                
                logger.debug(f"Historical data request - Symbol: {symbol}, Data: {data}")
                result = self.safe_api_call(self.fyers.history, data)
                
                if not result:
                    logger.error(f"Historical data API call timed out or failed for {symbol}")
                    return []
                
                if result and result.get('s') == 'ok':
                    # Convert Fyers response to compatible format
                    candles = []
                    if 'candles' in result:
                        for candle in result['candles']:
                            candles.append({
                                'date': datetime.fromtimestamp(candle[0], tz=self.ist_timezone),
                                'open': candle[1],
                                'high': candle[2],
                                'low': candle[3],
                                'close': candle[4],
                                'volume': candle[5]
                            })
                    
                    logger.debug(f"Historical data fetched successfully on attempt {attempt + 1}")
                    return candles
                else:
                    error_msg = result.get('message', 'Unknown error') if result else 'No response'
                    logger.error(f"Historical data API error: {error_msg}")
                    if attempt == max_retries - 1:
                        return None
                    
            except Exception as e:
                error_msg = str(e).lower()
                if "too many requests" in error_msg or "rate limit" in error_msg:
                    if attempt < max_retries - 1:
                        logger.warning(f"Rate limit hit, retrying in {retry_delay}s (attempt {attempt + 1}/{max_retries})")
                        print(f"⚠️ Rate limit hit, waiting {retry_delay}s before retry...")
                        time.sleep(retry_delay)
                        retry_delay *= 2  # Exponential backoff
                        continue
                    else:
                        logger.error(f"Rate limit exceeded after {max_retries} attempts")
                        print(f"❌ Rate limit exceeded after {max_retries} attempts")
                        return None
                else:
                    logger.error(f"Error fetching historical data: {e}")
                    return None
        
        return None

    def check_vwap_override_file(self) -> bool:
        """Check vwap_override.txt file for VWAP override value and auto-freeze instruments"""
        try:
            if os.path.exists(self.vwap_override_file):
                # Try reading with UTF-8 encoding first, fallback to other encodings if needed
                content = ""
                encodings_to_try = ['utf-8', 'utf-8-sig', 'latin-1', 'cp1252']
                
                for encoding in encodings_to_try:
                    try:
                        with open(self.vwap_override_file, 'r', encoding=encoding) as f:
                            content = f.read().strip()
                        logger.debug(f"Successfully read file with {encoding} encoding")
                        break
                    except UnicodeDecodeError:
                        logger.debug(f"Failed to read with {encoding} encoding, trying next...")
                        continue
                    except Exception as e:
                        logger.warning(f"Error reading file with {encoding}: {e}")
                        continue
                
                # If all encodings failed, recreate the file
                if not content and content != "0":  # Empty content but not intentionally set to 0
                    logger.warning("File appears corrupted or unreadable. Recreating with default value.")
                    try:
                        with open(self.vwap_override_file, 'w', encoding='utf-8') as f:
                            f.write('0')
                        content = '0'
                        logger.info("Created new clean VWAP override file with value '0'")
                    except Exception as e:
                        logger.error(f"Failed to recreate VWAP override file: {e}")
                        return False
                
                # Clean up any non-printable characters
                content = ''.join(char for char in content if char.isprintable() or char.isspace()).strip()
                logger.debug(f"Checking VWAP override file: {self.vwap_override_file}, cleaned content: '{content}'")
                
                # Additional validation: check if content contains only digits, decimal point, and whitespace
                if content and not content.replace('.', '').replace('-', '').isdigit():
                    # Content contains invalid characters, treat as corrupted file
                    logger.warning(f"VWAP override file contains invalid characters: '{content}'. Creating clean file.")
                    # Create a clean file with '0' to reset
                    with open(self.vwap_override_file, 'w', encoding='utf-8') as f:
                        f.write('0')
                    content = '0'
                if content and content != "0" and content != "":
                    try:
                        override_value = float(content)
                        if override_value > 0:
                            # Only update if value changed to avoid repeated logs
                            if not self.vwap_override_enabled or self.vwap_override_value != override_value:
                                self.vwap_override_enabled = True
                                self.vwap_override_value = override_value
                                self.vwap_override_timestamp = self.get_ist_time()
                                
                                # 🔒 AUTO-FREEZE current instruments ONLY when override is FIRST enabled
                                if not self.instrument_freeze_enabled and self.combined_premium_data:
                                    latest_data = self.combined_premium_data[-1]
                                    self.frozen_ce_symbol = latest_data.get('ce_tradingsymbol')
                                    self.frozen_pe_symbol = latest_data.get('pe_tradingsymbol')
                                    self.instrument_freeze_enabled = True
                                    logger.info(f"📁 VWAP Override from file: {override_value:.2f}")
                                    logger.info(f"🔒 Auto-frozen instruments: CE={self.frozen_ce_symbol}, PE={self.frozen_pe_symbol}")
                                    print(f"📁 VWAP Override ENABLED from file: {override_value:.2f}")
                                    print(f"🔒 Auto-frozen current instruments")
                                elif not self.combined_premium_data:
                                    logger.info(f"📁 VWAP Override from file: {override_value:.2f} (no instruments to freeze yet)")
                                    print(f"📁 VWAP Override ENABLED from file: {override_value:.2f}")
                                else:
                                    # Override value changed but instruments already frozen - just update value
                                    logger.info(f"📁 VWAP Override updated: {override_value:.2f} (instruments remain frozen)")
                                    print(f"📁 VWAP Override UPDATED to: {override_value:.2f}")
                            return True
                        else:
                            # Value is 0 or negative, disable override and unfreeze
                            if self.vwap_override_enabled:
                                self.vwap_override_enabled = False
                                self.vwap_override_value = None
                                self.vwap_override_timestamp = None
                                # 🔓 AUTO-UNFREEZE when override is disabled
                                self.instrument_freeze_enabled = False
                                self.frozen_ce_symbol = None
                                self.frozen_pe_symbol = None
                                logger.info("📁 VWAP Override DISABLED from file (value <= 0)")
                                logger.info("🔓 Auto-unfrozen instruments")
                                print("📁 VWAP Override DISABLED from file")
                                print("🔓 Auto-unfrozen instruments")
                            return False
                    except ValueError as ve:
                        # Invalid number in file
                        logger.warning(f"ValueError parsing VWAP override file content '{content}': {ve}")
                        if self.vwap_override_enabled:
                            self.vwap_override_enabled = False
                            self.vwap_override_value = None
                            self.vwap_override_timestamp = None
                            # 🔓 AUTO-UNFREEZE on error
                            self.instrument_freeze_enabled = False
                            self.frozen_ce_symbol = None
                            self.frozen_pe_symbol = None
                            logger.warning(f"📁 VWAP Override DISABLED - Invalid value in file: '{content}'")
                            print(f"📁 VWAP Override DISABLED - Invalid value in file: '{content}'")
                        return False
                else:
                    # File is empty or contains 0
                    if self.vwap_override_enabled:
                        self.vwap_override_enabled = False
                        self.vwap_override_value = None
                        self.vwap_override_timestamp = None
                        # 🔓 AUTO-UNFREEZE when disabled
                        self.instrument_freeze_enabled = False
                        self.frozen_ce_symbol = None
                        self.frozen_pe_symbol = None
                        logger.info("📁 VWAP Override DISABLED from file (empty/0)")
                        logger.info("🔓 Auto-unfrozen instruments")
                        print("📁 VWAP Override DISABLED from file")
                        print("🔓 Auto-unfrozen instruments")
                    return False
            else:
                # File doesn't exist, disable override if it was enabled
                if self.vwap_override_enabled:
                    self.vwap_override_enabled = False
                    self.vwap_override_value = None
                    self.vwap_override_timestamp = None
                    # 🔓 AUTO-UNFREEZE when file is missing
                    self.instrument_freeze_enabled = False
                    self.frozen_ce_symbol = None
                    self.frozen_pe_symbol = None
                    logger.info("📁 VWAP Override DISABLED - File not found")
                    logger.info("🔓 Auto-unfrozen instruments")
                    print("📁 VWAP Override DISABLED - File not found")
                    print("🔓 Auto-unfrozen instruments")
                return False
                
        except Exception as e:
            logger.error(f"Error checking VWAP override file: {e}")
            return False

    def calculate_vwap(self) -> Optional[float]:
        """Calculate VWAP using Fyers historical data API for all intervals"""
        logger.debug("Calculating VWAP...")
        try:
            # 📁 Check file-based VWAP override first
            self.check_vwap_override_file()
            
            # 🎯 VWAP OVERRIDE CHECK - Return manual value if override is enabled
            if self.vwap_override_enabled and self.vwap_override_value is not None:
                logger.debug(f"Using VWAP OVERRIDE: {self.vwap_override_value:.2f} (set at {self.vwap_override_timestamp})")
                return self.vwap_override_value
            
            if not self.combined_premium_data:
                logger.warning("VWAP calculation skipped: No premium data")
                return None
            
            # For all intervals (including 1-minute), only fetch historical data at interval boundaries
            if not self.should_fetch_interval_data():
                # Use cached interval data if available
                if self.current_vwap is not None:
                    logger.debug(f"Using cached VWAP: {self.current_vwap:.2f} (not at interval boundary)")
                    return self.current_vwap
                else:
                    logger.debug("No cached VWAP available and not at interval boundary")
                    return None
            
            # We're at an interval boundary, fetch fresh historical data
            if not self.fyers:
                logger.warning("VWAP calculation skipped: No Fyers API for historical data")
                return None
                
            # Get the latest option symbols
            latest_data = self.combined_premium_data[-1]
            ce_symbol = latest_data.get('ce_tradingsymbol')
            pe_symbol = latest_data.get('pe_tradingsymbol')
            
            # Ensure symbols have proper NSE: prefix for historical data API
            if ce_symbol and not ce_symbol.startswith('NSE:'):
                ce_symbol = f"NSE:{ce_symbol}"
            if pe_symbol and not pe_symbol.startswith('NSE:'):
                pe_symbol = f"NSE:{pe_symbol}"
            
            if not ce_symbol or not pe_symbol:
                logger.error("Missing trading symbols for VWAP calculation")
                return self.current_vwap
            
            logger.info(f"Fetching {self.decision_interval} historical data at boundary for VWAP: CE={ce_symbol}, PE={pe_symbol}")

            today = self.get_ist_time()
            from_date = today.replace(hour=9, minute=15, second=0, microsecond=0)
            to_date = self.get_ist_time()
            
            # Convert interval to Fyers format
            fyers_resolution = self._convert_interval_to_fyers_resolution(self.decision_interval)
            
            # Fetch intraday historical data for both options
            try:
                ce_historical = self._get_historical_data_with_rate_limit(
                    symbol=ce_symbol,
                    from_date=from_date,
                    to_date=to_date,
                    resolution=fyers_resolution
                )
                
                pe_historical = self._get_historical_data_with_rate_limit(
                    symbol=pe_symbol,
                    from_date=from_date,
                    to_date=to_date,
                    resolution=fyers_resolution
                )
                
                if not ce_historical or not pe_historical:
                    logger.warning("No historical data available for VWAP calculation")
                    return self.current_vwap  # Return cached value if available
                
                # Calculate combined VWAP
                total_pv = 0  # Price * Volume
                total_volume = 0
                
                min_length = min(len(ce_historical), len(pe_historical))
                logger.info(f"Processing {min_length} {self.decision_interval} candles for VWAP calculation")
                
                for i in range(min_length):
                    ce_candle = ce_historical[i]
                    pe_candle = pe_historical[i]
                    
                    # Combined typical price (High + Low + Close) / 3
                    ce_typical = (ce_candle['high'] + ce_candle['low'] + ce_candle['close']) / 3
                    pe_typical = (pe_candle['high'] + pe_candle['low'] + pe_candle['close']) / 3
                    combined_typical = ce_typical + pe_typical
                    
                    # Combined volume
                    combined_volume = ce_candle['volume'] + pe_candle['volume']
                    
                    total_pv += combined_typical * combined_volume
                    total_volume += combined_volume
                
                if total_volume > 0:
                    vwap = total_pv / total_volume
                    
                    # Update fetch time and cache the result
                    self.last_interval_fetch_time = self.get_ist_time()
                    
                    logger.info(f"VWAP calculated at {self.decision_interval} boundary: {vwap:.2f}")
                    print(f"📊 {self.decision_interval} VWAP updated: {vwap:.2f}")
                    return vwap
                else:
                    logger.warning("VWAP calculation failed: Zero total volume")
                    return self.current_vwap  # Return cached value if available
                    
            except Exception as e:
                logger.error(f"Error fetching historical data: {e}")
                print(f"Error fetching historical data: {e}")
                return self.current_vwap  # Return cached value if available
                
        except Exception as e:
            logger.error(f"Error calculating VWAP: {e}")
            print(f"Error calculating VWAP: {e}")
            return self.current_vwap  # Return cached value if available
    
    def calculate_market_vwap_for_display(self) -> Optional[float]:
        """Calculate actual market VWAP for display purposes - always calculates regardless of override"""
        logger.debug("Calculating market VWAP for display...")
        try:
            if not self.combined_premium_data:
                logger.warning("Market VWAP calculation skipped: No premium data")
                return None
            
            # For display VWAP, we can be more flexible with timing
            # Calculate at interval boundaries or if we don't have cached data
            if not self.should_fetch_interval_data() and self.current_market_vwap is not None:
                logger.debug(f"Using cached market VWAP: {self.current_market_vwap:.2f}")
                return self.current_market_vwap
            
            if not self.fyers:
                logger.warning("Market VWAP calculation skipped: No Fyers API")
                return None
                
            # Get the latest option symbols
            latest_data = self.combined_premium_data[-1]
            ce_symbol = latest_data.get('ce_tradingsymbol')
            pe_symbol = latest_data.get('pe_tradingsymbol')
            
            # Ensure symbols have proper NSE: prefix for historical data API
            if ce_symbol and not ce_symbol.startswith('NSE:'):
                ce_symbol = f"NSE:{ce_symbol}"
            if pe_symbol and not pe_symbol.startswith('NSE:'):
                pe_symbol = f"NSE:{pe_symbol}"
            
            if not ce_symbol or not pe_symbol:
                logger.error("Missing trading symbols for market VWAP calculation")
                return self.current_market_vwap
            
            logger.info(f"Fetching {self.decision_interval} historical data for display VWAP: CE={ce_symbol}, PE={pe_symbol}")

            today = self.get_ist_time()
            from_date = today.replace(hour=9, minute=15, second=0, microsecond=0)
            to_date = self.get_ist_time()
            
            # Convert interval to Fyers format
            fyers_resolution = self._convert_interval_to_fyers_resolution(self.decision_interval)
            
            # Fetch intraday historical data for both options
            try:
                ce_historical = self._get_historical_data_with_rate_limit(
                    symbol=ce_symbol,
                    from_date=from_date,
                    to_date=to_date,
                    resolution=fyers_resolution
                )
                
                pe_historical = self._get_historical_data_with_rate_limit(
                    symbol=pe_symbol,
                    from_date=from_date,
                    to_date=to_date,
                    resolution=fyers_resolution
                )
                
                if not ce_historical or not pe_historical:
                    logger.warning("No historical data available for market VWAP calculation")
                    return self.current_market_vwap
                
                # Calculate combined VWAP
                total_pv = 0  # Price * Volume
                total_volume = 0
                
                min_length = min(len(ce_historical), len(pe_historical))
                logger.info(f"Processing {min_length} {self.decision_interval} candles for market VWAP calculation")
                
                for i in range(min_length):
                    ce_candle = ce_historical[i]
                    pe_candle = pe_historical[i]
                    
                    # Combined typical price (High + Low + Close) / 3
                    ce_typical = (ce_candle['high'] + ce_candle['low'] + ce_candle['close']) / 3
                    pe_typical = (pe_candle['high'] + pe_candle['low'] + pe_candle['close']) / 3
                    combined_typical = ce_typical + pe_typical
                    
                    # Combined volume
                    combined_volume = ce_candle['volume'] + pe_candle['volume']
                    
                    total_pv += combined_typical * combined_volume
                    total_volume += combined_volume
                
                if total_volume > 0:
                    market_vwap = total_pv / total_volume
                    
                    # Cache the result
                    self.current_market_vwap = market_vwap
                    
                    logger.info(f"Market VWAP calculated for display: {market_vwap:.2f}")
                    print(f"📊 Market VWAP (Display): {market_vwap:.2f}")
                    return market_vwap
                else:
                    logger.warning("Market VWAP calculation failed: Zero total volume")
                    return self.current_market_vwap
                    
            except Exception as e:
                logger.error(f"Error fetching historical data for market VWAP: {e}")
                return self.current_market_vwap
                
        except Exception as e:
            logger.error(f"Error calculating market VWAP: {e}")
            return self.current_market_vwap
    
    def _convert_interval_to_fyers_resolution(self, interval: str) -> str:
        """Convert interval string to Fyers resolution format"""
        interval_map = {
            "5second": "5S",
            "10second": "10S",
            "15second": "15S",
            "30second": "30S",
            "1minute": "1",
            "3minute": "3", 
            "5minute": "5",
            "10minute": "10",
            "15minute": "15",
            "30minute": "30"
        }
        return interval_map.get(interval, "5")  # Default to 5 minutes
    
    def _create_order_params(self, symbol: str, transaction_type: str, quantity: int = 75) -> dict:
        """Create standardized order parameters for Fyers API v3"""
        # Create alphanumeric-only order tag
        symbol_clean = ''.join(c for c in symbol if c.isalnum())  # Remove special characters
        order_tag = f"{transaction_type}{symbol_clean}"[:20]  # Limit to 20 chars and make alphanumeric
        
        return {
            "symbol": symbol,  # Full symbol with NSE: prefix for Fyers API v3
            "qty": quantity,
            "type": 2,  # 2 = Market Order
            "side": -1 if transaction_type == "SELL" else 1,  # -1 = Sell, 1 = Buy
            "productType": "MARGIN",
            "limitPrice": 0,
            "stopPrice": 0,
            "validity": "DAY",
            "disclosedQty": 0,
            "offlineOrder": False,
            "orderTag": order_tag
        }
    
    def place_real_order(self, option_type: str, action: str = "SELL") -> str:
        """Place a real order using Fyers API"""
        current_time = self.get_ist_time()
        strike = self.current_atm_strike
        
        logger.info(f"Placing REAL {action} order for {option_type} at strike {strike}")
        print(f"\n🔥 REAL ORDER PLACED at {current_time.strftime('%H:%M:%S')}")
        logger.info(f"REAL ORDER PLACED at {current_time.strftime('%H:%M:%S')}")
        print(f"   Type: {action} {option_type}")
        logger.info(f"Type: {action} {option_type}")
        print(f"   Strike: {strike}")
        logger.info(f"Strike: {strike}")
        print(f"   Nifty Price: {self.current_nifty_price:.2f}")
        logger.info(f"Nifty Price: {self.current_nifty_price:.2f}")
        
        if not self.combined_premium_data:
            logger.error("No options data available for real order placement.")
            print("❌ No options data available.")
            return "ERROR"
        
        if not self.fyers:
            logger.error("Fyers API not configured. Cannot place real orders.")
            print("❌ Fyers API not configured.")
            return "ERROR"
        
        latest_data = self.combined_premium_data[-1]
        individual_entry_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
        symbol = latest_data['ce_tradingsymbol'] if option_type == "CE" else latest_data['pe_tradingsymbol']
        
        try:
            # Create order parameters
            order_params = self._create_order_params(symbol, action, 75)
            
            logger.debug(f"Order parameters: {order_params}")
            print(f"   Symbol: {symbol}")
            print(f"   Entry Price: {individual_entry_price:.2f}")
            
            # Track order attempt for UI display
            order_index = self._track_order_attempt(option_type, action, symbol, individual_entry_price, order_params)
            
            # Place real order through Fyers API with timeout protection
            order_response = self.safe_api_call(self.fyers.place_order, data=order_params)
            
            if not order_response or order_response.get('s') != 'ok':
                # Extract detailed error information
                error_code = order_response.get('code') if order_response else None
                fyers_message = order_response.get('message', 'No response from API') if order_response else 'No response from API'
                error_msg = f"Order placement failed - Code: {error_code}, Message: {fyers_message}"
                
                # DISABLE TRADING FOR ANY ORDER PLACEMENT FAILURE
                self.trading_disabled = True
                self.trading_disabled_reason = f"Order placement failed: {fyers_message}"
                
                # Log the trading suspension
                logger.error(f"🛑 TRADING DISABLED DUE TO ORDER PLACEMENT FAILURE")
                logger.error(f"🛑 Error Code: {error_code}")
                logger.error(f"🛑 Error Message: {fyers_message}")
                logger.error(f"🛑 Click 'Reset Trading Cycle' to resume trading")
                
                print(f"\n🛑 TRADING DISABLED DUE TO ORDER PLACEMENT FAILURE")
                print(f"🛑 Error Code: {error_code}")
                print(f"🛑 Error Message: {fyers_message}")
                print(f"🛑 System will stop placing new orders")
                print(f"🛑 Click 'Reset Trading Cycle' in UI to resume trading")
                
                # Track the failure with detailed information
                self._track_order_failure(order_index, order_response, error_msg)
                
                logger.error(error_msg)
                print(f"❌ {error_msg}")
                print(f"❌ Order rejection recorded for UI display")
                return "ERROR"
            
            order_id = order_response.get('id', 'UNKNOWN')
            
            # Track the success
            self._track_order_success(order_index, order_id, order_response)
            
            # Create real order record for existing system
            real_order = {
                "order_id": order_id,
                "option_type": option_type,
                "action": action,
                "strike": strike,
                "entry_price": individual_entry_price,
                "combined_entry_price": latest_data['combined'],
                "entry_time": current_time,
                "quantity": 75,
                "status": "PLACED",
                "tradingsymbol": symbol.replace("NSE:", ""),
                "expiry_date": latest_data.get('expiry_date', 'N/A'),
                "expiry_type": latest_data.get('expiry_type', 'N/A')
            }
            
            # Store in all_orders list for existing tracking
            self.all_orders.append(real_order)
            
            # Export order data to Excel
            self._export_order_to_excel(real_order)
            
            print(f"   Combined Premium: {latest_data['combined']:.2f}")
            logger.info(f"Combined Premium: {latest_data['combined']:.2f}")
            current_vwap_display = f"{self.current_vwap:.2f}" if self.current_vwap is not None else "Not calculated"
            print(f"   Current VWAP: {current_vwap_display}")
            logger.info(f"Current VWAP: {current_vwap_display}")
            print(f"   ✅ Real order placed successfully!")
            logger.info(f"Real order placed successfully!")
            print(f"   Real Order ID: {order_id}")
            logger.info(f"Real Order ID: {order_id}")
            print(f"   📊 Order success recorded for UI display")
            
            return order_id
            
        except Exception as e:
            error_msg = f"Exception during order placement: {str(e)}"
            
            # Track the exception as failure if we have order_index
            try:
                if 'order_index' in locals():
                    self._track_order_failure(order_index, None, error_msg)
            except:
                pass
            
            logger.error(error_msg)
            print(f"❌ {error_msg}")
            print(f"❌ Order exception recorded for UI display")
            return "ERROR"
    
    def square_off_real_order(self, option_type: str, reason: str = "Manual Exit"):
        """Square off a real order using Fyers API"""
        current_time = self.get_ist_time()
        
        logger.debug(f"square_off_real_order called with option_type={option_type}, reason='{reason}'")
        
        if not self.positions.get(option_type) or self.positions[option_type] is None:
            logger.warning(f"No {option_type} position to square off")
            print(f"❌ No {option_type} position to square off")
            return
        
        position = self.positions[option_type]
        if position is None:
            logger.warning(f"Position {option_type} is None, cannot square off")
            print(f"❌ Position {option_type} is None, cannot square off")
            return
        
        if not self.combined_premium_data:
            logger.error("No current market data for square off")
            print("❌ No current market data for square off")
            return
        
        if not self.fyers:
            logger.error("Fyers API not configured. Cannot square off real orders.")
            print("❌ Fyers API not configured.")
            return
        
        latest_data = self.combined_premium_data[-1]
        symbol = latest_data['ce_tradingsymbol'] if option_type == "CE" else latest_data['pe_tradingsymbol']
        
        try:
            # Determine opposite transaction type for square off
            original_action = position.get('action', 'SELL')
            square_off_action = "BUY" if original_action == "SELL" else "SELL"
            
            # Create square off order parameters
            order_params = self._create_order_params(symbol, square_off_action, 75)
            
            logger.info(f"Squaring off REAL {option_type} position")
            print(f"\n🔄 REAL SQUARE OFF - {option_type} at {current_time.strftime('%H:%M:%S')}")
            logger.info(f"REAL SQUARE OFF - {option_type} at {current_time.strftime('%H:%M:%S')}")
            print(f"   Reason: {reason}")
            logger.info(f"Reason: {reason}")
            print(f"   Symbol: {symbol}")
            print(f"   Action: {square_off_action}")
            
            # Place square off order through Fyers API with timeout protection
            order_response = self.safe_api_call(self.fyers.place_order, data=order_params)
            
            if not order_response or order_response.get('s') != 'ok':
                # Extract error details
                error_code = order_response.get('code') if order_response else None
                fyers_message = order_response.get('message', 'No response from API') if order_response else 'No response from API'
                
                # DISABLE TRADING FOR ANY SQUARE OFF ORDER PLACEMENT FAILURE
                self.trading_disabled = True
                self.trading_disabled_reason = f"Square off order placement failed: {fyers_message}"
                
                error_msg = f"Real square off order placement failed: {order_response}"
                logger.error(f"🛑 TRADING DISABLED DUE TO SQUARE OFF ORDER FAILURE")
                logger.error(f"🛑 {error_msg}")
                logger.error(f"🛑 Click 'Reset Trading Cycle' to resume trading")
                print(f"\n🛑 TRADING DISABLED DUE TO SQUARE OFF ORDER FAILURE")
                print(f"❌ {error_msg}")
                print(f"🛑 Click 'Reset Trading Cycle' in UI to resume trading")
                return
            
            square_off_order_id = order_response.get('id', 'UNKNOWN')
            
            # Get market prices for P&L calculation
            exit_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
            entry_price = position['entry_price']
            
            # Calculate P&L (for short positions, profit when exit price < entry price)
            if original_action == "SELL":
                pnl = (entry_price - exit_price) * 75  # 75 is lot size
            else:
                pnl = (exit_price - entry_price) * 75
            
            print(f"   Entry Price: {entry_price:.2f}")
            logger.info(f"Entry Price: {entry_price:.2f}")
            print(f"   Exit Price: {exit_price:.2f}")
            logger.info(f"Exit Price: {exit_price:.2f}")
            print(f"   P&L: {pnl:.2f}")
            logger.info(f"P&L: {pnl:.2f}")
            
            # Update trading portfolio (used for both real and virtual trading)
            self.trading_portfolio["total_pnl"] += pnl
            self.trading_portfolio["total_trades"] += 1
            if pnl > 0:
                self.trading_portfolio["winning_trades"] += 1
                print(f"     ✅ PROFIT: {pnl:.2f}")
                logger.info(f"PROFIT: {pnl:.2f}")
            else:
                self.trading_portfolio["losing_trades"] += 1
                print(f"   📉 LOSS: {pnl:.2f}")
                logger.info(f"LOSS: {pnl:.2f}")
            
            # Create square off record
            square_off_record = {
                "original_order_id": position.get('order_id', 'N/A'),
                "square_off_order_id": square_off_order_id,
                "option_type": option_type,
                "entry_price": entry_price,
                "exit_price": exit_price,
                "pnl": pnl,
                "exit_time": current_time,
                "reason": reason,
                "duration_minutes": (current_time - position['timestamp']).total_seconds() / 60,
                "entry_time": position['timestamp'],
                "action": original_action,
                "strike": position.get('strike', self.current_atm_strike),
                "quantity": 75,
                "nifty_entry": self.current_nifty_price,
                "vwap_entry": self.current_vwap,
                "combined_entry_price": position.get('combined_entry_price', 0),
                "tradingsymbol": position.get('tradingsymbol', 'N/A'),
                "expiry_date": 'N/A',
            }
            
            # Export trade data to Excel
            self._export_trade_to_excel(square_off_record)
            
            # Update order record in all_orders list
            for order in self.all_orders:
                if order['order_id'] == position.get('order_id') and order['option_type'] == option_type:
                    order['exit_price'] = exit_price
                    order['pnl'] = pnl
                    order['exit_time'] = current_time
                    order['status'] = 'SQUARED_OFF'
                    order['square_off_order_id'] = square_off_order_id
                    break
            
            # Clear position
            self.positions[option_type] = None
            
            # Check if both positions are now closed, if so reset VWAP tracking
            if self.positions["CE"] is None and self.positions["PE"] is None:
                self._reset_vwap_diff_tracking()
                print(f"   📊 All positions closed - VWAP difference tracking reset")
                logger.info(f"All positions closed - VWAP difference tracking reset")
            
            print(f"   ✅ Real square off completed")
            print(f"   Square Off Order ID: {square_off_order_id}")
            logger.info(f"Real square off completed - Order ID: {square_off_order_id}")
            
            return square_off_record
            
        except Exception as e:
            error_msg = f"Error in real square off: {e}"
            logger.error(error_msg)
            print(f"❌ {error_msg}")
            return None
    
    def enhanced_square_off_with_real_directional_trade(self, option_type: str, reason: str = "VWAP Rising Exit"):
        """Enhanced square off: Buy 150 qty instead of 75 qty to create directional long position using real orders"""
        current_time = self.get_ist_time()
        
        if not self.positions.get(option_type) or self.positions[option_type] is None:
            logger.warning(f"No {option_type} position to square off")
            print(f"❌ No {option_type} position to square off")
            return
        
        position = self.positions[option_type]
        if position is None:
            logger.warning(f"Position {option_type} is None, cannot square off")
            print(f"❌ Position {option_type} is None, cannot square off")
            return
        
        if not self.combined_premium_data:
            logger.error("No current market data for enhanced square off")
            print("❌ No current market data for enhanced square off")
            return
        
        if not self.fyers:
            logger.error("Fyers API not configured. Cannot place enhanced real orders.")
            print("❌ Fyers API not configured.")
            return
        
        latest_data = self.combined_premium_data[-1]
        symbol = latest_data['ce_tradingsymbol'] if option_type == "CE" else latest_data['pe_tradingsymbol']
        entry_price = position['entry_price']
        
        try:
            logger.info(f"Enhanced square off REAL {option_type} position with directional trade")
            print(f"\n🚀 ENHANCED REAL SQUARE OFF + DIRECTIONAL TRADE - {option_type} at {current_time.strftime('%H:%M:%S')}")
            logger.info(f"ENHANCED REAL SQUARE OFF + DIRECTIONAL TRADE - {option_type} at {current_time.strftime('%H:%M:%S')}")
            print(f"   Reason: {reason}")
            logger.info(f"Reason: {reason}")
            print(f"   Strategy: BUY 150 qty (75 close + 75 new long)")
            logger.info(f"Strategy: BUY 150 qty (75 close + 75 new long)")
            print(f"   Symbol: {symbol}")
            
            # Determine transaction type - we need to BUY 150 qty (square off 75 + new long 75)
            original_action = position.get('action', 'SELL')
            
            # Place order for 150 qty to square off existing 75 and create new long 75
            order_params = self._create_order_params(symbol, "BUY", 150)
            
            logger.debug(f"Enhanced order parameters: {order_params}")
            
            # Place the enhanced order through Fyers API with timeout protection
            order_response = self.safe_api_call(self.fyers.place_order, data=order_params)
            
            if not order_response or order_response.get('s') != 'ok':
                # Extract error details
                error_code = order_response.get('code') if order_response else None
                fyers_message = order_response.get('message', 'No response from API') if order_response else 'No response from API'
                
                # DISABLE TRADING FOR ANY ENHANCED ORDER PLACEMENT FAILURE
                self.trading_disabled = True
                self.trading_disabled_reason = f"Enhanced square off order placement failed: {fyers_message}"
                
                error_msg = f"Enhanced square off order placement failed: {order_response}"
                logger.error(f"🛑 TRADING DISABLED DUE TO ENHANCED ORDER FAILURE")
                logger.error(f"🛑 {error_msg}")
                logger.error(f"🛑 Click 'Reset Trading Cycle' to resume trading")
                print(f"\n🛑 TRADING DISABLED DUE TO ENHANCED ORDER FAILURE")
                print(f"❌ {error_msg}")
                print(f"🛑 Click 'Reset Trading Cycle' in UI to resume trading")
                return
            
            enhanced_order_id = order_response.get('id', 'UNKNOWN')
            
            # Get market prices for P&L calculation
            exit_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
            
            # Calculate P&L for the original short position (75 qty)
            if original_action == "SELL":
                short_pnl = (entry_price - exit_price) * 75  # 75 is lot size for closing
            else:
                short_pnl = (exit_price - entry_price) * 75
            
            print(f"   Original Short Position:")
            print(f"     Entry Price: {entry_price:.2f}")
            print(f"     Exit Price: {exit_price:.2f}")
            print(f"     Short P&L: {short_pnl:.2f}")
            logger.info(f"Original Short - Entry: {entry_price:.2f}, Exit: {exit_price:.2f}, P&L: {short_pnl:.2f}")
            
            # Update virtual portfolio with short position P&L (reusing existing structure for tracking)
            self.trading_portfolio["total_pnl"] += short_pnl
            self.trading_portfolio["total_trades"] += 1
            if short_pnl > 0:
                self.trading_portfolio["winning_trades"] += 1
                print(f"     ✅ Short PROFIT: {short_pnl:.2f}")
                logger.info(f"Short PROFIT: {short_pnl:.2f}")
            else:
                self.trading_portfolio["losing_trades"] += 1
                print(f"     📉 Short LOSS: {short_pnl:.2f}")
                logger.info(f"Short LOSS: {short_pnl:.2f}")
            
            # Create square off record for the short position
            square_off_record = {
                "original_order_id": position.get('order_id', 'N/A'),
                "enhanced_order_id": enhanced_order_id,
                "option_type": option_type,
                "entry_price": entry_price,
                "exit_price": exit_price,
                "pnl": short_pnl,
                "exit_time": current_time,
                "reason": reason,
                "duration_minutes": (current_time - position['timestamp']).total_seconds() / 60,
                "entry_time": position['timestamp'],
                "action": original_action,
                "strike": position.get('strike', self.current_atm_strike),
                "quantity": 75,
                "nifty_entry": self.current_nifty_price,
                "vwap_entry": self.current_vwap,
                "combined_entry_price": position.get('combined_entry_price', 0),
                "tradingsymbol": position.get('tradingsymbol', 'N/A'),
                "expiry_date": 'N/A',
                "trade_type": "ENHANCED_SQUARE_OFF"
            }
            
            # Export trade data to Excel
            self._export_trade_to_excel(square_off_record)
            
            # Update order record in all_orders list for the square off
            for order in self.all_orders:
                if order['order_id'] == position.get('order_id') and order['option_type'] == option_type:
                    order['exit_price'] = exit_price
                    order['pnl'] = short_pnl
                    order['exit_time'] = current_time
                    order['status'] = 'ENHANCED_SQUARED_OFF'
                    order['enhanced_order_id'] = enhanced_order_id
                    break
            
            # Create NEW LONG POSITION (the additional 75 qty)
            print(f"   New Long Position:")
            print(f"     Entry Price: {exit_price:.2f}")
            print(f"     Quantity: 75 (LONG)")
            print(f"     Strategy: Monitor for lower wick exit")
            logger.info(f"New Long - Entry: {exit_price:.2f}, Qty: 75 LONG")
            
            # Generate order ID for tracking the long position
            long_order_id = f"LONG_{option_type}_{current_time.strftime('%H%M%S')}"
            
            # Create virtual order record for the long position (for tracking purposes)
            long_order = {
                "order_id": long_order_id,
                "option_type": option_type,
                "action": "BUY",
                "strike": self.current_atm_strike,
                "entry_price": exit_price,
                "combined_entry_price": latest_data['combined'],
                "entry_time": current_time,
                "quantity": 75,
                "status": "FILLED",
                "tradingsymbol": symbol.replace("NSE:", ""),
                "expiry_date": latest_data.get('expiry_date', 'N/A'),
                "expiry_type": latest_data.get('expiry_type', 'N/A'),
                "trade_type": "DIRECTIONAL_LONG",
                "enhanced_order_id": enhanced_order_id
            }
            
            self.all_orders.append(long_order)
            
            # Export long order data to Excel
            self._export_order_to_excel(long_order)
            
            # Store long position information
            self.long_positions[option_type] = {
                "strike": self.current_atm_strike,
                "action": "BUY",
                "timestamp": current_time,
                "entry_price": exit_price,
                "combined_entry_price": latest_data['combined'],
                "order_id": long_order_id,
                "tradingsymbol": symbol.replace("NSE:", ""),
                "original_short_exit_reason": reason,
                "enhanced_order_id": enhanced_order_id
            }
            
            # Clear the original short position
            self.positions[option_type] = None
            
            print(f"   📊 Enhanced square off completed:")
            print(f"     ✅ Short position closed with P&L: {short_pnl:.2f}")
            print(f"     🎯 New long position created: {option_type} @ {exit_price:.2f}")
            print(f"     🔍 Monitoring for lower wick exit signals")
            print(f"   Enhanced Order ID: {enhanced_order_id}")
            logger.info(f"Enhanced square off completed - Short P&L: {short_pnl:.2f}, Long entry: {exit_price:.2f}, Order ID: {enhanced_order_id}")
            
            return square_off_record
            
        except Exception as e:
            error_msg = f"Error in enhanced real square off: {e}"
            logger.error(error_msg)
            print(f"❌ {error_msg}")
            return None
    
    def enhanced_square_off_with_directional_trade(self, option_type: str, reason: str = "VWAP Rising Exit"):
        """Enhanced square off: Buy 150 qty instead of 75 qty to create directional long position"""
        current_time = self.get_ist_time()
        
        if not self.positions.get(option_type) or self.positions[option_type] is None:
            logger.warning(f"No {option_type} position to square off")
            print(f"❌ No {option_type} position to square off")
            return
        
        position = self.positions[option_type]
        if position is None:
            logger.warning(f"Position {option_type} is None, cannot square off")
            print(f"❌ Position {option_type} is None, cannot square off")
            return
        
        if not self.combined_premium_data:
            logger.error("No current market data for enhanced square off")
            print("❌ No current market data for enhanced square off")
            return
        
        latest_data = self.combined_premium_data[-1]
        exit_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
        entry_price = position['entry_price']
        
        logger.info(f"Enhanced square off REAL {option_type} position with directional trade")
        print(f"\n🚀 ENHANCED REAL SQUARE OFF + DIRECTIONAL TRADE - {option_type} at {current_time.strftime('%H:%M:%S')}")
        logger.info(f"ENHANCED REAL SQUARE OFF + DIRECTIONAL TRADE - {option_type} at {current_time.strftime('%H:%M:%S')}")
        print(f"   Reason: {reason}")
        logger.info(f"Reason: {reason}")
        print(f"   Strategy: BUY 150 qty (75 close + 75 new long)")
        logger.info(f"Strategy: BUY 150 qty (75 close + 75 new long)")
        
        # Calculate P&L for the original short position (75 qty)
        if position['action'] == "SELL":
            short_pnl = (entry_price - exit_price) * 75  # 75 is lot size for closing
        else:
            short_pnl = (exit_price - entry_price) * 75
        
        print(f"   Original Short Position:")
        print(f"     Entry Price: {entry_price:.2f}")
        print(f"     Exit Price: {exit_price:.2f}")
        print(f"     Short P&L: {short_pnl:.2f}")
        logger.info(f"Original Short - Entry: {entry_price:.2f}, Exit: {exit_price:.2f}, P&L: {short_pnl:.2f}")
        
        # Update virtual portfolio with short position P&L
        self.trading_portfolio["total_pnl"] += short_pnl
        self.trading_portfolio["total_trades"] += 1
        if short_pnl > 0:
            self.trading_portfolio["winning_trades"] += 1
            print(f"     ✅ Short PROFIT: {short_pnl:.2f}")
            logger.info(f"Short PROFIT: {short_pnl:.2f}")
        else:
            self.trading_portfolio["losing_trades"] += 1
            print(f"     📉 Short LOSS: {short_pnl:.2f}")
            logger.info(f"Short LOSS: {short_pnl:.2f}")
        
        # Create square off record for the short position
        square_off_record = {
            "original_order_id": position.get('order_id', 'N/A'),
            "option_type": option_type,
            "entry_price": entry_price,
            "exit_price": exit_price,
            "pnl": short_pnl,
            "exit_time": current_time,
            "reason": reason,
            "duration_minutes": (current_time - position['timestamp']).total_seconds() / 60,
            "entry_time": position['timestamp'],
            "action": position.get('action', 'SELL'),
            "strike": position.get('strike', self.current_atm_strike),
            "quantity": 75,
            "nifty_entry": self.current_nifty_price,
            "vwap_entry": self.current_vwap,
            "combined_entry_price": position.get('combined_entry_price', 0),
            "tradingsymbol": position.get('tradingsymbol', 'N/A'),
            "expiry_date": 'N/A',
            "trade_type": "ENHANCED_SQUARE_OFF"
        }
        
        # Export trade data to Excel immediately
        self._export_trade_to_excel(square_off_record)
        
        # Update virtual order record for square off
        for order in self.all_orders:
            if order['order_id'] == position.get('order_id') and order['option_type'] == option_type:
                order['exit_time'] = current_time
                order['exit_price'] = exit_price
                order['pnl'] = short_pnl
                order['exit_reason'] = reason
                break
        
        # Create NEW LONG POSITION (the additional 75 qty)
        print(f"   New Long Position:")
        print(f"     Entry Price: {exit_price:.2f}")
        print(f"     Quantity: 75 (LONG)")
        print(f"     Strategy: Monitor for lower wick exit")
        logger.info(f"New Long - Entry: {exit_price:.2f}, Qty: 75 LONG")
        
        # Get symbol for the option
        symbol = latest_data['ce_tradingsymbol'] if option_type == "CE" else latest_data['pe_tradingsymbol']
        
        # Place REAL order for long position (Buy 75 qty)
        try:
            buy_order_params = {
                "symbol": symbol,
                "qty": 75,  # Buy 75 qty for long position
                "type": 2,  # Market order
                "side": 1,  # Buy
                "productType": "MARGIN",
                "limitPrice": 0,
                "stopPrice": 0,
                "validity": "DAY",
                "disclosedQty": 0,
                "offlineOrder": False
            }
            
            logger.debug(f"Enhanced BUY order parameters: {buy_order_params}")
            long_order_id = self.safe_api_call(self.fyers.place_order, **buy_order_params)
            
            if long_order_id:
                print(f"   ✅ Long position order placed! Order ID: {long_order_id}")
                logger.info(f"Long position order placed successfully! Order ID: {long_order_id}")
                
                # Create real order record for the long position
                long_order_record = {
                    "order_id": long_order_id,
                    "option_type": option_type,
                    "action": "BUY",
                    "strike": self.current_atm_strike,
                    "entry_price": exit_price,
                    "combined_entry_price": latest_data['combined'],
                    "entry_time": current_time,
                    "quantity": 75,
                    "status": "FILLED",
                    "tradingsymbol": symbol,
                    "expiry_date": latest_data.get('expiry_date', 'N/A'),
                    "expiry_type": latest_data.get('expiry_type', 'N/A'),
                    "trade_type": "DIRECTIONAL_LONG"
                }
                
                self.all_orders.append(long_order_record)
                self._export_order_to_excel(long_order_record)
                
            else:
                logger.error("Enhanced BUY order placement failed - no order ID returned")
                print(f"   ❌ Long position order placement failed")
                long_order_id = "FAILED"
                
        except Exception as e:
            logger.error(f"Error placing enhanced BUY order for {option_type}: {e}")
            print(f"   ❌ Error placing long position order: {e}")
            long_order_id = "ERROR"
        
        # Store long position information only if order was successful
        if long_order_id and long_order_id not in ["FAILED", "ERROR"]:
            self.long_positions[option_type] = {
                "strike": self.current_atm_strike,
                "action": "BUY",
                "timestamp": current_time,
                "entry_price": exit_price,
                "combined_entry_price": latest_data['combined'],
                "order_id": long_order_id,
                "tradingsymbol": symbol,
                "original_short_exit_reason": reason
            }
        
        # Clear the original short position
        self.positions[option_type] = None
        
        print(f"   📊 Enhanced square off completed:")
        print(f"     ✅ Short position closed with P&L: {short_pnl:.2f}")
        print(f"     🎯 New long position created: {option_type} @ {exit_price:.2f}")
        print(f"     🔍 Monitoring for lower wick exit signals")
        logger.info(f"Enhanced square off completed - Short P&L: {short_pnl:.2f}, Long entry: {exit_price:.2f}")
        
        return square_off_record
    
    def square_off_real_long_position(self, option_type: str, reason: str = "Lower Wick Exit"):
        """Square off a real long position created by enhanced strategy"""
        current_time = self.get_ist_time()
        
        if not self.long_positions.get(option_type) or self.long_positions[option_type] is None:
            logger.warning(f"No {option_type} long position to square off")
            print(f"❌ No {option_type} long position to square off")
            return
        
        long_position = self.long_positions[option_type]
        if long_position is None:
            logger.warning(f"Long position {option_type} is None, cannot square off")
            print(f"❌ Long position {option_type} is None, cannot square off")
            return
        
        if not self.combined_premium_data:
            logger.error("No current market data for long position square off")
            print("❌ No current market data for long position square off")
            return
        
        if not self.fyers:
            logger.error("Fyers API not configured. Cannot square off real long positions.")
            print("❌ Fyers API not configured.")
            return
        
        latest_data = self.combined_premium_data[-1]
        symbol = latest_data['ce_tradingsymbol'] if option_type == "CE" else latest_data['pe_tradingsymbol']
        
        try:
            # Create square off order parameters (SELL to close long position)
            order_params = self._create_order_params(symbol, "SELL", 75)
            
            logger.info(f"Squaring off REAL LONG {option_type} position")
            print(f"\n🔄 REAL LONG SQUARE OFF - {option_type} at {current_time.strftime('%H:%M:%S')}")
            logger.info(f"REAL LONG SQUARE OFF - {option_type} at {current_time.strftime('%H:%M:%S')}")
            print(f"   Reason: {reason}")
            logger.info(f"Reason: {reason}")
            print(f"   Symbol: {symbol}")
            print(f"   Action: SELL")
            
            # Place square off order through Fyers API with timeout protection
            order_response = self.safe_api_call(self.fyers.place_order, data=order_params)
            
            if not order_response or order_response.get('s') != 'ok':
                # Extract error details
                error_code = order_response.get('code') if order_response else None
                fyers_message = order_response.get('message', 'No response from API') if order_response else 'No response from API'
                
                # DISABLE TRADING FOR ANY LONG SQUARE OFF ORDER PLACEMENT FAILURE
                self.trading_disabled = True
                self.trading_disabled_reason = f"Long square off order placement failed: {fyers_message}"
                
                error_msg = f"Real long square off order placement failed: {order_response}"
                logger.error(f"🛑 TRADING DISABLED DUE TO LONG SQUARE OFF ORDER FAILURE")
                logger.error(f"🛑 {error_msg}")
                logger.error(f"🛑 Click 'Reset Trading Cycle' to resume trading")
                print(f"\n🛑 TRADING DISABLED DUE TO LONG SQUARE OFF ORDER FAILURE")
                print(f"❌ {error_msg}")
                print(f"🛑 Click 'Reset Trading Cycle' in UI to resume trading")
                return
            
            square_off_order_id = order_response.get('id', 'UNKNOWN')
            
            # Get market prices for P&L calculation
            exit_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
            entry_price = long_position['entry_price']
            
            # Calculate P&L for long position (profit when exit price > entry price)
            long_pnl = (exit_price - entry_price) * 75  # 75 is lot size
            
            print(f"   Entry Price: {entry_price:.2f}")
            logger.info(f"Entry Price: {entry_price:.2f}")
            print(f"   Exit Price: {exit_price:.2f}")
            logger.info(f"Exit Price: {exit_price:.2f}")
            print(f"   Long P&L: {long_pnl:.2f}")
            logger.info(f"Long P&L: {long_pnl:.2f}")
            
            # Update virtual portfolio (reusing existing structure for tracking)
            self.trading_portfolio["total_pnl"] += long_pnl
            self.trading_portfolio["total_trades"] += 1
            if long_pnl > 0:
                self.trading_portfolio["winning_trades"] += 1
                print(f"   ✅ LONG PROFIT: {long_pnl:.2f}")
                logger.info(f"LONG PROFIT: {long_pnl:.2f}")
            else:
                self.trading_portfolio["losing_trades"] += 1
                print(f"   📉 LONG LOSS: {long_pnl:.2f}")
                logger.info(f"LONG LOSS: {long_pnl:.2f}")
            
            # Create square off record for long position
            long_square_off_record = {
                "original_order_id": long_position.get('order_id', 'N/A'),
                "square_off_order_id": square_off_order_id,
                "option_type": option_type,
                "entry_price": entry_price,
                "exit_price": exit_price,
                "pnl": long_pnl,
                "exit_time": current_time,
                "reason": reason,
                "duration_minutes": (current_time - long_position['timestamp']).total_seconds() / 60,
                "entry_time": long_position['timestamp'],
                "action": "BUY",
                "strike": long_position.get('strike', self.current_atm_strike),
                "quantity": 75,
                "nifty_entry": self.current_nifty_price,
                "vwap_entry": self.current_vwap,
                "combined_entry_price": long_position.get('combined_entry_price', 0),
                "tradingsymbol": long_position.get('tradingsymbol', 'N/A'),
                "expiry_date": 'N/A',
                "trade_type": "LONG_SQUARE_OFF"
            }
            
            # Export trade data to Excel
            self._export_trade_to_excel(long_square_off_record)
            
            # Update virtual order record
            for order in self.all_orders:
                if order['order_id'] == long_position.get('order_id') and order['option_type'] == option_type:
                    order['exit_price'] = exit_price
                    order['pnl'] = long_pnl
                    order['exit_time'] = current_time
                    order['status'] = 'LONG_SQUARED_OFF'
                    order['square_off_order_id'] = square_off_order_id
                    break
            
            # Clear long position
            self.long_positions[option_type] = None
            
            # Check if VWAP override cycle should be completed
            self._check_vwap_override_cycle_completion()
            
            print(f"   ✅ Real long square off completed")
            print(f"   Square Off Order ID: {square_off_order_id}")
            logger.info(f"Real long square off completed - Order ID: {square_off_order_id}")
            
            return long_square_off_record
            
        except Exception as e:
            error_msg = f"Error in real long square off: {e}"
            logger.error(error_msg)
            print(f"❌ {error_msg}")
            return None
    
    def square_off_long_position(self, option_type: str, reason: str = "Lower Wick Exit"):
        """Square off a long position created by enhanced strategy"""
        current_time = self.get_ist_time()
        
        if not self.long_positions.get(option_type) or self.long_positions[option_type] is None:
            logger.warning(f"No {option_type} long position to square off")
            print(f"❌ No {option_type} long position to square off")
            return
        
        long_position = self.long_positions[option_type]
        if long_position is None:
            logger.warning(f"Long position {option_type} is None, cannot square off")
            print(f"❌ Long position {option_type} is None, cannot square off")
            return
        
        if not self.combined_premium_data:
            logger.error("No current market data for long position square off")
            print("❌ No current market data for long position square off")
            return
        
        latest_data = self.combined_premium_data[-1]
        exit_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
        entry_price = long_position['entry_price']
        
        # Calculate P&L for long position (profit when exit price > entry price)
        long_pnl = (exit_price - entry_price) * 75  # 75 is lot size
        
        logger.info(f"Squaring off REAL LONG {option_type} position")
        print(f"\n🔄 REAL LONG SQUARE OFF - {option_type} at {current_time.strftime('%H:%M:%S')}")
        logger.info(f"REAL LONG SQUARE OFF - {option_type} at {current_time.strftime('%H:%M:%S')}")
        print(f"   Reason: {reason}")
        logger.info(f"Reason: {reason}")
        print(f"   Entry Price: {entry_price:.2f}")
        logger.info(f"Entry Price: {entry_price:.2f}")
        print(f"   Exit Price: {exit_price:.2f}")
        logger.info(f"Exit Price: {exit_price:.2f}")
        print(f"   Long P&L: {long_pnl:.2f}")
        logger.info(f"Long P&L: {long_pnl:.2f}")
        
        # Update virtual portfolio
        self.trading_portfolio["total_pnl"] += long_pnl
        self.trading_portfolio["total_trades"] += 1
        if long_pnl > 0:
            self.trading_portfolio["winning_trades"] += 1
            print(f"   ✅ LONG PROFIT: {long_pnl:.2f}")
            logger.info(f"LONG PROFIT: {long_pnl:.2f}")
        else:
            self.trading_portfolio["losing_trades"] += 1
            print(f"   📉 LONG LOSS: {long_pnl:.2f}")
            logger.info(f"LONG LOSS: {long_pnl:.2f}")
        
        # Create square off record for long position
        long_square_off_record = {
            "original_order_id": long_position.get('order_id', 'N/A'),
            "option_type": option_type,
            "entry_price": entry_price,
            "exit_price": exit_price,
            "pnl": long_pnl,
            "exit_time": current_time,
            "reason": reason,
            "duration_minutes": (current_time - long_position['timestamp']).total_seconds() / 60,
            "entry_time": long_position['timestamp'],
            "action": "BUY",  # This was a long position
            "strike": long_position.get('strike', self.current_atm_strike),
            "quantity": 75,
            "nifty_entry": self.current_nifty_price,
            "vwap_entry": self.current_vwap,
            "combined_entry_price": long_position.get('combined_entry_price', 0),
            "tradingsymbol": long_position.get('tradingsymbol', 'N/A'),
            "expiry_date": 'N/A',
            "trade_type": "LONG_SQUARE_OFF"
        }
        
        # Export trade data to Excel immediately
        self._export_trade_to_excel(long_square_off_record)
        
        # Update virtual order record
        for order in self.all_orders:
            if order['order_id'] == long_position.get('order_id') and order['option_type'] == option_type:
                order['exit_time'] = current_time
                order['exit_price'] = exit_price
                order['pnl'] = long_pnl
                order['exit_reason'] = reason
                break
        
        # Clear long position
        self.long_positions[option_type] = None
        
        print(f"   ✅ Real long square off completed")
        logger.info(f"Real long square off completed")
        
        return long_square_off_record
    
    def calculate_unrealized_pnl(self) -> float:
        """Calculate current unrealized P&L for virtual positions and track max profit/loss"""
        if not self.combined_premium_data:
            return 0.0
        
        latest_data = self.combined_premium_data[-1]
        total_unrealized_pnl = 0.0
        current_time = self.get_ist_time()
        
        # Calculate P&L for short positions (original straddle)
        for option_type, position in self.positions.items():
            if position is None:
                continue
                
            current_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
            entry_price = position['entry_price']
            
            # For short positions (SELL), profit when current price < entry price
            if position['action'] == "SELL":
                pnl = (entry_price - current_price) * 75  # 75 is lot size
            else:
                pnl = (current_price - entry_price) * 75
                
            total_unrealized_pnl += pnl
        
        # Calculate P&L for long positions (from enhanced strategy)
        for option_type, long_position in self.long_positions.items():
            if long_position is None:
                continue
                
            current_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
            entry_price = long_position['entry_price']
            
            # For long positions (BUY), profit when current price > entry price
            long_pnl = (current_price - entry_price) * 75  # 75 is lot size
            total_unrealized_pnl += long_pnl
        
        # Track max profit and loss (High Water Mark Analysis)
        if total_unrealized_pnl != 0:  # Only track when we have active positions
            vp = self.trading_portfolio
            
            # Update current session tracking
            if total_unrealized_pnl > vp["current_session_max_profit"]:
                vp["current_session_max_profit"] = total_unrealized_pnl
                vp["last_peak_time"] = current_time
                logger.debug(f"New session profit peak: {total_unrealized_pnl:.2f}")
            
            if total_unrealized_pnl < vp["current_session_max_loss"]:
                vp["current_session_max_loss"] = total_unrealized_pnl
                vp["last_trough_time"] = current_time
                logger.debug(f"New session loss trough: {total_unrealized_pnl:.2f}")
            
            # Update all-time tracking
            if total_unrealized_pnl > vp["max_profit_seen"]:
                vp["max_profit_seen"] = total_unrealized_pnl
                logger.info(f"NEW ALL-TIME MAX PROFIT: {total_unrealized_pnl:.2f}")
            
            if total_unrealized_pnl < vp["max_loss_seen"]:
                vp["max_loss_seen"] = total_unrealized_pnl
                logger.info(f"NEW ALL-TIME MAX LOSS: {total_unrealized_pnl:.2f}")
            
            # Calculate peak drawdown (how much we've fallen from the highest point)
            if vp["current_session_max_profit"] > 0:
                current_drawdown = vp["current_session_max_profit"] - total_unrealized_pnl
                if current_drawdown > vp["peak_drawdown"]:
                    vp["peak_drawdown"] = current_drawdown
                    logger.debug(f"New peak drawdown: {current_drawdown:.2f}")
        
        return total_unrealized_pnl
    
    def print_trading_portfolio_summary(self):
        """Print detailed trading portfolio summary with max profit/loss tracking"""
        vp = self.trading_portfolio
        print(f"\n💰 TRADING PORTFOLIO SUMMARY")
        print(f"   Starting Capital: {vp['cash']:,.2f}")
        print(f"   Total P&L: {vp['total_pnl']:,.2f}")
        print(f"   Current Value: {vp['cash'] + vp['total_pnl']:,.2f}")
        print(f"   Total Trades: {vp['total_trades']}")
        
        if vp['total_trades'] > 0:
            win_rate = (vp['winning_trades'] / vp['total_trades']) * 100
            print(f"   Winning Trades: {vp['winning_trades']} ({win_rate:.1f}%)")
            print(f"   Losing Trades: {vp['losing_trades']} ({100-win_rate:.1f}%)")
            avg_pnl = vp['total_pnl'] / vp['total_trades']
            print(f"   Average P&L per Trade: {avg_pnl:.2f}")
            
            # Return percentage
            return_pct = (vp['total_pnl'] / vp['cash']) * 100
            print(f"   Return: {return_pct:.2f}%")
        
        # 🏆 HIGH WATER MARK ANALYSIS
        print(f"\n🏆 HIGH WATER MARK ANALYSIS")
        print(f"   📈 Max Profit Ever Seen: {vp['max_profit_seen']:,.2f}")
        print(f"   📉 Max Loss Ever Seen: {vp['max_loss_seen']:,.2f}")
        
        # Current session analysis
        if vp['current_session_max_profit'] > 0 or vp['current_session_max_loss'] < 0:
            print(f"\n📊 CURRENT SESSION ANALYSIS")
            print(f"   🔥 Session Max Profit: {vp['current_session_max_profit']:,.2f}")
            print(f"   🔻 Session Max Loss: {vp['current_session_max_loss']:,.2f}")
            
            if vp['peak_drawdown'] > 0:
                print(f"   📉 Peak Drawdown: {vp['peak_drawdown']:,.2f}")
            
            # Show timing if available
            if vp['last_peak_time']:
                peak_time_str = vp['last_peak_time'].strftime("%H:%M:%S")
                print(f"   ⏰ Last Peak Time: {peak_time_str}")
            
            if vp['last_trough_time']:
                trough_time_str = vp['last_trough_time'].strftime("%H:%M:%S")
                print(f"   ⏰ Last Trough Time: {trough_time_str}")
        
        # Opportunity analysis
        if vp['max_profit_seen'] > vp['total_pnl'] and vp['max_profit_seen'] > 0:
            missed_profit = vp['max_profit_seen'] - vp['total_pnl']
            print(f"\n💡 OPPORTUNITY ANALYSIS")
            print(f"   💰 Profit Left on Table: {missed_profit:,.2f}")
            print(f"   📊 Realization Ratio: {(vp['total_pnl'] / vp['max_profit_seen'] * 100):.1f}%")
        
        # Show virtual order history
        if self.all_orders:
            print(f"\n📋 RECENT VIRTUAL TRADES:")
            for order in self.all_orders[-5:]:  # Show last 5 trades
                entry_time = order['entry_time'].strftime("%H:%M:%S")
                status = order.get('status', 'ACTIVE')
                if status == 'SQUARED_OFF':
                    exit_time = order.get('exit_time', '').strftime("%H:%M:%S") if order.get('exit_time') else 'N/A'
                    pnl = order.get('pnl', 0)
                    pnl_status = "✅" if pnl > 0 else "❌"
                    duration = f"{order.get('duration_minutes', 0):.0f}min" if 'duration_minutes' in order else 'N/A'
                    print(f"   {order['option_type']} {entry_time}-{exit_time} ({duration}): {pnl:.2f} {pnl_status}")
                else:
                    print(f"   {order['option_type']} {entry_time} (ACTIVE): Entry {order['entry_price']:.2f}")
        
        # FILE-BASED VWAP CONTROL STATUS
        self.print_file_based_status()
        
        return vp
    
    def reset_session_tracking(self):
        """Reset current session max profit/loss tracking when new positions are opened"""
        vp = self.trading_portfolio
        vp["current_session_max_profit"] = 0
        vp["current_session_max_loss"] = 0
        vp["peak_drawdown"] = 0
        vp["last_peak_time"] = None
        vp["last_trough_time"] = None
        logger.info("Session profit/loss tracking reset for new positions")
        print("🔄 Session profit/loss tracking reset for new positions")
    
    def get_decision_candle_data(self) -> Optional[Dict]:
        """Get candle data for decision-making using the configured interval"""
        logger.debug(f"Fetching {self.decision_interval} candle data...")
        try:
            if not self.combined_premium_data:
                logger.warning("No combined premium data available for candle fetch")
                return None
            
            # For all intervals (including 1-minute), only fetch at interval boundaries
            if not self.should_fetch_interval_data():
                # Use cached candle data if available
                if self.interval_candle_data is not None:
                    logger.debug(f"Using cached {self.decision_interval} candle data (not at boundary)")
                    return self.interval_candle_data
                else:
                    logger.debug("No cached candle data available and not at interval boundary")
                    return None
            
            # We're at an interval boundary, fetch fresh data
            if not self.fyers:
                logger.error("Fyers API not configured. Cannot fetch candle data.")
                print("❌ Fyers API not configured. Cannot fetch candle data.")
                return None
                
            # Get the latest option symbols
            latest_data = self.combined_premium_data[-1]
            ce_tradingsymbol = latest_data.get('ce_tradingsymbol')
            pe_tradingsymbol = latest_data.get('pe_tradingsymbol')
            
            # Ensure symbols have proper NSE: prefix for historical data API
            if ce_tradingsymbol and not ce_tradingsymbol.startswith('NSE:'):
                ce_tradingsymbol = f"NSE:{ce_tradingsymbol}"
            if pe_tradingsymbol and not pe_tradingsymbol.startswith('NSE:'):
                pe_tradingsymbol = f"NSE:{pe_tradingsymbol}"
            
            if not ce_tradingsymbol or not pe_tradingsymbol:
                logger.error("Missing trading symbols for candle data fetch")
                return self.interval_candle_data  # Return cached if available
                
            logger.info(f"Fetching {self.decision_interval} candle data at boundary: CE={ce_tradingsymbol}, PE={pe_tradingsymbol}")
            
            # Get current time and lookback period for historical data
            to_date = self.get_ist_time()
            # Use 2x the interval as lookback to ensure we get at least one complete candle
            lookback_minutes = self.decision_interval_minutes # * 2
            from_date = to_date - timedelta(minutes=lookback_minutes)
            logger.debug(f"Time range: {from_date} to {to_date}")
            
            try:
                # Fetch historical data for CE
                ce_historical = self._get_historical_data_with_rate_limit(
                    symbol=ce_tradingsymbol,
                    from_date=from_date,
                    to_date=to_date,
                    resolution=self._convert_interval_to_fyers_resolution(self.decision_interval)
                )
                
                # Fetch historical data for PE
                pe_historical = self._get_historical_data_with_rate_limit(
                    symbol=pe_tradingsymbol,
                    from_date=from_date,
                    to_date=to_date,
                    resolution=self._convert_interval_to_fyers_resolution(self.decision_interval)
                )
                
                if ce_historical and pe_historical:
                    # Get the just completed candle data (second last, since last is currently forming)
                    if len(ce_historical) >= 2 and len(pe_historical) >= 2:
                        latest_ce = ce_historical[-2]  # Just completed candle
                        latest_pe = pe_historical[-2]  # Just completed candle
                        logger.info(f"Retrieved {len(ce_historical)} CE candles and {len(pe_historical)} PE candles at {self.decision_interval} boundary (using completed candle)")
                    else:
                        # Fallback to last candle if we don't have enough data
                        latest_ce = ce_historical[-1]
                        latest_pe = pe_historical[-1]
                        logger.warning(f"Insufficient candles for completed data, using last available candle")
                    
                    # Calculate combined OHLC
                    combined_open = latest_ce['open'] + latest_pe['open']
                    combined_high = latest_ce['high'] + latest_pe['high']
                    combined_low = latest_ce['low'] + latest_pe['low']
                    combined_close = latest_ce['close'] + latest_pe['close']
                    combined_volume = latest_ce['volume'] + latest_pe['volume']
                    
                    candle_data = {
                        "timestamp": latest_ce['date'],
                        "open": combined_open,
                        "high": combined_high,
                        "low": combined_low,
                        "close": combined_close,
                        "volume": combined_volume,
                        "interval": self.decision_interval
                    }
                    logger.debug(f"Combined candle data: {candle_data}")
                    # Cache the candle data
                    self.interval_candle_data = candle_data
                    
                    logger.info(f"{self.decision_interval} candle at boundary: O={combined_open:.2f}, H={combined_high:.2f}, L={combined_low:.2f}, C={combined_close:.2f}, V={combined_volume}")
                    print(f"📊 {self.decision_interval} candle updated: O={combined_open:.2f}, C={combined_close:.2f}")
                    return candle_data
                else:
                    logger.warning("No candle data available from historical API")
                    print("No candle data available")
                    return self.interval_candle_data  # Return cached data if available
                    
            except Exception as e:
                logger.error(f"Error fetching historical candle data: {e}")
                print(f"Error fetching historical data: {e}")
                return self.interval_candle_data  # Return cached data if available
                
        except Exception as e:
            logger.error(f"Error in get_decision_candle_data: {e}")
            print(f"Error fetching {self.decision_interval} candle data: {e}")
            return self.interval_candle_data  # Return cached data if available
    
    def get_individual_candle_data(self, option_type: str) -> Optional[Dict]:
        """Get individual CE or PE candle data for Heikin Ashi calculation with market boundary logic"""
        logger.debug(f"Fetching {option_type} candle data for {self.decision_interval}...")
        try:
            if not self.combined_premium_data:
                logger.warning("No combined premium data available for individual candle fetch")
                return None
            
            # For all intervals (including 1-minute), only fetch at interval boundaries
            if not self.should_fetch_interval_data():
                # Use cached individual candle data if available
                cached_candle = getattr(self, f'individual_candle_data_{option_type.lower()}', None)
                if cached_candle is not None:
                    logger.debug(f"Using cached {option_type} {self.decision_interval} candle data (not at boundary)")
                    return cached_candle
                else:
                    logger.debug(f"No cached {option_type} candle data available and not at interval boundary")
                    return None
            
            # We're at an interval boundary, fetch fresh data
            if not self.fyers:
                logger.error("Fyers API not configured. Cannot fetch candle data.")
                print("❌ Fyers API not configured. Cannot fetch candle data.")
                return None
                
            # Get the latest option symbols
            latest_data = self.combined_premium_data[-1]
            if option_type == "CE":
                tradingsymbol = latest_data.get('ce_tradingsymbol')
            else:
                tradingsymbol = latest_data.get('pe_tradingsymbol')
            
            # Ensure symbol has proper NSE: prefix for historical data API
            if tradingsymbol and not tradingsymbol.startswith('NSE:'):
                tradingsymbol = f"NSE:{tradingsymbol}"
            
            if not tradingsymbol:
                logger.error(f"Missing {option_type} trading symbol for candle data fetch")
                cached_candle = getattr(self, f'individual_candle_data_{option_type.lower()}', None)
                return cached_candle
            
            logger.info(f"Fetching {option_type} {self.decision_interval} candle data at boundary for: {tradingsymbol}")
            
            # Get current time and lookback period for historical data
            to_date = self.get_ist_time()
            # Use 2x the interval as lookback to ensure we get at least one complete candle
            lookback_minutes = self.decision_interval_minutes * 2
            from_date = to_date - timedelta(minutes=lookback_minutes)
            logger.debug(f"Time range: {from_date} to {to_date}")
            
            try:
                # Fetch historical data for individual option
                historical_data = self._get_historical_data_with_rate_limit(
                    symbol=tradingsymbol,
                    from_date=from_date,
                    to_date=to_date,
                    resolution=self._convert_interval_to_fyers_resolution(self.decision_interval)
                )
                
                if historical_data:
                    # Get the just completed candle data (second last, since last is currently forming)
                    if len(historical_data) >= 2:
                        latest_candle = historical_data[-2]  # Just completed candle
                        logger.info(f"Retrieved {len(historical_data)} {option_type} candles at {self.decision_interval} boundary (using completed candle)")
                    else:
                        # Fallback to last candle if we don't have enough data
                        latest_candle = historical_data[-1]
                        logger.warning(f"Insufficient {option_type} candles for completed data, using last available candle")
                    
                    candle_data = {
                        "timestamp": latest_candle['date'],
                        "open": latest_candle['open'],
                        "high": latest_candle['high'],
                        "low": latest_candle['low'],
                        "close": latest_candle['close'],
                        "volume": latest_candle['volume'],
                        "interval": self.decision_interval,
                        "option_type": option_type
                    }
                    
                    # Cache the individual candle data
                    setattr(self, f'individual_candle_data_{option_type.lower()}', candle_data)
                    
                    logger.info(f"Individual {option_type} {self.decision_interval} Candle at Boundary: O={latest_candle['open']:.2f}, H={latest_candle['high']:.2f}, L={latest_candle['low']:.2f}, C={latest_candle['close']:.2f}, V={latest_candle['volume']}")
                    print(f"📊 {option_type} {self.decision_interval} candle updated: O={latest_candle['open']:.2f}, C={latest_candle['close']:.2f}")
                    return candle_data
                else:
                    logger.warning(f"No {option_type} candle data available from historical API")
                    print(f"No {option_type} candle data available")
                    # Return cached data if available
                    cached_candle = getattr(self, f'individual_candle_data_{option_type.lower()}', None)
                    return cached_candle
                    
            except Exception as e:
                logger.error(f"Error fetching {option_type} historical candle data: {e}")
                print(f"Error fetching {option_type} historical data: {e}")
                # Return cached data if available
                cached_candle = getattr(self, f'individual_candle_data_{option_type.lower()}', None)
                return cached_candle
                
        except Exception as e:
            logger.error(f"Error in get_individual_candle_data for {option_type}: {e}")
            print(f"Error fetching {option_type} {self.decision_interval} candle data: {e}")
            # Return cached data if available
            cached_candle = getattr(self, f'individual_candle_data_{option_type.lower()}', None)
            return cached_candle
    
    def place_order(self, option_type: str, action: str = "SELL") -> Optional[str]:
        """Place real order for production trading"""
        current_time = self.get_ist_time().strftime("%H:%M:%S")
        strike = self.current_atm_strike
        
        # Production trading - always use real orders
        real_order_id = self.place_real_order(option_type, action)
        
        if real_order_id and real_order_id not in ["ERROR", "SKIPPED_LOW_PREMIUM"]:
            # Store position information for real trading
            if not self.combined_premium_data:
                logger.error("No premium data available for position setup")
                return "ERROR"
                    
            latest_data = self.combined_premium_data[-1]
            individual_entry_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
            
            self.positions[option_type] = {
                "strike": strike,
                "action": action,
                "timestamp": self.get_ist_time(),
                "entry_price": individual_entry_price,
                "combined_entry_price": latest_data['combined'],
                "order_id": real_order_id,
                "tradingsymbol": latest_data['ce_symbol'] if option_type == "CE" else latest_data['pe_symbol']
            }
            
            return real_order_id
        else:
            return real_order_id  # Return the error/skip status    
    def calculate_heikin_ashi(self, candle_data: Dict, option_type: str = "COMBINED") -> Optional[Dict]:
        """Calculate Heikin Ashi candle from regular OHLC data for combined or individual options"""
        logger.debug(f"Calculating Heikin Ashi candle for {option_type}...")
        try:
            if not candle_data:
                logger.error(f"No candle data provided for Heikin Ashi calculation for {option_type}")
                return None
                
            # Validate required fields
            required_fields = ['open', 'high', 'low', 'close', 'volume', 'timestamp']
            for field in required_fields:
                if field not in candle_data:
                    logger.error(f"Missing required field '{field}' in candle data for {option_type}")
                    return None
            
            logger.debug(f"Starting Heikin Ashi calculation for {option_type}")
            
            # Choose the appropriate data store based on option type
            if option_type == "CE":
                ha_data_store = self.heikin_ashi_ce_data
            elif option_type == "PE":
                ha_data_store = self.heikin_ashi_pe_data
            else:
                ha_data_store = self.heikin_ashi_data  # Combined/default
            
            if not ha_data_store:
                logger.debug(f"First Heikin Ashi candle calculation for {option_type}")
                # First candle: HA_Open = (Open + Close) / 2
                ha_open = (candle_data['open'] + candle_data['close']) / 2
                ha_close = (candle_data['open'] + candle_data['high'] + candle_data['low'] + candle_data['close']) / 4
                ha_high = max(candle_data['high'], ha_open, ha_close)
                ha_low = min(candle_data['low'], ha_open, ha_close)
                logger.debug(f"Current candle data for {option_type}: {candle_data}")
                logger.debug(f"First HA values for {option_type}: O={ha_open:.2f}, H={ha_high:.2f}, L={ha_low:.2f}, C={ha_close:.2f}")
            else:
                logger.debug(f"Calculating subsequent Heikin Ashi candle for {option_type}")
                # Subsequent candles: HA_Open = (Previous HA_Open + Previous HA_Close) / 2
                prev_ha = ha_data_store[-1]
                ha_open = (prev_ha['ha_open'] + prev_ha['ha_close']) / 2
                ha_close = (candle_data['open'] + candle_data['high'] + candle_data['low'] + candle_data['close']) / 4
                ha_high = max(candle_data['high'], ha_open, ha_close)
                ha_low = min(candle_data['low'], ha_open, ha_close)
                logger.debug(f"Previous HA values for {option_type}: O={prev_ha['ha_open']:.2f}, H={prev_ha['ha_high']:.2f}, L={prev_ha['ha_low']:.2f}, C={prev_ha['ha_close']:.2f}")
                logger.debug(f"Current candle data for {option_type}: {candle_data}")
                logger.debug(f"Subsequent HA values for {option_type}: O={ha_open:.2f}, H={ha_high:.2f}, L={ha_low:.2f}, C={ha_close:.2f}")
            
            ha_candle = {
                'timestamp': candle_data['timestamp'],
                'ha_open': ha_open,
                'ha_high': ha_high,
                'ha_low': ha_low,
                'ha_close': ha_close,
                'volume': candle_data['volume'],
                'option_type': option_type
            }
            
            logger.debug(f"Heikin Ashi values for {option_type}: O={ha_open:.2f}, H={ha_high:.2f}, L={ha_low:.2f}, C={ha_close:.2f}")
            
            ha_data_store.append(ha_candle)
            
            # Keep only last 50 HA candles for each type and update the instance variables
            if len(ha_data_store) > 50:
                ha_data_store = ha_data_store[-50:]
                logger.debug(f"Trimmed Heikin Ashi data for {option_type} to last 50 candles")
            
            # Write back to the appropriate instance variable
            if option_type == "CE":
                self.heikin_ashi_ce_data = ha_data_store
            elif option_type == "PE":
                self.heikin_ashi_pe_data = ha_data_store
            else:
                self.heikin_ashi_data = ha_data_store
            
            logger.info(f"Heikin Ashi candle calculated successfully for {option_type}. Total HA candles: {len(ha_data_store)}")
            return ha_candle
            
        except Exception as e:
            logger.error(f"Error calculating Heikin Ashi for {option_type}: {e}")
            print(f"Error calculating Heikin Ashi for {option_type}: {e}")
            return None
    
    def calculate_tick_heikin_ashi(self, option_type: str = "COMBINED") -> Optional[Dict]:
        """Calculate real-time tick-based Heikin Ashi using 5-second historical data from Fyers API"""
        logger.debug(f"Calculating tick-based Heikin Ashi for {option_type} using 5-second historical data...")
        try:
            if not self.fyers:
                logger.error("Fyers API not configured. Cannot fetch 5-second data.")
                return None
            
            if not self.combined_premium_data:
                logger.debug("No premium data available for symbol reference")
                return None
            
            # Get trading symbols from latest premium data
            latest_data = self.combined_premium_data[-1]
            
            if option_type == "CE":
                tradingsymbol = latest_data.get('ce_tradingsymbol')
                # Ensure symbol has proper NSE: prefix for historical data API
                if tradingsymbol and not tradingsymbol.startswith('NSE:'):
                    tradingsymbol = f"NSE:{tradingsymbol}"
            elif option_type == "PE":
                tradingsymbol = latest_data.get('pe_tradingsymbol')
                # Ensure symbol has proper NSE: prefix for historical data API
                if tradingsymbol and not tradingsymbol.startswith('NSE:'):
                    tradingsymbol = f"NSE:{tradingsymbol}"
            else:  # COMBINED - we'll fetch both and combine
                ce_tradingsymbol = latest_data.get('ce_tradingsymbol')
                pe_tradingsymbol = latest_data.get('pe_tradingsymbol')
                
                # Ensure symbols have proper NSE: prefix for historical data API
                if ce_tradingsymbol and not ce_tradingsymbol.startswith('NSE:'):
                    ce_tradingsymbol = f"NSE:{ce_tradingsymbol}"
                if pe_tradingsymbol and not pe_tradingsymbol.startswith('NSE:'):
                    pe_tradingsymbol = f"NSE:{pe_tradingsymbol}"
                    
                if not ce_tradingsymbol or not pe_tradingsymbol:
                    logger.error("Missing trading symbols for combined tick HA calculation")
                    return None
            
            # For individual options, check if symbol is available
            if option_type != "COMBINED" and not tradingsymbol:
                logger.error(f"Missing {option_type} trading symbol for tick HA calculation")
                return None
            
            # Get current time and fetch last 1 minute of 5-second data (12 candles)
            to_date = self.get_ist_time()
            from_date = to_date - timedelta(minutes=1)
            
            logger.debug(f"Fetching 5-second data for {option_type} from {from_date} to {to_date}")
            
            try:
                if option_type == "COMBINED":
                    # Fetch 5-second data for both CE and PE
                    ce_historical = self._get_historical_data_with_rate_limit(
                        symbol=ce_tradingsymbol,
                        from_date=from_date,
                        to_date=to_date,
                        resolution="5S"
                    )
                    
                    pe_historical = self._get_historical_data_with_rate_limit(
                        symbol=pe_tradingsymbol,
                        from_date=from_date,
                        to_date=to_date,
                        resolution="5S"
                    )
                    
                    if not ce_historical or not pe_historical:
                        logger.warning("Could not fetch 5-second data for both options")
                        return None
                    
                    # Use the latest completed 5-second candle (second last if available)
                    if len(ce_historical) >= 2 and len(pe_historical) >= 2:
                        latest_ce = ce_historical[-2]  # Just completed candle
                        latest_pe = pe_historical[-2]  # Just completed candle
                        logger.debug("Using completed 5-second candles for combined HA")
                    else:
                        # Fallback to last available candle
                        latest_ce = ce_historical[-1]
                        latest_pe = pe_historical[-1]
                        logger.debug("Using last available 5-second candles for combined HA")
                    
                    # Calculate combined OHLC from 5-second data
                    tick_candle = {
                        'open': latest_ce['open'] + latest_pe['open'],
                        'high': latest_ce['high'] + latest_pe['high'],
                        'low': latest_ce['low'] + latest_pe['low'],
                        'close': latest_ce['close'] + latest_pe['close'],
                        'volume': latest_ce['volume'] + latest_pe['volume'],
                        'timestamp': latest_ce['date']
                    }
                    
                else:
                    # Fetch 5-second data for individual option
                    historical_data = self._get_historical_data_with_rate_limit(
                        symbol=tradingsymbol,
                        from_date=from_date,
                        to_date=to_date,
                        resolution="5S"
                    )
                    
                    if not historical_data:
                        logger.warning(f"Could not fetch 5-second data for {option_type}")
                        return None
                    
                    # Use the latest completed 5-second candle (second last if available)
                    if len(historical_data) >= 2:
                        latest_candle = historical_data[-2]  # Just completed candle
                        logger.debug(f"Using completed 5-second candle for {option_type} HA")
                    else:
                        # Fallback to last available candle
                        latest_candle = historical_data[-1]
                        logger.debug(f"Using last available 5-second candle for {option_type} HA")
                    
                    # Create tick candle from 5-second historical data
                    tick_candle = {
                        'open': latest_candle['open'],
                        'high': latest_candle['high'],
                        'low': latest_candle['low'],
                        'close': latest_candle['close'],
                        'volume': latest_candle['volume'],
                        'timestamp': latest_candle['date']
                    }
                
                logger.debug(f"5-second tick candle for {option_type}: O={tick_candle['open']:.2f}, H={tick_candle['high']:.2f}, L={tick_candle['low']:.2f}, C={tick_candle['close']:.2f}")
                
                # Get previous tick HA data for calculation (use tick HA data, not regular HA data)
                prev_ha = None
                if option_type == "CE" and self.tick_ha_ce_data:
                    prev_ha = self.tick_ha_ce_data
                elif option_type == "PE" and self.tick_ha_pe_data:
                    prev_ha = self.tick_ha_pe_data
                elif option_type == "COMBINED" and self.tick_ha_combined_data:
                    prev_ha = self.tick_ha_combined_data
                
                # Calculate Heikin Ashi values from 5-second OHLC data
                if not prev_ha:
                    # First HA calculation
                    ha_open = (tick_candle['open'] + tick_candle['close']) / 2
                    logger.debug(f"First tick HA calculation for {option_type}")
                else:
                    # Use previous HA values
                    ha_open = (prev_ha['ha_open'] + prev_ha['ha_close']) / 2
                    logger.debug(f"Subsequent tick HA calculation for {option_type} using prev HA: O={prev_ha['ha_open']:.2f}, C={prev_ha['ha_close']:.2f}")
                
                ha_close = (tick_candle['open'] + tick_candle['high'] + tick_candle['low'] + tick_candle['close']) / 4
                ha_high = max(tick_candle['high'], ha_open, ha_close)
                ha_low = min(tick_candle['low'], ha_open, ha_close)
                
                # Create tick HA data
                tick_ha = {
                    'timestamp': tick_candle['timestamp'],
                    'ha_open': ha_open,
                    'ha_high': ha_high,
                    'ha_low': ha_low,
                    'ha_close': ha_close,
                    'tick_open': tick_candle['open'],
                    'tick_high': tick_candle['high'],
                    'tick_low': tick_candle['low'],
                    'tick_close': tick_candle['close'],
                    'volume': tick_candle['volume'],
                    'option_type': option_type,
                    'data_source': '5s_historical'
                }
                
                # Store tick HA data
                if option_type == "CE":
                    self.tick_ha_ce_data = tick_ha
                elif option_type == "PE":
                    self.tick_ha_pe_data = tick_ha
                else:
                    self.tick_ha_combined_data = tick_ha
                
                logger.info(f"5-second Tick HA for {option_type}: O={ha_open:.2f}, H={ha_high:.2f}, L={ha_low:.2f}, C={ha_close:.2f}")
                print(f"🔍 5s Tick HA {option_type}: O={ha_open:.2f}, H={ha_high:.2f}, L={ha_low:.2f}, C={ha_close:.2f}")
                return tick_ha
                
            except Exception as e:
                logger.error(f"Error fetching 5-second historical data for {option_type}: {e}")
                print(f"Error fetching 5-second data for {option_type}: {e}")
                return None
                
        except Exception as e:
            logger.error(f"Error calculating tick Heikin Ashi for {option_type}: {e}")
            return None
    
    def check_realtime_wick_formation(self, option_type: str = "COMBINED") -> Dict:
        """Check if current ongoing 1-minute candle is forming upper/lower wicks based on 5-second data"""
        logger.debug(f"Checking real-time wick formation for {option_type} during ongoing 1-minute candle...")
        try:
            current_time = self.get_ist_time()
            
            # Initialize 1-minute candle tracking if not exists
            if not hasattr(self, 'minute_candle_tracking'):
                self.minute_candle_tracking = {}
            
            # Check if we're at the start of a new 1-minute candle
            current_minute = current_time.replace(second=0, microsecond=0)
            
            # Initialize tracking for this option type if not exists
            if option_type not in self.minute_candle_tracking:
                self.minute_candle_tracking[option_type] = {
                    'current_minute': None,
                    'minute_ha_open': None,
                    'upper_wick_detected': False,
                    'lower_wick_detected': False,
                    'max_high_seen': None,
                    'min_low_seen': None
                }
            
            tracking = self.minute_candle_tracking[option_type]
            
            # Check if we've moved to a new minute candle
            if tracking['current_minute'] != current_minute:
                logger.info(f"New 1-minute candle started for {option_type} at {current_minute}")
                
                # FIRST: Ensure the just-completed minute candle is processed through proper HA calculation
                # Get the just-completed minute's candle data and calculate its HA values
                previous_minute = current_minute - timedelta(minutes=1)
                logger.debug(f"Processing just-completed minute candle: {previous_minute} for {option_type}")
                
                # Get the completed candle data for the previous minute
                completed_candle_data = self.get_individual_candle_data(option_type)
                if completed_candle_data:
                    # Calculate HA for the just-completed candle
                    logger.debug(f"Calculating HA for just-completed {option_type} candle: {previous_minute}")
                    completed_ha = self.calculate_heikin_ashi(completed_candle_data, option_type)
                    if completed_ha:
                        logger.debug(f"Just-completed {option_type} HA calculated: O={completed_ha['ha_open']:.2f}, C={completed_ha['ha_close']:.2f}")
                
                # NOW get the opening HA value for this new 1-minute candle using the updated HA data
                if option_type == "COMBINED":
                    # For combined, we need to get both CE and PE current prices and calculate combined HA open
                    if self.combined_premium_data:
                        latest_data = self.combined_premium_data[-1]
                        combined_price = latest_data['CE'] + latest_data['PE']
                        
                        # Use updated HA data (which now includes the just-completed candle)
                        if self.heikin_ashi_data:
                            prev_ha = self.heikin_ashi_data[-1]
                            minute_ha_open = (prev_ha['ha_open'] + prev_ha['ha_close']) / 2
                            logger.debug(f"Using updated combined HA data: prev_HA_O={prev_ha['ha_open']:.2f}, prev_HA_C={prev_ha['ha_close']:.2f} -> new_HA_O={minute_ha_open:.2f}")
                        else:
                            # First candle - use simple average
                            minute_ha_open = combined_price
                    else:
                        minute_ha_open = None
                else:
                    # For individual options - use the newly calculated HA data
                    if option_type == "CE" and self.heikin_ashi_ce_data:
                        prev_ha = self.heikin_ashi_ce_data[-1]
                        minute_ha_open = (prev_ha['ha_open'] + prev_ha['ha_close']) / 2
                        logger.debug(f"Using updated {option_type} HA data: prev_HA_O={prev_ha['ha_open']:.2f}, prev_HA_C={prev_ha['ha_close']:.2f} -> new_HA_O={minute_ha_open:.2f}")
                    elif option_type == "PE" and self.heikin_ashi_pe_data:
                        prev_ha = self.heikin_ashi_pe_data[-1]
                        minute_ha_open = (prev_ha['ha_open'] + prev_ha['ha_close']) / 2
                        logger.debug(f"Using updated {option_type} HA data: prev_HA_O={prev_ha['ha_open']:.2f}, prev_HA_C={prev_ha['ha_close']:.2f} -> new_HA_O={minute_ha_open:.2f}")
                    else:
                        # Use current price as fallback
                        logger.warning(f"Using current price as fallback for {option_type}")
                        if self.combined_premium_data:
                            latest_data = self.combined_premium_data[-1]
                            minute_ha_open = latest_data['CE'] if option_type == "CE" else latest_data['PE']
                        else:
                            minute_ha_open = None
                
                # Reset tracking for new candle
                tracking.update({
                    'current_minute': current_minute,
                    'minute_ha_open': minute_ha_open,
                    'upper_wick_detected': False,
                    'lower_wick_detected': False,
                    'max_high_seen': minute_ha_open,
                    'min_low_seen': minute_ha_open
                })
                
                logger.info(f"1-min candle HA open for {option_type}: {minute_ha_open:.2f} (calculated from just-completed minute's HA values)")
                print(f"🕐 New 1-min candle {option_type} - HA Open: {minute_ha_open:.2f} (from completed HA)")
            
            # If we don't have the minute HA open, can't check for wicks
            if tracking['minute_ha_open'] is None:
                logger.warning(f"No minute HA open available for {option_type}, cannot check wicks")
                return {
                    "upper_wick_forming": False,
                    "lower_wick_forming": False,
                    "reason": "No minute HA open available",
                    "minute_ha_open": None
                }
            
            # Get current 5-second data to check for wick formation
            tick_ha = self.calculate_tick_heikin_ashi(option_type)
            if not tick_ha:
                logger.warning(f"No 5-second tick HA data available for {option_type}, cannot check wicks")
                return {
                    "upper_wick_forming": False,
                    "lower_wick_forming": False,
                    "reason": "No 5-second data available",
                    "minute_ha_open": tracking['minute_ha_open']
                }
            
            # Get current 5-second high and low values
            current_5s_high = tick_ha['tick_high']  # Use raw tick data, not HA
            current_5s_low = tick_ha['tick_low']    # Use raw tick data, not HA
            minute_ha_open = tracking['minute_ha_open']
            
            logger.debug(f"Real-time wick check for {option_type}: 5s_high={current_5s_high:.2f}, 5s_low={current_5s_low:.2f}, minute_ha_open={minute_ha_open:.2f}")
            
            # Update max/min seen during this minute
            if tracking['max_high_seen'] is None or current_5s_high > tracking['max_high_seen']:
                tracking['max_high_seen'] = current_5s_high
                logger.debug(f"{option_type}: New max high seen: {current_5s_high:.2f}")
            
            if tracking['min_low_seen'] is None or current_5s_low < tracking['min_low_seen']:
                tracking['min_low_seen'] = current_5s_low
                logger.debug(f"{option_type}: New min low seen: {current_5s_low:.2f}")
            
            # Check for wick formation using absolute value thresholds or simple detection:
            if self.use_absolute_wick_thresholds:
                # Upper wick: if 5s_high > minute_ha_open + threshold_value
                # Lower wick: if 5s_low < minute_ha_open - threshold_value
                upper_wick_forming = current_5s_high > (minute_ha_open + self.upper_wick_threshold_value)
                lower_wick_forming = current_5s_low < (minute_ha_open - self.lower_wick_threshold_value)
                logger.debug(f"{option_type} absolute threshold check - upper: {current_5s_high:.2f} > {minute_ha_open + self.upper_wick_threshold_value:.2f} = {upper_wick_forming}, lower: {current_5s_low:.2f} < {minute_ha_open - self.lower_wick_threshold_value:.2f} = {lower_wick_forming}")
            else:
                # Original logic: any wick above/below HA open
                upper_wick_forming = current_5s_high > minute_ha_open
                lower_wick_forming = current_5s_low < minute_ha_open
                logger.debug(f"{option_type} simple threshold check - upper: {current_5s_high:.2f} > {minute_ha_open:.2f} = {upper_wick_forming}, lower: {current_5s_low:.2f} < {minute_ha_open:.2f} = {lower_wick_forming}")
            
            # Update detection flags
            if upper_wick_forming:
                tracking['upper_wick_detected'] = True
                logger.info(f"{option_type}: Upper wick detected - 5s_high {current_5s_high:.2f} exceeds threshold")
            if lower_wick_forming:
                tracking['lower_wick_detected'] = True
                logger.info(f"{option_type}: Lower wick detected - 5s_low {current_5s_low:.2f} exceeds threshold")
            
            # Calculate wick sizes
            upper_wick_size = max(0, tracking['max_high_seen'] - minute_ha_open)
            lower_wick_size = max(0, minute_ha_open - tracking['min_low_seen'])
            
            result = {
                "upper_wick_forming": upper_wick_forming,
                "lower_wick_forming": lower_wick_forming,
                "upper_wick_detected": tracking['upper_wick_detected'],
                "lower_wick_detected": tracking['lower_wick_detected'],
                "minute_ha_open": minute_ha_open,
                "current_5s_high": current_5s_high,
                "current_5s_low": current_5s_low,
                "max_high_seen": tracking['max_high_seen'],
                "min_low_seen": tracking['min_low_seen'],
                "upper_wick_size": upper_wick_size,
                "lower_wick_size": lower_wick_size,
                "current_minute": current_minute,
                "seconds_elapsed": (current_time - current_minute).total_seconds(),
                "reason": f"5s H:{current_5s_high:.2f} {'>' if upper_wick_forming else '<='} HA_Open:{minute_ha_open:.2f}, 5s L:{current_5s_low:.2f} {'<' if lower_wick_forming else '>='} HA_Open:{minute_ha_open:.2f}"
            }
            
            logger.info(f"Real-time wick check for {option_type}: Upper={upper_wick_forming}, Lower={lower_wick_forming}")
            
            # Print real-time wick status
            if upper_wick_forming or lower_wick_forming:
                wick_status = []
                if upper_wick_forming:
                    wick_status.append(f"📈 Upper Wick: +{upper_wick_size:.2f}")
                if lower_wick_forming:
                    wick_status.append(f"📉 Lower Wick: +{lower_wick_size:.2f}")
                
                elapsed = int((current_time - current_minute).total_seconds())
                print(f"⚡ Real-time Wick {option_type} ({elapsed}s): {' | '.join(wick_status)}")
            
            return result
            
        except Exception as e:
            logger.error(f"Error checking real-time wick formation for {option_type}: {e}")
            return {
                "upper_wick_forming": False,
                "lower_wick_forming": False,
                "reason": f"Error: {e}",
                "minute_ha_open": None
            }
    
    def check_upper_wick_exit_condition(self, option_type: str) -> Dict:
        """Check if upper wick is formed using real-time 1-minute wick detection with absolute value thresholds"""
        try:
            if not self.upper_wick_exit_enabled:
                return {"exit_signal": False, "reason": "Upper wick exit disabled"}
            
            # Use real-time wick formation detection with threshold logic
            wick_result = self.check_realtime_wick_formation(option_type)
            
            if not wick_result or wick_result.get("minute_ha_open") is None:
                return {"exit_signal": False, "reason": "No real-time wick data available"}
            
            # Get wick information
            upper_wick_detected = wick_result.get("upper_wick_detected", False)
            currently_forming = wick_result.get("upper_wick_forming", False)
            upper_wick_size = wick_result.get("upper_wick_size", 0)
            
            # Determine exit signal based on threshold mode
            if self.use_absolute_wick_thresholds:
                # Exit only if wick size meets absolute threshold
                exit_signal = (upper_wick_detected or currently_forming) and (upper_wick_size >= self.upper_wick_threshold_value)
                threshold_info = f">={self.upper_wick_threshold_value:.1f} points"
            else:
                # Exit on any wick formation (original logic)
                exit_signal = upper_wick_detected or currently_forming
                threshold_info = "any wick"
            
            result = {
                "exit_signal": exit_signal,
                "upper_wick_detected": upper_wick_detected,
                "currently_forming": currently_forming,
                "upper_wick_size": upper_wick_size,
                "threshold_met": upper_wick_size >= self.upper_wick_threshold_value if self.use_absolute_wick_thresholds else True,
                "threshold_value": self.upper_wick_threshold_value if self.use_absolute_wick_thresholds else 0,
                "minute_ha_open": wick_result.get("minute_ha_open"),
                "max_high_seen": wick_result.get("max_high_seen"),
                "min_low_seen": wick_result.get("min_low_seen"),
                "seconds_elapsed": wick_result.get("seconds_elapsed", 0),
                "reason": f"Upper wick {upper_wick_size:.2f} pts ({'MEETS' if exit_signal else 'BELOW'} threshold {threshold_info})"
            }
            
            logger.info(f"Real-time upper wick check for {option_type}: {result}")
            if exit_signal:
                if currently_forming:
                    print(f"🚨 UPPER WICK FORMING EXIT - {option_type}: {upper_wick_size:.2f} pts >= {self.upper_wick_threshold_value:.1f} at {wick_result.get('seconds_elapsed', 0)}s!")
                    logger.info(f"{option_type} Upper wick forming exit signal: {upper_wick_size:.2f} pts at {wick_result.get('seconds_elapsed', 0)}s")
                else:
                    print(f"🚨 UPPER WICK DETECTED EXIT - {option_type}: {upper_wick_size:.2f} pts >= {self.upper_wick_threshold_value:.1f}!")
                    logger.info(f"{option_type} Upper wick detected exit signal: {upper_wick_size:.2f} pts")
                    logger.info(f"{option_type} Upper wick detected exit signal")
            
            return result
            
        except Exception as e:
            logger.error(f"Error checking real-time upper wick exit for {option_type}: {e}")
            return {"exit_signal": False, "reason": f"Error: {e}"}
    
    def check_lower_wick_exit_condition(self, option_type: str) -> Dict:
        """Check if lower wick is formed using real-time 1-minute wick detection (no threshold - any wick triggers exit)"""
        try:
            if not self.upper_wick_exit_enabled:  # Use same setting for consistency
                return {"exit_signal": False, "reason": "Lower wick exit disabled"}
            
            # Use real-time wick formation detection - any wick formation triggers exit
            wick_result = self.check_realtime_wick_formation(option_type)
            
            if not wick_result or wick_result.get("minute_ha_open") is None:
                return {"exit_signal": False, "reason": "No real-time wick data available"}
            
            # Get wick information
            lower_wick_detected = wick_result.get("lower_wick_detected", False)
            currently_forming = wick_result.get("lower_wick_forming", False)
            lower_wick_size = wick_result.get("lower_wick_size", 0)
            
            # Determine exit signal based on threshold mode
            if self.use_absolute_wick_thresholds:
                # Exit only if wick size meets absolute threshold
                exit_signal = (lower_wick_detected or currently_forming) and (lower_wick_size >= self.lower_wick_threshold_value)
                threshold_info = f">={self.lower_wick_threshold_value:.1f} points"
            else:
                # Exit on any wick formation (original logic)
                exit_signal = lower_wick_detected or currently_forming
                threshold_info = "any wick"
            
            result = {
                "exit_signal": exit_signal,
                "lower_wick_detected": lower_wick_detected,
                "currently_forming": currently_forming,
                "lower_wick_size": lower_wick_size,
                "threshold_met": lower_wick_size >= self.lower_wick_threshold_value if self.use_absolute_wick_thresholds else True,
                "threshold_value": self.lower_wick_threshold_value if self.use_absolute_wick_thresholds else 0,
                "minute_ha_open": wick_result.get("minute_ha_open"),
                "max_high_seen": wick_result.get("max_high_seen"),
                "min_low_seen": wick_result.get("min_low_seen"),
                "seconds_elapsed": wick_result.get("seconds_elapsed", 0),
                "reason": f"Lower wick {lower_wick_size:.2f} pts ({'MEETS' if exit_signal else 'BELOW'} threshold {threshold_info})"
            }
            
            logger.info(f"Real-time lower wick check for {option_type}: {result}")
            if exit_signal:
                if currently_forming:
                    print(f"🚨 LOWER WICK FORMING EXIT - {option_type}: {lower_wick_size:.2f} pts >= {self.lower_wick_threshold_value:.1f} at {wick_result.get('seconds_elapsed', 0)}s!")
                    logger.info(f"{option_type} Lower wick forming exit signal: {lower_wick_size:.2f} pts at {wick_result.get('seconds_elapsed', 0)}s")
                else:
                    print(f"🚨 LOWER WICK DETECTED EXIT - {option_type}: {lower_wick_size:.2f} pts >= {self.lower_wick_threshold_value:.1f}!")
                    logger.info(f"{option_type} Lower wick detected exit signal: {lower_wick_size:.2f} pts")
            
            return result
            
        except Exception as e:
            logger.error(f"Error checking real-time lower wick exit for {option_type}: {e}")
            return {"exit_signal": False, "reason": f"Error: {e}"}
    
    def get_heikin_ashi_trend(self) -> str:
        """Get Heikin Ashi trend direction"""
        logger.debug("Analyzing Heikin Ashi trend direction...")
        try:
            if len(self.heikin_ashi_data) < 3:
                logger.debug("Insufficient Heikin Ashi data for trend analysis, returning NEUTRAL")
                return "NEUTRAL"
            
            # Get last 3 HA candles
            recent_candles = self.heikin_ashi_data[-3:]
            logger.debug(f"Analyzing last {len(recent_candles)} Heikin Ashi candles for trend")
            
            # Count bullish and bearish candles
            bullish_count = 0
            bearish_count = 0
            
            for candle in recent_candles:
                if candle['ha_close'] > candle['ha_open']:
                    bullish_count += 1
                elif candle['ha_close'] < candle['ha_open']:
                    bearish_count += 1
            
            # Determine trend
            if bullish_count >= 2:
                trend = "BULLISH"
            elif bearish_count >= 2:
                trend = "BEARISH"
            else:
                trend = "NEUTRAL"
                
            logger.info(f"Heikin Ashi trend analysis: {trend} (Bullish: {bullish_count}, Bearish: {bearish_count})")
            return trend
                
        except Exception as e:
            logger.error(f"Error getting Heikin Ashi trend: {e}")
            print(f"Error getting HA trend: {e}")
            logger.error(f"Error getting HA trend: {e}")
            return "NEUTRAL"
    
    def place_individual_straddle_orders(self, ce_symbol: str, pe_symbol: str) -> Dict:
        """Place real CE and PE orders using Fyers API"""
        logger.info("Initiating real straddle order placement...")
        logger.debug(f"CE Symbol: {ce_symbol}, PE Symbol: {pe_symbol}")
        
        try:
            if not self.fyers:
                logger.error("Fyers API not configured. Cannot place orders.")
                print("❌ Fyers API not configured. Cannot place orders.")
                return {"success": False, "reason": "No API"}
            
            print(f"\n🔥 PLACING REAL STRADDLE ORDERS")
            logger.info("PLACING REAL STRADDLE ORDERS")
            print(f"   CE Symbol: {ce_symbol}")
            logger.info(f"CE Symbol: {ce_symbol}")
            print(f"   PE Symbol: {pe_symbol}")
            logger.info(f"PE Symbol: {pe_symbol}")
            
            # Validate premium data availability before placing orders
            if not self.combined_premium_data:
                error_msg = "No premium data available for order placement"
                logger.error(error_msg)
                print(f"   ❌ {error_msg}")
                return {"success": False, "reason": error_msg}
            
            # Place real CE order
            logger.info("Placing real CE order...")
            ce_order_id = self.place_real_order("CE", "SELL")
            
            if ce_order_id == "ERROR":
                reason = "Real CE order placement failed"
                logger.error(reason)
                print(f"   ❌ {reason}")
                return {"success": False, "reason": reason}
            
            logger.info(f"Real CE order placed successfully! Order ID: {ce_order_id}")
            print(f"   ✅ Real CE order placed successfully! ID: {ce_order_id}")
            
            # Place real PE order
            logger.info("Placing real PE order...")
            print("   📤 Placing real PE order...")
            pe_order_id = self.place_real_order("PE", "SELL")
            
            if pe_order_id == "ERROR":
                # CRITICAL: PE order failed but CE succeeded - must rollback CE order immediately
                logger.error("🚨 CRITICAL: PE order failed but CE order was successful!")
                print(f"   🚨 CRITICAL: PE order failed but CE order was successful!")
                print(f"   🔄 Rolling back CE order to prevent asymmetric risk...")
                logger.error("Rolling back CE order to prevent asymmetric risk...")
                
                try:
                    # Temporarily set CE position to enable square off
                    latest_data = self.combined_premium_data[-1]
                    self.positions["CE"] = {
                        "strike": self.current_atm_strike,
                        "action": "SELL",
                        "timestamp": self.get_ist_time(),
                        "entry_price": latest_data['CE'],
                        "combined_entry_price": latest_data['combined'],
                        "order_id": ce_order_id,
                        "tradingsymbol": ce_symbol.replace("NSE:", "")
                    }
                    
                    # Square off the successful CE order
                    self.square_off_position("CE", "Rollback - PE order failed")
                    logger.info("CE order rolled back successfully")
                    print(f"   ✅ CE order rolled back successfully")
                    
                    # Stop trading to prevent further issues
                    self.is_running = False
                    self.trading_disabled = True
                    self.trading_disabled_reason = "PE order failed after CE success - rollback completed"
                    logger.error("🛑 TRADING DISABLED: Fix margin/account issues before restarting")
                    print(f"   🛑 TRADING DISABLED: Fix margin/account issues before restarting")
                    
                except Exception as rollback_error:
                    logger.error(f"❌ FAILED TO ROLLBACK CE ORDER: {rollback_error}")
                    print(f"   ❌ FAILED TO ROLLBACK CE ORDER: {rollback_error}")
                    print(f"   🚨 MANUAL INTERVENTION REQUIRED: Square off CE order manually!")
                    # Still stop trading
                    self.is_running = False
                    self.trading_disabled = True
                    self.trading_disabled_reason = "Failed to rollback CE order after PE failure - manual intervention required"
                
                reason = "PE order failed after CE success - CE rolled back, trading stopped"
                return {"success": False, "reason": reason}
            
            logger.info(f"Real PE order placed successfully! Order ID: {pe_order_id}")
            print(f"   ✅ Real PE order placed successfully! ID: {pe_order_id}")
            print("   🎉 Both real orders placed successfully - Real Straddle complete!")
            logger.info("Both real orders placed successfully - Real Straddle complete!")
            
            # Update positions for both CE and PE
            latest_data = self.combined_premium_data[-1]
            
            self.positions["CE"] = {
                "strike": self.current_atm_strike,
                "action": "SELL",
                "timestamp": self.get_ist_time(),
                "entry_price": latest_data['CE'],
                "combined_entry_price": latest_data['combined'],
                "order_id": ce_order_id,
                "tradingsymbol": ce_symbol.replace("NSE:", "")
            }
            
            self.positions["PE"] = {
                "strike": self.current_atm_strike,
                "action": "SELL",
                "timestamp": self.get_ist_time(),
                "entry_price": latest_data['PE'],
                "combined_entry_price": latest_data['combined'],
                "order_id": pe_order_id,
                "tradingsymbol": pe_symbol.replace("NSE:", "")
            }
            
            # Reset session tracking for new straddle
            self.reset_session_tracking()
            
            # Start VWAP difference tracking now that both legs of straddle are placed
            self._start_vwap_diff_tracking()
            
            return {
                "success": True,
                "ce_order_id": ce_order_id,
                "pe_order_id": pe_order_id,
                "message": "Real straddle orders placed successfully"
            }
            
        except Exception as e:
            error_msg = f"Error placing real straddle orders: {e}"
            print(f"❌ {error_msg}")
            logger.error(error_msg)
            return {"success": False, "reason": error_msg}
                
    def square_off_order_by_symbol(self, tradingsymbol: str, option_type: str):
        """Square off an order by trading symbol using real orders"""
        # Use real square off for production
        self.square_off_real_order(option_type, "Manual Square Off")
    
    def square_off_order_by_id(self, order_id: str, option_type: str):
        """Square off a specific order by order ID using real orders"""
        # Use real square off for production
        self.square_off_real_order(option_type, "Square Off by ID")

    def ensure_minute_ha_open(self, option_type: str):
        """Ensure minute_ha_open is set for wick detection if only one position remains mid-minute."""
        logger.debug(f"Ensuring minute_ha_open for {option_type} if missing...")
        if not hasattr(self, 'minute_candle_tracking'):
            self.minute_candle_tracking = {}
        
        tracking = self.minute_candle_tracking.get(option_type)
        if tracking is None:
            logger.debug(f"Initializing minute candle tracking for {option_type}")
            self.minute_candle_tracking[option_type] = {
                'current_minute': None,
                'minute_ha_open': None,
                'upper_wick_detected': False,
                'lower_wick_detected': False,
                'max_high_seen': None,
                'min_low_seen': None
            }
            tracking = self.minute_candle_tracking[option_type]
        
        # If minute_ha_open is missing, set it using latest HA data
        if tracking['minute_ha_open'] is None:
            logger.debug(f"Setting minute_ha_open for {option_type} using latest HA data")
            prev_ha = None
            if option_type == "CE" and self.heikin_ashi_ce_data:
                prev_ha = self.heikin_ashi_ce_data[-1]
            elif option_type == "PE" and self.heikin_ashi_pe_data:
                prev_ha = self.heikin_ashi_pe_data[-1]
            elif option_type == "COMBINED" and self.heikin_ashi_data:
                prev_ha = self.heikin_ashi_data[-1]
            
            if prev_ha:
                minute_ha_open = (prev_ha['ha_open'] + prev_ha['ha_close']) / 2
                tracking['minute_ha_open'] = minute_ha_open
                tracking['max_high_seen'] = minute_ha_open
                tracking['min_low_seen'] = minute_ha_open
                # Set current minute to avoid re-initialization
                current_time = self.get_ist_time()
                tracking['current_minute'] = current_time.replace(second=0, microsecond=0)
                
                logger.info(f"[ensure_minute_ha_open] Set minute_ha_open for {option_type}: {minute_ha_open:.2f}")
                print(f"[Mid-minute HA fix] Set minute_ha_open for {option_type}: {minute_ha_open:.2f}")
            else:
                logger.warning(f"[ensure_minute_ha_open] No HA data available for {option_type} - cannot set minute_ha_open")
                print(f"⚠️ [Mid-minute HA fix] No HA data available for {option_type} - wick detection unavailable")

    def is_first_order_allowed(self) -> bool:
        """Check if we can place the first order (40 minutes after market opening)"""
        return True
        # now = self.get_ist_time()
        # first_order_time = now.replace(hour=9, minute=55, second=0, microsecond=0)  # 9:55 AM IST
        # return now >= first_order_time
    
    def check_trading_conditions(self):
        """Check if conditions are met for placing orders"""
        logger.info("Starting trading condition check...")
        print("\n[check_trading_conditions] Starting trading condition check...")
        
        # First check: Is trading still active?
        if not self.is_running:
            logger.info("🛑 Trading is stopped - no new orders will be placed")
            print("[check_trading_conditions] Trading is stopped - skipping order placement.")
            return
        
        # Critical safety check: Is trading disabled due to errors?
        if self.trading_disabled:
            logger.error(f"🚨 TRADING DISABLED: {self.trading_disabled_reason}")
            print(f"[check_trading_conditions] 🚨 TRADING DISABLED: {self.trading_disabled_reason}")
            print("[check_trading_conditions] Fix the issue and restart trading to continue.")
            return
        
        # Pre-flight checks
        if not self.fyers:
            logger.error("Fyers API not configured for trading conditions check")
            print("❌ Fyers API not configured. Cannot check trading conditions.")
            return

        logger.debug(f"Combined premium data points: {len(self.combined_premium_data)}")
        print(f"[check_trading_conditions] Combined premium data points: {len(self.combined_premium_data)}")
        # NB Comments
        # if len(self.combined_premium_data) < 5:  # Need sufficient data for reliable signals
        #     logger.warning("Insufficient combined premium data for trading (<5 points)")
        #     print("[check_trading_conditions] Not enough combined premium data (<5), skipping.")
        #     return

        # Check if we can place the first order (40 minutes after market opening)
        if not self.is_first_order_allowed():
            current_time = self.get_ist_time()
            first_order_time = current_time.replace(hour=9, minute=55, second=0, microsecond=0)
            remaining_minutes = (first_order_time - current_time).total_seconds() / 60
            if remaining_minutes > 0:
                logger.info(f"First order scheduled for {first_order_time.strftime('%H:%M')} (in {remaining_minutes:.1f} minutes)")
                print(f"⏰ First order allowed after {first_order_time.strftime('%H:%M')} (in {remaining_minutes:.1f} minutes)")
                print("[check_trading_conditions] First order not allowed yet, skipping.")
                return

        # Check if we have any active positions (both short and long)
        ce_active = self.positions["CE"] is not None
        pe_active = self.positions["PE"] is not None
        ce_long_active = self.long_positions["CE"] is not None
        pe_long_active = self.long_positions["PE"] is not None

        logger.debug(f"Position status - CE active: {ce_active}, PE active: {pe_active}")
        logger.debug(f"Long position status - CE long: {ce_long_active}, PE long: {pe_long_active}")
        print(f"[check_trading_conditions] CE active: {ce_active}, PE active: {pe_active}")
        print(f"[check_trading_conditions] CE long: {ce_long_active}, PE long: {pe_long_active}")
        
        if ce_active or pe_active or ce_long_active or pe_long_active:
            if ce_long_active or pe_long_active:
                logger.info("Active LONG positions exist - skipping new entry to prevent overlap")
                print("[check_trading_conditions] Active LONG positions exist, skipping new entry to prevent overlap.")
            else:
                logger.info("Active positions exist, skipping new entry check")
                print("[check_trading_conditions] Active positions exist, skipping new entry.")
            return

        # Ensure we have all required data
        logger.debug(f"Market data - Nifty: {self.current_nifty_price}, ATM: {self.current_atm_strike}")
        print(f"[check_trading_conditions] Nifty price: {self.current_nifty_price}, ATM strike: {self.current_atm_strike}")
        if not self.current_nifty_price or not self.current_atm_strike:
            logger.warning("Missing required market data (Nifty price or ATM strike)")
            print("[check_trading_conditions] Missing Nifty price or ATM strike, skipping.")
            return

        # Get decision candle data using configured interval
        logger.debug(f"Fetching {self.decision_interval} candle data for trading decision...")
        print(f"[check_trading_conditions] Fetching {self.decision_interval} candle data...")
        candle = self.get_decision_candle_data()
        if not candle:
            logger.warning("No candle data available for trading decision")
            print("[check_trading_conditions] No candle data, skipping.")
            return

        logger.debug(f"Candle data retrieved: {candle}")
        print(f"[check_trading_conditions] Candle data: {candle}")

        # Calculate current VWAP
        logger.debug("Calculating VWAP for trading decision...")
        print("[check_trading_conditions] Calculating VWAP...")
        self.current_vwap = self.calculate_vwap()
        
        # Also calculate market VWAP for display purposes
        logger.debug("Calculating market VWAP for display...")
        self.calculate_market_vwap_for_display()
        
        logger.info(f"Current VWAP calculated: {self.current_vwap}")
        print(f"[check_trading_conditions] VWAP: {self.current_vwap}")
        if not self.current_vwap:
            logger.warning("VWAP calculation failed, skipping trading decision")
            print("[check_trading_conditions] VWAP calculation failed, skipping.")
            return

        # if not ha_candle:
        #     logger.warning("Heikin Ashi calculation failed, skipping trading decision")
        #     print("[check_trading_conditions] Heikin Ashi calculation failed, skipping.")
        #     return

        # Get Heikin Ashi trend
        ha_trend = self.get_heikin_ashi_trend()
        logger.info(f"Heikin Ashi trend determined: {ha_trend}")
        print(f"[check_trading_conditions] Heikin Ashi trend: {ha_trend}")

        current_close = candle['close']
        latest_premium_data = self.combined_premium_data[-1]
        logger.debug(f"Trading data - Current close: {current_close}, Premium data: {latest_premium_data}")
        print(f"[check_trading_conditions] Current candle close: {current_close}")
        print(f"[check_trading_conditions] Latest premium data: {latest_premium_data}")

        # Validate data quality
        logger.debug("Validating trading data quality...")
        print("[check_trading_conditions] Validating trading data...")
        if not self._validate_trading_data(candle, latest_premium_data):
            logger.warning("Trading data validation failed")
            print("[check_trading_conditions] Trading data validation failed, skipping.")
            return

        # Check entry condition: Combined premium closes below VWAP AND favorable HA trend
        # Check VWAP availability before proceeding
        if self.current_vwap is None:
            logger.warning("VWAP not available - cannot check entry conditions")
            print("⚠️ VWAP not available - cannot check entry conditions")
            return False
        
        # Get combined LTP from combined_premium_data
        combined_ltp = latest_premium_data['combined']
        entry_condition = combined_ltp < self.current_vwap
        logger.info(f"Entry condition analysis - Combined LTP < VWAP: {entry_condition} ({combined_ltp:.2f} < {self.current_vwap:.2f})")
        print(f"[check_trading_conditions] Entry condition: close < VWAP? {entry_condition}")
        
        # Check VWAP override cycle state (prevent excessive order placement when override is active)
        if self.vwap_override_enabled and self.vwap_override_cycle_state == "COMPLETED":
            logger.info(f"VWAP override cycle completed - no new orders until reset")
            print(f"[check_trading_conditions] VWAP override cycle COMPLETED - waiting for user reset")
            return
        
        if entry_condition:
            # logger.debug(f"HA trend evaluation for entry: {ha_trend}")
            # print(f"[check_trading_conditions] HA trend favorable? {ha_trend in ['BEARISH', 'NEUTRAL']}")
            # Check if Heikin Ashi trend is favorable for short straddle
            # if ha_trend in ["BEARISH", "NEUTRAL", "BULLISH"]:  # Bearish or neutral trend favors short straddle
                # print("[check_trading_conditions] Checking additional favorable conditions...")
                # Additional favorable condition checks
            if self._check_favorable_conditions(candle, latest_premium_data):
                print(f"\n📈 ENTRY SIGNAL DETECTED!")
                logger.info("ENTRY SIGNAL DETECTED!")
                print(f"   Candle Close: {current_close:.2f}")
                logger.info(f"Candle Close: {current_close:.2f}")
                print(f"   VWAP: {self.current_vwap:.2f}")
                logger.info(f"VWAP: {self.current_vwap:.2f}")
                print(f"   Condition: Close < VWAP ")
                logger.info(f"Condition: Close < VWAP ")
                print(f"   Heikin Ashi Trend: {ha_trend} ")
                logger.info(f"Heikin Ashi Trend: {ha_trend} ")
                print(f"   ATM Strike: {self.current_atm_strike}")
                logger.info(f"ATM Strike: {self.current_atm_strike}")
                print(f"   Nifty Price: {self.current_nifty_price:.2f}")
                logger.info(f"Nifty Price: {self.current_nifty_price:.2f}")

                # Get option symbols
                ce_symbol = latest_premium_data['ce_tradingsymbol']
                pe_symbol = latest_premium_data['pe_tradingsymbol']
                print(f"[check_trading_conditions] CE symbol: {ce_symbol}, PE symbol: {pe_symbol}")

                # Place individual straddle orders
                print("[check_trading_conditions] Placing straddle orders...")
                straddle_result = self.place_individual_straddle_orders(ce_symbol, pe_symbol)

                print(f"[check_trading_conditions] Straddle order result: {straddle_result}")
                logger.info(f"Straddle order result: {straddle_result}")
                if straddle_result["success"]:
                    print("   ✅ Straddle orders placed successfully!")
                    logger.info("Straddle orders placed successfully!")
                    print("   📊 Both CE and PE positions active")
                    logger.info("Both CE and PE positions active")
                    
                    # Mark VWAP override cycle as ACTIVE if override is enabled
                    if self.vwap_override_enabled:
                        self.vwap_override_cycle_state = "ACTIVE"
                        self.vwap_override_cycle_started = True
                        logger.info("VWAP override cycle marked as ACTIVE")
                        print("   🔄 VWAP override cycle marked as ACTIVE")
                else:
                    logger.error(f"Straddle orders failed: {straddle_result['reason']}")
                    print(f"   ❌ Straddle orders failed: {straddle_result['reason']}")

            else:
                logger.info("Additional favorable conditions not met, skipping entry")
                print("[check_trading_conditions] Additional favorable conditions not met, skipping entry.")
        else:
            logger.info(f"Price above VWAP: {current_close:.2f} > {self.current_vwap:.2f}")
            print(f"⚠️ Price above VWAP: {current_close:.2f} > {self.current_vwap:.2f}")
    
    
    def _validate_trading_data(self, candle: Dict, premium_data: Dict) -> bool:
        """Validate that all trading data is reliable"""
        logger.debug("Validating trading data reliability...")
        try:
            # Check if premium data is recent (within last 2 minutes)
            time_diff = self.get_ist_time() - premium_data['timestamp']
            if time_diff.total_seconds() > 120:  # 2 minutes
                logger.warning(f"Premium data is stale: {time_diff.total_seconds():.1f} seconds old")
                print("⚠️ Premium data is stale, skipping signal")
                return False
            
            # Check if premium values are reasonable (not zero or extremely high)
            ce_price = premium_data['CE']
            pe_price = premium_data['PE']
            
            if ce_price <= 0 or pe_price <= 0:
                logger.warning(f"Invalid premium prices - CE: {ce_price}, PE: {pe_price}")
                print("⚠️ Invalid premium prices (zero or negative)")
                return False
            
            if ce_price > 1000 or pe_price > 1000:  # Extremely high premiums
                logger.warning(f"Unusually high premium prices - CE: {ce_price}, PE: {pe_price}")
                print("⚠️ Unusually high premium prices, possible data error")
                return False
            
            # Check if candle has reasonable volume
            if candle['volume'] <= 0:
                logger.warning(f"No volume in current candle: {candle['volume']}")
                print("⚠️ No volume in current candle")
                return False
            
            logger.debug("Trading data validation passed")
            return True
            
        except Exception as e:
            logger.error(f"Error validating trading data: {e}")
            print(f"⚠️ Error validating trading data: {e}")
            return False
    
    def _check_favorable_conditions(self, candle: Dict, premium_data: Dict) -> bool:
        """Check additional favorable conditions before placing orders"""
        logger.debug("Checking favorable conditions for trade entry...")
        try:
            # 1. Check time constraints (avoid trading too early or too late)
            current_time = self.get_ist_time()
            trading_start = self.market_start + timedelta(minutes=5)  # 5 min after market open
            trading_end = self.market_end - timedelta(minutes=5)     # 5 min before market close
            
            if not (trading_start <= current_time <= trading_end):
                logger.warning(f"Outside preferred trading window: {current_time.strftime('%H:%M')} not in {trading_start.strftime('%H:%M')}-{trading_end.strftime('%H:%M')}")
                print("⚠️ Outside preferred trading window")
                return False
            
            # 2. Check VWAP breakdown strength (current price should be significantly below VWAP)
            vwap_breakdown_percentage = ((self.current_vwap - candle['close']) / self.current_vwap) * 100
            logger.warning(f"VWAP breakdown percent: {vwap_breakdown_percentage:.2f}%")
            # if vwap_breakdown_percentage < 0.5:  # At least 0.5% below VWAP
            #     logger.warning(f"VWAP breakdown too weak: {vwap_breakdown_percentage:.2f}%")
            #     print(f"⚠️ VWAP breakdown too weak: {vwap_breakdown_percentage:.2f}%")
            #     return False
            
            # 3. Check Nifty movement (ensure it's not too volatile)
            # if len(self.combined_premium_data) >= 3:
            #     prev_nifty_implied = self.combined_premium_data[-3]['combined']
            #     current_nifty_implied = premium_data['combined']
            #     volatility = abs(current_nifty_implied - prev_nifty_implied) / prev_nifty_implied * 100
                
            #     if volatility > 5:  # More than 5% change in combined premium
            #         print(f"⚠️ High volatility detected: {volatility:.2f}%")
            #         return False
            
            # 4. Check if ATM strike is appropriate (Nifty should be close to ATM)
            # Only check strike difference when instruments are not frozen
            if not self.instrument_freeze_enabled:
                # Check if we have any active positions
                active_positions = any(pos is not None for pos in self.positions.values())
                active_long_positions = any(pos is not None for pos in self.long_positions.values())
                
                strike_difference = abs(self.current_nifty_price - self.current_atm_strike)
                
                if strike_difference > 25:  # More than 25 points away from ATM
                    if not active_positions and not active_long_positions:
                        # No active positions - update ATM strike immediately to allow order placement
                        old_strike = self.current_atm_strike
                        self.current_atm_strike = self.round_to_nearest_50(self.current_nifty_price)
                        logger.info(f"ATM strike updated for order placement: {old_strike} -> {self.current_atm_strike} (Nifty: {self.current_nifty_price:.2f})")
                        print(f"🔄 ATM strike updated for order placement: {old_strike} -> {self.current_atm_strike}")
                        # Recalculate strike difference after update
                        strike_difference = abs(self.current_nifty_price - self.current_atm_strike)
                    else:
                        # Active positions exist - cannot update ATM, reject order
                        logger.warning(f"Nifty too far from ATM with active positions: {strike_difference:.0f} points")
                        print(f"⚠️ Nifty too far from ATM with active positions: {strike_difference:.0f} points")
                        return False
                
                # Final check after potential ATM update
                if strike_difference > 25:
                    logger.warning(f"Nifty still too far from ATM after update: {strike_difference:.0f} points")
                    print(f"⚠️ Nifty still too far from ATM: {strike_difference:.0f} points")
                    return False
            else:
                logger.debug("Instrument freeze enabled - skipping ATM strike proximity check")
            
            # 5. Check minimum combined premium (avoid very low premium trades)
            # combined_premium = premium_data['combined']
            # if combined_premium < 50:  # Minimum 50 rupees combined premium
            #     logger.warning(f"Combined premium too low: {combined_premium:.2f}")
            #     print(f"⚠️ Combined premium too low: {combined_premium:.2f}")
            #     return False
            
            # 6. Check candle pattern (ensure it's a proper close below VWAP for entry)
            # For below-VWAP entry, we want to see some selling pressure
            # if candle['close'] > candle['open']:  # Green candle might indicate false breakdown
            #     # Allow green candles only if they're small relative to the VWAP gap
            #     candle_body = candle['close'] - candle['open']
            #     vwap_gap = self.current_vwap - candle['close']
            #     if candle_body > vwap_gap * 0.3:  # Candle body more than 30% of VWAP gap
            #         logger.warning(f"Strong bullish candle despite VWAP breakdown - body: {candle_body:.2f}, gap: {vwap_gap:.2f}")
            #         print("⚠️ Strong bullish candle despite VWAP breakdown")
            #         return False
            
            logger.info("All favorable conditions met for trade entry")
            print("✅ All favorable conditions met for trade entry")
            return True
            
        except Exception as e:
            logger.error(f"Error checking favorable conditions: {e}")
            print(f"⚠️ Error checking favorable conditions: {e}")
            return False
    
    def update_instrument(self) -> None:
        """Update ATM strike based on current Nifty price - called every 12 seconds, updates every 2 minutes OR immediately if Nifty is >75 points from ATM"""
        logger.debug("ENTRY: Updating instrument...")
        logger.info(f"[UPDATE_INSTRUMENT] Starting ATM update check - Current Nifty: {self.current_nifty_price:.2f}, Current ATM: {self.current_atm_strike}")
        try:
            # Always calculate ATM strike if it's None (first time initialization)
            if self.current_atm_strike is None and self.current_nifty_price:
                self.current_atm_strike = self.round_to_nearest_50(self.current_nifty_price)
                logger.info(f"Initial ATM Strike Set: {self.current_atm_strike} (Nifty: {self.current_nifty_price:.2f})")
                print(f"\n Initial ATM Strike Set: {self.current_atm_strike}")
                return
                
            if self.instrument_freeze_enabled:
                logger.info("🔒 [UPDATE_INSTRUMENT] Instrument freeze enabled - skipping ATM update")
                print(f"🔒 Instrument freeze enabled - skipping ATM update")
                return

            if not hasattr(self, 'last_instrument_update'):
                logger.info("[UPDATE_INSTRUMENT] Initializing last_instrument_update timestamp")
                self.last_instrument_update = self.get_ist_time()
            
            # Check for active positions (both regular short positions and long positions)
            active_positions = any(pos is not None for pos in self.positions.values())
            active_long_positions = any(pos is not None for pos in self.long_positions.values())
            
            logger.info(f"[UPDATE_INSTRUMENT] Position status - Active short: {active_positions}, Active long: {active_long_positions}")
            
            # Log individual position details for debugging
            for pos_type, pos in self.positions.items():
                logger.debug(f"[UPDATE_INSTRUMENT] Short position {pos_type}: {pos is not None}")
            for pos_type, pos in self.long_positions.items():
                logger.debug(f"[UPDATE_INSTRUMENT] Long position {pos_type}: {pos is not None}")
            
            # Check if 2 minutes have passed since last update
            current_time = self.get_ist_time()
            time_since_update = (current_time - self.last_instrument_update).total_seconds()
            
            logger.info(f"[UPDATE_INSTRUMENT] Time since last update: {time_since_update:.1f} seconds ({time_since_update/60:.1f} minutes)")
            
            # If any positions are active (short or long), don't update instrument
            if active_positions or active_long_positions:
                if active_positions:
                    logger.info("[UPDATE_INSTRUMENT] Active short positions exist - skipping instrument update")
                if active_long_positions:
                    logger.info("[UPDATE_INSTRUMENT] Active long positions exist - skipping instrument update")
                return
            
            logger.info("[UPDATE_INSTRUMENT] No active positions found - checking if ATM update is needed")
            
            # For no active positions, check if ATM update is needed
            if self.current_nifty_price:
                new_atm = self.round_to_nearest_50(self.current_nifty_price)
                strike_difference = abs(self.current_nifty_price - self.current_atm_strike)
                
                logger.info(f"[UPDATE_INSTRUMENT] ATM calculation - New ATM: {new_atm}, Current ATM: {self.current_atm_strike}, Strike difference: {strike_difference:.0f} points")
                
                # Determine if immediate update is needed (strike drifted >25 points) or scheduled update (2-min timer)
                immediate_update_needed = strike_difference > 25
                scheduled_update_due = time_since_update >= 120  # 2 minutes
                
                logger.info(f"[UPDATE_INSTRUMENT] Update triggers - Immediate needed: {immediate_update_needed} (diff > 25), Scheduled due: {scheduled_update_due} (time >= 120s)")
                
                if new_atm != self.current_atm_strike and (immediate_update_needed or scheduled_update_due):
                    old_strike = self.current_atm_strike
                    self.current_atm_strike = new_atm
                    self.last_instrument_update = current_time  # Update the timestamp
                    
                    if immediate_update_needed:
                        update_reason = f"Immediate (strike drifted {strike_difference:.0f} points)"
                    else:
                        update_reason = "Scheduled (2-min timer)"
                    
                    logger.info(f"[UPDATE_INSTRUMENT] ✅ ATM Strike Updated: {old_strike} -> {new_atm} (Nifty: {self.current_nifty_price:.2f}) - Reason: {update_reason}")
                    print(f"\n🔄 ATM Strike Updated: {old_strike} to {new_atm}")
                    print(f"   📋 No active positions (short or long) - updating strike to {new_atm}")
                    print(f"   🔍 Update Reason: {update_reason}")
                    # Only clear premium data for new strike calculation
                    # Keep some old data for VWAP continuity
                    if len(self.combined_premium_data) > 50:
                        logger.debug("Trimming combined premium data to last 50 points for new strike")
                        self.combined_premium_data = self.combined_premium_data[-50:]
                    
                    logger.info("[UPDATE_INSTRUMENT] Strike update complete.")
                    print(f"   ✅ Strike update complete.")
                elif new_atm == self.current_atm_strike:
                    logger.info(f"[UPDATE_INSTRUMENT] ATM Strike unchanged: {new_atm} (Nifty: {self.current_nifty_price:.2f}, Diff: {strike_difference:.0f} pts) - updating timestamp only")
                    # Update timestamp even if strike didn't change
                    self.last_instrument_update = current_time
                else:
                    logger.info(f"[UPDATE_INSTRUMENT] ATM update skipped - waiting for timer or larger drift (New ATM: {new_atm}, Current: {self.current_atm_strike}, Diff: {strike_difference:.0f} pts, Time: {time_since_update:.0f}s)")
                    if not immediate_update_needed:
                        logger.debug(f"[UPDATE_INSTRUMENT] Immediate update not needed - strike difference {strike_difference:.0f} <= 25 points")
                    if not scheduled_update_due:
                        remaining_time = 120 - time_since_update
                        logger.debug(f"[UPDATE_INSTRUMENT] Scheduled update not due - {remaining_time:.0f} seconds remaining")
            else:
                logger.warning("[UPDATE_INSTRUMENT] No current Nifty price available - cannot update ATM")
                    
        except Exception as e:
            logger.error(f"[UPDATE_INSTRUMENT] Error updating instrument: {e}")
            print(f"Error updating instrument: {e}")
    
    def print_status(self):
        """Print current status"""
        now = self.get_ist_time().strftime("%H:%M:%S")
        
        print(f"\n📊 STATUS UPDATE - {now}")
        print(f"   � PRODUCTION MODE - Real Trading")
        print(f"   Nifty 50: {self.current_nifty_price:.2f}")
        print(f"   ATM Strike: {self.current_atm_strike}")
        
        if self.combined_premium_data:
            latest = self.combined_premium_data[-1]
            print(f"   CE Premium: {latest['CE']:.2f}")
            print(f"   PE Premium: {latest['PE']:.2f}")
            print(f"   Combined: {latest['combined']:.2f}")
        
        if self.current_vwap:
            print(f"   VWAP: {self.current_vwap:.2f}")
            
            # Show signal status
            if self.combined_premium_data:
                current_close = self.combined_premium_data[-1]['combined']
                if current_close < self.current_vwap:
                    print(f"   Signal: 📈 BELOW VWAP (Entry)")
                else:
                    print(f"   Signal: 📉 ABOVE VWAP (Exit)")
        
        # Show trading portfolio
        vp = self.trading_portfolio
        print(f"   📊 Trading Portfolio:")
        print(f"      Total P&L: {vp['total_pnl']:.2f}")
        print(f"      Total Trades: {vp['total_trades']}")
        if vp['total_trades'] > 0:
            win_rate = (vp['winning_trades'] / vp['total_trades']) * 100
            print(f"      Win Rate: {win_rate:.1f}% ({vp['winning_trades']}/{vp['total_trades']})")
        
        # Show active positions and P&L
        active_positions = [k for k, v in self.positions.items() if v is not None]
        active_long_positions = [k for k, v in self.long_positions.items() if v is not None]
        
        if active_positions or active_long_positions:
            if active_positions:
                print(f"   Short Positions: {', '.join(active_positions)}")
            if active_long_positions:
                print(f"   Long Positions: {', '.join(active_long_positions)} (Enhanced Strategy)")
            
            # Show current unrealized P&L for trading
            if self.combined_premium_data:
                unrealized_pnl = self.calculate_unrealized_pnl()
                status = "✅" if unrealized_pnl > 0 else "❌"
                print(f"   Current Unrealized P&L: {unrealized_pnl:.2f} {status}")
                
                # Show session high water marks
                vp = self.trading_portfolio
                if vp['current_session_max_profit'] > 0 or vp['current_session_max_loss'] < 0:
                    print(f"   📊 Session Peaks:")
                    if vp['current_session_max_profit'] > 0:
                        profit_status = "🏆" if unrealized_pnl == vp['current_session_max_profit'] else "📈"
                        print(f"      Max Profit: {vp['current_session_max_profit']:.2f} {profit_status}")
                    if vp['current_session_max_loss'] < 0:
                        loss_status = "🔻" if unrealized_pnl == vp['current_session_max_loss'] else "📉"
                        print(f"      Max Loss: {vp['current_session_max_loss']:.2f} {loss_status}")
                    
                    # Show drawdown if we've fallen from peak
                    if vp['current_session_max_profit'] > unrealized_pnl and vp['current_session_max_profit'] > 0:
                        drawdown = vp['current_session_max_profit'] - unrealized_pnl
                        print(f"      Current Drawdown: {drawdown:.2f} 📉")
        else:
            print("   Active Positions: None")
    
    def print_detailed_status(self, trading_status: Dict = None):
        """Print detailed status including trading conditions"""
        now = self.get_ist_time().strftime("%H:%M:%S")
        
        print(f"\n📊 DETAILED STATUS - {now}")
        print(f"   Nifty 50: {self.current_nifty_price:.2f}")
        print(f"   ATM Strike: {self.current_atm_strike}")
        
        if self.combined_premium_data:
            latest = self.combined_premium_data[-1]
            print(f"   CE Premium: {latest['CE']:.2f}")
            print(f"   PE Premium: {latest['PE']:.2f}")
            print(f"   Combined: {latest['combined']:.2f}")
        
        if self.current_vwap:
            print(f"   VWAP: {self.current_vwap:.2f}")
            
            # Show signal status
            if self.combined_premium_data:
                current_close = self.combined_premium_data[-1]['combined']
                if current_close < self.current_vwap:
                    diff_pct = ((self.current_vwap - current_close) / self.current_vwap) * 100
                    print(f"   Signal: 📈 BELOW VWAP (-{diff_pct:.2f}%) - ENTRY ZONE")
                else:
                    diff_pct = ((current_close - self.current_vwap) / self.current_vwap) * 100
                    print(f"   Signal: 📉 ABOVE VWAP (+{diff_pct:.2f}%) - EXIT ZONE")
        
        # Show trading status
        if trading_status:
            if trading_status["can_enter_new_trade"]:
                if trading_status["can_enter_ce"] and trading_status["can_enter_pe"]:
                    print("   Trading Status: 🟢 READY FOR FULL STRADDLE")
                else:
                    print("   Trading Status: 🟡 WAITING FOR BOTH LEGS AVAILABLE")
            else:
                reasons = ", ".join(trading_status["reasons"])
                print(f"   Trading Status: 🔴 NOT READY ({reasons})")
        
        # Show individual position status
        ce_status = "✅ ACTIVE" if self.positions["CE"] else "⭕ AVAILABLE"
        pe_status = "✅ ACTIVE" if self.positions["PE"] else "⭕ AVAILABLE"
        print(f"   CE Position: {ce_status}")
        print(f"   PE Position: {pe_status}")
        
        # Show Heikin Ashi trend status
        if len(self.heikin_ashi_data) > 0:
            ha_trend = self.get_heikin_ashi_trend()
            print(f"   Heikin Ashi Trend: {ha_trend}")
            
            # Show if trend is favorable for short straddle
            if ha_trend in ["BEARISH", "NEUTRAL"]:
                print(f"   HA Trend Status: ✅ FAVORABLE for short straddle")
            else:
                print(f"   HA Trend Status: ❌ NOT FAVORABLE for short straddle")
        
        # Show active positions and P&L
        active_positions = [k for k, v in self.positions.items() if v is not None]
        if active_positions:
            print(f"   Active Positions: {', '.join(active_positions)}")
            
            # Show P&L and position details
            pnl_data = self.get_position_pnl()
            if pnl_data["total_pnl"] != 0:
                status = "✅ PROFIT" if pnl_data["total_pnl"] > 0 else "❌ LOSS"
                print(f"   Total P&L: {pnl_data['total_pnl']:.2f} ({status})")
                
                # Show time in position
                if self.positions.get("CE"):
                    time_in_pos = self.get_ist_time() - self.positions["CE"]["timestamp"]
                    minutes = int(time_in_pos.total_seconds() / 60)
                    print(f"   Time in Position: {minutes} minutes")
                
                # Show exit monitoring status
                print(f"   Exit Strategy: VWAP-based exit monitoring")
        else:
            print("   Active Positions: None")
        
        # Show VWAP difference tracking status
        vwap_status = self.get_vwap_tracking_status()
        if vwap_status["tracking_enabled"]:
            print(f"\n📊 VWAP DIFFERENCE TRACKING")
            print(f"   Status: ✅ ACTIVE")
            print(f"   Current Diff: {vwap_status['current_diff_percent']:.3f}%")
            print(f"   Max Diff Seen: {vwap_status['max_diff_percent']:.3f}%")
            print(f"   Exit Threshold: {vwap_status['threshold_percent']:.1f}%")
            print(f"   Time Since Order: {vwap_status['time_since_order_minutes']:.1f} min")
            
            # Show warning if approaching threshold
            remaining_threshold = vwap_status['threshold_percent'] - vwap_status['max_diff_percent']
            if remaining_threshold <= 0.3:  # Within 0.3% of threshold
                print(f"   ⚠️ WARNING: Close to exit threshold! ({remaining_threshold:.3f}% remaining)")
            elif remaining_threshold <= 0.7:  # Within 0.7% of threshold
                print(f"   🔶 ALERT: Approaching exit threshold ({remaining_threshold:.3f}% remaining)")
        else:
            print(f"\n📊 VWAP DIFFERENCE TRACKING")
            print(f"   Status: ⭕ INACTIVE (No active positions)")
        
        # Show upper wick monitoring status for tick-based exits
        wick_status = self.get_upper_wick_status()
        print(f"\n⚡ UPPER WICK EXIT MONITORING")
        print(f"   Status: {'✅ ENABLED' if wick_status['enabled'] else '❌ DISABLED'}")
        print(f"   Threshold: {wick_status['threshold_percent']:.1f}%")
        
        if active_positions and wick_status['enabled']:
            if "CE" in active_positions and wick_status.get('ce_tick_ha_available'):
                ce_wick_pct = wick_status.get('ce_upper_wick_percent', 0)
                ce_signal = wick_status.get('ce_exit_signal', False)
                signal_icon = "🚨" if ce_signal else "✅" if ce_wick_pct < wick_status['threshold_percent'] * 0.8 else "🔶"
                print(f"   CE Upper Wick: {ce_wick_pct:.1f}% {signal_icon}")
                
            if "PE" in active_positions and wick_status.get('pe_tick_ha_available'):
                pe_wick_pct = wick_status.get('pe_upper_wick_percent', 0)
                pe_signal = wick_status.get('pe_exit_signal', False)
                signal_icon = "🚨" if pe_signal else "✅" if pe_wick_pct < wick_status['threshold_percent'] * 0.8 else "🔶"
                print(f"   PE Upper Wick: {pe_wick_pct:.1f}% {signal_icon}")
        else:
            print(f"   Monitoring: ⭕ NO ACTIVE POSITIONS")
            
        # Show market conditions if available
        if trading_status and "market_conditions" in trading_status:
            mc = trading_status["market_conditions"]
            if mc:
                strike_diff = mc.get("strike_difference", 0)
                print(f"   Strike Distance: {strike_diff:.0f} points from ATM")
    
    def is_market_hours(self) -> bool:
        """Check if current time is within market hours"""
        now = self.get_ist_time()
        # Ensure both market times are timezone-aware and on the same date as now
        market_start = now.replace(hour=9, minute=15, second=0, microsecond=0)
        market_end = now.replace(hour=15, minute=30, second=0, microsecond=0)
        return market_start <= now <= market_end
    
    def run_data_collection(self):
        """Continuous data collection and analysis"""
        logger.info("Starting live market tracking and data collection...")
        print("\n🚀 Starting live market tracking...")
        print("Press Ctrl+C to stop")
        
        self.is_running = True
        iteration = 0
        
        try:
            while self.is_running:
                logger.debug(f"Data collection iteration: {iteration+1}")
                print(f"\n[run_data_collection] Iteration: {iteration+1}")
                if not self.is_market_hours():
                    logger.info("Outside market hours, waiting...")
                    print(f"\n⏰ Outside market hours. Waiting...")
                    time.sleep(60)
                    continue
                
                # Check for emergency square off near market close
                if self.is_near_market_close():
                    logger.warning("Market close approaching, initiating emergency square off...")
                    print("[run_data_collection] Market close approaching, emergency square off...")
                    self.emergency_square_off("Market Close Approaching")
                    print("🕐 Market closing soon. All positions squared off.")
                    break
                
                iteration += 1
                
                # Reset API call tracking if needed (every minute)
                self.reset_api_call_tracking()
                
                # Check for VWAP override file changes (every iteration for real-time response)
                self.check_vwap_override_file()
                
                # Get current Nifty price
                logger.debug("Fetching current Nifty price...")
                print("[run_data_collection] Fetching Nifty price...")
                nifty_price = self.get_nifty_price()
                logger.debug(f"Nifty price retrieved: {nifty_price}")
                print(f"[run_data_collection] Nifty price: {nifty_price}")
                if nifty_price is None:
                    logger.warning("Nifty price fetch failed, retrying in 10 seconds...")
                    print("[run_data_collection] Nifty price fetch failed, sleeping 10s...")
                    time.sleep(10)
                    continue
                
                print("[run_data_collection] Updating instrument for new entry signal...")
                logger.debug(f"Current instrument_freeze_enabled: {self.instrument_freeze_enabled}")
                
                self.update_instrument()
                
                # Get options data
                logger.debug(f"Fetching options data for ATM strike: {self.current_atm_strike}")
                print(f"[run_data_collection] Fetching options data for strike {self.current_atm_strike}...")
                options_data = self.get_options_data(self.current_atm_strike)
                
                # Log API calls after the main API calls
                quote_calls = self.api_call_tracking["quote_calls"]
                hist_calls = self.api_call_tracking["historical_calls"]
                logger.info(f"API calls this minute: Quote={quote_calls}, Historical={hist_calls}")
                
                if options_data:
                    logger.debug(f"Options data received: {options_data}")
                    print(f"[run_data_collection] Options data: {options_data}")

                    # Print current P&L after each options data fetch
                    if self.combined_premium_data:
                        pnl_data = self.get_position_pnl()
                        print(f"[run_data_collection] Current P&L: {pnl_data['total_pnl']:.2f}")
                    
                    # Thread-safe append of options data
                    self.combined_premium_data.append(options_data)
                    
                    # Small delay after data update to prevent race conditions with UI polling
                    time.sleep(0.1)
                    
                    # Monitor SHORT positions for upper wick exits (only when one leg is open after selective exit)
                    short_positions_count = sum(1 for pos in [self.positions["CE"], self.positions["PE"]] if pos is not None)
                    if short_positions_count == 1:  # Only when one short leg remains (after selective VWAP exit)
                        logger.debug("One short position active - checking for upper wick exit conditions...")
                        print("[run_data_collection] Monitoring remaining SHORT leg for upper wick exit...")
                        
                        # Check CE short position for upper wick exit
                        if self.positions["CE"] is not None:
                            self.calculate_tick_heikin_ashi("CE")
                            ce_wick_result = self.check_upper_wick_exit_condition("CE")
                            logger.debug(f"CE Short upper wick exit check result: {ce_wick_result}")
                            if ce_wick_result["exit_signal"]:
                                print(f"\n⚡ CE SHORT UPPER WICK EXIT TRIGGERED!")
                                print(f"   Upper Wick: {ce_wick_result['upper_wick_size']:.1f} pts > {ce_wick_result['threshold_value']:.1f} pts")
                                print(f"   🔴 Squaring off remaining CE SHORT position due to upper wick formation")
                                self.square_off_real_order("CE", reason="UPPER_WICK_EXIT")
                        
                        # Check PE short position for upper wick exit
                        if self.positions["PE"] is not None:
                            self.calculate_tick_heikin_ashi("PE")
                            pe_wick_result = self.check_upper_wick_exit_condition("PE")
                            logger.debug(f"PE Short upper wick exit check result: {pe_wick_result}")
                            if pe_wick_result["exit_signal"]:
                                print(f"\n⚡ PE SHORT UPPER WICK EXIT TRIGGERED!")
                                print(f"   Upper Wick: {pe_wick_result['upper_wick_size']:.1f} pts > {pe_wick_result['threshold_value']:.1f} pts")
                                print(f"   🔴 Squaring off remaining PE SHORT position due to upper wick formation")
                                self.square_off_real_order("PE", reason="UPPER_WICK_EXIT")
                    elif short_positions_count == 2:
                        print("[run_data_collection] Both CE & PE short legs active - using regular VWAP-based exits only")
                    
                    # Monitor LONG positions for lower wick exits (from enhanced strategy)
                    if self.long_positions["CE"] is not None or self.long_positions["PE"] is not None:
                        print("[run_data_collection] Monitoring LONG positions for lower wick exits...")
                        
                        # Check CE long position for lower wick exit
                        if self.long_positions["CE"] is not None:
                            logger.debug("Checking CE LONG position for lower wick exit...")
                            self.calculate_tick_heikin_ashi("CE")
                            ce_lower_wick_result = self.check_lower_wick_exit_condition("CE")
                            if ce_lower_wick_result["exit_signal"]:
                                print(f"\n⚡ CE LONG LOWER WICK EXIT TRIGGERED!")
                                print(f"   Lower Wick: {ce_lower_wick_result['lower_wick_size']:.1f} pts > {ce_lower_wick_result['threshold_value']:.1f} pts")
                                print(f"   🔴 Squaring off CE LONG position due to lower wick formation")
                                self.square_off_real_long_position("CE", reason="LOWER_WICK_EXIT")
                        
                        # Check PE long position for lower wick exit
                        if self.long_positions["PE"] is not None:
                            logger.debug("Checking PE LONG position for lower wick exit...")
                            self.calculate_tick_heikin_ashi("PE")
                            pe_lower_wick_result = self.check_lower_wick_exit_condition("PE")
                            if pe_lower_wick_result["exit_signal"]:
                                print(f"\n⚡ PE LONG LOWER WICK EXIT TRIGGERED!")
                                print(f"   Lower Wick: {pe_lower_wick_result['lower_wick_size']:.1f} pts > {pe_lower_wick_result['threshold_value']:.1f} pts")
                                print(f"   🔴 Squaring off PE LONG position due to lower wick formation")
                                self.square_off_real_long_position("PE", reason="LOWER_WICK_EXIT")
                    
                    # Keep only last 100 data points to manage memory
                    if len(self.combined_premium_data) > 100:
                        logger.debug("Trimming combined premium data to last 100 points")
                        print("[run_data_collection] Trimming combined_premium_data to last 100 points")
                        self.combined_premium_data = self.combined_premium_data[-100:]
                else:
                    logger.warning("No options data received from API")
                    print("[run_data_collection] No options data received")
                
                # Get trading status
                print("[run_data_collection] Getting trading status...")
                trading_status = self.get_trading_status()
                print(f"[run_data_collection] Trading status: {trading_status}")
                
                # Calculate Heikin Ashi for combined and individual options
                logger.debug("Calculating Heikin Ashi candles for trend analysis...")
                print("[run_data_collection] Calculating Heikin Ashi candles...")
                candle = self.get_decision_candle_data()
                
                # Only calculate Heikin Ashi once per minute (when a new candle is formed)
                logger.debug("Checking if new Heikin Ashi candles need to be calculated...")
                if hasattr(self, 'last_ha_candle_time'):
                    last_ha_time = self.last_ha_candle_time
                    logger.debug(f"Last Heikin Ashi candle time: {last_ha_time}")
                else:
                    last_ha_time = None
                    logger.debug("No previous Heikin Ashi candle time found.")

                current_minute = candle['timestamp'].replace(second=0, microsecond=0) if candle and 'timestamp' in candle else self.get_ist_time().replace(second=0, microsecond=0)
                logger.debug(f"Current minute for Heikin Ashi: {current_minute}")

                if last_ha_time != current_minute:
                    logger.info(f"Calculating new Heikin Ashi candles for minute: {current_minute}")
                    
                    # Calculate combined Heikin Ashi (for overall trend)
                    if candle:
                        ha_candle = self.calculate_heikin_ashi(candle, "COMBINED")
                        logger.debug(f"Combined Heikin Ashi candle result: {ha_candle}")
                        print(f"[run_data_collection] Combined Heikin Ashi candle: {ha_candle}")
                    
                    # Calculate individual CE and PE Heikin Ashi for exit decisions
                    ce_candle = self.get_individual_candle_data("CE")
                    if ce_candle:
                        ha_ce_candle = self.calculate_heikin_ashi(ce_candle, "CE")
                        logger.debug(f"CE Heikin Ashi candle result: {ha_ce_candle}")
                        print(f"[run_data_collection] CE Heikin Ashi candle: {ha_ce_candle}")
                    
                    pe_candle = self.get_individual_candle_data("PE")
                    if pe_candle:
                        ha_pe_candle = self.calculate_heikin_ashi(pe_candle, "PE")
                        logger.debug(f"PE Heikin Ashi candle result: {ha_pe_candle}")
                        print(f"[run_data_collection] PE Heikin Ashi candle: {ha_pe_candle}")
                    
                    self.last_ha_candle_time = current_minute
                else:
                    logger.debug("Heikin Ashi candles already calculated for this minute; skipping.")

                self.current_vwap = self.calculate_vwap()
                # Also calculate market VWAP for display purposes
                self.calculate_market_vwap_for_display()
                print(f"[run_data_collection] Current VWAP: {self.current_vwap}")
                print(f"[run_data_collection] Market VWAP: {self.current_market_vwap}")
                
                # Reset VWAP exit candle tracking for each new minute
                self._reset_vwap_exit_candle_tracking()
                
                # Update VWAP difference tracking if enabled
                if self.vwap_diff_tracking_enabled:
                    self._update_vwap_diff_tracking()
                    
                    # Check if VWAP exit condition is met
                    if self._check_vwap_exit_condition():
                        print("[run_data_collection] VWAP exit condition triggered!")
                        self._square_off_both_legs_vwap_exit()
                        # Continue the loop after squaring off
                
                # Check for new entry signals (if any position is available)
                if trading_status["can_enter_new_trade"]:
                    print("[run_data_collection] Entry signal detected, checking trading conditions...")
                    self.check_trading_conditions()
                else:
                    print("[run_data_collection] No entry signal")
                
                # Manage stop-losses for active positions (only every 5 minutes)
                if trading_status["has_active_positions"]:
                    print("[run_data_collection] Managing stop-losses...")
                    try:
                        self.manage_stop_losses()
                    except Exception as e:
                        logger.error(f"Error in stop-loss management: {e}")
                        print(f"[run_data_collection] Error in stop-loss management: {e}")
                        # Continue execution despite stop-loss error
                
                if iteration % 5 == 0:
                    print("[run_data_collection] Printing detailed status...")
                    self.print_detailed_status(trading_status)
                    
                    # Export portfolio status to Excel every 10 iterations
                    self._export_portfolio_to_excel()
                    
                    # Print TRADING PORTFOLIO SUMMARY every 30 iterations (roughly every 6 minutes)
                    if iteration % 30 == 0:
                        print("\n" + "="*50)
                        self.print_trading_portfolio_summary()
                        print("="*50)
                
                # Wait before next iteration
                print("[run_data_collection] Sleeping 1s before next iteration...")
                time.sleep(1) 
                
        except KeyboardInterrupt:
            print("\n\n🛑 Stopping trader...")
            print("🔄 Squaring off all open positions before exit...")
            self.emergency_square_off("Manual Stop")
            self.is_running = False
        except Exception as e:
            print(f"\nError in main loop: {e}")
            print("🔄 Squaring off all open positions due to error...")
            self.emergency_square_off("System Error")
            self.is_running = False
    
    def start(self):
        """Start the virtual trading system"""
        print("=" * 60)
        print("🔄 NIFTY 50 OPTIONS TRADER - SIMULATION MODE")
        print("=" * 60)
        print("🎯 VIRTUAL TRADING FEATURES:")
        print("✅ Live Nifty 50 price tracking")
        print("✅ Dynamic ATM strike calculation")
        print("✅ Combined premium VWAP analysis")
        print("✅ 5-minute candle tracking")
        print("✅ Virtual straddle trading simulation")
        print("✅ VWAP-based exit monitoring")
        print("✅ Tick-based Heikin Ashi upper wick exits")
        print("✅ Real-time P&L calculation")
        print("✅ Trading performance analytics")
        print("")
        print("📊 TRADING RULES:")
        print(f"   * Entry: Combined premium closes below VWAP ({self.decision_interval})")
        print(f"   * Exit: Combined premium closes above VWAP ({self.decision_interval})")
        if self.use_absolute_wick_thresholds:
            print(f"   * Fast Exit: Upper wick >={self.upper_wick_threshold_value:.1f} pts, Lower wick >={self.lower_wick_threshold_value:.1f} pts")
        else:
            print(f"   * Fast Exit: Any upper/lower wick formation")
        print(f"   * Decision Interval: {self.decision_interval} ({self.decision_interval_minutes} minutes)")
        print("   * Uses LIVE market data")
        print("   * REAL ORDERS will be placed")
        print("=" * 60)
        
        print("� PRODUCTION MODE ACTIVE")
        print("   All trades are real - live money trading")
        print("   Ensure sufficient balance in trading account")
        print("=" * 60)
        
        # Initialize with current price
        initial_price = self.get_nifty_price()
        if initial_price:
            self.current_atm_strike = self.round_to_nearest_50(initial_price)
            print(f"\n📍 Initial Setup:")
            print(f"   Nifty 50: {initial_price:.2f}")
            print(f"   ATM Strike: {self.current_atm_strike}")
        
        # Start data collection
        self.run_data_collection()

    def square_off_position(self, option_type: str, reason: str = "Manual Exit"):
        """Square off (close) existing position - Production Trading"""
        # Debug logging to trace the reason parameter
        logger.debug(f"square_off_position called with option_type={option_type}, reason='{reason}'")
        
        if not self.positions[option_type]:
            print(f"❌ No {option_type} position to square off")
            logger.warning(f"No {option_type} position to square off")
            return
        
        position = self.positions[option_type]
        current_time = self.get_ist_time().strftime("%H:%M:%S")
        
        # Production real trading code
        print(f"\n🔄 REAL SQUARE OFF at {current_time}")
        print(f"   Type: {option_type}")
        print(f"   Strike: {position['strike']}")
        print(f"   Entry Action: {position['action']}")
        
        if not self.fyers:
            print("❌ Fyers API not configured. Cannot place real orders.")
            logger.error("Fyers API not configured for production trading")
            return
        
        try:
            # Determine opposite action for square off
            opposite_action = "BUY" if position['action'] == "SELL" else "SELL"
            
            # Ensure symbol has proper NSE: prefix for Fyers API
            symbol = position['tradingsymbol']
            if not symbol.startswith('NSE:'):
                symbol = f"NSE:{symbol}"
            
            # Place square off order
            order_params = {
                "symbol": symbol,
                "qty": 75,  # Same lot size
                "type": 2,  # Market order
                "side": 1 if opposite_action == "BUY" else -1,
                "productType": "MARGIN",
                "limitPrice": 0,
                "stopPrice": 0,
                "validity": "DAY",
                "disclosedQty": 0,
                "offlineOrder": False
            }
            
            print(f"   Symbol: {symbol}")
            logger.debug(f"Square off order params: {order_params}")
            
            # Place REAL order through Fyers API with timeout protection
            square_off_response = self.safe_api_call(self.fyers.place_order, data=order_params)
            
            if square_off_response and square_off_response.get('s') == 'ok':
                square_off_id = square_off_response.get('id', 'UNKNOWN')
                print(f"   ✅ Real square off order placed successfully!")
                print(f"   Square off Order ID: {square_off_id}")
                logger.info(f"Real square off order placed successfully! Order ID: {square_off_id}")
                # Clear position
                self.positions[option_type] = None
                # Check if VWAP override cycle should be completed
                self._check_vwap_override_cycle_completion()
            else:
                error_msg = f"Real square off order failed: {square_off_response}"
                print(f"   ❌ {error_msg}")
                logger.error(error_msg)
                raise Exception(error_msg)  # Raise exception to propagate error to web server
                
        except Exception as e:
            error_msg = f"Error placing real square off order: {e}"
            print(f"   ❌ {error_msg}")
            logger.error(error_msg)
            raise Exception(error_msg)  # Re-raise to propagate error to web server
            logger.error(error_msg)
    
    def square_off_all_positions(self):
        """Square off all active positions including both regular and long positions"""
        active_positions = [k for k, v in self.positions.items() if v is not None]
        active_long_positions = [k for k, v in self.long_positions.items() if v is not None]
        
        if not active_positions and not active_long_positions:
            print("ℹ️ No active positions to square off")
            return
        
        print(f"\n🔄 SQUARING OFF ALL POSITIONS")
        
        # Square off regular positions
        if active_positions:
            print(f"   Regular Positions: {', '.join(active_positions)}")
            for option_type in active_positions:
                self.square_off_position(option_type, "Square Off All Positions")
        
        # Square off long positions
        if active_long_positions:
            print(f"   Long Positions: {', '.join(active_long_positions)} (Enhanced Strategy)")
            for option_type in active_long_positions:
                self.square_off_real_long_position(option_type, "Square Off All Positions")
        
        print("✅ All positions squared off successfully")
        
        # Check if VWAP override cycle should be completed
        self._check_vwap_override_cycle_completion()
    
    def is_near_market_close(self, minutes_before_close: int = 5) -> bool:
        """Check if we are near market close"""
        now = self.get_ist_time()
        # Use current day's market end time
        market_end = now.replace(hour=15, minute=30, second=0, microsecond=0)
        close_time = market_end - timedelta(minutes=minutes_before_close)
        return now >= close_time
    
    def emergency_square_off(self, reason: str = "Market Close"):
        """Emergency virtual square off all positions including long positions"""
        active_positions = [k for k, v in self.positions.items() if v is not None]
        active_long_positions = [k for k, v in self.long_positions.items() if v is not None]
        
        if active_positions or active_long_positions:
            print(f"\n🚨 EMERGENCY REAL SQUARE OFF - {reason}")
            
            # Square off all real regular positions
            for option_type in active_positions:
                self.square_off_real_order(option_type, f"Emergency Exit - {reason}")
            
            # Square off all real long positions
            for option_type in active_long_positions:
                self.square_off_real_long_position(option_type, f"Emergency Exit - {reason}")
            
            # Check if VWAP override cycle should be completed
            self._check_vwap_override_cycle_completion()
            
            # Print final TRADING PORTFOLIO SUMMARY
            print("\n📊 FINAL TRADING PORTFOLIO SUMMARY:")
            self.print_trading_portfolio_summary()

    def get_position_pnl(self) -> Dict:
        """Calculate current P&L for all positions"""
        pnl_data = {"total_pnl": 0, "positions": {}}
        
        if not self.combined_premium_data:
            return pnl_data
        
        latest_data = self.combined_premium_data[-1]
        
        for option_type, position in self.positions.items():
            if position:
                # Get individual option prices
                current_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
                entry_price = position['entry_price']  # Individual entry price
                
                # Calculate P&L for this option
                if position['action'] == "SELL":
                    pnl = entry_price - current_price
                else:
                    pnl = current_price - entry_price
                
                pnl_data["positions"][option_type] = {
                    "entry_price": entry_price,
                    "current_price": current_price,
                    "pnl": pnl,
                    "action": position['action']
                }
                pnl_data["total_pnl"] += pnl
        
        return pnl_data

    def has_pending_orders(self) -> bool:
        """Check if there are any pending orders or active positions"""
        # Check for active positions
        active_positions = [k for k, v in self.positions.items() if v is not None]
        if active_positions:
            return True
        
        # If using Kite API, could check pending orders here
        # For now, we rely on position tracking
        return False
    
    def get_trading_status(self) -> Dict:
        """Get comprehensive trading status"""
        status = {
            "can_enter_new_trade": False,
            "has_active_positions": False,
            "can_enter_ce": False,
            "can_enter_pe": False,
            "market_conditions": {},
            "reasons": []
        }
        
        try:
            # Check individual positions (both short and long)
            ce_active = self.positions["CE"] is not None
            pe_active = self.positions["PE"] is not None
            ce_long_active = self.long_positions["CE"] is not None
            pe_long_active = self.long_positions["PE"] is not None
            
            status["has_active_positions"] = ce_active or pe_active or ce_long_active or pe_long_active
            
            # Determine what we can enter (prevent overlap with any existing positions)
            status["can_enter_ce"] = not (ce_active or ce_long_active)
            status["can_enter_pe"] = not (pe_active or pe_long_active)
            
            # We can enter new trade ONLY if BOTH legs are available (pure combined strategy)
            can_enter_any = status["can_enter_ce"] and status["can_enter_pe"]
            
            if not can_enter_any:
                if ce_active and pe_active:
                    status["reasons"].append("Both CE and PE positions already active")
                elif ce_active:
                    status["reasons"].append("CE position active - waiting for full exit before new entry")
                elif pe_active:
                    status["reasons"].append("PE position active - waiting for full exit before new entry")
                return status
            
            # Check market hours
            if not self.is_market_hours():
                status["reasons"].append("Outside market hours")
                return status
            
            # Check if we can place the first order (40 minutes after market opening)
            if not self.is_first_order_allowed():
                status["reasons"].append("First order not allowed yet (40 min after opening)")
                return status
            
            # Check if we're too close to market close
            if self.is_near_market_close(5):  # 5 minutes before close
                status["reasons"].append("Too close to market close")
                return status
            
            # Check if we have sufficient data
            # if len(self.combined_premium_data) < 5:
            #     status["reasons"].append("Insufficient market data")
            #     return status
            
            # Check if we have all required values
            if not all([self.current_nifty_price, self.current_atm_strike, self.current_vwap]):
                status["reasons"].append("Missing required market data")
                return status
            
            # Check if Fyers API is connected
            if not self.fyers:
                status["reasons"].append("Fyers API not connected")
                return status
            
            # Get current market conditions
            if self.combined_premium_data:
                latest_premium = self.combined_premium_data[-1]
                candle = self.get_decision_candle_data()
                
                if candle and self.current_vwap:
                    status["market_conditions"] = {
                        "current_premium": latest_premium['combined'],
                        "current_vwap": self.current_vwap,
                        "candle_close": candle['close'],
                        "below_vwap": candle['close'] < self.current_vwap,
                        "nifty_price": self.current_nifty_price,
                        "atm_strike": self.current_atm_strike,
                        "strike_difference": abs(self.current_nifty_price - self.current_atm_strike)
                    }
                    
                    # All conditions met for full straddle entry
                    status["can_enter_new_trade"] = True
                    status["reasons"].append("Ready for full straddle entry (combined strategy)")
                else:
                    status["reasons"].append("Cannot get current market data")
            else:
                status["reasons"].append("No premium data available")
            
            return status
            
        except Exception as e:
            status["reasons"].append(f"Error checking status: {e}")
            return status
    
    def manage_stop_losses(self):
        """Enhanced stop-loss management with selective exit based on individual premium trends - Production Trading"""
        logger.debug("Starting production stop-loss management...")
        if not self.combined_premium_data or not self.current_vwap:
            logger.warning("Stop-loss management skipped: Missing combined data or VWAP")
            return
        
        # Only manage SL every 1 minutes
        current_time = self.get_ist_time()
        # if self.last_sl_management_time:
        #     time_since_last = (current_time - self.last_sl_management_time).total_seconds()
        #     if time_since_last < 60: 
        #         logger.debug(f"Stop-loss management skipped: Only {time_since_last:.1f}s since last check (need 60s)")
        #         return
        
        # Check if we have any active positions
        active_positions = [k for k, v in self.positions.items() if v is not None]
        if not active_positions:
            logger.debug("No active positions for stop-loss management")
            return
        
        logger.info(f"Managing stop-losses for real positions: {active_positions}")
        
        # Update last management time
        self.last_sl_management_time = current_time
        
        # Get candle data based on decision interval for VWAP-based exit
        logger.debug(f"Fetching {self.decision_interval} candle data for stop-loss analysis...")
        candle = self.get_decision_candle_data()
        if not candle:
            logger.warning("No candle data available for stop-loss management")
            return
        
        latest_data = self.combined_premium_data[-1]
        current_price = latest_data['combined']
        
        # VWAP-based exit logic - only when current price is above VWAP
        if self.current_vwap is not None and current_price > self.current_vwap and ("CE" in active_positions and "PE" in active_positions):
            logger.info(f"PRODUCTION VWAP EXIT SIGNAL DETECTED! Close: {current_price:.2f} > VWAP: {self.current_vwap:.2f}")
            print(f"\n🚨 PRODUCTION VWAP EXIT SIGNAL DETECTED!")
            print(f"   Current Price: {current_price:.2f}")
            print(f"   VWAP: {self.current_vwap:.2f}")
            print(f"   Analyzing individual premium trends for real exit...")
            
            # Analyze individual premium trends for selective exit
            logger.debug("Executing production selective exit analysis based on individual premium trends")
            self._analyze_and_execute_selective_exit(active_positions)
            
        elif (len(active_positions) == 1):
            if self.current_vwap is not None:
                logger.debug(f"VWAP exit condition not met - Close: {current_price:.2f} <= VWAP: {self.current_vwap:.2f}")
            else:
                logger.debug(f"VWAP not available - Close: {current_price:.2f}")
            
            # Check if VWAP exit occurred in current candle before checking HA exits
            if self._is_vwap_exit_candle():
                logger.info("Single leg remaining but VWAP exit occurred in current candle - HA checks blocked")
                print(f"   🔒 Single leg HA exit blocked: VWAP exit in current candle")
            else:
                # Check for pending green Heikin Ashi exits
                logger.debug("Single leg remaining - checking HA exits (no VWAP exit conflict)")
                self._check_heikin_ashi_exits(active_positions)
            
            # Re-check active positions after HA exits (positions may have been closed)
            updated_active_positions = [k for k, v in self.positions.items() if v is not None]
            
            if updated_active_positions:
                # Print monitoring status
                print(f"\n📊 HEIKIN ASHI MONITORING")
                print(f"   Current Price: {current_price:.2f}")
                current_vwap_display = f"{self.current_vwap:.2f}" if self.current_vwap is not None else "Not calculated"
                print(f"   VWAP: {current_vwap_display}")
                print(f"   Status: Candle closed below VWAP - Holding real positions")
                
                # Show individual position status with unrealized P&L
                for option_type in updated_active_positions:
                    position = self.positions[option_type]
                    if position is None:  # Double-check position still exists
                        continue
                        
                    time_in_pos = self.get_ist_time() - position["timestamp"]
                    minutes = int(time_in_pos.total_seconds() / 60)
                    
                    # Calculate unrealized P&L for this position
                    if self.combined_premium_data:
                        latest_data = self.combined_premium_data[-1]
                        current_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
                        entry_price = position['entry_price']
                        
                        if position['action'] == "SELL":
                            pnl = (entry_price - current_price) * 75
                        else:
                            pnl = (current_price - entry_price) * 75
                        
                        pnl_status = "✅" if pnl > 0 else "❌"
                        
                        # Check if waiting for HA signal
                        if hasattr(self, 'waiting_for_ha_exit') and option_type in self.waiting_for_ha_exit:
                            print(f"   {option_type}: Waiting for Green Heikin Ashi ({minutes} min) - P&L: {pnl:.2f} {pnl_status}")
                        else:
                            print(f"   {option_type}: Holding for {minutes} min - P&L: {pnl:.2f} {pnl_status}")
            else:
                print(f"\n✅ All real positions have been closed")
                logger.info("All real positions have been closed")
    
    def _analyze_and_execute_selective_exit(self, active_positions):
        """Analyze individual premium trends and execute selective exits"""
        try:
            # Mark this candle as having VWAP exit to prevent HA exits in same candle
            self._mark_vwap_exit_candle()
            
            print(f"   📊 Analyzing trend using 1-minute candle data")
            
            # Analyze CE and PE trends using 1-minute candle data
            ce_trend = self._get_premium_trend("CE")
            pe_trend = self._get_premium_trend("PE")
            
            print(f"   CE Trend: {ce_trend}")
            logger.info(f"CE Trend: {ce_trend}")
            print(f"   PE Trend: {pe_trend}")
            logger.info(f"PE Trend: {pe_trend}")
            
            # Initialize waiting list if not exists
            if not hasattr(self, 'waiting_for_ha_exit'):
                self.waiting_for_ha_exit = set()
            
            # Check for both rising scenario first - don't place any orders
            if ("CE" in active_positions and ce_trend == "RISING" and 
                "PE" in active_positions and pe_trend == "RISING"):
                logger.info("Both CE and PE are RISING - Waiting for divergence before taking action")
                print(f"   ⚠️ Both CE and PE are RISING - Waiting for divergence")
                print(f"   🔒 No orders placed - Need one rising and one falling for selective exit")
                print(f"   🕐 Will check again in next cycle")
                return
            
            # Execute selective exits based on trends (only when one is rising)
            elif "CE" in active_positions and ce_trend == "RISING":
                logger.info("CE premium rising - Enhanced square off CE with directional trade")
                print(f"   📈 CE premium rising - Enhanced square off CE with directional trade")
                self.enhanced_square_off_with_real_directional_trade("CE", "CE Rising - VWAP Exit")
                
                # Keep PE for Heikin Ashi exit if it's not rising
                if "PE" in active_positions and pe_trend != "RISING":
                    logger.info("PE premium stable/falling - Waiting for Green Heikin Ashi")
                    print(f"   🟡 PE premium stable/falling - Waiting for Green Heikin Ashi")
                    self.waiting_for_ha_exit.add("PE")
            
            elif "PE" in active_positions and pe_trend == "RISING":
                logger.info("PE premium rising - Enhanced square off PE with directional trade")
                print(f"   📈 PE premium rising - Enhanced square off PE with directional trade")
                self.enhanced_square_off_with_real_directional_trade("PE", "PE Rising - VWAP Exit")
                
                # Keep CE for Heikin Ashi exit if it's not rising
                if "CE" in active_positions and ce_trend != "RISING":
                    logger.info("CE premium stable/falling - Waiting for Green Heikin Ashi")
                    print(f"   🟡 CE premium stable/falling - Waiting for Green Heikin Ashi")
                    self.waiting_for_ha_exit.add("CE")
            
            # else:
            #     # Both premiums are stable or falling - use enhanced square off for both
            #     logger.info("Both premiums stable/falling but above VWAP - Enhanced exit all positions")
            #     print(f"   � Both premiums stable/falling but above VWAP - Enhanced exit all positions")
            #     for option_type in active_positions:
            #         self.enhanced_square_off_with_directional_trade(option_type, "Both Stable - VWAP Exit")
                    
        except Exception as e:
            logger.error(f"Error in selective exit analysis: {e}")
            print(f"   ⚠️ Error in selective exit analysis: {e}")
            logger.warning("Falling back to exit all positions")
            print(f"   🔴 Falling back to exit all positions")
            for option_type in active_positions:
                self.square_off_position(option_type, "Error in Selective Exit Analysis")
    
    def _get_premium_trend(self, option_type):
        """Determine trend for individual option premium using previous 1-minute candle data"""
        try:
            if not self.fyers:
                logger.warning("Fyers API not available for trend analysis")
                return "NEUTRAL"
            
            if not self.combined_premium_data:
                logger.warning("No premium data available for symbol reference")
                return "NEUTRAL"
            
            # Get trading symbol from latest premium data
            latest_data = self.combined_premium_data[-1]
            if option_type == "CE":
                tradingsymbol = latest_data.get('ce_tradingsymbol')
            else:  # PE
                tradingsymbol = latest_data.get('pe_tradingsymbol')
            
            logger.debug(f"Retrieved {option_type} tradingsymbol from data: {tradingsymbol}")
            
            # Ensure symbol has proper NSE: prefix for historical data API
            if tradingsymbol and not tradingsymbol.startswith('NSE:'):
                logger.debug(f"Adding NSE: prefix to {tradingsymbol}")
                tradingsymbol = f"NSE:{tradingsymbol}"
            else:
                logger.debug(f"Symbol already has NSE: prefix: {tradingsymbol}")
            
            if not tradingsymbol:
                logger.warning(f"No trading symbol available for {option_type}")
                return "NEUTRAL"
            
            # Get current time and fetch last 3 minutes of 1-minute data to get previous completed candles
            to_date = self.get_ist_time()
            from_date = to_date - timedelta(minutes=4)  # Get 4 minutes to ensure we have completed candles
            
            logger.debug(f"Fetching 1-minute candle data for {option_type} trend: {tradingsymbol}")
            
            # Fetch 1-minute historical data
            historical_data = self._get_historical_data_with_rate_limit(
                symbol=tradingsymbol,
                from_date=from_date,
                to_date=to_date,
                resolution="1"  # 1-minute candles
            )
            
            if not historical_data or len(historical_data) < 2:
                logger.warning(f"Insufficient 1-minute candle data for {option_type} trend analysis")
                return "NEUTRAL"
            
            # Get the previous completed candle (second last, since last one might be forming)
            if len(historical_data) >= 2:
                prev_candle = historical_data[-2]  # Previous completed 1-minute candle
            else:
                prev_candle = historical_data[-1]  # Use last available if only one candle
            
            # Get current minute candle high from our real-time tracking
            current_high = self._get_current_minute_high(option_type)
            
            if current_high == 0:
                logger.warning(f"No current minute high available for {option_type}, falling back to quote API")
                # Fallback to quote API if current minute tracking not available
                try:
                    quote_response = self.safe_api_call(self.fyers.quotes, {"symbols": tradingsymbol})
                    if quote_response and quote_response.get('s') == 'ok':
                        quote_data = quote_response.get('d', [])
                        if quote_data and len(quote_data) > 0:
                            current_high = quote_data[0].get('v', {}).get('lp', 0)  # Use last price as fallback
                            logger.debug(f"Fallback: Using last price for {option_type}: {current_high:.2f}")
                        else:
                            logger.warning(f"No quote data available for {option_type}")
                            return "NEUTRAL"
                    else:
                        logger.warning(f"Quote API failed for {option_type}")
                        return "NEUTRAL"
                except Exception as quote_error:
                    logger.warning(f"Error fetching fallback quote for {option_type}: {quote_error}")
                    return "NEUTRAL"
            
            if current_high == 0:
                logger.error(f"Current minute high not available for {option_type}")
                return "NEUTRAL"
            
            # Extract previous candle OHLC data
            prev_open = prev_candle['open']
            prev_high = prev_candle['high']
            prev_low = prev_candle['low']
            prev_close = prev_candle['close']
            
            # Determine previous candle color
            prev_candle_color = "RED" if prev_close < prev_open else "GREEN"
            
            logger.debug(f"{option_type} candle analysis:")
            logger.debug(f"   Previous candle: O={prev_open:.2f}, H={prev_high:.2f}, L={prev_low:.2f}, C={prev_close:.2f}")
            logger.debug(f"   Previous candle color: {prev_candle_color}")
            logger.debug(f"   Current minute high: {current_high:.2f}")
            
            # Apply your specific RISING logic
            is_rising = False
            
            if prev_candle_color == "RED":
                # RED candle: Current high > Previous candle Open
                if current_high > prev_open:
                    is_rising = True
                    logger.debug(f"   RISING detected: RED candle + Current Minute High ({current_high:.2f}) > Prev Open ({prev_open:.2f})")
            elif prev_candle_color == "GREEN":
                # GREEN candle: Current high > Previous candle Close  
                if current_high > prev_close:
                    is_rising = True
                    logger.debug(f"   RISING detected: GREEN candle + Current Minute High ({current_high:.2f}) > Prev Close ({prev_close:.2f})")
            
            if is_rising:
                logger.debug(f"{option_type} trend: RISING (custom logic)")
                return "RISING"
            else:
                logger.debug(f"{option_type} trend: NEUTRAL (custom logic - not rising)")
                return "NEUTRAL"
                    
        except Exception as e:
            logger.error(f"Error calculating trend for {option_type}: {e}")
            print(f"   ⚠️ Error calculating trend for {option_type}: {e}")
            return "NEUTRAL"
    
    def get_current_trends(self) -> dict:
        """Get current CE and PE trends for display purposes"""
        try:
            if not self.combined_premium_data or len(self.combined_premium_data) < 4:
                return {
                    "ce_trend": "NEUTRAL", 
                    "pe_trend": "NEUTRAL",
                    "ha_trend": "NEUTRAL",
                    "data_points": len(self.combined_premium_data) if self.combined_premium_data else 0
                }
            
            # Calculate CE and PE trends using 1-minute candle data
            ce_trend = self._get_premium_trend("CE")
            pe_trend = self._get_premium_trend("PE")
            
            # Get Heikin Ashi trend
            ha_trend = self.get_heikin_ashi_trend()
            
            return {
                "ce_trend": ce_trend,
                "pe_trend": pe_trend, 
                "ha_trend": ha_trend,
                "data_points": len(self.combined_premium_data)
            }
            
        except Exception as e:
            logger.error(f"Error getting current trends: {e}")
            return {
                "ce_trend": "NEUTRAL",
                "pe_trend": "NEUTRAL", 
                "ha_trend": "NEUTRAL",
                "data_points": 0
            }

    def reset_trading_disabled_state(self):
        """Reset trading disabled state after fixing issues"""
        if self.trading_disabled:
            logger.info(f"Resetting trading disabled state. Previous reason: {self.trading_disabled_reason}")
            print(f"✅ Resetting trading disabled state")
            print(f"   Previous reason: {self.trading_disabled_reason}")
            
            self.trading_disabled = False
            self.trading_disabled_reason = None
            self.is_running = True  # Ensure system is marked as running
            logger.info("Trading re-enabled. System can now place new orders.")
            print(f"   🟢 Trading re-enabled. System can now place new orders.")
            return True
        else:
            logger.info("Trading was not disabled")
            print(f"ℹ️ Trading was not disabled")
            return False

    def get_trading_safety_status(self) -> Dict:
        """Get current trading safety status"""
        return {
            "trading_disabled": self.trading_disabled,
            "trading_disabled_reason": self.trading_disabled_reason,
            "is_running": self.is_running,
            "can_place_orders": not self.trading_disabled and self.is_running
        }

    def _check_vwap_override_cycle_completion(self):
        """Check if VWAP override cycle should be marked as completed"""
        logger.debug("Checking VWAP override cycle completion")
        logger.debug(f"VWAP override enabled: {self.vwap_override_enabled}")
        logger.debug(f"VWAP override cycle state: {self.vwap_override_cycle_state}")
        
        if not self.vwap_override_enabled:
            logger.debug("VWAP override not enabled - skipping cycle completion check")
            return
            
        if self.vwap_override_cycle_state != "ACTIVE":
            logger.debug(f"VWAP override cycle not ACTIVE (current: {self.vwap_override_cycle_state}) - skipping cycle completion check")
            return
        
        # Check if all positions are closed (both regular and long positions)
        active_positions = any(pos is not None for pos in self.positions.values())
        active_long_positions = any(pos is not None for pos in self.long_positions.values())
        
        logger.debug(f"Active regular positions: {active_positions} - {[k for k, v in self.positions.items() if v is not None]}")
        logger.debug(f"Active long positions: {active_long_positions} - {[k for k, v in self.long_positions.items() if v is not None]}")
        
        if not active_positions and not active_long_positions:
            self.vwap_override_cycle_state = "COMPLETED"
            logger.info("VWAP override cycle marked as COMPLETED - all positions closed")
            print("   🔄 VWAP override cycle COMPLETED - no new orders until reset")
            
            # Trigger immediate status broadcast if callback is available
            if hasattr(self, 'status_change_callback') and self.status_change_callback:
                try:
                    self.status_change_callback("vwap_cycle_completed")
                except Exception as e:
                    logger.warning(f"Failed to trigger status change callback: {e}")
        else:
            logger.debug("VWAP override cycle remains ACTIVE - positions still open")

    def get_vwap_override_cycle_status(self) -> Dict:
        """Get VWAP override cycle status for API response"""
        return {
            "vwap_override_enabled": self.vwap_override_enabled,
            "state": self.vwap_override_cycle_state,  # Changed from "cycle_state" to "state"
            "started": self.vwap_override_cycle_started,  # Changed from "cycle_started" to "started" 
            "can_reset_cycle": self.vwap_override_enabled and self.vwap_override_cycle_state == "COMPLETED"
        }

    def reset_vwap_override_cycle(self) -> Dict:
        """Reset VWAP override cycle to allow new orders"""
        if not self.vwap_override_enabled:
            return {"success": False, "message": "VWAP override not enabled"}
        
        if self.vwap_override_cycle_state != "COMPLETED":
            return {"success": False, "message": f"Cannot reset cycle in {self.vwap_override_cycle_state} state"}
        
        # Check that no positions are active
        active_positions = any(pos is not None for pos in self.positions.values())
        active_long_positions = any(pos is not None for pos in self.long_positions.values())
        
        if active_positions or active_long_positions:
            return {"success": False, "message": "Cannot reset cycle with active positions"}
        
        # Reset cycle state
        self.vwap_override_cycle_state = "READY"
        logger.info("VWAP override cycle reset to READY state")
        print("🔄 VWAP override cycle reset - ready for new orders")
        
        return {"success": True, "message": "VWAP override cycle reset successfully"}

    def reset_all_trading_blocks(self) -> Dict:
        """Consolidated reset for both trading disabled state and VWAP override cycle"""
        results = {
            "trading_disabled_reset": {"attempted": False, "success": False, "message": ""},
            "vwap_cycle_reset": {"attempted": False, "success": False, "message": ""},
            "overall_success": False,
            "message": ""
        }
        
        try:
            # Check if trading is disabled
            if self.trading_disabled:
                results["trading_disabled_reset"]["attempted"] = True
                reset_success = self.reset_trading_disabled_state()
                results["trading_disabled_reset"]["success"] = reset_success
                results["trading_disabled_reset"]["message"] = "Trading disabled state reset" if reset_success else "Failed to reset trading disabled state"
                logger.info(f"Trading disabled reset attempted: {reset_success}")
            else:
                results["trading_disabled_reset"]["message"] = "Trading was not disabled"
            
            # Check if VWAP override cycle needs reset
            if self.vwap_override_enabled and self.vwap_override_cycle_state == "COMPLETED":
                results["vwap_cycle_reset"]["attempted"] = True
                vwap_result = self.reset_vwap_override_cycle()
                results["vwap_cycle_reset"]["success"] = vwap_result["success"]
                results["vwap_cycle_reset"]["message"] = vwap_result["message"]
                logger.info(f"VWAP cycle reset attempted: {vwap_result['success']}")
            else:
                if not self.vwap_override_enabled:
                    results["vwap_cycle_reset"]["message"] = "VWAP override not enabled"
                elif self.vwap_override_cycle_state != "COMPLETED":
                    results["vwap_cycle_reset"]["message"] = f"VWAP cycle in {self.vwap_override_cycle_state} state - no reset needed"
            
            # Determine overall success
            trading_disabled_ok = not results["trading_disabled_reset"]["attempted"] or results["trading_disabled_reset"]["success"]
            vwap_cycle_ok = not results["vwap_cycle_reset"]["attempted"] or results["vwap_cycle_reset"]["success"]
            results["overall_success"] = trading_disabled_ok and vwap_cycle_ok
            
            # Compile overall message
            if results["overall_success"]:
                messages = []
                if results["trading_disabled_reset"]["attempted"] and results["trading_disabled_reset"]["success"]:
                    messages.append("Trading re-enabled")
                if results["vwap_cycle_reset"]["attempted"] and results["vwap_cycle_reset"]["success"]:
                    messages.append("VWAP cycle reset")
                
                if not messages:
                    results["message"] = "No reset actions were needed - trading already enabled"
                else:
                    results["message"] = f"✅ Reset completed: {', '.join(messages)}"
                
                logger.info("Consolidated reset completed successfully")
                print("🔄 Consolidated reset completed - trading fully enabled")
            else:
                error_messages = []
                if results["trading_disabled_reset"]["attempted"] and not results["trading_disabled_reset"]["success"]:
                    error_messages.append("trading disabled state")
                if results["vwap_cycle_reset"]["attempted"] and not results["vwap_cycle_reset"]["success"]:
                    error_messages.append("VWAP cycle")
                
                results["message"] = f"❌ Failed to reset: {', '.join(error_messages)}"
                logger.error(f"Consolidated reset failed for: {error_messages}")
            
            return results
            
        except Exception as e:
            error_msg = f"Error in consolidated reset: {e}"
            logger.error(error_msg)
            results["overall_success"] = False
            results["message"] = error_msg
            return results

    def _is_doji_candle(self, candle_data: Dict, doji_threshold: float = 0.1) -> Dict:
        """
        Detect Doji candle patterns in OHLC data
        Returns dict with doji type and characteristics
        """
        try:
            if not candle_data or not all(key in candle_data for key in ['open', 'high', 'low', 'close']):
                return {"is_doji": False, "type": "NONE", "body_ratio": 0}
            
            open_price = candle_data['open']
            high_price = candle_data['high']
            low_price = candle_data['low']
            close_price = candle_data['close']
            
            # Calculate body and shadows
            body_size = abs(close_price - open_price)
            total_range = high_price - low_price
            upper_shadow = high_price - max(open_price, close_price)
            lower_shadow = min(open_price, close_price) - low_price
            
            # Avoid division by zero
            if total_range == 0:
                return {"is_doji": False, "type": "NONE", "body_ratio": 0}
            
            # Calculate body ratio (body size relative to total range)
            body_ratio = (body_size / total_range) * 100
            
            # Doji detection: body is very small relative to total range
            is_doji = body_ratio <= doji_threshold
            
            if not is_doji:
                return {"is_doji": False, "type": "NONE", "body_ratio": body_ratio}
            
            # Classify Doji types based on shadow characteristics
            doji_type = "STANDARD"  # Default
            
            # Dragonfly Doji: Long lower shadow, little/no upper shadow
            if lower_shadow > (total_range * 0.6) and upper_shadow < (total_range * 0.1):
                doji_type = "DRAGONFLY"
            
            # Gravestone Doji: Long upper shadow, little/no lower shadow
            elif upper_shadow > (total_range * 0.6) and lower_shadow < (total_range * 0.1):
                doji_type = "GRAVESTONE"
            
            # Long-Legged Doji: Both shadows are long
            elif upper_shadow > (total_range * 0.3) and lower_shadow > (total_range * 0.3):
                doji_type = "LONG_LEGGED"
            
            return {
                "is_doji": True,
                "type": doji_type,
                "body_ratio": body_ratio,
                "body_size": body_size,
                "total_range": total_range,
                "upper_shadow": upper_shadow,
                "lower_shadow": lower_shadow
            }
            
        except Exception as e:
            logger.error(f"Error detecting Doji pattern: {e}")
            return {"is_doji": False, "type": "NONE", "body_ratio": 0}
    
    def _check_heikin_ashi_exits(self, active_positions):
        """Check for individual CE/PE Heikin Ashi and Doji exit signals for positions waiting for HA exit"""
        try:
            # Check if VWAP exit occurred in current candle - if so, skip HA exits
            if self._is_vwap_exit_candle():
                logger.info("VWAP exit occurred in current candle - skipping HA exit checks to avoid conflicts")
                print(f"   🔒 Skipping HA exits: VWAP exit already processed in this candle")
                return
            
            logger.debug("Checking individual CE/PE Heikin Ashi/Doji exits for legs: %s", getattr(self, 'waiting_for_ha_exit', set()))
            if not hasattr(self, 'waiting_for_ha_exit') or not self.waiting_for_ha_exit:
                logger.debug("No legs waiting for HA exit.")
                return
            
            # Check for tick-based upper wick exits first (fastest exit)
            upper_wick_exits = []
            
            for option_type in list(self.waiting_for_ha_exit):
                if option_type in active_positions:
                    # Calculate tick-based Heikin Ashi
                    self.calculate_tick_heikin_ashi(option_type)
                    
                    # Check upper wick exit condition
                    wick_result = self.check_upper_wick_exit_condition(option_type)
                    
                    if wick_result["exit_signal"]:
                        logger.info(f"{option_type} Upper wick exit triggered: {wick_result['reason']}")
                        upper_wick_exits.append((option_type, wick_result))
            
            # Execute upper wick exits immediately
            if upper_wick_exits:
                for option_type, wick_result in upper_wick_exits:
                    print(f"\n⚡ {option_type} UPPER WICK EXIT DETECTED!")
                    print(f"   Upper Wick: {wick_result['upper_wick_size']:.1f} pts (Threshold: {wick_result['threshold_value']:.1f} pts)")
                    print(f"   Max High: {wick_result['max_high_seen']:.2f}, HA Open: {wick_result['minute_ha_open']:.2f}, Min Low: {wick_result['min_low_seen']:.2f}")
                    print(f"   🔴 Fast exit due to upper wick formation")
                    
                    if self.positions[option_type] is not None:
                        print(f"   🔴 Squaring off {option_type} due to upper wick signal")
                        logger.info(f"Squaring off {option_type} due to upper wick signal")
                        self.square_off_position(option_type, f"Upper Wick Exit - {wick_result['upper_wick_size']:.1f}pts")
                        self.waiting_for_ha_exit.discard(option_type)
                
                # Clear waiting list if empty
                if not self.waiting_for_ha_exit:
                    delattr(self, 'waiting_for_ha_exit')
                return
            
            # Check for Doji exit on individual candles (applies to all waiting positions)
            doji_exit_positions = []
            
            for option_type in list(self.waiting_for_ha_exit):
                if option_type in active_positions:
                    # Get individual candle data for this specific option
                    individual_candle = self.get_individual_candle_data(option_type)
                    
                    if individual_candle:
                        logger.debug("Individual %s candle for Doji analysis: %s", option_type, individual_candle)
                        doji_info = self._is_doji_candle(individual_candle, doji_threshold=0.15)  # 0.15% threshold for options
                        logger.debug("%s Doji analysis result: %s", option_type, doji_info)
                        
                        if doji_info["is_doji"]:
                            logger.info("%s Doji candle detected (%s)", option_type, doji_info['type'])
                            doji_exit_positions.append((option_type, doji_info))
            
            # Exit positions with Doji signals
            if doji_exit_positions:
                for option_type, doji_info in doji_exit_positions:
                    print(f"\n🎯 {option_type} DOJI CANDLE DETECTED!")
                    print(f"   Type: {doji_info['type']}")
                    print(f"   Body Ratio: {doji_info['body_ratio']:.2f}%")
                    print(f"   🔴 Exiting {option_type} due to individual market indecision signal")
                    
                    if self.positions[option_type] is not None:
                        print(f"   🔴 Squaring off {option_type} due to Doji {doji_info['type']}")
                        logger.info(f"Squaring off {option_type} due to Doji {doji_info['type']}")
                        self.square_off_position(option_type, f"Doji Exit - {doji_info['type']}")
                        self.waiting_for_ha_exit.discard(option_type)
                
                # Clear waiting list if empty
                if not self.waiting_for_ha_exit:
                    delattr(self, 'waiting_for_ha_exit')
                return
            
            # Check individual CE and PE Heikin Ashi for selective exits (green candles)
            positions_to_exit = []
            
            # Check CE Heikin Ashi if CE is waiting
            if "CE" in self.waiting_for_ha_exit and len(self.heikin_ashi_ce_data) > 0:
                latest_ce_ha = self.heikin_ashi_ce_data[-1]
                is_green_ce_ha = latest_ce_ha['ha_close'] > latest_ce_ha['ha_open']
                
                logger.debug("CE HA analysis: %s", latest_ce_ha)
                logger.debug("CE HA is green: %s", is_green_ce_ha)
                
                if is_green_ce_ha:
                    logger.info("Green CE Heikin Ashi detected, exiting CE")
                    print(f"\n🟢 GREEN CE HEIKIN ASHI DETECTED!")
                    print(f"   CE HA Open: {latest_ce_ha['ha_open']:.2f}")
                    print(f"   CE HA Close: {latest_ce_ha['ha_close']:.2f}")
                    print(f"   🔴 Exiting CE due to bullish momentum")
                    positions_to_exit.append(("CE", "Green CE Heikin Ashi"))
            
            # Check PE Heikin Ashi if PE is waiting
            if "PE" in self.waiting_for_ha_exit and len(self.heikin_ashi_pe_data) > 0:
                latest_pe_ha = self.heikin_ashi_pe_data[-1]
                is_green_pe_ha = latest_pe_ha['ha_close'] > latest_pe_ha['ha_open']
                
                logger.debug("PE HA analysis: %s", latest_pe_ha)
                logger.debug("PE HA is green: %s", is_green_pe_ha)
                
                if is_green_pe_ha:
                    logger.info("Green PE Heikin Ashi detected, exiting PE")
                    print(f"\n🟢 GREEN PE HEIKIN ASHI DETECTED!")
                    print(f"   PE HA Open: {latest_pe_ha['ha_open']:.2f}")
                    print(f"   PE HA Close: {latest_pe_ha['ha_close']:.2f}")
                    print(f"   🔴 Exiting PE due to bullish momentum")
                    positions_to_exit.append(("PE", "Green PE Heikin Ashi"))
            
            # Execute individual exits
            if positions_to_exit:
                logger.debug("Exiting individual legs based on their HA signals: %s", positions_to_exit)
                for option_type, exit_reason in positions_to_exit:
                    if option_type in active_positions and self.positions[option_type] is not None:
                        print(f"   🔴 Squaring off {option_type} due to {exit_reason}")
                        logger.info(f"Squaring off {option_type} due to {exit_reason}")
                        logger.debug(f"About to call square_off_position with option_type='{option_type}', exit_reason='{exit_reason}'")
                        self.square_off_position(option_type, exit_reason)
                        
                        # Remove from waiting list
                        if hasattr(self, 'waiting_for_ha_exit') and option_type in self.waiting_for_ha_exit:
                            self.waiting_for_ha_exit.remove(option_type)
                            logger.debug("Removed %s from waiting_for_ha_exit", option_type)
                
                # Clear waiting list if empty
                if hasattr(self, 'waiting_for_ha_exit') and not self.waiting_for_ha_exit:
                    logger.debug("All legs exited, clearing waiting_for_ha_exit attribute.")
                    delattr(self, 'waiting_for_ha_exit')
            else:
                # Show waiting status with detailed analysis including upper wick info
                waiting_positions = [pos for pos in self.waiting_for_ha_exit if pos in active_positions]
                logger.debug("Still waiting for individual HA exit signals for: %s", waiting_positions)
                if waiting_positions:
                    print(f"\n🟡 MONITORING INDIVIDUAL LEGS FOR HA TICK EXIT SIGNALS")
                    
                    # Show individual HA status and upper wick status for each waiting position
                    for option_type in waiting_positions:
                        if option_type == "CE" and len(self.heikin_ashi_ce_data) > 0:
                            latest_ce_ha = self.heikin_ashi_ce_data[-1]
                            ce_status = " Red" if latest_ce_ha['ha_close'] < latest_ce_ha['ha_open'] else "🟡 Neutral"
                            print(f"   CE HA: {ce_status} (O:{latest_ce_ha['ha_open']:.2f}, C:{latest_ce_ha['ha_close']:.2f})")
                            logger.debug("CE HA status: %s", ce_status)
                            
                            # Show upper wick status for CE
                            if self.tick_ha_ce_data:
                                wick_result = self.check_upper_wick_exit_condition("CE")
                                print(f"   CE Upper Wick: {wick_result['upper_wick_size']:.1f} pts (Threshold: {wick_result['threshold_value']:.1f} pts)")
                        
                        elif option_type == "PE" and len(self.heikin_ashi_pe_data) > 0:
                            latest_pe_ha = self.heikin_ashi_pe_data[-1]
                            pe_status = " Red" if latest_pe_ha['ha_close'] < latest_pe_ha['ha_open'] else "🟡 Neutral"
                            print(f"   PE HA: {pe_status} (O:{latest_pe_ha['ha_open']:.2f}, C:{latest_pe_ha['ha_close']:.2f})")
                            logger.debug("PE HA status: %s", pe_status)
                            
                            # Show upper wick status for PE
                            if self.tick_ha_pe_data:
                                wick_result = self.check_upper_wick_exit_condition("PE")
                                print(f"   PE Upper Wick: {wick_result['upper_wick_size']:.1f} pts (Threshold: {wick_result['threshold_value']:.1f} pts)")
                        
                        else:
                            print(f"   {option_type}: Waiting for HA data...")
                            logger.debug("%s: Waiting for HA data", option_type)
                    
                    # Show Doji status for individual options
                    for option_type in waiting_positions:
                        individual_candle = self.get_individual_candle_data(option_type)
                        if individual_candle:
                            doji_info = self._is_doji_candle(individual_candle, doji_threshold=0.15)
                            if not doji_info["is_doji"]:
                                print(f"   {option_type} Candle: Regular (Body: {doji_info['body_ratio']:.2f}%)")
                                logger.debug("%s candle is not Doji. Body ratio: %.2f%%", option_type, doji_info['body_ratio'])
                    
                    print(f"   Legs waiting: {', '.join(waiting_positions)}")
                    logger.debug("Legs still waiting: %s", waiting_positions)
                    
                    # Show individual leg P&L while waiting
                    for option_type in waiting_positions:
                        if option_type in active_positions and self.combined_premium_data:
                            position = self.positions[option_type]
                            latest_data = self.combined_premium_data[-1]
                            current_price = latest_data['CE'] if option_type == "CE" else latest_data['PE']
                            entry_price = position['entry_price']
                            
                            if position['action'] == "SELL":
                                pnl = (entry_price - current_price) * 75
                            else:
                                pnl = (current_price - entry_price) * 75
                            
                            pnl_status = "✅" if pnl > 0 else "❌"
                            time_in_pos = self.get_ist_time() - position["timestamp"]
                            minutes = int(time_in_pos.total_seconds() / 60)
                            
                            print(f"      {option_type}: {minutes}min - P&L: {pnl:.2f} {pnl_status}")
                            logger.debug("Leg %s: %dmin - P&L: %.2f %s", option_type, minutes, pnl, pnl_status)
                            
        except Exception as e:
            logger.error(f"Error checking individual leg exits: {e}")
            print(f"   ⚠️ Error checking individual leg exits: {e}")

def load_credentials():
    """Load Fyers API credentials from config.txt file"""
    config_file = "config.txt"
    credentials = {
        "CLIENT_ID": None,
        "CLIENT_SECRET": None,
        "REDIRECT_URI": "https://www.google.com/"
    }
    
    try:
        if os.path.exists(config_file):
            print(f"📄 Loading credentials from {config_file}...")
            with open(config_file, 'r') as f:
                for line in f:
                    line = line.strip()
                    if line and not line.startswith('#'):  # Skip empty lines and comments
                        if '=' in line:
                            key, value = line.split('=', 1)
                            key = key.strip()
                            value = value.strip()
                            if key in credentials:
                                credentials[key] = value
                                print(f"   ✅ {key}: {'*' * len(value[:8])}...")
            
            # Validate required credentials
            if credentials["CLIENT_ID"] and credentials["CLIENT_SECRET"]:
                print("✅ Credentials loaded successfully")
                return credentials
            else:
                print("❌ Missing required credentials in config.txt")
                return None
        else:
            print(f"⚠️ {config_file} not found. Creating sample file...")
            # Create sample config file
            with open(config_file, 'w') as f:
                f.write("# Fyers API v3 Configuration\n")
                f.write("# Replace the values below with your actual Fyers API credentials\n")
                f.write("# You can get these from: https://myapi.fyers.in/\n\n")
                f.write("CLIENT_ID=your_fyers_client_id_here\n")
                f.write("CLIENT_SECRET=your_fyers_client_secret_here\n")
                f.write("REDIRECT_URI=https://www.google.com/\n\n")
                f.write("# Lines starting with # are comments and will be ignored\n")
            print(f"📝 Sample {config_file} created. Please edit it with your credentials.")
            return None
            
    except Exception as e:
        print(f"❌ Error loading credentials: {e}")
        return None

def main():
    """Main function to setup and run the Nifty options virtual trader with UI integration"""
    print("=" * 70)
    print("🔄 NIFTY 50 OPTIONS VIRTUAL TRADER - UI INTEGRATED MODE")
    print("=" * 70)
    print("🎯 IMPORTANT: This program runs in SIMULATION MODE")
    print("   * Uses LIVE market data from Fyers API v3")
    print("   * Places VIRTUAL orders only")
    print("   * No real money trades")
    print("   * Safe for testing strategies")
    print("   * Configuration loaded from web UI files")
    print("=" * 70)
    
    print("\n🚀 Initializing trader with web UI configuration...")
    print("📁 Loading config from: config.txt, access.txt, vwap_override.txt, expiry_override.txt")
    
    # Initialize trader with auto-config loading from UI files
    trader = NiftyOptionsTrader(auto_load_config=True)
    
    # Check if we have valid API configuration
    if trader.fyers:
        print("\n✅ Connected to Fyers API v3 with UI configuration")
        print("🔄 Starting VIRTUAL trading with LIVE data...")
        
        # Test connection before starting
        try:
            print("🧪 Testing API connection...")
            nifty_price = trader.get_nifty_price()
            if nifty_price:
                print(f"✅ API test successful - Live Nifty: {nifty_price:.2f}")
                print("🎯 Starting automated trading strategy...")
                print("\n" + "=" * 50)
                print("📊 LIVE TRADING SESSION STARTED")
                print("=" * 50)
                trader.start()
            else:
                print("❌ API test failed - cannot fetch Nifty price")
                _show_ui_config_help()
        except Exception as e:
            print(f"❌ API test failed: {e}")
            print("💡 Please check your configuration in the web UI")
            _show_ui_config_help()
    else:
        print("\n⚠️ Running in DEMO MODE - API credentials not configured")
        print("📊 This will simulate basic functionality only")
        
        # Show configuration help
        _show_ui_config_help()
        
        # Ask if user wants to continue in demo mode
        demo_choice = input("\nDo you want to continue in DEMO mode? (y/n): ").strip().lower()
        if demo_choice == 'y':
            print("✅ Starting in demo mode...")
            trader.print_trading_portfolio_summary()
        else:
            print("👋 Please configure API credentials via web UI and restart")
            return

def _show_ui_config_help():
    """Show help for configuring via web UI"""
    print("\n" + "=" * 50)
    print("📋 HOW TO CONFIGURE VIA WEB UI:")
    print("=" * 50)
    print("1. 🌐 Start the web server:")
    print("   python -m uvicorn web_server:app --host 0.0.0.0 --port 8000")
    print()
    print("2. 🖥️ Open web interface:")
    print("   http://localhost:8000")
    print()
    print("3. ⚙️ Configure in the 'Configuration' section:")
    print("   • Enter Fyers Client ID and Client Secret")
    print("   • Enter Access Token (get from Fyers app or API)")
    print("   • Set VWAP Override (optional)")
    print("   • Set Expiry Date (required for options trading)")
    print("   • Click 'Save API Config'")
    print()
    print("4. 🔄 Restart this trading bot:")
    print("   python3 fyers_vwap_9_1.py")
    print()
    print("📁 Configuration files will be created:")
    print("   • config.txt (API credentials)")
    print("   • access.txt (Access token)")
    print("   • vwap_override.txt (VWAP override)")
    print("   • expiry_override.txt (Expiry date)")
    print("=" * 50)

def main_legacy():
    """Legacy main function with manual choices (kept for reference)"""
    print("=" * 60)
    print("🔄 NIFTY 50 OPTIONS VIRTUAL TRADER - LEGACY MODE")
    print("=" * 60)
    print("🎯 IMPORTANT: This program runs in SIMULATION MODE")
    print("   * Uses LIVE market data from Fyers API v3")
    print("   * Places VIRTUAL orders only")
    print("   * No real money trades")
    print("   * Safe for testing strategies")
    print("=" * 60)
    
    # Load credentials from config file
    credentials = load_credentials()
    if not credentials:
        print("\n❌ Cannot proceed without valid credentials.")
        print("💡 Please edit config.txt with your Fyers API credentials and try again.")
        return
    
    CLIENT_ID = credentials["CLIENT_ID"]
    CLIENT_SECRET = credentials["CLIENT_SECRET"]
    REDIRECT_URI = credentials["REDIRECT_URI"]
    
    print("Choose your setup option:")
    print("1. Manual token entry (recommended for first time)")
    print("2. Use saved access token")
    print("3. Run without API (demo mode with simulated data)")
    
    choice = input("Enter choice (1, 2, or 3): ").strip()
    
    if choice == "1":
        # Manual setup with login flow
        print("\n🔑 Setting up Fyers API v3 for live data...")
        print("📊 Remember: Orders will be VIRTUAL only!")
        
        # Initialize trader
        trader = NiftyOptionsTrader(auto_load_config=False)
        
        # Setup API and get login URL
        fyers_session = trader.setup_fyers_api(CLIENT_ID, CLIENT_SECRET, REDIRECT_URI)
        
        if not fyers_session:
            print("❌ Failed to setup Fyers API v3")
            return
        
        # Wait for user to get authorization code
        auth_code = input("\nEnter the authorization code from the redirect URL: ").strip()
        
        if not auth_code:
            print("❌ No authorization code provided")
            return
        
        # Generate access token
        if trader.set_authorization_code(auth_code, fyers_session):
            print(f"✅ Access token generated: {trader.access_token}")
            print("💡 Save this access token for future use (valid until next login)")
            print("🔄 Starting VIRTUAL trading with LIVE data...")
            
            # Start virtual trading
            trader.start()
        else:
            print("❌ Failed to generate access token")
            
    elif choice == "2":
        # Use saved access token
        client_id = CLIENT_ID
        
        # Check for saved access token file first
        saved_token = None
        if os.path.exists('access.txt'):
            try:
                with open('access.txt', 'r') as f:
                    saved_token = f.read().strip()
                if saved_token:
                    print(f"📄 Found saved access token in access.txt")
                    use_saved = input("Use saved token? (y/n): ").strip().lower()
                    if use_saved == 'y':
                        access_token = saved_token
                    else:
                        access_token = input("Enter your access token: ").strip()
                else:
                    access_token = input("Enter your access token: ").strip()
            except Exception as e:
                print(f"⚠️ Could not read access.txt: {e}")
                access_token = input("Enter your access token: ").strip()
        else:
            access_token = input("Enter your access token: ").strip()
        
        if not client_id or not access_token:
            print("❌ Client ID and access token are required")
            return
        
        # Initialize trader with saved token
        trader = NiftyOptionsTrader(client_id=client_id, access_token=access_token, auto_load_config=False)
        
        if trader.fyers:
            print("✅ Connected to Fyers API v3 with saved token")
            print("🔄 Starting VIRTUAL trading with LIVE data...")
            
            # Test connection
            try:
                nifty_price = trader.get_nifty_price()
                if nifty_price:
                    print(f"✅ API test successful - Live Nifty: {nifty_price:.2f}")
                    trader.start()
                else:
                    print("❌ API test failed - cannot fetch Nifty price")
            except Exception as e:
                print(f"❌ API test failed: {e}")
                print("💡 Try option 1 for fresh login")
        else:
            print("❌ Failed to initialize with saved token")
            print("💡 Try option 1 for fresh login")
    
    elif choice == "3":
        # Run without API (demo mode)
        print("\n🔄 Running in DEMO MODE without real market data...")
        print("📊 This will simulate basic functionality only")
        
        # Initialize trader without API
        trader = NiftyOptionsTrader(auto_load_config=False)
        print("✅ Virtual trader initialized in demo mode")
        print("💡 For full functionality, use options 1 or 2 with valid API credentials")
        
        # Show virtual portfolio
        trader.print_trading_portfolio_summary()
    
    else:
        print("❌ Invalid choice")

if __name__ == "__main__":
    try:
        main()
    except KeyboardInterrupt:
        print("\n\n👋 Program interrupted by user")
    except Exception as e:
        print(f"\n💥 Fatal error: {e}")
        print("Please check your configuration and try again")
