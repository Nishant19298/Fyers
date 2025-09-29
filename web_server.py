#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Nifty Options Trading Web Server - Simple Version
Provides REST API and WebSocket interface for the trading bot
Single client setup with file-based configuration
"""

from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect, Depends, Request, Response
from fastapi.staticfiles import StaticFiles
from fastapi.responses import HTMLResponse, FileResponse, RedirectResponse
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from pydantic import BaseModel
import json
import os
import io
import sys
import subprocess
import signal
import asyncio
import bcrypt
import threading
import glob
import time
import platform
import re
from datetime import datetime, timedelta
from typing import Dict, List, Optional, Any
import logging
import pandas as pd
from pathlib import Path
import pyotp
import qrcode
from io import BytesIO
import base64
from jose import JWTError, jwt
from passlib.context import CryptContext
import secrets

# Server startup time for uptime calculation
start_time = datetime.utcnow()

# Fyers API status caching to prevent burst rate limit violations
fyers_status_cache = {
    "data": None,
    "last_update": None,
    "cache_duration": 10  # seconds - minimum time between actual API calls
}

# Try to import the trading bot, handle missing Fyers API gracefully
FYERS_AVAILABLE = False
try:
    from fyers_vwap_9_1 import NiftyOptionsTrader, load_credentials
    FYERS_AVAILABLE = True
    print("✅ Fyers API available - Full trading functionality enabled")
except ImportError as e:
    print(f"⚠️ Fyers API not available: {e}")
    print("📊 Running in simulation mode - Web interface available for configuration and testing")
    
    # Create simulation classes when Fyers API is not available
    import pytz

# Authentication Configuration
SECRET_KEY = secrets.token_urlsafe(32)
ALGORITHM = "HS256"
ACCESS_TOKEN_EXPIRE_MINUTES = 60

# Password hashing
pwd_context = CryptContext(schemes=["bcrypt"], deprecated="auto")
security = HTTPBearer()

# TOTP Configuration
APP_NAME = "Nifty Options Trader"
TOTP_SECRET_FILE = "totp_secret.txt"
AUTH_CONFIG_FILE = "auth_config.json"
ADMIN_AUTH_CONFIG_FILE = "admin_auth_config.json"

class AuthConfig:
    def __init__(self, config_file=AUTH_CONFIG_FILE, profile_name="user"):
        self.config_file = config_file
        self.profile_name = profile_name
        self.totp_secret = None
        self.is_setup = False
        self.load_config()
    
    def load_config(self):
        """Load authentication configuration"""
        try:
            if os.path.exists(self.config_file):
                with open(self.config_file, 'r') as f:
                    config = json.load(f)
                    self.totp_secret = config.get('totp_secret')
                    self.is_setup = config.get('is_setup', False)
            
            # Fallback to old secret file format (only for main user config)
            elif self.config_file == AUTH_CONFIG_FILE and os.path.exists(TOTP_SECRET_FILE):
                with open(TOTP_SECRET_FILE, 'r') as f:
                    self.totp_secret = f.read().strip()
                    self.is_setup = True
                self.save_config()  # Migrate to new format
        except Exception as e:
            print(f"Error loading {self.profile_name} auth config: {e}")
    
    def save_config(self):
        """Save authentication configuration"""
        try:
            config = {
                'totp_secret': self.totp_secret,
                'is_setup': self.is_setup,
                'profile': self.profile_name
            }
            with open(self.config_file, 'w') as f:
                json.dump(config, f)
        except Exception as e:
            print(f"Error saving {self.profile_name} auth config: {e}")
    
    def setup_totp(self):
        """Generate new TOTP secret and mark as setup"""
        self.totp_secret = pyotp.random_base32()
        self.is_setup = True
        self.save_config()
        return self.totp_secret
    
    def verify_totp(self, token: str) -> bool:
        """Verify TOTP token"""
        if not self.totp_secret:
            return False
        totp = pyotp.TOTP(self.totp_secret)
        return totp.verify(token, valid_window=1)  # Allow 1 window tolerance
    
    def get_qr_code_url(self, user_email: str = None) -> str:
        """Generate QR code URL for TOTP setup"""
        if not self.totp_secret:
            return None
        if user_email is None:
            user_email = f"{self.profile_name}@trading.local"
        return pyotp.totp.TOTP(self.totp_secret).provisioning_uri(
            name=user_email,
            issuer_name=f"{APP_NAME} ({self.profile_name.title()})"
        )

# Global auth config instances
auth_config = AuthConfig(AUTH_CONFIG_FILE, "user")
admin_auth_config = AuthConfig(ADMIN_AUTH_CONFIG_FILE, "admin")

# Password Configuration
class PasswordConfig:
    def __init__(self, config_file: str):
        self.config_file = config_file
        self.username = None
        self.password_hash = None
        self.is_setup = False
        self.load_config()
    
    def load_config(self):
        """Load password configuration from file"""
        try:
            if os.path.exists(self.config_file):
                with open(self.config_file, 'r') as f:
                    config = json.load(f)
                    self.username = config.get('username')
                    self.password_hash = config.get('password_hash')
                    self.is_setup = bool(self.username and self.password_hash)
        except Exception as e:
            print(f"Error loading password config: {e}")
    
    def reload_config(self):
        """Force reload of configuration from file"""
        self.load_config()
        return self.is_setup
    
    def get_current_status(self):
        """Get current setup status (with fresh reload)"""
        self.load_config()
        return {
            'is_setup': self.is_setup,
            'username': self.username,
            'config_file': self.config_file
        }
    
    def save_config(self):
        """Save password configuration to file"""
        try:
            config = {
                'username': self.username,
                'password_hash': self.password_hash,
                'is_setup': self.is_setup
            }
            with open(self.config_file, 'w') as f:
                json.dump(config, f)
        except Exception as e:
            print(f"Error saving password config: {e}")
    
    def setup_password(self, username: str, password: str):
        """Setup username and password with bcrypt hashing"""
        salt = bcrypt.gensalt()
        password_hash = bcrypt.hashpw(password.encode('utf-8'), salt).decode('utf-8')
        
        self.username = username
        self.password_hash = password_hash
        self.is_setup = True
        self.save_config()
    
    def verify_password(self, username: str, password: str) -> bool:
        """Verify username and password (with dynamic config reload)"""
        # Reload config from file on each verification to get latest changes
        self.load_config()
        
        if not self.is_setup or username != self.username:
            return False
        
        try:
            return bcrypt.checkpw(password.encode('utf-8'), self.password_hash.encode('utf-8'))
        except Exception:
            return False

# Global password config instances
PASSWORD_CONFIG_FILE = "password_config.json"
ADMIN_PASSWORD_CONFIG_FILE = "admin_password_config.json"
password_config = PasswordConfig(PASSWORD_CONFIG_FILE)
admin_password_config = PasswordConfig(ADMIN_PASSWORD_CONFIG_FILE)

# Setup default credentials if first run
def setup_default_credentials():
    """Setup default credentials for first-time users"""
    if not password_config.is_setup:
        # Create default admin/admin123 credentials for first setup
        # User should change these after first login
        password_config.setup_password("admin", "admin123")
        print("🔧 Default credentials created: admin/admin123")
        print("⚠️  SECURITY WARNING: Change default password after first login!")

# Initialize default credentials on startup
setup_default_credentials()

# Authentication Models
class TOTPSetupRequest(BaseModel):
    email: Optional[str] = "admin@trading.local"

class TOTPVerifyRequest(BaseModel):
    token: str

class PasswordSetupRequest(BaseModel):
    username: str
    password: str

class PasswordChangeRequest(BaseModel):
    current_password: str
    new_username: str
    new_password: str

class LoginRequest(BaseModel):
    username: str
    password: str
    totp_token: str

# Authentication Functions
def create_access_token(data: dict):
    to_encode = data.copy()
    expire = datetime.utcnow() + timedelta(minutes=ACCESS_TOKEN_EXPIRE_MINUTES)
    to_encode.update({"exp": expire})
    encoded_jwt = jwt.encode(to_encode, SECRET_KEY, algorithm=ALGORITHM)
    return encoded_jwt

def verify_token(credentials: HTTPAuthorizationCredentials = Depends(security)):
    try:
        token = credentials.credentials
        payload = jwt.decode(token, SECRET_KEY, algorithms=[ALGORITHM])
        username: str = payload.get("sub")
        if username is None:
            raise HTTPException(status_code=401, detail="Invalid token")
        return username
    except JWTError:
        raise HTTPException(status_code=401, detail="Invalid token")

def verify_admin_token(credentials: HTTPAuthorizationCredentials = Depends(security)):
    try:
        token = credentials.credentials
        payload = jwt.decode(token, SECRET_KEY, algorithms=[ALGORITHM])
        username: str = payload.get("sub")
        profile: str = payload.get("profile")
        if username != "admin" or profile != "admin":
            raise HTTPException(status_code=403, detail="Admin access required")
        return username
    except JWTError:
        raise HTTPException(status_code=401, detail="Invalid admin token")

def verify_totp_token(token: str) -> bool:
    """Verify TOTP token"""
    return auth_config.verify_totp(token)

    class NiftyOptionsTrader:
        def __init__(self, *args, **kwargs):
            self.simulation_mode = True
            self.is_running = False
            self.positions = {'CE': None, 'PE': None}
            self.long_positions = {'CE': None, 'PE': None}
            self.trading_portfolio = {
                'total_pnl': 0, 
                'total_trades': 0, 
                'winning_trades': 0,
                'losing_trades': 0,
                'cash': 100000,
                'max_profit_seen': 0,
                'max_loss_seen': 0,
                'current_session_max_profit': 0,
                'current_session_max_loss': 0,
                'peak_drawdown': 0,
                'last_peak_time': None,
                'last_trough_time': None
            }
            # No fake data - start with None values for real data fetching
            self.current_nifty_price = None
            self.current_atm_strike = None
            self.current_vwap = None
            self.combined_premium_data = []  # Empty - no fake data
            
            # Add all required attributes
            self.decision_interval = "1minute"
            self.decision_interval_minutes = 1
            self.last_interval_fetch_time = None
            self.interval_candle_data = None
            self.individual_candle_data_ce = None
            self.individual_candle_data_pe = None
            self.should_fetch_historical = False
            
            # VWAP override functionality
            self.vwap_override_enabled = False
            self.vwap_override_value = None
            
            # Market timing (Always IST)
            self.ist_timezone = pytz.timezone('Asia/Kolkata')
            now_ist = datetime.now(self.ist_timezone)
            self.market_start = now_ist.replace(hour=9, minute=15, second=0, microsecond=0)
            self.market_end = now_ist.replace(hour=15, minute=30, second=0, microsecond=0)
            self.first_order_time = self.market_start + timedelta(minutes=40)
            
            # Trading state
            self.ce_entry_price = None
            self.pe_entry_price = None
            self.ce_current_price = None
            self.pe_current_price = None
            self.last_trade_time = None
            self.trade_count = 0
            
            print("⚠️ Simulation Mode: NiftyOptionsTrader initialized without live API")
            
        def calculate_unrealized_pnl(self): return 0.0
        def get_api_usage_status(self): return {'quote_calls': 0, 'historical_calls': 0, 'quote_percentage': 0, 'historical_percentage': 0}
        def is_market_hours(self): return True
        def round_to_nearest_50(self, price): return int(round(price / 50) * 50)
        def calculate_vwap(self): return None  # No fake VWAP
        def get_options_data(self, strike): return None  # No fake options data
        def start(self): 
            self.is_running = True
            print("📊 Simulation trader started")
        
        def square_off_position(self, *args): 
            print(f"📊 Simulation: Squaring off position with args: {args}")
            return {"status": "success", "message": "Simulation position squared off"}
        
        def square_off_all_positions(self): 
            print("📊 Simulation: Squaring off all positions")
            self.positions = {'CE': None, 'PE': None}
            self.long_positions = {'CE': None, 'PE': None}
            return {"status": "success", "message": "Simulation: All positions squared off"}
        
        def get_nifty_price(self): 
            # Don't simulate fake prices - return None when API not available
            return None

    def load_credentials():
        return {'CLIENT_ID': 'simulation', 'CLIENT_SECRET': 'simulation', 'REDIRECT_URI': 'simulation'}

def check_expiry_date_configured():
    """Check if expiry date/token is configured in expiry_override.txt"""
    try:
        if os.path.exists('expiry_override.txt'):
            with open('expiry_override.txt', 'r') as f:
                expiry_value = f.read().strip()
                if expiry_value:
                    # Valid if file contains any non-empty value (could be date or token)
                    return True, expiry_value
                else:
                    return False, "Expiry date file is empty"
        else:
            return False, "expiry_override.txt file not found"
    except Exception as e:
        return False, f"Error reading expiry date: {str(e)}"

# Configure logging for both application and uvicorn
import logging.config

# Generate date-specific log filename for web server
current_date = datetime.now().strftime("%Y%m%d")
web_server_log_filename = f"web_server_{current_date}.log"

LOGGING_CONFIG = {
    'version': 1,
    'disable_existing_loggers': False,  # Keep this False to preserve trader logging
    'formatters': {
        'detailed': {
            'format': '%(asctime)s - %(name)s - %(levelname)s - [%(funcName)s:%(lineno)d] - %(message)s',
        },
        'simple': {
            'format': '%(asctime)s - %(levelname)s - %(message)s',
        },
    },
    'handlers': {
        'file': {
            'class': 'logging.FileHandler',
            'filename': web_server_log_filename,
            'formatter': 'detailed',
            'level': 'DEBUG',
        },
        'console': {
            'class': 'logging.StreamHandler',
            'formatter': 'detailed',
            'level': 'INFO',
        },
    },
    'loggers': {
        # Web server specific loggers
        'web_server': {
            'handlers': ['file', 'console'],
            'level': 'DEBUG',
            'propagate': False,
        },
        '__main__': {
            'handlers': ['file', 'console'],
            'level': 'DEBUG',
            'propagate': False,
        },
        # Uvicorn loggers
        'uvicorn': {
            'handlers': ['file', 'console'],
            'level': 'INFO',
            'propagate': False,
        },
        'uvicorn.access': {
            'handlers': ['file', 'console'],
            'level': 'INFO',
            'propagate': False,
        },
        'uvicorn.error': {
            'handlers': ['file', 'console'],
            'level': 'INFO',
            'propagate': False,
        },
        # Preserve trader logging - don't override it
        'fyers_vwap_9_1': {
            'level': 'DEBUG',
            'propagate': True,  # Let trader use its own logging configuration
        },
    },
}

logging.config.dictConfig(LOGGING_CONFIG)
logger = logging.getLogger(__name__)

# Helper function for structured logging
def log_function_entry(func_name: str, **kwargs):
    """Log function entry with parameters"""
    params = ', '.join([f"{k}={v}" for k, v in kwargs.items() if v is not None])
    logger.debug(f" ENTRY: {func_name}({params})")

def log_function_exit(func_name: str, status: str = "success", result=None, error=None):
    """Log function exit with result"""
    if error:
        logger.error(f" EXIT: {func_name} - FAILED: {error}")
    elif result:
        logger.debug(f" EXIT: {func_name} - SUCCESS: {result}")
    else:
        logger.debug(f" EXIT: {func_name} - {status.upper()}")

def log_trader_state(trader, context=""):
    """Log current trader state for debugging"""
    if not trader:
        logger.debug(f" TRADER_STATE({context}): None - trader not initialized")
        return
    
    logger.debug(f" TRADER_STATE({context}): "
                f"simulation_mode={getattr(trader, 'simulation_mode', 'unknown')}, "
                f"is_running={getattr(trader, 'is_running', 'unknown')}, "
                f"nifty_price={getattr(trader, 'current_nifty_price', 'unknown')}, "
                f"atm_strike={getattr(trader, 'current_atm_strike', 'unknown')}, "
                f"vwap={getattr(trader, 'current_vwap', 'unknown')}")
    
    positions = getattr(trader, 'positions', {})
    ce_pos = positions.get('CE')
    pe_pos = positions.get('PE')
    ce_active = (ce_pos is not None and ce_pos != {} and 
                (isinstance(ce_pos, dict) and ce_pos.get('quantity', 0) != 0))
    pe_active = (pe_pos is not None and pe_pos != {} and 
                (isinstance(pe_pos, dict) and pe_pos.get('quantity', 0) != 0))
    
    logger.debug(f" POSITIONS({context}): CE={ce_active} (data: {ce_pos}), PE={pe_active} (data: {pe_pos})")
    
    portfolio = getattr(trader, 'trading_portfolio', {})
    if portfolio:
        logger.debug(f" PORTFOLIO({context}): "
                    f"total_pnl={portfolio.get('total_pnl', 0)}, "
                    f"total_trades={portfolio.get('total_trades', 0)}, "
                    f"cash={portfolio.get('cash', 0)}")

# FastAPI app
app = FastAPI(title="Nifty Options Trading API", version="1.0.0")

# Serve static files
app.mount("/static", StaticFiles(directory="static"), name="static")

# TOTP Authentication Endpoints
@app.get("/auth/setup", response_class=HTMLResponse)
async def totp_setup_page():
    """TOTP Setup page"""
    if auth_config.is_setup:
        return RedirectResponse(url="/auth/login")
    
    return """
    <!DOCTYPE html>
    <html>
    <head>
        <title>Setup 2FA - Nifty Options Trader</title>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <style>
            body { font-family: 'Segoe UI', Arial, sans-serif; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); margin: 0; padding: 20px; min-height: 100vh; display: flex; align-items: center; justify-content: center; }
            .container { background: white; padding: 40px; border-radius: 15px; box-shadow: 0 10px 30px rgba(0,0,0,0.2); max-width: 500px; text-align: center; }
            h1 { color: #2d3748; margin-bottom: 30px; }
            .qr-container { margin: 30px 0; padding: 20px; background: #f7fafc; border-radius: 10px; }
            .secret-key { background: #edf2f7; padding: 15px; border-radius: 8px; font-family: monospace; word-break: break-all; margin: 20px 0; }
            input { width: 100%; padding: 15px; border: 2px solid #e2e8f0; border-radius: 8px; font-size: 16px; margin: 10px 0; }
            button { background: #4299e1; color: white; padding: 15px 30px; border: none; border-radius: 8px; font-size: 16px; cursor: pointer; width: 100%; }
            button:hover { background: #3182ce; }
            .step { margin: 20px 0; text-align: left; padding: 15px; background: #f0f4f8; border-radius: 8px; }
        </style>
    </head>
    <body>
        <div class="container">
            <h1>🔐 Setup Two-Factor Authentication</h1>
            <div class="step">
                <strong>Step 1:</strong> Install Google Authenticator or any TOTP app on your phone
            </div>
            <div class="step">
                <strong>Step 2:</strong> Click "Generate QR Code" below
            </div>
            <div class="step">
                <strong>Step 3:</strong> Scan the QR code with your authenticator app
            </div>
            <div class="step">
                <strong>Step 4:</strong> Enter the 6-digit code from your app to verify
            </div>
            
            <div id="qr-section" style="display: none;">
                <div class="qr-container">
                    <div id="qr-code"></div>
                    <div class="secret-key">
                        <strong>Manual Entry Key:</strong><br>
                        <span id="secret-key"></span>
                    </div>
                </div>
            </div>
            
            <button onclick="generateQR()" id="generate-btn">🔄 Generate QR Code</button>
            
            <div id="verify-section" style="display: none;">
                <input type="text" id="totp-code" placeholder="Enter 6-digit code from authenticator" maxlength="6">
                <button onclick="verifySetup()">✅ Verify & Complete Setup</button>
            </div>
        </div>

        <script>
            async function generateQR() {
                try {
                    const response = await fetch('/auth/setup-qr', { method: 'POST' });
                    const data = await response.json();
                    
                    document.getElementById('qr-code').innerHTML = `<img src="${data.qr_code}" alt="QR Code" style="max-width: 100%;">`;
                    document.getElementById('secret-key').textContent = data.secret;
                    document.getElementById('qr-section').style.display = 'block';
                    document.getElementById('verify-section').style.display = 'block';
                    document.getElementById('generate-btn').style.display = 'none';
                } catch (error) {
                    alert('Failed to generate QR code: ' + error.message);
                }
            }

            async function verifySetup() {
                const code = document.getElementById('totp-code').value;
                if (code.length !== 6) {
                    alert('Please enter a 6-digit code');
                    return;
                }

                try {
                    const response = await fetch('/auth/setup-verify', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ token: code })
                    });

                    if (response.ok) {
                        alert('✅ Setup complete! Redirecting to login...');
                        window.location.href = '/auth/login';
                    } else {
                        const error = await response.json();
                        alert('❌ ' + error.detail);
                    }
                } catch (error) {
                    alert('Failed to verify: ' + error.message);
                }
            }
        </script>
    </body>
    </html>
    """

@app.post("/auth/setup-qr")
async def generate_totp_qr(request: TOTPSetupRequest = TOTPSetupRequest()):
    """Generate TOTP QR code for setup"""
    if auth_config.is_setup:
        raise HTTPException(status_code=400, detail="TOTP already setup")
    
    secret = auth_config.setup_totp()
    provisioning_uri = auth_config.get_qr_code_url(request.email)
    
    # Generate QR code
    qr = qrcode.QRCode(version=1, box_size=10, border=5)
    qr.add_data(provisioning_uri)
    qr.make(fit=True)
    
    img = qr.make_image(fill_color="black", back_color="white")
    buffer = BytesIO()
    img.save(buffer, format='PNG')
    buffer.seek(0)
    
    # Convert to base64 for embedding in HTML
    img_base64 = base64.b64encode(buffer.getvalue()).decode()
    qr_code_data_url = f"data:image/png;base64,{img_base64}"
    
    return {
        "qr_code": qr_code_data_url,
        "secret": secret,
        "provisioning_uri": provisioning_uri
    }

@app.post("/auth/setup-verify")
async def verify_totp_setup(request: TOTPVerifyRequest):
    """Verify TOTP setup"""
    if not auth_config.totp_secret:
        raise HTTPException(status_code=400, detail="No TOTP secret found")
    
    if not auth_config.verify_totp(request.token):
        raise HTTPException(status_code=400, detail="Invalid TOTP token")
    
    return {"message": "TOTP setup completed successfully"}

@app.get("/auth/login", response_class=HTMLResponse)
async def login_page():
    """Login page with username, password and TOTP (with dynamic config reload)"""
    # Reload configs to get latest changes
    auth_config.load_config()
    password_config.reload_config()
    
    if not auth_config.is_setup:
        return RedirectResponse(url="/auth/setup")
    
    # Check if password setup is needed
    if not password_config.is_setup:
        return RedirectResponse(url="/auth/password-setup")
    
    return """
    <!DOCTYPE html>
    <html>
    <head>
        <title>Login - Nifty Options Trader</title>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <style>
            body { font-family: 'Segoe UI', Arial, sans-serif; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); margin: 0; padding: 20px; min-height: 100vh; display: flex; align-items: center; justify-content: center; }
            .container { background: white; padding: 40px; border-radius: 15px; box-shadow: 0 10px 30px rgba(0,0,0,0.2); max-width: 400px; text-align: center; }
            h1 { color: #2d3748; margin-bottom: 30px; }
            .form-group { margin: 15px 0; text-align: left; }
            label { display: block; margin-bottom: 5px; font-weight: bold; color: #4a5568; }
            input { width: 100%; padding: 15px; border: 2px solid #e2e8f0; border-radius: 8px; font-size: 16px; box-sizing: border-box; }
            input[type="text"]:last-of-type { text-align: center; letter-spacing: 3px; font-size: 18px; }
            input[type="password"] { letter-spacing: 2px; }
            button { background: #4299e1; color: white; padding: 15px 30px; border: none; border-radius: 8px; font-size: 16px; cursor: pointer; width: 100%; margin-top: 20px; }
            button:hover { background: #3182ce; }
            button:disabled { background: #a0aec0; cursor: not-allowed; }
            .info { color: #718096; margin: 20px 0; font-size: 14px; }
            .error { color: #e53e3e; margin: 10px 0; font-size: 14px; }
        </style>
    </head>
    <body>
        <div class="container">
            <h1>🔐 Nifty Options Trader</h1>
            <h2>Secure Login</h2>
            
            <div id="error-message" class="error" style="display: none;"></div>
            
            <div class="form-group">
                <label for="username">Username</label>
                <input type="text" id="username" placeholder="Enter username" autocomplete="username">
            </div>
            
            <div class="form-group">
                <label for="password">Password</label>
                <input type="password" id="password" placeholder="Enter password" autocomplete="current-password">
            </div>
            
            <div class="form-group">
                <label for="totp-code">Two-Factor Authentication Code</label>
                <input type="text" id="totp-code" placeholder="000000" maxlength="6" autocomplete="off">
            </div>
            
            <button onclick="login()" id="login-btn">🚀 Login</button>
            
            <div class="info" style="margin-top: 30px;">
                Enter your credentials and the 6-digit code from your authenticator app
            </div>
        </div>

        <script>
            // Auto-focus on username
            document.getElementById('username').focus();
            
            // Auto-submit when all fields are filled and 6 digits entered for TOTP
            document.getElementById('totp-code').addEventListener('input', function(e) {
                if (e.target.value.length === 6) {
                    const username = document.getElementById('username').value;
                    const password = document.getElementById('password').value;
                    if (username && password) {
                        login();
                    }
                }
            });

            function showError(message) {
                const errorEl = document.getElementById('error-message');
                errorEl.textContent = '❌ ' + message;
                errorEl.style.display = 'block';
                setTimeout(() => {
                    errorEl.style.display = 'none';
                }, 5000);
            }

            async function login() {
                const username = document.getElementById('username').value.trim();
                const password = document.getElementById('password').value;
                const code = document.getElementById('totp-code').value;
                
                if (!username) {
                    showError('Please enter username');
                    document.getElementById('username').focus();
                    return;
                }
                
                if (!password) {
                    showError('Please enter password');
                    document.getElementById('password').focus();
                    return;
                }
                
                if (code.length !== 6) {
                    showError('Please enter a 6-digit authentication code');
                    document.getElementById('totp-code').focus();
                    return;
                }

                const loginBtn = document.getElementById('login-btn');
                loginBtn.disabled = true;
                loginBtn.textContent = '🔄 Logging in...';

                try {
                    const response = await fetch('/auth/login', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ 
                            username: username,
                            password: password,
                            totp_token: code 
                        })
                    });

                    if (response.ok) {
                        const data = await response.json();
                        localStorage.setItem('auth_token', data.access_token);
                        window.location.href = '/';
                    } else {
                        const error = await response.json();
                        showError(error.detail);
                        document.getElementById('password').value = '';
                        document.getElementById('totp-code').value = '';
                        document.getElementById('username').focus();
                    }
                } catch (error) {
                    showError('Login failed: ' + error.message);
                } finally {
                    loginBtn.disabled = false;
                    loginBtn.textContent = '🚀 Login';
                }
            }

            // Enter key handling
            document.addEventListener('keypress', function(e) {
                if (e.key === 'Enter') {
                    login();
                }
            });
        </script>
    </body>
    </html>
    """

@app.get("/auth/password-setup", response_class=HTMLResponse)
async def password_setup_page():
    """Password setup page"""
    if not auth_config.is_setup:
        return RedirectResponse(url="/auth/setup")
    
    if password_config.is_setup:
        return RedirectResponse(url="/auth/login")
    
    return """
    <!DOCTYPE html>
    <html>
    <head>
        <title>Password Setup - Nifty Options Trader</title>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <style>
            body { font-family: 'Segoe UI', Arial, sans-serif; background: linear-gradient(135deg, #667eea 0%, #764ba2 100%); margin: 0; padding: 20px; min-height: 100vh; display: flex; align-items: center; justify-content: center; }
            .container { background: white; padding: 40px; border-radius: 15px; box-shadow: 0 10px 30px rgba(0,0,0,0.2); max-width: 450px; text-align: center; }
            h1 { color: #2d3748; margin-bottom: 30px; }
            .form-group { margin: 15px 0; text-align: left; }
            label { display: block; margin-bottom: 5px; font-weight: bold; color: #4a5568; }
            input { width: 100%; padding: 15px; border: 2px solid #e2e8f0; border-radius: 8px; font-size: 16px; box-sizing: border-box; }
            input[type="password"] { letter-spacing: 2px; }
            button { background: #48bb78; color: white; padding: 15px 30px; border: none; border-radius: 8px; font-size: 16px; cursor: pointer; width: 100%; margin-top: 20px; }
            button:hover { background: #38a169; }
            button:disabled { background: #a0aec0; cursor: not-allowed; }
            .info { color: #718096; margin: 20px 0; font-size: 14px; }
            .error { color: #e53e3e; margin: 10px 0; font-size: 14px; }
            .success { color: #38a169; margin: 10px 0; font-size: 14px; }
            .requirements { text-align: left; font-size: 12px; color: #718096; margin: 10px 0; }
        </style>
    </head>
    <body>
        <div class="container">
            <h1>🔐 Password Setup</h1>
            <h2>Create Login Credentials</h2>
            
            <div class="info">
                Set up your username and password for secure access to the trading dashboard.
            </div>
            
            <div id="message" style="display: none;"></div>
            
            <div class="form-group">
                <label for="username">Username</label>
                <input type="text" id="username" placeholder="Choose a username" autocomplete="username">
            </div>
            
            <div class="form-group">
                <label for="password">Password</label>
                <input type="password" id="password" placeholder="Choose a strong password" autocomplete="new-password">
                <div class="requirements">
                    • Minimum 8 characters<br>
                    • Include letters and numbers<br>
                    • Use special characters for extra security
                </div>
            </div>
            
            <div class="form-group">
                <label for="confirm-password">Confirm Password</label>
                <input type="password" id="confirm-password" placeholder="Confirm your password" autocomplete="new-password">
            </div>
            
            <button onclick="setupPassword()" id="setup-btn">✅ Setup Password</button>
            
            <div class="info" style="margin-top: 30px;">
                After setting up your password, you'll use it along with two-factor authentication to log in.
            </div>
        </div>

        <script>
            // Auto-focus on username
            document.getElementById('username').focus();

            function showMessage(message, type = 'error') {
                const messageEl = document.getElementById('message');
                messageEl.textContent = message;
                messageEl.className = type;
                messageEl.style.display = 'block';
                setTimeout(() => {
                    messageEl.style.display = 'none';
                }, 5000);
            }

            async function setupPassword() {
                const username = document.getElementById('username').value.trim();
                const password = document.getElementById('password').value;
                const confirmPassword = document.getElementById('confirm-password').value;
                
                if (!username) {
                    showMessage('❌ Please enter a username');
                    document.getElementById('username').focus();
                    return;
                }
                
                if (username.length < 3) {
                    showMessage('❌ Username must be at least 3 characters long');
                    document.getElementById('username').focus();
                    return;
                }
                
                if (!password) {
                    showMessage('❌ Please enter a password');
                    document.getElementById('password').focus();
                    return;
                }
                
                if (password.length < 8) {
                    showMessage('❌ Password must be at least 8 characters long');
                    document.getElementById('password').focus();
                    return;
                }
                
                if (password !== confirmPassword) {
                    showMessage('❌ Passwords do not match');
                    document.getElementById('confirm-password').focus();
                    return;
                }

                const setupBtn = document.getElementById('setup-btn');
                setupBtn.disabled = true;
                setupBtn.textContent = '🔄 Setting up...';

                try {
                    const response = await fetch('/auth/password-setup', {
                        method: 'POST',
                        headers: { 'Content-Type': 'application/json' },
                        body: JSON.stringify({ 
                            username: username,
                            password: password
                        })
                    });

                    if (response.ok) {
                        showMessage('✅ Password setup completed successfully! Redirecting to login...', 'success');
                        setTimeout(() => {
                            window.location.href = '/auth/login';
                        }, 2000);
                    } else {
                        const error = await response.json();
                        showMessage('❌ ' + error.detail);
                    }
                } catch (error) {
                    showMessage('❌ Setup failed: ' + error.message);
                } finally {
                    setupBtn.disabled = false;
                    setupBtn.textContent = '✅ Setup Password';
                }
            }

            // Enter key handling
            document.addEventListener('keypress', function(e) {
                if (e.key === 'Enter') {
                    setupPassword();
                }
            });
        </script>
    </body>
    </html>
    """

@app.post("/auth/password-setup")
async def setup_password(request: PasswordSetupRequest):
    """Setup username and password"""
    if not auth_config.is_setup:
        raise HTTPException(status_code=400, detail="TOTP not setup")
    
    if password_config.is_setup:
        raise HTTPException(status_code=400, detail="Password already setup")
    
    # Validate input
    if len(request.username.strip()) < 3:
        raise HTTPException(status_code=400, detail="Username must be at least 3 characters long")
    
    if len(request.password) < 8:
        raise HTTPException(status_code=400, detail="Password must be at least 8 characters long")
    
    # Setup password
    password_config.setup_password(request.username.strip(), request.password)
    
    return {"message": "Password setup completed successfully"}

@app.post("/auth/login")
async def login(request: LoginRequest):
    """Login with username, password and TOTP (with dynamic config reload)"""
    # Reload TOTP config to get latest changes
    auth_config.load_config()
    if not auth_config.is_setup:
        raise HTTPException(status_code=400, detail="TOTP not setup")
    
    # Reload password config to get latest changes (happens automatically in verify_password)
    if not password_config.reload_config():
        raise HTTPException(status_code=400, detail="Password not setup")
    
    # Verify password first (already includes config reload)
    if not password_config.verify_password(request.username, request.password):
        raise HTTPException(status_code=400, detail="Invalid username or password")
    
    # Then verify TOTP
    if not auth_config.verify_totp(request.totp_token):
        raise HTTPException(status_code=400, detail="Invalid TOTP token")
    
    access_token = create_access_token(data={"sub": "admin"})
    return {"access_token": access_token, "token_type": "bearer"}

@app.get("/auth/logout")
async def logout():
    """Logout (client-side token removal)"""
    return RedirectResponse(url="/auth/login")

@app.post("/auth/reload-config")
async def reload_auth_config():
    """Force reload authentication configuration without restart"""
    try:
        # Force reload both TOTP and password configs
        auth_config.load_config()
        password_config.reload_config()
        
        # Get fresh status
        password_status = password_config.get_current_status()
        
        return {
            "message": "Configuration reloaded successfully",
            "totp_setup": auth_config.is_setup,
            "password_setup": password_status['is_setup'],
            "current_username": password_status['username'],
            "timestamp": datetime.utcnow().isoformat(),
            "config_files_checked": [
                AUTH_CONFIG_FILE,
                PASSWORD_CONFIG_FILE
            ]
        }
    except Exception as e:
        raise HTTPException(status_code=500, detail=f"Failed to reload config: {str(e)}")

# =================
# ADMIN PAGE ROUTES
# =================

@app.get("/admin/auth/setup", response_class=HTMLResponse)
async def admin_setup_page():
    """Admin TOTP setup page"""
    return FileResponse("static/admin-setup.html")

@app.get("/admin/auth/login", response_class=HTMLResponse)
async def admin_login_page():
    """Admin login page"""
    if not admin_auth_config.is_setup:
        return RedirectResponse(url="/admin/auth/setup")
    return FileResponse("static/admin-login.html")

@app.get("/admin/dashboard", response_class=HTMLResponse)
async def admin_dashboard():
    """Admin dashboard - requires authentication"""
    if not admin_auth_config.is_setup:
        return RedirectResponse(url="/admin/auth/setup")
    return FileResponse("static/admin-dashboard.html")

@app.get("/admin")
async def admin_redirect():
    """Redirect /admin to appropriate page"""
    if not admin_auth_config.is_setup:
        return RedirectResponse(url="/admin/auth/setup")
    return RedirectResponse(url="/admin/dashboard")

@app.get("/auth/status")
async def auth_status():
    """Check authentication status (with dynamic config reload)"""
    # Reload both configs to get latest status
    auth_config.load_config()
    password_status = password_config.get_current_status()
    
    return {
        "totp_setup": auth_config.is_setup,
        "password_setup": password_status['is_setup'],
        "current_username": password_status['username'],
        "setup_url": "/auth/setup" if not auth_config.is_setup else None,
        "password_setup_url": "/auth/password-setup" if not password_status['is_setup'] else None,
        "login_url": "/auth/login",
        "config_reloaded": True
    }

# =================
# ADMIN AUTHENTICATION ENDPOINTS
# =================

@app.get("/admin/auth/status")
async def admin_auth_status():
    """Check admin authentication status"""
    return {
        "is_setup": admin_auth_config.is_setup,
        "setup_url": "/admin/auth/setup" if not admin_auth_config.is_setup else None,
        "login_url": "/admin/auth/login",
        "profile": "admin"
    }

@app.post("/admin/auth/setup-qr")
async def admin_setup_qr(request: TOTPSetupRequest):
    """Generate QR code for admin TOTP setup"""
    try:
        # Generate new TOTP secret
        secret = admin_auth_config.setup_totp()
        
        # Create QR code
        qr_url = admin_auth_config.get_qr_code_url(request.email or "admin@trading.local")
        
        # Generate QR code image
        qr = qrcode.QRCode(version=1, box_size=10, border=5)
        qr.add_data(qr_url)
        qr.make(fit=True)
        
        img = qr.make_image(fill_color="black", back_color="white")
        
        # Convert to base64
        buffer = io.BytesIO()
        img.save(buffer, format="PNG")
        buffer.seek(0)
        qr_base64 = base64.b64encode(buffer.getvalue()).decode()
        
        return {
            "qr_code": f"data:image/png;base64,{qr_base64}",
            "secret": secret,
            "qr_url": qr_url,
            "message": "Scan this QR code with Google Authenticator (Admin Profile)"
        }
        
    except Exception as e:
        logger.error(f"Admin TOTP setup error: {e}")
        raise HTTPException(status_code=500, detail=f"Setup failed: {str(e)}")

@app.post("/admin/auth/setup-verify")
async def admin_setup_verify(request: TOTPVerifyRequest):
    """Verify admin TOTP token during setup"""
    try:
        if not admin_auth_config.totp_secret:
            raise HTTPException(status_code=400, detail="No admin TOTP secret found. Please generate QR code first.")
        
        # Verify the token
        if not admin_auth_config.verify_totp(request.token):
            raise HTTPException(status_code=400, detail="Invalid TOTP code. Please try again.")
        
        # Create JWT token for admin
        token_data = {
            "sub": "admin", 
            "exp": datetime.utcnow() + timedelta(minutes=60),
            "profile": "admin"
        }
        token = jwt.encode(token_data, SECRET_KEY, algorithm=ALGORITHM)
        
        return {
            "message": "Admin TOTP setup completed successfully!",
            "access_token": token,
            "token_type": "bearer",
            "redirect_url": "/admin/dashboard"
        }
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Admin TOTP verification error: {e}")
        raise HTTPException(status_code=500, detail=f"Verification failed: {str(e)}")

@app.post("/admin/auth/login")
async def admin_login(request: TOTPVerifyRequest):
    """Admin login with TOTP verification"""
    try:
        if not admin_auth_config.is_setup:
            raise HTTPException(status_code=400, detail="Admin TOTP not configured. Please complete setup first.")
        
        # Verify TOTP token
        if not admin_auth_config.verify_totp(request.token):
            raise HTTPException(status_code=401, detail="Invalid TOTP code")
        
        # Create JWT token
        token_data = {
            "sub": "admin",
            "exp": datetime.utcnow() + timedelta(minutes=60),
            "profile": "admin"
        }
        token = jwt.encode(token_data, SECRET_KEY, algorithm=ALGORITHM)
        
        return {
            "access_token": token,
            "token_type": "bearer",
            "message": "Admin login successful",
            "redirect_url": "/admin/dashboard"
        }
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Admin login error: {e}")
        raise HTTPException(status_code=500, detail=f"Login failed: {str(e)}")

@app.post("/admin/auth/logout")
async def admin_logout():
    """Admin logout (client-side token removal)"""
    return {
        "message": "Admin logged out successfully",
        "redirect_url": "/admin/auth/login"
    }

# =================
# ADMIN SERVER MANAGEMENT ENDPOINTS
# =================

@app.get("/admin/server/status")
async def admin_server_status(admin: str = Depends(verify_admin_token)):
    """Get server status and system information"""
    try:
        try:
            import psutil
            # Get current process info
            process = psutil.Process()
            memory_mb = process.memory_info().rss / 1024 / 1024
            cpu_percent = process.cpu_percent()
        except ImportError:
            memory_mb = "unavailable (psutil not installed)"
            cpu_percent = "unavailable (psutil not installed)"
        
        # Get active connections count safely
        active_connections = 0
        try:
            # Check if connection manager exists in the global scope
            import sys
            current_module = sys.modules[__name__]
            if hasattr(current_module, 'connection_manager'):
                conn_mgr = getattr(current_module, 'connection_manager')
                if hasattr(conn_mgr, 'active_connections'):
                    active_connections = len(conn_mgr.active_connections)
        except Exception:
            active_connections = 0
        
        status = {
            "server_status": "running",
            "uptime_seconds": (datetime.utcnow() - start_time).total_seconds(),
            "memory_usage_mb": memory_mb,
            "cpu_percent": cpu_percent,
            "pid": os.getpid(),
            "auth_profiles": {
                "user_setup": auth_config.is_setup,
                "admin_setup": admin_auth_config.is_setup
            },
            "active_connections": active_connections
        }
        
        return status
        
    except Exception as e:
        logger.error(f"Error getting server status: {e}")
        raise HTTPException(status_code=500, detail=f"Failed to get server status: {str(e)}")

@app.post("/admin/server/restart")
async def admin_server_restart(admin: str = Depends(verify_admin_token)):
    """Restart the server (graceful shutdown and restart)"""
    try:
        logger.info(f"🔄 Server restart requested by admin: {admin}")
        
        # Schedule restart after response
        import threading
        
        def restart_server():
            import time
            time.sleep(1)  # Allow response to be sent
            logger.info("🔄 Restarting server...")
            
            # Cross-platform restart implementation
            try:
                if sys.platform == "win32":
                    # Windows: Start new process in new console
                    script_path = sys.argv[0]
                    python_exe = sys.executable
                    
                    subprocess.Popen([python_exe, script_path], 
                                   cwd=os.getcwd(),
                                   creationflags=subprocess.CREATE_NEW_CONSOLE)
                else:
                    # Linux/Unix: Check if running under systemd
                    if os.environ.get('SYSTEMD_EXEC_PID') or os.path.exists('/run/systemd/system'):
                        # Running under systemd - let systemd handle restart
                        logger.info("🔄 Detected systemd - exiting for systemd to restart")
                        # Just exit - systemd will restart us automatically
                        os._exit(0)
                    else:
                        # Direct execution - use exec to replace process
                        logger.info("🔄 Direct restart using execv")
                        os.execv(sys.executable, [sys.executable] + sys.argv)
                
            except Exception as restart_error:
                logger.error(f"❌ Restart failed: {restart_error}")
                # Fallback: just exit and hope something restarts us
                os._exit(1)
            
            # Exit current process (should not reach here on Linux with execv)
            os._exit(0)
        
        restart_thread = threading.Thread(target=restart_server)
        restart_thread.daemon = True
        restart_thread.start()
        
        return {
            "message": "Server restart initiated",
            "status": "restarting",
            "wait_time_seconds": 5
        }
        
    except Exception as e:
        logger.error(f"Error restarting server: {e}")
        raise HTTPException(status_code=500, detail=f"Failed to restart server: {str(e)}")

@app.post("/admin/server/shutdown")
async def admin_server_shutdown(admin: str = Depends(verify_admin_token)):
    """Shutdown the server gracefully"""
    try:
        logger.info(f"🛑 Server shutdown requested by admin: {admin}")
        
        # Schedule shutdown after response
        import threading
        
        def shutdown_server():
            import time
            time.sleep(1)  # Allow response to be sent
            logger.info(" Shutting down server...")
            os._exit(0)
        
        shutdown_thread = threading.Thread(target=shutdown_server)
        shutdown_thread.daemon = True
        shutdown_thread.start()
        
        return {
            "message": "Server shutdown initiated",
            "status": "shutting_down"
        }
        
    except Exception as e:
        logger.error(f"Error shutting down server: {e}")
        raise HTTPException(status_code=500, detail=f"Failed to shutdown server: {str(e)}")

@app.post("/admin/auth/reset-user")
async def admin_reset_user_auth(admin: str = Depends(verify_admin_token)):
    """Reset user authentication (admin only)"""
    try:
        # Remove user auth config file
        if os.path.exists(AUTH_CONFIG_FILE):
            os.remove(AUTH_CONFIG_FILE)
            logger.info(f"User auth config removed by admin: {admin}")
        
        # Reset in-memory config
        auth_config.totp_secret = None
        auth_config.is_setup = False
        
        return {
            "message": "User authentication reset successfully",
            "user_setup_required": True,
            "setup_url": "/auth/setup"
        }
        
    except Exception as e:
        logger.error(f"Error resetting user auth: {e}")
        raise HTTPException(status_code=500, detail=f"Failed to reset user auth: {str(e)}")

@app.post("/admin/auth/reset-admin")
async def admin_reset_admin_auth(admin: str = Depends(verify_admin_token)):
    """Reset admin authentication (requires restart)"""
    try:
        # Remove admin auth config file
        if os.path.exists(ADMIN_AUTH_CONFIG_FILE):
            os.remove(ADMIN_AUTH_CONFIG_FILE)
            logger.info(f"Admin auth config removed by admin: {admin}")
        
        return {
            "message": "Admin authentication reset - server restart required to take effect",
            "restart_required": True,
            "restart_url": "/admin/server/restart"
        }
        
    except Exception as e:
        logger.error(f"Error resetting admin auth: {e}")
        raise HTTPException(status_code=500, detail=f"Failed to reset admin auth: {str(e)}")

# Main dashboard route with authentication check
@app.get("/", response_class=HTMLResponse)
async def dashboard():
    """Main dashboard - redirect to setup/login if not authenticated"""
    if not auth_config.is_setup:
        return RedirectResponse(url="/auth/setup")
    
    # For now, we'll serve the static file, but add client-side auth check
    try:
        with open("static/index.html", "r", encoding="utf-8") as f:
            content = f.read()
        
        # Inject authentication check script
        auth_script = """
        <script>
        // Authentication check
        function checkAuth() {
            const token = localStorage.getItem('auth_token');
            if (!token) {
                window.location.href = '/auth/login';
                return false;
            }
            return true;
        }
        
        // Add auth headers to fetch requests
        const originalFetch = window.fetch;
        window.fetch = function(...args) {
            const token = localStorage.getItem('auth_token');
            if (token && args[1]) {
                args[1].headers = {
                    ...args[1].headers,
                    'Authorization': 'Bearer ' + token
                };
            } else if (token && !args[1]) {
                args[1] = {
                    headers: {
                        'Authorization': 'Bearer ' + token
                    }
                };
            }
            return originalFetch.apply(this, args);
        };
        
        // Check auth on page load
        if (!checkAuth()) {
            // Will redirect if not authenticated
        }
        </script>
        """
        
        # Insert before closing head tag
        content = content.replace("</head>", f"{auth_script}</head>")
        return HTMLResponse(content)
    except FileNotFoundError:
        return HTMLResponse("Dashboard not found")

# Program Flow Visualization Page
@app.get("/program-flow", response_class=HTMLResponse)
async def program_flow():
    """Program Flow Visualization Page"""
    try:
        with open("static/program-flow.html", "r", encoding="utf-8") as f:
            content = f.read()
        
        # Inject authentication check script
        auth_script = """
        <script>
        // Authentication check
        function checkAuth() {
            const token = localStorage.getItem('auth_token');
            if (!token) {
                window.location.href = '/auth/login';
                return false;
            }
            return true;
        }
        
        // Add auth headers to fetch requests
        const originalFetch = window.fetch;
        window.fetch = function(...args) {
            const token = localStorage.getItem('auth_token');
            if (token && args[1]) {
                args[1].headers = {
                    ...args[1].headers,
                    'Authorization': 'Bearer ' + token
                };
            } else if (token && !args[1]) {
                args[1] = {
                    headers: {
                        'Authorization': 'Bearer ' + token
                    }
                };
            }
            return originalFetch.apply(this, args);
        };
        
        // Check auth on page load
        if (!checkAuth()) {
            // Will redirect if not authenticated
        }
        </script>
        """
        
        # Insert before closing head tag
        content = content.replace("</head>", f"{auth_script}</head>")
        return HTMLResponse(content)
    except FileNotFoundError:
        return HTMLResponse("Program Flow page not found")

@app.get("/order-tracking", response_class=HTMLResponse)
async def order_tracking():
    """Order Tracking Page"""
    try:
        with open("static/order-tracking.html", "r", encoding="utf-8") as f:
            content = f.read()
        
        # Inject authentication check script (same as program-flow page)
        auth_script = """
        <script>
        // Authentication check
        function checkAuthOnLoad() {
            const token = localStorage.getItem('auth_token');
            if (!token) {
                window.location.href = '/auth/login';
                return false;
            }
            return true;
        }
        
        // Call auth check on page load
        document.addEventListener('DOMContentLoaded', function() {
            if (!checkAuthOnLoad()) {
                return;
            }
        });
        </script>
        """
        
        # Insert before closing head tag
        content = content.replace("</head>", f"{auth_script}</head>")
        return HTMLResponse(content)
    except FileNotFoundError:
        return HTMLResponse("Order Tracking page not found")

# Logout endpoint that serves static page
@app.get("/logout")
async def logout_page():
    """Logout page that clears token"""
    return HTMLResponse("""
    <!DOCTYPE html>
    <html>
    <head><title>Logged Out</title></head>
    <body>
        <script>
        localStorage.removeItem('auth_token');
        alert('Logged out successfully');
        window.location.href = '/auth/login';
        </script>
    </body>
    </html>
    """)

# Pydantic models for request/response
class APICredentials(BaseModel):
    client_id: str
    client_secret: str
    redirect_uri: str

class AccessTokenModel(BaseModel):
    access_token: str

class VWAPOverrideModel(BaseModel):
    vwap: Optional[float] = None

class ExpiryOverrideModel(BaseModel):
    date: str

class PositionSquareOff(BaseModel):
    option_type: str  # "CE" or "PE"

# State Management
class AppStateManager:
    def __init__(self):
        self.trader = None
        self.trading_thread = None
        self.is_trading_active = False
        self.websocket_clients = set()
        self.current_date = datetime.now().strftime('%Y%m%d')
        self.app_state_file = f'app_state_{self.current_date}.json'
        logger.info(f" AppStateManager initialized with state file: {self.app_state_file}")

    def load_state(self):
        """Load application state from date-based JSON file"""
        log_function_entry("load_state")
        try:
            # Try to load from today's app_state file first
            if os.path.exists(self.app_state_file):
                with open(self.app_state_file, 'r') as f:
                    state_data = json.load(f)
                logger.info(f" State loaded from {self.app_state_file} successfully")
                log_function_exit("load_state", "success")
                return state_data
            else:
                # Check if generic app_state.json exists and if it's from today
                if os.path.exists('app_state.json'):
                    with open('app_state.json', 'r') as f:
                        state_data = json.load(f)
                    
                    # Check if the state is from today by examining timestamp
                    state_timestamp = state_data.get('timestamp', '')
                    if state_timestamp:
                        try:
                            from datetime import datetime
                            state_date = datetime.fromisoformat(state_timestamp.replace('Z', '+00:00')).date()
                            today_date = datetime.now().date()
                            
                            if state_date == today_date:
                                # State is from today, migrate it
                                logger.info(" State from today found in app_state.json - migrating to today's file")
                                with open(self.app_state_file, 'w') as f:
                                    json.dump(state_data, f, indent=2, default=self._json_serializer)
                                logger.info(f" State migrated to {self.app_state_file}")
                                log_function_exit("load_state", "migrated")
                                return state_data
                            else:
                                logger.warning(f" State in app_state.json is from {state_date}, not today ({today_date}) - starting fresh")
                                log_function_exit("load_state", "stale_state")
                                return None
                        except Exception as date_parse_error:
                            logger.warning(f" Could not parse state timestamp '{state_timestamp}': {date_parse_error} - starting fresh")
                            log_function_exit("load_state", "invalid_timestamp")
                            return None
                    else:
                        logger.warning(" No timestamp in app_state.json - starting fresh for new day")
                        log_function_exit("load_state", "no_timestamp")
                        return None
                else:
                    logger.warning(f" {self.app_state_file} not found - starting with empty state")
                    log_function_exit("load_state", "no_file")
                    return None
        except Exception as e:
            logger.error(f"❌ Error loading state from {self.app_state_file}: {e}")
            log_function_exit("load_state", error=str(e))
            return None

    def save_current_state(self):
        """Save current application state to date-based JSON file"""
        log_function_entry("save_current_state")
        try:
            if not self.trader:
                logger.warning(" Cannot save state - trader not initialized")
                log_function_exit("save_current_state", "no_trader")
                return
                
            logger.debug(" Building state data for saving...")
            
            # Debug: Check what data we're about to save (no positions)
            logger.info(f"DEBUG SAVE: About to save non-position state data")
            
            state_data = {
                "timestamp": datetime.now().isoformat(),
                "trader_initialized": True,
                "is_trading_active": self.is_trading_active,
                "fyers_available": FYERS_AVAILABLE,
                "current_nifty_price": self.trader.current_nifty_price,
                "current_atm_strike": self.trader.current_atm_strike,
                "current_vwap": self.trader.current_vwap,
                "simulation_mode": self.trader.simulation_mode,
                # NOTE: Positions are now managed entirely by trader object, not saved to file
                "trading_portfolio": self._serialize_portfolio(self.trader.trading_portfolio),
                "decision_interval": self.trader.decision_interval,
                "vwap_override_enabled": self.trader.vwap_override_enabled,
                "vwap_override_value": self.trader.vwap_override_value,
                "recent_premium_data": self._serialize_premium_data(self.trader.combined_premium_data[-10:] if self.trader.combined_premium_data else [])
            }
            
            logger.debug(f" State data prepared (positions managed by trader object only)")
            
            # Save to date-based file only (no more generic app_state.json for daily reset)
            with open(self.app_state_file, 'w') as f:
                json.dump(state_data, f, indent=2, default=self._json_serializer)
            
            logger.debug(f" State saved to {self.app_state_file} successfully")
            log_function_exit("save_current_state", "success")
                
        except Exception as e:
            logger.error(f"❌ Error saving state to {self.app_state_file}: {e}")
            log_function_exit("save_current_state", error=str(e))

    def _json_serializer(self, obj):
        """Custom JSON serializer for datetime and other objects"""
        logger.debug(f" Serializing object of type: {type(obj)}")
        try:
            if isinstance(obj, datetime):
                result = obj.isoformat()
                logger.debug(f" Serialized datetime: {result}")
                return result
            elif hasattr(obj, '__dict__'):
                result = obj.__dict__
                logger.debug(f" Serialized object dict: {result}")
                return result
            else:
                result = str(obj)
                logger.debug(f" Serialized as string: {result}")
                return result
        except Exception as e:
            logger.error(f"❌ Error serializing object {obj}: {e}")
            return str(obj)

    def _serialize_portfolio(self, portfolio):
        """Serialize trading portfolio, handling datetime objects"""
        log_function_entry("_serialize_portfolio", portfolio_exists=portfolio is not None)
        try:
            if not portfolio:
                logger.debug(" Portfolio is None/empty - returning empty dict")
                return {}
            
            serialized = {}
            for key, value in portfolio.items():
                if isinstance(value, datetime):
                    serialized[key] = value.isoformat() if value else None
                    logger.debug(f" Serialized datetime field {key}: {serialized[key]}")
                else:
                    serialized[key] = value
                    logger.debug(f" Copied field {key}: {value}")
            
            logger.debug(f" Portfolio serialized successfully: {len(serialized)} fields")
            log_function_exit("_serialize_portfolio", "success", f"{len(serialized)} fields")
            return serialized
        except Exception as e:
            logger.error(f"❌ Error serializing portfolio: {e}")
            log_function_exit("_serialize_portfolio", error=str(e))
            return {}

    def _serialize_premium_data(self, premium_data):
        """Serialize premium data, handling datetime objects"""
        log_function_entry("_serialize_premium_data", data_count=len(premium_data) if premium_data else 0)
        try:
            if not premium_data:
                logger.debug(" Premium data is None/empty - returning empty list")
                return []
            
            serialized = []
            for i, data in enumerate(premium_data):
                if isinstance(data, dict):
                    serialized_data = {}
                    for key, value in data.items():
                        if isinstance(value, datetime):
                            serialized_data[key] = value.isoformat()
                        else:
                            serialized_data[key] = value
                    serialized.append(serialized_data)
                    logger.debug(f" Serialized premium data item {i}: {len(serialized_data)} fields")
                else:
                    serialized.append(data)
                    logger.debug(f" Added premium data item {i} as-is")
            
            logger.debug(f" Premium data serialized successfully: {len(serialized)} items")
            log_function_exit("_serialize_premium_data", "success", f"{len(serialized)} items")
            return serialized
        except Exception as e:
            logger.error(f"❌ Error serializing premium data: {e}")
            log_function_exit("_serialize_premium_data", error=str(e))
            return []

    def _serialize_positions(self, positions):
        """Convert position objects to serializable format"""
        log_function_entry("_serialize_positions", positions_exists=positions is not None)
        try:
            if not positions:
                logger.debug(" Positions is None/empty - returning default structure")
                return {"CE": None, "PE": None}
            
            logger.debug(f" Serializing positions: {type(positions)}")
            serialized = {}
            
            for key, position in positions.items():
                logger.debug(f" Processing position {key}: type={type(position)}, value={position}")
                
                if position is None:
                    serialized[key] = None
                    logger.debug(f" Position {key} is None")
                elif isinstance(position, dict):
                    # Already a dictionary, just ensure datetime objects are serialized
                    serialized_position = {}
                    for pos_key, pos_value in position.items():
                        if isinstance(pos_value, datetime):
                            serialized_position[pos_key] = pos_value.isoformat()
                            logger.debug(f" Serialized datetime {pos_key} for {key}")
                        else:
                            serialized_position[pos_key] = pos_value
                    serialized[key] = serialized_position
                    logger.debug(f" Position {key} serialized as dict with {len(serialized_position)} fields")
                else:
                    # Handle position objects with attributes
                    try:
                        if hasattr(position, '__dict__'):
                            pos_dict = {}
                            for attr_name, attr_value in position.__dict__.items():
                                if isinstance(attr_value, datetime):
                                    pos_dict[attr_name] = attr_value.isoformat()
                                    logger.debug(f" Serialized datetime attribute {attr_name} for {key}")
                                else:
                                    pos_dict[attr_name] = attr_value
                            serialized[key] = pos_dict
                            logger.debug(f" Position {key} serialized from object attributes: {len(pos_dict)} fields")
                        else:
                            # Fallback for unknown position types
                            fallback_dict = {
                                'symbol': getattr(position, 'symbol', 'Unknown'),
                                'qty': getattr(position, 'qty', 0),
                                'entry_price': getattr(position, 'avg_price', 0),
                                'current_price': getattr(position, 'current_price', 0)
                            }
                            serialized[key] = fallback_dict
                            logger.debug(f" Position {key} serialized using fallback method")
                    except Exception as e:
                        logger.warning(f"⚠️ Error serializing position {key}: {e}")
                        serialized[key] = {"error": "Could not serialize position", "type": str(type(position))}
            
            logger.debug(f" Positions serialized successfully: CE={serialized.get('CE') is not None}, PE={serialized.get('PE') is not None}")
            log_function_exit("_serialize_positions", "success", f"CE={serialized.get('CE') is not None}, PE={serialized.get('PE') is not None}")
            return serialized
        except Exception as e:
            logger.error(f"❌ Error serializing positions: {e}")
            log_function_exit("_serialize_positions", error=str(e))
            return {"CE": None, "PE": None}

    def start_periodic_save(self):
        """Start periodic state saving for non-position data"""
        log_function_entry("start_periodic_save")
        async def save_periodically():
            save_count = 0
            while True:
                try:
                    self.save_current_state()
                    save_count += 1
                    logger.debug(f"Periodic save #{save_count} completed (non-position data only)")
                    await asyncio.sleep(10)  # Save every 10 seconds - less frequent since no positions
                except Exception as e:
                    logger.error(f"❌ Error in periodic save #{save_count}: {e}")
                    await asyncio.sleep(10)
        
        logger.info("Starting periodic state saving (every 10 seconds, non-position data only)")
        asyncio.create_task(save_periodically())
        log_function_exit("start_periodic_save", "success")

    def add_websocket_client(self, websocket):
        """Add WebSocket client"""
        log_function_entry("add_websocket_client")
        self.websocket_clients.add(websocket)
        client_count = len(self.websocket_clients)
        logger.info(f" WebSocket client connected. Total clients: {client_count}")
        log_function_exit("add_websocket_client", "success", f"total_clients={client_count}")

    def remove_websocket_client(self, websocket):
        """Remove WebSocket client"""
        log_function_entry("remove_websocket_client")
        self.websocket_clients.discard(websocket)
        client_count = len(self.websocket_clients)
        logger.info(f" WebSocket client disconnected. Total clients: {client_count}")
        log_function_exit("remove_websocket_client", "success", f"total_clients={client_count}")

    def calculate_lifetime_portfolio_stats(self):
        """Calculate lifetime portfolio statistics by aggregating all historical app_state files"""
        log_function_entry("calculate_lifetime_portfolio_stats")
        try:
            import glob
            import os
            from datetime import datetime, timedelta
            
            # Find all app_state files with date pattern
            pattern = "app_state_*.json"
            state_files = glob.glob(pattern)
            
            if not state_files:
                logger.debug("No historical state files found")
                return {
                    "lifetime_total_pnl": 0,
                    "lifetime_total_trades": 0,
                    "lifetime_winning_trades": 0,
                    "lifetime_losing_trades": 0,
                    "lifetime_win_rate": 0,
                    "total_trading_days": 0,
                    "first_trading_date": None,
                    "last_trading_date": None,
                    "daily_breakdown": []
                }
            
            daily_stats = []
            total_pnl = 0
            total_trades = 0
            total_winning = 0
            total_losing = 0
            
            logger.debug(f"Found {len(state_files)} state files to analyze")
            
            for file_path in sorted(state_files):
                try:
                    # Extract date from filename
                    filename = os.path.basename(file_path)
                    if not filename.startswith('app_state_') or not filename.endswith('.json'):
                        continue
                        
                    date_str = filename.replace('app_state_', '').replace('.json', '')
                    if len(date_str) != 8:  # YYYYMMDD format
                        continue
                    
                    # Parse the date
                    file_date = datetime.strptime(date_str, '%Y%m%d').date()
                    
                    # Read the file
                    with open(file_path, 'r') as f:
                        state_data = json.load(f)
                    
                    # Extract portfolio data
                    portfolio = state_data.get('trading_portfolio', {})
                    # Backward compatibility: check for old virtual_portfolio key
                    if not portfolio:
                        portfolio = state_data.get('virtual_portfolio', {})
                    
                    if not portfolio:
                        continue
                    
                    day_pnl = portfolio.get('total_pnl', 0)
                    day_trades = portfolio.get('total_trades', 0)
                    day_winning = portfolio.get('winning_trades', 0)
                    day_losing = portfolio.get('losing_trades', 0)
                    
                    # Only include days with trading activity
                    if day_trades > 0:
                        daily_stats.append({
                            "date": file_date.strftime('%Y-%m-%d'),
                            "total_pnl": day_pnl,
                            "total_trades": day_trades,
                            "winning_trades": day_winning,
                            "losing_trades": day_losing,
                            "win_rate": (day_winning / day_trades * 100) if day_trades > 0 else 0,
                            "avg_pnl_per_trade": (day_pnl / day_trades) if day_trades > 0 else 0
                        })
                        
                        total_pnl += day_pnl
                        total_trades += day_trades
                        total_winning += day_winning
                        total_losing += day_losing
                        
                        logger.debug(f"Processed {file_date}: PnL={day_pnl}, Trades={day_trades}")
                
                except Exception as file_error:
                    logger.warning(f"Error processing file {file_path}: {file_error}")
                    continue
            
            # Calculate aggregated statistics
            lifetime_win_rate = (total_winning / total_trades * 100) if total_trades > 0 else 0
            
            # Get date range
            first_date = None
            last_date = None
            if daily_stats:
                first_date = daily_stats[0]["date"]
                last_date = daily_stats[-1]["date"]
            
            result = {
                "lifetime_total_pnl": total_pnl,
                "lifetime_total_trades": total_trades,
                "lifetime_winning_trades": total_winning,
                "lifetime_losing_trades": total_losing,
                "lifetime_win_rate": round(lifetime_win_rate, 2),
                "lifetime_avg_pnl_per_trade": round(total_pnl / total_trades, 2) if total_trades > 0 else 0,
                "total_trading_days": len(daily_stats),
                "first_trading_date": first_date,
                "last_trading_date": last_date,
                "daily_breakdown": daily_stats[-10:]  # Last 10 days for display
            }
            
            logger.info(f"Lifetime stats calculated: PnL={total_pnl}, Trades={total_trades}, Days={len(daily_stats)}")
            log_function_exit("calculate_lifetime_portfolio_stats", "success", f"days={len(daily_stats)}")
            return result
            
        except Exception as e:
            logger.error(f"❌ Error calculating lifetime portfolio stats: {e}")
            log_function_exit("calculate_lifetime_portfolio_stats", error=str(e))
            return {
                "lifetime_total_pnl": 0,
                "lifetime_total_trades": 0,
                "lifetime_winning_trades": 0,
                "lifetime_losing_trades": 0,
                "lifetime_win_rate": 0,
                "total_trading_days": 0,
                "error": str(e)
            }

    async def broadcast_to_websockets(self, message):
        """Broadcast message to all connected WebSocket clients"""
        log_function_entry("broadcast_to_websockets", client_count=len(self.websocket_clients))
        try:
            if not self.websocket_clients:
                logger.debug(" No WebSocket clients to broadcast to")
                log_function_exit("broadcast_to_websockets", "no_clients")
                return
                
            disconnected_clients = set()
            sent_count = 0
            
            logger.debug(f" Broadcasting message to {len(self.websocket_clients)} clients")
            
            for client in self.websocket_clients.copy():
                try:
                    await client.send_text(json.dumps(message))
                    sent_count += 1
                    logger.debug(f" Message sent to client #{sent_count}")
                except Exception as e:
                    logger.warning(f"⚠️ Failed to send message to WebSocket client: {e}")
                    disconnected_clients.add(client)
            
            # Clean up disconnected clients
            for client in disconnected_clients:
                self.remove_websocket_client(client)
            
            logger.debug(f" Broadcast completed: {sent_count} successful, {len(disconnected_clients)} failed")
            log_function_exit("broadcast_to_websockets", "success", f"sent={sent_count}, failed={len(disconnected_clients)}")
        except Exception as e:
            logger.error(f"❌ Error in WebSocket broadcast: {e}")
            log_function_exit("broadcast_to_websockets", error=str(e))

    def start_trading_thread(self):
        """Start trading in background thread"""
        log_function_entry("start_trading_thread")
        try:
            if self.trading_thread and self.trading_thread.is_alive():
                logger.warning(" Trading thread already running - skipping start")
                log_function_exit("start_trading_thread", "already_running")
                return

            def trading_worker():
                logger.info(" Trading background thread starting...")
                try:
                    self.is_trading_active = True
                    logger.info(f" Trading status set to active: {self.is_trading_active}")
                    logger.info("DEBUG: About to check trader and run_data_collection method...")
                    logger.info(f"DEBUG: self.trader is: {self.trader}")
                    logger.info(f"DEBUG: self.trader type: {type(self.trader) if self.trader else 'None'}")
                    if self.trader:
                        has_method = hasattr(self.trader, 'run_data_collection')
                        logger.info(f"DEBUG: hasattr(self.trader, 'run_data_collection'): {has_method}")
                    
                    if self.trader and hasattr(self.trader, 'run_data_collection'):
                        logger.info("🚀 Calling trader.run_data_collection() method to start continuous market data loop...")
                        log_trader_state(self.trader, "before_start")
                        
                        # Add debug info about the trader object
                        logger.info(f"🔍 Trader object type: {type(self.trader)}")
                        logger.info(f"🔍 Trader is_running before call: {getattr(self.trader, 'is_running', 'NOT_SET')}")
                        
                        # Call the method and catch any exceptions
                        try:
                            self.trader.run_data_collection()  # This will run the continuous trading data collection loop
                            logger.info("trader.run_data_collection() completed successfully")
                        except Exception as e:
                            logger.error(f"❌ Exception in run_data_collection(): {e}")
                            logger.exception("Full exception traceback:")
                        
                        log_trader_state(self.trader, "after_start")
                    else:
                        logger.error("❌ Trader run_data_collection method not found or trader not initialized")
                        if self.trader:
                            logger.info(f"🔍 Trader object type: {type(self.trader)}")
                            available_methods = [method for method in dir(self.trader) if not method.startswith('_')]
                            logger.info(f"🔍 Available methods: {available_methods[:10]}...")  # Show first 10 methods
                            run_methods = [method for method in available_methods if 'run' in method.lower()]
                            start_methods = [method for method in available_methods if 'start' in method.lower()]
                            logger.info(f"🔍 Methods with 'run': {run_methods}")
                            logger.info(f"🔍 Methods with 'start': {start_methods}")
                        else:
                            logger.error("❌ Trader object is None")
                        
                except Exception as e:
                    logger.error(f"❌ Critical error in trading thread: {e}")
                    logger.exception("Full error traceback:")
                finally:
                    logger.info(f"Trading thread finishing - is_trading_active remains: {self.is_trading_active}")
                    log_trader_state(self.trader, "thread_exit")

            logger.debug(" Creating trading thread...")
            self.trading_thread = threading.Thread(target=trading_worker, daemon=True)
            self.trading_thread.start()
            
            logger.info(f" Trading thread started successfully - is_trading_active: {self.is_trading_active}")
            log_function_exit("start_trading_thread", "success", f"thread_id={self.trading_thread.ident}")
        except Exception as e:
            logger.error(f"❌ Error starting trading thread: {e}")
            log_function_exit("start_trading_thread", error=str(e))

    def stop_trading(self):
        """Stop trading"""
        log_function_entry("stop_trading")
        try:
            if self.trader:
                logger.info(" Sending stop signal to trader...")
                self.trader.is_running = False
                logger.info(" Trading background thread stop signal sent")
                log_trader_state(self.trader, "stop_signal_sent")
            else:
                logger.warning(" Cannot stop trading - trader not initialized")
            
            self.is_trading_active = False
            logger.info(f"Trading status set to inactive: {self.is_trading_active}")
            log_function_exit("stop_trading", "success")
        except Exception as e:
            logger.error(f"❌ Error stopping trading: {e}")
            log_function_exit("stop_trading", error=str(e))

# Global state manager
state_manager = AppStateManager()

# Routes

@app.get("/", response_class=HTMLResponse)
async def read_root():
    """Serve the main dashboard"""
    log_function_entry("read_root")
    try:
        logger.info(" Serving main dashboard page")
        with open("static/index.html", encoding="utf-8") as f:
            content = f.read()
        logger.debug(f" HTML content loaded: {len(content)} characters")
        log_function_exit("read_root", "success", f"content_length={len(content)}")
        return HTMLResponse(content=content)
    except Exception as e:
        logger.error(f" Error serving main page: {e}")
        log_function_exit("read_root", "error", str(e))
        raise HTTPException(status_code=500, detail=f"Error loading main page: {str(e)}")

@app.get("/history", response_class=HTMLResponse)
async def read_history():
    """Serve the historical files page"""
    try:
        logger.info(" Serving historical files page")
        with open("static/history.html", encoding="utf-8") as f:
            content = f.read()
        return HTMLResponse(content=content)
    except FileNotFoundError:
        # If history.html doesn't exist, create a simple one
        logger.info(" Creating historical files page")
        simple_history_page = """
        <!DOCTYPE html>
        <html>
        <head>
            <title>Historical Excel Files</title>
            <meta charset="UTF-8">
            <meta name="viewport" content="width=device-width, initial-scale=1.0">
            <style>
                body { font-family: Arial, sans-serif; margin: 20px; background: #f5f5f5; }
                .container { max-width: 1200px; margin: 0 auto; background: white; padding: 20px; border-radius: 8px; }
                .header { text-align: center; margin-bottom: 30px; }
                .file-grid { display: grid; grid-template-columns: repeat(auto-fill, minmax(300px, 1fr)); gap: 15px; }
                .file-item { background: #f8f9fa; padding: 15px; border-radius: 8px; border: 1px solid #dee2e6; }
                .btn { padding: 8px 16px; background: #007bff; color: white; border: none; border-radius: 4px; cursor: pointer; text-decoration: none; display: inline-block; }
                .btn:hover { background: #0056b3; }
                .btn-secondary { background: #6c757d; }
                .btn-secondary:hover { background: #545b62; }
                .date-section { margin-bottom: 30px; }
                .date-header { background: #e9ecef; padding: 10px; border-radius: 4px; margin-bottom: 15px; }
            </style>
        </head>
        <body>
            <div class="container">
                <div class="header">
                    <h1>📚 Historical Excel Files</h1>
                    <p>All trading reports and analysis files</p>
                    <a href="/" class="btn btn-secondary">← Back to Dashboard</a>
                </div>
                <div id="history-content">
                    <p>Loading historical files...</p>
                </div>
            </div>
            <script>
                async function loadHistoricalFiles() {
                    try {
                        console.log('Loading historical files...');
                        const response = await fetch('/api/excel/list/all');
                        const data = await response.json();
                        console.log('API Response:', data);
                        
                        const container = document.getElementById('history-content');
                        
                        if (!data.files || data.files.length === 0) {
                            container.innerHTML = '<p>No historical files found.</p>';
                            return;
                        }
                        
                        console.log('Files found:', data.files.length);
                        
                        // Group files by date
                        const filesByDate = {};
                        data.files.forEach(file => {
                            const date = file.date;
                            console.log('Processing file:', file.filename, 'Date:', date);
                            if (!filesByDate[date]) {
                                filesByDate[date] = [];
                            }
                            filesByDate[date].push(file);
                        });
                        
                        console.log('Files grouped by date:', filesByDate);
                        
                        let html = '';
                        Object.keys(filesByDate).sort().reverse().forEach(date => {
                            const formatDate = date === 'unknown' ? 'Unknown Date' : 
                                new Date(date.substring(0,4) + '-' + date.substring(4,6) + '-' + date.substring(6,8)).toLocaleDateString();
                            
                            html += `<div class="date-section">`;
                            html += `<div class="date-header"><h3>${formatDate} (${date})</h3></div>`;
                            html += `<div class="file-grid">`;
                            
                            filesByDate[date].forEach(file => {
                                html += `
                                    <div class="file-item">
                                        <h5>${file.type.toUpperCase()}</h5>
                                        <p>${file.filename}</p>
                                        <p>Size: ${(file.size / 1024).toFixed(1)} KB</p>
                                        <p>Modified: ${new Date(file.modified).toLocaleString()}</p>
                                        <button class="btn" onclick="downloadFile('${file.type}', '${file.date}')">📊 Download</button>
                                    </div>
                                `;
                            });
                            
                            html += `</div></div>`;
                        });
                        
                        console.log('Generated HTML length:', html.length);
                        container.innerHTML = html;
                    } catch (error) {
                        console.error('Error loading historical files:', error);
                        document.getElementById('history-content').innerHTML = '<p>Error loading files: ' + error.message + '</p>';
                    }
                }
                
                async function downloadFile(fileType, fileDate) {
                    try {
                        const response = await fetch(`/api/excel/download/${fileType}?date=${fileDate}`);
                        if (response.ok) {
                            const blob = await response.blob();
                            const url = window.URL.createObjectURL(blob);
                            const a = document.createElement('a');
                            a.href = url;
                            
                            // Try to get filename from Content-Disposition header
                            const contentDisposition = response.headers.get('Content-Disposition');
                            let filename = `${fileType}_${fileDate}.xlsx`;
                            
                            if (contentDisposition) {
                                const filenameMatch = contentDisposition.match(/filename[^;=\\n]*=((['"]).*?\\2|[^;\\n]*)/);
                                if (filenameMatch && filenameMatch[1]) {
                                    filename = filenameMatch[1].replace(/['"]/g, '');
                                }
                            }
                            
                            a.download = filename;
                            document.body.appendChild(a);
                            a.click();
                            window.URL.revokeObjectURL(url);
                            document.body.removeChild(a);
                        } else {
                            const error = await response.json();
                            alert('Download failed: ' + error.detail);
                        }
                    } catch (error) {
                        alert('Download failed: ' + error.message);
                    }
                }
                
                // Load files when page loads
                loadHistoricalFiles();
            </script>
        </body>
        </html>
        """
        return HTMLResponse(content=simple_history_page)
    except Exception as e:
        logger.error(f" Error serving historical files page: {e}")
        raise HTTPException(status_code=500, detail=f"Error loading historical files page: {str(e)}")

@app.get("/lifetime-stats.html", response_class=HTMLResponse)
async def read_lifetime_stats():
    """Serve the lifetime statistics page"""
    try:
        logger.info(" Serving lifetime statistics page")
        with open("static/lifetime-stats.html", encoding="utf-8") as f:
            content = f.read()
        return HTMLResponse(content=content)
    except FileNotFoundError:
        logger.error(" lifetime-stats.html file not found")
        raise HTTPException(status_code=404, detail="Lifetime statistics page not found")
    except Exception as e:
        logger.error(f" Error serving lifetime statistics page: {e}")
        raise HTTPException(status_code=500, detail=f"Error loading lifetime statistics page: {str(e)}")

@app.post("/api/debug/clear-position/{option_type}")
async def debug_clear_position(option_type: str):
    """Debug endpoint to manually clear a position"""
    if not state_manager.trader:
        return {"error": "Trader not initialized"}
    
    if option_type not in ["CE", "PE"]:
        return {"error": "Invalid option type"}
    
    # Direct manipulation
    logger.info(f"Debug: Directly clearing {option_type} position")
    logger.info(f"Before clear: {state_manager.trader.positions.get(option_type)}")
    
    state_manager.trader.positions[option_type] = None
    
    logger.info(f"After clear: {state_manager.trader.positions.get(option_type)}")
    
    # Save state
    state_manager.save_current_state()
    
    return {
        "status": "success", 
        "message": f"Debug: {option_type} position cleared directly",
        "position_after": state_manager.trader.positions.get(option_type)
    }

@app.get("/api/debug/state-data")
async def debug_state_data():
    """Debug endpoint to see what would be saved"""
    if not state_manager.trader:
        return {"error": "Trader not initialized"}
    
    state_data = {
        "trader_positions_raw": state_manager.trader.positions,
        "trader_positions_serialized": state_manager._serialize_positions(state_manager.trader.positions),
        "trader_long_positions": state_manager.trader.long_positions,
    }
    return state_data

@app.post("/api/debug/save-state")
async def debug_save_state():
    """Debug endpoint to manually trigger state save"""
    try:
        state_manager.save_current_state()
        return {"status": "success", "message": "State saved manually"}
    except Exception as e:
        return {"status": "error", "message": str(e)}

@app.post("/api/debug/reset-portfolio")
async def debug_reset_portfolio():
    """Debug endpoint to reset portfolio to fresh state"""
    try:
        if not state_manager.trader:
            return {"status": "error", "message": "Trader not initialized"}
        
        # Reset portfolio to initial values
        state_manager.trader.trading_portfolio = {
            "cash": 100000,  # Starting with 1 lakh trading cash
            "total_pnl": 0,
            "total_trades": 0,
            "winning_trades": 0,
            "losing_trades": 0,
            "max_profit_seen": 0,
            "max_loss_seen": 0,
            "current_session_max_profit": 0,
            "current_session_max_loss": 0,
            "peak_drawdown": 0,
            "last_peak_time": None,
            "last_trough_time": None
        }
        
        # Clear all positions
        state_manager.trader.positions = {"CE": None, "PE": None}
        state_manager.trader.long_positions = {"CE": None, "PE": None}
        
        # Save the reset state
        state_manager.save_current_state()
        
        return {
            "status": "success", 
            "message": "Portfolio reset to fresh state",
            "portfolio": state_manager.trader.trading_portfolio
        }
    except Exception as e:
        return {"status": "error", "message": str(e)}

@app.get("/api/debug/trader-positions")
async def debug_trader_positions():
    """Debug endpoint to check raw trader positions"""
    if not state_manager.trader:
        return {"error": "Trader not initialized"}
    
    return {
        "trader_positions": state_manager.trader.positions,
        "trader_long_positions": state_manager.trader.long_positions,
        "positions_type": type(state_manager.trader.positions).__name__,
        "positions_id": id(state_manager.trader.positions)
    }

@app.get("/api/status")
async def get_trading_status(current_user: str = Depends(verify_token)):
    """Get current trading status"""
    log_function_entry("get_trading_status")
    try:
        logger.debug(" Building trading status response...")
        
        if not state_manager.trader:
            logger.warning(" Trading bot not initialized - returning not_initialized status")
            log_function_exit("get_trading_status", "not_initialized")
            return {"status": "not_initialized", "message": "Trading bot not initialized"}
        
        log_trader_state(state_manager.trader, "status_check")
        
        # Calculate unrealized PnL safely
        logger.debug(" Calculating unrealized PnL...")
        try:
            unrealized_pnl = state_manager.trader.calculate_unrealized_pnl()
            logger.debug(f" Unrealized PnL calculated: {unrealized_pnl}")
        except Exception as e:
            logger.warning(f"⚠️ Could not calculate unrealized PnL: {e}")
            unrealized_pnl = 0.0
        
        # Get API usage safely
        logger.debug(" Getting API usage status...")
        try:
            api_usage = state_manager.trader.get_api_usage_status()
            logger.debug(f" API usage retrieved: {api_usage}")
        except Exception as e:
            logger.warning(f"⚠️ Could not get API usage: {e}")
            api_usage = {"quote_calls": 0, "historical_calls": 0}
        
        # Check market hours safely
        logger.debug(" Checking market hours...")
        try:
            market_hours = state_manager.trader.is_market_hours()
            logger.debug(f" Market hours check: {market_hours}")
        except Exception as e:
            logger.warning(f"⚠️ Could not check market hours: {e}")
            market_hours = True  # Default to True
        
        # Test actual Fyers API connectivity
        logger.debug(" Testing Fyers API connectivity...")
        api_working = False
        api_error_message = None
        try:
            if hasattr(state_manager.trader, 'fyers') and state_manager.trader.fyers is not None:
                # Try to get Nifty price as a connectivity test
                nifty_price = state_manager.trader.get_nifty_price()
                if nifty_price is not None and nifty_price > 0:
                    api_working = True
                    logger.debug(f" Fyers API working - Nifty price: {nifty_price}")
                else:
                    api_error_message = "API call returned invalid data"
                    logger.warning(f" Fyers API test failed: {api_error_message}")
            else:
                api_error_message = "Fyers API not configured"
                logger.warning(f" Fyers API test failed: {api_error_message}")
        except Exception as e:
            api_error_message = str(e)
            logger.warning(f"⚠️ Fyers API connectivity test failed: {e}")
        
        # Build status data
        trading_active = state_manager.is_trading_active or (state_manager.trading_thread and state_manager.trading_thread.is_alive())
        
        # Get current CE and PE prices from latest data with thread safety
        current_ce_price = 0.0
        current_pe_price = 0.0
        combined_premium = 0.0
        latest_data = None
        data_snapshot = []  # Initialize data_snapshot to prevent UnboundLocalError
        
        # Create a thread-safe snapshot of the latest data to prevent race conditions
        try:
            if state_manager.trader.combined_premium_data:
                # Take a snapshot to avoid race condition during data updates
                data_snapshot = list(state_manager.trader.combined_premium_data)
                if data_snapshot:
                    latest_data = data_snapshot[-1].copy()  # Create a copy to prevent modification during access
                    current_ce_price = latest_data.get('CE', 0.0)
                    current_pe_price = latest_data.get('PE', 0.0)
                    combined_premium = current_ce_price + current_pe_price
                    logger.debug(f"💰 Current prices (thread-safe): CE={current_ce_price}, PE={current_pe_price}, Combined={combined_premium}")
        except (IndexError, AttributeError, TypeError) as e:
            logger.warning(f"⚠️ Error accessing latest price data: {e}, using fallback values")
            current_ce_price = current_pe_price = combined_premium = 0.0
            data_snapshot = []  # Ensure data_snapshot is empty list on error
        
        # Get position data to determine the active trading ATM strike
        active_positions = any(pos is not None for pos in state_manager.trader.positions.values())
        active_long_positions = any(pos is not None for pos in state_manager.trader.long_positions.values())
        
        # Calculate what the current market ATM should be based on Nifty price
        market_atm_strike = None
        if state_manager.trader.current_nifty_price:
            market_atm_strike = state_manager.trader.round_to_nearest_50(state_manager.trader.current_nifty_price)
        
        # The trading ATM is the one currently being used for positions
        trading_atm_strike = state_manager.trader.current_atm_strike
        
        status_data = {
            "status": "active" if trading_active else "inactive",
            "positions": state_manager.trader.positions or {"CE": None, "PE": None},
            "long_positions": state_manager.trader.long_positions or {"CE": None, "PE": None},
            "portfolio": state_manager.trader.trading_portfolio or {"total_pnl": 0, "total_trades": 0},
            "nifty_price": state_manager.trader.current_nifty_price or 0.0,
            "atm_strike": trading_atm_strike or 0,  # The ATM strike being used for trading
            "market_atm_strike": market_atm_strike or 0,  # What ATM should be based on current Nifty
            "atm_locked": active_positions or active_long_positions,  # Whether ATM is locked due to positions
            "current_vwap": state_manager.trader.current_vwap or 0.0,
            "current_market_vwap": getattr(state_manager.trader, 'current_market_vwap', None) or 0.0,
            "unrealized_pnl": unrealized_pnl,
            "simulation_mode": getattr(state_manager.trader, 'simulation_mode', True),
            "decision_interval": getattr(state_manager.trader, 'decision_interval', "1minute"),
            "vwap_override": {
                "enabled": getattr(state_manager.trader, 'vwap_override_enabled', False),
                "value": getattr(state_manager.trader, 'vwap_override_value', None),
                "cycle": state_manager.trader.get_vwap_override_cycle_status() if state_manager.trader else {"state": "READY", "started": False}
            },
            # Enhanced price information
            "current_prices": {
                "ce_price": current_ce_price,
                "pe_price": current_pe_price,
                "combined_premium": combined_premium,
                "last_updated": latest_data.get('timestamp') if latest_data else None
            },
            "api_usage": api_usage,
            "timestamp": datetime.now().isoformat(),
            "market_hours": market_hours,
            "combined_premium_data": data_snapshot[-5:] if data_snapshot else [],
            "fyers_available": FYERS_AVAILABLE,
            "fyers_api_status": {
                "module_available": FYERS_AVAILABLE,
                "api_configured": hasattr(state_manager.trader, 'fyers') and state_manager.trader.fyers is not None,
                "has_credentials": bool(getattr(state_manager.trader, 'client_id', None) and getattr(state_manager.trader, 'access_token', None)),
                "api_working": api_working,
                "api_error": api_error_message
            },
            "trading_safety": state_manager.trader.get_trading_safety_status() if hasattr(state_manager.trader, 'get_trading_safety_status') else {
                "trading_disabled": False,
                "trading_disabled_reason": None,
                "is_running": getattr(state_manager.trader, 'is_running', False),
                "can_place_orders": True
            },
            "reset_capabilities": {
                "trading_disabled_reset_needed": getattr(state_manager.trader, 'trading_disabled', False),
                "vwap_cycle_reset_needed": (getattr(state_manager.trader, 'vwap_override_enabled', False) and 
                                          getattr(state_manager.trader, 'vwap_override_cycle_state', 'READY') == "COMPLETED"),
                "consolidated_reset_available": True,
                "individual_resets_available": True
            },
            "trader_initialized": True
        }
        
        # Helper function to check if position is active
        def is_position_active(position):
            return (position is not None and 
                   position != {} and 
                   isinstance(position, dict) and 
                   (position.get('quantity', 0) != 0 or  # For positions with quantity field
                    (position.get('strike') is not None and position.get('entry_price') is not None)))  # For positions with strike/price data
        
        ce_position = status_data['positions'].get('CE')
        pe_position = status_data['positions'].get('PE')
        
        logger.info(f"Status data compiled - status: {status_data['status']}, "
                   f"CE_pos: {is_position_active(ce_position)}, "
                   f"PE_pos: {is_position_active(pe_position)}, "
                   f"nifty: {status_data['nifty_price']}")
        
        log_function_exit("get_trading_status", "success", f"status={status_data['status']}")
        return status_data
        
    except Exception as e:
        logger.error(f"❌ Error getting trading status: {e}")
        logger.exception("Full error traceback:")
        log_function_exit("get_trading_status", error=str(e))
        
        # Return a safe default status instead of error
        fallback_status = {
            "status": "error",
            "message": f"Error getting status: {str(e)}",
            "trader_initialized": False,
            "nifty_price": 0.0,
            "atm_strike": 0,
            "current_vwap": 0.0,
            "positions": {"CE": None, "PE": None},
            "long_positions": {"CE": None, "PE": None},
            "portfolio": {"total_pnl": 0, "total_trades": 0},
            "current_prices": {
                "ce_price": 0.0,
                "pe_price": 0.0,
                "combined_premium": 0.0,
                "last_updated": None
            },
            "simulation_mode": True,
            "fyers_available": FYERS_AVAILABLE,
            "fyers_api_status": {
                "module_available": FYERS_AVAILABLE,
                "api_configured": False,
                "has_credentials": False,
                "api_working": False,
                "api_error": "Trader not initialized"
            },
            "timestamp": datetime.now().isoformat()
        }
        
        logger.debug(f" Returning fallback status due to error")
        return fallback_status

@app.get("/fyers-status", response_class=HTMLResponse)
async def fyers_status_page():
    """Simple HTML page to check Fyers API status"""
    return f"""
    <!DOCTYPE html>
    <html>
    <head>
        <title>Fyers API Status - Nifty Options Trader</title>
        <meta charset="UTF-8">
        <meta name="viewport" content="width=device-width, initial-scale=1.0">
        <style>
            body {{
                font-family: 'Segoe UI', Arial, sans-serif;
                margin: 0;
                padding: 20px;
                background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
                min-height: 100vh;
            }}
            .container {{
                max-width: 800px;
                margin: 0 auto;
                background: white;
                border-radius: 15px;
                box-shadow: 0 10px 30px rgba(0,0,0,0.1);
                padding: 30px;
            }}
            h1 {{
                color: #333;
                text-align: center;
                margin-bottom: 30px;
            }}
            .status-card {{
                background: #f8f9fa;
                border-radius: 10px;
                padding: 20px;
                margin: 20px 0;
                border-left: 5px solid #007bff;
            }}
            .status-connected {{
                border-left-color: #28a745;
                background: #d4edda;
            }}
            .status-error {{
                border-left-color: #dc3545;
                background: #f8d7da;
            }}
            .status-warning {{
                border-left-color: #ffc107;
                background: #fff3cd;
            }}
            .btn {{
                background: #007bff;
                color: white;
                padding: 10px 20px;
                border: none;
                border-radius: 5px;
                cursor: pointer;
                margin: 10px 5px;
                transition: background 0.3s;
            }}
            .btn:hover {{
                background: #0056b3;
            }}
            .detail-row {{
                display: flex;
                justify-content: space-between;
                margin: 10px 0;
                padding: 5px;
                border-bottom: 1px solid #eee;
            }}
            .detail-label {{
                font-weight: bold;
                color: #555;
            }}
            .detail-value {{
                color: #333;
            }}
            #statusContent {{
                min-height: 200px;
            }}
            .loading {{
                text-align: center;
                color: #666;
                font-style: italic;
            }}
            .back-link {{
                display: inline-block;
                margin-top: 20px;
                color: #007bff;
                text-decoration: none;
                font-weight: bold;
            }}
            .back-link:hover {{
                text-decoration: underline;
            }}
        </style>
    </head>
    <body>
        <div class="container">
            <h1>🔗 Fyers API Connection Status</h1>
            
            <div class="status-card">
                <h3>Connection Status Check</h3>
                <p>This page tests your Fyers API connection and displays the current status.</p>
                <button class="btn" onclick="checkStatus()">🔄 Check Status Now</button>
                <button class="btn" onclick="autoRefresh()">⏱️ Auto Refresh (30s)</button>
            </div>
            
            <div id="statusContent" class="loading">
                Click "Check Status Now" to test your Fyers API connection...
            </div>
            
            <div class="status-card">
                <h3>💡 Troubleshooting Tips</h3>
                <ul>
                    <li><strong>Module Unavailable:</strong> Install Fyers API with <code>pip install fyers-apiv3</code></li>
                    <li><strong>API Not Configured:</strong> Set your API credentials in the configuration page</li>
                    <li><strong>Connection Failed:</strong> Check your access token and ensure it's not expired</li>
                    <li><strong>Invalid Token:</strong> Generate a new access token from the Fyers app</li>
                </ul>
            </div>
            
            <a href="/" class="back-link">← Back to Trading Dashboard</a>
        </div>

        <script>
            let autoRefreshInterval = null;
            
            async function checkStatus() {{
                const content = document.getElementById('statusContent');
                content.innerHTML = '<div class="loading">🔄 Testing Fyers API connection...</div>';
                
                try {{
                    // Check if we're logged in first
                    const token = localStorage.getItem('auth_token');
                    if (!token) {{
                        content.innerHTML = `
                            <div class="status-card status-error">
                                <h3>❌ Authentication Required</h3>
                                <p>Please log in first to check API status.</p>
                                <a href="/auth/login" class="btn">Login</a>
                            </div>
                        `;
                        return;
                    }}
                    
                    const response = await fetch('/api/fyers/status', {{
                        headers: {{
                            'Authorization': `Bearer ${{token}}`
                        }}
                    }});
                    
                    if (!response.ok) {{
                        throw new Error(`HTTP ${{response.status}}: ${{response.statusText}}`);
                    }}
                    
                    const data = await response.json();
                    displayStatus(data);
                    
                }} catch (error) {{
                    content.innerHTML = `
                        <div class="status-card status-error">
                            <h3>❌ Error Checking Status</h3>
                            <p>Failed to check API status: ${{error.message}}</p>
                            <p>Make sure you're logged in and the server is running.</p>
                        </div>
                    `;
                }}
            }}
            
            function displayStatus(data) {{
                const content = document.getElementById('statusContent');
                
                // Determine status color
                let statusClass = 'status-warning';
                let statusIcon = '⚠️';
                let statusText = data.connection_status;
                
                if (data.connection_status === 'connected') {{
                    statusClass = 'status-connected';
                    statusIcon = '✅';
                    statusText = 'Connected Successfully';
                }} else if (data.connection_status.includes('error') || data.connection_status.includes('failed')) {{
                    statusClass = 'status-error';
                    statusIcon = '❌';
                }}
                
                let html = `
                    <div class="status-card ${{statusClass}}">
                        <h3>${{statusIcon}} ${{statusText}}</h3>
                        <div class="detail-row">
                            <span class="detail-label">Last Test Time:</span>
                            <span class="detail-value">${{new Date(data.last_test_time).toLocaleString()}}</span>
                        </div>
                `;
                
                // Add basic status details
                html += `
                    <div class="detail-row">
                        <span class="detail-label">Fyers Module Available:</span>
                        <span class="detail-value">${{data.fyers_module_available ? '✅ Yes' : '❌ No'}}</span>
                    </div>
                    <div class="detail-row">
                        <span class="detail-label">Trader Initialized:</span>
                        <span class="detail-value">${{data.trader_initialized ? '✅ Yes' : '❌ No'}}</span>
                    </div>
                `;
                
                // Add credentials status
                if (data.api_credentials_status) {{
                    html += `
                        <div class="detail-row">
                            <span class="detail-label">Client ID Present:</span>
                            <span class="detail-value">${{data.api_credentials_status.client_id_present ? '✅ Yes' : '❌ No'}}</span>
                        </div>
                        <div class="detail-row">
                            <span class="detail-label">Access Token Present:</span>
                            <span class="detail-value">${{data.api_credentials_status.access_token_present ? '✅ Yes' : '❌ No'}}</span>
                        </div>
                    `;
                }}
                
                // Add test results if available
                if (data.test_results && Object.keys(data.test_results).length > 0) {{
                    html += `<h4>🧪 Test Results:</h4>`;
                    if (data.test_results.success) {{
                        html += `
                            <div class="detail-row">
                                <span class="detail-label">Response Time:</span>
                                <span class="detail-value">${{data.test_results.response_time_ms}} ms</span>
                            </div>
                            <div class="detail-row">
                                <span class="detail-label">Test Symbol:</span>
                                <span class="detail-value">${{data.test_results.test_symbol}}</span>
                            </div>
                            <div class="detail-row">
                                <span class="detail-label">Current Price:</span>
                                <span class="detail-value">${{data.test_results.current_price}}</span>
                            </div>
                        `;
                    }} else {{
                        html += `
                            <div class="detail-row">
                                <span class="detail-label">Error:</span>
                                <span class="detail-value">${{data.test_results.error || 'API test failed'}}</span>
                            </div>
                        `;
                    }}
                }}
                
                // Add error details if present
                if (data.error_details) {{
                    html += `
                        <h4>⚠️ Error Details:</h4>
                        <p style="background: #fff; padding: 10px; border-radius: 5px; font-family: monospace; font-size: 14px;">
                            ${{data.error_details}}
                        </p>
                    `;
                }}
                
                // Add trader info if available
                if (data.trader_info) {{
                    html += `
                        <h4>🤖 Trader Information:</h4>
                        <div class="detail-row">
                            <span class="detail-label">Client ID:</span>
                            <span class="detail-value">${{data.trader_info.client_id}}</span>
                        </div>
                        <div class="detail-row">
                            <span class="detail-label">Simulation Mode:</span>
                            <span class="detail-value">${{data.trader_info.simulation_mode ? '🎭 Yes' : '💰 No (Live Trading)'}}</span>
                        </div>
                        <div class="detail-row">
                            <span class="detail-label">Trading Active:</span>
                            <span class="detail-value">${{data.trader_info.is_running ? '🚀 Yes' : '⏸️ No'}}</span>
                        </div>
                    `;
                }}
                
                html += '</div>';
                content.innerHTML = html;
            }}
            
            function autoRefresh() {{
                if (autoRefreshInterval) {{
                    clearInterval(autoRefreshInterval);
                    autoRefreshInterval = null;
                    return;
                }}
                
                checkStatus(); // Check immediately
                autoRefreshInterval = setInterval(checkStatus, 30000); // Then every 30 seconds
                
                // Update button text
                const button = event.target;
                button.textContent = '⏹️ Stop Auto Refresh';
                button.onclick = function() {{
                    clearInterval(autoRefreshInterval);
                    autoRefreshInterval = null;
                    button.textContent = '⏱️ Auto Refresh (30s)';
                    button.onclick = autoRefresh;
                }};
            }}
            
            // Auto-check status on page load
            window.addEventListener('load', checkStatus);
        </script>
    </body>
    </html>
    """

@app.get("/api/fyers/status")
async def get_fyers_api_status(current_user: str = Depends(verify_token)):
    """Get detailed Fyers API connection status and test the connection (with caching to prevent burst calls)"""
    log_function_entry("get_fyers_api_status")
    
    current_time = datetime.now()
    
    # Check if we have valid cached data
    if (fyers_status_cache["data"] is not None and 
        fyers_status_cache["last_update"] is not None and 
        (current_time - fyers_status_cache["last_update"]).total_seconds() < fyers_status_cache["cache_duration"]):
        
        logger.debug(f"🔄 Returning cached Fyers status (age: {(current_time - fyers_status_cache['last_update']).total_seconds():.1f}s)")
        cached_data = fyers_status_cache["data"].copy()
        cached_data["cached"] = True
        cached_data["cache_age_seconds"] = round((current_time - fyers_status_cache["last_update"]).total_seconds(), 1)
        log_function_exit("get_fyers_api_status", "cached_response")
        return cached_data
    
    try:
        logger.info("🔍 Performing fresh Fyers API connection status check...")
        
        # Basic availability check
        status_data = {
            "fyers_module_available": FYERS_AVAILABLE,
            "trader_initialized": state_manager.trader is not None,
            "connection_status": "unknown",
            "last_test_time": current_time.isoformat(),
            "cached": False,
            "cache_age_seconds": 0,
            "api_credentials_status": {
                "client_id_present": False,
                "access_token_present": False,
                "config_file_exists": os.path.exists("config.txt"),
                "access_file_exists": os.path.exists("access.txt")
            },
            "test_results": {},
            "error_details": None
        }
        
        # Check if config files exist and have content
        try:
            if os.path.exists("config.txt"):
                with open("config.txt", "r") as f:
                    config_content = f.read().strip()
                    status_data["api_credentials_status"]["client_id_present"] = "CLIENT_ID" in config_content and len(config_content) > 20
            
            if os.path.exists("access.txt"):
                with open("access.txt", "r") as f:
                    access_content = f.read().strip()
                    status_data["api_credentials_status"]["access_token_present"] = len(access_content) > 10
        except Exception as e:
            logger.warning(f"Error reading config files: {e}")
        
        # If Fyers module is not available, return early
        if not FYERS_AVAILABLE:
            status_data["connection_status"] = "module_unavailable"
            status_data["error_details"] = "Fyers API module not installed or not importable"
            logger.warning("⚠️ Fyers API module not available")
            
            # Cache this result since module availability won't change without restart
            fyers_status_cache["data"] = status_data.copy()
            fyers_status_cache["last_update"] = current_time
            fyers_status_cache["cache_duration"] = 30  # Longer cache for static conditions
            
            log_function_exit("get_fyers_api_status", "module_unavailable")
            return status_data
        
        # Check if trader is initialized with API credentials
        if not state_manager.trader:
            status_data["connection_status"] = "trader_not_initialized"
            status_data["error_details"] = "Trading bot not initialized. Please set API credentials and initialize."
            logger.warning("⚠️ Trading bot not initialized")
            
            # Cache this result but with shorter duration since trader can be initialized
            fyers_status_cache["data"] = status_data.copy()
            fyers_status_cache["last_update"] = current_time
            fyers_status_cache["cache_duration"] = 5  # Shorter cache for dynamic conditions
            
            log_function_exit("get_fyers_api_status", "trader_not_initialized")
            return status_data
        
        # Check if trader has Fyers API connection
        if not hasattr(state_manager.trader, 'fyers') or state_manager.trader.fyers is None:
            status_data["connection_status"] = "api_not_configured"
            status_data["error_details"] = "Fyers API not configured in trader. Check API credentials."
            logger.warning("⚠️ Fyers API not configured in trader")
            
            # Cache this result with shorter duration since API can be configured
            fyers_status_cache["data"] = status_data.copy()
            fyers_status_cache["last_update"] = current_time
            fyers_status_cache["cache_duration"] = 5
            
            log_function_exit("get_fyers_api_status", "api_not_configured")
            return status_data
        
        # Test API connection with a simple quote request
        logger.info("🧪 Testing Fyers API connection with quote request...")
        try:
            # Test with Nifty 50 index quote (safe and always available)
            test_symbol = "NSE:NIFTY50-INDEX"
            quote_data = {"symbols": test_symbol}
            
            start_time = time.time()
            quote_response = state_manager.trader.fyers.quotes(quote_data)
            response_time = round((time.time() - start_time) * 1000, 2)  # Convert to milliseconds
            
            logger.debug(f"Quote response: {quote_response}")
            
            # Check if response is successful
            if quote_response and isinstance(quote_response, dict):
                if quote_response.get('s') == 'ok' and quote_response.get('d'):
                    # Handle both dict and list response formats from Fyers API
                    data_section = quote_response.get('d', {})
                    current_price = 'N/A'
                    
                    # Debug: Log the actual response structure
                    logger.debug(f"API response data section type: {type(data_section)}")
                    logger.debug(f"API response data content: {data_section}")
                    
                    # Handle different response formats
                    if isinstance(data_section, dict):
                        # Standard dict format
                        symbol_data = data_section.get(test_symbol, {})
                        if isinstance(symbol_data, dict):
                            current_price = symbol_data.get('v', {}).get('lp', 'N/A')
                    elif isinstance(data_section, list) and len(data_section) > 0:
                        # List format - take first item
                        first_item = data_section[0]
                        if isinstance(first_item, dict):
                            current_price = first_item.get('v', {}).get('lp', 'N/A') if isinstance(first_item.get('v'), dict) else first_item.get('lp', 'N/A')
                    
                    status_data["connection_status"] = "connected"
                    status_data["test_results"] = {
                        "test_type": "quote_request",
                        "test_symbol": test_symbol,
                        "response_time_ms": response_time,
                        "success": True,
                        "data_received": True,
                        "api_response_status": quote_response.get('s'),
                        "current_price": current_price,
                        "response_format": f"data is {type(data_section).__name__}"
                    }
                    logger.info(f"✅ Fyers API connection successful! Response time: {response_time}ms, Price: {current_price}")
                else:
                    status_data["connection_status"] = "api_error"
                    status_data["error_details"] = f"API returned error: {quote_response.get('message', 'Unknown error')}"
                    status_data["test_results"] = {
                        "test_type": "quote_request",
                        "test_symbol": test_symbol,
                        "response_time_ms": response_time,
                        "success": False,
                        "api_response": quote_response
                    }
                    logger.error(f"❌ Fyers API error: {quote_response}")
            else:
                status_data["connection_status"] = "invalid_response"
                status_data["error_details"] = f"Invalid API response format: {type(quote_response)}"
                status_data["test_results"] = {
                    "test_type": "quote_request",
                    "test_symbol": test_symbol,
                    "response_time_ms": response_time,
                    "success": False,
                    "response_type": str(type(quote_response))
                }
                logger.error(f"❌ Invalid Fyers API response: {quote_response}")
                
        except Exception as api_error:
            status_data["connection_status"] = "connection_failed"
            status_data["error_details"] = f"API connection test failed: {str(api_error)}"
            status_data["test_results"] = {
                "test_type": "quote_request",
                "test_symbol": test_symbol,
                "success": False,
                "error": str(api_error)
            }
            logger.error(f"❌ Fyers API connection test failed: {api_error}")
        
        # Add additional context if trader is available
        if state_manager.trader:
            status_data["trader_info"] = {
                "client_id": getattr(state_manager.trader, 'client_id', 'Not set')[:8] + "..." if getattr(state_manager.trader, 'client_id', None) else 'Not set',
                "has_access_token": bool(getattr(state_manager.trader, 'access_token', None)),
                "simulation_mode": getattr(state_manager.trader, 'simulation_mode', True),
                "is_running": getattr(state_manager.trader, 'is_running', False)
            }
        
        # Cache the successful result
        fyers_status_cache["data"] = status_data.copy()
        fyers_status_cache["last_update"] = current_time
        fyers_status_cache["cache_duration"] = 10  # Reset to normal cache duration
        logger.debug(f"💾 Cached fresh Fyers status result: {status_data['connection_status']}")
        
        log_function_exit("get_fyers_api_status", status_data["connection_status"])
        return status_data
        
    except Exception as e:
        logger.error(f"❌ Error checking Fyers API status: {e}")
        logger.exception("Full error traceback:")
        log_function_exit("get_fyers_api_status", error=str(e))
        
        error_response = {
            "fyers_module_available": FYERS_AVAILABLE,
            "trader_initialized": state_manager.trader is not None,
            "connection_status": "status_check_failed",
            "last_test_time": current_time.isoformat(),
            "cached": False,
            "cache_age_seconds": 0,
            "error_details": f"Status check failed: {str(e)}",
            "test_results": {"error": str(e)}
        }
        
        # Cache error responses for a shorter duration (5 seconds) to prevent repeated failures
        fyers_status_cache["data"] = error_response.copy()
        fyers_status_cache["last_update"] = current_time
        fyers_status_cache["cache_duration"] = 5  # Shorter cache for errors
        logger.debug("💾 Cached error response for 5 seconds")
        
        return error_response

@app.get("/api/portfolio/lifetime")
async def get_lifetime_portfolio_stats():
    """Get lifetime portfolio statistics across all trading days"""
    log_function_entry("get_lifetime_portfolio_stats")
    try:
        logger.info(" Calculating lifetime portfolio statistics...")
        
        # Calculate lifetime stats
        lifetime_stats = state_manager.calculate_lifetime_portfolio_stats()
        
        # Add current day stats if trader is initialized
        current_day_stats = None
        if state_manager.trader:
            current_day_stats = {
                "date": datetime.now().strftime('%Y-%m-%d'),
                "total_pnl": state_manager.trader.trading_portfolio.get('total_pnl', 0),
                "total_trades": state_manager.trader.trading_portfolio.get('total_trades', 0),
                "winning_trades": state_manager.trader.trading_portfolio.get('winning_trades', 0),
                "losing_trades": state_manager.trader.trading_portfolio.get('losing_trades', 0),
                "win_rate": (state_manager.trader.trading_portfolio.get('winning_trades', 0) / 
                            max(1, state_manager.trader.trading_portfolio.get('total_trades', 1)) * 100),
                "max_profit_seen": state_manager.trader.trading_portfolio.get('max_profit_seen', 0),
                "max_loss_seen": state_manager.trader.trading_portfolio.get('max_loss_seen', 0)
            }
        
        response_data = {
            "status": "success",
            "lifetime_stats": lifetime_stats,
            "current_day": current_day_stats,
            "timestamp": datetime.now().isoformat()
        }
        
        logger.info(f" Lifetime stats calculated: {lifetime_stats.get('total_trading_days', 0)} days, "
                   f"Rs.{lifetime_stats.get('lifetime_total_pnl', 0)} total P&L")
        log_function_exit("get_lifetime_portfolio_stats", "success")
        return response_data
        
    except Exception as e:
        logger.error(f"❌ Error getting lifetime portfolio stats: {e}")
        log_function_exit("get_lifetime_portfolio_stats", error=str(e))
        return {
            "status": "error",
            "message": f"Error calculating lifetime stats: {str(e)}",
            "lifetime_stats": {
                "lifetime_total_pnl": 0,
                "lifetime_total_trades": 0,
                "total_trading_days": 0,
                "error": str(e)
            }
        }

# Configuration APIs

@app.post("/api/config/api-credentials")
async def set_api_credentials(credentials: APICredentials, current_user: str = Depends(verify_token)):
    """Create/update config.txt with API credentials"""
    log_function_entry("set_api_credentials", client_id=credentials.client_id[:8] + "...", redirect_uri=credentials.redirect_uri)
    try:
        logger.info(" Setting API credentials in config.txt")
        
        config_data = {
            "CLIENT_ID": credentials.client_id,
            "CLIENT_SECRET": credentials.client_secret,
            "REDIRECT_URI": credentials.redirect_uri
        }
        
        logger.debug(f" Writing config data: CLIENT_ID={credentials.client_id[:8]}..., REDIRECT_URI={credentials.redirect_uri}")
        
        with open('config.txt', 'w') as f:
            for key, value in config_data.items():
                f.write(f"{key}={value}\n")
        
        logger.info(" API credentials saved to config.txt successfully")
        log_function_exit("set_api_credentials", "success")
        return {"status": "success", "message": "API credentials saved successfully"}
        
    except Exception as e:
        logger.error(f"❌ Error saving API credentials to config.txt: {e}")
        log_function_exit("set_api_credentials", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error saving API credentials: {str(e)}")

@app.post("/api/config/access-token")
async def set_access_token(token: AccessTokenModel, current_user: str = Depends(verify_token)):
    """Create/update access.txt with access token and reload trader config"""
    log_function_entry("set_access_token", token_length=len(token.access_token))
    try:
        logger.info(" Setting access token in access.txt")
        
        with open('access.txt', 'w') as f:
            f.write(token.access_token)
        
        logger.info(f"✅ Access token saved to access.txt (length: {len(token.access_token)})")
        
        # Update the trader's access token immediately if trader is initialized
        if state_manager.trader:
            logger.info(" Updating trader's access token...")
            state_manager.trader.access_token = token.access_token
            
            # Reinitialize Fyers API with new token if we have client_id
            if hasattr(state_manager.trader, 'client_id') and state_manager.trader.client_id:
                try:
                    from fyers_apiv3 import fyersModel
                    state_manager.trader.fyers = fyersModel.FyersModel(
                        client_id=state_manager.trader.client_id,
                        token=token.access_token,
                        log_path=""
                    )
                    logger.info("✅ Fyers API reinitialized with new access token")
                except Exception as e:
                    logger.warning(f"⚠️ Could not reinitialize Fyers API: {e}")
            
            logger.info("✅ Trader access token updated - no restart required")
        else:
            logger.info(" No active trader to update - changes will take effect on next restart")
        
        log_function_exit("set_access_token", "success")
        return {
            "status": "success", 
            "message": "Access token saved and trader updated successfully" if state_manager.trader else "Access token saved successfully - restart required",
            "restart_required": state_manager.trader is None
        }
        
    except Exception as e:
        logger.error(f"❌ Error saving access token to access.txt: {e}")
        log_function_exit("set_access_token", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error saving access token: {str(e)}")

@app.post("/api/config/reload-trader")
async def reload_trader_config(current_user: str = Depends(verify_token)):
    """Reload trader configuration from files without restarting server"""
    log_function_entry("reload_trader_config")
    try:
        if not state_manager.trader:
            logger.warning("❌ No trader to reload - please restart server")
            raise HTTPException(status_code=400, detail="No trader initialized - server restart required")
        
        logger.info(" Reloading trader configuration...")
        
        # Reload the UI config which loads all the files
        config = state_manager.trader._load_ui_config()
        
        # Update trader with new config
        if 'access_token' in config:
            state_manager.trader.access_token = config['access_token']
            logger.info("✅ Access token reloaded")
        
        if 'client_id' in config:
            state_manager.trader.client_id = config['client_id']
            logger.info("✅ Client ID reloaded")
        
        # Reinitialize Fyers API if we have both client_id and access_token
        if hasattr(state_manager.trader, 'client_id') and hasattr(state_manager.trader, 'access_token') and state_manager.trader.client_id and state_manager.trader.access_token:
            try:
                from fyers_apiv3 import fyersModel
                state_manager.trader.fyers = fyersModel.FyersModel(
                    client_id=state_manager.trader.client_id,
                    token=state_manager.trader.access_token,
                    log_path=""
                )
                logger.info("✅ Fyers API reinitialized with reloaded credentials")
            except Exception as e:
                logger.warning(f"⚠️ Could not reinitialize Fyers API: {e}")
        
        logger.info("✅ Trader configuration reloaded successfully")
        log_function_exit("reload_trader_config", "success")
        return {
            "status": "success", 
            "message": "Trader configuration reloaded successfully",
            "has_fyers_api": hasattr(state_manager.trader, 'fyers') and state_manager.trader.fyers is not None
        }
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"❌ Error reloading trader config: {e}")
        log_function_exit("reload_trader_config", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error reloading trader config: {str(e)}")

@app.post("/api/config/vwap-override")
async def set_vwap_override(vwap: VWAPOverrideModel, current_user: str = Depends(verify_token)):
    """Create/update vwap_override.txt"""
    log_function_entry("set_vwap_override", vwap_value=vwap.vwap)
    try:
        if vwap.vwap is None:
            # Clear override
            logger.info(" Clearing VWAP override")
            if os.path.exists('vwap_override.txt'):
                os.remove('vwap_override.txt')
                logger.debug(" vwap_override.txt file removed")
            
            if state_manager.trader:
                state_manager.trader.vwap_override_enabled = False
                state_manager.trader.vwap_override_value = None
                
                # 🔓 AUTO-UNFREEZE instruments when VWAP override is cleared via UI
                state_manager.trader.instrument_freeze_enabled = False
                state_manager.trader.frozen_ce_symbol = None
                state_manager.trader.frozen_pe_symbol = None
                logger.info(" Auto-unfrozen instruments via UI")
                
                logger.debug(" Trader VWAP override disabled")
            
            logger.info(" VWAP override cleared successfully")
            log_function_exit("set_vwap_override", "cleared")
            return {"status": "success", "message": "VWAP override cleared"}
        else:
            # Set override
            logger.info(f"🎯 Setting VWAP override to {vwap.vwap}")
            
            try:
                # Get current working directory for debugging
                current_dir = os.getcwd()
                file_path = os.path.join(current_dir, 'vwap_override.txt')
                logger.debug(f" Working directory: {current_dir}")
                logger.debug(f" Full file path: {file_path}")
                
                with open('vwap_override.txt', 'w') as f:
                    f.write(str(vwap.vwap))
                logger.debug(f" VWAP override written to file: {vwap.vwap}")
                
                # Verify file was created
                if os.path.exists('vwap_override.txt'):
                    with open('vwap_override.txt', 'r') as f:
                        file_content = f.read().strip()
                    logger.debug(f" File verification: exists=True, content='{file_content}'")
                else:
                    logger.error(" File verification: vwap_override.txt not found after writing!")
                
            except Exception as file_error:
                logger.error(f"❌ Error writing VWAP override file: {file_error}")
                raise file_error
            
            if state_manager.trader:
                state_manager.trader.vwap_override_enabled = True
                state_manager.trader.vwap_override_value = vwap.vwap
                
                # 🔒 AUTO-FREEZE instruments when VWAP override is set via UI
                if not state_manager.trader.instrument_freeze_enabled and hasattr(state_manager.trader, 'combined_premium_data') and state_manager.trader.combined_premium_data:
                    latest_data = state_manager.trader.combined_premium_data[-1]
                    state_manager.trader.frozen_ce_symbol = latest_data.get('ce_tradingsymbol')
                    state_manager.trader.frozen_pe_symbol = latest_data.get('pe_tradingsymbol')
                    state_manager.trader.instrument_freeze_enabled = True
                    logger.info(f"Auto-frozen instruments via UI: CE={state_manager.trader.frozen_ce_symbol}, PE={state_manager.trader.frozen_pe_symbol}")
                
                logger.debug(f" Trader VWAP override enabled: {vwap.vwap}")
            
            logger.info(f"VWAP override set to {vwap.vwap}")
            log_function_exit("set_vwap_override", "success", f"value={vwap.vwap}")
            return {"status": "success", "message": f"VWAP override set to {vwap.vwap}"}
            
    except Exception as e:
        logger.error(f"❌ Error setting VWAP override: {e}")
        log_function_exit("set_vwap_override", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error setting VWAP override: {str(e)}")

@app.post("/api/vwap-override/reset-cycle")
async def reset_vwap_override_cycle(current_user: str = Depends(verify_token)):
    """Reset VWAP override cycle to allow new orders"""
    log_function_entry("reset_vwap_override_cycle")
    try:
        logger.info("🔄 Resetting VWAP override cycle")
        
        if not state_manager.trader:
            log_function_exit("reset_vwap_override_cycle", error="No trader instance")
            raise HTTPException(status_code=400, detail="No trader instance available")
        
        result = state_manager.trader.reset_vwap_override_cycle()
        
        if result["success"]:
            logger.info(f"✅ {result['message']}")
            log_function_exit("reset_vwap_override_cycle", "success")
            return {"status": "success", "message": result["message"]}
        else:
            logger.warning(f"⚠️ {result['message']}")
            log_function_exit("reset_vwap_override_cycle", "failed", result["message"])
            raise HTTPException(status_code=400, detail=result["message"])
            
    except HTTPException:
        raise  # Re-raise HTTP exceptions
    except Exception as e:
        logger.error(f"❌ Error resetting VWAP override cycle: {e}")
        log_function_exit("reset_vwap_override_cycle", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error resetting VWAP override cycle: {str(e)}")

@app.post("/api/config/expiry-override")
async def set_expiry_override(expiry: ExpiryOverrideModel, current_user: str = Depends(verify_token)):
    """Create/update expiry_override.txt"""
    log_function_entry("set_expiry_override", expiry_date=expiry.date)
    try:
        logger.info(f"📅 Setting expiry override to {expiry.date}")
        
        with open('expiry_override.txt', 'w') as f:
            f.write(expiry.date)
        
        logger.info(f"✅ Expiry override set to {expiry.date}")
        log_function_exit("set_expiry_override", "success", f"date={expiry.date}")
        return {"status": "success", "message": f"Expiry override set to {expiry.date}"}
        
    except Exception as e:
        logger.error(f"❌ Error setting expiry override: {e}")
        log_function_exit("set_expiry_override", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error setting expiry override: {str(e)}")

@app.get("/api/config/current-values")
async def get_current_config_values(current_user: str = Depends(verify_token)):
    """Get current values from config files"""
    log_function_entry("get_current_config_values")
    try:
        logger.info(" Reading current configuration values from files")
        
        result = {
            "api_config": {},
            "access_token": None,
            "vwap_override": None, 
            "expiry_override": None
        }
        
        # Read config.txt
        if os.path.exists('config.txt'):
            logger.debug(" Reading config.txt")
            with open('config.txt', 'r') as f:
                for line_num, line in enumerate(f, 1):
                    if '=' in line:
                        key, value = line.strip().split('=', 1)
                        result["api_config"][key] = value
                        logger.debug(f" Config line {line_num}: {key}={value[:8]}..." if key == "CLIENT_SECRET" else f" Config line {line_num}: {key}={value}")
            logger.debug(f" Config.txt loaded: {len(result['api_config'])} entries")
        else:
            logger.debug(" config.txt not found")
        
        # Read access.txt
        if os.path.exists('access.txt'):
            logger.debug(" Reading access.txt")
            with open('access.txt', 'r') as f:
                result["access_token"] = f.read().strip()
            logger.debug(f" Access token loaded: length {len(result['access_token'])}")
        else:
            logger.debug(" access.txt not found")
        
        # Read vwap_override.txt
        if os.path.exists('vwap_override.txt'):
            logger.debug(" Reading vwap_override.txt")
            with open('vwap_override.txt', 'r') as f:
                try:
                    result["vwap_override"] = float(f.read().strip())
                    logger.debug(f" VWAP override loaded: {result['vwap_override']}")
                except ValueError as ve:
                    logger.warning(f"⚠️ Invalid VWAP override value: {ve}")
                    result["vwap_override"] = None
        else:
            logger.debug(" vwap_override.txt not found")
        
        # Read expiry_override.txt
        if os.path.exists('expiry_override.txt'):
            logger.debug(" Reading expiry_override.txt")
            with open('expiry_override.txt', 'r') as f:
                result["expiry_override"] = f.read().strip()
            logger.debug(f" Expiry override loaded: {result['expiry_override']}")
        else:
            logger.debug(" expiry_override.txt not found")
        
        # Also include current app state information if available
        app_state_data = state_manager.load_state()
        if app_state_data:
            result["app_state"] = {
                "file": state_manager.app_state_file,
                "timestamp": app_state_data.get("timestamp"),
                "trader_initialized": app_state_data.get("trader_initialized", False),
                "is_trading_active": app_state_data.get("is_trading_active", False),
                "simulation_mode": app_state_data.get("simulation_mode", True),
                "current_nifty_price": app_state_data.get("current_nifty_price"),
                "current_atm_strike": app_state_data.get("current_atm_strike"),
                "has_positions": any(pos for pos in app_state_data.get("positions", {}).values() if pos)
            }
            logger.debug(f" App state information included from {state_manager.app_state_file}")
        else:
            result["app_state"] = {"file": state_manager.app_state_file, "available": False}
        
        logger.info(f"Configuration values loaded successfully")
        log_function_exit("get_current_config_values", "success", f"config_keys={len(result['api_config'])}")
        return result
        
    except Exception as e:
        logger.error(f"❌ Error reading configuration values: {e}")
        log_function_exit("get_current_config_values", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error reading config values: {str(e)}")

# Trading Control APIs

@app.post("/api/trading/initialize")
async def initialize_trading(current_user: str = Depends(verify_token)):
    """Initialize the trading bot"""
    log_function_entry("initialize_trading")
    try:
        logger.info(" Starting trading bot initialization...")
        
        # ✅ VALIDATION: Check if expiry date is configured
        expiry_configured, expiry_message = check_expiry_date_configured()
        if not expiry_configured:
            error_msg = f"❌ Cannot initialize trader: Options expiry date/token must be set first. {expiry_message}"
            logger.error(error_msg)
            log_function_exit("initialize_trading", "expiry_not_configured")
            raise HTTPException(status_code=400, detail=error_msg)
        
        logger.info(f"✅ Expiry configuration validation passed: {expiry_message}")
        
        if state_manager.trader:
            logger.warning(" Trading bot already initialized - skipping initialization")
            log_function_exit("initialize_trading", "already_initialized")
            return {"status": "success", "message": "Trading bot already initialized"}
        
        # Load credentials
        logger.debug(" Loading API credentials...")
        credentials = load_credentials()
        logger.debug(f" Credentials loaded: CLIENT_ID={credentials.get('CLIENT_ID', 'None')[:8]}...")
        
        # Initialize trader with UI auto-config loading enabled
        logger.info(" Creating NiftyOptionsTrader instance with auto-config loading...")
        trader = NiftyOptionsTrader(auto_load_config=True)
        state_manager.trader = trader
        logger.info(" Trading bot instance created successfully")
        
        # Set up status change callback for immediate WebSocket broadcasts
        def status_change_callback(change_type):
            """Callback to trigger immediate status broadcast when critical state changes"""
            if state_manager.websocket_clients:
                try:
                    logger.info(f"🔔 Triggering immediate status broadcast for: {change_type}")
                    # Create a coroutine to broadcast the status change
                    async def broadcast_status_change():
                        await state_manager.broadcast_to_websockets({
                            "type": "status_change", 
                            "change_type": change_type,
                            "timestamp": datetime.now().isoformat(),
                            "message": f"Status change: {change_type}"
                        })
                    
                    # Schedule the coroutine to run in the event loop
                    try:
                        loop = asyncio.get_event_loop()
                        if loop.is_running():
                            asyncio.create_task(broadcast_status_change())
                        else:
                            loop.run_until_complete(broadcast_status_change())
                    except RuntimeError:
                        # If no event loop is running, create a new one
                        asyncio.run(broadcast_status_change())
                        
                except Exception as e:
                    logger.error(f"Failed to broadcast status change: {e}")
        
        # Assign callback to trader
        trader.status_change_callback = status_change_callback
        
        # 🔧 IMPROVED: Only restore portfolio data if it's from today
        logger.info(" Loading saved state data with daily reset logic...")
        try:
            # Try to load from today's date-specific state file only
            today_state_file = f'app_state_{datetime.now().strftime("%Y%m%d")}.json'
            
            if os.path.exists(today_state_file):
                logger.debug(f" Loading data from today's state file: {today_state_file}")
                with open(today_state_file, 'r') as f:
                    saved_state = json.load(f)
                
                # Restore trading portfolio only if it's from today
                saved_portfolio = saved_state.get('trading_portfolio', {})
                # Backward compatibility: check for old virtual_portfolio key
                if not saved_portfolio:
                    saved_portfolio = saved_state.get('virtual_portfolio', {})
                    if saved_portfolio:
                        logger.info(" Found legacy virtual_portfolio data, migrating to trading_portfolio")
                
                if saved_portfolio:
                    trader.trading_portfolio.update(saved_portfolio)
                    logger.info(f"✅ Restored TODAY's trading portfolio: PnL={saved_portfolio.get('total_pnl', 0)}, Trades={saved_portfolio.get('total_trades', 0)}")
                else:
                    logger.debug(" No portfolio data found in today's state file")
                
                # Restore market data
                if saved_state.get('current_nifty_price'):
                    trader.current_nifty_price = saved_state.get('current_nifty_price')
                    logger.debug(f" Restored Nifty price: {trader.current_nifty_price}")
                if saved_state.get('current_atm_strike'):
                    trader.current_atm_strike = saved_state.get('current_atm_strike')
                    logger.debug(f" Restored ATM strike: {trader.current_atm_strike}")
                if saved_state.get('current_vwap'):
                    trader.current_vwap = saved_state.get('current_vwap')
                    logger.debug(f" Restored VWAP: {trader.current_vwap}")
                
                logger.info(" ✅ Today's state restoration completed - fresh start for new trading day")
            else:
                logger.info(f" No state file found for today ({today_state_file}) - starting with fresh portfolio for new trading day")
        
        except Exception as restore_error:
            logger.warning(f"⚠️ Could not restore saved state: {restore_error} - starting fresh")
        
        # Fetch initial data to populate the dashboard
        logger.info(" Fetching initial market data...")
        try:
            # Get initial Nifty price (only if not already restored)
            if not trader.current_nifty_price:
                logger.debug(" Fetching current Nifty price...")
                nifty_price = trader.get_nifty_price()
                
                # Only set Nifty price - ATM strike management is delegated to trading engine
                if nifty_price:
                    trader.current_nifty_price = nifty_price
                    logger.info(f"Initial data fetched: Nifty={nifty_price:.2f}, ATM will be managed by trading engine")
                else:
                    logger.warning(" Could not fetch Nifty price - keeping as None")
            else:
                logger.debug(f" Using restored Nifty price: {trader.current_nifty_price}")
            
            # Try to calculate initial VWAP (only if not already restored)
            if not trader.current_vwap and hasattr(trader, 'calculate_vwap'):
                try:
                    logger.debug(" Calculating initial VWAP...")
                    vwap = trader.calculate_vwap()
                    if vwap:
                        trader.current_vwap = vwap
                        logger.info(f"📊 Initial VWAP calculated: {vwap:.2f}")
                    else:
                        logger.debug(" VWAP calculation returned None")
                except Exception as vwap_error:
                    logger.warning(f"⚠️ Could not calculate initial VWAP: {vwap_error}")
            else:
                logger.debug(f" Using restored VWAP: {trader.current_vwap}")
            
        except Exception as data_error:
            logger.warning(f"⚠️ Could not fetch initial market data: {data_error}")
            logger.debug(" Keeping market data as None - no fake data will be generated")
        
        # Log final state
        has_positions = trader.positions.get('CE') is not None or trader.positions.get('PE') is not None
        log_trader_state(trader, "initialization_complete")
        
        logger.info(f" Trading bot initialized successfully. "
                   f"Nifty: {trader.current_nifty_price}, "
                   f"ATM: {trader.current_atm_strike}, "
                   f"VWAP: {trader.current_vwap}, "
                   f"Positions: {has_positions}")
        
        # Save app state immediately after initialization
        state_manager.save_current_state()
        logger.debug(" App state saved after trading initialization")
        
        result = {
            "status": "success", 
            "message": f"Trading bot initialized successfully",
            "nifty_price": trader.current_nifty_price,
            "atm_strike": trader.current_atm_strike,
            "current_vwap": trader.current_vwap,
            "simulation_mode": trader.simulation_mode,
            "fyers_available": FYERS_AVAILABLE,
            "positions_restored": has_positions,
            "ce_position": trader.positions.get('CE') is not None,
            "pe_position": trader.positions.get('PE') is not None
        }
        
        log_function_exit("initialize_trading", "success", f"nifty={trader.current_nifty_price}, positions={has_positions}")
        return result
        
    except Exception as e:
        error_msg = f"Error initializing trader: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception("Full initialization error traceback:")
        log_function_exit("initialize_trading", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/refresh-data")
async def refresh_market_data(current_user: str = Depends(verify_token)):
    """Refresh market data (Nifty price, ATM strike, VWAP)"""
    log_function_entry("refresh_market_data")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot refresh data - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        trader = state_manager.trader
        logger.info(" Starting market data refresh...")
        log_trader_state(trader, "before_refresh")
        
        # Fetch current Nifty price
        # Note: ATM strike management is handled by the trading engine (fyers_vwap_9_1.py)
        # We only update Nifty price here - the trading engine will update ATM as needed
        logger.debug(" Fetching current Nifty price...")
        try:
            nifty_price = trader.get_nifty_price()
            if nifty_price:
                trader.current_nifty_price = nifty_price
                logger.info(f"📊 Market data refreshed: Nifty={nifty_price:.2f}, ATM={trader.current_atm_strike}")
            else:
                logger.warning(" Could not fetch Nifty price - keeping existing value")
        except Exception as e:
            logger.error(f"❌ Error fetching Nifty price: {e}")
        
        # Try to recalculate VWAP
        logger.debug(" Recalculating VWAP...")
        try:
            if hasattr(trader, 'calculate_vwap'):
                vwap = trader.calculate_vwap()
                if vwap:
                    trader.current_vwap = vwap
                    logger.info(f"📊 VWAP recalculated: {vwap:.2f}")
                else:
                    logger.debug(" VWAP calculation returned None")
            else:
                logger.warning(" Trader does not have calculate_vwap method")
        except Exception as e:
            logger.warning(f"⚠️ Could not recalculate VWAP: {e}")
        
        # Get current options data if positions exist
        positions_updated = False
        logger.debug(" Checking if options data needs refresh...")
        if trader.current_atm_strike:
            try:
                if hasattr(trader, 'get_options_data'):
                    logger.debug(f" Fetching options data for ATM strike {trader.current_atm_strike}...")
                    options_data = trader.get_options_data(trader.current_atm_strike)
                    if options_data:
                        logger.info(" Options data refreshed successfully")
                        positions_updated = True
                    else:
                        logger.debug(" Options data fetch returned None")
                else:
                    logger.warning(" Trader does not have get_options_data method")
            except Exception as e:
                logger.warning(f"⚠️ Could not refresh options data: {e}")
        else:
            logger.debug(" No ATM strike available - skipping options data refresh")
        
        log_trader_state(trader, "after_refresh")
        
        result = {
            "status": "success",
            "message": "Market data refreshed successfully",
            "nifty_price": trader.current_nifty_price,
            "atm_strike": trader.current_atm_strike,
            "current_vwap": trader.current_vwap,
            "positions_updated": positions_updated,
            "timestamp": datetime.now().isoformat()
        }
        
        logger.info(f"✅ Market data refresh completed: Nifty={trader.current_nifty_price}, VWAP={trader.current_vwap}")
        log_function_exit("refresh_market_data", "success", f"nifty={trader.current_nifty_price}")
        return result
        
    except HTTPException:
        raise
    except Exception as e:
        error_msg = f"Error refreshing market data: {str(e)}"
        logger.error(f"❌ {error_msg}")
        log_function_exit("refresh_market_data", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/start")
async def start_trading(current_user: str = Depends(verify_token)):
    """Start the trading bot"""
    log_function_entry("start_trading")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot start trading - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        if state_manager.is_trading_active:
            logger.warning(" Trading already active - ignoring start request")
            log_function_exit("start_trading", "already_active")
            return {"status": "success", "message": "Trading already active"}
        
        logger.info(" Starting trading bot...")
        log_trader_state(state_manager.trader, "before_start")
        
        # Start trading in background thread
        state_manager.start_trading_thread()
        
        # Save app state immediately after starting trading
        state_manager.save_current_state()
        logger.debug(" App state saved after trading start")
        
        logger.info(" Trading started successfully via Web UI")
        log_function_exit("start_trading", "success")
        return {"status": "success", "message": "Trading started successfully"}
        
    except Exception as e:
        logger.error(f"❌ Error starting trading: {e}")
        log_function_exit("start_trading", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error starting trading: {str(e)}")

@app.post("/api/trading/stop")
async def stop_trading(current_user: str = Depends(verify_token)):
    """Stop the trading bot"""
    log_function_entry("stop_trading")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot stop trading - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        logger.info(" Stopping trading bot...")
        log_trader_state(state_manager.trader, "before_stop")
        
        state_manager.stop_trading()
        
        logger.info(" Trading stopped successfully via Web UI")
        log_function_exit("stop_trading", "success")
        return {"status": "success", "message": "Trading stopped successfully"}
        
    except Exception as e:
        logger.error(f"❌ Error stopping trading: {e}")
        log_function_exit("stop_trading", error=str(e))
        raise HTTPException(status_code=500, detail=f"Error stopping trading: {str(e)}")

@app.post("/api/trading/emergency-stop")
async def emergency_stop_trading(current_user: str = Depends(verify_token)):
    """Emergency stop: Stop trading AND square off all positions"""
    log_function_entry("emergency_stop_trading")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot emergency stop - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        logger.info("🚨 EMERGENCY STOP INITIATED - Stopping trading and squaring off all positions...")
        log_trader_state(state_manager.trader, "before_emergency_stop")
        
        # Step 1: Stop all trading to prevent new orders
        logger.info("🛑 Step 1: Stopping trading bot...")
        state_manager.stop_trading()
        
        # Step 2: Square off all positions (both short and long)
        logger.info("🔄 Step 2: Squaring off all positions...")
        
        # Check if we have any positions to square off
        positions_to_square = []
        
        # Check short positions
        for option_type in ["CE", "PE"]:
            position = state_manager.trader.positions.get(option_type)
            if (position is not None and position != {} and isinstance(position, dict) and 
                (position.get('quantity', 0) != 0 or 
                 (position.get('strike') is not None and position.get('entry_price') is not None))):
                positions_to_square.append(f"Short {option_type}")
        
        # Check long positions  
        for option_type in ["CE", "PE"]:
            long_position = state_manager.trader.long_positions.get(option_type)
            if (long_position is not None and long_position != {} and isinstance(long_position, dict) and
                (long_position.get('quantity', 0) != 0 or
                 (long_position.get('strike') is not None and long_position.get('entry_price') is not None))):
                positions_to_square.append(f"Long {option_type}")
        
        if not positions_to_square:
            logger.info("✅ No positions found to square off")
            log_function_exit("emergency_stop_trading", "no_positions")
            return {"status": "success", "message": "Emergency stop completed - No positions to square off"}
        
        logger.info(f"📋 Found positions to square off: {positions_to_square}")
        
        # Perform emergency square off
        try:
            result = state_manager.trader.square_off_all_positions()
            logger.info("✅ All positions squared off successfully during emergency stop")
            log_trader_state(state_manager.trader, "after_emergency_stop")
            
            # Save app state immediately
            state_manager.save_current_state()
            logger.debug("💾 App state saved after emergency stop")
            
            message = f"Emergency stop completed successfully - Trading stopped and {len(positions_to_square)} positions squared off"
            logger.info(f"🚨 {message}")
            
            log_function_exit("emergency_stop_trading", "success", f"squared_off={len(positions_to_square)}")
            return {"status": "success", "message": message, "positions_squared": positions_to_square}
            
        except Exception as square_off_error:
            logger.error(f"❌ Error during emergency square off: {square_off_error}")
            logger.exception("Full emergency square off error traceback:")
            raise square_off_error
        
    except HTTPException:
        raise
    except Exception as e:
        error_msg = f"Error during emergency stop: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception("Full emergency stop error traceback:")
        log_function_exit("emergency_stop_trading", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/reset-disabled-state")
async def reset_trading_disabled_state(current_user: str = Depends(verify_token)):
    """Reset trading disabled state after fixing issues (e.g., margin problems)"""
    log_function_entry("reset_trading_disabled_state")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot reset trading state - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        # Get current status
        safety_status = state_manager.trader.get_trading_safety_status()
        
        if not safety_status["trading_disabled"]:
            logger.info("ℹ️ Trading was not disabled")
            log_function_exit("reset_trading_disabled_state", "not_disabled")
            return {"status": "success", "message": "Trading was not disabled"}
        
        # Reset the disabled state
        reset_success = state_manager.trader.reset_trading_disabled_state()
        
        if reset_success:
            logger.info("✅ Trading disabled state reset successfully")
            log_function_exit("reset_trading_disabled_state", "success")
            return {
                "status": "success", 
                "message": "Trading disabled state reset successfully. You can now start trading again.",
                "previous_reason": safety_status["trading_disabled_reason"]
            }
        else:
            logger.error("❌ Failed to reset trading disabled state")
            log_function_exit("reset_trading_disabled_state", "failed")
            return {"status": "error", "message": "Failed to reset trading disabled state"}
            
    except Exception as e:
        error_msg = f"Error resetting trading disabled state: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception("Full reset disabled state error traceback:")
        log_function_exit("reset_trading_disabled_state", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/reset-all-blocks")
async def reset_all_trading_blocks(current_user: str = Depends(verify_token)):
    """Consolidated reset for both trading disabled state and VWAP override cycle"""
    log_function_entry("reset_all_trading_blocks")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot reset trading blocks - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        logger.info("🔄 Starting consolidated reset of all trading blocks...")
        
        # Perform consolidated reset
        result = state_manager.trader.reset_all_trading_blocks()
        
        if result["overall_success"]:
            logger.info("✅ Consolidated trading reset completed successfully")
            log_function_exit("reset_all_trading_blocks", "success")
            return {
                "status": "success",
                "message": result["message"],
                "details": {
                    "trading_disabled_reset": result["trading_disabled_reset"],
                    "vwap_cycle_reset": result["vwap_cycle_reset"]
                }
            }
        else:
            logger.error(f"❌ Consolidated trading reset failed: {result['message']}")
            log_function_exit("reset_all_trading_blocks", "failed")
            return {
                "status": "partial_success" if any([
                    result["trading_disabled_reset"]["success"], 
                    result["vwap_cycle_reset"]["success"]
                ]) else "error",
                "message": result["message"],
                "details": {
                    "trading_disabled_reset": result["trading_disabled_reset"],
                    "vwap_cycle_reset": result["vwap_cycle_reset"]
                }
            }
            
    except Exception as e:
        error_msg = f"Error in consolidated trading reset: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception("Full consolidated reset error traceback:")
        log_function_exit("reset_all_trading_blocks", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/square-off/{option_type}")
async def square_off_position(option_type: str, current_user: str = Depends(verify_token)):
    """Square off specific position (CE or PE)"""
    log_function_entry("square_off_position", option_type=option_type)
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot square off position - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        if option_type not in ["CE", "PE", 'ce', 'pe']:
            logger.error(f"❌ Invalid option type: {option_type}. Must be 'CE' or 'PE'")
            raise HTTPException(status_code=400, detail="Invalid option type. Use 'CE' or 'PE'")
        
        logger.info(f" Starting square off for {option_type} position...")
        log_trader_state(state_manager.trader, f"before_square_off_{option_type}")
        
        # Normalize option_type to uppercase for position lookup
        option_type_key = option_type.upper()
        
        # Check if position exists before squaring off
        current_position = state_manager.trader.positions.get(option_type_key)
        logger.debug(f" Raw position data for {option_type_key}: {current_position}")
        
        # More robust position existence check - handle both quantity-based and strike/price-based positions
        has_position = (current_position is not None and 
                       current_position != {} and 
                       isinstance(current_position, dict) and 
                       (current_position.get('quantity', 0) != 0 or  # For positions with quantity field
                        (current_position.get('strike') is not None and current_position.get('entry_price') is not None)))  # For positions with strike/price data
        
        if not has_position:
            logger.warning(f"No {option_type_key} position found to square off. Position data: {current_position}")
            log_function_exit("square_off_position", "no_position", f"{option_type_key}={current_position}")
            return {"status": "success", "message": f"No {option_type_key} position to square off"}
        
        logger.debug(f" Current {option_type_key} position exists: {current_position}")
        
        # Perform square off
        try:
            result = state_manager.trader.square_off_position(option_type_key)
            logger.info(f"✅ {option_type_key} position squared off successfully")
            log_trader_state(state_manager.trader, f"after_square_off_{option_type_key}")
            
            # NOTE: No state saving needed - positions are managed entirely by trader object
            
            log_function_exit("square_off_position", "success", f"{option_type_key}_squared_off")
            return {"status": "success", "message": f"{option_type_key} position squared off"}
        except Exception as square_off_error:
            logger.error(f"❌ Error during {option_type} square off operation: {square_off_error}")
            logger.exception(f"Full {option_type} square off error traceback:")
            raise square_off_error
        
    except HTTPException:
        raise
    except Exception as e:
        error_msg = f"Error squaring off {option_type} position: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception(f"Full {option_type} square off error traceback:")
        log_function_exit("square_off_position", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/square-off-long/{option_type}")
async def square_off_long_position(option_type: str, current_user: str = Depends(verify_token)):
    """Square off specific long position (CE or PE)"""
    log_function_entry("square_off_long_position", option_type=option_type)
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot square off long position - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        if option_type not in ["CE", "PE", 'ce', 'pe']:
            logger.error(f"❌ Invalid option type: {option_type}. Must be 'CE' or 'PE'")
            raise HTTPException(status_code=400, detail="Invalid option type. Use 'CE' or 'PE'")
        
        # Normalize option_type to uppercase
        option_type_key = option_type.upper()
        
        logger.info(f" Starting square off for {option_type_key} long position...")
        
        # Check if long position exists
        current_long_position = state_manager.trader.long_positions.get(option_type_key)
        logger.debug(f" Raw long position data for {option_type_key}: {current_long_position}")
        
        if not current_long_position:
            logger.warning(f"No {option_type_key} long position found to square off")
            return {"status": "success", "message": f"No {option_type_key} long position to square off"}
        
        logger.debug(f" Current {option_type_key} long position exists: {current_long_position}")
        
        # Perform square off using the existing method with UI Manual Exit reason
        try:
            result = state_manager.trader.square_off_long_position(option_type_key, "UI Manual Exit")
            logger.info(f"✅ {option_type_key} long position squared off successfully")
            
            log_function_exit("square_off_long_position", "success", f"{option_type_key}_long_squared_off")
            return {"status": "success", "message": f"{option_type_key} long position squared off"}
        except Exception as square_off_error:
            logger.error(f"❌ Error during {option_type} long square off operation: {square_off_error}")
            logger.exception(f"Full {option_type} long square off error traceback:")
            raise square_off_error
        
    except HTTPException:
        raise
    except Exception as e:
        error_msg = f"Error squaring off {option_type} long position: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception(f"Full {option_type} long square off error traceback:")
        log_function_exit("square_off_long_position", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/square-off-all")
async def square_off_all_positions(current_user: str = Depends(verify_token)):
    """Square off all positions including both regular and long positions"""
    log_function_entry("square_off_all_positions")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot square off positions - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        logger.info("🔄 Starting square off for ALL positions (regular + long)...")
        log_trader_state(state_manager.trader, "before_square_off_all")
        
        # Check current positions before squaring off
        ce_position = state_manager.trader.positions.get('CE')
        pe_position = state_manager.trader.positions.get('PE')
        ce_long_position = state_manager.trader.long_positions.get('CE')
        pe_long_position = state_manager.trader.long_positions.get('PE')
        
        logger.debug(f"🔍 Current positions before square off:")
        logger.debug(f"   Regular: CE={ce_position is not None}, PE={pe_position is not None}")
        logger.debug(f"   Long: CE={ce_long_position is not None}, PE={pe_long_position is not None}")
        
        # Count positions to square off
        positions_to_square = []
        if ce_position is not None:
            positions_to_square.append("CE")
        if pe_position is not None:
            positions_to_square.append("PE")
        if ce_long_position is not None:
            positions_to_square.append("CE Long")
        if pe_long_position is not None:
            positions_to_square.append("PE Long")
        
        if not positions_to_square:
            logger.warning("⚠️ No positions found to square off")
            log_function_exit("square_off_all_positions", "no_positions")
            return {
                "status": "success", 
                "message": "No positions to square off",
                "positions_squared": []
            }
        
        # Perform square off all
        try:
            result = state_manager.trader.square_off_all_positions()
            logger.info(f"✅ All positions squared off successfully: {', '.join(positions_to_square)}")
            log_trader_state(state_manager.trader, "after_square_off_all")
            
            # Save app state immediately after square off all
            state_manager.save_current_state()
            logger.debug(" App state saved after square off all")
            
            # Log the result if it contains useful information
            if result and isinstance(result, dict):
                logger.debug(f" Square off all result: {result}")
            
            log_function_exit("square_off_all_positions", "success", f"squared_off={len(positions_to_square)}")
            return {
                "status": "success", 
                "message": f"All positions squared off: {', '.join(positions_to_square)}",
                "positions_squared": positions_to_square,
                "count": len(positions_to_square)
            }
        except Exception as square_off_error:
            logger.error(f"❌ Error during square off all operation: {square_off_error}")
            logger.exception("Full square off all error traceback:")
            raise square_off_error
        
    except HTTPException:
        raise
    except Exception as e:
        error_msg = f"Error squaring off all positions: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception("Full square off all error traceback:")
        log_function_exit("square_off_all_positions", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

@app.post("/api/trading/square-off-all-reset-vwap")
async def square_off_all_and_reset_vwap(current_user: str = Depends(verify_token)):
    """Square off all positions (regular + long) and reset VWAP override to 0"""
    log_function_entry("square_off_all_and_reset_vwap")
    try:
        if not state_manager.trader:
            logger.error("❌ Cannot perform operations - trading bot not initialized")
            raise HTTPException(status_code=400, detail="Trading bot not initialized")
        
        logger.info("🔄 Starting Square Off All + Reset VWAP operation...")
        
        # Step 1: Square off all positions (including long positions)
        logger.info("Step 1: Squaring off ALL positions (regular + long)...")
        log_trader_state(state_manager.trader, "before_square_off_all_reset")
        
        # Check current positions before squaring off
        ce_position = state_manager.trader.positions.get('CE')
        pe_position = state_manager.trader.positions.get('PE')
        ce_long_position = state_manager.trader.long_positions.get('CE')
        pe_long_position = state_manager.trader.long_positions.get('PE')
        
        logger.debug(f"🔍 Current positions before square off:")
        logger.debug(f"   Regular: CE={ce_position is not None}, PE={pe_position is not None}")
        logger.debug(f"   Long: CE={ce_long_position is not None}, PE={pe_long_position is not None}")
        
        # Count positions to square off
        positions_to_square = []
        if ce_position is not None:
            positions_to_square.append("CE")
        if pe_position is not None:
            positions_to_square.append("PE")
        if ce_long_position is not None:
            positions_to_square.append("CE Long")
        if pe_long_position is not None:
            positions_to_square.append("PE Long")
        
        square_off_message = ""
        if not positions_to_square:
            logger.warning("⚠️ No positions found to square off")
            square_off_message = "No positions to square off"
        else:
            # Perform square off all
            try:
                result = state_manager.trader.square_off_all_positions()
                logger.info(f"✅ All positions squared off successfully: {', '.join(positions_to_square)}")
                square_off_message = f"All positions squared off: {', '.join(positions_to_square)} ({len(positions_to_square)} total)"
                log_trader_state(state_manager.trader, "after_square_off_all_reset")
                
                # Log the result if it contains useful information
                if result and isinstance(result, dict):
                    logger.debug(f"📊 Square off all result: {result}")
                    
            except Exception as square_off_error:
                logger.error(f"❌ Error during square off all operation: {square_off_error}")
                logger.exception("Full square off all error traceback:")
                raise square_off_error
        
        # Step 2: Reset VWAP override to 0
        logger.info("📋 Step 2: Resetting VWAP override to 0...")
        try:
            # Write 0 to vwap_override.txt
            with open('vwap_override.txt', 'w') as f:
                f.write('0')
            logger.debug("💾 VWAP override written to file: 0")
            
            # Update trader VWAP override settings
            state_manager.trader.vwap_override_enabled = True
            state_manager.trader.vwap_override_value = 0
            logger.debug("🎯 Trader VWAP override set to 0")
            
            logger.info("✅ VWAP override reset to 0")
            
        except Exception as vwap_error:
            logger.error(f"❌ Error resetting VWAP override: {vwap_error}")
            logger.exception("Full VWAP reset error traceback:")
            raise vwap_error
        
        # Step 3: Save app state
        try:
            state_manager.save_current_state()
            logger.debug("💾 App state saved after square off all + VWAP reset")
        except Exception as save_error:
            logger.warning(f"⚠️ Could not save state: {save_error}")
        
        success_message = f"{square_off_message} + VWAP override reset to 0"
        logger.info(f"✅ Square Off All + Reset VWAP completed: {success_message}")
        log_function_exit("square_off_all_and_reset_vwap", "success", success_message)
        
        return {
            "status": "success", 
            "message": success_message,
            "details": {
                "positions_squared_off": square_off_message,
                "positions_list": positions_to_square if positions_to_square else [],
                "position_count": len(positions_to_square) if positions_to_square else 0,
                "vwap_override_reset": "VWAP override set to 0"
            }
        }
        
    except HTTPException:
        raise
    except Exception as e:
        error_msg = f"Error in square off all + reset VWAP operation: {str(e)}"
        logger.error(f"❌ {error_msg}")
        logger.exception("Full square off all + reset VWAP error traceback:")
        log_function_exit("square_off_all_and_reset_vwap", error=error_msg)
        raise HTTPException(status_code=500, detail=error_msg)

# Excel Export APIs

@app.get("/api/excel/download/{file_type}")
async def download_excel_file(file_type: str, date: Optional[str] = None):
    """Download Excel files for analysis"""
    try:
        # Use provided date or default to current date
        target_date = date if date and date != "null" else datetime.now().strftime('%Y%m%d')
        
        # Map file types to actual date-based file names
        file_mapping = {
            "orders": f"nifty_orders_{target_date}.xlsx",
            "trades": f"nifty_trades_{target_date}.xlsx", 
            "portfolio": f"nifty_portfolio_{target_date}.xlsx",
            "nifty": f"nifty_orders_{target_date}.xlsx",  # Legacy mapping
            "options": f"nifty_trades_{target_date}.xlsx",  # Legacy mapping
            "analysis": f"nifty_portfolio_{target_date}.xlsx"  # Legacy mapping
        }
        
        if file_type not in file_mapping:
            raise HTTPException(status_code=400, detail="Invalid file type")
            
        file_name = file_mapping[file_type]
        file_path = os.path.join(os.getcwd(), file_name)
        
        # Check if file exists, if not try to find latest file
        if not os.path.exists(file_path):
            # Look for files with pattern matching
            pattern_mapping = {
                "orders": "nifty_orders_*.xlsx",
                "trades": "nifty_trades_*.xlsx",
                "portfolio": "nifty_portfolio_*.xlsx",
                "nifty": "nifty_orders_*.xlsx",
                "options": "nifty_trades_*.xlsx", 
                "analysis": "nifty_portfolio_*.xlsx"
            }
            
            pattern = pattern_mapping[file_type]
            matching_files = glob.glob(pattern)
            
            if matching_files:
                # Get the latest file
                file_path = max(matching_files, key=os.path.getctime)
                file_name = os.path.basename(file_path)
            else:
                # Create sample Excel file if no files exist
                sample_data = pd.DataFrame({
                    "Timestamp": [datetime.now()],
                    "Type": [file_type.upper()],
                    "Status": ["No data available yet"],
                    "Note": ["File will be created when trading starts"]
                })
                sample_data.to_excel(file_path, index=False)
        
        return FileResponse(
            path=file_path,
            filename=file_name,
            media_type="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet"
        )
        
    except Exception as e:
        logger.error(f"Error downloading Excel file: {e}")
        raise HTTPException(status_code=500, detail=f"Error downloading file: {str(e)}")

@app.get("/api/excel/list")
async def list_excel_files():
    """List today's Excel files only"""
    try:
        excel_files = []
        current_date = datetime.now().strftime('%Y%m%d')
        
        # Check for today's files only
        file_patterns = {
            "orders": f"nifty_orders_{current_date}.xlsx",
            "trades": f"nifty_trades_{current_date}.xlsx",
            "portfolio": f"nifty_portfolio_{current_date}.xlsx"
        }
        
        for file_type, filename in file_patterns.items():
            if os.path.exists(filename):
                file_info = {
                    "type": file_type,
                    "filename": filename,
                    "exists": True,
                    "size": os.path.getsize(filename),
                    "modified": datetime.fromtimestamp(os.path.getmtime(filename)).isoformat()
                }
            else:
                # File doesn't exist yet
                file_info = {
                    "type": file_type,
                    "filename": filename,
                    "exists": False,
                    "size": 0,
                    "modified": None
                }
            
            excel_files.append(file_info)
        
        return {"files": excel_files}
        
    except Exception as e:
        logger.error(f"Error listing Excel files: {e}")
        raise HTTPException(status_code=500, detail=f"Error listing files: {str(e)}")

@app.get("/api/excel/list/all")
async def list_all_excel_files():
    """List all Excel files (current and historical)"""
    try:
        excel_files = []
        
        # Check for all date-based files
        file_patterns = {
            "orders": "nifty_orders_*.xlsx",
            "trades": "nifty_trades_*.xlsx",
            "portfolio": "nifty_portfolio_*.xlsx"
        }
        
        for file_type, pattern in file_patterns.items():
            matching_files = glob.glob(pattern)
            
            for file_path in matching_files:
                filename = os.path.basename(file_path)
                # Extract date from filename - more flexible regex
                date_match = re.search(r'_(\d{8})', filename)
                file_date = date_match.group(1) if date_match else "unknown"
                
                file_info = {
                    "type": file_type,
                    "filename": filename,
                    "date": file_date,
                    "exists": True,
                    "size": os.path.getsize(file_path),
                    "modified": datetime.fromtimestamp(os.path.getmtime(file_path)).isoformat()
                }
                excel_files.append(file_info)
        
        # Sort by date (newest first)
        excel_files.sort(key=lambda x: x['date'], reverse=True)
        
        return {"files": excel_files}
        
    except Exception as e:
        logger.error(f"Error listing Excel files: {e}")
        raise HTTPException(status_code=500, detail=f"Error listing files: {str(e)}")

# Log File Download APIs

@app.get("/api/logs/download/{log_type}")
async def download_log_file(log_type: str, date: Optional[str] = None):
    """Download log files for debugging and analysis"""
    try:
        current_date = datetime.now().strftime("%Y%m%d")
        # Handle "null" string from frontend
        target_date = date if date and date != "null" else current_date
        
        # Map log types to file patterns
        if log_type == "trader":
            filename = f"nifty_trader_{target_date}.log"
        elif log_type == "webserver":
            filename = "web_server.log"
        else:
            raise HTTPException(status_code=400, detail="Invalid log type. Use 'trader' or 'webserver'")
        
        file_path = filename
        
        # Check if file exists
        if not os.path.exists(file_path):
            raise HTTPException(status_code=404, detail=f"Log file not found: {filename}")
        
        # Check file size to prevent downloading huge files
        file_size = os.path.getsize(file_path)
        if file_size > 50 * 1024 * 1024:  # 50MB limit
            raise HTTPException(status_code=400, detail="Log file too large (>50MB). Please contact administrator.")
        
        return FileResponse(
            path=file_path,
            media_type='text/plain',
            filename=filename,
            headers={"Content-Disposition": f"attachment; filename={filename}"}
        )
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error downloading log file: {e}")
        raise HTTPException(status_code=500, detail=f"Error downloading log file: {str(e)}")

@app.get("/api/logs/list")
async def list_log_files():
    """List available log files separated by today vs historical"""
    try:
        today_date = datetime.now().strftime("%Y%m%d")
        log_files = {
            "today": [],
            "historical": []
        }
        
        # Look for trader log files (pattern: nifty_trader_YYYYMMDD.log)
        trader_log_files = glob.glob("nifty_trader_*.log")
        
        for log_file in trader_log_files:
            if os.path.exists(log_file):
                # Extract date from filename
                date_part = log_file.split("_")[-1].replace(".log", "") if "_" in log_file else "unknown"
                
                file_info = {
                    "type": "trader",
                    "filename": log_file,
                    "date": date_part,
                    "exists": True,
                    "size": os.path.getsize(log_file),
                    "size_mb": round(os.path.getsize(log_file) / (1024 * 1024), 2),
                    "modified": datetime.fromtimestamp(os.path.getmtime(log_file)).isoformat()
                }
                
                # Categorize as today or historical
                if date_part == today_date:
                    log_files["today"].append(file_info)
                else:
                    log_files["historical"].append(file_info)
        
        # Look for web server log files (pattern: web_server_YYYYMMDD.log)
        web_server_log_files = glob.glob("web_server_*.log")
        
        for log_file in web_server_log_files:
            if os.path.exists(log_file):
                # Extract date from filename
                date_part = log_file.split("_")[-1].replace(".log", "") if "_" in log_file else "unknown"
                
                file_info = {
                    "type": "webserver",
                    "filename": log_file,
                    "date": date_part,
                    "exists": True,
                    "size": os.path.getsize(log_file),
                    "size_mb": round(os.path.getsize(log_file) / (1024 * 1024), 2),
                    "modified": datetime.fromtimestamp(os.path.getmtime(log_file)).isoformat()
                }
                
                # Categorize as today or historical
                if date_part == today_date:
                    log_files["today"].append(file_info)
                else:
                    log_files["historical"].append(file_info)
        
        # Check for legacy web_server.log (without date)
        if os.path.exists("web_server.log"):
            file_info = {
                "type": "webserver",
                "filename": "web_server.log",
                "date": "legacy",
                "exists": True,
                "size": os.path.getsize("web_server.log"),
                "size_mb": round(os.path.getsize("web_server.log") / (1024 * 1024), 2),
                "modified": datetime.fromtimestamp(os.path.getmtime("web_server.log")).isoformat()
            }
            log_files["historical"].append(file_info)
        
        # Sort each category by modification time (newest first)
        log_files["today"].sort(key=lambda x: x['modified'], reverse=True)
        log_files["historical"].sort(key=lambda x: x['modified'], reverse=True)
        
        return log_files
        
    except Exception as e:
        logger.error(f"Error listing log files: {e}")
        raise HTTPException(status_code=500, detail=f"Error listing log files: {str(e)}")

@app.get("/api/logs/tail/{log_type}")
async def tail_log_file(log_type: str, lines: int = 100, date: Optional[str] = None):
    """Get the last N lines of a log file for quick viewing"""
    try:
        if lines > 1000:
            raise HTTPException(status_code=400, detail="Cannot request more than 1000 lines")
        
        current_date = datetime.now().strftime("%Y%m%d")
        # Handle "null" string from frontend
        target_date = date if date and date != "null" else current_date
        
        # Map log types to file patterns
        if log_type == "trader":
            filename = f"nifty_trader_{target_date}.log"
        elif log_type == "webserver":
            filename = "web_server.log"
        else:
            raise HTTPException(status_code=400, detail="Invalid log type. Use 'trader' or 'webserver'")
        
        if not os.path.exists(filename):
            raise HTTPException(status_code=404, detail=f"Log file not found: {filename}")
        
        # Read last N lines
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            all_lines = f.readlines()
        
        last_lines = all_lines[-lines:] if len(all_lines) > lines else all_lines
        
        # Get file stats for live monitoring
        file_stats = os.stat(filename)
        
        return {
            "filename": filename,
            "total_lines": len(all_lines),
            "returned_lines": len(last_lines),
            "content": "".join(last_lines),
            "file_size": file_stats.st_size,
            "last_modified": datetime.fromtimestamp(file_stats.st_mtime).isoformat(),
            "can_stream": True,  # Indicates WebSocket streaming is available
            "stream_url": f"/ws/logs/{log_type}"
        }
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error tailing log file: {e}")
        raise HTTPException(status_code=500, detail=f"Error reading log file: {str(e)}")

@app.get("/api/logs/follow/{log_type}")
async def follow_log_file(log_type: str, lines: int = 50, date: Optional[str] = None):
    """Get recent log lines with metadata for following (like tail -f)"""
    try:
        if lines > 500:
            raise HTTPException(status_code=400, detail="Cannot request more than 500 lines for following")
        
        current_date = datetime.now().strftime("%Y%m%d")
        target_date = date if date and date != "null" else current_date
        
        # Map log types to file patterns
        if log_type == "trader":
            filename = f"nifty_trader_{target_date}.log"
        elif log_type == "webserver":
            filename = "web_server.log"
        else:
            raise HTTPException(status_code=400, detail="Invalid log type. Use 'trader' or 'webserver'")
        
        if not os.path.exists(filename):
            # Return empty result for non-existent files (they might be created later)
            return {
                "filename": filename,
                "exists": False,
                "lines": [],
                "total_lines": 0,
                "file_size": 0,
                "last_modified": None,
                "next_check_in_ms": 2000
            }
        
        # Read recent lines
        with open(filename, 'r', encoding='utf-8', errors='ignore') as f:
            all_lines = f.readlines()
        
        recent_lines = all_lines[-lines:] if len(all_lines) > lines else all_lines
        
        # Parse lines into structured format
        parsed_lines = []
        for i, line in enumerate(recent_lines):
            line_clean = line.rstrip()
            if line_clean:
                # Try to extract timestamp and level from log line
                timestamp_match = None
                level = "INFO"
                
                # Look for common timestamp patterns
                import re
                timestamp_pattern = r'(\d{4}-\d{2}-\d{2} \d{2}:\d{2}:\d{2}[,\d]*)'
                level_pattern = r'(DEBUG|INFO|WARNING|ERROR|CRITICAL)'
                
                ts_match = re.search(timestamp_pattern, line_clean)
                level_match = re.search(level_pattern, line_clean)
                
                if ts_match:
                    timestamp_match = ts_match.group(1)
                if level_match:
                    level = level_match.group(1)
                
                parsed_lines.append({
                    "line_number": len(all_lines) - len(recent_lines) + i + 1,
                    "content": line_clean,
                    "timestamp": timestamp_match,
                    "level": level,
                    "raw": line_clean
                })
        
        # Get file stats
        file_stats = os.stat(filename)
        
        return {
            "filename": filename,
            "exists": True,
            "lines": parsed_lines,
            "total_lines": len(all_lines),
            "file_size": file_stats.st_size,
            "last_modified": datetime.fromtimestamp(file_stats.st_mtime).isoformat(),
            "next_check_in_ms": 1000,  # Suggest checking again in 1 second
            "websocket_available": True,
            "websocket_url": f"/ws/logs/{log_type}"
        }
        
    except HTTPException:
        raise
    except Exception as e:
        logger.error(f"Error following log file: {e}")
        raise HTTPException(status_code=500, detail=f"Error reading log file: {str(e)}")

@app.get("/api/debug/positions")
async def debug_positions():
    """Debug endpoint to check position data flow"""
    try:
        debug_info = {
            "timestamp": datetime.now().isoformat(),
            "trader_exists": state_manager.trader is not None,
            "trading_active": state_manager.is_trading_active,
            "app_state_file_exists": os.path.exists('app_state.json'),
            "data_state_file_exists": os.path.exists('data/current_state.json')
        }
        
        if state_manager.trader:
            debug_info.update({
                "trader_positions": state_manager.trader.positions,
                "trader_long_positions": state_manager.trader.long_positions,
                "trader_simulation_mode": getattr(state_manager.trader, 'simulation_mode', None),
                "trader_trading_portfolio": getattr(state_manager.trader, 'trading_portfolio', None)
            })
        
        # Read state files for comparison
        if os.path.exists('app_state.json'):
            with open('app_state.json', 'r') as f:
                app_state = json.load(f)
                debug_info["app_state_positions"] = app_state.get('positions', {})
                debug_info["app_state_portfolio"] = app_state.get('trading_portfolio', {})
                # Backward compatibility: check for old virtual_portfolio key
                if not debug_info["app_state_portfolio"]:
                    debug_info["app_state_portfolio"] = app_state.get('virtual_portfolio', {})
        
        if os.path.exists('data/current_state.json'):
            with open('data/current_state.json', 'r') as f:
                data_state = json.load(f)
                trader_state = data_state.get('trader_state', {})
                debug_info["data_state_positions"] = trader_state.get('positions', {})
        
        return debug_info
        
    except Exception as e:
        logger.error(f"Error in debug positions endpoint: {e}")
        return {"error": str(e), "timestamp": datetime.now().isoformat()}

# Chart APIs - placeholders for UI compatibility
@app.get("/api/charts/current-tokens")
async def get_current_tokens():
    """Get current option tokens for charting"""
    try:
        if not state_manager.trader:
            return {"tokens": {}, "message": "Trading bot not initialized"}
        
        # Return current strike information if available
        result = {
            "tokens": {},
            "current_atm_strike": getattr(state_manager.trader, 'current_atm_strike', None),
            "current_nifty_price": getattr(state_manager.trader, 'current_nifty_price', None),
            "message": "Simulation mode - chart data not available"
        }
        
        # If we have positions, include their symbols
        if hasattr(state_manager.trader, 'positions'):
            positions = state_manager.trader.positions
            if positions.get('CE'):
                result["tokens"]["CE"] = positions['CE'].get('tradingsymbol', 'N/A')
            if positions.get('PE'):
                result["tokens"]["PE"] = positions['PE'].get('tradingsymbol', 'N/A')
        
        return result
        
    except Exception as e:
        logger.error(f"Error getting current tokens: {e}")
        return {"error": str(e), "tokens": {}}

# Helper functions for chart data
def convert_premium_data_to_ohlc(premium_data, timeframe="1m", option_type="combined"):
    """Convert premium data to OHLC format for charting"""
    if not premium_data:
        return []
    
    try:
        # Extract the price data based on option type
        price_key = {
            "CE": "CE",
            "PE": "PE", 
            "combined": "combined"
        }.get(option_type, "combined")
        
        # Group data by timeframe intervals
        from datetime import datetime, timedelta
        import pytz
        
        # Convert timeframe to minutes
        interval_minutes = {
            "1m": 1,
            "5m": 5,
            "15m": 15,
            "30m": 30,
            "1h": 60
        }.get(timeframe, 1)
        
        # Group data into intervals
        grouped_data = {}
        ist_tz = pytz.timezone('Asia/Kolkata')
        
        for data_point in premium_data:
            try:
                # Parse timestamp
                if isinstance(data_point['timestamp'], str):
                    timestamp = datetime.fromisoformat(data_point['timestamp'].replace('Z', '+00:00'))
                else:
                    timestamp = data_point['timestamp']
                
                # Convert to IST if needed
                if timestamp.tzinfo is None:
                    timestamp = ist_tz.localize(timestamp)
                elif timestamp.tzinfo != ist_tz:
                    timestamp = timestamp.astimezone(ist_tz)
                
                # Round to interval boundary
                minute = (timestamp.minute // interval_minutes) * interval_minutes
                interval_start = timestamp.replace(minute=minute, second=0, microsecond=0)
                
                price = data_point.get(price_key, 0)
                if price is None:
                    continue
                    
                interval_key = interval_start.isoformat()
                
                if interval_key not in grouped_data:
                    grouped_data[interval_key] = {
                        'open': price,
                        'high': price,
                        'low': price,
                        'close': price,
                        'timestamp': interval_start,
                        'count': 1
                    }
                else:
                    grouped_data[interval_key]['high'] = max(grouped_data[interval_key]['high'], price)
                    grouped_data[interval_key]['low'] = min(grouped_data[interval_key]['low'], price)
                    grouped_data[interval_key]['close'] = price  # Latest price becomes close
                    grouped_data[interval_key]['count'] += 1
                    
            except Exception as e:
                logger.warning(f"Error processing data point {data_point}: {e}")
                continue
        
        # Convert to chart format
        ohlc_data = []
        for interval_data in sorted(grouped_data.values(), key=lambda x: x['timestamp']):
            ohlc_data.append({
                'time': interval_data['timestamp'].isoformat(),
                'open': float(interval_data['open']),
                'high': float(interval_data['high']),
                'low': float(interval_data['low']),
                'close': float(interval_data['close'])
            })
        
        return ohlc_data[-100:]  # Return last 100 candles
        
    except Exception as e:
        logger.error(f"Error converting premium data to OHLC: {e}")
        return []

def get_historical_ohlc_data(trader, symbol, timeframe="1m", limit=100):
    """Get historical OHLC data using Fyers API"""
    if not trader or not hasattr(trader, '_get_historical_data_with_rate_limit'):
        return []
    
    try:
        from datetime import datetime, timedelta
        import pytz
        
        # Calculate date range
        ist_tz = pytz.timezone('Asia/Kolkata')
        end_date = datetime.now(ist_tz)
        
        # Go back enough days to get sufficient data
        days_back = 5 if timeframe in ["1m", "5m"] else 10
        start_date = end_date - timedelta(days=days_back)
        
        # Convert timeframe to Fyers resolution
        resolution_map = {
            "1m": "1",
            "5m": "5", 
            "15m": "15",
            "30m": "30",
            "1h": "60"
        }
        resolution = resolution_map.get(timeframe, "1")
        
        # Get historical data
        candles = trader._get_historical_data_with_rate_limit(
            symbol=symbol,
            from_date=start_date,
            to_date=end_date,
            resolution=resolution
        )
        
        if not candles:
            return []
        
        # Convert to chart format
        ohlc_data = []
        for candle in candles[-limit:]:  # Get last N candles
            ohlc_data.append({
                'time': candle['time'],
                'open': float(candle['open']),
                'high': float(candle['high']),
                'low': float(candle['low']),
                'close': float(candle['close'])
            })
        
        return ohlc_data
        
    except Exception as e:
        logger.error(f"Error getting historical OHLC data: {e}")
        return []

@app.get("/api/charts/ce-ohlc")
async def get_ce_ohlc(timeframe: str = "1m"):
    """Get CE option OHLC data for charting"""
    try:
        if not state_manager.trader:
            return {
                "data": [],
                "symbol": "CE Option",
                "timeframe": timeframe,
                "message": "Trader not initialized",
                "current_price": None
            }
        
        trader = state_manager.trader
        symbol = "CE Option"
        current_price = None
        
        # Try to get current option symbols and prices
        if hasattr(trader, 'positions') and trader.positions.get('CE'):
            ce_symbol = trader.positions['CE'].get('tradingsymbol', '')
            symbol = ce_symbol.replace("NSE:", "") if ce_symbol else "CE Option"
            
        # Get current CE price from latest premium data
        if hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            latest_data = trader.combined_premium_data[-1]
            current_price = latest_data.get('CE')
        
        # Try to get historical OHLC data first
        ohlc_data = []
        if hasattr(trader, 'positions') and trader.positions.get('CE'):
            ce_symbol = trader.positions['CE'].get('tradingsymbol', '')
            if ce_symbol and not trader.simulation_mode:
                ohlc_data = get_historical_ohlc_data(trader, ce_symbol, timeframe)
        
        # If no historical data, convert premium data to OHLC
        if not ohlc_data and hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            ohlc_data = convert_premium_data_to_ohlc(trader.combined_premium_data, timeframe, "CE")
        
        return {
            "data": ohlc_data,
            "symbol": symbol,
            "timeframe": timeframe,
            "message": f"Live data ({len(ohlc_data)} candles)" if ohlc_data else "No data available",
            "current_price": current_price
        }
        
    except Exception as e:
        logger.error(f"Error getting CE OHLC data: {e}")
        return {"error": str(e), "data": []}

@app.get("/api/charts/pe-ohlc")
async def get_pe_ohlc(timeframe: str = "1m"):
    """Get PE option OHLC data for charting"""
    try:
        if not state_manager.trader:
            return {
                "data": [],
                "symbol": "PE Option",
                "timeframe": timeframe,
                "message": "Trader not initialized",
                "current_price": None
            }
        
        trader = state_manager.trader
        symbol = "PE Option"
        current_price = None
        
        # Try to get current option symbols and prices
        if hasattr(trader, 'positions') and trader.positions.get('PE'):
            pe_symbol = trader.positions['PE'].get('tradingsymbol', '')
            symbol = pe_symbol.replace("NSE:", "") if pe_symbol else "PE Option"
            
        # Get current PE price from latest premium data
        if hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            latest_data = trader.combined_premium_data[-1]
            current_price = latest_data.get('PE')
        
        # Try to get historical OHLC data first
        ohlc_data = []
        if hasattr(trader, 'positions') and trader.positions.get('PE'):
            pe_symbol = trader.positions['PE'].get('tradingsymbol', '')
            if pe_symbol and not trader.simulation_mode:
                ohlc_data = get_historical_ohlc_data(trader, pe_symbol, timeframe)
        
        # If no historical data, convert premium data to OHLC
        if not ohlc_data and hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            ohlc_data = convert_premium_data_to_ohlc(trader.combined_premium_data, timeframe, "PE")
        
        return {
            "data": ohlc_data,
            "symbol": symbol,
            "timeframe": timeframe,
            "message": f"Live data ({len(ohlc_data)} candles)" if ohlc_data else "No data available",
            "current_price": current_price
        }
        
    except Exception as e:
        logger.error(f"Error getting PE OHLC data: {e}")
        return {"error": str(e), "data": []}

@app.get("/api/charts/combined-ohlc")
async def get_combined_ohlc(timeframe: str = "1m"):
    """Get combined OHLC data for charting"""
    try:
        if not state_manager.trader:
            return {
                "data": [],
                "symbol": "Combined Options",
                "timeframe": timeframe,
                "message": "Trader not initialized",
                "current_price": None,
                "current_vwap": None
            }
        
        trader = state_manager.trader
        symbol = "Combined Options (CE + PE)"
        current_price = None
        current_vwap = None
        
        # Get current combined price and VWAP
        if hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            latest_data = trader.combined_premium_data[-1]
            current_price = latest_data.get('combined')
            
        if hasattr(trader, 'current_vwap'):
            current_vwap = trader.current_vwap
        
        # Convert premium data to OHLC for combined prices
        ohlc_data = []
        if hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            ohlc_data = convert_premium_data_to_ohlc(trader.combined_premium_data, timeframe, "combined")
        
        return {
            "data": ohlc_data,
            "symbol": symbol,
            "timeframe": timeframe,
            "message": f"Live data ({len(ohlc_data)} candles)" if ohlc_data else "No data available",
            "current_price": current_price,
            "current_vwap": current_vwap
        }
        
    except Exception as e:
        logger.error(f"Error getting combined OHLC data: {e}")
        return {"error": str(e), "data": []}

def convert_ohlc_to_heikin_ashi(ohlc_data):
    """Convert OHLC data to Heikin Ashi format"""
    if not ohlc_data:
        return []
    
    ha_data = []
    prev_ha_close = None
    prev_ha_open = None
    
    for i, candle in enumerate(ohlc_data):
        try:
            open_price = candle['open']
            high_price = candle['high']
            low_price = candle['low']
            close_price = candle['close']
            
            if i == 0:
                # First candle
                ha_open = (open_price + close_price) / 2
                ha_close = (open_price + high_price + low_price + close_price) / 4
            else:
                # Subsequent candles
                ha_open = (prev_ha_open + prev_ha_close) / 2
                ha_close = (open_price + high_price + low_price + close_price) / 4
            
            ha_high = max(high_price, ha_open, ha_close)
            ha_low = min(low_price, ha_open, ha_close)
            
            ha_data.append({
                'time': candle['time'],
                'open': ha_open,
                'high': ha_high,
                'low': ha_low,
                'close': ha_close
            })
            
            prev_ha_open = ha_open
            prev_ha_close = ha_close
            
        except Exception as e:
            logger.warning(f"Error processing Heikin Ashi candle {i}: {e}")
            continue
    
    return ha_data

@app.get("/api/charts/heikin-ashi/{option_type}")
async def get_heikin_ashi(option_type: str, timeframe: str = "1m"):
    """Get Heikin Ashi chart data for CE, PE, or COMBINED options"""
    try:
        symbol_map = {
            "CE": "CE Option (Heikin Ashi)",
            "PE": "PE Option (Heikin Ashi)", 
            "COMBINED": "Combined Options (Heikin Ashi)"
        }
        
        if option_type not in symbol_map:
            raise HTTPException(status_code=400, detail="Invalid option type. Use CE, PE, or COMBINED")
        
        if not state_manager.trader:
            return {
                "data": [],
                "symbol": symbol_map[option_type],
                "timeframe": timeframe,
                "message": "Trader not initialized",
                "current_price": None
            }
        
        trader = state_manager.trader
        symbol = symbol_map[option_type]
        current_price = None
        
        # Get current price based on option type
        if hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            latest_data = trader.combined_premium_data[-1]
            if option_type == "CE":
                current_price = latest_data.get('CE')
                symbol = latest_data.get('ce_symbol', symbol)
            elif option_type == "PE":
                current_price = latest_data.get('PE')
                symbol = latest_data.get('pe_symbol', symbol)
            else:  # COMBINED
                current_price = latest_data.get('combined')
        
        # Get OHLC data first
        ohlc_data = []
        if hasattr(trader, 'combined_premium_data') and trader.combined_premium_data:
            price_type = option_type.lower() if option_type != "COMBINED" else "combined"
            ohlc_data = convert_premium_data_to_ohlc(trader.combined_premium_data, timeframe, price_type)
        
        # Convert OHLC to Heikin Ashi
        ha_data = convert_ohlc_to_heikin_ashi(ohlc_data)
        
        return {
            "data": ha_data,
            "symbol": symbol,
            "timeframe": timeframe,
            "message": f"Live Heikin Ashi data ({len(ha_data)} candles)" if ha_data else "No data available",
            "current_price": current_price
        }
        
    except Exception as e:
        logger.error(f"Error getting Heikin Ashi data for {option_type}: {e}")
        return {"error": str(e), "data": []}

# WebSocket endpoint for live log streaming
@app.websocket("/ws/logs/{log_type}")
async def log_stream_websocket(websocket: WebSocket, log_type: str, date: Optional[str] = None):
    """Stream live log updates via WebSocket"""
    log_function_entry("log_stream_websocket", log_type=log_type, date=date)
    
    try:
        await websocket.accept()
        logger.info(f"🔌 Log streaming WebSocket connected for {log_type}")
        
        # Validate log type
        if log_type not in ["trader", "webserver"]:
            error_msg = "Invalid log type. Use 'trader' or 'webserver'"
            logger.error(f"❌ {error_msg}")
            await websocket.send_text(json.dumps({"error": error_msg}))
            return
        
        # Determine log file
        current_date = datetime.now().strftime("%Y%m%d")
        target_date = date if date and date != "null" else current_date
        
        if log_type == "trader":
            log_file = f"nifty_trader_{target_date}.log"
        else:
            log_file = "web_server.log"
        
        logger.debug(f" Streaming log file: {log_file}")
        
        if not os.path.exists(log_file):
            error_msg = f"Log file not found: {log_file}"
            logger.error(f"❌ {error_msg}")
            await websocket.send_text(json.dumps({"error": error_msg}))
            return
        
        # Send initial message
        await websocket.send_text(json.dumps({
            "type": "connected",
            "log_type": log_type,
            "filename": log_file,
            "message": f"Connected to {log_file} - streaming live updates"
        }))
        
        logger.debug(f" Starting live log streaming for {log_file}")
        
        # Track last file position
        last_position = 0
        if os.path.exists(log_file):
            # Start from end of file
            with open(log_file, 'r') as f:
                f.seek(0, 2)  # Seek to end
                last_position = f.tell()
        
        # Stream new log entries
        while True:
            try:
                if os.path.exists(log_file):
                    current_size = os.path.getsize(log_file)
                    if current_size > last_position:
                        with open(log_file, 'r', encoding='utf-8', errors='ignore') as f:
                            f.seek(last_position)
                            new_lines = f.readlines()
                            if new_lines:
                                for line in new_lines:
                                    await websocket.send_text(json.dumps({
                                        "type": "log",
                                        "content": line.rstrip(),
                                        "timestamp": datetime.now().isoformat()
                                    }))
                                last_position = f.tell()
                                logger.debug(f" Streamed {len(new_lines)} new log lines")
                
                # Wait before next check
                await asyncio.sleep(1)
                
            except Exception as e:
                logger.error(f"❌ Error reading log file during streaming: {e}")
                await websocket.send_text(json.dumps({
                    "type": "error",
                    "message": f"Error reading log file: {str(e)}"
                }))
                break
                
    except WebSocketDisconnect:
        logger.info(f"🔌 Log streaming WebSocket disconnected for {log_type}")
        log_function_exit("log_stream_websocket", "disconnected")
    except Exception as e:
        logger.error(f"❌ WebSocket log streaming error: {e}")
        log_function_exit("log_stream_websocket", error=str(e))

# WebSocket endpoint
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    log_function_entry("websocket_endpoint")
    try:
        await websocket.accept()
        state_manager.add_websocket_client(websocket)
        logger.info(" Main WebSocket client connected")
        
        try:
            while True:
                # Keep connection alive and handle incoming messages
                data = await websocket.receive_text()
                logger.debug(f" WebSocket received data: {data}")
                
                # You can add message handling here if needed
                # For now, just echo back or ignore
                
        except WebSocketDisconnect:
            logger.info(" Main WebSocket client disconnected")
            log_function_exit("websocket_endpoint", "disconnected")
        except Exception as e:
            logger.error(f"❌ WebSocket error during message handling: {e}")
            raise e
            
    except WebSocketDisconnect:
        logger.info(" WebSocket disconnected during setup")
    except Exception as e:
        logger.error(f"❌ WebSocket error: {e}")
        log_function_exit("websocket_endpoint", error=str(e))
    finally:
        state_manager.remove_websocket_client(websocket)

async def frequent_price_broadcast():
    """Background task to broadcast CE/PE prices every 2 seconds"""
    logger.info(" Starting frequent price broadcast task")
    
    while True:
        try:
            # Only broadcast if we have an active trader and WebSocket clients
            if state_manager.trader and state_manager.websocket_clients:
                price_update = None
                
                # Try to get current ATM strike and fetch fresh options data
                if (hasattr(state_manager.trader, 'current_atm_strike') and 
                    state_manager.trader.current_atm_strike):
                    
                    try:
                        # Fetch fresh options data directly for real-time prices
                        logger.debug(f"🔄 Fetching fresh options data for ATM strike: {state_manager.trader.current_atm_strike}")
                        fresh_options_data = state_manager.trader.get_options_data(state_manager.trader.current_atm_strike)
                        
                        if fresh_options_data:
                            # Get current trends
                            trends = state_manager.trader.get_current_trends()
                            
                            # Use fresh data for broadcast
                            price_update = {
                                "type": "price_update",
                                "timestamp": datetime.now().isoformat(),
                                "nifty_price": state_manager.trader.current_nifty_price,
                                "atm_strike": state_manager.trader.current_atm_strike,
                                "ce_price": fresh_options_data.get('CE', 0),
                                "pe_price": fresh_options_data.get('PE', 0),
                                "combined_premium": fresh_options_data.get('combined', 0),
                                "ce_symbol": fresh_options_data.get('ce_tradingsymbol', ''),
                                "pe_symbol": fresh_options_data.get('pe_tradingsymbol', ''),
                                "ce_trend": trends.get('ce_trend', 'NEUTRAL'),
                                "pe_trend": trends.get('pe_trend', 'NEUTRAL'),
                                "ha_trend": trends.get('ha_trend', 'NEUTRAL'),
                                "source": "fresh_fetch"
                            }
                            logger.debug(f"📡 Using fresh options data: CE={fresh_options_data.get('CE', 0):.2f}, PE={fresh_options_data.get('PE', 0):.2f}")
                        else:
                            logger.debug("⚠️ Fresh options data fetch failed, trying cached data")
                    except Exception as e:
                        logger.warning(f"⚠️ Error fetching fresh options data: {e}")
                
                # Fallback to cached data if fresh fetch failed
                if not price_update and (hasattr(state_manager.trader, 'combined_premium_data') and
                                       state_manager.trader.combined_premium_data):
                    
                    latest_data = state_manager.trader.combined_premium_data[-1]
                    trends = state_manager.trader.get_current_trends()
                    
                    price_update = {
                        "type": "price_update",
                        "timestamp": datetime.now().isoformat(),
                        "nifty_price": state_manager.trader.current_nifty_price,
                        "atm_strike": state_manager.trader.current_atm_strike,
                        "ce_price": latest_data.get('CE', 0),
                        "pe_price": latest_data.get('PE', 0),
                        "combined_premium": latest_data.get('combined', 0),
                        "ce_symbol": latest_data.get('ce_tradingsymbol', ''),
                        "pe_symbol": latest_data.get('pe_tradingsymbol', ''),
                        "ce_trend": trends.get('ce_trend', 'NEUTRAL'),
                        "pe_trend": trends.get('pe_trend', 'NEUTRAL'),
                        "ha_trend": trends.get('ha_trend', 'NEUTRAL'),
                        "source": "cached_data"
                    }
                    logger.debug(f"📡 Using cached data: CE={latest_data.get('CE', 0):.2f}, PE={latest_data.get('PE', 0):.2f}")
                
                # Broadcast if we have data
                if price_update:
                    await state_manager.broadcast_to_websockets(price_update)
                    logger.debug(f"📡 Broadcasted price update from {price_update['source']}")
                else:
                    logger.debug("📡 No price data available for broadcast")
            
            # Wait 2 seconds before next broadcast
            await asyncio.sleep(2)
            
        except Exception as e:
            logger.error(f"❌ Error in frequent price broadcast: {e}")
            await asyncio.sleep(5)  # Wait longer on error

# Startup event
@app.on_event("startup")
async def startup_event():
    log_function_entry("startup_event")
    logger.info(" Starting Nifty Options Trading Web Server")
    
    # Log system information
    logger.info(f" System Information:")
    logger.info(f"   • Python Version: {platform.python_version()}")
    logger.info(f"   • FastAPI Available: True")
    logger.info(f"   • Fyers API Available: {FYERS_AVAILABLE}")
    logger.info(f"   • Current Working Directory: {os.getcwd()}")
    logger.info(f"   • Log File: web_server.log")
    
    if FYERS_AVAILABLE:
        logger.info(" Fyers API is available - live trading enabled")
    else:
        logger.info(" Running in simulation mode - web interface only")
    
    # Check for existing state files
    if os.path.exists('app_state.json'):
        logger.info(" Found existing app_state.json")
    if os.path.exists('data/current_state.json'):
        logger.info(" Found existing data/current_state.json")
    if os.path.exists('config.txt'):
        logger.info(" Found existing config.txt")
    if os.path.exists('access.txt'):
        logger.info(" Found existing access.txt")
    
    # Start periodic state saving
    logger.info(" Starting periodic state saving...")
    state_manager.start_periodic_save()
    
    # Start frequent price broadcasting
    logger.info(" Starting frequent price broadcasting...")
    asyncio.create_task(frequent_price_broadcast())
    
    logger.info(" Nifty Options Trading Web Server startup completed successfully")
    log_function_exit("startup_event", "success")

# Order Tracking API Endpoints
@app.get("/api/orders/history")
async def get_order_history(current_user: str = Depends(verify_token)):
    """Get complete order history for UI display"""
    try:
        if not state_manager.trader:
            return {"error": "Trading bot not initialized"}
        
        return {
            "success": True,
            "data": state_manager.trader.get_order_history_for_ui()
        }
    except Exception as e:
        logger.error(f"Error getting order history: {e}")
        return {"error": str(e)}

@app.get("/api/orders/status")
async def get_order_status(current_user: str = Depends(verify_token)):
    """Get latest order status for real-time UI updates"""
    try:
        if not state_manager.trader:
            return {"error": "Trading bot not initialized"}
        
        return {
            "success": True,
            "data": state_manager.trader.get_latest_order_status()
        }
    except Exception as e:
        logger.error(f"Error getting order status: {e}")
        return {"error": str(e)}

@app.get("/api/orders/failures")
async def get_failed_orders(current_user: str = Depends(verify_token)):
    """Get failed orders for UI display"""
    try:
        if not state_manager.trader:
            return {"error": "Trading bot not initialized"}
        
        failed_orders = getattr(state_manager.trader, 'failed_orders', [])
        return {
            "success": True,
            "data": {
                "failed_orders": failed_orders,
                "count": len(failed_orders),
                "recent_failures": failed_orders[-5:] if failed_orders else []
            }
        }
    except Exception as e:
        logger.error(f"Error getting failed orders: {e}")
        return {"error": str(e)}

if __name__ == "__main__":
    import uvicorn
    
    # Enhanced startup banner with logging
    startup_banner = [
        "============================================================",
        "🚀 Starting Nifty Options Trading Web Server",
        "============================================================",
        "📊 Features:",
        "   ✅ REST API for trading control",
        "   ✅ WebSocket for real-time updates", 
        "   ✅ JSON state management",
        "   ✅ Excel export for analysis",
        "   ✅ File-based configuration",
        "   ✅ Background trading service",
        "   ✅ Comprehensive logging system",
        "   ✅ Live log streaming via WebSocket"
    ]
    
    if FYERS_AVAILABLE:
        startup_banner.append("   ✅ Live Fyers API integration")
    else:
        startup_banner.append("   ⚠️  Simulation mode (Fyers API not available)")
    
    startup_banner.extend([
        "============================================================",
        "🌐 Server will be available at:",
        "   * Main UI: http://localhost:8000",
        "   * API Docs: http://localhost:8000/docs", 
        "   * WebSocket: ws://localhost:8000/ws",
        "   * Log Streaming: ws://localhost:8000/ws/logs/{trader|webserver}",
        "============================================================",
        f"📝 Logging Configuration:",
        f"   * Console Level: INFO",
        f"   * File Level: DEBUG",
        f"   * Log File: web_server.log",
        f"   * Format: [Function:Line] - Message",
        "============================================================"
    ])
    
    # Print startup banner
    for line in startup_banner:
        print(line)
        logger.info(line.replace("🚀", "").replace("📊", "").replace("✅", "").replace("⚠️", "").replace("🌐", "").replace("📝", "").strip())
    
    # Log startup parameters
    logger.info(" Starting uvicorn server with parameters:")
    logger.info("  • Host: 0.0.0.0")
    logger.info("  • Port: 8000") 
    logger.info("  • Reload: False (production mode)")
    logger.info("  • Log Level: info")
    logger.info("  • Custom Log Config: enabled")
    
    try:
        uvicorn.run(
            "web_server:app", 
            host="localhost", 
            port=8003, 
            reload=False,  # Disable reload for production
            log_level="info",
            log_config=LOGGING_CONFIG
        )
    except KeyboardInterrupt:
        logger.info(" Server shutdown requested by user (Ctrl+C)")
        print("\n🛑 Server shutdown complete. Goodbye!")
    except Exception as e:
        logger.error(f"❌ Server startup failed: {e}")
        logger.exception("Full server startup error traceback:")
        print(f"\n❌ Server failed to start: {e}")
    finally:
        logger.info(" Web server process completed")
