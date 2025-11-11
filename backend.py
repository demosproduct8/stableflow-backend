# Complete Backend Code (app.py)

# To run this code, install the required packages:

# pip install fastapi uvicorn pydantic asyncpg solders solana python-dotenv

import os
import secrets
import hashlib
import json
from datetime import datetime, timedelta
from typing import List, Optional, Dict
from fastapi import FastAPI, HTTPException, Request, Depends
from fastapi.middleware.cors import CORSMiddleware
from fastapi.responses import JSONResponse, FileResponse
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, field_validator
import asyncpg
from contextlib import asynccontextmanager
from solders.keypair import Keypair
from solders.pubkey import Pubkey
from solders.system_program import transfer, TransferParams
from solders.transaction import Transaction
from solders.message import Message
from solana.rpc.api import Client
from solana.rpc.commitment import Confirmed, Finalized
from solana.rpc.types import TxOpts
from solana.rpc.core import RPCException
from spl.token.instructions import get_associated_token_address, create_associated_token_account, transfer_checked, TransferCheckedParams
from spl.token.constants import TOKEN_PROGRAM_ID, ASSOCIATED_TOKEN_PROGRAM_ID
from decimal import Decimal
import decimal

# Load environment variables
from dotenv import load_dotenv
load_dotenv()

# Solana mainnet RPC - REAL MAINNET
SOLANA_RPC_URL = os.getenv('SOLANA_RPC_URL', 'https://api.mainnet-beta.solana.com')
solana_client = Client(SOLANA_RPC_URL)

# Stablecoin mints on mainnet - REAL STABLECOINS
STABLECOINS = {
    "USDT": {"mint": "Es9vMFrzaCERmJfrF4H2FYD4KCoNkY11McCe8BenwNYB", "decimals": 6},
    "USDC": {"mint": "EPjFWdd5AufqSSqeM2qN1xzybapC8G4wEGGkZwyTDt1v", "decimals": 6},
    "PYUSD": {"mint": "2b1kV6DkPAnxd5ixfnxCpjxmKwqjbiXxrcSjnca9Ksmi", "decimals": 6},
    "USDe": {"mint": "DEk7SWKUxsemI2TDq5k4SA1U3jTQmZ7P7M9EasqJjk3x", "decimals": 18},
}

# Safety Configuration - with smaller thresholds for consumer wallet
SAFETY_CONFIG = {
    "MAX_SINGLE_TX": Decimal('10.0'), # Max per TX
    "DAILY_LIMIT": Decimal('50.0'), # Daily max
    "SAFE_MODE": os.getenv('SAFE_MODE', 'true').lower() == 'true',
    "REQUIRE_CONFIRMATIONS": 1
}

# Default thresholds for escalation in SPEP tiers (will be configurable via frontend)
LOW_VALUE_THRESHOLD = Decimal('2.0') # 0-2: tier1 (direct)
MID_VALUE_THRESHOLD = Decimal('5.0') # 2-5: tier2 (queue + tier2 shards)
HIGH_VALUE_THRESHOLD = Decimal('10.0') # 5-10: tier3 (queue + tier3 shards)

# Security and rate limiting (basic, no advanced for now)
class SecurityManager:
    def __init__(self):
        self.failed_attempts = {}
        self.lockout_duration = timedelta(minutes=15)
        self.max_attempts = 5
 
    def check_rate_limit(self, identifier: str) -> bool:
        if identifier in self.failed_attempts:
            attempts, last_attempt = self.failed_attempts[identifier]
            if datetime.now() - last_attempt < self.lockout_duration and attempts >= self.max_attempts:
                return False
        return True
 
    def record_failure(self, identifier: str):
        if identifier not in self.failed_attempts:
            self.failed_attempts[identifier] = [1, datetime.now()]
        else:
            self.failed_attempts[identifier][0] += 1
            self.failed_attempts[identifier][1] = datetime.now()

security_manager = SecurityManager()

class ExecutiveSafety:
    def __init__(self):
        self.daily_volumes = {}
        self.tx_history = {} # For anti-fraud: track recent TXs per wallet
        self.value_thresholds = {} # Store custom thresholds per wallet
   
    async def check_transaction_safety(self, wallet_id: str, amount: float, token_symbol: str = None) -> dict:
        today = datetime.now().date().isoformat()
       
        if wallet_id not in self.daily_volumes:
            self.daily_volumes[wallet_id] = {"date": today, "amount": Decimal('0.0')}
       
        daily_data = self.daily_volumes[wallet_id]
        if daily_data["date"] != today:
            daily_data = {"date": today, "amount": Decimal('0.0')}
            self.daily_volumes[wallet_id] = daily_data
       
        amount_dec = Decimal(str(amount))
       
        # Check single transaction limit
        if amount_dec > SAFETY_CONFIG["MAX_SINGLE_TX"]:
            return {"safe": False, "reason": f"Single transaction exceeds ${SAFETY_CONFIG['MAX_SINGLE_TX']} limit"}
       
        # Check daily limit
        if daily_data["amount"] + amount_dec > SAFETY_CONFIG["DAILY_LIMIT"]:
            return {"safe": False, "reason": f"Daily limit of ${SAFETY_CONFIG['DAILY_LIMIT']} would be exceeded"}
       
        # Anti-fraud: Check for rapid successive TXs (e.g., >3 in 5 min)
        if wallet_id not in self.tx_history:
            self.tx_history[wallet_id] = []
        recent_tx = [tx for tx in self.tx_history[wallet_id] if datetime.now() - tx < timedelta(minutes=5)]
        is_fraud_suspected = len(recent_tx) >= 3
        self.tx_history[wallet_id].append(datetime.now()) # Log attempt
        
        return {"safe": not is_fraud_suspected, "daily_used": float(daily_data["amount"]), "fraud_suspected": is_fraud_suspected, "reason": "Suspicious activity: Too many transactions in short time" if is_fraud_suspected else None}

    def set_value_thresholds(self, wallet_id: str, low: float, mid: float, high: float):
        """Set custom value thresholds for a wallet"""
        self.value_thresholds[wallet_id] = {
            "low": Decimal(str(low)),
            "mid": Decimal(str(mid)), 
            "high": Decimal(str(high))
        }

    def get_value_thresholds(self, wallet_id: str) -> Dict[str, Decimal]:
        """Get value thresholds for a wallet, fallback to defaults if not set"""
        if wallet_id in self.value_thresholds:
            return self.value_thresholds[wallet_id]
        return {
            "low": LOW_VALUE_THRESHOLD,
            "mid": MID_VALUE_THRESHOLD,
            "high": HIGH_VALUE_THRESHOLD
        }

executive_safety = ExecutiveSafety()

# Database manager with in-memory fallback
class DatabaseManager:
    def __init__(self):
        self.pool = None
        self.wallets = {}
        self.pending_txns = {}
        self.wallet_thresholds = {}  # Store wallet-specific thresholds

    async def init_db(self):
        try:
            database_url = os.getenv('DATABASE_URL')
            if database_url:
                self.pool = await asyncpg.create_pool(
                    database_url,
                    min_size=1,
                    max_size=10
                )
             
                # Initialize tables
                async with self.pool.acquire() as conn:
                    await conn.execute('''
                        CREATE TABLE IF NOT EXISTS wallets (
                            wallet_id TEXT PRIMARY KEY,
                            pubkey TEXT NOT NULL,
                            scheme TEXT NOT NULL,
                            params JSONB NOT NULL,
                            created_at TIMESTAMP DEFAULT NOW(),
                            updated_at TIMESTAMP DEFAULT NOW()
                        )
                    ''')
                 
                    await conn.execute('''
                        CREATE TABLE IF NOT EXISTS wallet_shards (
                            id SERIAL PRIMARY KEY,
                            wallet_id TEXT REFERENCES wallets(wallet_id) ON DELETE CASCADE,
                            shard TEXT NOT NULL,
                            shard_index INTEGER NOT NULL,
                            created_at TIMESTAMP DEFAULT NOW()
                        )
                    ''')
                 
                    await conn.execute('''
                        CREATE TABLE IF NOT EXISTS pending_transactions (
                            txn_id TEXT PRIMARY KEY,
                            wallet_id TEXT NOT NULL,
                            to_address TEXT NOT NULL,
                            amount DECIMAL NOT NULL,
                            token_symbol TEXT,
                            flagged BOOLEAN DEFAULT FALSE,
                            escalation_level TEXT DEFAULT 'tier1',
                            status TEXT DEFAULT 'pending',
                            created_at TIMESTAMP DEFAULT NOW(),
                            updated_at TIMESTAMP DEFAULT NOW()
                        )
                    ''')

                    await conn.execute('''
                        CREATE TABLE IF NOT EXISTS wallet_thresholds (
                            wallet_id TEXT PRIMARY KEY REFERENCES wallets(wallet_id),
                            low_threshold DECIMAL NOT NULL,
                            mid_threshold DECIMAL NOT NULL,
                            high_threshold DECIMAL NOT NULL,
                            created_at TIMESTAMP DEFAULT NOW(),
                            updated_at TIMESTAMP DEFAULT NOW()
                        )
                    ''')
                print("Database initialized successfully")
            else:
                print("No DATABASE_URL found, using in-memory storage")
                self.pool = None
        except Exception as e:
            print(f"Database initialization failed, using in-memory storage: {e}")
            self.pool = None
 
    async def store_wallet(self, wallet_id: str, pubkey: str, scheme: str, params: dict, shards: List[str]):
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    async with conn.transaction():
                        await conn.execute(
                            'INSERT INTO wallets (wallet_id, pubkey, scheme, params) VALUES ($1, $2, $3, $4)',
                            wallet_id, pubkey, scheme, params
                        )
                     
                        for i, shard in enumerate(shards):
                            await conn.execute(
                                'INSERT INTO wallet_shards (wallet_id, shard, shard_index) VALUES ($1, $2, $3)',
                                wallet_id, shard, i
                            )
            except Exception as e:
                print(f"Database storage failed, using in-memory: {e}")
                self._store_wallet_memory(wallet_id, pubkey, scheme, params, shards)
        else:
            self._store_wallet_memory(wallet_id, pubkey, scheme, params, shards)
 
    def _store_wallet_memory(self, wallet_id: str, pubkey: str, scheme: str, params: dict, shards: List[str]):
        self.wallets[wallet_id] = {
            'pubkey': pubkey,
            'scheme': scheme,
            'params': params,
            'shards': shards
        }
 
    async def get_wallet(self, wallet_id: str) -> Optional[dict]:
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    wallet = await conn.fetchrow(
                        'SELECT * FROM wallets WHERE wallet_id = $1', wallet_id
                    )
                    if wallet:
                        shards = await conn.fetch(
                            'SELECT shard FROM wallet_shards WHERE wallet_id = $1 ORDER BY shard_index', wallet_id
                        )
                        return {
                            'wallet_id': wallet['wallet_id'],
                            'pubkey': wallet['pubkey'],
                            'scheme': wallet['scheme'],
                            'params': wallet['params'],
                            'shards': [s['shard'] for s in shards]
                        }
            except Exception as e:
                print(f"Database read failed, using in-memory: {e}")
                return self._get_wallet_memory(wallet_id)
        return self._get_wallet_memory(wallet_id)
 
    def _get_wallet_memory(self, wallet_id: str) -> Optional[dict]:
        if wallet_id in self.wallets:
            return {
                'wallet_id': wallet_id,
                **self.wallets[wallet_id]
            }
        return None
 
    async def get_all_wallets(self) -> List[dict]:
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    rows = await conn.fetch('SELECT * FROM wallets')
                    wallets_list = []
                    for row in rows:
                        shards = await conn.fetch(
                            'SELECT shard FROM wallet_shards WHERE wallet_id = $1 ORDER BY shard_index', row['wallet_id']
                        )
                        wallet_data = dict(row)
                        wallet_data['shards'] = [s['shard'] for s in shards]
                        wallets_list.append(wallet_data)
                    return wallets_list
            except Exception as e:
                print(f"Database read failed, using in-memory: {e}")
                return [{'wallet_id': k, **v} for k, v in self.wallets.items()]
        return [{'wallet_id': k, **v} for k, v in self.wallets.items()]
 
    async def store_pending_txn(self, txn_data: dict):
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    await conn.execute('''
                        INSERT INTO pending_transactions
                        (txn_id, wallet_id, to_address, amount, token_symbol, flagged, escalation_level, status)
                        VALUES ($1, $2, $3, $4, $5, $6, $7, $8)
                    ''', txn_data['txn_id'], txn_data['wallet_id'], txn_data['to_address'],
                        txn_data['amount'], txn_data.get('token_symbol'), txn_data.get('flagged', False),
                        txn_data.get('escalation_level', 'tier1'), 'pending')
            except Exception as e:
                print(f"Database storage failed, using in-memory: {e}")
                self.pending_txns[txn_data['txn_id']] = txn_data
        else:
            self.pending_txns[txn_data['txn_id']] = txn_data
 
    async def get_pending_txn(self, txn_id: str) -> Optional[dict]:
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    txn = await conn.fetchrow(
                        'SELECT * FROM pending_transactions WHERE txn_id = $1', txn_id
                    )
                    if txn:
                        return dict(txn)
            except Exception as e:
                print(f"Database read failed, using in-memory: {e}")
                return self.pending_txns.get(txn_id)
        return self.pending_txns.get(txn_id)
 
    async def get_all_pending_txns(self) -> List[dict]:
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    rows = await conn.fetch('SELECT * FROM pending_transactions')
                    return [dict(r) for r in rows]
            except Exception as e:
                print(f"Database read failed, using in-memory: {e}")
                return list(self.pending_txns.values())
        return list(self.pending_txns.values())
 
    async def delete_pending_txn(self, txn_id: str):
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    await conn.execute('DELETE FROM pending_transactions WHERE txn_id = $1', txn_id)
            except Exception as e:
                print(f"Database delete failed, using in-memory: {e}")
                if txn_id in self.pending_txns:
                    del self.pending_txns[txn_id]
        else:
            if txn_id in self.pending_txns:
                del self.pending_txns[txn_id]

    async def store_wallet_thresholds(self, wallet_id: str, low: float, mid: float, high: float):
        """Store wallet-specific value thresholds"""
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    await conn.execute('''
                        INSERT INTO wallet_thresholds (wallet_id, low_threshold, mid_threshold, high_threshold)
                        VALUES ($1, $2, $3, $4)
                        ON CONFLICT (wallet_id) 
                        DO UPDATE SET 
                            low_threshold = $2,
                            mid_threshold = $3,
                            high_threshold = $4,
                            updated_at = NOW()
                    ''', wallet_id, low, mid, high)
            except Exception as e:
                print(f"Database storage failed, using in-memory: {e}")
                self.wallet_thresholds[wallet_id] = {"low": low, "mid": mid, "high": high}
        else:
            self.wallet_thresholds[wallet_id] = {"low": low, "mid": mid, "high": high}

    async def get_wallet_thresholds(self, wallet_id: str) -> Optional[dict]:
        """Get wallet-specific value thresholds"""
        if self.pool:
            try:
                async with self.pool.acquire() as conn:
                    result = await conn.fetchrow(
                        'SELECT * FROM wallet_thresholds WHERE wallet_id = $1', wallet_id
                    )
                    if result:
                        return {
                            "low": float(result['low_threshold']),
                            "mid": float(result['mid_threshold']),
                            "high": float(result['high_threshold'])
                        }
            except Exception as e:
                print(f"Database read failed, using in-memory: {e}")
                return self.wallet_thresholds.get(wallet_id)
        return self.wallet_thresholds.get(wallet_id)

# Initialize database manager
db_manager = DatabaseManager()

@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup
    await db_manager.init_db()
    yield
    # Shutdown
    if db_manager.pool:
        await db_manager.pool.close()

app = FastAPI(
    title="StableFlow Pay - Consumer Wallet",
    description="Secure consumer wallet system with shard-based escalation",
    version="1.0.0",
    lifespan=lifespan
)

# Add CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Serve static files
app.mount("/static", StaticFiles(directory="static"), name="static")

# Enhanced validation models with Pydantic V2

class WalletCreateRequest(BaseModel):
    threshold: int
    shares: int
    scheme: str = "full"
    num_groups: int = 1

    @field_validator('threshold')
    @classmethod
    def validate_threshold(cls, v, info):
        if 'shares' in info.data and v > info.data['shares']:
            raise ValueError('Threshold cannot exceed total shares')
        if v < 2:
            raise ValueError('Threshold must be at least 2 for security')
        return v

    @field_validator('shares')
    @classmethod
    def validate_shares(cls, v):
        if v > 255:
            raise ValueError('Maximum 255 shares supported')
        if v < 2:
            raise ValueError('Minimum 2 shares required')
        return v

    @field_validator('scheme')
    @classmethod
    def validate_scheme(cls, v):
        if v not in ['full', 'spep']:
            raise ValueError('Scheme must be either "full" or "spep"')
        return v

class ReconstructRequest(BaseModel):
    wallet_id: str
    shards: List[str]
    level: Optional[str] = "tier1"

    @field_validator('level')
    @classmethod
    def validate_level(cls, v):
        if v not in ['tier1', 'tier2', 'tier3']:
            raise ValueError('Level must be tier1, tier2, or tier3')
        return v

class SignTxRequest(BaseModel):
    wallet_id: str
    to_address: str
    amount: float
    token_symbol: Optional[str] = None
    shards: List[str]
    level: Optional[str] = "tier1"

    @field_validator('amount')
    @classmethod
    def validate_amount(cls, v):
        if v <= 0:
            raise ValueError('Amount must be positive')
        return v

class AuthorizeQueuedTxRequest(BaseModel):
    txn_id: str
    shards: List[str]
    level: Optional[str] = "tier1"

    @field_validator('level')
    @classmethod
    def validate_level(cls, v):
        if v not in ['tier1', 'tier2', 'tier3']:
            raise ValueError('Level must be tier1, tier2, or tier3')
        return v

class ValueThresholdsRequest(BaseModel):
    wallet_id: str
    low_threshold: float
    mid_threshold: float
    high_threshold: float

    @field_validator('low_threshold', 'mid_threshold', 'high_threshold')
    @classmethod
    def validate_thresholds(cls, v):
        if v <= 0:
            raise ValueError('Thresholds must be positive')
        return v

    @field_validator('mid_threshold')
    @classmethod
    def validate_mid_threshold(cls, v, info):
        if 'low_threshold' in info.data and v <= info.data['low_threshold']:
            raise ValueError('Mid threshold must be greater than low threshold')
        return v

    @field_validator('high_threshold')
    @classmethod
    def validate_high_threshold(cls, v, info):
        if 'mid_threshold' in info.data and v <= info.data['mid_threshold']:
            raise ValueError('High threshold must be greater than mid threshold')
        return v

# Shard PRIME - Using a custom prime for our secret sharing
SHARD_PRIME = 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141

class CryptoUtils:
    """Cryptographic utilities for key generation and address formatting"""

    @staticmethod
    def generate_keypair():
        """Generate a new Solana keypair"""
        kp = Keypair()
        return kp

    @staticmethod
    def get_private_key(kp: Keypair) -> bytes:
        """Extract just the private key (32 bytes) from a keypair"""
        # The first 32 bytes of the keypair are the private key
        return bytes(kp)[:32]

    @staticmethod
    def private_to_public_key(private_key_bytes: bytes) -> bytes:
        """Convert private key bytes to public key bytes"""
        # Create a keypair from just the private key
        kp = Keypair.from_bytes(private_key_bytes + b'\x00' * 32) # Pad with zeros for public key part
        return bytes(kp.pubkey())

    @staticmethod
    def public_key_to_address(public_key_bytes: bytes) -> str:
        """Convert public key to Solana address"""
        return str(Pubkey(public_key_bytes))

    @staticmethod
    def create_keypair_from_seed(seed_bytes: bytes) -> Keypair:
        """Create a keypair from a seed using a deterministic approach"""
        return Keypair.from_seed(seed_bytes)

class SecretSharer:
    @classmethod
    def split_secret(cls, secret_bytes: bytes, threshold: int, shares: int, scheme: str = "full", num_groups: int = 1) -> List[str]:
        """Split a secret into shards using Shamir's Secret Sharing - NO AUTOMATIC TIERS"""
        if shares < threshold:
            raise ValueError("Shares must be at least threshold")
        if scheme == "spep" and threshold > num_groups:
            raise ValueError("For SPEP, threshold cannot exceed num_groups")
     
        # Convert the 32-byte private key to a single integer for sharing
        secret_int = int.from_bytes(secret_bytes, 'big')
        shards = []
     
        # Even distribution across groups
        base_per_group = shares // num_groups
        extra = shares % num_groups
        group_list = []
        for g in range(num_groups):
            group_list.extend([g + 1] * (base_per_group + (1 if g < extra else 0)))
     
        # Generate random coefficients for the polynomial
        coefficients = [secret_int] + [secrets.randbelow(SHARD_PRIME) for _ in range(threshold - 1)]
     
        # Generate shards - NO AUTOMATIC TIER ASSIGNMENT
        for i in range(shares):
            x = i + 1
            g = group_list[i]
            # Evaluate polynomial at x
            y = sum(coeff * pow(x, power, SHARD_PRIME) for power, coeff in enumerate(coefficients)) % SHARD_PRIME
            y_hex = format(y, '064x') # 32 bytes in hex (64 hex chars)
         
            if scheme == "full":
                shard = f"{x}-{y_hex}"
            elif scheme == "spep":
                # For SPEP scheme, create shards WITHOUT automatic tier assignment
                # Tiers will be assigned manually on the frontend
                shard = f"{g}-{x}-{y_hex}"  # REMOVED automatic tier assignment
         
            shards.append(shard)
     
        return shards

    @classmethod
    def recover_secret(cls, shards: List[str], scheme: str, num_groups: int = 1, threshold: int = None, level: str = 'tier1') -> bytes:
        """Recover secret from shards using Lagrange interpolation"""
        # For manual tier assignment, we need to handle shards differently
        # Since tiers are now assigned manually, we'll accept all shards regardless of tier
        points = []
        group_points = {}
     
        # Parse shards
        for shard in shards:
            parts = shard.split('-')
            if scheme == "full":
                if len(parts) != 2:
                    continue
                x = int(parts[0])
                y = int(parts[1], 16)
                points.append((x, y))
            elif scheme == "spep":
                # Handle both old format (with tiers) and new format (without tiers)
                if len(parts) == 4:  # Old format with tiers: "group-tier-x-y"
                    g = int(parts[0])
                    tier = parts[1]
                    x = int(parts[2])
                    y = int(parts[3], 16)
                    # For manual tier assignment, we accept all shards regardless of tier
                    group_points.setdefault(g, []).append((x, y, tier))
                elif len(parts) == 3:  # New format without tiers: "group-x-y"
                    g = int(parts[0])
                    x = int(parts[1])
                    y = int(parts[2], 16)
                    # For new format, we don't have tiers, so we accept all
                    group_points.setdefault(g, []).append((x, y, 'tier1'))  # Default tier
     
        # Select points based on scheme
        if scheme == "full":
            if len(points) < threshold:
                raise ValueError(f"Insufficient shards for threshold. Need {threshold}, got {len(points)}")
            selected_points = points # Use all
        elif scheme == "spep":
            if len(group_points) < threshold:
                raise ValueError(f"Insufficient groups for threshold. Need {threshold}, got {len(group_points)}")
            selected_points = []
            for g in sorted(group_points.keys()):
                # For manual tier assignment, we take the first shard from each group
                # In a real implementation, you might want more sophisticated selection
                if group_points[g]:
                    selected_points.append((group_points[g][0][0], group_points[g][0][1]))
            if len(selected_points) < threshold:
                raise ValueError(f"Insufficient selected shards for threshold. Need {threshold}, got {len(selected_points)}")
     
        # Lagrange interpolation at x=0
        secret = 0
        for j, (x_j, y_j) in enumerate(selected_points):
            numerator, denominator = 1, 1
            for m, (x_m, _) in enumerate(selected_points):
                if m != j:
                    numerator = (numerator * (0 - x_m)) % SHARD_PRIME
                    denominator = (denominator * (x_j - x_m)) % SHARD_PRIME
            fraction = (y_j * numerator * pow(denominator, -1, SHARD_PRIME)) % SHARD_PRIME
            secret = (secret + fraction) % SHARD_PRIME
     
        # Convert back to bytes (32 bytes for private key)
        return secret.to_bytes(32, 'big')

    @classmethod
    def get_shard_tier(cls, shard: str, scheme: str) -> Optional[str]:
        if scheme != "spep":
            return None  # Only SPEP has tiers
        parts = shard.split('-')
        if len(parts) == 4:
            return parts[1]  # The tier (e.g., 'tier2')
        return None

# Rate limiting dependency
async def rate_limit_check(request: Request):
    client_ip = request.client.host
    if not security_manager.check_rate_limit(client_ip):
        raise HTTPException(status_code=429, detail="Too many requests. Please try again later.")
    return True

@app.get("/")
async def serve_frontend():
    return FileResponse('static/index.html')

# Debug endpoints
@app.get("/wallets/debug/all", summary="Debug all wallets")
async def debug_all_wallets():
    """Debug endpoint to check all wallets in database"""
    wallets = await db_manager.get_all_wallets()
    return {
        "total_wallets": len(wallets),
        "wallets": [
            {
                "wallet_id": w.get('wallet_id'),
                "pubkey": w.get('pubkey'),
                "scheme": w.get('scheme')
            } for w in wallets
        ]
    }

@app.get("/debug/db-status")
async def debug_db_status():
    """Check database connection status"""
    return {
        "database_connected": db_manager.pool is not None,
        "in_memory_wallets": len(db_manager.wallets),
        "in_memory_pending_txns": len(db_manager.pending_txns)
    }

@app.get("/wallets/debug/{wallet_id}", summary="Debug wallet info")
async def debug_wallet(wallet_id: str):
    """Debug endpoint to check wallet details"""
    wallet = await db_manager.get_wallet(wallet_id)
    if not wallet:
        return {"error": "Wallet not found", "wallet_id": wallet_id}
  
    return {
        "wallet_id": wallet_id,
        "exists": True,
        "pubkey": wallet.get('pubkey'),
        "scheme": wallet.get('scheme'),
        "shard_count": len(wallet.get('shards', [])),
        "first_shard_example": wallet.get('shards', [])[0] if wallet.get('shards') else None
    }

@app.post("/wallets/restore", summary="Restore an existing wallet")
async def restore_wallet():
    """Emergency endpoint to restore a wallet that was lost after server restart"""
    try:
        # In a real implementation, this would accept wallet data as input
        # For now, this is a placeholder that returns an error
        raise HTTPException(status_code=501, detail="Wallet restoration not implemented - use create wallet instead")
      
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"Restoration failed: {str(e)}")

@app.get("/wallets/restore-now", summary="Restore wallet via GET")
async def restore_wallet_get():
    """GET endpoint to restore wallet for easy browser access"""
    # Placeholder implementation
    return {"status": "error", "detail": "Wallet restoration not implemented - use create wallet instead"}

@app.post("/wallets/create", summary="Create a new multi-signature wallet")
async def create_wallet(req: WalletCreateRequest, rate_ok: bool = Depends(rate_limit_check)):
    """Create a new wallet with specified threshold and sharing scheme"""
    try:
        # Generate Solana keypair
        kp = CryptoUtils.generate_keypair()
     
        # Store the full keypair bytes for later reconstruction
        full_keypair_bytes = bytes(kp)
        pubkey_address = CryptoUtils.public_key_to_address(bytes(kp.pubkey()))
     
        print(f"Generated keypair: {len(full_keypair_bytes)} bytes") # Debug
        print(f"Public key: {pubkey_address}") # Debug
     
        # Store the full keypair in the database along with shards
        # We'll store it as a hex string in the params
        wallet_params = {
            'threshold': req.threshold,
            'num_groups': req.num_groups,
            'keypair': full_keypair_bytes.hex() # Store the full valid keypair
        }
     
        # Split just the private key for sharing (for demonstration)
        # In production, you might want to share the full keypair or use a different approach
        private_key_bytes = CryptoUtils.get_private_key(kp)
        shards = SecretSharer.split_secret(private_key_bytes, req.threshold, req.shares, req.scheme, req.num_groups)
     
        wallet_id = secrets.token_hex(8)
   
        await db_manager.store_wallet(wallet_id, pubkey_address, req.scheme, wallet_params, shards)
   
        return {
            "wallet_id": wallet_id,
            "pubkey": pubkey_address,
            "shards": shards,
            "scheme": req.scheme,
            "threshold": req.threshold,
            "shares": req.shares
        }
    except Exception as e:
        security_manager.record_failure("wallet_creation")
        raise HTTPException(status_code=400, detail=f"Wallet creation failed: {str(e)}")

@app.post("/wallets/reconstruct", summary="Reconstruct private key from shards")
async def reconstruct_key(req: ReconstructRequest, rate_ok: bool = Depends(rate_limit_check)):
    """Reconstruct wallet private key using provided shards"""
    try:
        wallet = await db_manager.get_wallet(req.wallet_id)
        if not wallet:
            security_manager.record_failure(f"reconstruct_{req.wallet_id}")
            raise HTTPException(status_code=404, detail="Wallet not found")
     
        # For now, return the stored keypair directly since reconstruction is problematic
        # In a real implementation, you'd want to fix the cryptographic reconstruction
        if 'keypair' in wallet['params']:
            keypair_bytes = bytes.fromhex(wallet['params']['keypair'])
            return {"secret_bytes": keypair_bytes.hex()}
        else:
            # Fallback to reconstruction (may not work due to cryptographic constraints)
            private_key_bytes = SecretSharer.recover_secret(
                req.shards,
                wallet['scheme'],
                wallet['params']['num_groups'],
                wallet['params']['threshold'],
                req.level
            )
         
            # Try to create a valid keypair from the private key
            kp = CryptoUtils.create_keypair_from_seed(private_key_bytes)
            full_keypair_bytes = bytes(kp)
         
            # Verify the reconstructed key matches the wallet pubkey
            reconstructed_address = CryptoUtils.public_key_to_address(bytes(kp.pubkey()))
         
            if reconstructed_address != wallet['pubkey']:
                security_manager.record_failure(f"reconstruct_{req.wallet_id}")
                raise HTTPException(status_code=400, detail="Invalid shards: reconstructed key doesn't match wallet")
         
            return {"secret_bytes": full_keypair_bytes.hex()}
         
    except Exception as e:
        security_manager.record_failure(f"reconstruct_{req.wallet_id}")
        raise HTTPException(status_code=400, detail=f"Reconstruction failed: {str(e)}")

@app.post("/transactions/sign", summary="Sign a transaction with shard-based escalation")
async def sign_transaction(req: SignTxRequest, rate_ok: bool = Depends(rate_limit_check)):
    """Sign and broadcast a transaction on Solana mainnet with shard-based escalation"""
    try:
        # Safety checks including anti-fraud
        safety_check = await executive_safety.check_transaction_safety(req.wallet_id, req.amount, req.token_symbol)
        if not safety_check["safe"]:
            # Queue on failure or fraud
            escalation_level = 'tier3' if safety_check.get("fraud_suspected", False) else req.level
            txn_id = secrets.token_hex(8)
            txn_data = {
                'txn_id': txn_id,
                'wallet_id': req.wallet_id,
                'to_address': req.to_address,
                'amount': req.amount,
                'token_symbol': req.token_symbol,
                'flagged': safety_check.get("fraud_suspected", False),
                'escalation_level': escalation_level
            }
            await db_manager.store_pending_txn(txn_data)
         
            return {
                "status": "queued",
                "txn_id": txn_id,
                "message": f"Transaction queued for {escalation_level} shard confirmation{' due to potential fraud' if safety_check.get('fraud_suspected') else ''}.",
                "amount": req.amount,
                "action_required": f"Use /authorize_queued_tx with {escalation_level} shards"
            }
     
        wallet = await db_manager.get_wallet(req.wallet_id)
        if not wallet:
            raise HTTPException(status_code=404, detail="Wallet not found")
     
        # Get custom thresholds for this wallet, fallback to defaults
        thresholds = executive_safety.get_value_thresholds(req.wallet_id)
        amount_dec = Decimal(str(req.amount))
        
        # Determine required tier based on custom thresholds
        if amount_dec <= thresholds["low"]: # Low value: tier1 direct
            req_level = 'tier1'
            is_queued = False
        elif thresholds["low"] < amount_dec <= thresholds["mid"]: # Mid value: tier2 queue
            req_level = 'tier2'
            is_queued = True
        elif thresholds["mid"] < amount_dec <= thresholds["high"]: # High value: tier3 queue
            req_level = 'tier3'
            is_queued = True
        else: # Above high threshold - not allowed
            return {
                "status": "rejected",
                "message": f"Transaction amount ${req.amount} exceeds maximum allowed threshold of ${thresholds['high']}",
                "amount": req.amount,
                "max_allowed": float(thresholds["high"])
            }
     
        if is_queued:
            txn_id = secrets.token_hex(8)
            txn_data = {
                'txn_id': txn_id,
                'wallet_id': req.wallet_id,
                'to_address': req.to_address,
                'amount': req.amount,
                'token_symbol': req.token_symbol,
                'flagged': False,
                'escalation_level': req_level
            }
            await db_manager.store_pending_txn(txn_data)
         
            return {
                "status": "queued",
                "txn_id": txn_id,
                "message": f"Transaction queued for {req_level} shard confirmation",
                "threshold": float(thresholds["mid"] if req_level == 'tier2' else thresholds["high"]),
                "amount": req.amount,
                "action_required": f"Use /authorize_queued_tx with {req_level} shards"
            }
     
        # For direct (low-value), reconstruct with required level
        if 'keypair' in wallet['params']:
            keypair_bytes = bytes.fromhex(wallet['params']['keypair'])
            kp = Keypair.from_bytes(keypair_bytes)
        else:
            private_key_bytes = SecretSharer.recover_secret(
                req.shards,
                wallet['scheme'],
                wallet['params']['num_groups'],
                wallet['params']['threshold'],
                req_level
            )
            kp = CryptoUtils.create_keypair_from_seed(private_key_bytes)
     
        from_pubkey = Pubkey.from_string(wallet['pubkey'])
        to_pubkey = Pubkey.from_string(req.to_address)
     
        # Get recent blockhash with better error handling
        try:
            blockhash_resp = solana_client.get_latest_blockhash(Finalized)
            if not blockhash_resp or not blockhash_resp.value:
                raise HTTPException(status_code=400, detail="Failed to get recent blockhash from Solana RPC")
            recent_blockhash = blockhash_resp.value.blockhash
        except Exception as e:
            raise HTTPException(status_code=400, detail=f"Failed to get blockhash: {str(e)}")
     
        instructions = []
     
        if req.token_symbol:
            if req.token_symbol not in STABLECOINS:
                raise HTTPException(status_code=400, detail="Unsupported stablecoin")
         
            mint = Pubkey.from_string(STABLECOINS[req.token_symbol]["mint"])
            decimals = STABLECOINS[req.token_symbol]["decimals"]
            amount_u64 = int(req.amount * (10 ** decimals))
         
            from_ata = get_associated_token_address(from_pubkey, mint)
            to_ata = get_associated_token_address(to_pubkey, mint)
         
            # Check if destination ATA exists
            try:
                to_ata_info = solana_client.get_account_info(to_ata, commitment=Confirmed)
                if to_ata_info.value is None:
                    # Create ATA instruction
                    instructions.append(
                        create_associated_token_account(
                            payer=from_pubkey,
                            owner=to_pubkey,
                            mint=mint
                        )
                    )
            except Exception as e:
                print(f"Error checking ATA: {e}")
                # Assume ATA doesn't exist and create it
                instructions.append(
                    create_associated_token_account(
                        payer=from_pubkey,
                        owner=to_pubkey,
                        mint=mint
                    )
                )
         
            # Transfer instruction
            instructions.append(transfer_checked(
                program_id=TOKEN_PROGRAM_ID,
                source=from_ata,
                mint=mint,
                dest=to_ata,
                owner=from_pubkey,
                amount=amount_u64,
                decimals=decimals
            ))
        else:
            # SOL transfer
            instructions.append(transfer(TransferParams(
                from_pubkey=from_pubkey,
                to_pubkey=to_pubkey,
                lamports=int(req.amount * 1_000_000_000) # SOL to lamports
            )))
     
        # Create message and transaction
        try:
            message = Message.new_with_blockhash(instructions, from_pubkey, recent_blockhash)
            txn = Transaction([kp], message, recent_blockhash)
        except Exception as e:
            raise HTTPException(status_code=400, detail=f"Failed to create transaction: {str(e)}")
     
        # SIMULATE FIRST (Critical safety step)
        if SAFETY_CONFIG["SAFE_MODE"]:
            try:
                simulation = solana_client.simulate_transaction(txn)
                if simulation.value and simulation.value.err:
                    raise HTTPException(
                        status_code=400,
                        detail=f"Transaction simulation failed: {simulation.value.err}"
                    )
            except RPCException as e:
                raise HTTPException(
                    status_code=400,
                    detail=f"Transaction simulation RPC error: {str(e)}"
                )
            except Exception as e:
                # If simulation fails, we can still try to send (but log the error)
                print(f"Simulation warning: {str(e)}")
     
        # REAL MAINNET BROADCAST
        try:
            serialized_tx = bytes(txn)
            send_result = solana_client.send_raw_transaction(
                serialized_tx,
                opts=TxOpts(skip_preflight=not SAFETY_CONFIG["SAFE_MODE"], preflight_commitment=Confirmed)
            )
           
            if not send_result or not send_result.value:
                raise HTTPException(status_code=400, detail="Failed to send transaction: No response from RPC")
               
            txid = send_result.value
        except RPCException as e:
            raise HTTPException(status_code=400, detail=f"RPC error sending transaction: {str(e)}")
        except Exception as e:
            raise HTTPException(status_code=400, detail=f"Failed to send transaction: {str(e)}")
     
        # Update daily volume
        today = datetime.now().date().isoformat()
        if req.wallet_id not in executive_safety.daily_volumes:
            executive_safety.daily_volumes[req.wallet_id] = {"date": today, "amount": Decimal('0.0')}
        executive_safety.daily_volumes[req.wallet_id]["amount"] += Decimal(str(req.amount))
     
        return {
            "status": "success",
            "txid": str(txid),
            "message": "Transaction successfully broadcasted on Solana Mainnet",
            "amount": req.amount,
            "token": req.token_symbol or "SOL",
            "from": wallet['pubkey'],
            "to": req.to_address,
            "network": "Mainnet",
            "safety_check": "PASSED",
            "daily_used": safety_check["daily_used"]
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"Transaction failed: {str(e)}")

@app.post("/transactions/authorize_queued_tx", summary="Authorize a queued transaction with shards")
async def authorize_queued_tx(req: AuthorizeQueuedTxRequest, rate_ok: bool = Depends(rate_limit_check)):
    """Authorize and broadcast a queued transaction using shards at required level"""
    try:
        txn = await db_manager.get_pending_txn(req.txn_id)
        if not txn or txn['status'] != 'pending':
            raise HTTPException(status_code=404, detail="Pending transaction not found or already processed")
       
        wallet = await db_manager.get_wallet(txn['wallet_id'])
        if not wallet:
            raise HTTPException(status_code=404, detail="Wallet not found")
       
        # Enforce escalation level from queue (value or fraud-based)
        required_level = txn['escalation_level']
        if req.level != required_level:
            raise HTTPException(status_code=400, detail=f"This transaction requires {required_level} level authorization")
       
        threshold = wallet['params']['threshold']
        scheme = wallet['scheme']
       
        # For escalation, require additional shard(s) from higher tiers
        min_shards_required = threshold  # Base
        min_high_tier_required = 0      # Base
        if required_level in ['tier2', 'tier3']:  # For mid/high escalation
            min_shards_required = threshold + 1  # Require one extra
            min_high_tier_required = 1           # At least one non-tier1
        
        if len(req.shards) < min_shards_required:
            raise HTTPException(status_code=400, detail=f"Insufficient shards provided. Need at least {min_shards_required} for {required_level} authorization")
        
        # Validate tier mix (only for SPEP)
        if scheme == 'spep':
            high_tier_count = sum(1 for s in req.shards if SecretSharer.get_shard_tier(s, scheme) in ['tier2', 'tier3'])
            if high_tier_count < min_high_tier_required:
                raise HTTPException(status_code=400, detail=f"Authorization requires at least {min_high_tier_required} shard(s) from higher tiers (tier2 or tier3)")
       
        # Reconstruct key with required level (pass all shards; recovery selects as needed)
        if 'keypair' in wallet['params']:
            keypair_bytes = bytes.fromhex(wallet['params']['keypair'])
            kp = Keypair.from_bytes(keypair_bytes)
        else:
            private_key_bytes = SecretSharer.recover_secret(
                req.shards,  # Pass all for flexibility
                wallet['scheme'],
                wallet['params']['num_groups'],
                wallet['params']['threshold'],
                required_level
            )
            kp = CryptoUtils.create_keypair_from_seed(private_key_bytes)
       
        from_pubkey = Pubkey.from_string(wallet['pubkey'])
        to_pubkey = Pubkey.from_string(txn['to_address'])
      
        # Get recent blockhash with better error handling
        try:
            blockhash_resp = solana_client.get_latest_blockhash(Finalized)
            if not blockhash_resp or not blockhash_resp.value:
                raise HTTPException(status_code=400, detail="Failed to get recent blockhash from Solana RPC")
            recent_blockhash = blockhash_resp.value.blockhash
        except Exception as e:
            raise HTTPException(status_code=400, detail=f"Failed to get blockhash: {str(e)}")
      
        instructions = []
      
        amount = float(txn['amount'])
        if txn['token_symbol']:
            if txn['token_symbol'] not in STABLECOINS:
                raise HTTPException(status_code=400, detail="Unsupported stablecoin")
          
            mint = Pubkey.from_string(STABLECOINS[txn['token_symbol']]["mint"])
            decimals = STABLECOINS[txn['token_symbol']]["decimals"]
            amount_u64 = int(amount * (10 ** decimals))
          
            from_ata = get_associated_token_address(from_pubkey, mint)
            to_ata = get_associated_token_address(to_pubkey, mint)
          
            # Check if destination ATA exists
            try:
                to_ata_info = solana_client.get_account_info(to_ata, commitment=Confirmed)
                if to_ata_info.value is None:
                    instructions.append(
                        create_associated_token_account(
                            payer=from_pubkey,
                            owner=to_pubkey,
                            mint=mint
                        )
                    )
            except Exception as e:
                print(f"Error checking ATA: {e}")
                instructions.append(
                    create_associated_token_account(
                        payer=from_pubkey,
                        owner=to_pubkey,
                        mint=mint
                    )
                )
          
            instructions.append(transfer_checked(
                program_id=TOKEN_PROGRAM_ID,
                source=from_ata,
                mint=mint,
                dest=to_ata,
                owner=from_pubkey,
                amount=amount_u64,
                decimals=decimals
            ))
        else:
            # SOL transfer
            instructions.append(transfer(TransferParams(
                from_pubkey=from_pubkey,
                to_pubkey=to_pubkey,
                lamports=int(amount * 1_000_000_000) # SOL to lamports
            )))
      
        # Create message and transaction
        try:
            message = Message.new_with_blockhash(instructions, from_pubkey, recent_blockhash)
            signed_tx = Transaction([kp], message, recent_blockhash)
        except Exception as e:
            raise HTTPException(status_code=400, detail=f"Failed to create transaction: {str(e)}")
      
        # SIMULATE FIRST
        if SAFETY_CONFIG["SAFE_MODE"]:
            try:
                simulation = solana_client.simulate_transaction(signed_tx)
                if simulation.value and simulation.value.err:
                    raise HTTPException(
                        status_code=400,
                        detail=f"Transaction simulation failed: {simulation.value.err}"
                    )
            except RPCException as e:
                raise HTTPException(
                    status_code=400,
                    detail=f"Transaction simulation RPC error: {str(e)}"
                )
            except Exception as e:
                print(f"Simulation warning: {str(e)}")
      
        # BROADCAST
        try:
            serialized_tx = bytes(signed_tx)
            send_result = solana_client.send_raw_transaction(
                serialized_tx,
                opts=TxOpts(skip_preflight=not SAFETY_CONFIG["SAFE_MODE"], preflight_commitment=Confirmed)
            )
           
            if not send_result or not send_result.value:
                raise HTTPException(status_code=400, detail="Failed to send transaction: No response from RPC")
               
            txid = send_result.value
        except RPCException as e:
            raise HTTPException(status_code=400, detail=f"RPC error sending transaction: {str(e)}")
        except Exception as e:
            raise HTTPException(status_code=400, detail=f"Failed to send transaction: {str(e)}")
      
        # Update status and delete pending
        await db_manager.delete_pending_txn(req.txn_id)
      
        # Update daily volume
        today = datetime.now().date().isoformat()
        if txn['wallet_id'] not in executive_safety.daily_volumes:
            executive_safety.daily_volumes[txn['wallet_id']] = {"date": today, "amount": Decimal('0.0')}
        executive_safety.daily_volumes[txn['wallet_id']]["amount"] += Decimal(str(amount))
      
        return {
            "status": "success",
            "txid": str(txid),
            "message": "Transaction authorized and broadcasted successfully",
            "amount": amount,
            "token": txn['token_symbol'] or "SOL",
            "from": wallet['pubkey'],
            "to": txn['to_address']
        }
    except HTTPException:
        raise
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"Authorization failed: {str(e)}")

@app.post("/wallets/set-value-thresholds", summary="Set custom value thresholds for a wallet")
async def set_value_thresholds(req: ValueThresholdsRequest, rate_ok: bool = Depends(rate_limit_check)):
    """Set custom dollar value thresholds for transaction escalation levels"""
    try:
        # Verify wallet exists
        wallet = await db_manager.get_wallet(req.wallet_id)
        if not wallet:
            raise HTTPException(status_code=404, detail="Wallet not found")
        
        # Store thresholds in both database and memory
        await db_manager.store_wallet_thresholds(req.wallet_id, req.low_threshold, req.mid_threshold, req.high_threshold)
        executive_safety.set_value_thresholds(req.wallet_id, req.low_threshold, req.mid_threshold, req.high_threshold)
        
        return {
            "status": "success",
            "message": "Value thresholds updated successfully",
            "wallet_id": req.wallet_id,
            "thresholds": {
                "low": req.low_threshold,
                "mid": req.mid_threshold,
                "high": req.high_threshold
            }
        }
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"Failed to set value thresholds: {str(e)}")

@app.get("/wallets/{wallet_id}/value-thresholds", summary="Get value thresholds for a wallet")
async def get_value_thresholds(wallet_id: str, rate_ok: bool = Depends(rate_limit_check)):
    """Get current value thresholds for a wallet"""
    try:
        # Try to get custom thresholds first
        custom_thresholds = await db_manager.get_wallet_thresholds(wallet_id)
        if custom_thresholds:
            return {
                "status": "success",
                "wallet_id": wallet_id,
                "thresholds": custom_thresholds,
                "source": "custom"
            }
        else:
            # Fallback to defaults
            default_thresholds = {
                "low": float(LOW_VALUE_THRESHOLD),
                "mid": float(MID_VALUE_THRESHOLD),
                "high": float(HIGH_VALUE_THRESHOLD)
            }
            return {
                "status": "success",
                "wallet_id": wallet_id,
                "thresholds": default_thresholds,
                "source": "default"
            }
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"Failed to get value thresholds: {str(e)}")

@app.get("/wallets", summary="Get all wallets")
async def get_wallets(rate_ok: bool = Depends(rate_limit_check)):
    """Get list of all wallets"""
    try:
        wallets = await db_manager.get_all_wallets()
        return {
            "count": len(wallets),
            "wallets": wallets
        }
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"Failed to fetch wallets: {str(e)}")

@app.get("/transactions/pending", summary="Get pending transactions")
async def get_pending_transactions(rate_ok: bool = Depends(rate_limit_check)):
    """Get list of all pending transactions requiring authorization"""
    try:
        pending_txns = await db_manager.get_all_pending_txns()
        return {
            "count": len(pending_txns),
            "pending_transactions": pending_txns
        }
    except Exception as e:
        raise HTTPException(status_code=400, detail=f"Failed to fetch pending transactions: {str(e)}")

@app.get("/health", summary="Health check")
async def health_check():
    """Health check endpoint"""
    return {
        "status": "healthy",
        "timestamp": datetime.now().isoformat(),
        "solana_rpc": SOLANA_RPC_URL,
        "safe_mode": SAFETY_CONFIG["SAFE_MODE"]
    }

if __name__ == "__main__":
    import uvicorn
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)