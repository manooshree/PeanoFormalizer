import os
import json
import hashlib

# Load or initialize caches
def load_cache(cache_file):
    if os.path.exists(cache_file):
        with open(cache_file, 'r') as f:
            try:
                return json.load(f)
            except json.JSONDecodeError:
                return {}
    return {}

# tactic_cache = load_cache(TACTIC_CACHE_FILE)
# goal_cache = load_cache(GOAL_CACHE_FILE)

def save_cache(cache, cache_file):
    with open(cache_file, 'w') as f:
        json.dump(cache, f)

def create_cache_key(data):
    """Create a deterministic cache key from input data"""
    serialized = json.dumps(data, sort_keys=True)
    return hashlib.md5(serialized.encode()).hexdigest()