"""Stable semantic identity of a validated Protocol IR model."""
import hashlib
import json


def model_hash(model):
    return hashlib.sha256(json.dumps(model, sort_keys=True, separators=(",", ":")).encode()).hexdigest()
