#!/usr/bin/env python3
"""Check SHA-256 of all manifest entries; reject missing or changed files."""
from pathlib import Path
import hashlib
import sys

root = Path(__file__).resolve().parent
errors = []
lines = (root / 'SHA256SUMS').read_text().splitlines()
for line in lines:
    expected, name = line.split('  ', 1)
    path = root / name
    if not path.resolve().is_relative_to(root):
        errors.append('Invalid manifest path: ' + name)
    elif not path.is_file():
        errors.append('Missing: ' + name)
    elif hashlib.sha256(path.read_bytes()).hexdigest() != expected:
        errors.append('Changed: ' + name)
for error in errors:
    print(error, file=sys.stderr)
print(f'{len(lines)} manifest entries; {len(errors)} errors.')
sys.exit(bool(errors))
