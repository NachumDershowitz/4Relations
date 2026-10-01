#!/usr/bin/env python3
"""Check the release manifest, then reproduce the finite-coverage audit."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]

def main():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    for name, expected in manifest["files"].items():
        path = ROOT / name
        if not path.is_file():
            raise ValueError("Missing archive file: " + name)
        content = path.read_bytes()
        if len(content) != expected["bytes"] or hashlib.sha256(content).hexdigest() != expected["sha256"]:
            raise ValueError("Changed archive file: " + name)
    print(f"Verified {len(manifest['files'])} files against MANIFEST.json.", flush=True)
    subprocess.run([sys.executable, str(ROOT / "verification/verify_results.py")], check=True)
    print("Archive integrity and finite-coverage checks passed.")

if __name__ == "__main__":
    main()
