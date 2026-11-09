#!/bin/sh
# Regenerate into a temporary directory, then compare with the checked files.
set -eu
cd "$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
source_dir=$(pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT HUP INT TERM
for name in kernel.py base_build.py build_branching.py build_extensions.py export_rocq.py; do
  cp "$name" "$work/$name"
done
(cd "$work" && PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=197 python3 build_extensions.py &&
  PYTHONDONTWRITEBYTECODE=1 PYTHONHASHSEED=197 python3 export_rocq.py)
cmp "$source_dir/proof.json" "$work/proof.json"
cmp "$source_dir/WellFoundedUnionsProofTerms.v" "$work/WellFoundedUnionsProofTerms.v"
printf '%s\n' 'PASS: certificate and explicit proof-term export regenerate byte for byte.'
