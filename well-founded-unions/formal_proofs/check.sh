#!/bin/sh
set -eu
cd "$(dirname "$0")"
proof_tmp=$(mktemp -d "${TMPDIR:-/tmp}/four-relations-check.XXXXXX")
trap 'rm -rf "$proof_tmp"' EXIT HUP INT TERM
cp FourRelationsCounterexample.v "$proof_tmp/"
cd "$proof_tmp"
rocq --version
rocq compile FourRelationsCounterexample.v
rocq check -silent FourRelationsCounterexample
printf '%s\n' 'Compilation and independent kernel check succeeded.'
