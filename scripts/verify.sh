#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
lake build
lake env lean --trust=0 -DmaxRecDepth=100000 -DmaxHeartbeats=0 verification/Audit.lean
python3 research/verify_witness.py
