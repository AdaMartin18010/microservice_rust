#!/usr/bin/env bash
set -euo pipefail
ROOT_DIR="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT_DIR"

echo "==> Running linkcheck"
bash ./scripts/linkcheck.sh

echo "==> Running stylecheck (skipped on Unix)"
echo "Tip: run stylecheck on Windows: scripts/stylecheck.ps1"

echo "All doc checks passed."


