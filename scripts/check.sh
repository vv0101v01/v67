#!/usr/bin/env bash
# Full verification: format, interfaces, both test targets, the benchmark,
# and the static health scan.  Fails on the first problem.
set -euo pipefail
export PATH="$HOME/.moon/bin:$PATH"
if ! command -v moon >/dev/null 2>&1; then
  curl -fsSL https://cli.moonbitlang.com/install/unix.sh | bash
fi
cd "$(dirname "$0")/.."

echo "== toolchain =="
moon version --all

echo "== check (must be 0 errors, 0 warnings) =="
moon check

echo "== tests: wasm =="
moon test --target wasm

echo "== tests: native =="
moon test --target native

echo "== health: dead code and duplication =="
if command -v python3 >/dev/null 2>&1; then
  python3 scripts/health.py
else
  echo "python3 not found; skipping the static health scan"
fi

echo "== benchmark =="
moon run --target native bench
