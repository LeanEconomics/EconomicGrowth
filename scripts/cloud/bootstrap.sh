#!/usr/bin/env bash
# SPDX-License-Identifier: Unlicense
# Install what cloud sessions need outside any one Lake project: the elan
# release pinned in CI, and TheoryDebugger with its Python adapter (cvc5).
# Idempotent; safe to rerun.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$here/env.sh"

ELAN_VERSION=v4.2.4
THEORYDEBUGGER_URL=https://github.com/mvazcar/TheoryDebugger.git

if ! command -v elan >/dev/null; then
  tmp="$(mktemp -d)"
  curl --fail --location --silent --show-error \
    "https://github.com/leanprover/elan/releases/download/$ELAN_VERSION/elan-x86_64-unknown-linux-gnu.tar.gz" \
    -o "$tmp/elan.tar.gz"
  tar xzf "$tmp/elan.tar.gz" -C "$tmp"
  "$tmp/elan-init" -y --no-modify-path --default-toolchain none
  rm -rf "$tmp"
fi
elan --version

if [ ! -d "$THEORYDEBUGGER_HOME/.git" ]; then
  git clone --depth 1 "$THEORYDEBUGGER_URL" "$THEORYDEBUGGER_HOME"
fi
git -C "$THEORYDEBUGGER_HOME" log -1 --format='TheoryDebugger %h %s'

if [ ! -x "$THEORYDEBUGGER_VENV/bin/python" ]; then
  python3 -m venv "$THEORYDEBUGGER_VENV"
fi
if ! "$THEORYDEBUGGER_VENV/bin/python" -c 'import cvc5, theorydebugger' 2>/dev/null; then
  "$THEORYDEBUGGER_VENV/bin/python" -m pip install --quiet -e "$THEORYDEBUGGER_HOME"
fi
"$THEORYDEBUGGER_VENV/bin/python" -c 'import cvc5; print("cvc5", cvc5.Solver().getVersion().decode())'
