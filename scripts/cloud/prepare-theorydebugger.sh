#!/usr/bin/env bash
# SPDX-License-Identifier: Unlicense
# Fetch TheoryDebugger's Mathlib files (the module list its CI uses) and build
# its Lean library, so `python -m theorydebugger` can kernel-check certificates.
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$here/env.sh"
cd "$THEORYDEBUGGER_HOME"

modules=$(grep -m1 'lake exe cache get' .github/workflows/check.yml |
          grep -o 'Mathlib\.[A-Za-z0-9_.]*' || true)
if [ -z "$modules" ]; then
  echo "No Mathlib module list found in TheoryDebugger's CI workflow" >&2
  exit 1
fi
lake exe cache get $modules
lake build
