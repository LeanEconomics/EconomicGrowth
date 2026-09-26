#!/usr/bin/env bash
# SPDX-License-Identifier: Unlicense
# Fetch the prebuilt Mathlib files one growth project imports, as CI does.
# Usage: scripts/cloud/prepare-project.sh <SolowSwan|Uzawa|RamseyCassKoopmans>
set -euo pipefail
here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
source "$here/env.sh"
project="${1:?usage: prepare-project.sh <SolowSwan|Uzawa|RamseyCassKoopmans>}"
cd "$here/../../$project"

python3 - <<'PY'
import json, subprocess
from pathlib import Path
config = json.loads(Path('proof-manifest.json').read_text())
imports = {line.removeprefix('import ') for name in config['modules']
           for line in Path(name).read_text().splitlines()
           if line.startswith('import Mathlib.')}
subprocess.run(['lake', 'exe', 'cache', 'get', *sorted(imports)], check=True)
PY
