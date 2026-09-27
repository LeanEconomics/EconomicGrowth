#!/usr/bin/env bash
# SPDX-License-Identifier: Unlicense
# SessionStart hook (.claude/settings.json). In Claude Code cloud sessions it
# installs elan and TheoryDebugger and fetches Mathlib caches for the projects
# in GROWTH_PROJECTS (default: Uzawa). Local sessions exit immediately.
# Every step is idempotent, so rerunning by hand is safe. The summary printed
# at the end becomes context for the session.
set -uo pipefail
[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0

here="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
logs="$HOME/.cache/growth-setup"
mkdir -p "$logs"
if [ -n "${CLAUDE_ENV_FILE:-}" ] && ! grep -qF "$here/env.sh" "$CLAUDE_ENV_FILE" 2>/dev/null; then
  echo "source \"$here/env.sh\"" >> "$CLAUDE_ENV_FILE"
fi

summary=()
step() {
  local name=$1 start=$SECONDS
  shift
  if "$@" >"$logs/$name.log" 2>&1; then
    summary+=("ok      $name ($((SECONDS - start))s)")
  else
    summary+=("FAILED  $name ($((SECONDS - start))s), last lines of $logs/$name.log:")
    summary+=("$(tail -n 15 "$logs/$name.log" | sed 's/^/          /')")
  fi
}

step bootstrap bash "$here/bootstrap.sh"
for project in ${GROWTH_PROJECTS:-Uzawa}; do
  step "mathlib-$project" bash "$here/prepare-project.sh" "$project"
done
if [ "${GROWTH_SKIP_THEORYDEBUGGER:-}" != 1 ]; then
  step theorydebugger-lean bash "$here/prepare-theorydebugger.sh"
fi

echo "Cloud Lean setup for EconomicGrowth:"
printf '  %s\n' "${summary[@]}"
echo "  disk free: $(df -h "$HOME" | awk 'NR == 2 {print $4}')"
exit 0
