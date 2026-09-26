# SPDX-License-Identifier: Unlicense
# Tool paths for Claude Code cloud sessions. Sourced by the setup scripts and,
# through CLAUDE_ENV_FILE, before each Bash command. Safe to source repeatedly.
export ELAN_HOME="${ELAN_HOME:-$HOME/.elan}"
export THEORYDEBUGGER_HOME="${THEORYDEBUGGER_HOME:-$HOME/TheoryDebugger}"
export THEORYDEBUGGER_VENV="${THEORYDEBUGGER_VENV:-$HOME/.venvs/theorydebugger}"
for dir in "$THEORYDEBUGGER_VENV/bin" "$ELAN_HOME/bin"; do
  case ":$PATH:" in *":$dir:"*) ;; *) PATH="$dir:$PATH" ;; esac
done
export PATH
