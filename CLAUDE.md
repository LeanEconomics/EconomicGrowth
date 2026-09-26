# EconomicGrowth

Lean 4 formalizations of growth theory. Three independent Lake projects, each
with its own `lean-toolchain`, `lake-manifest.json`, `proof-manifest.json` and
`scripts/verify.py`:

| Project | Library | Toolchain |
|---|---|---|
| `SolowSwan/` | `Solow1956` | `v4.34.0` |
| `Uzawa/` | `UzawaModern` | `v4.34.0-rc2` |
| `RamseyCassKoopmans/` | `RamseyCassKoopmans` | `v4.34.0` |

Always `cd` into the project before running `lake`.

## Cloud sessions

- The SessionStart hook runs `scripts/cloud/session-start.sh`: it installs elan,
  fetches the Mathlib cache for the projects in `$GROWTH_PROJECTS` (default
  `Uzawa`) and installs TheoryDebugger in `$THEORYDEBUGGER_HOME`. Its summary
  is at the top of the session; logs are in `~/.cache/growth-setup/`.
- If `lake` is not on `PATH`, run `source scripts/cloud/env.sh`.
- To work on another project: `bash scripts/cloud/prepare-project.sh RamseyCassKoopmans`.
- Never build Mathlib from source. If `lake exe cache get` fails, stop and report
  the error (including the host it tried to reach).
- Never run `lake update` or edit `lean-toolchain` / `lake-manifest.json`; the
  pins are part of the audit.
- Commands time out after 10 minutes. While iterating, check one file with
  `lake env lean <Library>/Path/File.lean`; run the full verifier before committing.

## Proof rules (enforced by `scripts/verify.py`)

- No `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` outside comments.
- The build must produce no errors and no warnings.
- Only the axioms `propext`, `Classical.choice` and `Quot.sound`.
- Declarations must be `theorem`, `lemma`, `def`, `abbrev` or a simple
  `structure ... where` (optionally `noncomputable`/`protected`). The verifier
  rejects `private`, `instance`, `inductive`, `opaque` and `extends`.
- Every `.lean` file under the library directory must be listed in
  `proof-manifest.json` `modules`, imported from the root `<Library>.lean`, and
  counted in `theorem_counts` (number of `theorem` + `lemma` declarations).
- State economic domains and assumptions explicitly. Record the source and the
  economics-to-Lean correspondence in the project's `docs/`.
- Done means `python scripts/verify.py` passes in the project. Commit the
  regenerated `verification/verification.json` with the proofs.

## TheoryDebugger

Use it to test algebraic steps before spending effort on a Lean proof: whether
a polynomial claim is valid, an exact counterexample, or whether a candidate
extra assumption repairs it and is still satisfiable. Scope: real variables,
`+ - *`, natural powers, comparisons, Boolean combinations; at most 8
variables and 30 assumptions. No derivatives, integrals, limits or ODEs.

```bash
cd "$THEORYDEBUGGER_HOME" && python -m theorydebugger problem.json --out /tmp/td
```

Input format: see `$THEORYDEBUGGER_HOME/examples/*.json`. Only `lean_kernel`
evidence is checked; `solver_only` is a hint. `RamseyCassKoopmans/scripts/check_theorydebugger.py`
takes `--theorydebugger "$THEORYDEBUGGER_HOME"`.

## New results

Requests live in `targets/` (format: `targets/TEMPLATE.md`). Cite papers by
section and equation; do not copy their text into the repository. Work on a
branch and open a pull request; never push to `main`.
