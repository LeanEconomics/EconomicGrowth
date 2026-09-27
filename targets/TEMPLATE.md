# <Short name of the result>

Copy this file to `targets/<project>-<short-name>.md` and fill it in.

- **Source:** author(s), year, title; section, equation and theorem numbers.
  Cite it; do not paste the paper's text.
- **Project:** SolowSwan | Uzawa | RamseyCassKoopmans | new project
- **Primitives and domains:** functions, variables, and where they live
  (for example `f : ℝ → ℝ`, `k > 0`, `s ∈ (0, 1)`).
- **Assumptions:**
  1. ...
- **Claim:** the precise informal statement to prove.
- **Proof sketch:** the paper's argument, or yours, step by step.
- **Known subtleties:** suspected gaps, boundary cases, steps worth checking
  with TheoryDebugger first.
- **Model:** Opus (default) or Fable (escalate when Opus stalls).
- **Done when:** named theorem(s) in `<Library>/<Path>.lean`, `scripts/verify.py`
  passes, and `docs/` maps the Lean statement to the source.
