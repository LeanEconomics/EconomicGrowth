# Contributing

Contributions of fixes, examples, and clearer economic statements are welcome.
Submit only work you have the right to contribute. By contributing original
material here, you agree to dedicate it under the repository's Unlicense.
Identify any third-party material and preserve its notices.

State domains and assumptions explicitly. Do not use proof placeholders or add
axioms. Run `python scripts/verify.py`; it builds the complete library and
freshly recompiles every contributed theorem, checking its axiom dependencies.
For new named theorems, update proof-manifest.json so the audit covers them.
Document mathematical sources and the correspondence between economics and Lean.
