# TheoryDebugger algebra audit

Run `python scripts/check_theorydebugger.py --theorydebugger /path/to/TheoryDebugger --lake lake`
from the project root, using a Python environment with TheoryDebugger's dependencies.
This uses the actual CVC5 backend and TheoryDebugger Lean verifier; every accepted
case has a Lean-checked validity or refutation certificate and a Lean-checked
feasibility certificate. The Lean verifier audits every generated declaration,
allowing only `propext`, `Classical.choice`, and `Quot.sound`.

`results.json` contains complete diagnostics, exact witnesses and certificate paths.
`environment.json` records the runtime versions and hashes of inputs, the script,
the mathlib manifest and the TheoryDebugger Python implementation. Generated Lean
source and compiler logs are retained in `certificates`; compiled `.olean` files
are reproducible build outputs.

The twenty-four cases are polynomial abstractions. TheoryDebugger accepts at most
eight variables, so the identity checks use exact candidate-minus-competitor gaps
`V = U0-U1`, `F = f0-f1`, `Z = z0-z1`, `K = k0-k1`, and the resource gap
`c0-c1 = F-Z`. The costate normalization and present-value boundary derivative
are separately checked. In particular:

- The pointwise welfare identity eliminates consumption, capital derivatives and
  the costate derivative using the resource equations and candidate costate law.
  `RamseyCassKoopmans/Algebra.lean` exposes the equivalent theorem with all those
  equations explicit. It does not assume the costate law for the competitor.
- The corresponding present-value identity is checked independently with weight
  `w` and price `p`; the Lean analytic theorem uses its nonnegative-comparison
  corollary, `present_value_comparison_nonneg`.
- The investment-complementarity check permits zero investment. The attempted
  implication to costate equality is refuted; positive investment repairs it.
- In the terminal comparison, `A` denotes competitor-minus-candidate welfare,
  `k0` candidate terminal capital and `k1` competitor terminal capital. The checked
  premise is `A ≤ -p*(k1-k0)`. Its correct equivalent is `A ≤ p*(k0-k1)`;
  the reversed bound is refuted at `(A,p,k0,k1)=(1,1,2,1)`.
- The population-discount identity uses the population-weighted welfare convention.

Nine additional checks concern the explicit square-root Cass construction:

- The interior resource and state-derivative identities.
- Nonnegative investment below the transformed threshold `x=2/3`, and a
  counterexample above it (`x=1` gives investment `-1`).
- The corner costate identity and factorization of the investment wedge.
- Nonnegativity of the wedge product given its factor bounds. The remaining
  factor's bound and the exponential substitution are proved in the analytic
  library, not postulated as consequences of a solver result.
- Matching capital derivatives at the switch.
- A counterexample to imposing the interior consumption Euler equation during
  the zero-investment regime. Its failure at the switch also identifies why
  consumption continuity must not be silently strengthened to differentiability.

Four more checks cover the Hamiltonian derivative, its discounted version,
the identity `H(0)=-2/c(0)` at capacity in the Koopmans boundary example, and
a refutation of the claim that this Hamiltonian must be nonnegative.
They check only algebra; the no-path theorem is a separate analytic Lean proof.

The final record contains 19 valid claims and 5 refutations, each accompanied
by a checked feasibility witness: 48 certificates in total.

The wedge-product check initially obtained only solver evidence: the CLI's
`nlinarith` fallback did not reconstruct a proof of the cubic product. The tool
correctly left it uncertified. Adding the Lean `positivity` fallback, already
present in the native frontend, closed that reconstruction gap. Both the valid
case and the false version with the upper bound omitted have real-Lean regression
tests. The recorded run uses the revised source hashes in `environment.json`.
The small [source patch](positivity-fallback.patch) is included for reproducing
the run with a TheoryDebugger checkout that predates that fallback. Apply it in
the TheoryDebugger checkout before rerunning the diagnostic script; check
`environment.json` for the exact Python source hashes. The analytic library
build and axiom audit do not require installing TheoryDebugger.

The Hamiltonian check exposed a second reconstruction gap: a defining equality
needed substitution inside another product. The generator now tries checked
substitution and ring normalization, and supplies explicitly proved products
of equality assumptions by variables. For example, it proves `c*r^2=r` from
`c*r=1` by multiplying the equality by `r`; it never imports the solver's verdict
as a proof. The [additional source and regression-test patch](equality-reconstruction.patch)
applies after the positivity patch. All 31 TheoryDebugger tests passed with the
real Lean boundary tests enabled, including acceptance of the valid consequences
and rejection when the required equality is removed.

These checks do not prove path existence, convergence, differentiability,
integration by parts, or the analytic terminal limit. The analytic verification
theorems are separate Lean declarations in the project.
