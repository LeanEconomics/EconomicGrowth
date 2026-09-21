# Solow–Swan growth in Lean

This is the `SolowSwan/` proof project in
[LeanEconomics/EconomicGrowth](https://github.com/LeanEconomics/EconomicGrowth).
Run the commands below from this directory: `cd SolowSwan` from the repository
root. [Return to the growth library index](../README.md).

A checked formalization of general neoclassical Solow–Swan growth using
**Acemoglu, Chapter 2**, alongside the original Solow (1956) Cobb–Douglas proofs.
The library contains **132 theorems** and audits **150 named declarations**.
It constructs global positive solutions, proves uniqueness, strict monotone
convergence and stability, establishes all eight source comparative-statics
signs, and connects Golden Rule saving to the stationary Cass condition.

Start with the [general theorem and detailed proof](docs/acemoglu-general-solow.md)
and the [Acemoglu source map](docs/acemoglu-source-map.md). The main theorem is
`Solow1956.Neoclassical.general_solow`, for `k' = s f(k) - m k` with explicit
neoclassical assumptions and `s,m,k₀>0`. Consumption additionally needs `s<1`.
The code proves the assumptions for powers and sums of powers, including
`f(k)=k^(1/2)+k^(1/3)`. Saving shocks and effective-labour convergence are included.

## Original Cobb–Douglas model

For $b,m,k_0>0$ and $0<\alpha<1$, consider

$$k'(t)=b k(t)^\alpha-m k(t),\qquad k(0)=k_0,\qquad t\geq0.$$

Set $q=1-\alpha$. The unique nonnegative solution on future time is

$$k(t)=\left[\frac bm+\left(k_0^q-\frac bm\right)e^{-qm t}\right]^{1/q}.$$

It remains positive and converges monotonically to $k^*=(b/m)^{1/q}$.
The proof establishes positivity for every nonnegative solution with positive
initial capital before applying the power transformation; it does not assume
uniqueness or simply infer convergence from the sign of the derivative.

In Solow's net-output formulation, $b=sA$ and $m=n$. A separately identified
effective-labour extension uses $m=n+g+\delta>0$. Zero capital is also stationary,
but uniqueness at zero initial capital is not claimed.

Read the [complete statement, source map, and detailed argument](docs/solow-swan-dynamics.md).
The primary source is Robert M. Solow (1956), *A Contribution to the Theory of
Economic Growth*, QJE 70(1), 65–94, [DOI 10.2307/1884513](https://doi.org/10.2307/1884513).
The formalization follows the Cobb–Douglas example on pp. 76–77 and the
normalization on p. 69. Swan's original article is credited as a founding
reference, but its full text has not been inspected. This is not a formalization
of every result in either original paper. The Acemoglu extension supplies general
neoclassical convergence in the separately documented modules below.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SolowSwan](Solow1956/Growth/SolowSwan.lean) | 16 | Normalization, square-root model, stationary states |
| [SolowSwanDynamics](Solow1956/Growth/SolowSwanDynamics.lean) | 37 | General exponent, complete dynamics, comparative statics |
| [SolowSwanExamples](Solow1956/Growth/SolowSwanExamples.lean) | 6 | Boundary checks and effective-labour bridge |
| [Neoclassical](Solow1956/Growth/Neoclassical.lean) | 14 | Primitive assumptions, production geometry, stationary existence |
| [GeneralSolow](Solow1956/Growth/GeneralSolow.lean) | 5 | Existence, positivity, uniqueness, strict monotone convergence |
| [SolowComparative](Solow1956/Growth/SolowComparative.lean) | 18 | Differentiable stationary stock and all eight source partials |
| [SolowGoldenRule](Solow1956/Growth/SolowGoldenRule.lean) | 9 | Golden Rule saving and stationary Cass connection |
| [GeneralSolowApplications](Solow1956/Growth/GeneralSolowApplications.lean) | 4 | Stability, saving shock, effective-labour convergence |
| [GeneralSolowExamples](Solow1956/Growth/GeneralSolowExamples.lean) | 6 | Powers, sums of powers, and assumption checks |
| [Analysis helpers](Solow1956/Analysis/) | 17 | Global ODE construction, scalar dynamics, and limits |

Import `Solow1956`. For the original explicit solution, start with
`Solow1956.SolowSwan.CobbDouglas.nonnegative_dynamics`; monotonicity and output
limits are separate named theorems in the same namespace.

Related growth results: [uzawa-modern-lean](https://github.com/mvazcar/uzawa-modern-lean).

## Reproduce the verification

Install [Lean through elan](https://github.com/leanprover/elan) and Python 3.12+,
then run from this project directory:

```sh
lake exe cache get
python scripts/verify.py
```

Lean and Mathlib are pinned to **v4.34.0**, with transitive revisions in
`lake-manifest.json`. The script builds the library, freshly recompiles the
proof sources without importing their compiled project modules, and checks
each named declaration's axiom dependencies. Only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Warnings, failed proofs, and
placeholder axioms fail verification. Mathlib's Apache-specific header style
rule is disabled because this independent distribution uses The Unlicense;
the mathematical and other style checks remain enabled.

The checked source hashes, theorem names, and axiom lists are recorded in
[verification/verification.json](verification/verification.json). GitHub Actions
repeats the build and fresh audit on pushes and pull requests. A JSON record is
evidence of a run; the Lean proof terms and kernel checks are the certificates.

Ten saved TheoryDebugger diagnostics have twenty Lean certificates: seven valid
algebraic claims, three refutations, and assumption-feasibility evidence.
The normal audit validates their hashes. Regeneration requires TheoryDebugger
revision `5c1fa57` and its CVC5 dependency:

```sh
python scripts/check_theorydebugger.py --theorydebugger /path/to/TheoryDebugger
```

These diagnostics check finite algebra. The analytic existence and convergence
proofs are independently checked in Lean.

## Development and credit

Developed primarily with **OpenAI Codex**, under the direction of
[@mvazcar](https://github.com/mvazcar), who chooses the research questions and reviews
the economic interpretation. Codex assists with source comparison, proof development,
implementation, documentation, and tests. This follows
[LeanEconomics' transparent attribution of AI assistance](https://github.com/LeanEconomics/LeanEconomics#provenance).
LeanEconomics
credits Claude for its own development; that credit is not a claim that Claude wrote
these new modules. Lean verifies the encoded statements; their economic interpretation
still requires researcher review.

Development and review used **Astra 6** with **Ultra** and **Extra High**
reasoning settings.

The original three Cobb–Douglas modules were developed as independent proposed
LeanEconomics contributions. [proof-manifest.json](proof-manifest.json) preserves
their import provenance and records the Acemoglu extension separately.
Selected analytic helpers and Golden Rule arguments adapt our original Cass
work, with fresh proof checking and local imports; the source map records that
reuse. The Solow project has no build dependency on the Cass branch.

[TheoryDebugger](https://github.com/mvazcar/TheoryDebugger) helped diagnose
assumptions, boundary cases, and algebraic proof steps. Its external solver is
not a trusted oracle or a runtime dependency of this library. The complete
proofs here use Lean and Mathlib.

## License

Our original work is dedicated to the public domain under
[The Unlicense](UNLICENSE). Use, modify, derive from, and redistribute it freely,
including commercially, without payment or a permission request. External
dependencies and research papers retain their own terms; see
[third-party notices](THIRD_PARTY_NOTICES.md). Papers and dependency binaries
are not bundled. Earlier Apache 2.0 grants of our original contribution remain
available. Contributions follow [CONTRIBUTING.md](CONTRIBUTING.md).
