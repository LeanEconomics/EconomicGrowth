# Solow 1956 in Lean

This is the `SolowSwan/` proof project in
[LeanEconomics/EconomicGrowth](https://github.com/LeanEconomics/EconomicGrowth).
Run the commands below from this directory: `cd SolowSwan` from the repository
root. [Return to the growth library index](../README.md).

A checked formalization of the Cobb–Douglas Solow–Swan growth model:
**59 theorems**, including an explicit solution, existence, positivity,
uniqueness among nonnegative differentiable paths, monotone adjustment,
convergence, and comparative statics.

## Exact model

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
of every result in either original paper or of general neoclassical convergence.

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [SolowSwan](Solow1956/Growth/SolowSwan.lean) | 16 | Normalization, square-root model, stationary states |
| [SolowSwanDynamics](Solow1956/Growth/SolowSwanDynamics.lean) | 37 | General exponent, complete dynamics, comparative statics |
| [SolowSwanExamples](Solow1956/Growth/SolowSwanExamples.lean) | 6 | Boundary checks and effective-labour bridge |

Import `Solow1956`. Start with
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

Lean and Mathlib are pinned to **v4.34.0-rc2**, with transitive revisions in
`lake-manifest.json`. The script builds the library, freshly recompiles the
proof sources without importing their compiled project modules, and checks
each named theorem's axiom dependencies. Only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Warnings, failed proofs, and
placeholder axioms fail verification. Mathlib's Apache-specific header style
rule is disabled because this independent distribution uses The Unlicense;
the mathematical and other style checks remain enabled.

The checked source hashes, theorem names, and axiom lists are recorded in
[verification/verification.json](verification/verification.json). GitHub Actions
repeats the build and fresh audit on pushes and pull requests. A JSON record is
evidence of a run; the Lean proof terms and kernel checks are the certificates.

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

The modules were first developed as independent proposed LeanEconomics
contributions. [proof-manifest.json](proof-manifest.json) records the original
commits and source hashes. This standalone library changes the project namespace,
imports, and license header while preserving the mathematical proof bodies.

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
