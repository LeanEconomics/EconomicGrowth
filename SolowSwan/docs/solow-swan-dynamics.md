# Solow–Swan: general Cobb–Douglas dynamics

> Research note from TheoryDebugger. Links to diagnostic examples and archived
> contribution checks point to that repository. The standalone modules here have
> their own build and fresh axiom audit: run `python scripts/verify.py` from this
> repository root and consult `verification/verification.json`. Our original
> material in this standalone distribution uses The Unlicense.

This extends the [original square-root case study](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/docs/solow-swan.md) to **every
exponent `0 < α < 1`**, with positive trajectories, uniqueness, monotone
adjustment, and convergence. TheoryDebugger diagnoses intermediate claims;
Mathlib and Lean check the complete analytic argument.

## Sources and correspondence

Robert M. Solow (1956), *A Contribution to the Theory of Economic Growth*,
Quarterly Journal of Economics 70(1), 65–94,
[DOI 10.2307/1884513](https://doi.org/10.2307/1884513), is the primary source.
A [UNAM course copy](https://www.depfe.unam.mx/doctorado/teorias-crecimiento-desarrollo/solow_1956.pdf)
is preserved privately, with SHA-256
`5384fe4dccd16af0d2fe74f971f893e13b4445ec821e2c5e768486f16eb2fc57`.
The PDF has a cover sheet: printed p. 76 is PDF page 13. The formulas on
printed pp. 69, 76 and 77 were visually checked.

| Source location | Content | Formal counterpart |
| --- | --- | --- |
| p. 67 | Accumulation uses output net of depreciation | Original model has no separate depreciation term |
| p. 69, equation (6) | Capital/labour normalization | `hasDerivAt_capitalPerWorker`, `intensiveForm_of_homogeneous` |
| pp. 70–71, footnote 4 | Zero-capital boundary | `rate_zero`, `rate_eq_zero_iff`, actual `zero_solution` |
| p. 76, Example 2 and equation (7) | General Cobb–Douglas explicit solution | `hasDerivAt_power`, `hasDerivAt_path`, `positive_dynamics` |
| pp. 76–77 | Stationary stock, comparative statics, limiting output | `steadyState_*`, `tendsto_path`, `tendsto_output` |
| p. 77 | Stationary capital/output ratio | `steadyState_capital_output_ratio` |

Solow writes his explicit solution in aggregate capital. We work with capital
per worker and construct the equivalent intensive-form path through
`z=k^(1-α)`. The quotient-rule normalization and analytic argument are proved
separately. Our constant productivity multiplier `A` extends the source's
normalized coefficient of one. Depreciation and effective labour below are
explicit extensions, not attributed in full to the original Example 2.

Trevor W. Swan (1956), *Economic Growth and Capital Accumulation*, Economic
Record 32(2), 334–361,
[DOI 10.1111/j.1475-4932.1956.tb00434.x](https://doi.org/10.1111/j.1475-4932.1956.tb00434.x),
is the other founding reference. A usable original PDF has **not** been obtained:
the publisher request was denied and the indexed course copy was unavailable.
The archived [Dimand–Spencer study](https://www.nber.org/papers/w13950) is
historical background. No Swan-specific derivation is claimed checked.

## Model and precise statement

In the original net-output model, `L>0`, `L'=nL`, `K'=sF(K,L)` and constant
returns gives `F(K,L)=L f(K/L)`. Thus `k=K/L` satisfies `k'=s f(k)-nk`.
Take `f(k)=A k^α`, with constant `A>0`, and write `b=sA`, `m=n`.

The theorem concerns

**`k'(t)=b k(t)^α-m k(t)` for every `t≥0`, with `k(0)=k₀`.**

Assume `b>0`, `m>0`, `0<α<1`, and `k₀>0`. Define

```
q = 1 - α,                 z* = b/m,
λ = q m,                   k* = (b/m)^(1/q),
z(t) = z* + (k₀^q - z*) exp(-λ t),
k(t) = z(t)^(1/q).
```

The formalized conclusions are:

1. This path starts at `k₀`, stays strictly positive, and satisfies the
   differential equation at every nonnegative time.
2. Every nonnegative differentiable solution with the same positive initial
   value remains strictly positive and equals this path on `[0,∞)`.
3. The path converges to `k*`. Consequently every solution in that nonnegative
   solution class has this limit.
4. It is nondecreasing if `k₀≤k*` and nonincreasing if `k*≤k₀`. A path that
   starts strictly below `k*` remains strictly below it.
5. The exact transformed deviation is
   `k(t)^q-(k*)^q=(k₀^q-(k*)^q) exp(-λt)`.
6. Output per worker/effective worker converges to `A(k*)^α`.

The predicate `IsNonnegativeSolution` contains the initial value, nonnegative
capital, and `HasDerivAt` at every `t≥0`. The theorem `nonnegative_dynamics`
derives strict positivity, equality with the explicit path on future time, and
convergence. The intermediate predicate `IsPositiveSolution` is used for the
power transformation. Paths are functions on the reals with ordinary derivatives
at nonnegative dates, including zero; negative-time behaviour is not constrained
by the economic equations. No uniqueness claim concerns negative time.

An economically interpreted saving fraction usually satisfies `s≤1`. That
upper bound is unnecessary for the stated mathematical conclusions, but matters
for nonnegative consumption `(1-s)Y`. Positive `m` is essential. Neither `m=0`
nor `α=1` belongs to this finite positive steady-state theorem. Many supporting
positive-path lemmas only require `α<1`; the bundled economic statement includes
`α>0`, which also makes zero capital stationary.

## Detailed argument

**Normalization.** Differentiate `K/L`, substitute the aggregate equations,
and use constant returns to obtain `s f(k)-nk`. The proof checks the quotient
denominator using `L>0`; a separate lemma derives the intensive normalization
from homogeneity of degree one.

**Stationary states.** For `k>0`, real-power laws give
`b k^α-mk=k^α(b-m k^(1-α))`. Since `k^α>0`, stationarity is equivalent to
`k^q=b/m`. Raising to `1/q` gives `k*`. At zero, `0^α=0` because `α>0`, so
zero is stationary too. `rate_eq_zero_iff` classifies all nonnegative stationary
stocks as exactly `0` and `k*`. No division silently removes the boundary.

**Linearization.** At a positive point of an actual solution, the chain rule
gives `z'=q k^(q-1)k'`. Substituting the differential equation and using
`k^α k^(q-1)=1` yields `z'=q(b-mz)`. The theorem concerns derivatives of
functions; derivatives are not represented by unconstrained algebraic variables.

**Why positive initial capital cannot hit zero.** For any nonnegative solution,
differentiate `v(t)=k(t)exp(mt)`. The equation gives
`v'(t)=b k(t)^α exp(mt)≥0`. The mean value theorem therefore makes `v`
nondecreasing on `[0,∞)`. Since `v(0)=k₀>0`, we have `v(t)>0` and hence
`k(t)>0` at every finite future date. This proves positivity without assuming
the solution formula or uniqueness. It justifies applying the power transformation
to every nonnegative solution with positive initial capital.

**Integrating factor and uniqueness.** For any transformed solution, differentiate
`w(t)=(z(t)-b/m) exp(qmt)`. Its derivative vanishes. The mean value theorem
on every closed interval `[0,t]`, including the initial endpoint, gives
`w(t)=w(0)`. Division by the positive exponential yields the explicit formula.
Raising both sides to `1/q` recovers uniqueness of positive capital paths.
Uniqueness is proved, not assumed as a premise.

**Constructive existence and positivity.** Set `e=exp(-λt)`. From `λ>0` and
`t≥0`, obtain `0<e≤1`. Rewrite the proposed transformed path as
`z*(1-e)+k₀^q e`. Its first term is nonnegative and its second strictly positive.
Thus the inverse power is legitimate. Differentiate it and use the real-power
identities to recover `k'=b k^α-mk`. At time zero, `e=1` and
`(k₀^q)^(1/q)=k₀`. These checks prove an actual solution exists for all future time.

**Convergence.** Since `λ>0`, `exp(-λt)→0`, so `z(t)→b/m>0`. Continuity
of the real power at this positive limit gives `k(t)→k*`. The convergence
theorem for other positive solutions follows from their equality with this path
for all nonnegative time. Adjustment signs alone are not used as a substitute
for existence, uniqueness, or convergence.

**Monotonicity and limiting output.** The exponential decreases. Multiplication
by the initial transformed deviation reverses or preserves order according to
its sign; the inverse power is increasing. This proves monotone adjustment.
The exact transformed-deviation formula checks the no-crossing statement.
Continuity of `A k^α` gives the output limit. `λ` is an exact exponential
rate for transformed capital, not an asserted exact exponential rate for `k`.

**Comparative statics.** Since `1/q>0`, the positive stationary stock increases
strictly with `b` and decreases strictly with `m`. Increasing saving at fixed
productivity therefore raises it. The equation `sA(k*)^α=mk*`, with positive
denominators, gives `k*/[A(k*)^α]=s/m`, equal to `s/n` in the original model.

## Explicit extension: depreciation and effective labour

Let technology `B` grow at rate `g`, labour `L` at rate `n`, and `E=BL>0`.
The product rule proves `E'=(n+g)E`. Suppose gross output is `Y=E f(K/E)`
and accumulation is `K'=sY-δK`. The quotient rule then proves

`(K/E)'=s f(K/E)-(n+g+δ)(K/E)`.

For `f(k)=A k^α`, take `b=sA` and `m=n+g+δ>0` in the trajectory theorem.
`A` is a constant multiplier; `B(t)` is the evolving labour-augmenting index.
These normalization results are conditional on the stated growth and production
equations; a technology process is not derived from optimizing behaviour.

## Executed TheoryDebugger checks

These are deliberate test claims, not errors attributed to the original authors.
The earlier [square-root example](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/examples/SolowSwan.lean) detects loss of
the zero stationary state, accepts strict positivity, and rejects an inconsistent
restriction. Its actual square-root bridge is also proved.

The new [dynamics example](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/examples/SolowSwanDynamics.lean) adds:

| Proposed claim | Diagnosis | Repair and result |
| --- | --- | --- |
| `z₀>0`, `e>0` imply `1+(z₀-1)e>0` | Mixed; a weight above one can refute it | `e≤1`: valid and feasible |
| Same claim | — | `e≤0`: inconsistent; rejected |
| `α>0`, `m>0` imply `(1-α)m>0` | Mixed; `α≥1` refutes it | `α<1`: valid and feasible |
| Same claim | — | `α≤0`: inconsistent; rejected |

Every repair retains all original assumptions and the same conclusion.
The new example proves that the actual exponential weight satisfies the accepted
restriction. It proves the derivative of `d exp(-λt)` and that the derivative
of its squared deviation is `-2λw²≤0`. Algebraic obligations are separate lemmas
where the surrounding analytic context is outside the native extractor's language.
Polynomial diagnostics alone do not certify exponential decay or real-power
calculus; those bridges and the full trajectory are checked in Lean. The review
also fixed an extractor bug affecting nested `have` steps: already-assigned
elaboration variables are now substituted before checking closure. Regression
tests require both validity and feasibility, while rejecting genuinely unresolved
propositions and hidden local dependencies.

Reproduce the native checks:

```sh
python scripts/verify_solow.py
python scripts/verify_solow_dynamics.py
```

The first checks three reports and six theorem axiom reports. The second checks
six reports, four repair decisions, exact rational witnesses, preservation of
the original claims, and seven theorem axiom reports. Its output is saved in
`demo/solow-dynamics/`. Hashes bind logs to checked inputs; JSON alone is not a
proof certificate.

## Contribution and verification

The [complete contribution package](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/contributions/lean-economics-solow-dynamics/README.md)
contains the patch, a fresh source audit, and verification metadata.

| Module | Theorems | Scope |
| --- | ---: | --- |
| `SolowSwan` | 16 | Original normalization and square-root results |
| `SolowSwanDynamics` | 37 | General exponent, trajectories, uniqueness, convergence, comparative statics |
| `SolowSwanExamples` | 6 | Positive example, boundary checks, effective-labour product rule |
| Total | **59** | Fresh compilation and full project build |

The patch targets upstream commit `8e7d5172e253cb20af2aea27e53f384d7ef18a25`.
The fresh audit recompiles all contributed proofs without importing contributed
compiled modules. Only the standard axioms `propext`, `Classical.choice` and
`Quot.sound` are allowed; no proof placeholders or additional axioms are admitted.
LeanEconomics uses Lean/Mathlib `v4.34.0-rc2`; TheoryDebugger uses `v4.34.0`.
Each is checked in its own environment. Native diagnostics run in TheoryDebugger
CI; the separate contribution's full build is recorded as a local Windows check.

## Limits and credit

This is the Cobb–Douglas model, not a convergence theorem for every neoclassical
production function. General-production assumptions, zero-initial-stock
uniqueness, nonconstant parameters, stochastic dynamics, and the golden rule
are not formalized here. For positive initial capital, the new weighted-capital
argument excludes hitting zero within the nonnegative solution class. Swan's
original presentation still needs primary-source inspection.

These additions were developed with **OpenAI Codex**, under the direction of
the TheoryDebugger project maintainer, who chooses the questions and reviews
their economic interpretation. Codex assists with sources, proofs, implementation,
documentation, and verification. This follows LeanEconomics' transparent credit
for Claude. Lean verifies formal statements; their economic faithfulness requires
researcher review. Reasoning settings are development provenance, not certificates.

TheoryDebugger complements TheoryGuru. Original examples use The Unlicense;
archived LeanEconomics contributions retain Apache 2.0 and our original work
is additionally offered under The Unlicense. Downloaded papers are
excluded from the release.
