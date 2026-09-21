# General Solow–Swan growth from Acemoglu

This contribution formalizes general **continuous-time** Solow–Swan dynamics
using Daron Acemoglu, *Introduction to Modern Economic Growth*, Chapter 2.
The [source map](acemoglu-source-map.md) identifies the precise propositions,
assumptions, pages, and differences in scope. The original Solow (1956)
Cobb–Douglas development remains available alongside this extension.

The main entry point is
`Solow1956.Neoclassical.general_solow` in
[GeneralSolow.lean](../Solow1956/Growth/GeneralSolow.lean).
Import `Solow1956` to use the complete library.

## Model and assumptions

For constant saving `s`, effective dilution `m`, and intensive production `f`,

\[
\dot k(t)=s f(k(t))-m k(t),\qquad k(0)=k_0>0.
\]

Without technological change, `m = δ + n`. With labour-augmenting technical
progress, `m = δ + n + g`, and capital is measured per effective worker.
The dynamics require `s > 0` and `m > 0`. The economic saving restriction
`s < 1` additionally ensures strictly positive consumption `(1-s)f(k)`.
The capital theorem intentionally also covers saving rates at or above one;
it does not assign those cases positive-consumption interpretations.

The structure `Technology f` states:

1. `f` is continuous on nonnegative capital and `f(0)=0`.
2. `f` is differentiable on positive capital, with a continuous first derivative.
3. `f` is strictly concave on nonnegative capital.
4. Marginal product is strictly positive at every positive stock.
5. Marginal product tends to infinity at zero from the right and to zero at infinity.

No derivative at zero, steady state, solution path, or convergence is assumed.
`technology_of_second_derivative` proves that the source's twice-differentiable,
negative-second-derivative conditions imply these intensive-form assumptions.
The production function is represented in Lean as `ℝ → ℝ`, but its economically
relevant assumptions concern only nonnegative inputs.

## Checked conclusions

For every positive initial stock, Lean constructs a future path and proves:

- There is exactly one **positive** stationary stock `k*`, satisfying
  `s f(k*) = m k*`. Zero is stationary too.
- The constructed path starts at `k₀`, has the actual derivative specified by
  the accumulation equation, and remains strictly positive.
- It is the unique path on `t ≥ 0` among nonnegative classical solutions with
  the same initial stock. Paths are represented on the real line; the economic
  equations and uniqueness conclusion are required only at nonnegative times.
- Below `k*`, capital strictly increases and stays strictly below `k*` at every
  finite future time. Above `k*`, capital strictly decreases and stays above it.
- Starting at `k*` gives the constant path.
- Every path stays between its initial stock and `k*`, and converges to `k*`.
- Output and consumption converge to `f(k*)` and `(1-s)f(k*)`.

`every_path_converges` transfers convergence to any admissible nonnegative
classical solution, using the proved uniqueness theorem.
`path_stable` establishes the quantitative bound

\[
|k(t)-k^*|\leq |k(0)-k^*|.
\]

This proves Lyapunov stability as well as global attraction on positive capital:
an initial distance less than any `ε > 0` stays less than that same `ε`.

## Proof construction

### Production geometry and the stationary stock

Strict concavity yields the supporting-line gap

\[
f'(k)k<f(k),\qquad k>0.
\]

Consequently average product `a(k)=f(k)/k` has strictly negative derivative

\[
a'(k)=\frac{f'(k)k-f(k)}{k^2}<0.
\]

The Inada condition near zero provides a positive stock with positive capital
drift. At a sufficiently large stock, a supporting tangent with sufficiently
small slope gives `f(k) ≤ (m/s)k`. These finite brackets and continuity give a
positive stationary stock by the intermediate value theorem. Strictly decreasing
average product gives uniqueness on the whole positive half-line, and determines
the drift's strict sign on either side of the stationary stock.

### Existence on the infinite future

Choose a compact interval with positive lower endpoint that contains both the
initial and stationary stocks in its interior. Clip the argument of the drift
to this interval. The resulting vector field is globally bounded and Lipschitz:
the original derivative is continuous and hence bounded on the compact interval.

`exists_global_solution` obtains local trajectories from Mathlib's
Picard–Lindelöf theorem on arbitrarily long intervals and glues them using ODE
uniqueness. This constructs a globally defined trajectory of the clipped field.
Strict inward drift at the two interval boundaries prevents the trajectory from
leaving the interval for future times. Thus it solves the original economic ODE.
Clipping is an auxiliary existence argument, not a modification of the model.

### Monotonicity, convergence, and uniqueness

If a nonstationary solution reached the stationary stock at a finite time,
ODE uniqueness for the clipped field would make it identical to the constant
solution, contradicting its initial stock. Continuity then prevents crossing.
The drift sign gives strict monotonicity. Bounded monotone paths have limits.

Continuity of the field makes the derivative converge to the drift at that
limit. A nonzero limiting derivative would eventually create a uniform positive
or negative drift. The mean value theorem would then force unbounded movement.
The limit must therefore be a stationary stock, and positive bounds identify it
with `k*`. The proof does not exchange differentiation and limits.

For an arbitrary nonnegative competing path, nonnegative gross investment gives

\[
k(t)\geq k(0)e^{-mt}>0.
\]

On each finite time interval, both trajectories lie in a compact positive
capital interval, where the original field is Lipschitz. ODE uniqueness applies
there. Since the time interval is arbitrary, uniqueness holds for the entire
future. No local Lipschitz hypothesis at the zero-capital boundary is needed.

## Comparative statics

[SolowComparative.lean](../Solow1956/Growth/SolowComparative.lean) constructs
`capitalAtRatio h r`, the inverse of average product for `r > 0`, and defines

\[
\texttt{steadyCapital}(s,m)=a^{-1}(m/s).
\]

The inverse function theorem supplies its actual derivative. The code's
`savingResponse` and `dilutionResponse` retain the chain-rule expressions
`[a'(k*)]⁻¹(-m/s²)` and `[a'(k*)]⁻¹/s`, whose signs are proved.

The theorem also proves global strict monotonicity in saving and global strict
antitonicity in dilution, rather than only local derivative signs.

For the productivity specification `A f(k)`, stationary capital is
`steadyCapital h (s*A) (δ+n)`. `acemoglu_capital_partials` proves the four
partial-derivative signs with respect to `A`, `s`, `δ`, and `n`.
`acemoglu_output_partials` proves the corresponding four signs for output
`A f(k*)`, including productivity's direct effect. Differentiability of the
equilibrium function is proved; it is not an extra assumption in these results.

## Golden Rule and the stationary Cass connection

[SolowGoldenRule.lean](../Solow1956/Growth/SolowGoldenRule.lean) constructs the
unique positive stock `kG` satisfying `f'(kG)=m`. Strict concavity proves that it
strictly maximizes sustainable stationary consumption `f(k)-mk` over all other
nonnegative stocks.

The saving rate `sG = m kG / f(kG)` lies strictly between zero and one, supports
`kG` as the Solow steady state, and uniquely maximizes stationary consumption
over saving rates in `(0,1)`. This is a global comparison, not merely a vanishing
derivative at a proposed optimum. It does not claim that Golden Rule saving
maximizes discounted welfare from an arbitrary initial stock.

If a Cass stationary stock satisfies `f'(kC)=d+m` with `d>0`, the theorem
`cass_stationary_bridge` proves `kC<kG` and identifies a constant Solow saving
rate `sC=m kC/f(kC)` with `0<sC<sG<1`. That Solow economy has the same stationary
capital and consumption. **Its transition path is not claimed to equal the
optimal Cass path.** The bridge uses stationary conditions explicitly and does
not depend on importing the Cass project or its pending PR.

## Applications and examples

`saving_increase_transition` starts from the old steady state and constructs
the path after a permanent saving increase. Capital strictly increases toward
the new steady state. Consumption falls immediately at the unchanged initial
capital stock; no claim is made that its eventual level must exceed the old one.

`effective_labour_convergence` derives the normalized differential equation
from actual derivatives of aggregate capital and effective labour, then applies
the general convergence theorem. It covers the capital convergence component
of Acemoglu's Proposition 2.13.

`technology_rpow` checks the assumptions for every exponent in `(0,1)`.
`Technology.add` permits sums of admissible technologies. In particular,
`mixed_power_technology` proves the assumptions for
`f(k)=k^(1/2)+k^(1/3)`, where the new theorem applies without a closed-form
trajectory. Additional lemmas show that nonpositive dilution precludes a
positive stationary stock under maintained positive-saving assumptions, and
that a linear technology can have multiple positive stationary stocks.

## TheoryDebugger and verification

Run `python scripts/verify.py` after fetching the pinned Mathlib cache. The
verifier builds all modules, freshly elaborates their source together without
importing compiled project modules, and checks transitive axioms for all named
theorems, definitions, and the technology structure. Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Placeholders, extra axioms,
unchecked evaluators, warnings, and uncovered library modules fail the audit.

TheoryDebugger independently checks ten polynomial abstractions of the proof:
seven valid claims and three refuted claims, together with feasible witnesses.
The resulting twenty certificates are in
`verification/theorydebugger/`. They check local algebra and hypotheses, not
the ODE existence theorem, Inada limits, or infinite-time convergence.

To regenerate them using the documented TheoryDebugger revision:

```sh
python scripts/check_theorydebugger.py --theorydebugger /path/to/TheoryDebugger
```

Lean and Mathlib are pinned to `v4.34.0`. Replaying solver searches additionally
requires TheoryDebugger and its CVC5 dependency. The normal proof audit uses
Lean and Python: it validates the saved inputs and hashes, freshly recompiles
all twenty certificates, checks the proof types against the original JSON
propositions, and audits their axiom dependencies. It does not rerun CVC5.

Original formalization and exposition: OpenAI Codex under the direction of
[@mvazcar](https://github.com/mvazcar), using Astra 6 Ultra and Extra High.
Original contributions use The Unlicense; Acemoglu's publications and external
dependencies retain their own terms. TheoryDebugger complements TheoryGuru.
