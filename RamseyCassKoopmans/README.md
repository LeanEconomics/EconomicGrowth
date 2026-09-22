# Ramsey–Cass–Koopmans in Lean

Lean proofs for the positive-discount optimal-growth model, developed with
[TheoryDebugger](https://github.com/mvazcar/TheoryDebugger). The development
now constructs the unique Cass optimum from **every positive initial capital
stock for general production and utility functions** under explicit Inada and
twice-differentiable curvature assumptions. It proves capital and consumption
convergence, strict capital and consumption monotonicity away from steady state,
finite candidate welfare, and equality of every optimum with the constructed path. The possible
zero-investment corner remains in the equations throughout.

The main theorem is [`cass_general_dynamic`](RamseyCassKoopmans/CassGeneral.lean).
Its admissible class uses continuous controls and positive consumption. It also
proves asymptotic welfare dominance over **every** Cass-feasible competitor,
without requiring competitor welfare to have a finite limit. See the
[general proof and exact assumptions](docs/cass-general.md).

The Koopmans investigation found a substantive boundary obstruction:
`f(k)=8k/(1+k)`, `U(c)=c−1/c`, `d=m=1` meets the published appendix's displayed
scalar conditions, but no regular feasible Euler path from `k0=7` can have
`k(t)→1`. Lean proves this contradiction without assuming consumption convergence.
The [detailed source comparison and proof](docs/koopmans-boundary-obstruction.md)
states the regularity scope and distinguishes this result from a claim about
all generalized controls or a completed repaired existence theorem.

## Mathematical results

* **Finite-horizon comparison:** a competitor's welfare advantage is at most
  the present-value price times candidate minus competitor terminal capital.
  The proof derives the boundary derivative from actual path equations, checks
  the algebra, proves integrability, and applies the fundamental theorem of calculus.
* **Infinite-horizon verification:** the finite comparison and a vanishing
  terminal term imply optimality among competitors with finite limiting welfare.
  `AsymptoticallyDominates` extends the comparison to arbitrary competitors:
  their finite-horizon welfare advantage is eventually smaller than any positive
  epsilon. Divergent lifetime integrals are never assigned a finite value.
* **Cass's investment constraint:** complementary slackness handles zero
  investment. The candidate's membership in Cass's feasible class is explicit
  in `IsCassOptimal` and `cass_certificate_is_optimal`.
* **Capital and terminal bounds:** resource laws imply an upper capital bound;
  concavity and marginal product tending to zero provide a capacity threshold.
  Positive discounting and a finite marginal-utility limit make prices vanish.
* **Stationary states:** the Inada limits give finite brackets; continuity and
  strict concavity yield a unique positive stationary capital/consumption pair.
  Positive discount places capital below the golden-rule stock, which strictly
  maximizes sustainable consumption.
* **Constructed stationary optimum:** the stationary pair determines an actual
  feasible path. Its welfare is `U(c*) / d`; it dominates every finite-welfare
  feasible competitor with the same stationary initial capital. The theorem
  proves existence of this path rather than assuming its existence.
* **Uniqueness:** strict concavity turns a difference in consumption or capital
  into a strictly positive welfare gap. Under the stated derivative and positivity
  assumptions, equal welfare implies equality of capital, consumption and investment.
* **Convergent Euler candidates:** the chain rule connects an actual consumption
  Euler equation to the costate equation. Positive consumption convergence
  supplies price decay and hence verification. This theorem assumes convergence.
* **Constructed nonstationary Cass optimum:** for `f(k)=2*sqrt(k)`,
  `U(c)=2*sqrt(c)`, and `d=m=1`, every `k0>0` determines an actual unique optimum.
  Capital and consumption converge strictly monotonically to `1/4` and `3/4`
  unless they start at that steady state. Large stocks receive a proved
  zero-investment prefix, joined with matching capital and price derivatives.
  Feasibility implies finite welfare for every Cass competitor; this is proved
  rather than required as an additional hypothesis.
* **General nonstationary Cass optimum:** compact inverse marginal utility,
  global ODE solutions, continuous dependence and a connected shooting argument
  construct the path. Comparison and finite drift bounds prove monotonicity;
  the unique equilibrium identifies its limit. Quantitative estimates prove
  all auxiliary clipping bounds are inactive along the selected future path.

The original stationary example uses logarithmic utility:

\[
f(k)=2\sqrt{k},\quad U(c)=\log c,\quad d=m=1,
\qquad k^*=\tfrac14,\quad c^*=\tfrac34.
\]

[`Examples.logSqrtPath_optimal`](RamseyCassKoopmans/Examples.lean) proves that every
admissible finite-welfare competitor starting at `k(0) = 1/4` has lifetime welfare
at most `log(3/4)`. The stationary path's feasibility, nonnegative investment and
attainment of that welfare are proved separately. The comparison even allows
competitors that disinvest; it therefore also bounds Cass's narrower class.

The new [dynamic theorem](RamseyCassKoopmans/CassSpecialization.lean),
`ClosedForm.cass_dynamic_theorem`, uses **square-root utility**, not logarithmic
utility. For `0 < k0 ≤ 4/9`, put

\[
x(t)=\tfrac12+(\sqrt{k_0}-\tfrac12)e^{-2t},\qquad
k(t)=x(t)^2,\quad c(t)=3x(t)^2,\quad z(t)=2x(t)-3x(t)^2.
\]

For `k0 > 4/9`, investment is zero until `τ=log(9*k0/4)`; afterwards the same
interior formula starts at `x(τ)=2/3`. Lean proves feasibility at the switch,
the price certificate, lifetime welfare, uniqueness and monotone convergence.
`every_optimum_eq` and `every_optimum_converges` derive equality and convergence
from optimality itself, without assuming an Euler equation for the competitor.
See the [detailed construction and proof](docs/cass-square-root.md).

The exact statements are in [the source map](docs/source-map.md). The
[proof status](docs/proof-status.md) separates proved statements, regularity
restrictions and the remaining extensions.

## Admissibility and conventions

Capital, consumption and gross investment satisfy

\[
c+z=f(k),\qquad \dot k=z-mk,\qquad
W(T)=\int_0^T e^{-dt}U(c(t))\,dt.
\]

Here `d` is effective utility discounting and `m` is depreciation plus population
dilution. Cass's population-weighted convention is `d = rho - n`, `m = n + mu`.
Koopmans's per-worker convention uses its own discount rate directly.

`FeasiblePath` requires nonnegative capital, strictly positive consumption,
continuous controls and classical capital derivatives for nonnegative time.
It permits disinvestment. Cass additionally requires `NonnegativeInvestment`.
These regularity and welfare restrictions are explicit: the code does not claim
to cover all of the original papers' admissible controls. `HasWelfare` means
convergence of finite-horizon welfare to a real number. It does not interpret a
divergent infinite Bochner integral as zero. Verification theorems prove the
finite integrals are integrable before using them.

## TheoryDebugger's role

The [diagnostic record](verification/theorydebugger/README.md) contains **24
checks and 48 Lean-verified certificates**, including feasibility witnesses.
It checks welfare identities, costate normalization, complementary slackness,
discount normalization and the boundary sign. It refutes both the incorrect
terminal-sign inference and the claim that complementary slackness always
implies Euler equality at zero investment. The dynamic checks also refute an
everywhere-interior Cass path for large initial capital and the extension of the
interior consumption Euler equation into the zero-investment phase.
Four further checks cover Hamiltonian differentiation, discounting and the
negative capacity Hamiltonian used in the Koopmans boundary obstruction.

The exported [algebra lemmas](RamseyCassKoopmans/Algebra.lean) are used by the
analytic proof. Solver outputs are not trusted axioms: Lean checks reconstructed
polynomial proofs and the separate calculus, integration and limit arguments.
The economic interpretation of the formal assumptions still needs human review.

## Reproduce

The project pins Lean **4.34.0** and the matching Mathlib revision in
`lean-toolchain` and `lake-manifest.json`.

The standard Mathlib lint set is enabled in both the library build and the
fresh-source audit, following the main LeanEconomics project's configuration.
Only the Apache-specific header rule is disabled because this original
contribution uses the Unlicense. Warnings fail verification.

```sh
lake exe cache get
lake build
python scripts/verify.py
```

The audit builds the library, freshly elaborates all original proof source,
checks named declarations and structure constructors/projections for extra axioms,
and records hashes. It also freshly compiles the 48 saved TheoryDebugger certificates
and checks their proof types against the original diagnostic inputs. This step
requires only Lean and Python; it does not rerun CVC5 or trust saved success labels.
Only Lean's standard `propext`, `Classical.choice` and `Quot.sound` are accepted.
See [verification/verification.json](verification/verification.json).
The current fresh-source audit covers **423 theorems and 576 declarations in
52 modules**, including structure constructors and projections, with no
placeholder proofs or additional axioms.

Replaying the diagnostic search additionally needs a TheoryDebugger checkout
and its Python dependencies (including CVC5):

```sh
python scripts/check_theorydebugger.py --theorydebugger ../TheoryDebugger
```

## Sources and attribution

Primary sources are Ramsey (1928), Cass (1965), and Koopmans's published 1965
chapter; the 1963 Koopmans draft is retained in the separate research archive
for comparison. Precise statements, pages and versions appear in the
[source map](docs/source-map.md). Source PDFs are not bundled or relicensed.

Developed with **OpenAI Codex, under the direction of
[@mvazcar](https://github.com/mvazcar)**. The research workflow uses **Astra 6
with Ultra and Extra High reasoning settings**, following the project's
requested transparent attribution of AI assistance, similar to
[LeanEconomics's provenance practice](https://github.com/LeanEconomics/LeanEconomics#provenance).
This is not an attribution of these modules to Claude or an endorsement by
LeanEconomics. TheoryDebugger is a complement to TheoryGuru.

Our original code and explanatory writing are dedicated to the public domain
under [The Unlicense](UNLICENSE): free use, modification, derivative works and
redistribution, including commercial use. Dependencies and papers retain their
own terms; see [third-party notices](THIRD_PARTY_NOTICES.md).
