# Solow–Swan in discrete time

The [`DiscreteTime/`](../DiscreteTime/) library redoes the continuous-time results
of `Solow1956/` for the difference equation

\[
k(t+1) = G(k(t)),\qquad G(k)=\frac{s f(k) + (1-\delta)k}{\gamma},
\]

where `γ = (1+n)(1+g)` is the gross growth of effective labour. Acemoglu's
equation (2.17) is the case `γ = 1`. Import `DiscreteTime`; the namespace is
`Solow1956.DiscreteTime`.

## Assumptions

`Params s δ γ` requires `s > 0`, `δ ≤ 1`, `γ > 0` and `m = γ − 1 + δ > 0`. The
technology is the same `Technology f` as the continuous library. `δ ≤ 1` makes `G`
increasing, which the global dynamics need; `depreciation_above_one_breaks_positivity`
shows the map can send a positive stock to a negative one without it.

## Shared steady state

`G(k) − k = rate f s m k / γ` (`next_sub_self`), so the positive fixed point of `G`
is the continuous steady state with effective dilution `m = γ − 1 + δ`
(`steady h s δ γ := steadyCapital h s (γ − 1 + δ)`). With `γ = 1 + n`, `m = δ + n`
exactly. Existence, uniqueness, the comparative statics and the Golden Rule are
therefore statements about the same stock as in continuous time; only the
dynamics are new.

## Source map

Primary source: Acemoglu, *Introduction to Modern Economic Growth* (2009), Chapter 2,
Sections 2.2–2.3, the same publisher PDF as the [continuous source map](acemoglu-source-map.md)
(SHA-256 `0d35fe85…4d095`).

| Source location | Formal result | Scope |
| --- | --- | --- |
| Equation (2.17), p. 37 | `next`, `next_acemoglu` | General `γ`; `γ = 1` is (2.17) verbatim. |
| Proposition 2.2, p. 39 | `existsUnique_steadyState`, `steady_state_equilibrium` | Unique positive fixed point, `y* = f(k*)`, `c* = (1−s) f(k*)`; zero is also fixed. |
| Proposition 2.3, p. 40 | `acemoglu_capital_partials`, `acemoglu_output_partials`, `steady_derivative_signs` | With `f = A f̃` and `γ = 1 + n`, plus the population-growth partial. |
| Proposition 2.4, p. 42 | `acemoglu_golden_rule`, `exists_unique_golden_saving` | `f'(k_gold) = δ` for `γ = 1`, `= γ − 1 + δ` in general; unique global maximum over `s ∈ (0,1)`. |
| Proposition 2.5, p. 45 | `general_solow`, `IsPath.orbit`, `slope_at_steady` | Global monotone convergence from every `k₀ > 0`; local stability `G'(k*) ∈ (0,1)`. |
| Proposition 2.6, p. 46 | `factor_prices`, `wage_strictMono` | From below `k*` the wage rises and `R = f'(k)` falls every period; the opposite from above. |

## Counterparts of the continuous modules

| Discrete module | Continuous module | Notes |
| --- | --- | --- |
| [Analysis/ScalarMap](../DiscreteTime/Analysis/ScalarMap.lean) | `Analysis/ScalarFlow` | Monotone-map orbit convergence; no ODE theory needed. |
| [Neoclassical](../DiscreteTime/Neoclassical.lean) | `Neoclassical` | The map, positivity, monotonicity, fixed points, Proposition 2.2. |
| [GeneralSolow](../DiscreteTime/GeneralSolow.lean) | `GeneralSolow` | Existence and uniqueness are immediate (iteration); Proposition 2.5. |
| [SolowComparative](../DiscreteTime/SolowComparative.lean) | `SolowComparative` | Proposition 2.3. |
| [SolowGoldenRule](../DiscreteTime/SolowGoldenRule.lean) | `SolowGoldenRule` | Proposition 2.4; Cass bridge with discount factor `β(1 + f'(k) − δ) = γ`. |
| [GeneralSolowApplications](../DiscreteTime/GeneralSolowApplications.lean) | `GeneralSolowApplications` | Strict per-period stability, saving shock, effective labour from aggregates, Proposition 2.6. |
| [GeneralSolowExamples](../DiscreteTime/GeneralSolowExamples.lean) | `GeneralSolowExamples` | Sum of powers, no steady state without dilution, `δ ≤ 1` is needed, linear technology. |
| [SolowSwan](../DiscreteTime/SolowSwan.lean) | `SolowSwan` | Solow's net-output model: `δ = 0`, `γ = 1 + n`; square-root fixed points and **global** dynamics (the continuous module proves only signs). |
| [SolowSwanDynamics](../DiscreteTime/SolowSwanDynamics.lean) | `SolowSwanDynamics` | Cobb–Douglas. No closed form for `δ < 1`; with `δ = 1`, `k(t) = k*^(1−α^t) k₀^(α^t)` and the log gap shrinks by exactly `α` per period. |
| [SolowSwanExamples](../DiscreteTime/SolowSwanExamples.lean) | `SolowSwanExamples` | Explicit path `4^((1/2)^t)`, boundary checks, effective labour. |
| [SolowConvergence](../DiscreteTime/SolowConvergence.lean) | `SolowConvergence` | Absolute convergence and its rate (below). |

## Convergence and its rate

For two paths `k`, `l` of identical economies with `k(0) < l(0)` and
`D(t) = log l(t) − log k(t)`:

- paths never cross (`paths_ordered`), and paths that meet agree at every earlier
  date (`path_eq_of_meet`);
- the poorer economy's growth factor `k(t+1)/k(t)` is strictly higher every period
  (`poorer_grows_faster`); `D` is strictly decreasing and tends to `0`
  (`log_gap_strictAnti`, `absolute_convergence`);
- the local contraction `κ(k) = k G'(k)/G(k)` lies in `(0,1)`; any bound `ρ` on it
  over the paths' range gives `D(t) ≤ ρ^t D(0)` (`log_gap_le_of_contraction_bound`),
  and some `ρ < 1` exists (`exists_uniform_rate`); the level gap obeys the same
  geometric bound (`level_gap_le`); the constant steady-state path gives a single
  economy's rate (`log_gap_steady_le`);
- the exact asymptotic factor is `ρ* = κ(k*) = G'(k*) = (s f'(k*) + 1 − δ)/γ`:
  `D(t+1)/D(t) → ρ*` (`log_gap_ratio_tendsto`) and `log D(t)/t → log ρ*`
  (`log_gap_rate_tendsto`), with an explicit sandwich (`sharp_convergence_rate`);
- `ρ* = 1 − β*/γ` where `β* = m − s f'(k*)` is the continuous-time rate
  (`contraction_steady_eq`); for Cobb–Douglas `ρ* = 1 − (1−α)(γ−1+δ)/γ`
  (`cobbDouglas_contraction`), which is `α` when `δ = 1` and `γ = 1`.
