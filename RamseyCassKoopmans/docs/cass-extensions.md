# Policy function, convergence rate, comparative statics, value function, decentralization

These modules extend the general Cass theorem (`cass_general_dynamic`) using its
primitive assumptions, bundled as `CassPrimitives f U d m`. None of them assumes a
stable manifold, a differentiable policy, or a differentiable value function.

## Certified optima and time consistency — [`CassCertified`](../RamseyCassKoopmans/CassCertified.lean)

`CassCertificate f U d m a q` records the current-value costate `q` of a path `a`:
the costate equation, the investment wedge `q ≤ U'(c)`, complementary slackness,
transversality and finite welfare.

* `exists_certified`: the constructed optimum from every `k₀ > 0` carries one.
* `CassCertificate.isCassOptimal`, `CassCertificate.eq_of_isCassOptimal`: a
  certificate makes a path optimal, and every optimum from the same stock equals it.
* `FeasiblePath.shift`, `CassCertificate.shift`, `hasWelfare_shift`: the tail of a
  certified path after any date is certified from the stock it has reached.
* `CassCertificate.dynamics`, `CassCertificate.capital_bounds`: every certified
  path converges monotonically to `k*` and stays on its side of it.

## Policy function, non-crossing paths, absolute convergence — [`CassPolicy`](../RamseyCassKoopmans/CassPolicy.lean)

`policy P k` is initial consumption on the unique optimum from `k`.

* `consumption_eq_policy`: along every optimal path `c(t) = policy P (k(t))`, so
  the saddle path is the graph of the policy (time consistency).
* `exists_shift_of_between`: on either side of `k*`, optimal paths are time
  translates of one another.
* `policy_strictMono`: consumption is strictly increasing in capital.
* `capital_lt_of_lt`, `consumption_lt_of_lt`: optimal paths of identical economies
  never cross, and the poorer economy consumes strictly less at every date.
* `absolute_convergence`: gaps in capital and consumption tend to zero and the
  capital ratio tends to one.

## The exact local speed of convergence — [`CassRate`](../RamseyCassKoopmans/CassRate.lean), [`RiccatiRate`](../RamseyCassKoopmans/RiccatiRate.lean)

With `A = f''(k*) U'(c*) / U''(c*)` and `β* = (√(d² + 4A) − d)/2`, and assuming
`f''(k*) < 0`:

* `slope_tendsto`: along every nonstationary optimum
  `(c − c*)/(k − k*) → d + β*`, the stable eigenvector slope.
* `speed_tendsto`: `k̇/(k − k*) → −β*`.
* `capital_rate`, `consumption_rate`: `log|k − k*|/t → −β*`, `log|c − c*|/t → −β*`.
* `policy_hasDerivAt`: the policy is differentiable at `k*` with slope `d + β*`.

The slope `S = (c − c*)/(k − k*)` solves a Riccati equation
`S' = S² − D(t) S + B(t)` with `D → d` and `B → −A`. `riccati_tendsto` shows that
a positive solution defined for all large times must converge to the positive
root: above it, solutions blow up in finite time (`1/S` reaches zero); below it,
they are driven negative. Positivity of `S` is the monotonicity of optimal paths.

## Comparative statics and dynamics — [`CassComparative`](../RamseyCassKoopmans/CassComparative.lean)

The inverse marginal product `marginalInverse P` gives `k* = g(d + m)`
(`cassSteady_eq_marginalInverse`). The inverse function theorem gives
`g' = 1/f''` (`marginalInverse_hasDerivAt`), hence:

* `steady_hasDerivAt_discount`, `steady_hasDerivAt_dilution`: `∂k*/∂d = ∂k*/∂m = 1/f''(k*) < 0`;
* `steadyConsumption_hasDerivAt_discount`: `∂c*/∂d = d/f''(k*) < 0`;
* `steadyConsumption_hasDerivAt_dilution`: `∂c*/∂m = d/f''(k*) − k* < 0`;
* `steady_strictAnti_discount`, `steady_strictAnti_dilution'`,
  `steady_strictMono_productivity`: the corresponding strict orderings, with
  productivity entering as `A f`.

Comparative dynamics, starting from the old steady state:

* `patience_rise`: after a permanent fall in `d`, capital rises strictly to the new
  higher steady state; consumption falls strictly on impact below the old level,
  then rises strictly to a higher new level.
* `impatience_rise`: the mirror image after a rise in `d`.

The impact effects use a Gronwall step: if consumption did not jump, `(k − k₀)e^{−λt}`
would be monotone in the wrong direction.

## The value function — [`CassValue`](../RamseyCassKoopmans/CassValue.lean), [`CassEnvelope`](../RamseyCassKoopmans/CassEnvelope.lean)

`value P k` is optimal lifetime welfare from `k`.

* `value_strictMono`: strictly increasing (copying the lower optimum's investment
  from a higher stock leaves strictly more to consume).
* `value_strictConcave`: strictly concave (a mixture of two optima is feasible and
  strictly better by strict concavity of `f`).
* `value_le_supergradient`: `V(k₁) ≤ V(k₀) + q(0)(k₁ − k₀)`, from the verification
  comparison with unequal initial stocks (`finite_horizon_comparison'`).
* `value_hasDerivAt`: the envelope theorem, `V'(k₀) = q(0)`;
  `value_deriv_eq_marginal_utility`: `V'(k₀) = U'(c(0))` when the optimum invests
  at time zero.

The envelope theorem follows Clausen and Strub (2020), *Reverse calculus and
nested optimization*, Journal of Economic Theory 187: `clausen_strub_sandwich`
shows a function squeezed between two support functions that touch it at `k₀` and
share a derivative there is differentiable with that derivative. The upper support
is the affine supergradient bound; the lower support is the welfare of the path
copying the optimum's investment, whose derivative at `k₀` is identified from the
costate identity `q(0) = ∫₀^∞ e^{−(d+m)t} U'(c) f'(k) dt` and uniform continuity
of `U'` and `f'`.

## Competitive decentralization — [`CassDecentralization`](../RamseyCassKoopmans/CassDecentralization.lean)

Households own capital, rent it at `R(t)`, earn wage `w(t)`, and choose consumption
and irreversible investment subject to `c + z = R k + w`, `k̇ = z − m k`, `k ≥ 0`,
`z ≥ 0` (`HouseholdPlan`). Firms set `R = f'(k)`, `w = f(k) − k f'(k)`, which
maximizes profit at zero (`firm_optimal`). `CompetitiveEquilibrium` requires firm
optimality, feasibility and household optimality against every plan.

* `second_welfare_theorem`: the certified optimum with these prices is a
  competitive equilibrium. Household assets may grow without bound; the comparison
  closes because the boundary term is at most the discounted value of the planner's
  capital.
* `first_welfare_theorem`: every competitive-equilibrium allocation is Cass optimal;
  `equilibrium_eq_optimum`: it is the unique optimum.
