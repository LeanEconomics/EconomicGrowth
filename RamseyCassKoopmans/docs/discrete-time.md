# The discrete-time Ramsey–Cass–Koopmans model

The [`DiscreteTime/`](../DiscreteTime/) library (namespace
`RamseyCassKoopmans.DiscreteTime`) treats the standard discrete-time optimal growth
model (Stokey–Lucas, Section 2.1; Acemoglu, Chapter 6):

\[
\max \sum_{t\ge0} \beta^t u(c_t),\qquad c_t = F(k_t) - k_{t+1},\qquad
0 \le k_{t+1} \le F(k_t),\qquad F(k) = f(k) + (1-\delta)k .
\]

## Assumptions (`Primitives f u β δ`)

`0 < β < 1`, `0 < δ ≤ 1`. Production `f` is continuous on `[0,∞)`, `f(0) = 0`,
strictly concave, differentiable on `(0,∞)` with a continuous positive derivative,
and satisfies both Inada conditions. Utility `u` is continuous on `[0,∞)`, strictly
concave, differentiable on `(0,∞)` with a continuous positive derivative, and
`u'(0⁺) = ∞`.

**Scope restriction.** Utility is continuous at zero consumption, so welfare is a
bounded convergent series. This covers, for example, `√c` and CRRA utility with
curvature below one, but **not logarithmic utility**. Cass's irreversibility
constraint is not imposed in discrete time (the Stokey–Lucas convention).

## Results

| Module | Result |
| --- | --- |
| [Model](../DiscreteTime/Model.lean) | Feasible paths are bounded (`Feasible.le_bound`); the feasible set is compact in the product topology (`isCompact_feasibleSet`); welfare is continuous on it (`continuousOn_welfare`); an optimal path exists (`exists_optimal`). |
| [Bellman](../DiscreteTime/Bellman.lean) | `W(k) = u(c₀) + β W(tail)` (`welfare_eq_head_add`); tails of optima are optimal (`tail_optimal`); the Bellman equation (`bellman`); the optimum is unique (`optimal_unique`); `V` is strictly increasing and strictly concave. |
| [Euler](../DiscreteTime/Euler.lean) | Tails of optima are optimal at every date (`IsOptimal.shift`); by the Inada conditions the Bellman maximizer is interior (`interior_choice`); capital and consumption stay positive (`IsOptimal.interior`); the Euler equation `u'(c_t) = β u'(c_{t+1}) (f'(k_{t+1}) + 1 − δ)` (`IsOptimal.euler`). |
| [Dynamics](../DiscreteTime/Dynamics.lean) | The policy `k' = g(k)` is followed by every optimal path and is strictly increasing (`policy_strictMono`, by increasing differences, with strictness from the Euler equation); the unique steady state `β(f'(k*) + 1 − δ) = 1`; every optimal path converges to `k*` (`IsOptimal.tendsto`) strictly monotonically with consumption moving the same way (`IsOptimal.dynamics_below`, `IsOptimal.dynamics_above`); consumption is strictly increasing in capital (`consumptionPolicy_strictMono`); optimal paths never cross and identical economies converge to each other (`IsOptimal.capital_lt`, `IsOptimal.consumption_lt`, `IsOptimal.absolute_convergence`). |
| [Envelope](../DiscreteTime/Envelope.lean) | `V'(x) = u'(c₀)(f'(x) + 1 − δ)` (`value_hasDerivAt`) via the Clausen–Strub sandwich, the upper support coming from concavity (`concave_le_tangent_of_lower_support`); the steady state rises with `β` and falls with `δ`. |

## How the convergence proof works

The policy is monotone, so every optimal path is monotone and bounded, and it
converges to some `L`. Three cases remain:

* `0 < L` with `F(L) > L`: the Euler equation passes to the limit and forces
  `β(f'(L) + 1 − δ) = 1`, so `L = k*`;
* `L = 0`: eventually `β F'(k_{t+1}) > 1`, so consumption rises strictly while it
  must tend to zero — impossible;
* `F(L) = L` (the maximal sustainable stock, which exceeds `k*`): consumption tends
  to zero, and moving to `k*` and staying there beats the optimal tail.
