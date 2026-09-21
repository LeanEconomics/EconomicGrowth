# Source-to-proof map

## Primary references

* David Cass (1965), *Optimum Growth in an Aggregative Model of Capital
  Accumulation*, Review of Economic Studies 32(3), 233–240.
  [DOI](https://doi.org/10.2307/2295827).
* Tjalling C. Koopmans (1965), *On the Concept of Optimal Economic Growth*,
  in *The Econometric Approach to Development Planning*, Scripta Varia 28,
  Part I, 225–287; discussion 289–300.
  [Official publication record](https://www.pas.va/en/publications/scripta-varia/sv28pas_a.html),
  [official scanned volume](https://www.pas.va/content/dam/casinapioiv/pas/pdf-volumi/scripta-varia/sv28apas.pdf).
  Article PDF pages 262–324; discussion PDF pages 325–336.
* Frank P. Ramsey (1928), *A Mathematical Theory of Saving*, Economic Journal
  38(152), 543–559. [DOI](https://doi.org/10.2307/2224098).
  The original bliss-shortfall problem is background and future work here;
  the present library does not claim to formalize Ramsey's entire paper.

## Proven correspondence

| Source argument | Lean module / principal declaration | Scope |
|---|---|---|
| Resource constraints, Cass pp. 233–234; Koopmans appendix pp. 261–262 | `Model.FeasiblePath` (namespace `RamseyCassKoopmans`), `Cass.FeasiblePath.resource_derivative` | Continuous controls, positive consumption, classical capital derivatives; investment sign separate |
| Cass costate and complementary slackness, p. 235 | `cassSupportingPrices`, `cass_certificate_is_optimal` | Sufficient certificate for a supplied Cass-feasible path |
| Koopmans Proposition G, p. 246; appendix equation (43), p. 263 | `finite_horizon_comparison` | Proved calculus and finite integrals, with terminal capital retained |
| Koopmans p. 250, Appendix A7 pp. 278–279 | `infinite_horizon_optimality`, `Terminal.*` | Finite limiting welfare and explicit terminal limit; bounds/price decay proved separately |
| Cass p. 236; Koopmans Proposition H, p. 247 | `existsUnique_positive_stationary_pair_of_inada` | Positive discount/nonnegative discount versions as stated; strict concavity and explicit boundary conditions |
| Golden rule and impatience comparison | `golden_rule_strictly_maximizes_consumption`, `stationary_capital_lt_golden_rule_of_strictConcave` | Global comparison of stationary consumption and capital |
| Stationary optimality | `exists_stationary_optimal_path_of_inada` | Constructed optimum when initial capital equals the derived stationary stock |
| Consumption Euler equation, Koopmans p. 276, and positive-limit verification, pp. 278–279 | `euler_implies_current_value_costate`, `convergent_euler_candidate_optimal` | Chain rule proved; positive consumption convergence remains a hypothesis |
| Strict concavity and uniqueness, Cass p. 235; Koopmans pp. 278–279 | `strict_welfare_separation`, `path_eq_of_welfare_eq` | Strict pointwise gaps integrated on positive measure; supplied candidate, finite welfare and terminal conditions |
| Original illustrative specialization | `Examples.logSqrtPath_optimal` | Actual log/square-root economy with stationary initial stock; not a claimed equation copied from a source |
| Cass's arbitrary-stock conclusion, pp. 237–238, specialized to square-root production and utility | `ClosedForm.cass_dynamic_theorem`, `ClosedForm.every_optimum_eq` | Constructed existence, optimality, uniqueness and monotone convergence for every `k0>0`; the functions and `d=m=1` are fixed |
| Cass's possible initial zero investment, p. 237 | `CornerDynamics`, `CornerPath`, `CornerOptimality` | Explicit prefix, actual switch regularity, costate and complementarity; independently derived formulas |
| Welfare existence in the explicit economy | `exists_hasWelfare_of_nonneg_bounded`, `ClosedForm.cass_path_hasWelfare` | Discounted finite welfare derived for every Cass-admissible competitor |
| Cass's general arbitrary-stock existence and asymptotic argument, pp. 237–238 | `cass_general_dynamic`, `CassInadaData`, `CassConstruction`, `CassConstructedOptimality` | Constructed global path for general C2 primitives; capital/consumption monotonicity, constant steady path, convergence, eventual positive investment, all-competitor asymptotic dominance and finite-welfare uniqueness; continuous controls |

Module names in the table are file locations; most declarations live directly
in namespace `RamseyCassKoopmans`, not in a namespace named after their module.

## Terminal-sign correction

The official scan's equation (25), printed p. 246, contains

\[
\int_0^T p_t(c_t-\widehat c_t)\,dt
\le \int_0^T(q_t+\dot p_t)(k_t-\widehat k_t)\,dt
-p_T(k_T-\widehat k_T).
\]

With the Euler price equation, the correct bound is therefore
`p(T) * (candidateCapital(T) - competitorCapital(T))`.
The printed equations (29)–(30), pp. 248 and 250, reverse this sign. The
accompanying prose describes consumption revenue plus terminal capital value,
consistent with the corrected bound. This is our documented algebraic correction
of an apparent printing error, not a claim to have located a historical erratum.
TheoryDebugger refutes the reversed algebraic inference; Lean proves the actual
finite-horizon inequality. Vanishing of the terminal term leaves the limiting
optimality argument unaffected by this printing discrepancy.

## Version and model differences

The 1963 Koopmans draft's Proposition H uses an Euler-only characterization.
Published Proposition I, p. 248, includes convergence to stationary capital.
Published appendix p. 279 expressly recognizes feasible nonoptimal Euler
trajectories with consumption tending to zero. We do not infer optimality from
Euler alone or hide convergence inside feasibility.

The published appendix assumes utility tends to negative infinity at zero.
Our verification theorem does not require that utility-level boundary limit;
its explicit positive-consumption and finite-welfare scope makes it a separately
stated sufficiency result. Stationary Inada existence uses an infinite marginal
product at zero, a modern boundary formulation distinct from Koopmans's displayed
finite `f'(0)` upper-discount bound. The finite-bracket stationary theorem is also
available. Cass's stronger investment constraint is never silently transferred
to Koopmans's model.

The dynamic specialization uses `U(c)=2*sqrt(c)`, whose marginal utility diverges
at zero but whose utility level does not tend to negative infinity. It therefore
does not instantiate all of Koopmans's published appendix assumptions. Its
unconstrained-investment version is a separately stated verification result.

The **general-function Cass construction** is now proved by global ODE,
comparison, connectedness and finite drift estimates; see the
[detailed argument](cass-general.md). It includes the investment corner and
derives convergence without assuming a stable manifold. For the regular interpretation of Koopmans's unconstrained
investment characterization, the extracted scalar assumptions admit a proved
boundary obstruction. See [the explicit economy and proof](koopmans-boundary-obstruction.md).
Cass's investment constraint is not transferred to that model, and a repaired
Koopmans existence theorem is not silently substituted for the source statement.

## New source-assumption diagnostic

`KoopmansBoundaryEconomy.displayed_assumptions` and `utility_at_zero` verify the
appendix scalar conditions for `f(k)=8k/(1+k)` and `U(c)=c-1/c`, with `d=m=1`.
`KoopmansBoundary.no_convergent_euler_path` rules out a regular feasible Euler
path from capacity 7 converging to steady capital 1. The proof derives price
decay from capital convergence and derives candidate welfare from the actual
Hamiltonian derivative. A separately constructed positive-welfare competitor
then contradicts verification. No consumption convergence is assumed.

This is a formal obstruction to the attempted regular existence statement,
with the source's weaker right-derivative convention distinguished explicitly.
The detailed note does not claim a historical erratum or general nonexistence
of impulsive or measurable-control optima.
