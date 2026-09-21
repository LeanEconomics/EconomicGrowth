# Proof status and remaining work

The library contains checked definitions and proofs, not statements completed
with `sorry` or additional axioms. The source and axiom audit is reproducible.

## Completed analytic core

1. Actual feasible paths and a discount convention.
2. Concavity-to-tangent inequalities and strict remainders.
3. TheoryDebugger-checked polynomial identities and false-claim counterexamples.
4. Boundary differentiation, finite-interval integrability, the fundamental
   theorem of calculus, and the finite-horizon welfare comparison.
5. Infinite-horizon verification for finite limiting welfare.
6. Capacity bounds from resource dynamics and price decay from discounting.
7. Inada-to-brackets, unique stationary capital/consumption, and golden rule.
8. A constructed stationary optimal path and its explicit finite welfare.
9. Cass's current-value costate/complementarity bridge, including feasibility
   of both the candidate and its competitors in the Cass optimality predicate.
10. The consumption Euler equation's chain-rule bridge and verification of
    candidates with an assumed positive consumption limit.
11. Strict welfare separation and equality of capital, consumption and investment
    for equal-welfare paths under the explicit strict-concavity hypotheses.
12. A concrete log-utility, square-root-production stationary optimum with
    `d=m=1`, `k*=1/4`, `c*=3/4` and lifetime welfare `log(3/4)`.

## Completed dynamic specialization

For `f(k)=2*sqrt(k)`, **`U(c)=2*sqrt(c)`**, and `d=m=1`, the library now proves:

1. An explicit globally feasible interior trajectory for every positive initial
   stock when disinvestment is permitted.
2. The exact threshold `k0=4/9` for this path's Cass investment constraint.
3. A zero-investment prefix for larger stocks and its explicitly selected
   switching time `log(9*k0/4)`.
4. Continuous controls and classical capital/price derivatives at the join.
   Consumption need not be differentiable at the switch.
5. Actual marginal utility/product, costate dynamics, the investment wedge and
   complementary slackness, including the corner.
6. Capital and consumption convergence derived from explicit paths, together
   with strict monotonicity and the constant steady-state case.
7. Finite welfare for every Cass competitor, derived from feasibility and a
   capital bound; this hypothesis is discharged for the entire admissible class.
8. The optimal lifetime value, including an evaluated corner prefix integral.
9. Optimality and uniqueness of the entire path for every `k0>0`.
10. Equality with the constructed path, and hence convergence, for any optimum.

The principal statement is `ClosedForm.cass_dynamic_theorem`; necessity of the
constructed path is `ClosedForm.every_optimum_eq`. The
[detailed proof](cass-square-root.md) gives the formulas and economic scope.

## Exact restrictions

* Consumption is strictly positive and controls are continuous. Capital has a
  classical derivative at each nonnegative time (the capacity lemma itself
  only needs right derivatives).
* In the general verification theorems, compared objectives converge to finite
  real values. For the complete square-root Cass specialization that convergence
  is proved for every admissible competitor. The general Cass theorem additionally proves asymptotic dominance using
  finite-horizon welfare differences for every competitor, including those
  without finite limiting objectives. It does not assert that all objectives
  converge to real values.
* General verification receives a candidate and its price/Euler certificate.
  Where convergence is an input, the theorem does not purport to prove it.
* General-function constructed existence now covers every positive initial
  stock under the explicit Inada and C2 assumptions of `cass_general_dynamic`.
  The statement proves finite welfare for the constructed candidate, not for
  every general-utility competitor.

## Completed general Cass construction

`cass_general_dynamic` now constructs the path from primitives and proves
optimality, uniqueness of every optimum, strict capital and consumption monotonicity away from
steady state, the constant steady path, eventual positive investment, and
capital/consumption convergence. It also proves asymptotic welfare dominance
over every Cass competitor without a finite-welfare assumption. The proof constructs inverse
marginal utility on a compact interval, obtains global Lipschitz ODE solutions,
uses connected shooting between two invariant escape regions, proves the
selected path's monotonicity and limit, and removes every auxiliary clipping
bound. The Inada condition supplies the quantitative upper-price bound. Finite
candidate welfare also holds for utility that takes negative values.

The fresh source audit at this milestone checks 423 theorems and 576 audited
declarations in 52 modules. See [the general proof](cass-general.md).

## Koopmans boundary obstruction

The general regular Euler existence claim under the extracted published scalar
assumptions has an explicit obstruction, now proved in Lean. The economy
`f(k)=8k/(1+k)`, `U(c)=c-1/c`, `d=m=1` satisfies those assumptions but has no
regular feasible Euler path from capacity `k0=7` with capital converging to
`ks=1`. No consumption-convergence, monotonicity, finite-welfare or terminal
hypothesis is assumed in the contradiction. See the
[detailed proof and exact source correspondence](koopmans-boundary-obstruction.md).

Thus this missing existence statement cannot honestly be filled by a proof
within the stated regular interpretation. A repaired disinvestment theorem
requires an explicitly revised assumption set; adding marginal utility tending
to zero at infinity excludes the example, but a general sufficiency theorem
under that repair is not claimed here. The published right-derivative convention
and generalized controls require separate treatment.

## Separate extensions

Ramsey's undiscounted bliss criterion and Koopmans's zero/negative-discount
results are separate extensions. They are not obtained by setting `d = 0` in
the positive-discount price-decay proof. The general Cass theorem proves eventual
interior investment; a single-switch formula is supplied for the explicit
square-root specialization, not asserted for every pair of primitive functions.
