# A complete dynamic Cass specialization

This document explains the theorem proved in
[`CassSpecialization.lean`](../RamseyCassKoopmans/CassSpecialization.lean).
It realizes the dynamic conclusions of Cass (1965), printed p. 238, for a
specific economy. The formulas below are our independently derived example,
not formulas attributed to Cass. The general-function existence theorem remains
separate unfinished work.

## Statement and scope

Fix

\[
f(k)=2\sqrt{k},\qquad U(c)=2\sqrt{c},\qquad d=m=1.
\]

This is Cobb–Douglas production with exponent one half and CRRA utility with
relative risk aversion one half. **It is not the logarithmic utility used in the
library's earlier stationary example.** For every initial stock \(k_0>0\),
among the library's Cass-admissible paths there is a unique optimum. Capital and
consumption converge to

\[
k^*=\frac14,\qquad c^*=\frac34.
\]

They increase strictly when \(k_0<k^*\), decrease strictly when \(k_0>k^*\),
and are constant when \(k_0=k^*\). Uniqueness means equality at every
nonnegative time of capital, consumption and investment.

Admissibility means nonnegative capital, strictly positive consumption,
continuous consumption and investment, nonnegative gross investment, and the
classical resource dynamics

\[
c+z=f(k),\qquad \dot k=z-k,\qquad k(0)=k_0.
\]

The objective is the limit of finite integrals
\(J(c)=\lim_{T\to\infty}\int_0^T e^{-t}U(c(t))\,dt\).
For this economy, its existence as a finite real number is **proved for every
admissible competitor**. It is not an extra restriction imposed by the final
dynamic theorem. Measurable controls, zero consumption and equality only almost
everywhere are outside this implementation's admissible class.

## Constructing the interior branch

Let \(x=\sqrt{k}\). The interior policy \(c=3k\) gives

\[
\dot x=1-2x,\qquad
x(t)=\frac12+\left(x_0-\frac12\right)e^{-2t},
\]
\[
k=x^2,\quad c=3x^2,\quad z=2x-3x^2,\quad
q=\frac{1}{\sqrt3\,x}.
\]

Lean proves derivatives of these actual functions, the resource identities and
strict positivity for all nonnegative times. It also proves

\[
U'(c)=q,\qquad f'(k)=\frac1x,\qquad
\dot q=2q-U'(c)f'(k).
\]

For positive \(x\), investment is nonnegative exactly up to \(x=2/3\).
If \(0<k_0\le4/9\), choosing \(x_0=\sqrt{k_0}\) keeps the entire path
in that region. The path's limit follows directly from \(e^{-2t}\to0\);
monotonicity follows from the sign of \(x_0-1/2\).

For larger stocks this interior path is still feasible if disinvestment is
allowed, and its optimality for finite-welfare competitors is also proved.
It is not Cass-admissible: at \(x=1\), for example, investment is \(-1\).
TheoryDebugger supplies a checked counterexample to the incorrect claim that
the same interior construction satisfies Cass's constraint at all stocks.

## Constructing the investment corner

For \(k_0>4/9\), select

\[
\tau=\log\left(\frac{9k_0}{4}\right)>0.
\]

For \(0\le t\le\tau\), set

\[
k(t)=\frac49e^{\tau-t}=k_0e^{-t},\qquad
c(t)=\frac43e^{(\tau-t)/2}=f(k(t)),\qquad z(t)=0.
\]

Write \(r=e^{(t-\tau)/4}\), so \(0<r\le1\). The current-value price is

\[
q(t)=\frac{\sqrt3}{10}(6r^3-r^8),\qquad
U'(c(t))=\frac{\sqrt3}{2}r,\qquad f'(k(t))=\frac32r^2.
\]

The actual exponential derivatives give the costate equation. Positivity of
\(q\) and the investment wedge \(q\le U'(c)\) are proved, using

\[
5r-6r^3+r^8
=r(1-r)(5+5r-r^2-r^3-r^4-r^5-r^6)\ge0.
\]

For \(0\le r\le1\), each power \(r^j\), \(j=2,\ldots,6\), is at
most \(r\), so the last factor is nonnegative. TheoryDebugger checks the
polynomial identity and the sign-product implication; Lean separately proves
the exponential substitution and all its domain bounds.

After \(\tau\), use the interior path with elapsed time \(t-\tau\) and
initial transformed capital \(2/3\). At the switch both branches give

| Quantity | Matching value |
|---|---:|
| Capital | \(4/9\) |
| Consumption | \(4/3\) |
| Investment | \(0\) |
| Current-value price and marginal utility | \(\sqrt3/2\) |
| Marginal product | \(3/2\) |
| Capital derivative | \(-4/9\) |
| Price derivative | \(\sqrt3/4\) |

[`PathGluing.lean`](../RamseyCassKoopmans/PathGluing.lean) proves continuity and
differentiability of the joins from these matching values and derivatives.
Consumption is continuous but has different one-sided derivatives:
\(-2/3\) before and \(-4/3\) after the switch. The proof therefore does not
assume an everywhere differentiable consumption path or an interior Euler
equation during the corner. This distinction is also checked by a
TheoryDebugger counterexample.

## Welfare and optimality

The interior branch has lifetime value

\[
J=\frac{2\sqrt3}{3}(1+\sqrt{k_0}).
\]

For the corner branch, splitting the finite integral at \(\tau\), translating
the tail and then taking the limit gives

\[
J=\frac{16\sqrt3}{15}e^{\tau/4}
  +\frac{2\sqrt3}{45}e^{-\tau}.
\]

Lean evaluates the prefix integral as well as the tail; no undefined infinite
integral is substituted. The formulas agree at \(\tau=0\), where
\(J=10\sqrt3/9\).

For every Cass competitor, resource feasibility bounds capital by
\(K=\max(4,k_0)\), because \(f(k)\le k\) for \(k\ge4\). Nonnegative
investment then bounds consumption by \(2\sqrt K\), and hence felicity by
\(2\sqrt{2\sqrt K}\). Finite-horizon welfare is nondecreasing and bounded
above by this constant, since the discount rate is one. Its finite limit is
proved using monotone convergence of real functions.

The general welfare comparison theorem is then applied to the constructed
supporting prices. Concavity supplies the utility and production tangent
inequalities. The investment wedge and complementary slackness supply the
allocation inequality, including the corner. Present-value prices tend to zero
because the current-value price has a finite limit and discounting is positive.
Bounded capital therefore makes the terminal boundary term vanish.

Strict concavity makes a difference in consumption or capital give a strict
welfare gap. The library proves that a pointwise strict gap persists over an
interval and has a strictly positive integral. Thus equality of lifetime welfare
forces equality of the whole path, and every optimum equals the construction.

## Where to inspect each proof

| Obligation | File / declaration |
|---|---|
| Interior path, derivatives, limits, welfare | `ClosedFormDynamics.lean` |
| Prefix, actual costate and wedge | `CornerDynamics.lean` |
| Matching branches and global feasibility | `CornerPath.lean`, `PathGluing.lean` |
| Finite-integral splitting and tail limit | `TailWelfare.lean` |
| Corner optimality and evaluated value | `CornerOptimality.lean`, `cornerValue_eq` |
| Uniqueness and component monotonicity | `GlobalCass.lean` |
| Automatic welfare existence | `BoundedWelfare.lean`, `cass_path_hasWelfare` |
| All dynamic conclusions together | `CassSpecialization.lean`, `cass_dynamic_theorem` |
| Necessity of the constructed optimum | `every_optimum_eq`, `every_optimum_converges` |

The primary reference and version distinctions are in the
[source map](source-map.md). In particular, square-root utility has finite value
at zero and therefore does not satisfy the published Koopmans appendix's
negative-infinite utility-level boundary condition. The code does not advertise
this example as a proof of his full Proposition I.
