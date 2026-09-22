# Koopmans: a certified obstruction at the capacity boundary

The proposed general existence statement cannot be proved for regular Euler
paths under the scalar assumptions we extracted from the published appendix.
There is an explicit economy satisfying those assumptions in which **no feasible
regular Euler path from the capacity stock converges to stationary capital**.
This is a theorem about actual functions, derivatives, finite integrals and
limits, not a numerical shooting failure.

The principal declaration is
[`KoopmansBoundary.no_convergent_euler_path`](../RamseyCassKoopmans/KoopmansBoundaryObstruction.lean).
Neither consumption convergence, monotonicity, transversality, optimality nor
finite candidate welfare is assumed. Positive capital is derived from
feasibility. The proof derives finite welfare and price decay before obtaining
a contradiction.

## Source and exact interpretation

The source is Tjalling C. Koopmans (1965), *On the Concept of Optimal Economic
Growth*, Scripta Varia 28, Part I, pp. 225–287, in the
[official scanned volume](https://www.pas.va/content/dam/casinapioiv/pas/pdf-volumi/scripta-varia/sv28apas.pdf).
Proposition I is on printed p. 248 (PDF p. 285); appendix A2 assumptions and
feasibility are on printed pp. 261–262 (PDF pp. 298–299); the Euler system and
existence discussion are on printed pp. 276–279 (PDF pp. 313–316).

The displayed utility conditions are positive marginal utility, strictly
negative second derivative, and utility tending to minus infinity at zero.
They do not impose marginal utility tending to zero at infinity. Disinvestment
is allowed: consumption is not bounded above by current production.

Our checked path class uses continuous controls and classical capital
derivatives; the Euler candidate additionally has a classical consumption
derivative at every nonnegative time. The source uses right derivatives and
right continuity in its feasible-path convention. Thus the precise formal
conclusion concerns the regular ODE interpretation we were attempting to
formalize. It is not a theorem about all measurable, discontinuous or impulsive
controls. The source-level interpretation and any historical correction merit
separate human review; we have not located or claimed a published erratum.

## 1. The economy satisfies the displayed scalar assumptions

Take effective utility discount and capital dilution `d=m=1`, and

\[
 f(k)=\frac{8k}{1+k},\qquad U(c)=c-\frac1c.
\]

For `k≥0` and `c>0`,

\[
 f'(k)=\frac8{(1+k)^2}>0,\quad f''(k)=-\frac{16}{(1+k)^3}<0,
\]
\[
 U'(c)=1+\frac1{c^2}>0,\quad U''(c)=-\frac2{c^3}<0.
\]

We have `f(0)=0`, `f'(0)=8`, and `U(c)→−∞` as `c→0+`.
For every `0<m<8`, the positive capacity stock is `8/m−1`.
At `m=1`, capacity is `kbar=7`. The positive discount bound holds:
`0<d=1<f'(0)−m=7`. The stationary stock and consumption are

\[
 k_s=1,\qquad f'(1)=d+m=2,\qquad c_s=f(1)-1=3.
\]

The key boundary feature is `U'(c)→1` as `c→∞`.
[`KoopmansBoundaryEconomy.lean`](../RamseyCassKoopmans/KoopmansBoundaryEconomy.lean)
proves the derivatives, strict concavity, limits, capacity and scalar assumptions.
Its globally defined Lean production function is written `8−8/(1+k)`;
`production_formula` proves the displayed expression on nonnegative capital.

## 2. Suppose a convergent Euler path existed

Write `g(k)=f(k)−k`, and let `q=U'(c)`. The resource and Euler equations give

\[
 \dot k=g(k)-c,\qquad \dot q=(2-f'(k))q.
\]

Suppose `k(0)=7` and `k(t)→1`. Present-value marginal utility
`p(t)=e^{−t}q(t)` then satisfies

\[
 \dot p=(1-f'(k))p.
\]

Its logarithmic derivative tends to `−1`. Eventually it is at most `−1/2`.
An explicit Grönwall estimate proves `p(t)→0`. This step does **not** require
consumption to converge or marginal utility to be bounded.
The reusable estimate is in
[`ExponentialDecay.lean`](../RamseyCassKoopmans/ExponentialDecay.lean).

## 3. The Hamiltonian forces negative candidate welfare

Define the current-value Hamiltonian

\[
 H=U(c)+q\bigl(g(k)-c\bigr).
\]

The chain and product rules, resource law and costate equation imply

\[
 \dot H=q\dot k,\qquad \frac{d}{dt}(e^{-t}H)=-e^{-t}U(c).
\]

For this utility, an exact simplification gives

\[
 H=qg(k)-\frac2c,\qquad 0<\frac2c\le q.
\]

Since `p→0` and `g(k)→3`, both `p g(k)` and `e^{−t}2/c` tend to zero.
Consequently `e^{−t}H→0`. Integrating the actual Hamiltonian derivative on
each finite interval, then taking the limit, proves

\[
 J_a=\lim_{T\to\infty}\int_0^T e^{-t}U(c(t))\,dt
     =H(0)=-\frac2{c(0)}<0.
\]

The final equality uses `g(7)=0`. Finite welfare is a conclusion here, not an
assumption or an assigned value for a divergent improper integral.
[`Hamiltonian.lean`](../RamseyCassKoopmans/Hamiltonian.lean) contains the reusable
derivative identities and primitive-to-welfare theorem.

## 4. An explicit feasible competitor has positive welfare

Construct

\[
 k_b(t)=1+6e^{-t},\qquad z_b(t)=1,\qquad c_b(t)=f(k_b(t))-1.
\]

It starts at `7`, satisfies `k_b'=1−k_b`, and satisfies the resource equation.
Consumption remains in a compact positive interval; the checked bounds are
`3≤c_b(t)≤7`. Thus

\[
 U(c_b(t))\ge\frac83,\qquad J_b\ge\frac83>0,
\]

with finite `J_b`. These are proved in
[`KoopmansBoundaryCompetitor.lean`](../RamseyCassKoopmans/KoopmansBoundaryCompetitor.lean).

But strict concavity supplies supporting utility and production prices along
the hypothetical Euler candidate. Every feasible path from `7` has capital
bounded by `7`, by the resource law and the proved production capacity bound.
The finite-horizon comparison and `p→0` therefore imply `J_b≤J_a`.
This contradicts `J_b≥8/3>0>J_a`.

An additive normalization of utility cannot remove the contradiction: it
shifts both discounted welfare values by the same constant.

## What this changes in the project

The general Cass theorem remains valid: it retains the nonnegative-investment
constraint, and its construction has been checked independently. Koopmans
verification of a supplied candidate also remains valid; the obstruction uses
that verification argument.

What fails in this example is existence of the proposed regular convergent
Euler candidate under the extracted scalar assumptions. Requiring
`U'(c)→0` as `c→∞` excludes this example and is a natural additional boundary
condition to investigate. This document does **not** claim that adding that
condition alone has already been proved sufficient for a repaired general
existence theorem. Such a theorem must state and prove its own assumptions.

TheoryDebugger checks the local Hamiltonian algebra and refutes a nonnegative
capacity-Hamiltonian claim with an exact rational witness. The analytic
nonexistence argument is separately checked by Lean. The full audit freshly
elaborates the source and permits only Lean's standard axioms.

Original formalization and exposition: OpenAI Codex, under the direction of
[@mvazcar](https://github.com/mvazcar), using Astra 6 Ultra and Extra High.
Original project files use the Unlicense; source publications retain their own
terms. TheoryDebugger is a complement to TheoryGuru.
