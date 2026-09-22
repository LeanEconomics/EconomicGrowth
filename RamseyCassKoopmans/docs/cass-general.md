# General Cass construction: statement and proof

The principal Lean theorem is `RamseyCassKoopmans.cass_general_dynamic` in
[`CassGeneral.lean`](../RamseyCassKoopmans/CassGeneral.lean). This is an original
formal proof of the positive-discount Cass conclusion, motivated by Cass (1965),
pp. 233–238. The square-root formulas are not used in its trajectory construction.

## Statement and assumptions

Let `d>0`, `m>0`, and `k0>0`. Production satisfies `f(0)=0`, is strictly concave
on nonnegative capital, has positive marginal product, and has continuous first
and second derivatives on positive capital. Its marginal product tends to
infinity at zero and to zero at infinity. Utility is strictly concave on positive
consumption, with positive marginal utility, continuous first and second
derivatives, strictly negative second derivative, and marginal utility tending
to infinity at zero. No third derivative is assumed.

The [source comparison](source-map.md#version-and-model-differences) records
the differences from Cass's displayed assumptions: the formal statement makes
`f(0)=0` and derivative continuity explicit and uses a regular admissible class
with strictly positive consumption. It does not assert coverage of every
control allowed by the paper.

There is a unique positive stationary stock `ks` satisfying `f'(ks)=d+m`.
The proof constructs a feasible path from `k0` with nonnegative gross investment,
finite lifetime welfare, and capital and consumption limits

\[
 k(t)\to k_s,\qquad c(t)\to f(k_s)-mk_s>0.
\]

Capital and consumption increase strictly when `k0<ks` and decrease strictly
when `k0>ks`. At `k0=ks` the entire path is constant. Below steady initial
capital, investment is positive at every nonnegative time. From any initial
stock, investment is strictly positive after some finite time.
The path maximizes welfare among the library's Cass-feasible competitors with
finite real limiting welfare. Every optimum with that initial stock has exactly
the same capital, consumption and investment at every nonnegative time.

Feasibility means continuous consumption and investment, positive consumption,
nonnegative capital, and an actual classical derivative satisfying the resource
equation. The theorem does not claim all measurable-control extensions or that
every competitor has finite welfare. It proves the stronger comparison
`AsymptoticallyDominates` against every feasible Cass competitor, without a
competitor welfare-limit assumption: for each `epsilon>0`, the competitor's
finite-horizon welfare advantage is eventually smaller than `epsilon`.
An explicit single switching-time formula is proved in the square-root
specialization; the general result retains the corner equations and proves
eventual interior investment.

## 1. Use capital and marginal-utility prices

Write `mu=U'`, `lambda=d+m`, and let `C` denote inverse marginal utility. The
constrained consumption and investment are

\[
 c(k,q)=\min\{C(q),f(k)\},\qquad z(k,q)=f(k)-c(k,q)\ge0.
\]

The current-value system is

\[
 \dot k=z-mk,\qquad
 \dot q=\lambda q-\max\{q,\mu(f(k))\}f'(k).
\]

Lean proves `mu(c)=max(q,mu(f(k)))`, the wedge `q<=mu(c)`, and complementary
slackness `(q-mu(c))*z=0`. The field is continuous even at the investment switch;
an interior consumption Euler equation is not imposed on a corner.

## 2. Construct the inverse and global auxiliary solutions

On a finite positive consumption interval, continuity and strict negativity of
`mu'` give a uniform negative derivative bound by compactness. The mean value
theorem gives a quantitative decrease bound. The intermediate value theorem
then constructs `C`; the same bound proves it is Lipschitz and antitone.

Clipping capital and prices to finite intervals makes the field bounded and
globally Lipschitz. Picard–Lindelof supplies finite-window solutions, uniqueness
glues them into a global flow, and Gronwall proves continuous dependence on
initial conditions. The flow composition law is proved from ODE uniqueness.

These are auxiliary equations only. Step 5 proves their clipping is inactive on
the selected future path.

## 3. Select a path by connectedness

The field is cooperative: capital velocity increases with price, and price
velocity increases with capital. The strict lower and strict upper quadrants
relative to `(ks,qs)` are forward invariant. Simultaneous exponential barriers
prove weak order comparison; a signed Gronwall bound proves strict invariance.

Very low initial prices force capital down far enough to enter the lower
quadrant in finite time. Very high prices keep consumption low long enough to
enter the upper quadrant. Both endpoint escapes are proved with explicit finite
time and velocity bounds. Initial prices that eventually enter either open
quadrant form disjoint open sets. An interval of initial prices is connected,
so some initial price avoids both escape sets forever.

## 4. Derive monotonicity and identify the limit

The selected path cannot reach equilibrium at a finite time unless it started
there, by ODE uniqueness. The capital-axis velocity points into an escape region
at every other point of that axis, so the selected path stays on its initial
side of stationary capital.

Below steady capital, the price velocity is negative. If capital velocity were
nonpositive, order comparison with a constant supersolution would trap the
future below its current point. A uniform negative price drift would then force
escape in finite time, a contradiction. Thus capital rises and price falls.

Above steady capital, a nonnegative capital velocity would imply a positive
price velocity and force upper escape. A nonpositive price velocity implies a
corner; comparison preserves zero investment and forces capital down through
steady capital in finite time. Both are impossible. Thus capital falls and
price rises, including along any permitted corner segment.

Both coordinates are now monotone and bounded. Their finite limits exist.
Continuity of the autonomous field makes the derivative converge to the field
at the limit. A nonzero limiting derivative would force unbounded drift by the
mean value theorem, so the limit is an equilibrium. The clipped field has only
one equilibrium, proved algebraically using strict marginal-product decrease:
the actual steady state.

## 5. Remove all artificial bounds

Capital lies between its positive initial and steady stocks. On the upper
branch, nonpositive prices contradict the proved positive price velocity, and
prices remain below steady price. On the lower branch,

\[
 q(t)\ge q(0)\exp(-f'(k_l)t).
\]

Choose a positive consumption threshold below net output at `kl`, and a finite
time long enough for the corresponding capital drift to cross `ks`. An initial
price above a sufficiently large bound would stay above that threshold price
for the entire finite time, forcing capital to cross `ks`, a contradiction.
The Inada limit of marginal utility chooses a positive consumption floor whose
price exceeds precisely this finite bound. Thus the selected initial price,
and all subsequent prices, are inside the price interval. The original economic
field and the auxiliary field coincide everywhere on the selected future path.

## 6. Verify welfare and uniqueness

The constructed consumption remains in a compact positive interval. Continuity
of utility bounds its absolute value there. Decomposing felicity into positive
and negative parts proves finite discounted welfare, without assigning a value
to a divergent infinite integral.

The actual costate, wedge and slackness identities feed the existing Cass
verification theorem. Concavity and vanishing marginal product supply a finite
capital capacity for every competitor. Positive discounting and convergence of
the constructed price make the terminal comparison vanish. Strict concavity
then forces equality of capital, consumption and investment whenever a
competitor attains the same welfare. Applying optimality in both directions
establishes necessity for any other optimum; no Euler equation or convergence
is assumed of that competitor.

The same finite-horizon inequality gives asymptotic dominance without assuming
that competitor welfare converges. Its welfare advantage is bounded above by
the terminal capital term, which tends to zero.

## 7. Consumption and investment conclusions

For the lower branch, capital rises and price falls. Strict increase of
production and strict decrease of marginal utility imply that both arguments
of `max(q,U'(f(k)))` fall strictly; therefore consumption rises strictly.
On the upper branch both arguments rise strictly, so consumption falls strictly.
This proof uses the marginal-utility identity and never differentiates
consumption at a corner.

The constructed constant trajectory supplies the steady-state case. Investment
converges to `m*ks>0`, so every corner ends before some finite time. On the lower
branch, nonpositive investment would give strictly negative capital drift,
contradicting capital monotonicity. Finally the gross saving rate converges to
`m*ks/f(ks)`, which is strictly between zero and one. These results are in
[`CassQualitative.lean`](../RamseyCassKoopmans/CassQualitative.lean).

## Verification and provenance

The complete source is freshly elaborated by `scripts/verify.py`, and every
named theorem and definition is checked for extra axioms. The current milestone
has 423 theorems and 576 audited declarations across 52 modules. Allowed axioms are
only `propext`, `Classical.choice`, and `Quot.sound`. The existing TheoryDebugger
record supplies 24 algebra diagnostics and 48 Lean-verified certificates; the
global analytic construction is checked directly by Lean and Mathlib.

Original formalization and exposition: OpenAI Codex, under the direction of
[@mvazcar](https://github.com/mvazcar), using Astra 6 Ultra and Extra High.
TheoryDebugger complements TheoryGuru. Original project files use the Unlicense;
the cited papers and dependencies retain their own terms.
