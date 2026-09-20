# Uzawa: two Jones-Scrimgeour arguments and Schlicht's contribution

> Research note from TheoryDebugger. Links to diagnostic examples and archived
> contribution checks point to that repository. The standalone modules here have
> their own build and fresh axiom audit: run `python scripts/verify.py` from this
> repository root and consult `verification/verification.json`. Our original
> material in this standalone distribution uses The Unlicense.

Research comparison, 20 September 2026. This note distinguishes the papers'
claims, our mathematical audit, and the exact statements checked by Lean.
The November 2004 argument is not a second completed formal proof.

**Implementation update:** the [repaired elasticity theorem](uzawa-elasticity-repaired.md)
is now completed with explicit global range and domain-wide share assumptions.
There are two checked representation arguments with a shared accounting
lemma. The source-version audit below still applies to the literal 2004 text.

## Original source

Uzawa (1961), *Neutral Inventions and the Stability of Growth Equilibrium*,
Review of Economic Studies 28(2), 117–124, is the original reference.
See the [source status and proposed original-paper formalization](uzawa-1961-source.md).
The modern results below do not claim to formalize every result in that paper.

## Source versions

- **Jones and Scrimgeour, November 2004.** *The Steady-State Growth Theorem:
  A Comment on Uzawa (1961)*, NBER Working Paper 10921. This is the user's
  supplied PDF. Definitions: printed pp. 3-4; proof: pp. 5-7.
  [NBER record](https://www.nber.org/papers/w10921).
- **Schlicht, 2006.** *A Variant of Uzawa's Theorem*, Economics Bulletin
  5(6), cited as pp. 1-5. The downloaded journal PDF has a cover and four
  numbered pages; the mathematical argument is on numbered pp. 1-2.
  [Publisher PDF](https://www.accessecon.com/pubs/EB/2006/Volume5/EB-06E10001A.pdf).
  The [LMU repository](https://epub.ub.uni-muenchen.de/897/) also supplies
  Munich Discussion Paper 2006-8; we downloaded that version separately.
- **Jones and Scrimgeour, 2008.** *A New Proof of Uzawa's Steady-State Growth
  Theorem*, Review of Economics and Statistics 90(1), 180-182,
  DOI [10.1162/rest.90.1.180](https://doi.org/10.1162/rest.90.1.180).
  [Author-hosted PDF](https://web.stanford.edu/~chadj/JonesScrimgeour2008.pdf).
  The theorem and proof are on p. 181. Its reference to an earlier working
  paper concerns a **2005 revision**; we have not treated that revision as
  byte-identical to the supplied November 2004 PDF.

The PDFs and their hashes are in the local research archive, outside the
code release. Equations below use consistent notation and our own exposition.

## Shared question and notation

There is one reproducible capital good, with output and accumulation

\[
Y(t)=F(K(t),L(t),t),\qquad
Y(t)=C(t)+I(t),\qquad
\dot K(t)=I(t)-\delta K(t),\qquad
L(t)=L_0e^{nt}.
\]

Use lower-case \(y=Y/L\), \(k=K/L\), and \(x=K/Y=k/y\).
Let \(g_Y,g_K,g_I,g_C\) denote aggregate growth rates, and
\(g=g_Y-n\) output-per-worker growth. Schlicht uses different symbols
and puts labor first in the production function; this note puts capital first.

The target is a **representation along the given path**:

\[
Y(t)=G(K(t),A(t)L(t)),\qquad \dot A/A=g.
\]

That statement neither identifies the actual invention process nor asserts
equality of technologies at all counterfactual capital/labor combinations.
A proof must also say what properties G has and whether it is the original
technology frozen at a reference date.

## 2004: the capital/output elasticity argument

The written theorem assumes a neoclassical technology, including constant
returns, positive and diminishing marginal products, and Inada conditions;
positive initial capital and labor; nonnegative depreciation and labor growth;
constant exponential growth of the quantities; constant, nonzero factor
shares; and strictly positive output-per-worker growth. It concludes that
a neoclassical G exists with the path representation above. **Positive
investment is not an explicit condition in this supplied version.**

The following reconstructs its four steps, retaining the obligations that
a formal proof must discharge.

### 1. Change the coordinate from capital per worker to capital/output

At fixed t, put \(f(k,t)=F(k,1,t)\), so \(y=f(k,t)\), and define

\[
h(k,t)=\frac{k}{f(k,t)},\qquad
\alpha(k,t)=\frac{k f_k(k,t)}{f(k,t)}.
\]

The quotient rule gives

\[
h_k=\frac{f-kf_k}{f^2}=\frac{1-\alpha}{f}>0
\]

when output is positive and the labor share \(1-\alpha\) is positive.
A continuously differentiable h with nonzero derivative has a local inverse.
For a global inverse one must specify its image and prove the relevant
monotonicity and range results; nonzero derivatives alone do not prove
surjectivity onto all positive numbers. Where the inverse is justified, write

\[
\kappa(x,t)=h(\cdot,t)^{-1}(x),\qquad
\phi(x,t)=f(\kappa(x,t),t).
\]

### 2. Derive the elasticity identity

The identity \(\kappa=x f(\kappa,t)=x\phi\) holds on a neighborhood,
not merely at one observed point. Differentiating it at fixed t yields

\[
\kappa_x=\phi+x f_k\kappa_x,
\qquad
\frac{x\phi_x}{\phi}
=\frac{x f_k}{1-x f_k}
=\frac{\alpha}{1-\alpha}.
\]

This explains how a capital-share calculation controls the elasticity of
output with respect to capital/output. These quotient, sign, and elasticity
calculations are the **three existing Lean lemmas**. The inverse and its
differentiability are hypotheses of the third lemma, not conclusions.

### 3. Separate technology from the capital/output coordinate

The paper moves from steady-state share constancy to a time-independent
right-hand side and integrates the elasticity equation to obtain

\[
\log\phi(x,t)=a(t)+\int\frac{\alpha(x)}{1-\alpha(x)}\frac{dx}{x},
\qquad
\phi(x,t)=A(t)\psi(x).
\]

**Our audit:** constancy of \(\alpha(x(t),t)\) along one path is a condition
on a curve. Integration with respect to x requires an identity on an interval
of x values. These are different quantifiers. A rigorous version must supply
the latter condition or avoid this integration. It must also establish that
\(x(t)\) is constant before inferring from \(y=A\psi(x)\) that
\(\dot A/A=\dot y/y\).

There is a simple independent diagnostic for the quantifier problem. On an
interval around x=1, take

\[
\phi(x,t)=\exp\{t+q\log x+\varepsilon\sin(t)(\log x)^2\},\quad q>0.
\]

Its elasticity is \(q+2\varepsilon\sin(t)\log x\), hence equals q
at x=1 for every t. Nevertheless, for x different from 1 the ratio
\(\phi(x,t)/\phi(1,t)\) depends on t. For nonzero epsilon this excludes
separation on a product neighborhood. This is a smooth local diagnostic,
not a claim that this particular phi defines a globally neoclassical economy.

### 4. Construct the proposed G

If separation is justified and \(\psi\) is invertible, let
\(z=y/A=\psi(x)\). Then

\[
\frac{k}{A}=xz=z\psi^{-1}(z).
\]

Invert \(z\mapsto z\psi^{-1}(z)\) on its justified range, obtaining H.
Define \(G(K,E)=E H(K/E)\). This gives the desired algebraic form.
Positive derivatives help establish injectivity; domains and ranges still
matter. Neoclassical properties of G must be proved. Equality of F and G
only at the observed points does not, by itself, transfer their derivatives,
curvature, or Inada limits away from those points.

## A boundary case admitted by the supplied 2004 statement

This is our mathematical audit, not a quotation from the papers. Let

\[
F(K,L,t)=e^t\sqrt{KL},\quad K(t)=L(t)=1,\quad
Y(t)=C(t)=e^t,\quad I(t)=0,\quad\delta=n=0.
\]

Production, the resource equation, and accumulation all hold. Every quantity
used in the 2004 definition has a constant exponential path. Output per worker
grows at rate 1; both factor shares equal 1/2. At each fixed t, for positive
inputs,

\[
F_K=\tfrac12e^t\sqrt{L/K}>0,\qquad
F_{KK}=-\tfrac14e^t\sqrt L\,K^{-3/2}<0,
\]

with the symmetric expressions for labor. The marginal products have the
required zero/infinity limits, so the usual neoclassical conditions hold.
Yet \(K/Y=e^{-t}\) is not constant.

The elasticity calculation remains valid: \(x=e^{-t}\sqrt{k}\) implies
\(\phi(x,t)=e^{2t}x\). Thus even exact separation here supplies a technology
factor with growth 2, not the required output-per-worker growth 1.

Could a different neoclassical G rescue the stated conclusion? No. Any
positive differentiable A with growth 1 is \(A(t)=a e^t\), a>0. The proposed
representation would require

\[
G(1,a)=1,\qquad G(1,ae)=e.
\]

Constant returns applied to the second equality gives
\(G(e^{-1},a)=1\). Since \(e^{-1}<1\), this contradicts strict increase
in capital at fixed effective labor. The argument works for every a>0.

**Verification boundary:** the local research file `UzawaVersionAudit.lean`
checks this two-point obstruction and its application to explicit exponential
A paths for arbitrary constant-returns, strictly increasing G. The existing
TheoryDebugger example checks the economic identities and failure with the
frozen original F. The derivative/Inada calculations above and the general
ODE characterization A=ae^t are presented mathematically here; they are not
claimed as part of an end-to-end Lean encoding of the 2004 model.

Consequently the literal supplied assumptions need repair; finishing the
remaining Lean steps cannot turn this counterexample into a proof. This is
an audit of that precise November 2004 formulation, not a claim that every
version of Uzawa's theorem is false.

## Schlicht 2006: the shortcut and its omitted case

Schlicht eliminates the inverse-function and elasticity route. From exponential
paths and accumulation he obtains

\[
(g_K+\delta)K_0
=Y_0e^{(g_Y-g_K)t}-C_0e^{(g_C-g_K)t}.
\]

Differentiation restricts the rates. He then sets G to the original technology
at time zero and uses homogeneity. No saving rule or factor-share restriction
is required. However, his exclusion of \(Y_0=C_0\) assumes it would force
\(K_0=0\). The displayed equation also permits \(g_K=-\delta\) with
positive capital and zero investment. The 2008 paper explicitly identifies
and repairs this omission. See Schlicht's numbered p. 2 and Jones-Scrimgeour
p. 181. Thus the completed proof uses Schlicht's idea **with the correction**.

## 2008: positive investment and the original technology

The published theorem assumes exponential paths for Y, C, I, K, L and
strictly positive investment after a reference date tau. It drops the earlier
constant-share and strictly-positive-g requirements. Its neoclassical
definition does not list Inada conditions. It concludes

\[
Y(t)=F(K(t),A(t)L(t),\tau),\qquad
A(t)=e^{(g_Y-n)(t-\tau)}.
\]

The authors use the resource equation and accumulation to establish
\(g_Y=g_I=g_K\); homogeneity then gives the representation. G is now
specifically F frozen at tau, so its neoclassical properties are inherited
directly. The paper credits Schlicht and explains the positive-investment
correction. [Published theorem and discussion, p. 181](https://web.stanford.edu/~chadj/JonesScrimgeour2008.pdf).

### Our checked reconstruction of the rate argument

The following algebra describes our implementation, which uses three dates
instead of the paper's second differentiation. It also handles zero consumption
without assigning economic meaning to a growth rate of an identically zero series.

Let Y, C, I be initial levels and put
\(a=e^{g_Y}, b=e^{g_C}, d=e^{g_I}\). Resource feasibility at tau,
tau+1, tau+2 gives

\[
Y=C+I,\quad Ya=Cb+Id,\quad Ya^2=Cb^2+Id^2.
\]

Subtract twice a times the middle equality and add a-squared times the first:

\[
C(b-a)^2+I(d-a)^2=0.
\]

With C nonnegative and I positive, both summands are nonnegative and
\(d=a\), hence \(g_I=g_Y\). If C is positive, also \(g_C=g_Y\);
if C is zero, its chosen exponential rate is immaterial.

The derivative of the capital path and accumulation imply
\(I(t)=(g_K+\delta)K(t)\). Comparing tau and tau+1, then cancelling
positive initial investment, gives \(e^{g_I}=e^{g_K}\). Therefore
\(g_Y=g_I=g_K\); the equality is derived, not built into the definition.

Now set \(s=e^{g_Y(t-\tau)}\). The capital path satisfies
\(K(t)=sK(\tau)\). Our A makes \(A(t)L(t)=sL(\tau)\).
Constant returns therefore supplies

\[
F(K(t),A(t)L(t),\tau)
=sF(K(\tau),L(\tau),\tau)
=sY(\tau)=Y(t).
\]

Lean also checks A is positive, A(tau)=1, its derivative divided by its
level is \(g_Y-n\), and output per worker has that exponential rate.
Only constant returns at tau is needed for the representation identity;
curvature and sign restrictions on n, delta, and g are not used in this code.

## Comparison for the project

| Question | Supplied Jones-Scrimgeour 2004 | Schlicht 2006 | Jones-Scrimgeour 2008 / our completed proof |
| --- | --- | --- | --- |
| Main method | Inverse coordinate, elasticity, integration | Exponential accounting and homogeneity | Corrected accounting and homogeneity |
| Constant factor shares | Explicit assumption | Not needed | Not needed |
| Strictly positive per-worker growth | Explicit assumption | Not needed by the scaling identity | Not required |
| Positive investment | Not explicitly imposed | Omitted in the critical rate step | Explicit and used |
| Production function in conclusion | A constructed neoclassical G | F at time zero | F at the reference date tau |
| Main audit issue | Coordinate domains, curve-to-interval inference, zero investment, properties of G | Zero-investment branch | State the path scope and positivity conditions exactly |
| Existing Lean status | Three local calculus lemmas | Core idea used with correction | Full on-path representation plus witnesses |

These are not three independent completed machine proofs. They are two
Jones-Scrimgeour source versions and a key intervening paper. Our subsequent
development adds a repaired elasticity theorem to the completed published
representation theorem; their assumptions differ explicitly.

## The repaired second formalization

The completed elasticity-based proof states its target and changes to the
source explicitly. The strengthened version uses:

1. Positive investment and nonnegative consumption on exponential paths,
   so the accounting argument establishes constant K/Y.
2. A common connected capital/output domain with justified differentiable
   inverse maps; require \(\alpha(x,t)=\bar\alpha(x)\) throughout that
   domain, not just at the observed x(t).
3. Differentiability sufficient to compare elasticities and show the derivative
   of \(\phi(x,t)/\phi(x,\tau)\) is zero. The mean value theorem proves
   this quotient is constant in x on the positive half-line.

The third step yields \(\phi(x,t)=A(t)\phi(x,\tau)\), after normalization.
The coordinate identities then yield
\(f(k,t)=A(t)f(k/A(t),\tau)\) on the mapped domain. With global domain/range
conditions this reuses the reference-date F, preserving its properties, while
constant x on the observed path identifies A's growth rate.

This is a **strengthened domain-wide theorem**, not a literal encoding of
the 2004 assumptions. Inverse existence, continuity, and differentiability
are now proved from the explicit global range hypothesis and the positive
ratio derivative. See the new [proof map](uzawa-elasticity-repaired.md).
A simpler repaired on-path 2004-style conclusion
follows immediately from the completed 2008 theorem after adding positive
investment; that corollary would not constitute a second independent proof.

## Verification record

The subsequent combined development adds 38 theorems, for **63 Uzawa
declarations**, and seven new native TheoryDebugger theorems. Its fresh-source
audit and full build are recorded in the
[combined contribution package](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/contributions/lean-economics-uzawa-elasticity/README.md).
The counts below describe the earlier verification checkpoint.

Fresh verification on 20 September 2026 recompiled the contribution sources,
ran full LeanEconomics builds, checked source hashes against the saved patches,
and audited dependencies of all **41 declarations**: 16 Solow and 25 Uzawa.
Both TheoryDebugger scripts passed, including all **13 example theorems**,
counterexamples, accepted feasible repairs, and rejected inconsistent repairs.
This confirms the encoded claims, not every informal step in the papers.

The three additional version-audit lemmas also compile with only
`propext`, `Classical.choice`, and `Quot.sound`; no `sorryAx` remains.
They are separate research checks and do not change the 25-declaration
contribution patch or turn the 2004 proof into a completed theorem.

Local evidence lives in `project-context/reverification/20260920T104434Z`
and `project-context/uzawa-jones/version-audit-verification.json`.
The [existing case study](uzawa-jones.md) maps the published theorem to code.
