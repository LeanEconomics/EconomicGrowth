# The repaired elasticity proof: assumptions, construction, and checks

> Research note from TheoryDebugger. Links to diagnostic examples and archived
> contribution checks point to that repository. The standalone modules here have
> their own build and fresh axiom audit: run `python scripts/verify.py` from this
> repository root and consult `verification/verification.json`. Our original
> material in this standalone distribution uses The Unlicense.

We now have two completed formal representation arguments: the published
Schlicht/Jones-Scrimgeour on-path proof, and the strengthened coordinate-based
argument documented here. They have different hypotheses. This second result
does **not** claim to verify the literal November 2004 theorem, whose
zero-investment boundary and domain issues are explained in the
[source comparison](uzawa-versions-comparison.md).

The [combined contribution package](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/contributions/lean-economics-uzawa-elasticity/README.md)
contains both arguments and their examples. The new source modules are
`LeanEconomics/Growth/UzawaSeparation.lean` and `UzawaSeparationExamples.lean`.
They add 38 theorems to the previous 25, giving 63 Uzawa declarations.

## Exact assumptions of the new technology theorem

The structure `Technology` contains an intensive production function f(t,k)
and its certified derivative m(t,k). For every real date t and positive k:

1. f(t,k)>0, and f(t,.) has derivative m(t,k).
2. The capital share alpha=m(t,k)k/f(t,k) is less than 1. Thus the ratio map
   h(t,k)=k/f(t,k) has strictly positive derivative.
3. For every x>0 there exists k>0 with h(t,k)=x. This is an **explicit global
   range assumption**, not a conclusion inferred from a nonzero derivative.

The theorem additionally assumes `SharesInvariant T reference`: for every
real t and every x>0, the capital shares evaluated at the inverse ratio
coordinates agree with those at the reference date. The quantifier is across
the whole positive x-domain, not only at the x-values an economy happens
to visit. The implementation states the technology assumptions for all real
dates; economic path and accounting assumptions below apply only from the
starting date onward.

The identity does not need a positive marginal product, concavity, or Inada
limits. Those can be imposed as additional economic restrictions on f or F.
The explicit range assumption has not been derived from a full formal
neoclassical/Inada structure. No savings rule or household optimization is
assumed. None of these omitted conditions is silently claimed to be checked.

## What Lean constructs and proves

Write kappa(t,x) for the inverse ratio coordinate, and
phi(t,x)=f(t,kappa(t,x)). The proof has the following dependency chain.

| Stage | Formal result | Why it matters |
| --- | --- | --- |
| Ratio derivative | `hasDerivAt_ratio`, `ratio_derivative_pos` | Checks h'=(1-alpha)/f>0 |
| Injectivity | `ratio_strictMonoOn` | Uses the mean value theorem on the connected positive half-line |
| Inverse construction | `capital`, `ratio_capital`, `capital_ratio` | Chooses positive preimages using the range hypothesis and proves both inverse laws |
| Inverse regularity | `capital_image`, `continuousAt_capital`, `hasDerivAt_capital` | Proves continuity, then differentiability using Mathlib's inverse derivative theorem |
| Elasticity | `elasticity` | Derives x phi_x/phi=alpha/(1-alpha), using the constructed inverse |
| Separation | `hasDerivAt_phi_ratio_zero`, `separation` | Proves phi(t,x)/phi(reference,x) has zero derivative and is constant in x |
| Reconstruction | `intensive_representation`, `production_representation` | Gives the labor-augmenting form for all positive inputs |
| Original technology | `production_eq_original`, `original_production_representation` | Identifies the reconstructed function with the original CRS F |

The technology factor is defined from the production functions themselves:

\[
A(t)=\frac{\phi(t,1)}{\phi(\tau,1)}>0,\qquad A(\tau)=1.
\]

Equal shares imply equal elasticities. Since x>0, this yields

\[
\phi_x(t,x)\phi(\tau,x)=\phi(t,x)\phi_x(\tau,x).
\]

The quotient rule therefore gives

\[
\frac{d}{dx}\left(\frac{\phi(t,x)}{\phi(\tau,x)}\right)=0.
\]

The mean value theorem on (0,infinity) now proves
phi(t,x)=A(t)phi(tau,x). This is the rigorous replacement for the informal
integration step. Positivity permits every division, and connectedness is
explicit; the desired separation is proved, not included in the assumptions.

Using kappa(t,x)=x phi(t,x), Lean reconstructs

\[
f(t,k)=A(t)f(\tau,k/A(t)).
\]

Define the CRS technology P(t,K,L)=L f(t,K/L). For all K,L>0,

\[
P(t,K,L)=P(\tau,K,A(t)L).
\]

For an original CRS production function F with f(t,k)=F(k,1,t), the
`production_eq_original` bridge proves P(t,K,L)=F(K,L,t). Consequently the
reference function is literally the original F at tau. Additional curvature
or other properties of that reference function are preserved by identity;
we do not infer them from agreement along a single path.

## Adding the balanced-growth conclusion

The technology theorem alone does not determine A's time growth. The
economic theorem additionally uses the existing `BalancedGrowthData`:
explicit exponential Y,C,I,K,L paths; positive initial K,L,I; nonnegative
initial C; production; resource feasibility Y=C+I; and accumulation
K'=I-delta K, from tau onward.

`technology_eq_balanced_growth` uses the checked accounting result
gY=gI=gK to establish constant K/Y. Evaluating the separated phi functions
at that common positive ratio then identifies their scale factor:

\[
A(t)=\frac{Y(t)/L(t)}{Y(\tau)/L(\tau)}
=e^{(g_Y-n)(t-\tau)}.
\]

`repaired_labor_augmenting_representation` applies the separation proof and
this calibration to obtain the desired on-path representation.
`hasDerivWithinAt_technology_of_balanced_growth` checks the resulting
derivative on [tau,infinity), including the appropriate one-sided boundary
at tau. This does not assume a two-sided continuation of the economic path
before its starting date.

The new proof **shares the accounting lemma** `outputGrowth_eq_capitalGrowth`
with the 2008 proof. It does not call that proof's
`BalancedGrowthData.labor_augmenting_representation`. Thus there are two
representation arguments with a common checked accounting foundation,
rather than two completely disjoint formal developments.

## A checked, nonempty class of examples

For any positive multiplier b(t), `sqrtTechnology` uses
f(t,k)=b(t)sqrt(k). Lean checks every `Technology` field, including the
global range: x>0 has positive preimage k=(b(t)x)^2. It derives

\[
\alpha=1/2,\qquad
\kappa(t,x)=(b(t)x)^2,\qquad
\phi(t,x)=b(t)^2x,\qquad
A(t)=b(t)^2/b(\tau)^2.
\]

The example takes b(t)=4 exp(t), tau=0, K=exp(2t), L=1,
Y=4 exp(2t), C=I=2 exp(2t), and delta=0. Existing checked resource and
accumulation results are reused; the new module verifies production and the
global share condition, applies the repaired theorem, and checks A=exp(2t).
Both proof routes therefore apply to the same strictly positive economy.

## TheoryDebugger diagnostics and their limits

Run `python scripts/verify_uzawa_separation.py` in TheoryDebugger's environment.
The script recompiles the native example and checks four reports:

- With x>=0, x*u=x*v does not imply u=v: the tool finds x=0,u=1,v=0.
- Explicitly adding x>0 repairs cancellation and has a feasible assignment.
- Adding x<0 is inconsistent with the original assumptions and is rejected.
- The family phi(t,x)=1+x+t(x-1)^2 does not preserve the ratio of values at
  x=2 and x=1: the tool returns t=1/2 as a counterexample and t=0 as a
  satisfying case in [0,1].

Seven native Lean theorems connect the diagnostics to mathematics. They
include an actual quotient-derivative bridge; phi(t,1)=2;
phi_x(t,1)=1; constant elasticity 1/2 at that anchor; positivity of phi for
t>=0,x>0; and a proof that **no functions A and psi** can separate this family
on t in [0,1],x>0. This polynomial example isolates the quantifier issue.
It is not presented as a complete counterexample to a neoclassical growth
model with all of the repaired assumptions.

TheoryDebugger's solver handles these algebraic diagnostics. Ordinary
Mathlib/Lean proofs establish global inverse regularity, separation, and
the economic representation. Both paths terminate in kernel-checked proofs;
the solver itself is not added to the trusted axioms.

## Verification and comparison

The combined audit freshly elaborates all five Uzawa modules in one source
file without importing their existing compiled artifacts, checks all 63
theorem axiom dependencies, and runs the complete LeanEconomics build.
The new modules have no warnings. Only the usual `propext`,
`Classical.choice`, and `Quot.sound` are permitted; `sorryAx` is rejected.
The source hashes, build results, and reproducible axiom audit are packaged
with the contribution. Native diagnostics have their own report under
`demo/uzawa-separation/` and are included in TheoryDebugger's CI workflow.

| Scope | Published 2008 proof | Repaired elasticity proof |
| --- | --- | --- |
| Technology condition | CRS at reference date | Differentiable positive intensive output; share<1; explicit global ratio range; domain-wide share invariance |
| Technology-only conclusion | Not asserted globally by our 2008 theorem | Representation for all positive K,L |
| Balanced-growth accounting | Exponential paths, C>=0, I>0 | Same checked accounting foundation |
| On-path conclusion | Original reference-date F with exponential labor index | Same conclusion, with the index derived from separated technologies |
| Actual proof route | Exponential scaling | Constructed inverse, elasticity, zero quotient derivative, reconstruction |
| Literal November 2004 statement | Different published formulation | Explicitly repaired and strengthened formulation |

The extra assumptions are useful for studying the 2004 method, but are
unnecessary if the only goal is the published on-path representation.
