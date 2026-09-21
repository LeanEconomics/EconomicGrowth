# Uzawa's theorem: the Jones–Scrimgeour versions

> Research note from TheoryDebugger. Links to diagnostic examples and archived
> contribution checks point to that repository. The standalone modules here have
> their own build and fresh axiom audit: run `python scripts/verify.py` from this
> repository root and consult `verification/verification.json`. Our original
> material in this standalone distribution uses The Unlicense.

This case study starts with the supplied November 2004 NBER working paper
10921, *The Steady-State Growth Theorem: A Comment on Uzawa (1961)*, by
Charles I. Jones and Dean Scrimgeour. The attachment is preserved in the local
research archive. Its proof and the subsequent published proof are distinct.

The authors' [2008 published paper](https://web.stanford.edu/~chadj/JonesScrimgeour2008.pdf),
*A New Proof of Uzawa's Steady-State Growth Theorem*, Review of Economics and
Statistics 90(1), 180–182, replaces the earlier argument with a proof credited
to Schlicht (2006). The published statement explicitly requires positive
investment and represents output using the original technology at the starting
date. Our full formal result follows this published statement. Three additional
lemmas check the local elasticity calculation from the attached 2004 version.

The [detailed version comparison](uzawa-versions-comparison.md) reconstructs
both arguments, identifies Schlicht's original omission, and analyzes a
zero-investment counterexample admitted by the supplied 2004 assumptions.
It distinguishes repairs to the statement from unfinished proof code.

The subsequent [repaired elasticity development](uzawa-elasticity-repaired.md)
now constructs the inverse and completes a strengthened separation theorem.
It uses explicit global range and domain-wide share assumptions. The original
25-declaration package below is preserved; the combined package adds 38
theorems. The literal November 2004 statement remains distinct from this repair.

## Economic statement and assumptions

Let the five quantities `Y, C, I, K, L` follow constant exponential paths after
date `τ`, with initially positive capital, labor, and investment and nonnegative
consumption. Assume the resource identity `Y=C+I`, accumulation `K'=I-δK`, and
production `Y=F(K,L,t)`. Let `F(·,·,τ)` have constant returns on positive inputs.
The Lean theorem derives `gY=gI=gK`; equality of these rates is not an assumption.

Define `A(t)=exp((gY-n)(t-τ))`. The proved conclusion is

```
Y(t) = F(K(t), A(t) L(t), τ),    A'(t)/A(t) = gY - n.
```

An accompanying identity verifies that output per worker itself follows an
exponential path with rate `gY-n`. Thus the technology rate equals the growth
rate of output per worker. Also `A(t)>0` and `A(τ)=1`.

This is an identity **along the specified balanced path**. It does not assert
that `F(K,L,t)=F(K,A(t)L,τ)` for every counterfactual input pair. It establishes
the stated representation, not a unique underlying mechanism of innovation.

Only constant returns is needed of the production function for this identity.
The usual neoclassical marginal-product and curvature assumptions may be added,
but are not used by this proof. Likewise, nonnegative labor growth and
depreciation and strictly positive output-per-worker growth are unnecessary for
the representation identity. This is a statement of the checked hypotheses,
not a claim of a new economic theorem. The same frozen production function is
used, so its other properties need not be inferred from equality along a path.

## What Lean proves

The [separate contribution package](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/contributions/lean-economics-uzawa/README.md)
contains three Mathlib-only modules, with 25 proved declarations in total.

| Module and main declarations | Checked content |
| --- | --- |
| `Growth/Uzawa.lean`: `outputGrowth_eq_investmentGrowth` | The resource constraint makes the two growth rates equal when investment is positive and consumption nonnegative |
| `investmentGrowth_eq_capitalGrowth` | Actual derivatives of exponential capital paths and the accumulation equation identify the investment and capital rates |
| `BalancedGrowthData.labor_augmenting_representation` | Scaling the production function at `τ` gives the published on-path conclusion |
| `technology_growthRate`, `output_per_worker` | The index and output per worker have the required exponential rate |
| `Growth/UzawaElasticity.lean` | Three local calculus results from the 2004 proof |
| `Growth/UzawaExamples.lean` | A concrete Cobb–Douglas economy satisfies all premises of the general representation theorem |

The published argument differentiates the resource identity twice. Our
implementation instead evaluates its explicit exponential paths at `τ`,
`τ+1`, and `τ+2`. Writing `a=exp(gY)`, `b=exp(gC)`, and `d=exp(gI)`, these give

```
Y = C+I,   Y a = C b + I d,   Y a² = C b² + I d².
```

Their weighted-square identity is `C(b-a)²+I(d-a)²=0`. Nonnegative `C` and
strictly positive `I` imply `d=a`; injectivity of the exponential gives `gI=gY`.
This proof also handles identically zero consumption. It avoids introducing
unjustified differentiability assumptions or dividing by a zero consumption
level. The subsequent accumulation and constant-returns steps follow the
published construction.

The positive example uses `K=exp(2t)`, `L=1`, `Y=4exp(2t)`,
`C=I=2exp(2t)`, `δ=0`, and `F(K,L,t)=4exp(t)sqrt(KL)`. Lean checks all five
levels are positive, all required equations and constant returns, then applies
the general theorem. The assumptions are therefore jointly realizable.

## What TheoryDebugger checks

[The runnable example](https://github.com/mvazcar/TheoryDebugger/blob/codex/initial-version/examples/UzawaJones.lean) isolates the cancellation
step `I(gI-gK)=0`. Its `accumulation_rate_bridge` derives that scalar equation
from an actual differentiable functional accumulation identity.

With only `I≥0`, TheoryDebugger finds a counterexample with `I=0` and unequal
rates, and also a satisfying assignment. The classification is **mixed**.
Adding `I>0` explicitly repairs the claim and has a Lean-checked feasible
assignment. Adding `I<0` instead contradicts the existing assumption and is
rejected as an inconsistent repair. The original variables, hypotheses, and
conclusion are retained in the repair record.

A second check connects the boundary case to economic functions. Set
`K=L=1`, `δ=I=0`, `Y=C=exp(t)`, and `F(K,L,t)=exp(t)sqrt(KL)`. Lean verifies
the resource equation, accumulation, production on the path, and constant
returns. At `t=2`, the proposed index `A=exp(t)` would require
`exp(2)=sqrt(exp(2))`, which Lean refutes. This illustrates the zero-investment
exception discussed in the published paper. The complete set of neoclassical
curvature/Inada conditions is not separately formalized for this example.

Run `python scripts/verify_uzawa.py` in TheoryDebugger's environment. It checks
the three diagnostic reports, the explicit repair decisions, the feasibility
evidence, and the axiom dependencies of all seven example theorems. The saved
record and compiler output are in `demo/uzawa/`. They identify the tested
source by hash; recompile the Lean source to reproduce the proof checks.

## What remains of the attached 2004 argument

Printed pp. 5–6 introduce `h(k)=k/f(k)`, with share `α=f'(k)k/f(k)`.
We prove its derivative is `(1-α)/f(k)`, positive when output is positive and
`α<1`. Given a differentiable local inverse parameterization satisfying
`k(x)=x f(k(x))` in a neighborhood, Lean derives the output elasticity
`α/(1-α)`. The neighborhood identity is essential for legitimate differentiation;
equality at a single point is insufficient.

The original three-lemma module does **not** prove inverse existence or the
later separation step. The separate repaired development now proves those
steps under additional explicit hypotheses; it is not the literal 2004 proof.
In particular, a
literal formalization of its separation step must specify the domain on which
share invariance holds. Constancy along one observed path must not silently be
strengthened to constancy over counterfactual input values. The completed 2008
proof does not depend on this unresolved part of the earlier proof map.

This distinction is part of the learning workflow: inspect the exact source
version, expose the hypotheses, obtain diagnostics, and check the final formal
claim without overstating which informal proof has been verified.
