# Modern proofs of Uzawa's theorem in Lean

This is the `Uzawa/` proof project in
[LeanEconomics/EconomicGrowth](https://github.com/LeanEconomics/EconomicGrowth).
Run the commands below from this directory: `cd Uzawa` from the repository
root. [Return to the growth library index](../README.md).

Two checked representation arguments, with **63 main theorems and 3 additional
obstruction lemmas**, explicit assumptions, and a comparison of the modern
source versions. Start with the published Jones–Scrimgeour/Schlicht route.

The original reference is Hirofumi Uzawa (1961), *Neutral Inventions and the
Stability of Growth Equilibrium*, Review of Economic Studies 28(2), 117–124,
[DOI 10.2307/2295709](https://doi.org/10.2307/2295709). This repository currently
formalizes modern arguments, not all results or the original proof in that
article. See [the original-source status and extension plan](docs/uzawa-1961-source.md).

## What the two proofs establish

| Route | Assumptions that matter | Conclusion |
| --- | --- | --- |
| Published Jones–Scrimgeour (2008), using Schlicht's idea with its correction | Exponential paths for output, consumption, investment, capital and labour; resource and accumulation equations; positive investment, capital and labour; nonnegative consumption; constant returns at a reference date | Along that path, output equals the reference technology evaluated at capital and labour augmented at the output-per-worker growth rate |
| Repaired elasticity route | Positive differentiable intensive output, capital share below one, full positive range for the capital/output coordinate, and shares invariant across time at **every** positive capital/output coordinate | A domain-wide labour-augmenting representation; the same balanced-growth accounting then calibrates its technology factor on the path |

For the first route, if the reference date is $\tau$, then

$$Y(t)=F(K(t),A(t)L(t),\tau),\qquad A(t)=e^{(g_Y-n)(t-\tau)},\qquad t\geq\tau.$$

The first conclusion is an on-path representation, not a statement about every
counterfactual input combination. The second route has stronger global
assumptions. Both share the growth-accounting lemma; their representation
arguments are different. Neither requires an external solver as a proof oracle.

The literal November 2004 working-paper assumptions admit a zero-investment
boundary case. Three obstruction lemmas check why that case cannot have the
claimed representation with a constant-returns, strictly capital-increasing
technology and the specified exponential labour augmentation. A full formal
encoding of all derivative and Inada conditions of that countermodel is not
claimed. The repaired route is explicitly stronger than the 2004 statement.

## Read the arguments and sources

- [Published proof, exact hypotheses, and Lean correspondence](docs/uzawa-jones.md).
- [Detailed comparison of the 2004, 2006, and 2008 sources](docs/uzawa-versions-comparison.md).
- [Completed repaired elasticity argument](docs/uzawa-elasticity-repaired.md).
- Jones and Scrimgeour (2008), *A New Proof of Uzawa's Steady-State Growth Theorem*,
  REST 90(1), 180–182: [author PDF](https://web.stanford.edu/~chadj/JonesScrimgeour2008.pdf).
- Schlicht (2006), *A Variant of Uzawa's Theorem*, Economics Bulletin 5(6):
  [publisher PDF](https://www.accessecon.com/pubs/EB/2006/Volume5/EB-06E10001A.pdf).
- Jones and Scrimgeour (November 2004), NBER Working Paper 10921:
  [NBER record](https://www.nber.org/papers/w10921).

## Library map

| Module | Theorems | Contents |
| --- | ---: | --- |
| [Uzawa](UzawaModern/Growth/Uzawa.lean) | 16 | Growth accounting and published representation |
| [UzawaElasticity](UzawaModern/Growth/UzawaElasticity.lean) | 3 | Ratio derivative and elasticity identities |
| [UzawaExamples](UzawaModern/Growth/UzawaExamples.lean) | 6 | Positive economy satisfying the published theorem's hypotheses |
| [UzawaSeparation](UzawaModern/Growth/UzawaSeparation.lean) | 28 | Inverse coordinate, separation, global representation, calibration |
| [UzawaSeparationExamples](UzawaModern/Growth/UzawaSeparationExamples.lean) | 10 | Actual technology satisfying the repaired assumptions |
| [VersionAudit](UzawaModern/VersionAudit.lean) | 3 | Two-point obstruction for the 2004 boundary case |

Import `UzawaModern`. The two main statements are
`UzawaModern.Uzawa.BalancedGrowthData.labor_augmenting_representation` and
`UzawaModern.UzawaSeparation.Technology.repaired_labor_augmenting_representation`.

Related dynamics: [solow1956-lean](https://github.com/mvazcar/solow1956-lean).

## Reproduce the verification

Install [Lean through elan](https://github.com/leanprover/elan) and Python 3.12+,
then run from this project directory:

```sh
lake exe cache get
python scripts/verify.py
```

Lean and Mathlib are pinned to **v4.34.0-rc2**, with transitive revisions in
`lake-manifest.json`. The script builds the library, freshly recompiles the
proof sources without importing their compiled project modules, and checks
107 declarations, including all 66 theorems, definitions, structures, their
constructors, and field projections. It also checks that every library module
is listed and imported, and rejects unchecked constructs even when unused.
Only Lean's standard `propext`,
`Classical.choice`, and `Quot.sound` are allowed. Warnings, failed proofs, and
placeholder axioms fail verification. Mathlib's Apache-specific header style
rule is disabled because this independent distribution uses The Unlicense;
the mathematical and other style checks remain enabled.

The checked source hashes, theorem names, and axiom lists are recorded in
[verification/verification.json](verification/verification.json). GitHub Actions
repeats the build and fresh audit on pushes and pull requests. A JSON record is
evidence of a run; the Lean proof terms and kernel checks are the certificates.

## Development and credit

Developed primarily with **OpenAI Codex**, under the direction of
[@mvazcar](https://github.com/mvazcar), who chooses the research questions and reviews
the economic interpretation. Codex assists with source comparison, proof development,
implementation, documentation, and tests. This follows
[LeanEconomics' transparent attribution of AI assistance](https://github.com/LeanEconomics/LeanEconomics#provenance).
LeanEconomics
credits Claude for its own development; that credit is not a claim that Claude wrote
these new modules. Lean verifies the encoded statements; their economic interpretation
still requires researcher review.

Development and review used **Astra 6** with **Ultra** and **Extra High**
reasoning settings.

The modules were first developed as independent proposed LeanEconomics
contributions. [proof-manifest.json](proof-manifest.json) records the original
commits and source hashes. This standalone library changes the project namespace,
imports, and license header while preserving the mathematical proof bodies.

[TheoryDebugger](https://github.com/mvazcar/TheoryDebugger) helped diagnose
assumptions, boundary cases, and algebraic proof steps. Its external solver is
not a trusted oracle or a runtime dependency of this library. The complete
proofs here use Lean and Mathlib.

## License

Our original work is dedicated to the public domain under
[The Unlicense](UNLICENSE). Use, modify, derive from, and redistribute it freely,
including commercially, without payment or a permission request. External
dependencies and research papers retain their own terms; see
[third-party notices](THIRD_PARTY_NOTICES.md). Papers and dependency binaries
are not bundled. Earlier Apache 2.0 grants of our original contribution remain
available. Contributions follow [CONTRIBUTING.md](CONTRIBUTING.md).
