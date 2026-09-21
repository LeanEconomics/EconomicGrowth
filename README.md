# Economic Growth in Lean

Checked growth theory, starting with Solow–Swan dynamics and two modern proofs
of Uzawa representation results. Each folder is an independent Lean/Mathlib
project with a precise statement, sources, examples, and reproducible proof checks.

| Project | Checked results | Start here |
| --- | --- | --- |
| [SolowSwan](SolowSwan/README.md) | 59 theorems: Cobb–Douglas existence, positivity, uniqueness, monotone adjustment, convergence, comparative statics, and normalization | [Detailed statement and proof](SolowSwan/docs/solow-swan-dynamics.md) |
| [Uzawa](Uzawa/README.md) | 63 main theorems plus 3 obstruction lemmas: the published Jones–Scrimgeour/Schlicht route and a repaired elasticity route | [Comparison of the source versions](Uzawa/docs/uzawa-versions-comparison.md) |

## Scope

Solow–Swan here means the Cobb–Douglas equation $k'=bk^alpha-mk$, with
$b,m,k_0>0$ and $0<alpha<1$. The library constructs the solution and proves
uniqueness among nonnegative differentiable future paths with positive initial
capital. It does not claim convergence for every neoclassical production function
or uniqueness for zero initial capital.

The published Uzawa route proves a labour-augmenting representation along an
exponential balanced-growth path with positive investment. The repaired elasticity
route has explicit global range and domain-wide share assumptions. Its stronger
conclusion must not be confused with the on-path theorem. The literal November
2004 statement and the complete original Uzawa (1961) paper are not claimed as
formalized; [the original-paper extension is documented](Uzawa/docs/uzawa-1961-source.md).

## Build and verify

Install [elan](https://github.com/leanprover/elan) and Python 3.12+. Each project
pins Lean and Mathlib to `v4.34.0-rc2`; its own Lake manifest pins transitive
dependencies. From the repository root:

```sh
cd SolowSwan
lake exe cache get
python scripts/verify.py
```

For Uzawa, start from the repository root and run:

```sh
cd Uzawa
lake exe cache get
python scripts/verify.py
```

The verifier builds the complete project, freshly recompiles every contributed
proof without importing its compiled project module, and audits each named
theorem's transitive axioms. Only `propext`, `Classical.choice`, and `Quot.sound`
are allowed. Warnings, failed proofs, or placeholder axioms fail the check.
GitHub Actions runs both projects independently on pushes and pull requests.
The generated `verification/verification.json` records source hashes and axiom
lists. Proof checking happens in Lean's kernel; the JSON is a record of a run.

## Development and provenance

These contributions were developed primarily with **OpenAI Codex**, under the
direction of [@mvazcar](https://github.com/mvazcar), who chooses the research
questions and reviews the economic interpretation. Development and review used
**Astra 6** with **Ultra** and **Extra High** reasoning settings. This follows
[LeanEconomics' transparent attribution practice](https://github.com/LeanEconomics/LeanEconomics#provenance).
LeanEconomics credits Claude for its own development; these new contributions
carry their separate Codex attribution. Lean checks the formal statements;
economic faithfulness still requires researcher review.

[TheoryDebugger](https://github.com/mvazcar/TheoryDebugger) helped diagnose
assumptions, algebraic steps, and boundary cases. Neither TheoryDebugger nor
its external solver is a runtime dependency or trusted proof oracle here.
The proof projects require Lean and Mathlib. Original import revisions and
file hashes are recorded in [IMPORT-PROVENANCE.json](IMPORT-PROVENANCE.json).

## Licensing

The pre-existing repository [LICENSE](LICENSE) is Apache 2.0 and is retained.
The contributed `SolowSwan/` and `Uzawa/` projects are additionally available
under **The Unlicense**, as stated in each project's license files. The original
README, import manifest, ignore rules, and verification workflow added with
these contributions are also dedicated under [The Unlicense](UNLICENSE).
This dedication does not relicense pre-existing or third-party material.

Lean, Mathlib, transitive dependencies, and cited research papers retain their
own terms. See [SolowSwan notices](SolowSwan/THIRD_PARTY_NOTICES.md) and
[Uzawa notices](Uzawa/THIRD_PARTY_NOTICES.md). Papers and dependency binaries
are not bundled. No payment or permission request is needed to reuse our
original contributions under The Unlicense.
