# Acemoglu source map

Primary source: Daron Acemoglu, *Introduction to Modern Economic Growth*,
Princeton University Press, 2009, Chapter 2, “The Solow Growth Model.”
The publisher provides the [chapter PDF](https://assets.press.princeton.edu/chapters/s2_8764.pdf).
The cited pages below are printed page numbers. The downloaded publisher file
repeats the opening portion of the chapter; the complete sequence later in the
file contains all the cited results. Bibliographic year 2009 and the PDF's 2008
copyright notice refer to the same book, not two different theorem versions.

Supporting source: Acemoglu, MIT 14.452, Fall 2016,
[Lectures 2 and 3: The Solow Growth Model](https://ocw.mit.edu/courses/14-452-economic-growth-fall-2016/2b68057aa4e74410d00ae89a0c49752f_MIT14_452F16_Lec2and3.pdf).
The book is the source for proposition numbering. The lectures were downloaded
as supporting material; they do not replace the book's assumptions.

| Source location | Formal result | Scope and correspondence |
| --- | --- | --- |
| Assumptions 1–2, pp. 29, 33–34 | `Technology`, `technology_of_second_derivative` | Intensive-form production; the primitive negative second derivative implies the strict concavity used in the proofs. No differentiability at zero. |
| Equation (2.33), p. 49 | `rate`, `general_solow` | `k'=s f(k)-m k`, with `m=δ+n>0`. |
| Proposition 2.7, p. 50 | `existsUnique_steadyState`, `steadyCapital_spec` | Exactly one positive stationary stock; the zero stock is also stationary. |
| Proposition 2.8, p. 50 | `acemoglu_capital_partials`, `acemoglu_output_partials` | All eight partial-derivative signs; the inverse function theorem proves differentiability of the constructed stationary stock. |
| Proposition 2.9, p. 52 | `general_solow`, `every_path_converges`, `path_stable` | Constructive existence, uniqueness, strict monotone convergence, and quantitative stability for positive initial capital. |
| Proposition 2.4 and equation (2.23), pp. 41–42 | `exists_unique_golden_saving`, `golden_rule_maximizes` | The stationary-consumption maximization argument is extended to general effective dilution `m`, replacing the no-population-growth source's `δ`. |
| Section 2.7.4, equations (2.50)–(2.52), pp. 64–66; Proposition 2.13, p. 67 | `effective_labour_convergence` | Actual aggregate derivatives imply the normalized equation with `m=δ+n+g`; every admissible effective-capital path converges. This does not claim every assertion about aggregate balanced-growth rates is formalized. |
| Section 2.8, pp. 67–68 | `saving_increase_transition` | Permanent saving increase from an old steady state; strict capital deepening and immediate consumption loss. |
| Our Cass stationary module and its source map | `cass_stationary_bridge` | Explicit added comparison, using `f'(kC)=d+m`; it is not attributed to Proposition 2.9 and does not equate transition paths. |

## Assumption and scope decisions

- Constant `s>0`, `m>0`, and `k₀>0` are required for the principal dynamics
  theorem. A consumption interpretation adds `s<1`.
- The positive stationary state is unique. Neither the source's informal
  “unique steady state” wording nor the code eliminates the zero stationary
  state when `f(0)=0`.
- Functions are continuous on nonnegative capital and continuously
  differentiable on positive capital. The source's stronger differentiability
  conditions imply the hypotheses used here.
- Aggregate constant returns are represented by the explicit intensive form
  `Y=E f(K/E)` in the normalization theorem. This contribution does not prove a
  general multivariate constant-returns representation theorem.
- The proof concerns classical continuous-time trajectories. Discrete-time
  propositions, empirical convergence regressions, stochastic growth, endogenous
  technology, and competitive decentralization of Cass are outside this PR.
- The stationary Cass bridge uses the same production and dilution units on
  both sides. Its `d` is the effective utility discount rate, not an unexplained
  substitution for an unnormalized household discount parameter.

## Source provenance

The two PDFs were inspected/downloaded on 2026-09-21 and remain outside the
public repository. They are references, not material released under our
Unlicense. Original proof terms and explanations are supplied here instead.

| Reference file | SHA-256 |
| --- | --- |
| Publisher Chapter 2 PDF | `0d35fe854feeaa8a52d20f5fce592277f6b1d23b96bebaa44c6ca6a492d4d095` |
| MIT Fall 2016 lectures 2–3 PDF | `fe348b6f73ae89b3b78192a286a6028f404b2932001dd33291be5b9aac61ca83` |

`GlobalFlow`, `CompactExtension`, and `AsymptoticODE` adapt selected helpers from
the project's original Cass development at EconomicGrowth commit
`b1e9dd2dfe5c7a6f69ac4713f419293d1d175d17`. The namespaces and imports are local
to `Solow1956`, and every adapted proof is re-elaborated in this project. The
Golden Rule supporting-line argument likewise reuses that original work.
There is no build dependency on the Cass branch or an external unpublished
proof library. These helpers share the original contribution's Unlicense.

TheoryDebugger revision `5c1fa57` generated the diagnostics. Exact Python-source
hashes, problem inputs, certificate source hashes, and tool versions are recorded
in `verification/theorydebugger/environment.json` and `results.json`.
