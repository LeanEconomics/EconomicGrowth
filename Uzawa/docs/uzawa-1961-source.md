# Uzawa (1961): original source and next formalization

> Research note from TheoryDebugger. Links to diagnostic examples and archived
> contribution checks point to that repository. The standalone modules here have
> their own build and fresh axiom audit: run `python scripts/verify.py` from this
> repository root and consult `verification/verification.json`. Our original
> material in this standalone distribution uses The Unlicense.

Hirofumi Uzawa, **Neutral Inventions and the Stability of Growth Equilibrium**,
*The Review of Economic Studies* 28(2), February 1961, pp. 117–124.
DOI: [10.2307/2295709](https://doi.org/10.2307/2295709).

## What has been verified

The [journal record](https://academic.oup.com/restud/article-abstract/28/2/117/1556013)
confirms the citation. The [publisher's introduction to Uzawa's collected-paper reprint](https://www.cambridge.org/core/books/abs/preference-production-and-capital/neutral-inventions-and-the-stability-of-growth-equilibrium/ADB27D2441D9AD8D49F94E17E888D01F)
describes two parts: a characterization of Harrod-neutral inventions in terms of
labour efficiency, followed by growth-equilibrium stability under a neoclassical
technology without imposing the Cobb–Douglas form.

The complete 1961 text has **not yet been obtained or inspected**. The journal
PDF endpoint did not supply the paper and the JSTOR record did not expose its
full text. Consequently this note assigns no theorem numbers, exact hypotheses,
or page-specific proof steps to the original article. No original-paper theorem
is claimed to be formally checked here.

## Recommended structure

Keep the published Jones–Scrimgeour/Schlicht route as the reader's first proof.
It separates growth accounting from the homogeneity argument and makes the
positive-investment condition visible. Keep the repaired elasticity proof as
a second route with its stronger, explicitly quantified assumptions.

Add the original-paper development separately after obtaining the full source:

1. Transcribe each exact definition and theorem, with its page and assumptions.
2. Separate the characterization of Harrod neutrality from the equilibrium
   stability result. Neither is automatically identical to the modern on-path
   representation theorem.
3. Map original hypotheses to modern ones; mark implications proved, assumptions
   strengthened, and missing equivalences. Diagnose scalar implications and
   boundary cases with TheoryDebugger before writing their Lean proofs.
4. Formalize actual derivatives, domains, monotonicity, and limiting arguments
   in Lean. Reuse the existing calculus where the mathematical statements match.
5. Compare the original route and both modern routes in a theorem-level table.

This is a documented research extension, not a completed formalization or a
reason to label the current library a complete encoding of the 1961 paper.
The current name `uzawa-modern-lean` accurately describes the checked scope;
an original-source module can be added without renaming the repository.
