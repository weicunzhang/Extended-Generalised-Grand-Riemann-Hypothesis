# On the Extended, Generalized, and Grand Riemann Hypotheses: A Unified Approach via the Divisibility Property of Entire Functions

**Author:** Weicun Zhang

This repository provides a place to access and discuss the author's manuscript proposing a unified approach to the Extended Riemann Hypothesis (ERH), the Generalized Riemann Hypothesis (GRH), and the Grand Riemann Hypothesis.

## Manuscript

- **Latest preprint record:** [Preprints.org — manuscript 202506.0481](https://www.preprints.org/manuscript/202506.0481)
- **Current listed version:** Version 23
- **Posted:** 19 November 2026
- **Version-specific DOI:** [10.20944/preprints202506.0481.v23](https://doi.org/10.20944/preprints202506.0481.v23)
- **PDF currently stored in this repository:** [ERH-GRH-GRAND-NEW Version PDF](./ERH-GRH-GRAND-NEW%20Version.pdf)

The PDF in this GitHub repository is identified by its filename above. Please consult the Preprints.org record for the latest version and the canonical version-specific citation.

## Overview of the manuscript

The manuscript proposes a unified framework based on general properties of \(L\)-functions and the divisibility property of entire functions. Its stated line of argument includes:

1. Pairing complex-conjugate zeros in Hadamard products of completed \(L\)-functions. The manuscript distinguishes the self-dual case from the non-self-dual case, using the corresponding completed function or product of completed functions.
2. Using the Euler-product property and the location of zeros in the critical strip to obtain absolutely and locally uniformly convergent infinite products with irreducible real quadratic factors.
3. Substituting these products into the symmetric functional equation to derive divisibility relations.
4. Combining those relations with the uniqueness of zero multiplicities to argue that the relevant zeros lie on the critical line.

The manuscript applies this framework to Dirichlet \(L\)-functions (GRH), Dedekind zeta functions (ERH), and cuspidal automorphic \(L\)-functions and broader classes of \(L\)-functions (Grand RH). It also claims that Landau–Siegel zeros are excluded. The author states that the Davenport–Heilbronn counterexample is outside the scope of the proposed method because it does not possess an Euler product.

These points summarize the manuscript's stated approach and claims; they are not an independent verification of its arguments or conclusions.

## Citation

Weicun Zhang (2026). *On the Extended, Generalized, and Grand Riemann Hypotheses: A Unified Approach via the Divisibility Property of Entire Functions*. Preprints.org, Version 23. https://doi.org/10.20944/preprints202506.0481.v23


## Lean 4 formalization

**Lemma 1, Lemma 2, and Theorem 1 have been formalized and successfully verified using Lean 4 and Mathlib.** The project build and axiom audit passed in [GitHub Actions Run #48 on the `main` branch](https://github.com/weicunzhang/Extended-Generalised-Grand-Riemann-Hypothesis/actions/runs/45119141696).

The formalized results are:

- **Lemma 1:** An irreducible polynomial over `ℝ` that divides a finite product divides at least one of its factors.
- **Lemma 2:** Under the formalized entire-quotient, pointwise product-representation, and absolute-convergence hypotheses, divisibility by an irreducible polynomial implies that it divides at least one factor of the infinite product.
- **Theorem 1:** Under the formalized symmetry, product-representation, absolute-convergence, and zero-quadruple-uniqueness hypotheses, every quadratic factor has center `k/2`; the absolute zero heights are pairwise distinct; and, under the stated weighted summability condition, they admit a strictly increasing bijective reindexing.

The Lean source files are available in the [Lean project](./Lean/README.md): [Lemma 1](./Lean/RiemannHypothesisLean/Lemma1.lean), [Lemma 2](./Lean/RiemannHypothesisLean/Lemma2.lean), and [Theorem 1](./Lean/RiemannHypothesisLean/Theorem1.lean). The [Lean README](./Lean/README.md) describes the formal statements, hypotheses, and proof scope in more detail.

These machine-checked results verify the formalized statements under their explicitly encoded hypotheses. They do not, by themselves, establish the manuscript's broader applications or prove ERH, GRH, the Grand Riemann Hypothesis, or the exclusion of Landau–Siegel zeros.
