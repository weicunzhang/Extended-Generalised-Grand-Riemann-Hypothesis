# Lean 4 formalization of the preprint

This directory contains a Lean 4 project using Mathlib, intended to formalize selected statements from:

*Weicun Zhang, On the Extended, Generalized, and Grand Riemann Hypotheses: A Unified Approach via the Divisibility Property of Entire Functions*, Preprints.org, Version 23 (19 November 2026).

- [Current PDF in this repository](../ERH-GRH-GRAND-NEW%20Version.pdf)
- [Preprints.org manuscript record](https://www.preprints.org/manuscript/202506.0481)
- [Version 23 DOI](https://doi.org/10.20944/preprints202506.0481.v23)

## Scope and status

| Paper statement | Formalization status |
|---|---|
| Lemma 1: irreducible polynomial divides a finite product | Formalized and merged in PR #2; CI passed |
| Lemma 2: divisibility for infinite products of entire functions | Formalized in PR #3 and corrected in PR #4; final CI passed |
| Theorem 1: symmetric entire-function product theorem | Center-line conclusion, distinct heights, and strictly increasing bijective reindexing formalized in PRs #5–#6; final CI passed. PR #7 adds the local absolute-convergence bridge |

## Lemma 1

The paper's statement assumes

\(m,g_1,\ldots,g_n\in\mathbb R[x],\quad n\geq 2\),

with \(m\) irreducible (prime) and \(m\mid g_1\cdots g_n\), and concludes that \(m\) divides one of the factors.

In Lean, the finite family is represented by a list. The file first proves the generic fact for a prime element of a commutative monoid with zero, then applies it to `Polynomial ℝ`. The list theorem is slightly stronger than the paper's stated version because it does not need a separate lower bound on the list length.

## Build

The project is pinned to Lean `v4.36.0` and Mathlib `v4.36.0`.

From this directory, run:

```bash
lake update
lake exe cache get
lake build
```

A GitHub Actions workflow builds the project and audits theorem axioms. A statement is described as machine-verified only after that workflow succeeds. No `sorry` or project-defined axiom is intended to be used.

## Lemma 2

`RiemannHypothesisLean/Lemma2.lean` formalizes the pointwise argument at a complex root of an irreducible real polynomial. Absolute convergence at that point is expressed as summability of the norms of the deviations of the factors from `1`; the infinite product is represented by Mathlib's `HasProd`.

The function-level theorem assumes an entire quotient witnessing divisibility by `m`, together with the pointwise product representation. It then proves that `m` divides one factor. This formal theorem is stronger than the paper's stated algebraic conclusion: it does not require each factor to be irreducible or to have the same degree as `m`. The global locally uniform convergence hypothesis and the condition `f(0) ≠ 0` are not needed for this root-level implication; the product's pointwise absolute convergence and the existence of the entire quotient are the hypotheses used by the proof.


## Theorem 1

`RiemannHypothesisLean/Theorem1.lean` uses the exact normalized quadratic factors from the paper, `1 + (X - C α)^2 / C (β^2)`; it does not replace them by monic scalar multiples, which would change the infinite product.

The formalization is layered:

1. Under the symmetry, irreducibility, and uniqueness of zero quadruples, it proves that every center parameter equals `k / 2`.
2. It proves that the absolute imaginary parts are pairwise distinct.
3. Using the summability condition `∑ mᵢ / βᵢ² < ∞`, it proves that the heights tend to infinity and constructs a bijective reindexing under which they are strictly increasing.

The lower-level theorem uses pointwise `HasProd` and summability of the deviations from `1`. PR #7 adds a formal bridge from local uniform absolute convergence to these pointwise conditions. Local uniform absolute convergence is expressed by a compact-wise summable majorant: on each compact set, one summable sequence bounds all factor deviations uniformly. Taking a singleton gives pointwise summability; Mathlib's summable-product theorem then gives `HasProd`. The pointwise representation identifies the resulting product with `F(z)`.

This is specifically an absolute-convergence condition on the factor deviations, not merely convergence of the partial products uniformly on compact sets. The entire-function packaging is stronger than what the pointwise root argument itself needs.
