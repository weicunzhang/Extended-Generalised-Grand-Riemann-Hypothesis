# Lean 4 formalization of the preprint

This directory contains a Lean 4 project using Mathlib, intended to formalize selected statements from:

*Weicun Zhang, On the Extended, Generalized, and Grand Riemann Hypotheses: A Unified Approach via the Divisibility Property of Entire Functions*, Preprints.org, Version 23 (19 November 2026).

- [Current PDF in this repository](../ERH-GRH-GRAND-NEW%20Version.pdf)
- [Preprints.org manuscript record](https://www.preprints.org/manuscript/202506.0481)
- [Version 23 DOI](https://doi.org/10.20944/preprints202506.0481.v23)

## Scope and status

| Paper statement | Formalization status |
|---|---|
| Lemma 1: irreducible polynomial divides a finite product | Initial Lean statement and proof written; awaiting CI compilation |
| Lemma 2: divisibility for infinite products of entire functions | Root-level and function-level Lean theorem written; CI verification pending |
| Theorem 1: symmetric entire-function product theorem | Not yet formalized |

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
