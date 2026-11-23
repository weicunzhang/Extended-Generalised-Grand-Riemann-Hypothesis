module

import Mathlib

/-!
# Lemma 2: divisibility for an absolutely convergent infinite product

The paper's Lemma 2 is reduced to its pointwise root argument. At a fixed
complex root α of an irreducible real polynomial m, absolute convergence
of the product is represented by summability of the deviations
`‖g_n(α) - 1‖`. The product itself is represented by `HasProd`.

The formal theorem is stronger than the paper's algebraic conclusion:
the factors `g_n` need not be irreducible and need not have the same
degree as `m`. Once a factor shares the root α with irreducible `m`,
`Irreducible.dvd_iff_aeval_eq_zero` gives `m ∣ g_n` directly.
-/

namespace RiemannHypothesisLean

/-- If the deviations of a complex sequence from `1` are summable,
then its infinite product is nonzero whenever no factor is zero. -/
theorem tprod_ne_zero_of_summable_sub_one
    (u : ℕ → ℂ)
    (hsum : Summable (fun n => ‖u n - 1‖))
    (hne : ∀ n, u n ≠ 0) :
    ∏' n, u n ≠ 0 := by
  have h := tprod_one_add_ne_zero_of_summable
    (f := fun n => u n - 1)
    (fun n => by simpa using hne n)
    (by simpa using hsum)
  simpa using h

/-- The root-level divisibility statement underlying Lemma 2.

If `m` is irreducible, `α` is a root of `m`, the product of the values
`g n (α)` is zero, and the deviations from `1` are summable, then some
factor `g n` vanishes at `α`. Irreducibility then implies `m ∣ g n`.
This version does not require the factors `g n` to be irreducible or
to have the same degree as `m`. -/
theorem lemma2_core
    (m : Polynomial ℝ)
    (g : ℕ → Polynomial ℝ)
    (α : ℂ)
    (hm : Irreducible m)
    (hm_root : m.aeval α = 0)
    (hprod : HasProd (fun n => (g n).aeval α) 0)
    (hsum : Summable (fun n => ‖(g n).aeval α - 1‖)) :
    ∃ n, m ∣ g n := by
  by_contra hnone
  have hne : ∀ n, (g n).aeval α ≠ 0 := by
    intro n hn
    apply hnone
    exact ⟨n, (hm.dvd_iff_aeval_eq_zero hm_root).2 hn⟩
  have hprod_ne : ∏' n, (g n).aeval α ≠ 0 := by
    simpa using
      (tprod_one_add_ne_zero_of_summable
        (f := fun n => (g n).aeval α - 1)
        (fun n => by simpa using hne n)
        (by simpa using hsum))
  exact hprod_ne hprod.tprod_eq

/-- A function-level version of Lemma 2.

`hdiv` expresses divisibility in the ring of entire functions by
providing an entire quotient. `hprod` records the pointwise infinite
product representation, and `habsolutely` records absolute convergence
through summability of the deviations from `1`. The proof only needs
these hypotheses at one complex root of `m`.

The paper's extra assumptions `f(0) ≠ 0`, degree `1` or `2`, and
irreducibility of each `g n` are not needed for this implication. -/
theorem lemma2
    (f : ℂ → ℂ)
    (g : ℕ → Polynomial ℝ)
    (m : Polynomial ℝ)
    (hm : Irreducible m)
    (hdiv : ∃ h : ℂ → ℂ, Differentiable ℂ h ∧
      f = fun z => (m.aeval z) * h z)
    (hprod : ∀ z : ℂ, HasProd (fun n => (g n).aeval z) (f z))
    (habsolutely : ∀ z : ℂ, Summable (fun n => ‖(g n).aeval z - 1‖)) :
    ∃ n, m ∣ g n := by
  obtain ⟨α, hα⟩ : ∃ α : ℂ, m.aeval α = 0 :=
    IsAlgClosed.exists_aeval_eq_zero _ m (degree_pos_of_irreducible hm).ne'
  rcases hdiv with ⟨h, h_entire, h_eq⟩
  have hfα : f α = 0 := by
    have hfactor : f α = (m.aeval α) * h α := congrFun h_eq α
    rw [hfactor, hα, zero_mul]
  have hprod0 : HasProd (fun n => (g n).aeval α) 0 := by
    simpa [hfα] using hprod α
  exact lemma2_core m g α hm hα hprod0 (habsolutely α)

end RiemannHypothesisLean
