import Mathlib

/-!
# Lemma 1: finite-product divisibility

The paper states the result for polynomials in ℝ[X] and a product of
n ≥ 2 factors. We first prove the underlying algebraic fact for any
finite list in a commutative monoid with zero, then specialize it to
Polynomial ℝ.

For polynomials over a field, Mathlib supplies the unique-factorization
structure, so an irreducible polynomial is prime.
-/

namespace RiemannHypothesisLean

/-- A prime divisor of a finite product divides at least one factor.

This generic list formulation is slightly stronger than the paper's
statement, which assumes at least two factors. -/
theorem prime_dvd_list_prod
    {R : Type*} [CommMonoidWithZero R] {p : R}
    (hp : Prime p) :
    ∀ xs : List R, p ∣ xs.prod → ∃ x ∈ xs, p ∣ x := by
  intro xs
  induction xs with
  | nil =>
      intro h
      simp only [List.prod_nil] at h
      exact False.elim (hp.not_dvd_one h)
  | cons a xs ih =>
      intro h
      simp only [List.prod_cons] at h
      rcases hp.dvd_mul.mp h with ha | hxs
      · exact ⟨a, by simp, ha⟩
      · rcases ih hxs with ⟨x, hx, hpx⟩
        exact ⟨x, by simp [hx], hpx⟩

/-- Lemma 1 of the preprint, expressed with a finite list of factors. -/
theorem lemma1
    (m : Polynomial ℝ)
    (gs : List (Polynomial ℝ))
    (hm : Irreducible m)
    (hdiv : m ∣ gs.prod) :
    ∃ g ∈ gs, m ∣ g := by
  have hm_prime : Prime m := hm.prime
  exact prime_dvd_list_prod hm_prime gs hdiv

end RiemannHypothesisLean
