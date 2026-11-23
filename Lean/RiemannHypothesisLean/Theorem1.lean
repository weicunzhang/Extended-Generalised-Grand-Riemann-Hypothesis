module

public import Mathlib
public import RiemannHypothesisLean.Lemma2

public section

/-!
# Theorem 1: the symmetry forces the quadratic factors onto the center line

We formalize the central algebraic step of Theorem 1. The normalized
quadratic factor in the paper is a nonzero scalar multiple of
(X - C α)^2 + C (β^2); we use this monic normalization because it
has the same roots and irreducibility.

The hypotheses record:
* the pointwise product representation, with each factor repeated
  according to its positive multiplicity;
* absolute convergence at every point, expressed by summability of
  the deviations of the repeated factors from 1;
* the symmetry F(z) = F(k-z);
* irreducibility of each real quadratic factor; and
* uniqueness of the zero quadruple, encoded by the condition that
  αᵢ + αⱼ = k and βᵢ² = βⱼ² imply i = j.

The theorem proves αᵢ = k/2 for every i. A separate corollary proves
that the values βᵢ² (and hence |βᵢ|) are pairwise distinct. The
increasing enumeration of these values is a reindexing step.
-/

namespace RiemannHypothesisLean

/-- Monic real quadratic with roots a ± I*b. -/
noncomputable def quadraticFactor (a b : ℝ) : Polynomial ℝ :=
  (Polynomial.X - Polynomial.C a) ^ 2 + Polynomial.C (b ^ 2)

/-- The root represented by the upper-half-plane zero. -/
lemma quadraticFactor_aeval_root (a b : ℝ) :
    (quadraticFactor a b).aeval ((a : ℂ) + Complex.I * b) = 0 := by
  simp [quadraticFactor]
  rw [Complex.I_sq]
  ring

/-- If a quadratic factor vanishes at the reflected point
k - (a + I*b), then its center and squared height satisfy the
corresponding reflection identities. -/
lemma quadraticFactor_root_coordinates {a b c d k : ℝ}
    (hb : b ≠ 0)
    (hroot : (quadraticFactor c d).aeval
      ((k : ℂ) - ((a : ℂ) + Complex.I * b)) = 0) :
    a + c = k ∧ b ^ 2 = d ^ 2 := by
  let u : ℝ := k - a - c
  have hroot' :
      ((k : ℂ) - ((a : ℂ) + Complex.I * b) - (c : ℂ)) ^ 2 + (d : ℂ) ^ 2 = 0 := by
    simpa [quadraticFactor] using hroot
  have hval : ((u : ℂ) - Complex.I * b) ^ 2 + (d : ℂ) ^ 2 = 0 := by
    dsimp [u]
    convert hroot' using 1 <;> push_cast <;> ring
  have hvalMul : ((u : ℂ) - Complex.I * b) * ((u : ℂ) - Complex.I * b)
      + (d : ℂ) ^ 2 = 0 := by
    simpa only [pow_two] using hval
  have hre := congrArg Complex.re hvalMul
  have him := congrArg Complex.im hvalMul
  simp [Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.I_re, Complex.I_im] at hre
  simp [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im] at him
  have hu : u = 0 := by
    have hub : u * b = 0 := by nlinarith [him]
    rcases mul_eq_zero.mp hub with hu | hb0
    · exact hu
    · exact (hb hb0).elim
  constructor
  · dsimp [u] at hu
    linarith
  · rw [hu] at hre
    nlinarith [hre]

/-- The center-line conclusion of Theorem 1.

The product representation is given pointwise by HasProd; absolute
convergence is expressed by summability of the deviations from 1.
The multiplicities are positive natural numbers. -/
theorem theorem1_centers
    (k : ℝ)
    (α β : ℕ → ℝ)
    (mult : ℕ → ℕ)
    (F : ℂ → ℂ)
    (hβ : ∀ i, β i ≠ 0)
    (hmult : ∀ i, 0 < mult i)
    (hquad : ∀ i, Irreducible (quadraticFactor (α i) (β i)))
    (hunique : ∀ i l, α i + α l = k → β i ^ 2 = β l ^ 2 → i = l)
    (hsym : ∀ z : ℂ, F z = F ((k : ℂ) - z))
    (hprod : ∀ z : ℂ, HasProd
      (fun n : ℕ => ((quadraticFactor (α n) (β n)).aeval z) ^ mult n) (F z))
    (habsolute : ∀ z : ℂ, Summable
      (fun n : ℕ => ‖((quadraticFactor (α n) (β n)).aeval z) ^ mult n - 1‖)) :
    ∀ i, α i = k / 2 := by
  intro i
  let z : ℂ := (α i : ℂ) + Complex.I * β i
  have hzroot : (quadraticFactor (α i) (β i)).aeval z = 0 := by
    simpa [z] using quadraticFactor_aeval_root (α i) (β i)
  have hzeroProd : HasProd
      (fun n : ℕ => ((quadraticFactor (α n) (β n)).aeval z) ^ mult n) 0 := by
    apply hasProd_zero_of_exists_eq_zero
    refine ⟨i, ?_⟩
    rw [hzroot]
    exact zero_pow (Nat.ne_of_gt (hmult i))
  have hFzero : F z = 0 := by
    rw [← (hprod z).tprod_eq]
    exact hzeroProd.tprod_eq
  have hFref : F ((k : ℂ) - z) = 0 := by
    rw [← hsym z, hFzero]
  have hprodRef : HasProd
      (fun l : ℕ =>
        ((quadraticFactor (α l) (β l)).comp
          (Polynomial.C k - Polynomial.X) ^ mult l).aeval z) 0 := by
    simpa [Polynomial.aeval_comp, hFref] using hprod ((k : ℂ) - z)
  have hsumRef : Summable
      (fun l : ℕ => ‖(((quadraticFactor (α l) (β l)).comp
        (Polynomial.C k - Polynomial.X)) ^ mult l).aeval z - 1‖) := by
    simpa [Polynomial.aeval_comp] using habsolute ((k : ℂ) - z)
  obtain ⟨l, hdiv⟩ := lemma2_core
    (quadraticFactor (α i) (β i))
    (fun l : ℕ => (quadraticFactor (α l) (β l)).comp
      (Polynomial.C k - Polynomial.X) ^ mult l)
    z (hquad i) hzroot hprodRef hsumRef
  have hpowroot :
      ((quadraticFactor (α l) (β l)).comp
        (Polynomial.C k - Polynomial.X) ^ mult l).aeval z = 0 := by
    exact ((hquad i).dvd_iff_aeval_eq_zero hzroot).2 hdiv
  have hfactorroot :
      ((quadraticFactor (α l) (β l)).comp
        (Polynomial.C k - Polynomial.X)).aeval z = 0 := by
    rw [Polynomial.aeval_pow] at hpowroot
    exact pow_eq_zero hpowroot
  have hrootl : (quadraticFactor (α l) (β l)).aeval
      ((k : ℂ) - z) = 0 := by
    simpa [Polynomial.aeval_comp] using hfactorroot
  have hcoords : α i + α l = k ∧ β i ^ 2 = β l ^ 2 := by
    apply quadraticFactor_root_coordinates (hβ i)
    simpa [z] using hrootl
  have hil : i = l := hunique i l hcoords.1 hcoords.2
  subst l
  nlinarith [hcoords.1]

/-- Once all centers equal k/2, uniqueness of zero quadruples forces
the squared heights to be pairwise distinct. -/
theorem theorem1_beta_sq_injective
    (k : ℝ)
    (α β : ℕ → ℝ)
    (hcenter : ∀ i, α i = k / 2)
    (hunique : ∀ i l, α i + α l = k → β i ^ 2 = β l ^ 2 → i = l) :
    Function.Injective (fun i => β i ^ 2) := by
  intro i l h
  apply hunique i l
  · rw [hcenter i, hcenter l]
    ring
  · exact h

/-- The absolute imaginary parts are pairwise distinct. -/
theorem theorem1_abs_beta_injective
    (k : ℝ)
    (α β : ℕ → ℝ)
    (hcenter : ∀ i, α i = k / 2)
    (hunique : ∀ i l, α i + α l = k → β i ^ 2 = β l ^ 2 → i = l) :
    Function.Injective (fun i => |β i|) := by
  intro i l h
  apply theorem1_beta_sq_injective k α β hcenter hunique
  calc
    β i ^ 2 = |β i| ^ 2 := (sq_abs (β i)).symm
    _ = |β l| ^ 2 := by rw [h]
    _ = β l ^ 2 := sq_abs (β l)

end RiemannHypothesisLean
