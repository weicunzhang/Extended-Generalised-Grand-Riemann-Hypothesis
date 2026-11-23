module

public import Mathlib
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import RiemannHypothesisLean.Lemma2

public section

/-!
# Theorem 1: the symmetry forces the quadratic factors onto the center line

We formalize the central algebraic step of Theorem 1 using the exact
normalized factor from the paper,
1 + (X - C α)^2 / C (β^2). This is important: replacing every factor
by its monic scalar multiple would change the infinite product itself.

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

/-- Normalized real quadratic factor with roots a ± I*b. -/
noncomputable def quadraticFactor (a b : ℝ) : Polynomial ℝ :=
  1 + Polynomial.C ((b ^ 2)⁻¹) * (Polynomial.X - Polynomial.C a) ^ 2

/-- The root represented by the upper-half-plane zero. -/
lemma quadraticFactor_aeval_root (a b : ℝ) (hb : b ≠ 0) :
    (quadraticFactor a b).aeval ((a : ℂ) + Complex.I * b) = 0 := by
  simp [quadraticFactor, mul_pow, Complex.I_sq, ← Complex.ofReal_pow]
  field_simp [hb]
  ring

/-- The normalized quadratic factor has degree two when its height is nonzero. -/
lemma quadraticFactor_natDegree (a b : ℝ) (hb : b ≠ 0) :
    (quadraticFactor a b).natDegree = 2 := by
  have hscale : (b ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero 2 hb)
  have hterm :
      (Polynomial.C ((b ^ 2)⁻¹) *
        (Polynomial.X - Polynomial.C a) ^ 2).natDegree = 2 := by
    rw [Polynomial.natDegree_C_mul hscale]
    simp
  change (1 + Polynomial.C ((b ^ 2)⁻¹) *
    (Polynomial.X - Polynomial.C a) ^ 2).natDegree = 2
  calc
    (1 + Polynomial.C ((b ^ 2)⁻¹) *
        (Polynomial.X - Polynomial.C a) ^ 2).natDegree
        = (Polynomial.C ((b ^ 2)⁻¹) *
            (Polynomial.X - Polynomial.C a) ^ 2).natDegree := by
          simpa only [add_comm] using
            (Polynomial.natDegree_add_eq_left_of_natDegree_lt
              (p := Polynomial.C ((b ^ 2)⁻¹) *
                (Polynomial.X - Polynomial.C a) ^ 2)
              (q := (1 : Polynomial ℝ))
              (by rw [hterm]; simp))
    _ = 2 := hterm

/-- The normalized quadratic factor has no real roots. -/
lemma quadraticFactor_not_isRoot (a b : ℝ) (hb : b ≠ 0) :
    ∀ x : ℝ, ¬ (quadraticFactor a b).IsRoot x := by
  intro x hx
  change (quadraticFactor a b).eval x = 0 at hx
  have hEval : 1 + (b ^ 2)⁻¹ * (x - a) ^ 2 = 0 := by
    simpa [quadraticFactor] using hx
  have hpos : 0 < (b ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_ne_zero hb)
  have hnonneg : 0 ≤ (b ^ 2)⁻¹ * (x - a) ^ 2 :=
    mul_nonneg (le_of_lt hpos) (sq_nonneg (x - a))
  linarith

/-- Every normalized quadratic factor with nonzero height is irreducible over ℝ. -/
lemma quadraticFactor_irreducible (a b : ℝ) (hb : b ≠ 0) :
    Irreducible (quadraticFactor a b) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [quadraticFactor_natDegree a b hb]
    norm_num
  · exact quadraticFactor_not_isRoot a b hb

/-- If a quadratic factor vanishes at the reflected point
k - (a + I*b), then its center and squared height satisfy the
corresponding reflection identities. -/
lemma quadraticFactor_root_coordinates {a b c d k : ℝ}
    (hb : b ≠ 0) (hd : d ≠ 0)
    (hroot : (quadraticFactor c d).aeval
      ((k : ℂ) - ((a : ℂ) + Complex.I * b)) = 0) :
    a + c = k ∧ b ^ 2 = d ^ 2 := by
  let u : ℝ := k - a - c
  have hroot' :
      1 + ((d ^ 2)⁻¹ : ℂ) *
        (((k : ℂ) - ((a : ℂ) + Complex.I * b) - (c : ℂ)) ^ 2) = 0 := by
    simpa [quadraticFactor] using hroot
  have hnorm : 1 + ((d ^ 2)⁻¹ : ℂ) * (((u : ℂ) - Complex.I * b) ^ 2) = 0 := by
    convert hroot' using 1 <;> dsimp [u] <;> push_cast <;> ring
  have hval : ((u : ℂ) - Complex.I * b) ^ 2 + (d : ℂ) ^ 2 = 0 := by
    field_simp [hd] at hnorm
    simpa [← Complex.ofReal_pow, add_comm] using hnorm
  have hvalMul : ((u : ℂ) - Complex.I * b) * ((u : ℂ) - Complex.I * b)
      + (d : ℂ) ^ 2 = 0 := by
    simpa only [pow_two] using hval
  have hwr : ((u : ℂ) - Complex.I * b).re = u := by
    simp [Complex.sub_re, Complex.mul_re]
  have hwi : ((u : ℂ) - Complex.I * b).im = -b := by
    simp [Complex.sub_im, Complex.mul_im]
  have hdre : (((d : ℂ) ^ 2).re) = d ^ 2 := by
    simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hdim : (((d : ℂ) ^ 2).im) = 0 := by
    simp only [pow_two, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hre := congrArg Complex.re hvalMul
  have him := congrArg Complex.im hvalMul
  simp [Complex.add_re, Complex.mul_re, hwr, hwi, hdre] at hre
  simp [Complex.add_im, Complex.mul_im, hwr, hwi, hdim] at him
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
    simpa [z] using quadraticFactor_aeval_root (α i) (β i) (hβ i)
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
  have hqi : Irreducible (quadraticFactor (α i) (β i)) :=
    quadraticFactor_irreducible (α i) (β i) (hβ i)
  obtain ⟨l, hdiv⟩ := lemma2_core
    (quadraticFactor (α i) (β i))
    (fun l : ℕ => (quadraticFactor (α l) (β l)).comp
      (Polynomial.C k - Polynomial.X) ^ mult l)
    z hqi hzroot hprodRef hsumRef
  have hpowroot :
      ((quadraticFactor (α l) (β l)).comp
        (Polynomial.C k - Polynomial.X) ^ mult l).aeval z = 0 := by
    exact (hqi.dvd_iff_aeval_eq_zero hzroot).2 hdiv
  have hpowroot' :
      (((quadraticFactor (α l) (β l)).comp
        (Polynomial.C k - Polynomial.X)).aeval z) ^ mult l = 0 := by
    simpa only [map_pow] using hpowroot
  have hfactorroot :
      ((quadraticFactor (α l) (β l)).comp
        (Polynomial.C k - Polynomial.X)).aeval z = 0 :=
    (pow_eq_zero_iff (Nat.ne_of_gt (hmult l))).1 hpowroot'
  have hrootl : (quadraticFactor (α l) (β l)).aeval
      ((k : ℂ) - z) = 0 := by
    simpa [Polynomial.aeval_comp] using hfactorroot
  have hcoords : α i + α l = k ∧ β i ^ 2 = β l ^ 2 := by
    apply quadraticFactor_root_coordinates (hβ i) (hβ l)
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
  change |β i| = |β l| at h
  apply theorem1_beta_sq_injective k α β hcenter hunique
  calc
    β i ^ 2 = |β i| ^ 2 := (sq_abs (β i)).symm
    _ = |β l| ^ 2 := by rw [h]
    _ = β l ^ 2 := sq_abs (β l)

end RiemannHypothesisLean
