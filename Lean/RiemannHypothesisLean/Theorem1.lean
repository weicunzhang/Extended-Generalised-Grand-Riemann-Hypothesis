module

public import Mathlib
public import Mathlib.Algebra.Polynomial.SpecificDegree
public import Mathlib.Order.SuccPred.LinearLocallyFinite
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


/-- A finite cutoff for a sequence tending to +∞: after this index,
all values exceed the prescribed value r b. -/
noncomputable def tendstoBound (r : ℕ → ℝ)
    (hr : Filter.Tendsto r (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)) (b : ℕ) : ℕ :=
  Classical.choose
    (Filter.eventually_atTop.mp
      (hr.eventually (Filter.eventually_gt_atTop (r b))))

theorem tendstoBound_spec (r : ℕ → ℝ)
    (hr : Filter.Tendsto r (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)) (b n : ℕ)
    (hn : tendstoBound r hr b ≤ n) : r b < r n := by
  have hspec := Classical.choose_spec
    (Filter.eventually_atTop.mp
      (hr.eventually (Filter.eventually_gt_atTop (r b))))
  have hn' : Classical.choose
      (Filter.eventually_atTop.mp
        (hr.eventually (Filter.eventually_gt_atTop (r b)))) ≤ n := by
    simpa only [tendstoBound] using hn
  exact hspec n hn'

/-- A finite set containing exactly the indices whose r-values
lie in the closed interval [r a, r b], when r tends to +∞. -/
noncomputable def tendstoIccFinset (r : ℕ → ℝ)
    (hr : Filter.Tendsto r (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)) (a b : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (tendstoBound r hr b)).filter
    (fun n => r a ≤ r n ∧ r n ≤ r b)

theorem mem_tendstoIccFinset (r : ℕ → ℝ)
    (hr : Filter.Tendsto r (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)) (a b x : ℕ) :
    x ∈ tendstoIccFinset r hr a b ↔ r a ≤ r x ∧ r x ≤ r b := by
  classical
  simp only [tendstoIccFinset, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨_, hax, hxb⟩
    exact ⟨hax, hxb⟩
  · rintro ⟨hax, hxb⟩
    refine ⟨?_, hax, hxb⟩
    by_contra hx
    have hx' : tendstoBound r hr b ≤ x := Nat.le_of_not_gt hx
    exact (not_lt_of_ge hxb) (tendstoBound_spec r hr b x hx')

/-- If sum mult n / beta n^2 converges and every multiplicity is positive,
then the absolute heights tend to infinity. -/
theorem theorem1_abs_beta_tendsto_atTop
    (β : ℕ → ℝ) (mult : ℕ → ℕ)
    (hβ : ∀ n, β n ≠ 0)
    (hmult : ∀ n, 0 < mult n)
    (hsum : Summable (fun n => (mult n : ℝ) / β n ^ 2)) :
    Filter.Tendsto (fun n => |β n|) (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ) := by
  have hsum' : Summable (fun n => (mult n : ℝ) * (β n ^ 2)⁻¹) := by
    simpa only [div_eq_mul_inv] using hsum
  have hrecip : Summable (fun n => (|β n| ^ 2)⁻¹) := by
    apply Summable.of_nonneg_of_le
      (f := fun n => (mult n : ℝ) * (β n ^ 2)⁻¹)
      (g := fun n => (|β n| ^ 2)⁻¹)
    · intro n
      exact inv_nonneg.mpr (sq_nonneg (|β n|))
    · intro n
      have hmult1 : (1 : ℝ) ≤ (mult n : ℝ) := by
        exact_mod_cast (Nat.succ_le_of_lt (hmult n))
      rw [sq_abs]
      simpa only [one_mul] using
        (mul_le_mul_of_nonneg_right hmult1
          (inv_nonneg.mpr (sq_nonneg (β n))))
    · exact hsum'
  have hzero : Filter.Tendsto (fun n => (|β n| ^ 2)⁻¹) (Filter.atTop : Filter ℕ) (𝓝 0) :=
    hrecip.tendsto_atTop_zero
  refine Filter.tendsto_atTop.2 ?_
  intro B
  let C : ℝ := max B 0 + 1
  have hCpos : 0 < C := by
    dsimp [C]
    positivity
  have hBC : B < C := by
    dsimp [C]
    linarith [le_max_left B 0]
  have hsmall : ∀ᶠ n : ℕ in atTop, (|β n| ^ 2)⁻¹ < (C ^ 2)⁻¹ := by
    have hnhds : Set.Iio ((C ^ 2)⁻¹) ∈ 𝓝 (0 : ℝ) :=
      Iio_mem_nhds (by positivity)
    exact hzero.eventually hnhds
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hsmall
  refine ⟨N, ?_⟩
  intro n hn
  have hβpos : 0 < |β n| := abs_pos.mpr (hβ n)
  have hsq : C ^ 2 < |β n| ^ 2 :=
    (inv_lt_inv₀ (pow_pos hβpos 2) (pow_pos hCpos 2)).1 (hN n hn)
  have hCr : C < |β n| := by
    nlinarith
  exact hBC.trans hCr

/-- A finite interval of indices, lifted to a type synonym so that
the order induced by r does not overwrite the usual order on ℕ. -/
noncomputable def tendstoIccFinsetULift (r : ℕ → ℝ)
    (hr : Filter.Tendsto r (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
    (a b : ULift ℕ) : Finset (ULift ℕ) := by
  classical
  exact ((Finset.range (tendstoBound r hr b.down)).image ULift.up).filter
    (fun n => r a.down ≤ r n.down ∧ r n.down ≤ r b.down)

theorem mem_tendstoIccFinsetULift (r : ℕ → ℝ)
    (hr : Filter.Tendsto r (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ))
    (a b x : ULift ℕ) :
    x ∈ tendstoIccFinsetULift r hr a b ↔
      r a.down ≤ r x.down ∧ r x.down ≤ r b.down := by
  classical
  simp only [tendstoIccFinsetULift, Finset.mem_filter, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨⟨n, hn, hEq⟩, hax, hxb⟩
    cases hEq
    exact ⟨hax, hxb⟩
  · rintro ⟨hax, hxb⟩
    refine ⟨⟨x.down, ?_, ?_⟩, hax, hxb⟩
    · by_contra hx
      have hbound : tendstoBound r hr b.down ≤ x.down := Nat.le_of_not_gt hx
      exact (not_lt_of_ge hxb) (tendstoBound_spec r hr b.down x.down hbound)
    · cases x
      rfl

/-- A sequence of distinct real numbers tending to +∞ can be
reindexed by a permutation of ℕ so that it is strictly increasing.

We use ULift for the ordered index type, keeping the target ℕ in the
usual order. Bounded intervals in the induced order are finite; the
order has a least element and no greatest element. -/
theorem exists_strictMono_reindex_of_tendsto_atTop
    (r : ℕ → ℝ) (hinj : Function.Injective r)
    (hr : Filter.Tendsto r (Filter.atTop : Filter ℕ) (Filter.atTop : Filter ℝ)) :
    ∃ σ : ℕ ≃ ℕ, StrictMono (fun n => r (σ n)) := by
  classical
  let rLift : ULift ℕ → ℝ := fun n => r n.down
  have hrLiftInj : Function.Injective rLift := by
    intro a b hab
    apply ULift.down_injective
    exact hinj hab
  letI : LinearOrder (ULift ℕ) := LinearOrder.lift' rLift hrLiftInj
  letI : LE (ULift ℕ) := ⟨fun a b => r a.down ≤ r b.down⟩
  letI : LT (ULift ℕ) := ⟨fun a b => r a.down < r b.down⟩
  letI : LocallyFiniteOrder (ULift ℕ) :=
    LocallyFiniteOrder.ofIcc' (ULift ℕ) (tendstoIccFinsetULift r hr) (by
      intro a b x
      change x ∈ tendstoIccFinsetULift r hr a b ↔
        r a.down ≤ r x.down ∧ r x.down ≤ r b.down
      exact mem_tendstoIccFinsetULift r hr a b x)
  let N0 : ℕ := tendstoBound r hr 0
  have hN0 : 0 < N0 := by
    by_contra hN0
    have hN0' : N0 = 0 := Nat.eq_zero_of_not_pos hN0
    have hle : tendstoBound r hr 0 ≤ 0 := by
      simpa [N0, hN0']
    have hcontr : r 0 < r 0 := tendstoBound_spec r hr 0 0 hle
    exact (lt_irrefl (r 0)) hcontr
  let S : Finset (ULift ℕ) :=
    ((Finset.range N0).image ULift.up).filter (fun n => r n.down ≤ r 0)
  have h0S : ULift.up 0 ∈ S := by
    simp [S, hN0]
  have hS : S.Nonempty := ⟨ULift.up 0, h0S⟩
  let b : ULift ℕ := S.min' hS
  have hbS : b ∈ S := Finset.min'_mem S hS
  have hbr0 : r b.down ≤ r 0 := (Finset.mem_filter.mp hbS).2
  letI : Bot (ULift ℕ) := ⟨b⟩
  letI : OrderBot (ULift ℕ) :=
    ⟨fun n => by
      change r b.down ≤ r n.down
      by_cases hn : n.down < N0
      · by_cases hle : r n.down ≤ r 0
        · have hnS : n ∈ S := by
            simp [S, hn, hle]
          exact Finset.min'_le S hS n hnS
        · exact le_of_lt (hbr0.trans_lt (lt_of_not_ge hle))
      · have h0n : r 0 < r n.down :=
          tendstoBound_spec r hr 0 n.down (Nat.le_of_not_gt hn)
        exact le_of_lt (hbr0.trans_lt h0n)⟩
  letI : NoMaxOrder (ULift ℕ) :=
    ⟨fun n => by
      have hev : ∀ᶠ m : ℕ in Filter.atTop, r n.down < r m :=
        hr.eventually (Filter.eventually_gt_atTop (r n.down))
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev
      refine ⟨ULift.up (N + n.down + 1), ?_⟩
      change r n.down < r (N + n.down + 1)
      exact hN _ (by omega)⟩
  letI : SuccOrder (ULift ℕ) :=
    LinearLocallyFiniteOrder.succOrder (ULift ℕ)
  letI : PredOrder (ULift ℕ) :=
    LinearLocallyFiniteOrder.predOrder (ULift ℕ)
  let e : ULift ℕ ≃o ℕ :=
    LinearLocallyFiniteOrder.orderIsoNatOfLinearSuccPredArch
  let σ : ℕ ≃ ℕ where
    toFun n := (e.symm n).down
    invFun n := e (ULift.up n)
    left_inv n := by simp
    right_inv n := by simp
  refine ⟨σ, ?_⟩
  intro n m hnm
  have hlt : e.symm n < e.symm m := e.symm.strictMono hnm
  change r (e.symm n).down < r (e.symm m).down at hlt
  change r (σ n) < r (σ m)
  exact hlt

/-- The increasing-height conclusion of Theorem 1, with the
reindexing made explicit as a bijection of the natural-number indices. -/
theorem theorem1_sorted_heights
    (β : ℕ → ℝ) (mult : ℕ → ℕ)
    (hβ : ∀ n, β n ≠ 0)
    (hmult : ∀ n, 0 < mult n)
    (hinj : Function.Injective (fun n => |β n|))
    (hsum : Summable (fun n => (mult n : ℝ) / β n ^ 2)) :
    ∃ σ : ℕ ≃ ℕ, StrictMono (fun n => |β (σ n)|) := by
  have htendsto := theorem1_abs_beta_tendsto_atTop β mult hβ hmult hsum
  exact exists_strictMono_reindex_of_tendsto_atTop
    (fun n => |β n|) hinj htendsto

end RiemannHypothesisLean
