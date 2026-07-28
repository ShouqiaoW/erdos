import Erdos390.Full.PaperBridgeFit

/-!
# Uniform finite-n nuisance gap from the literal paper cells

The positivity theorem in `PaperBridgeFit` chooses a finite-dimensional
left inverse separately for each `n`.  That proves positivity at a fixed
`n`, but by itself does not produce the constant `gamma_W` used in the
paper.  Here we give the quantitative argument directly.  A common lower
bound for every normalized head/physical cell, a fixed separation between
the two physical means, and a fixed bound for those means imply a covariance
gap with a completely explicit constant.  No limiting mixture occurs.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The selected cell pairs used to reconstruct the physical coordinate
and each nonreference head coordinate. -/
def nuisanceSelectedPair : Option B.HeadIndex -> Cell Head × Cell Head
  | none =>
      ((B.referenceHead, PhysicalSign.plus),
        (B.referenceHead, PhysicalSign.minus))
  | some h =>
      ((h.1, PhysicalSign.minus),
        (B.referenceHead, PhysicalSign.minus))

theorem nuisanceSelectedPair_injective :
    Function.Injective B.nuisanceSelectedPair := by
  intro i j hij
  cases i with
  | none =>
      cases j with
      | none => rfl
      | some h =>
          have hfirst := congrArg (fun z => z.1.2) hij
          simp [nuisanceSelectedPair] at hfirst
  | some h =>
      cases j with
      | none =>
          have hfirst := congrArg (fun z => z.1.2) hij
          simp [nuisanceSelectedPair] at hfirst
      | some k =>
          have hhead : h.1 = k.1 := by
            simpa [nuisanceSelectedPair] using
              congrArg (fun z => z.1.1) hij
          exact congrArg some (Subtype.ext hhead)

/-- Exact coordinate expansion of the nuisance Euclidean norm. -/
theorem nuisance_norm_sq_coordinates (x : B.NuisanceSpace) :
    ‖x‖ ^ 2 =
      x NuisanceCoord.physical ^ 2 +
        ∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]
  let e : NuisanceCoord B.HeadIndex ≃ Option B.HeadIndex :=
    { toFun := fun c => match c with
        | .physical => none
        | .head h => some h
      invFun := fun c => match c with
        | none => .physical
        | some h => .head h
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro c; cases c <;> rfl }
  calc
    (∑ c : NuisanceCoord B.HeadIndex, x c ^ 2) =
        ∑ c : Option B.HeadIndex, x (e.symm c) ^ 2 := by
      exact Fintype.sum_equiv e (fun c => x c ^ 2)
        (fun c => x (e.symm c) ^ 2) (fun c => by simp)
    _ = x NuisanceCoord.physical ^ 2 +
        ∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2 := by
      rw [Fintype.sum_option]
      rfl

/-- Evaluation of the selected physical pair difference. -/
theorem inner_nuisanceSelectedPair_none [Nonempty Head]
    (x : B.NuisanceSpace) :
    inner ℝ x
        (B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair none).1 -
          B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair none).2) =
      (B.cellPhysicalMean (B.referenceHead, .plus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical := by
  rw [show (B.nuisanceSelectedPair none).1 =
      (B.referenceHead, PhysicalSign.plus) by rfl,
    show (B.nuisanceSelectedPair none).2 =
      (B.referenceHead, PhysicalSign.minus) by rfl,
    B.nuisancePattern_sameHead_sub B.referenceHead,
    inner_smul_right, EuclideanSpace.inner_single_right]
  simp only [RCLike.conj_to_real, one_mul]

/-- Evaluation of a selected head-pair difference. -/
theorem inner_nuisanceSelectedPair_some [Nonempty Head]
    (x : B.NuisanceSpace) (h : B.HeadIndex) :
    inner ℝ x
        (B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair (some h)).1 -
          B.nuisanceCoarseBaseline.pattern
            (B.nuisanceSelectedPair (some h)).2) =
      (B.cellPhysicalMean (h.1, .minus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical + x (NuisanceCoord.head h) := by
  rw [show (B.nuisanceSelectedPair (some h)).1 =
      (h.1, PhysicalSign.minus) by rfl,
    show (B.nuisanceSelectedPair (some h)).2 =
      (B.referenceHead, PhysicalSign.minus) by rfl,
    B.nuisancePattern_head_sub h .minus,
    inner_add_right, inner_smul_right,
    EuclideanSpace.inner_single_right,
    EuclideanSpace.inner_single_right]
  simp only [RCLike.conj_to_real, one_mul]

/-- Sum of the squared scalar differences on the explicitly selected cell
pairs. -/
def nuisanceSelectedSquare [Nonempty Head] (x : B.NuisanceSpace) : ℝ :=
  ∑ o : Option B.HeadIndex,
    (inner ℝ x
      (B.nuisanceCoarseBaseline.pattern (B.nuisanceSelectedPair o).1 -
        B.nuisanceCoarseBaseline.pattern (B.nuisanceSelectedPair o).2)) ^ 2

theorem nuisanceSelectedSquare_eq [Nonempty Head]
    (x : B.NuisanceSpace) :
    B.nuisanceSelectedSquare x =
      ((B.cellPhysicalMean (B.referenceHead, .plus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical) ^ 2 +
      ∑ h : B.HeadIndex,
        ((B.cellPhysicalMean (h.1, .minus) -
            B.cellPhysicalMean (B.referenceHead, .minus)) *
          x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 := by
  rw [nuisanceSelectedSquare, Fintype.sum_option,
    B.inner_nuisanceSelectedPair_none]
  apply congrArg₂ (· + ·) rfl
  apply Finset.sum_congr rfl
  intro h _
  rw [B.inner_nuisanceSelectedPair_some]

/-- A conditional physical mean is at most any cellwise upper bound. -/
theorem cellPhysicalMean_le_of_cellwise [Nonempty Head]
    (c : Cell Head) (r : ℝ)
    (hpoint : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = c → B.physicalScore m ≤ r) :
    B.cellPhysicalMean c ≤ r := by
  let s := (Finset.univ : Finset B.sampleData.Sample).filter
    (fun m => B.sampleData.cellOf m = c)
  have hsum :
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m) ≤
      B.nuisanceCoarseBaseline.weight c * r := by
    calc
      (∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
        B.nuisanceFineBaseline.weight m * B.physicalScore m) ≤
          ∑ m ∈ s, B.nuisanceFineBaseline.weight m * r := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (hpoint m (Finset.mem_filter.mp hm).2)
          (B.nuisanceFineBaseline.weight_nonneg m)
      _ = (∑ m ∈ s, B.nuisanceFineBaseline.weight m) * r := by
        rw [Finset.sum_mul]
      _ = B.nuisanceCoarseBaseline.weight c * r := by
        have hmass := B.nuisanceCoarseCertificate.cell_mass c
        simpa only [s] using congrArg (fun z => z * r) hmass
  rw [← B.cellPhysicalMean_mul_weight c] at hsum
  exact (mul_le_mul_iff_right₀
    (B.nuisanceCoarseBaseline_weight_pos c)).mp hsum

/-- A conditional physical mean is at least any cellwise lower bound. -/
theorem le_cellPhysicalMean_of_cellwise [Nonempty Head]
    (c : Cell Head) (r : ℝ)
    (hpoint : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = c → r ≤ B.physicalScore m) :
    r ≤ B.cellPhysicalMean c := by
  let s := (Finset.univ : Finset B.sampleData.Sample).filter
    (fun m => B.sampleData.cellOf m = c)
  have hsum :
      B.nuisanceCoarseBaseline.weight c * r ≤
        ∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
          B.nuisanceFineBaseline.weight m * B.physicalScore m := by
    calc
      B.nuisanceCoarseBaseline.weight c * r =
          (∑ m ∈ s, B.nuisanceFineBaseline.weight m) * r := by
        have hmass := B.nuisanceCoarseCertificate.cell_mass c
        simpa only [s] using (congrArg (fun z => z * r) hmass).symm
      _ = ∑ m ∈ s, B.nuisanceFineBaseline.weight m * r := by
        rw [Finset.sum_mul]
      _ ≤ ∑ m ∈ (Finset.univ : Finset B.sampleData.Sample) with
          B.sampleData.cellOf m = c,
          B.nuisanceFineBaseline.weight m * B.physicalScore m := by
        apply Finset.sum_le_sum
        intro m hm
        exact mul_le_mul_of_nonneg_left
          (hpoint m (Finset.mem_filter.mp hm).2)
          (B.nuisanceFineBaseline.weight_nonneg m)
  rw [← B.cellPhysicalMean_mul_weight c] at hsum
  exact (mul_le_mul_iff_right₀
    (B.nuisanceCoarseBaseline_weight_pos c)).mp hsum

theorem abs_cellPhysicalMean_le_of_cellwise [Nonempty Head]
    (c : Cell Head) (R : ℝ)
    (hpoint : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = c → |B.physicalScore m| ≤ R) :
    |B.cellPhysicalMean c| ≤ R := by
  rw [abs_le]
  constructor
  · apply B.le_cellPhysicalMean_of_cellwise c (-R)
    intro m hm
    exact (abs_le.mp (hpoint m hm)).1
  · apply B.cellPhysicalMean_le_of_cellwise c R
    intro m hm
    exact (abs_le.mp (hpoint m hm)).2

/-- Fixed cellwise physical ranges give the quantitative separation needed
by the uniform covariance theorem. -/
theorem cellPhysicalMean_sub_ge_of_cellwise [Nonempty Head]
    (h : Head) (rminus rplus : ℝ)
    (hminus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (h, .minus) →
        B.physicalScore m ≤ rminus)
    (hplus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (h, .plus) →
        rplus ≤ B.physicalScore m) :
    rplus - rminus ≤
      B.cellPhysicalMean (h, .plus) -
        B.cellPhysicalMean (h, .minus) := by
  have hm := B.cellPhysicalMean_le_of_cellwise (h, .minus) rminus hminus
  have hp := B.le_cellPhysicalMean_of_cellwise (h, .plus) rplus hplus
  linarith

/-- The baseline coarse covariance dominates the selected reconstruction
sum.  This is an exact finite inequality and uses only a common lower bound
for the actual normalized cell masses. -/
theorem nuisanceCoarseBaseline_covariance_ge_selected
    [Nonempty Head] {lambda : ℝ} (hlambda : 0 ≤ lambda)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (x : B.NuisanceSpace) :
    (lambda ^ 2 / 2) * B.nuisanceSelectedSquare x ≤
      B.nuisanceCoarseBaseline.covarianceForm x := by
  let term : (Cell Head × Cell Head) → ℝ := fun ij =>
    B.nuisanceCoarseBaseline.weight ij.1 *
      B.nuisanceCoarseBaseline.weight ij.2 *
      (inner ℝ x
        (B.nuisanceCoarseBaseline.pattern ij.1 -
          B.nuisanceCoarseBaseline.pattern ij.2)) ^ 2
  have hcoarseWeight : ∀ c : Cell Head,
      lambda ≤ B.nuisanceCoarseBaseline.weight c := by
    intro c
    rw [B.nuisanceCoarseBaseline_weight c]
    exact hweight c
  have hterm_nonneg : ∀ ij, 0 ≤ term ij := by
    intro ij
    exact mul_nonneg
      (mul_nonneg
        (B.nuisanceCoarseBaseline.weight_nonneg ij.1)
        (B.nuisanceCoarseBaseline.weight_nonneg ij.2))
      (sq_nonneg _)
  have hselectedWeight :
      lambda ^ 2 * B.nuisanceSelectedSquare x ≤
        ∑ o : Option B.HeadIndex, term (B.nuisanceSelectedPair o) := by
    rw [nuisanceSelectedSquare, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro o _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hleft := hcoarseWeight (B.nuisanceSelectedPair o).1
    have hright := hcoarseWeight (B.nuisanceSelectedPair o).2
    have hwleft := B.nuisanceCoarseBaseline.weight_nonneg
      (B.nuisanceSelectedPair o).1
    have hwright := B.nuisanceCoarseBaseline.weight_nonneg
      (B.nuisanceSelectedPair o).2
    nlinarith
  have hselectedSubset :
      (∑ o : Option B.HeadIndex, term (B.nuisanceSelectedPair o)) ≤
        ∑ ij : Cell Head × Cell Head, term ij := by
    calc
      (∑ o : Option B.HeadIndex, term (B.nuisanceSelectedPair o)) =
          ∑ ij ∈ (Finset.univ : Finset (Option B.HeadIndex)).image
              B.nuisanceSelectedPair, term ij := by
            rw [Finset.sum_image]
            intro a _ b _ hab
            exact B.nuisanceSelectedPair_injective hab
      _ ≤ ∑ ij ∈ (Finset.univ : Finset (Cell Head × Cell Head)),
            term ij := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.subset_univ _)
            (fun ij _ _ => hterm_nonneg ij)
      _ = ∑ ij : Cell Head × Cell Head, term ij := by simp
  rw [B.nuisanceCoarseBaseline.covarianceForm_pairDifference x]
  calc
    (lambda ^ 2 / 2) * B.nuisanceSelectedSquare x =
        (1 / 2 : ℝ) *
          (lambda ^ 2 * B.nuisanceSelectedSquare x) := by ring
    _ ≤ (1 / 2 : ℝ) *
        (∑ o : Option B.HeadIndex,
          term (B.nuisanceSelectedPair o)) := by
      exact mul_le_mul_of_nonneg_left hselectedWeight (by norm_num)
    _ ≤ (1 / 2 : ℝ) *
        (∑ ij : Cell Head × Cell Head, term ij) := by
      exact mul_le_mul_of_nonneg_left hselectedSubset (by norm_num)
    _ = (1 / 2 : ℝ) * ∑ i, ∑ j,
        B.nuisanceCoarseBaseline.weight i *
          B.nuisanceCoarseBaseline.weight j *
          (inner ℝ x
            (B.nuisanceCoarseBaseline.pattern i -
              B.nuisanceCoarseBaseline.pattern j)) ^ 2 := by
      simp only [Fintype.sum_prod_type, term]

/-- A uniform geometric denominator.  Its only dimensional dependence is
the fixed number of nonreference head coordinates. -/
def nuisanceGeometryConstant (sep R : ℝ) : ℝ :=
  2 * sep ^ 2 + 1 +
    8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ)

theorem nuisanceGeometryConstant_pos (sep R : ℝ) :
    0 < B.nuisanceGeometryConstant sep R := by
  unfold nuisanceGeometryConstant
  positivity

/-- One head coordinate is controlled by its selected pair difference and
the physical coordinate, with constants depending only on the common bound
for the physical cell means. -/
theorem headCoordinate_sq_le [Nonempty Head]
    {R : ℝ}
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) (h : B.HeadIndex) :
    x (NuisanceCoord.head h) ^ 2 ≤
      2 * ((B.cellPhysicalMean (h.1, .minus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
      8 * R ^ 2 * x NuisanceCoord.physical ^ 2 := by
  let r := B.cellPhysicalMean (h.1, .minus) -
    B.cellPhysicalMean (B.referenceHead, .minus)
  let xr := x NuisanceCoord.physical
  let xh := x (NuisanceCoord.head h)
  let q := r * xr + xh
  have hrabs : |r| ≤ 2 * R := by
    calc
      |r| ≤ |B.cellPhysicalMean (h.1, .minus)| +
          |B.cellPhysicalMean (B.referenceHead, .minus)| := by
        simpa only [r] using
          (abs_sub (B.cellPhysicalMean (h.1, .minus))
            (B.cellPhysicalMean (B.referenceHead, .minus)))
      _ ≤ R + R := add_le_add
        (hmean (h.1, .minus))
        (hmean (B.referenceHead, .minus))
      _ = 2 * R := by ring
  have hrsq : r ^ 2 ≤ (2 * R) ^ 2 := by
    simpa only [sq_abs] using
      (pow_le_pow_left₀ (abs_nonneg r) hrabs 2)
  have hrx : (r * xr) ^ 2 ≤ 4 * R ^ 2 * xr ^ 2 := by
    calc
      (r * xr) ^ 2 = r ^ 2 * xr ^ 2 := by ring
      _ ≤ (2 * R) ^ 2 * xr ^ 2 :=
        mul_le_mul_of_nonneg_right hrsq (sq_nonneg xr)
      _ = 4 * R ^ 2 * xr ^ 2 := by ring
  have hbasic : xh ^ 2 ≤ 2 * q ^ 2 + 2 * (r * xr) ^ 2 := by
    dsimp only [q]
    nlinarith [sq_nonneg ((r * xr + xh) + r * xr)]
  dsimp only [r, xr, xh, q] at hbasic hrx ⊢
  linarith

theorem headCoordinates_sum_sq_le [Nonempty Head]
    {R : ℝ}
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    (∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2) ≤
      2 * ∑ h : B.HeadIndex,
        ((B.cellPhysicalMean (h.1, .minus) -
            B.cellPhysicalMean (B.referenceHead, .minus)) *
          x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
      8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ) *
        x NuisanceCoord.physical ^ 2 := by
  calc
    (∑ h : B.HeadIndex, x (NuisanceCoord.head h) ^ 2) ≤
        ∑ h : B.HeadIndex,
          (2 * ((B.cellPhysicalMean (h.1, .minus) -
              B.cellPhysicalMean (B.referenceHead, .minus)) *
            x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
          8 * R ^ 2 * x NuisanceCoord.physical ^ 2) := by
      apply Finset.sum_le_sum
      intro h _
      exact B.headCoordinate_sq_le hmean x h
    _ = 2 * ∑ h : B.HeadIndex,
          ((B.cellPhysicalMean (h.1, .minus) -
              B.cellPhysicalMean (B.referenceHead, .minus)) *
            x NuisanceCoord.physical + x (NuisanceCoord.head h)) ^ 2 +
        8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ) *
          x NuisanceCoord.physical ^ 2 := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

theorem physicalCoordinate_sq_le_selected [Nonempty Head]
    {sep : ℝ} (hsep : 0 < sep)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (x : B.NuisanceSpace) :
    sep ^ 2 * x NuisanceCoord.physical ^ 2 ≤
      ((B.cellPhysicalMean (B.referenceHead, .plus) -
          B.cellPhysicalMean (B.referenceHead, .minus)) *
        x NuisanceCoord.physical) ^ 2 := by
  let d := B.cellPhysicalMean (B.referenceHead, .plus) -
    B.cellPhysicalMean (B.referenceHead, .minus)
  have hd0 : 0 ≤ d := le_trans (le_of_lt hsep) hphysical
  have hsq : sep ^ 2 ≤ d ^ 2 :=
    (sq_le_sq₀ (le_of_lt hsep) hd0).2 hphysical
  calc
    sep ^ 2 * x NuisanceCoord.physical ^ 2 ≤
        d ^ 2 * x NuisanceCoord.physical ^ 2 :=
      mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = (d * x NuisanceCoord.physical) ^ 2 := by ring

/-- Quantitative reconstruction inequality for the literal nuisance cell
patterns.  The constant is uniform over `n` once `sep` and `R` are fixed. -/
theorem nuisance_norm_sq_le_selected [Nonempty Head]
    {sep R : ℝ} (hsep : 0 < sep)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    sep ^ 2 * ‖x‖ ^ 2 ≤
      B.nuisanceGeometryConstant sep R *
        B.nuisanceSelectedSquare x := by
  let xr := x NuisanceCoord.physical
  let p := (B.cellPhysicalMean (B.referenceHead, .plus) -
      B.cellPhysicalMean (B.referenceHead, .minus)) * xr
  let qs : ℝ := ∑ h : B.HeadIndex,
    ((B.cellPhysicalMean (h.1, .minus) -
        B.cellPhysicalMean (B.referenceHead, .minus)) * xr +
      x (NuisanceCoord.head h)) ^ 2
  let A : ℝ := 1 +
    8 * R ^ 2 * (Fintype.card B.HeadIndex : ℝ)
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hqs : 0 ≤ qs := by
    exact Finset.sum_nonneg fun h _ => sq_nonneg _
  have hp : 0 ≤ p ^ 2 := sq_nonneg p
  have hhead := B.headCoordinates_sum_sq_le hmean x
  have hnorm : ‖x‖ ^ 2 ≤ 2 * qs + A * xr ^ 2 := by
    rw [B.nuisance_norm_sq_coordinates]
    dsimp only [qs, A, xr] at hhead ⊢
    linarith
  have hphys : sep ^ 2 * xr ^ 2 ≤ p ^ 2 := by
    simpa only [xr, p] using
      B.physicalCoordinate_sq_le_selected hsep hphysical x
  have hfirst : sep ^ 2 * ‖x‖ ^ 2 ≤
      2 * sep ^ 2 * qs + A * p ^ 2 := by
    calc
      sep ^ 2 * ‖x‖ ^ 2 ≤
          sep ^ 2 * (2 * qs + A * xr ^ 2) :=
        mul_le_mul_of_nonneg_left hnorm (sq_nonneg sep)
      _ = 2 * sep ^ 2 * qs + A * (sep ^ 2 * xr ^ 2) := by ring
      _ ≤ 2 * sep ^ 2 * qs + A * p ^ 2 :=
        add_le_add_right (mul_le_mul_of_nonneg_left hphys hA) _
  have hsecond : 2 * sep ^ 2 * qs + A * p ^ 2 ≤
      (2 * sep ^ 2 + A) * (p ^ 2 + qs) := by
    nlinarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sq_nonneg sep)) hp, mul_nonneg hA hqs]
  rw [B.nuisanceSelectedSquare_eq]
  change sep ^ 2 * ‖x‖ ^ 2 ≤
    B.nuisanceGeometryConstant sep R * (p ^ 2 + qs)
  have hconstant : B.nuisanceGeometryConstant sep R =
      2 * sep ^ 2 + A := by
    simp only [nuisanceGeometryConstant, A]
    ring
  rw [hconstant]
  exact hfirst.trans hsecond

/-- Explicit positive constant for the uniform baseline nuisance gap. -/
def uniformNuisanceGap (lambda sep R : ℝ) : ℝ :=
  lambda ^ 2 * sep ^ 2 /
    (2 * B.nuisanceGeometryConstant sep R)

theorem uniformNuisanceGap_pos
    {lambda sep R : ℝ} (hlambda : 0 < lambda) (hsep : 0 < sep) :
    0 < B.uniformNuisanceGap lambda sep R := by
  exact div_pos (mul_pos (sq_pos_of_pos hlambda) (sq_pos_of_pos hsep))
    (mul_pos (by norm_num) (B.nuisanceGeometryConstant_pos sep R))

/-- Uniform finite-`n` baseline covariance bound.  In contrast with
`nuisanceBaselineGap`, this gap depends only on the three displayed common
geometric constants, not on a separately chosen inverse at the current `n`. -/
theorem nuisanceFineBaseline_uniform_gap [Nonempty Head]
    {lambda sep R : ℝ} (hlambda : 0 < lambda)
    (hsep : 0 < sep)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    B.uniformNuisanceGap lambda sep R * ‖x‖ ^ 2 ≤
      B.nuisanceFineBaseline.covarianceForm x := by
  have hgeom := B.nuisance_norm_sq_le_selected
    hsep hphysical hmean x
  have hcoarse := B.nuisanceCoarseBaseline_covariance_ge_selected
    (le_of_lt hlambda) hweight x
  have hC : 0 < B.nuisanceGeometryConstant sep R :=
    B.nuisanceGeometryConstant_pos sep R
  have hscale : 0 ≤ lambda ^ 2 /
      (2 * B.nuisanceGeometryConstant sep R) := by positivity
  calc
    B.uniformNuisanceGap lambda sep R * ‖x‖ ^ 2 =
        (lambda ^ 2 /
          (2 * B.nuisanceGeometryConstant sep R)) *
            (sep ^ 2 * ‖x‖ ^ 2) := by
      unfold uniformNuisanceGap
      field_simp [ne_of_gt hC]
    _ ≤ (lambda ^ 2 /
          (2 * B.nuisanceGeometryConstant sep R)) *
            (B.nuisanceGeometryConstant sep R *
              B.nuisanceSelectedSquare x) :=
      mul_le_mul_of_nonneg_left hgeom hscale
    _ = (lambda ^ 2 / 2) * B.nuisanceSelectedSquare x := by
      field_simp [ne_of_gt hC]
    _ ≤ B.nuisanceCoarseBaseline.covarianceForm x := hcoarse
    _ ≤ B.nuisanceFineBaseline.covarianceForm x :=
      B.nuisanceCoarseCertificate.coarse_covarianceForm_le_fine x

/-- Operator form of the same baseline bound. -/
theorem nuisanceCovarianceOperator_zero_uniform_gap [Nonempty Head]
    {lambda sep R : ℝ} (hlambda : 0 < lambda)
    (hsep : 0 < sep)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (hphysical : sep ≤
      B.cellPhysicalMean (B.referenceHead, .plus) -
        B.cellPhysicalMean (B.referenceHead, .minus))
    (hmean : ∀ c : Cell Head, |B.cellPhysicalMean c| ≤ R)
    (x : B.NuisanceSpace) :
    B.uniformNuisanceGap lambda sep R * ‖x‖ ^ 2 ≤
      inner ℝ x (B.nuisanceCovarianceOperator 0 x) := by
  rw [B.nuisanceCovarianceOperator_quadratic, B.nuisanceFineAt_zero]
  exact B.nuisanceFineBaseline_uniform_gap hlambda hsep
    hweight hphysical hmean x

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
