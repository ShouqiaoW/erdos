import Erdos390.Full.ArithmeticGaugeStableInverse
import Erdos390.Full.MovingLowGaugeTransfer

/-!
# Export of the sharp inverse in the paper's weighted band norm

The finite graph argument is naturally written after the diagonal change of
variables `b j = alpha j * q j`.  This file records the change of variables
as an exact linear equivalence between the two arithmetic gauges.  It also
proves that the projected raw row-normalized matrix is conjugate to
`projectedSharpLinearMap`.  Consequently an inverse estimate in the ordinary
supremum norm of `q` is literally the paper estimate
`max_j |b_j| / |alpha_j|` for the unscaled band coefficient `b`.

There is no limiting centre and no continuum gauge in this algebraic export.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.PaperWeightedInverseExport

open ArithmeticGaugeStableInverse
open CompressedArithmeticOperator
open FiniteGraphQuotientInverse
open FiniteGraphStableInverse
open MovingLowGaugeTransfer

variable {Band : Type*} [Fintype Band]

/-- The weights defining the original arithmetic gauge
`sum_j H_j alpha_j b_j = 0`. -/
def rawGaugeWeight (H alpha : Band → ℝ) (j : Band) : ℝ :=
  H j * alpha j

abbrev RawGaugeSpace (H alpha : Band → ℝ) :=
  GaugeSpace (rawGaugeWeight H alpha)

abbrev SharpGaugeSpace (H alpha : Band → ℝ) :=
  GaugeSpace (sharpWeight H alpha)

/-- Exact scaling equivalence between the sharp gauge and the paper's raw
arithmetic gauge. -/
def scaleGaugeLinearEquiv (H alpha : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0) :
    SharpGaugeSpace H alpha ≃ₗ[ℝ] RawGaugeSpace H alpha where
  toFun q := ⟨fun j ↦ alpha j * q.1 j, by
    change ∑ j, rawGaugeWeight H alpha j * (alpha j * q.1 j) = 0
    rw [← q.2]
    apply Finset.sum_congr rfl
    intro j _
    unfold rawGaugeWeight sharpWeight
    ring⟩
  invFun b := ⟨fun j ↦ b.1 j / alpha j, by
    change ∑ j, sharpWeight H alpha j * (b.1 j / alpha j) = 0
    rw [← b.2]
    apply Finset.sum_congr rfl
    intro j _
    unfold rawGaugeWeight sharpWeight
    field_simp [hAlpha j]⟩
  left_inv q := by
    apply Subtype.ext
    funext j
    simp only
    field_simp [hAlpha j]
  right_inv b := by
    apply Subtype.ext
    funext j
    simp only
    field_simp [hAlpha j]
  map_add' q r := by
    apply Subtype.ext
    funext j
    simp only [Submodule.coe_add, Pi.add_apply]
    ring
  map_smul' c q := by
    apply Subtype.ext
    funext j
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply]
    ring

@[simp]
theorem scaleGaugeLinearEquiv_apply
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (q : SharpGaugeSpace H alpha) (j : Band) :
    ((scaleGaugeLinearEquiv H alpha hAlpha q : RawGaugeSpace H alpha) :
      Band → ℝ) j = alpha j * q.1 j := rfl

@[simp]
theorem scaleGaugeLinearEquiv_symm_apply
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) (j : Band) :
    (((scaleGaugeLinearEquiv H alpha hAlpha).symm b :
      SharpGaugeSpace H alpha) : Band → ℝ) j =
        b.1 j / alpha j := rfl

/-- The paper's weighted band norm, expressed through the exact gauge
equivalence. -/
def paperSharpNorm (H alpha : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) : ℝ :=
  ‖(scaleGaugeLinearEquiv H alpha hAlpha).symm b‖

theorem paperSharpNorm_eq_piNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) :
    paperSharpNorm H alpha hAlpha b =
      ‖fun j ↦ b.1 j / alpha j‖ := by
  rfl

/-- The row-normalized matrix before sharp conjugation. -/
def rawOperator (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (b : Band → ℝ) (i : Band) : ℝ :=
  diagonal i * b i + ∑ j, kernel i j * b j

theorem rawOperator_scale_eq
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (alpha q : Band → ℝ) (hAlpha : ∀ i, alpha i ≠ 0)
    (i : Band) :
    rawOperator diagonal kernel (scaleByCenter alpha q) i =
      alpha i * sharpOperator diagonal kernel alpha q i := by
  unfold rawOperator scaleByCenter sharpOperator
  have hsum :
      (∑ j, kernel i j * (alpha j * q j)) =
        alpha i * ∑ j, kernel i j * (alpha j / alpha i) * q j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    field_simp [hAlpha i]
  rw [hsum]
  ring

theorem weightedGaugeProjection_scale_eq
    (H alpha x : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (hTotal : sharpWeightTotal H alpha ≠ 0)
    (i : Band) :
    weightedGaugeProjection H alpha (scaleByCenter alpha x) i =
      alpha i * meanProjection (sharpWeight H alpha) x i := by
  have hconj := congrFun
    (unscale_weightedGaugeProjection_scale_eq H alpha x hAlpha hTotal) i
  unfold unscaleByCenter at hconj
  unfold meanProjection weightedMean weightTotal
  calc
    weightedGaugeProjection H alpha (scaleByCenter alpha x) i =
        alpha i *
          (weightedGaugeProjection H alpha (scaleByCenter alpha x) i /
            alpha i) := by field_simp [hAlpha i]
    _ = alpha i *
        (x i - (∑ k, sharpWeight H alpha k * x k) /
          sharpWeightTotal H alpha) := by rw [hconj]

theorem weightedGaugeProjection_mem_rawGauge
    (H alpha x : Band → ℝ)
    (hTotal : sharpWeightTotal H alpha ≠ 0) :
    ∑ i, rawGaugeWeight H alpha i *
        weightedGaugeProjection H alpha x i = 0 := by
  have hden : (∑ j, H j * alpha j ^ 2) ≠ 0 := by
    simpa only [sharpWeightTotal, sharpWeight] using hTotal
  unfold rawGaugeWeight weightedGaugeProjection sharpWeightTotal sharpWeight
  have hsum :
      (∑ i, H i * alpha i *
        (x i - alpha i *
          ((∑ k, H k * alpha k * x k) /
            ∑ j, H j * alpha j ^ 2))) =
      (∑ i, H i * alpha i * x i) -
        (∑ i, H i * alpha i ^ 2) *
          ((∑ k, H k * alpha k * x k) /
            ∑ j, H j * alpha j ^ 2) := by
    calc
      _ = (∑ i, H i * alpha i * x i) -
          ∑ i, (H i * alpha i ^ 2) *
            ((∑ k, H k * alpha k * x k) /
              ∑ j, H j * alpha j ^ 2) := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [← Finset.sum_mul]
  rw [hsum]
  field_simp [hden]
  ring

lemma rawOperator_add
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (b c : Band → ℝ) :
    rawOperator diagonal kernel (b + c) =
      rawOperator diagonal kernel b + rawOperator diagonal kernel c := by
  funext i
  unfold rawOperator
  simp only [Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

lemma rawOperator_smul
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (c : ℝ) (b : Band → ℝ) :
    rawOperator diagonal kernel (c • b) =
      c • rawOperator diagonal kernel b := by
  funext i
  unfold rawOperator
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ j, kernel i j * (c * b j)) =
        c * ∑ j, kernel i j * b j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum]
  ring

lemma weightedGaugeProjection_add
    (H alpha x y : Band → ℝ) :
    weightedGaugeProjection H alpha (x + y) =
      weightedGaugeProjection H alpha x +
        weightedGaugeProjection H alpha y := by
  funext i
  unfold weightedGaugeProjection
  simp only [Pi.add_apply]
  have hsum :
      (∑ k, H k * alpha k * (x k + y k)) =
        (∑ k, H k * alpha k * x k) +
          ∑ k, H k * alpha k * y k := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring

lemma weightedGaugeProjection_smul
    (H alpha : Band → ℝ) (c : ℝ) (x : Band → ℝ) :
    weightedGaugeProjection H alpha (c • x) =
      c • weightedGaugeProjection H alpha x := by
  funext i
  unfold weightedGaugeProjection
  simp only [Pi.smul_apply, smul_eq_mul]
  have hsum :
      (∑ k, H k * alpha k * (c * x k)) =
        c * ∑ k, H k * alpha k * x k := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsum]
  ring

/-- The projected paper matrix on the original arithmetic gauge. -/
def projectedRawLinearMap
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (H alpha : Band → ℝ)
    (hTotal : sharpWeightTotal H alpha ≠ 0) :
    RawGaugeSpace H alpha →ₗ[ℝ] RawGaugeSpace H alpha where
  toFun b := ⟨weightedGaugeProjection H alpha
      (rawOperator diagonal kernel b.1),
    weightedGaugeProjection_mem_rawGauge H alpha
      (rawOperator diagonal kernel b.1) hTotal⟩
  map_add' b c := by
    apply Subtype.ext
    change weightedGaugeProjection H alpha
        (rawOperator diagonal kernel (b.1 + c.1)) =
      weightedGaugeProjection H alpha (rawOperator diagonal kernel b.1) +
        weightedGaugeProjection H alpha (rawOperator diagonal kernel c.1)
    rw [rawOperator_add, weightedGaugeProjection_add]
  map_smul' c b := by
    apply Subtype.ext
    change weightedGaugeProjection H alpha
        (rawOperator diagonal kernel (c • b.1)) =
      c • weightedGaugeProjection H alpha
        (rawOperator diagonal kernel b.1)
    rw [rawOperator_smul, weightedGaugeProjection_smul]

/-- Exact conjugation of the paper's raw projected matrix by the centre
scaling. -/
theorem scale_projectedSharpLinearMap_eq_projectedRawLinearMap
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (H alpha : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (hTotal : sharpWeightTotal H alpha ≠ 0)
    (q : SharpGaugeSpace H alpha) :
    scaleGaugeLinearEquiv H alpha hAlpha
        (projectedSharpLinearMap diagonal kernel alpha
          (sharpWeight H alpha) hTotal q) =
      projectedRawLinearMap diagonal kernel H alpha hTotal
        (scaleGaugeLinearEquiv H alpha hAlpha q) := by
  apply Subtype.ext
  funext i
  change alpha i * meanProjection (sharpWeight H alpha)
      (sharpOperator diagonal kernel alpha q.1) i =
    weightedGaugeProjection H alpha
      (rawOperator diagonal kernel
        (fun j ↦ alpha j * q.1 j)) i
  have hraw :
      rawOperator diagonal kernel (fun j ↦ alpha j * q.1 j) =
        scaleByCenter alpha (sharpOperator diagonal kernel alpha q.1) := by
    funext k
    exact rawOperator_scale_eq diagonal kernel alpha q.1 hAlpha k
  rw [hraw]
  exact (weightedGaugeProjection_scale_eq H alpha
    (sharpOperator diagonal kernel alpha q.1) hAlpha hTotal i).symm

/-- A sharp-gauge inverse is exactly a weighted inverse for the paper's raw
projected matrix.  Both the equation and the norm estimate are conclusions;
no inverse of the raw matrix is assumed. -/
theorem exists_raw_solution_with_paperSharpNorm_bound
    [Nonempty Band]
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (H alpha : Band → ℝ)
    (hAlpha : ∀ j, alpha j ≠ 0)
    (hTotalPos : 0 < sharpWeightTotal H alpha)
    (actualEquiv : SharpGaugeSpace H alpha ≃L[ℝ]
      SharpGaugeSpace H alpha)
    (hactual : ∀ q, actualEquiv q =
      projectedSharpCLM diagonal kernel alpha (sharpWeight H alpha)
        (ne_of_gt hTotalPos) q)
    {C : ℝ}
    (hinv : ∀ v, ‖actualEquiv.symm v‖ ≤ C * ‖v‖)
    (u : RawGaugeSpace H alpha) :
    ∃ b : RawGaugeSpace H alpha,
      projectedRawLinearMap diagonal kernel H alpha
          (ne_of_gt hTotalPos) b = u ∧
      paperSharpNorm H alpha hAlpha b ≤
        C * paperSharpNorm H alpha hAlpha u := by
  let S := scaleGaugeLinearEquiv H alpha hAlpha
  let uSharp : SharpGaugeSpace H alpha := S.symm u
  let q : SharpGaugeSpace H alpha := actualEquiv.symm uSharp
  let b : RawGaugeSpace H alpha := S q
  refine ⟨b, ?_, ?_⟩
  · rw [← scale_projectedSharpLinearMap_eq_projectedRawLinearMap
      diagonal kernel H alpha hAlpha (ne_of_gt hTotalPos) q]
    have hmap :
        projectedSharpLinearMap diagonal kernel alpha
            (sharpWeight H alpha) (ne_of_gt hTotalPos) q = uSharp := by
      change projectedSharpCLM diagonal kernel alpha
          (sharpWeight H alpha) (ne_of_gt hTotalPos) q = uSharp
      rw [← hactual q]
      exact actualEquiv.apply_symm_apply uSharp
    rw [hmap]
    exact S.apply_symm_apply u
  · change ‖S.symm b‖ ≤ C * ‖S.symm u‖
    rw [show S.symm b = q from S.symm_apply_apply q]
    exact hinv uSharp

/-- Coordinate form of the preceding weighted bound. -/
theorem abs_raw_coordinate_le_paperSharpNorm
    (H alpha : Band → ℝ) (hAlpha : ∀ j, alpha j ≠ 0)
    (b : RawGaugeSpace H alpha) (j : Band) :
    |b.1 j| ≤ |alpha j| * paperSharpNorm H alpha hAlpha b := by
  have hcoord : |b.1 j / alpha j| ≤
      paperSharpNorm H alpha hAlpha b := by
    rw [paperSharpNorm_eq_piNorm]
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (fun k ↦ b.1 k / alpha k) j
  have hrewrite : |b.1 j| = |alpha j| * |b.1 j / alpha j| := by
    rw [abs_div]
    field_simp [abs_ne_zero.mpr (hAlpha j)]
  rw [hrewrite]
  exact mul_le_mul_of_nonneg_left hcoord (abs_nonneg (alpha j))

end Erdos390.Full.PaperWeightedInverseExport
