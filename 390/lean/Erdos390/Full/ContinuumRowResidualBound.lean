import Erdos390.Full.ContinuumSharpArithmeticTransfer
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# An explicit moving-low bound for the continuum row residual

Harmonic cell centers need not be close pointwise to the coordinate in the
moving low cell.  The correct cancellation is instead
`center * ∫ dt/t = ∫ dt`.  This file exploits that exact identity before
taking absolute values.  Consequently the residual is controlled by the
ordinary modulus of continuity of `F` and of the removable kernel on the
closed physical square, together with the omitted initial tail.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PoissonDickmanWeightedInverse

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

theorem center_mul_harmonicMass (i : Band) :
    M.center i * M.harmonicMass i = M.length i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]

/-- Exact coverage information for a finite mesh of the truncated physical
interval `[base,1]`.  It is purely interval combinatorics; no covariance
gap, inverse, or residual estimate is stored here. -/
structure TailPartitionCertificate where
  base : ℝ
  base_nonneg : 0 ≤ base
  base_le_one : base ≤ 1
  totalLength : ∑ j, M.length j = 1 - base
  kernelIntegral_split : ∀ s,
    (∑ j, ∫ t in M.lower j..M.upper j,
      covarianceKernelQuotient t s) =
      ∫ t in base..1, covarianceKernelQuotient t s
  kernelDoubleIntegral_split : ∀ i,
    (∑ j, ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s) =
      ∫ s in M.lower i..M.upper i,
        ∫ t in base..1, covarianceKernelQuotient t s

/-- Harmonic and ordinary cell averages of a continuous function differ
only by its oscillation on that cell.  This remains uniform when the lower
endpoint tends to zero. -/
theorem abs_center_mul_integral_div_sub_integral_le
    (f : ℝ → ℝ) (hf : Continuous f) (i : Band)
    {rho : ℝ}
    (hosc : ∀ t ∈ Icc (M.lower i) (M.upper i),
      |f t - f (M.lower i)| ≤ rho) :
    |M.center i * (∫ t in M.lower i..M.upper i, f t / t) -
        ∫ t in M.lower i..M.upper i, f t| ≤
      2 * rho * M.length i := by
  let a := M.lower i
  let b := M.upper i
  let c := f a
  have ha : 0 < a := M.lower_pos i
  have hab : a ≤ b := le_of_lt (M.lower_lt_upper i)
  have hba : 0 ≤ b - a := sub_nonneg.mpr hab
  have hdivInt : IntervalIntegrable (fun t : ℝ => f t / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact hf.continuousAt.div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  have hcdivInt : IntervalIntegrable (fun t : ℝ => c * (1 / t)) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    simpa only [div_eq_mul_inv, one_mul] using
      (continuousAt_const.div continuousAt_id
        (ne_of_gt (ha.trans_le ht.1))).continuousWithinAt
  have hdiffDivInt : IntervalIntegrable
      (fun t : ℝ => (f t - c) / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact (hf.continuousAt.sub continuousAt_const).div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  have hmajorInt : IntervalIntegrable (fun t : ℝ => rho / t) volume a b := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro t ht
    exact continuousAt_const.div continuousAt_id
      (ne_of_gt (ha.trans_le ht.1)) |>.continuousWithinAt
  have hweighted :
      |∫ t in a..b, (f t - c) / t| ≤ rho * M.harmonicMass i := by
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ t in a..b, (f t - c) / t‖ ≤
          ∫ t in a..b, rho / t := by
        apply intervalIntegral.norm_integral_le_of_norm_le hab _ hmajorInt
        filter_upwards with t ht
        have htcc : t ∈ Icc a b := ⟨ht.1.le, ht.2⟩
        have htpos : 0 < t := ha.trans_le htcc.1
        rw [Real.norm_eq_abs, abs_div, abs_of_pos htpos]
        exact div_le_div_of_nonneg_right (hosc t htcc) htpos.le
      _ = rho * M.harmonicMass i := by
        unfold harmonicMass
        rw [show (fun t : ℝ => rho / t) =
            fun t : ℝ => rho * (1 / t) by
          funext t
          ring, intervalIntegral.integral_const_mul]
  have hordinary :
      |∫ t in a..b, f t - c| ≤ rho * M.length i := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := rho) (f := fun t : ℝ => f t - c)
      (fun t ht => by
        have htcc : t ∈ Icc a b := by
          have ht' : t ∈ uIcc a b := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le hab] using ht'
        simpa only [Real.norm_eq_abs] using hosc t htcc)
    rw [Real.norm_eq_abs, abs_of_nonneg hba] at hnorm
    exact hnorm
  have hweightedDecomp :
      (∫ t in a..b, (f t - c) / t) =
        (∫ t in a..b, f t / t) - c * M.harmonicMass i := by
    rw [show (fun t : ℝ => (f t - c) / t) =
        fun t : ℝ => f t / t - c * (1 / t) by
      funext t
      ring]
    rw [intervalIntegral.integral_sub hdivInt hcdivInt,
      intervalIntegral.integral_const_mul]
    rfl
  have hfInt : IntervalIntegrable f volume a b := hf.intervalIntegrable _ _
  have hcInt : IntervalIntegrable (fun _t : ℝ => c) volume a b :=
    continuous_const.intervalIntegrable _ _
  have hordinaryDecomp :
      (∫ t in a..b, f t - c) =
        (∫ t in a..b, f t) - c * M.length i := by
    rw [intervalIntegral.integral_sub hfInt hcInt]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    unfold length
    ring
  have hidentity :
      M.center i * (∫ t in a..b, f t / t) -
          (∫ t in a..b, f t) =
        M.center i * (∫ t in a..b, (f t - c) / t) -
          (∫ t in a..b, f t - c) := by
    have hw : (∫ t in a..b, f t / t) =
        (∫ t in a..b, (f t - c) / t) + c * M.harmonicMass i := by
      linarith [hweightedDecomp]
    have ho : (∫ t in a..b, f t) =
        (∫ t in a..b, f t - c) + c * M.length i := by
      linarith [hordinaryDecomp]
    rw [hw, ho]
    calc
      M.center i *
            ((∫ t in a..b, (f t - c) / t) +
              c * M.harmonicMass i) -
          ((∫ t in a..b, f t - c) + c * M.length i) =
        (M.center i * (∫ t in a..b, (f t - c) / t) -
          (∫ t in a..b, f t - c)) +
          c * (M.center i * M.harmonicMass i - M.length i) := by ring
      _ = _ := by rw [M.center_mul_harmonicMass]; ring
  rw [hidentity]
  calc
    |M.center i * (∫ t in a..b, (f t - c) / t) -
        (∫ t in a..b, f t - c)| ≤
      |M.center i * (∫ t in a..b, (f t - c) / t)| +
        |∫ t in a..b, f t - c| := abs_sub _ _
    _ = M.center i * |∫ t in a..b, (f t - c) / t| +
        |∫ t in a..b, f t - c| := by
      rw [abs_mul, abs_of_pos (M.center_pos i)]
    _ ≤ M.center i * (rho * M.harmonicMass i) +
        rho * M.length i :=
      add_le_add
        (mul_le_mul_of_nonneg_left hweighted (M.center_pos i).le)
        hordinary
    _ = 2 * rho * M.length i := by
      rw [show M.center i * (rho * M.harmonicMass i) =
          rho * M.length i by
        rw [← mul_assoc, mul_comm (M.center i) rho, mul_assoc,
          M.center_mul_harmonicMass]]
      ring

private theorem continuous_innerKernel (a b : ℝ) :
    Continuous (fun s : ℝ =>
      ∫ t in a..b, covarianceKernelQuotient t s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := a) (b₀ := b)
  exact continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)

private theorem continuous_innerKernelDiv (j : Band) :
    Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) := by
  let d : ℝ → ℝ := fun t => max t (M.lower j / 2)
  have hdcont : Continuous d :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower j / 2)
  have hd0 (t : ℝ) : d t ≠ 0 := by
    have hdpos : 0 < d t := by
      dsimp only [d]
      exact (half_pos (M.lower_pos j)).trans_le (le_max_right _ _)
    exact ne_of_gt hdpos
  have hsurrogate : Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / d t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := M.lower j) (b₀ := M.upper j)
    exact (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).div
        (hdcont.comp continuous_snd) (fun z => hd0 z.2)
  have heq : (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) =
      (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / d t) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    have hhalf : M.lower j / 2 ≤ t := by
      linarith [M.lower_pos j, htcc.1]
    change covarianceKernelQuotient t s / t =
      covarianceKernelQuotient t s / d t
    rw [show d t = t by simp [d, max_eq_left hhalf]]
  rw [heq]
  exact hsurrogate

/-- Input-cell contribution to the physical-null residual after the exact
harmonic-center cancellation is exposed. -/
def inputCellResidual (i j : Band) : ℝ :=
  ∫ s in M.lower i..M.upper i,
    (M.center j *
      (∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) -
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s)

theorem abs_inputCellResidual_le
    (i j : Band) {rhoKernel : ℝ}
    (hosc : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (M.lower j) (M.upper j),
        |covarianceKernelQuotient t s -
          covarianceKernelQuotient (M.lower j) s| ≤ rhoKernel) :
    |M.inputCellResidual i j| ≤
      (2 * rhoKernel * M.length j) * M.length i := by
  unfold inputCellResidual
  have hpoint (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |M.center j *
          (∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t) -
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s| ≤
        2 * rhoKernel * M.length j := by
    apply M.abs_center_mul_integral_div_sub_integral_le
      (fun t => covarianceKernelQuotient t s)
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)) j
    intro t ht
    exact hosc s (M.cell_mem_unit hs) t ht
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i)
    (C := 2 * rhoKernel * M.length j)
    (f := fun s : ℝ =>
      M.center j *
          (∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t) -
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s)
    (fun s hs => by
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        have hs' : s ∈ uIcc (M.lower i) (M.upper i) :=
          uIoc_subset_uIcc hs
        simpa only [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs'
      simpa only [Real.norm_eq_abs] using hpoint s hscc)
  simpa only [Real.norm_eq_abs, length,
    abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] using hnorm

/-- Omitted initial kernel tail in one output cell. -/
def kernelTailResidual (base : ℝ) (i : Band) : ℝ :=
  ∫ s in M.lower i..M.upper i,
    ∫ t in (0 : ℝ)..base, covarianceKernelQuotient t s

theorem abs_kernelTailResidual_le
    (i : Band) {base C : ℝ}
    (hbase : 0 ≤ base) (hbaseOne : base ≤ 1)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C) :
    |M.kernelTailResidual base i| ≤
      (C * base) * M.length i := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |∫ t in (0 : ℝ)..base, covarianceKernelQuotient t s| ≤
        C * base := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := base) (C := C)
      (f := fun t : ℝ => covarianceKernelQuotient t s)
      (fun t ht => by
        have htcc : t ∈ Icc (0 : ℝ) base := by
          have ht' : t ∈ uIcc (0 : ℝ) base := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le hbase] using ht'
        rw [Real.norm_eq_abs]
        exact hKernel s (M.cell_mem_unit hs) t
          ⟨htcc.1, htcc.2.trans hbaseOne⟩)
    simpa only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hbase] using hnorm
  unfold kernelTailResidual
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i) (C := C * base)
    (f := fun s : ℝ =>
      ∫ t in (0 : ℝ)..base, covarianceKernelQuotient t s)
    (fun s hs => by
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        have hs' : s ∈ uIcc (M.lower i) (M.upper i) :=
          uIoc_subset_uIcc hs
        simpa only [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs'
      simpa only [Real.norm_eq_abs] using hinner s hscc)
  simpa only [Real.norm_eq_abs, length,
    abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] using hnorm

theorem inputCellResidual_eq (i j : Band) :
    M.inputCellResidual i j =
      M.center j *
          (∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t) -
        ∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s := by
  unfold inputCellResidual
  have hleft : IntervalIntegrable (fun s : ℝ =>
      M.center j *
        (∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t)) volume
      (M.lower i) (M.upper i) :=
    (continuous_const.mul (M.continuous_innerKernelDiv j)).intervalIntegrable _ _
  have hright : IntervalIntegrable (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_innerKernel (M.lower j) (M.upper j)).intervalIntegrable _ _
  rw [intervalIntegral.integral_sub hleft hright,
    intervalIntegral.integral_const_mul]

theorem length_mul_normalizedDiagonalCell (i : Band) :
    M.length i * M.normalizedDiagonalCell i =
      M.center i *
        (∫ s in M.lower i..M.upper i, F s / s) := by
  unfold normalizedDiagonalCell
  rw [← M.center_mul_harmonicMass i]
  field_simp [ne_of_gt (M.harmonicMass_pos i)]

theorem length_mul_normalizedKernel_ratio (i j : Band) :
    M.length i *
        (M.normalizedKernelCell i j * (M.center j / M.center i)) =
      M.center j *
        (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t) := by
  unfold normalizedKernelCell
  rw [← M.center_mul_harmonicMass i]
  field_simp [ne_of_gt (M.harmonicMass_pos i),
    ne_of_gt (M.center_pos i)]

/-- Integrated removable row-sum identity after truncating the input
interval at `P.base`. -/
theorem diagonal_add_truncatedKernel_eq_neg_tail
    (P : M.TailPartitionCertificate) (i : Band) :
    (∫ s in M.lower i..M.upper i, F s) +
        (∫ s in M.lower i..M.upper i,
          ∫ t in P.base..1, covarianceKernelQuotient t s) =
      -M.kernelTailResidual P.base i := by
  have hpoint (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      F s + (∫ t in P.base..1, covarianceKernelQuotient t s) =
        -(∫ t in (0 : ℝ)..P.base,
          covarianceKernelQuotient t s) := by
    have hrow := weightedKernel_rowSum s (M.cell_mem_unit hs)
    have hleft : IntervalIntegrable
        (fun t : ℝ => covarianceKernelQuotient t s) volume 0 P.base :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hright : IntervalIntegrable
        (fun t : ℝ => covarianceKernelQuotient t s) volume P.base 1 :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
    linarith
  have hFint : IntervalIntegrable F volume (M.lower i) (M.upper i) :=
    continuous_F.intervalIntegrable _ _
  have htruncInt : IntervalIntegrable (fun s : ℝ =>
      ∫ t in P.base..1, covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_innerKernel P.base 1).intervalIntegrable _ _
  unfold kernelTailResidual
  rw [← intervalIntegral.integral_add hFint htruncInt,
    ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs
  have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
    simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs
  exact hpoint s hscc

/-- Exact decomposition of the continuum null-vector defect into one
diagonal oscillation, the input-cell oscillations, and the omitted initial
tail. -/
theorem length_mul_rowResidual_eq
    (P : M.TailPartitionCertificate) (i : Band) :
    M.length i * M.rowResidual i =
      (M.center i *
          (∫ s in M.lower i..M.upper i, F s / s) -
        ∫ s in M.lower i..M.upper i, F s) +
      (∑ j, M.inputCellResidual i j) -
        M.kernelTailResidual P.base i := by
  have hscaled : M.length i * M.rowResidual i =
      M.center i *
          (∫ s in M.lower i..M.upper i, F s / s) +
        ∑ j, M.center j *
          (∫ s in M.lower i..M.upper i,
            ∫ t in M.lower j..M.upper j,
              covarianceKernelQuotient t s / t) := by
    unfold rowResidual
    rw [mul_add, Finset.mul_sum, M.length_mul_normalizedDiagonalCell]
    apply congrArg
      (fun x : ℝ =>
        M.center i *
          (∫ s in M.lower i..M.upper i, F s / s) + x)
    apply Finset.sum_congr rfl
    intro j hj
    exact M.length_mul_normalizedKernel_ratio i j
  have hinput : (∑ j, M.inputCellResidual i j) =
      (∑ j, M.center j *
        (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t)) -
      (∫ s in M.lower i..M.upper i,
        ∫ t in P.base..1, covarianceKernelQuotient t s) := by
    simp_rw [M.inputCellResidual_eq i]
    rw [Finset.sum_sub_distrib, P.kernelDoubleIntegral_split]
  have hrow := M.diagonal_add_truncatedKernel_eq_neg_tail P i
  rw [hscaled, hinput]
  linarith

/-- Quantitative moving-low residual bound.  The low endpoint enters only
through the omitted-tail term `C * P.base`; no factor `1 / center` occurs. -/
theorem abs_rowResidual_le
    (P : M.TailPartitionCertificate)
    {rhoF rhoKernel C : ℝ}
    (hFosc : ∀ j, ∀ s ∈ Icc (M.lower j) (M.upper j),
      |F s - F (M.lower j)| ≤ rhoF)
    (hKernelOsc : ∀ j, ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (M.lower j) (M.upper j),
        |covarianceKernelQuotient t s -
          covarianceKernelQuotient (M.lower j) s| ≤ rhoKernel)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C)
    (i : Band) :
    |M.rowResidual i| ≤
      2 * rhoF + 2 * rhoKernel * (1 - P.base) + C * P.base := by
  have hdiag :
      |M.center i *
          (∫ s in M.lower i..M.upper i, F s / s) -
        ∫ s in M.lower i..M.upper i, F s| ≤
        (2 * rhoF) * M.length i := by
    simpa only [mul_assoc] using
      (M.abs_center_mul_integral_div_sub_integral_le
        F continuous_F i (hFosc i))
  have hinputEach (j : Band) :
      |M.inputCellResidual i j| ≤
        (2 * rhoKernel * M.length j) * M.length i :=
    M.abs_inputCellResidual_le i j (hKernelOsc j)
  have hinput :
      |∑ j, M.inputCellResidual i j| ≤
        (2 * rhoKernel * (1 - P.base)) * M.length i := by
    calc
      |∑ j, M.inputCellResidual i j| ≤
          ∑ j, |M.inputCellResidual i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j,
          (2 * rhoKernel * M.length j) * M.length i := by
        apply Finset.sum_le_sum
        intro j hj
        exact hinputEach j
      _ = (2 * rhoKernel * (∑ j, M.length j)) * M.length i := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = (2 * rhoKernel * (1 - P.base)) * M.length i := by
        rw [P.totalLength]
  have htail : |M.kernelTailResidual P.base i| ≤
      (C * P.base) * M.length i :=
    M.abs_kernelTailResidual_le i P.base_nonneg P.base_le_one hKernel
  have hscaled :
      |M.length i * M.rowResidual i| ≤
        ((2 * rhoF) + (2 * rhoKernel * (1 - P.base)) +
          C * P.base) * M.length i := by
    rw [M.length_mul_rowResidual_eq P i]
    calc
      |(M.center i *
            (∫ s in M.lower i..M.upper i, F s / s) -
          ∫ s in M.lower i..M.upper i, F s) +
          (∑ j, M.inputCellResidual i j) -
          M.kernelTailResidual P.base i| ≤
        |M.center i *
            (∫ s in M.lower i..M.upper i, F s / s) -
          ∫ s in M.lower i..M.upper i, F s| +
        |∑ j, M.inputCellResidual i j| +
        |M.kernelTailResidual P.base i| := by
          calc
            _ ≤
                |(M.center i *
                    (∫ s in M.lower i..M.upper i, F s / s) -
                  ∫ s in M.lower i..M.upper i, F s) +
                  (∑ j, M.inputCellResidual i j)| +
                |M.kernelTailResidual P.base i| := abs_sub _ _
            _ ≤ _ := by
              have hadd := abs_add_le
                (M.center i *
                    (∫ s in M.lower i..M.upper i, F s / s) -
                  ∫ s in M.lower i..M.upper i, F s)
                (∑ j, M.inputCellResidual i j)
              linarith
      _ ≤ (2 * rhoF) * M.length i +
          (2 * rhoKernel * (1 - P.base)) * M.length i +
          (C * P.base) * M.length i :=
        add_le_add (add_le_add hdiag hinput) htail
      _ = ((2 * rhoF) + (2 * rhoKernel * (1 - P.base)) +
          C * P.base) * M.length i := by ring
  have hlength : 0 < M.length i := M.length_pos i
  apply le_of_mul_le_mul_left _ hlength
  calc
    M.length i * |M.rowResidual i| =
        |M.length i * M.rowResidual i| := by
      rw [abs_mul, abs_of_pos hlength]
    _ ≤
        ((2 * rhoF) + (2 * rhoKernel * (1 - P.base)) +
          C * P.base) * M.length i := hscaled
    _ = M.length i *
        (2 * rhoF + 2 * rhoKernel * (1 - P.base) + C * P.base) := by ring

/-- Joint modulus of continuity in exactly the orientation used by the
cell residual.  Compactness is invoked on the closed physical interval and
square, so the constants do not depend on the moving low endpoint. -/
theorem exists_uniform_cell_oscillation_modulus
    {rhoF rhoKernel : ℝ} (hrhoF : 0 < rhoF)
    (hrhoKernel : 0 < rhoKernel) :
    ∃ eta : ℝ, 0 < eta ∧
      (∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
        |x - y| < eta → |F x - F y| < rhoF) ∧
      (∀ s ∈ Icc (0 : ℝ) 1,
        ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
          |t - u| < eta →
            |covarianceKernelQuotient t s -
              covarianceKernelQuotient u s| < rhoKernel) := by
  have hFu : UniformContinuousOn F (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous continuous_F.continuousOn
  obtain ⟨etaF, hetaF, hFmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hFu rhoF hrhoF
  let square : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hKu : UniformContinuousOn
      (Function.uncurry covarianceKernelQuotient) square :=
    (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
      continuous_uncurry_covarianceKernelQuotient.continuousOn
  obtain ⟨etaK, hetaK, hKmod⟩ :=
    Metric.uniformContinuousOn_iff.mp hKu rhoKernel hrhoKernel
  refine ⟨min etaF etaK, lt_min hetaF hetaK, ?_, ?_⟩
  · intro x hx y hy hxy
    rw [← Real.dist_eq] at hxy ⊢
    exact hFmod x hx y hy (hxy.trans_le (min_le_left _ _))
  · intro s hs t ht u hu htu
    have hdist : dist (t, s) (u, s) < etaK := by
      simpa only [Prod.dist_eq, dist_self, Real.dist_eq,
        max_eq_left (abs_nonneg (t - u))] using
        htu.trans_le (min_le_right etaF etaK)
    have h := hKmod (t, s) ⟨ht, hs⟩ (u, s) ⟨hu, hs⟩ hdist
    simpa only [Function.uncurry_apply_pair, Real.dist_eq] using h

/-- For every target error one may choose the mesh diameter and initial
tail cutoff first; every certified mesh satisfying those elementary
geometric inequalities then has a uniformly small row residual. -/
theorem exists_rowResidual_uniform_tolerances
    {target : ℝ} (htarget : 0 < target) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ beta : ℝ, 0 < beta ∧
      ∀ P : M.TailPartitionCertificate,
        P.base < beta → (∀ j, M.length j < eta) →
          ∀ i, |M.rowResidual i| < target := by
  obtain ⟨C, hC, hKernel⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernelQuotient_bound
  have hrho : 0 < target / 8 := div_pos htarget (by norm_num)
  obtain ⟨eta, heta, hFmod, hKmod⟩ :=
    exists_uniform_cell_oscillation_modulus hrho hrho
  let beta := target / (2 * (C + 1))
  have hCplus : 0 < C + 1 := by linarith
  have hbeta : 0 < beta := div_pos htarget (mul_pos (by norm_num) hCplus)
  refine ⟨eta, heta, beta, hbeta, ?_⟩
  intro P hbase hdiam i
  have hFosc (j : Band) (s : ℝ)
      (hs : s ∈ Icc (M.lower j) (M.upper j)) :
      |F s - F (M.lower j)| ≤ target / 8 := by
    apply (hFmod s (M.cell_mem_unit hs) (M.lower j)
      ⟨(M.lower_pos j).le, (M.lower_lt_upper j).le.trans (M.upper_le_one j)⟩ ?_).le
    have hsupper : s - M.lower j ≤ M.length j := by
      unfold length
      linarith [hs.2]
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    exact hsupper.trans_lt (hdiam j)
  have hKosc (j : Band) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (M.lower j) (M.upper j)) :
      |covarianceKernelQuotient t s -
        covarianceKernelQuotient (M.lower j) s| ≤ target / 8 := by
    apply (hKmod s hs t (M.cell_mem_unit ht) (M.lower j)
      ⟨(M.lower_pos j).le, (M.lower_lt_upper j).le.trans (M.upper_le_one j)⟩ ?_).le
    have htupper : t - M.lower j ≤ M.length j := by
      unfold length
      linarith [ht.2]
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    exact htupper.trans_lt (hdiam j)
  have hraw := M.abs_rowResidual_le P hFosc hKosc
    (fun s hs t ht => hKernel t ht s hs) i
  have htail : C * P.base < target / 2 := by
    have hfirst : C * P.base ≤ (C + 1) * P.base :=
      mul_le_mul_of_nonneg_right (by linarith) P.base_nonneg
    have hsecond : (C + 1) * P.base < (C + 1) * beta :=
      mul_lt_mul_of_pos_left hbase hCplus
    have heq : (C + 1) * beta = target / 2 := by
      unfold beta
      field_simp [ne_of_gt hCplus]
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  have hpart : 1 - P.base ≤ 1 := by linarith [P.base_nonneg]
  have hkernelTerm :
      2 * (target / 8) * (1 - P.base) ≤ target / 4 := by
    have hnonneg : 0 ≤ 2 * (target / 8) := by positivity
    calc
      2 * (target / 8) * (1 - P.base) ≤
          2 * (target / 8) * 1 :=
        mul_le_mul_of_nonneg_left hpart hnonneg
      _ = target / 4 := by ring
  calc
    |M.rowResidual i| ≤
        2 * (target / 8) +
          2 * (target / 8) * (1 - P.base) + C * P.base := hraw
    _ < target := by
      have hdiag : 2 * (target / 8) = target / 4 := by ring
      rw [hdiag]
      linarith

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
