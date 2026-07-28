import Erdos390.Full.ContinuumSharpArithmeticTransfer
import Erdos390.Full.FiniteRawLowDiagonal

/-!
# Ordinary low-row bounds for the continuum cell compression

The product estimate `|K(s,t)| ≤ C s t` cancels both harmonic variables in
the compressed kernel.  Consequently the entire raw kernel row of a cell is
bounded by its harmonic centre, even when the mesh contains many cells below
a fixed cutoff.  This is the estimate that prevents the growing low harmonic
mass from entering the ordinary inverse.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open DickmanBasic
open PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- A product-kernel bound gives an exact raw continuum kernel-cell bound. -/
theorem abs_normalizedKernelCell_le_center_mul_length
    {C : ℝ}
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (i j : Band) :
    |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t| ≤ C * M.length j := by
    have hconst := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := M.lower j) (b := M.upper j) (C := C)
      (f := fun t : ℝ ↦ covarianceKernelQuotient t s / t) (by
        intro t ht
        have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
          simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using
            uIoc_subset_uIcc ht
        have hsUnit := M.cell_mem_unit hs
        have htUnit := M.cell_mem_unit htcc
        have hs0 : s ≠ 0 := ne_of_gt ((M.lower_pos i).trans_le hs.1)
        have ht0 : t ≠ 0 := ne_of_gt ((M.lower_pos j).trans_le htcc.1)
        change |covarianceKernelQuotient t s / t| ≤ C
        rw [covarianceKernelQuotient_eq_div htUnit hsUnit hs0,
          abs_div, abs_div, abs_of_pos ((M.lower_pos i).trans_le hs.1),
          abs_of_pos ((M.lower_pos j).trans_le htcc.1)]
        calc
          |covarianceKernel t s| / s / t ≤ (C * t * s) / s / t := by
            exact div_le_div_of_nonneg_right
              (div_le_div_of_nonneg_right (hKernel t htUnit s hsUnit)
                ((M.lower_pos i).trans_le hs.1).le)
              ((M.lower_pos j).trans_le htcc.1).le
          _ = C := by field_simp [hs0, ht0])
    rw [Real.norm_eq_abs,
      abs_of_pos (sub_pos.mpr (M.lower_lt_upper j))] at hconst
    simpa only [length] using hconst
  have houter := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i) (C := C * M.length j)
    (f := fun s : ℝ ↦
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) (by
      intro s hs
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using
          uIoc_subset_uIcc hs
      simpa only [Real.norm_eq_abs] using hinner s hscc)
  have hmass : 0 < M.harmonicMass i := M.harmonicMass_pos i
  unfold normalizedKernelCell center
  rw [abs_div, abs_of_pos hmass]
  calc
    |∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t| / M.harmonicMass i ≤
      ((C * M.length j) * M.length i) / M.harmonicMass i := by
        apply div_le_div_of_nonneg_right _ hmass.le
        rw [Real.norm_eq_abs,
          abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] at houter
        simpa only [length] using houter
    _ = C * (M.length i / M.harmonicMass i) * M.length j := by ring

/-- Summing the preceding estimate over all input cells retains only their
total ordinary length, not their total harmonic mass. -/
theorem sum_abs_normalizedKernelCell_le
    {C totalLength : ℝ} (hC : 0 ≤ C)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (hLength : ∑ j : Band, M.length j ≤ totalLength)
    (i : Band) :
    ∑ j : Band, |M.normalizedKernelCell i j| ≤
      C * M.center i * totalLength := by
  calc
    ∑ j : Band, |M.normalizedKernelCell i j| ≤
        ∑ j : Band, C * M.center i * M.length j := by
      exact Finset.sum_le_sum fun j _ ↦
        M.abs_normalizedKernelCell_le_center_mul_length hKernel i j
    _ = (C * M.center i) * ∑ j : Band, M.length j := by
      rw [Finset.mul_sum]
    _ ≤ (C * M.center i) * totalLength :=
      mul_le_mul_of_nonneg_left hLength
        (mul_nonneg hC (M.center_pos i).le)

/-- Harmonic averaging preserves a pointwise modulus from the value
`F(0)=1`; this is the exact diagonal estimate used on every low cell. -/
theorem abs_normalizedDiagonalCell_sub_one_le
    {d : ℝ} (i : Band)
    (hF : ∀ s ∈ Icc (M.lower i) (M.upper i), |F s - 1| ≤ d) :
    |M.normalizedDiagonalCell i - 1| ≤ d := by
  have hab : M.lower i ≤ M.upper i := (M.lower_lt_upper i).le
  have hdiffInt : IntervalIntegrable (fun s : ℝ ↦ (F s - 1) / s)
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact ((continuous_F.sub continuous_const).continuousAt.div
      continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1))).continuousWithinAt
  have hmajorInt : IntervalIntegrable (fun s : ℝ ↦ d * (1 / s))
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact (continuousAt_const.mul (continuousAt_const.div continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1)))).continuousWithinAt
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le hab
    (f := fun s : ℝ ↦ (F s - 1) / s)
    (g := fun s : ℝ ↦ d * (1 / s)) (by
      filter_upwards with s hs
      have hscc : s ∈ Icc (M.lower i) (M.upper i) :=
        ⟨hs.1.le, hs.2⟩
      rw [Real.norm_eq_abs, abs_div,
        abs_of_pos ((M.lower_pos i).trans_le hscc.1)]
      calc
        |F s - 1| / s ≤ d / s :=
          div_le_div_of_nonneg_right (hF s hscc)
            ((M.lower_pos i).trans_le hscc.1).le
        _ = d * (1 / s) := by ring) hmajorInt
  have hmass : 0 < M.harmonicMass i := M.harmonicMass_pos i
  have hnorm' : |∫ s in M.lower i..M.upper i, (F s - 1) / s| ≤
      d * M.harmonicMass i := by
    rw [intervalIntegral.integral_const_mul] at hnorm
    simpa only [Real.norm_eq_abs, harmonicMass] using hnorm
  unfold normalizedDiagonalCell
  have hFInt : IntervalIntegrable (fun s : ℝ ↦ F s / s)
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact (continuous_F.continuousAt.div continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1))).continuousWithinAt
  have hOneInt : IntervalIntegrable (fun s : ℝ ↦ 1 / s)
      volume (M.lower i) (M.upper i) := by
    apply ContinuousOn.intervalIntegrable_of_Icc hab
    intro s hs
    exact (continuousAt_const.div continuousAt_id
      (ne_of_gt ((M.lower_pos i).trans_le hs.1))).continuousWithinAt
  have hid : (∫ s in M.lower i..M.upper i, (F s - 1) / s) =
      (∫ s in M.lower i..M.upper i, F s / s) - M.harmonicMass i := by
    rw [show (fun s : ℝ ↦ (F s - 1) / s) =
        fun s : ℝ ↦ F s / s - 1 / s by
      funext s
      ring]
    rw [intervalIntegral.integral_sub hFInt hOneInt]
    unfold harmonicMass
    rfl
  rw [show (∫ s in M.lower i..M.upper i, F s / s) /
      M.harmonicMass i - 1 =
      ((∫ s in M.lower i..M.upper i, F s / s) -
        M.harmonicMass i) / M.harmonicMass i by
      field_simp [ne_of_gt hmass]]
  rw [← hid, abs_div, abs_of_pos hmass]
  exact (div_le_iff₀ hmass).2 (by
    simpa only [mul_comm] using hnorm')

/-- Final direct low-row estimate for the raw continuum compression. -/
theorem abs_rawContinuum_coordinate_le
    {C totalLength d G : ℝ} (hC : 0 ≤ C)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (hLength : ∑ j : Band, M.length j ≤ totalLength)
    (b : Band → ℝ) (i : Band)
    (hdOne : d < 1)
    (hF : ∀ s ∈ Icc (M.lower i) (M.upper i), |F s - 1| ≤ d)
    (hOutput : |rawOperator M.normalizedDiagonalCell
      M.normalizedKernelCell b i| ≤ G) :
    |b i| ≤
      (G + (C * M.center i * totalLength) * ‖b‖) / (1 - d) := by
  exact FiniteRawLowDiagonal.abs_coordinate_le
    M.normalizedDiagonalCell M.normalizedKernelCell b i
    (M.abs_normalizedDiagonalCell_sub_one_le i hF) hdOne
    (M.sum_abs_normalizedKernelCell_le hC hKernel hLength i) hOutput

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
