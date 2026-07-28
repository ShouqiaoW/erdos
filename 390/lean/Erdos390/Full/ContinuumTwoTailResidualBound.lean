import Erdos390.Full.ContinuumRowResidualBound

/-!
# Continuum row residual with both endpoint tails

For the literal arithmetic endpoint mesh the last endpoint is
`log(floor y)/log y`, not exactly `1`.  This file keeps both omitted tails
explicit.  It closes the top-endpoint gap without changing the continuum
operator or pretending that `floor y = y`.
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

/-- Exact coverage of a middle interval `[base, top]`. -/
structure TwoTailPartitionCertificate where
  base : ℝ
  upperEnd : ℝ
  base_nonneg : 0 ≤ base
  base_le_upperEnd : base ≤ upperEnd
  upperEnd_le_one : upperEnd ≤ 1
  totalLength : ∑ j, M.length j = upperEnd - base
  kernelDoubleIntegral_split : ∀ i,
    (∑ j, ∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s) =
      ∫ s in M.lower i..M.upper i,
        ∫ t in base..upperEnd, covarianceKernelQuotient t s

/-- Omitted upper kernel tail in one output cell. -/
def kernelUpperTailResidual (top : ℝ) (i : Band) : ℝ :=
  ∫ s in M.lower i..M.upper i,
    ∫ t in top..1, covarianceKernelQuotient t s

theorem abs_kernelUpperTailResidual_le
    (i : Band) {top C : ℝ}
    (htop : 0 ≤ top) (htopOne : top ≤ 1)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C) :
    |M.kernelUpperTailResidual top i| ≤
      (C * (1 - top)) * M.length i := by
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      |∫ t in top..1, covarianceKernelQuotient t s| ≤
        C * (1 - top) := by
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := top) (b := (1 : ℝ)) (C := C)
      (f := fun t : ℝ => covarianceKernelQuotient t s)
      (fun t ht => by
        have htcc : t ∈ Icc top (1 : ℝ) := by
          have ht' : t ∈ uIcc top (1 : ℝ) := uIoc_subset_uIcc ht
          simpa only [uIcc_of_le htopOne] using ht'
        rw [Real.norm_eq_abs]
        exact hKernel s (M.cell_mem_unit hs) t
          ⟨htop.trans htcc.1, htcc.2⟩)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr htopOne)] using hnorm
  unfold kernelUpperTailResidual
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := M.lower i) (b := M.upper i) (C := C * (1 - top))
    (f := fun s : ℝ =>
      ∫ t in top..1, covarianceKernelQuotient t s)
    (fun s hs => by
      have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
        have hs' : s ∈ uIcc (M.lower i) (M.upper i) :=
          uIoc_subset_uIcc hs
        simpa only [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs'
      simpa only [Real.norm_eq_abs] using hinner s hscc)
  simpa only [Real.norm_eq_abs, length,
    abs_of_pos (sub_pos.mpr (M.lower_lt_upper i))] using hnorm

private theorem continuous_middleKernel (a b : ℝ) :
    Continuous (fun s : ℝ =>
      ∫ t in a..b, covarianceKernelQuotient t s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := a) (b₀ := b)
  exact continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)

theorem diagonal_add_middleKernel_eq_neg_tails
    (P : M.TwoTailPartitionCertificate) (i : Band) :
    (∫ s in M.lower i..M.upper i, F s) +
        (∫ s in M.lower i..M.upper i,
          ∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) =
      -M.kernelTailResidual P.base i -
        M.kernelUpperTailResidual P.upperEnd i := by
  have hpoint (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      F s + (∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) =
        -(∫ t in (0 : ℝ)..P.base, covarianceKernelQuotient t s) -
          (∫ t in P.upperEnd..1, covarianceKernelQuotient t s) := by
    have hrow := weightedKernel_rowSum s (M.cell_mem_unit hs)
    let f : ℝ → ℝ := fun t => covarianceKernelQuotient t s
    have hleft : IntervalIntegrable f volume 0 P.base :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hmid : IntervalIntegrable f volume P.base P.upperEnd :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hzeroTop : IntervalIntegrable f volume 0 P.upperEnd :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have hright : IntervalIntegrable f volume P.upperEnd 1 :=
      (continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
    have haddLeft := intervalIntegral.integral_add_adjacent_intervals hleft hmid
    have haddRight := intervalIntegral.integral_add_adjacent_intervals
      hzeroTop hright
    dsimp only [f] at haddLeft haddRight
    linarith
  have hFint : IntervalIntegrable F volume (M.lower i) (M.upper i) :=
    continuous_F.intervalIntegrable _ _
  have hmidInt : IntervalIntegrable (fun s : ℝ =>
      ∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_middleKernel P.base P.upperEnd).intervalIntegrable _ _
  have hlowInt : IntervalIntegrable (fun s : ℝ =>
      ∫ t in (0 : ℝ)..P.base, covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_middleKernel 0 P.base).intervalIntegrable _ _
  have hnegLowInt : IntervalIntegrable (fun s : ℝ =>
      -(∫ t in (0 : ℝ)..P.base, covarianceKernelQuotient t s)) volume
      (M.lower i) (M.upper i) := hlowInt.neg
  have hhighInt : IntervalIntegrable (fun s : ℝ =>
      ∫ t in P.upperEnd..1, covarianceKernelQuotient t s) volume
      (M.lower i) (M.upper i) :=
    (continuous_middleKernel P.upperEnd 1).intervalIntegrable _ _
  unfold kernelTailResidual kernelUpperTailResidual
  rw [← intervalIntegral.integral_add hFint hmidInt,
    ← intervalIntegral.integral_neg,
    ← intervalIntegral.integral_sub hnegLowInt hhighInt]
  apply intervalIntegral.integral_congr
  intro s hs
  have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
    simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs
  exact hpoint s hscc

/-- Exact two-tail decomposition of the continuum null-vector defect. -/
theorem length_mul_rowResidual_eq_twoTails
    (P : M.TwoTailPartitionCertificate) (i : Band) :
    M.length i * M.rowResidual i =
      (M.center i *
          (∫ s in M.lower i..M.upper i, F s / s) -
        ∫ s in M.lower i..M.upper i, F s) +
      (∑ j, M.inputCellResidual i j) -
        M.kernelTailResidual P.base i -
        M.kernelUpperTailResidual P.upperEnd i := by
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
        M.center i * (∫ s in M.lower i..M.upper i, F s / s) + x)
    apply Finset.sum_congr rfl
    intro j hj
    exact M.length_mul_normalizedKernel_ratio i j
  have hinput : (∑ j, M.inputCellResidual i j) =
      (∑ j, M.center j *
        (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            covarianceKernelQuotient t s / t)) -
      (∫ s in M.lower i..M.upper i,
        ∫ t in P.base..P.upperEnd, covarianceKernelQuotient t s) := by
    simp_rw [M.inputCellResidual_eq i]
    rw [Finset.sum_sub_distrib, P.kernelDoubleIntegral_split]
  have hrow := M.diagonal_add_middleKernel_eq_neg_tails P i
  rw [hscaled, hinput]
  linarith

/-- Quantitative two-tail residual bound. -/
theorem abs_rowResidual_le_twoTails
    (P : M.TwoTailPartitionCertificate)
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
      2 * rhoF + 2 * rhoKernel * (P.upperEnd - P.base) +
        C * P.base + C * (1 - P.upperEnd) := by
  have hdiag := M.abs_center_mul_integral_div_sub_integral_le
    F continuous_F i (hFosc i)
  have hinputEach (j : Band) :=
    M.abs_inputCellResidual_le i j (hKernelOsc j)
  have hinput : |∑ j, M.inputCellResidual i j| ≤
      (2 * rhoKernel * (P.upperEnd - P.base)) * M.length i := by
    calc
      |∑ j, M.inputCellResidual i j| ≤
          ∑ j, |M.inputCellResidual i j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j, (2 * rhoKernel * M.length j) * M.length i := by
        apply Finset.sum_le_sum
        intro j hj
        exact hinputEach j
      _ = (2 * rhoKernel * (∑ j, M.length j)) * M.length i := by
        rw [Finset.mul_sum, Finset.sum_mul]
      _ = (2 * rhoKernel * (P.upperEnd - P.base)) * M.length i := by
        rw [P.totalLength]
  have hlow := M.abs_kernelTailResidual_le i P.base_nonneg
    (P.base_le_upperEnd.trans P.upperEnd_le_one) hKernel
  have hhigh := M.abs_kernelUpperTailResidual_le i
    (P.base_nonneg.trans P.base_le_upperEnd) P.upperEnd_le_one hKernel
  have hscaled : |M.length i * M.rowResidual i| ≤
      (2 * rhoF + 2 * rhoKernel * (P.upperEnd - P.base) +
        C * P.base + C * (1 - P.upperEnd)) * M.length i := by
    rw [M.length_mul_rowResidual_eq_twoTails P i]
    calc
      |_ + (∑ j, M.inputCellResidual i j) -
          M.kernelTailResidual P.base i -
          M.kernelUpperTailResidual P.upperEnd i| ≤
        |M.center i * (∫ s in M.lower i..M.upper i, F s / s) -
            ∫ s in M.lower i..M.upper i, F s| +
          |∑ j, M.inputCellResidual i j| +
          |M.kernelTailResidual P.base i| +
          |M.kernelUpperTailResidual P.upperEnd i| := by
        calc
          |_ - M.kernelUpperTailResidual P.upperEnd i| ≤
              |_ - M.kernelTailResidual P.base i| +
                |M.kernelUpperTailResidual P.upperEnd i| := abs_sub _ _
          _ ≤ (|_ + (∑ j, M.inputCellResidual i j)| +
                |M.kernelTailResidual P.base i|) +
                |M.kernelUpperTailResidual P.upperEnd i| := by
            gcongr
            exact abs_sub _ _
          _ ≤ _ := by
            gcongr
            exact abs_add_le _ _
      _ ≤ (2 * rhoF * M.length i) +
          ((2 * rhoKernel * (P.upperEnd - P.base)) * M.length i) +
          ((C * P.base) * M.length i) +
          ((C * (1 - P.upperEnd)) * M.length i) := by
        gcongr
      _ = _ := by ring
  have hlength : 0 < M.length i := M.length_pos i
  apply le_of_mul_le_mul_left _ hlength
  calc
    M.length i * |M.rowResidual i| =
        |M.length i * M.rowResidual i| := by
      rw [abs_mul, abs_of_pos hlength]
    _ ≤ _ := hscaled
    _ = M.length i *
        (2 * rhoF + 2 * rhoKernel * (P.upperEnd - P.base) +
          C * P.base + C * (1 - P.upperEnd)) := by ring

/-- Mesh diameter and both tail widths can be selected before the actual
endpoint mesh.  Every certified mesh satisfying them has uniformly small
row residual. -/
theorem exists_rowResidual_uniform_twoTail_tolerances
    {target : ℝ} (htarget : 0 < target) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ beta : ℝ, 0 < beta ∧
      ∀ P : M.TwoTailPartitionCertificate,
        P.base < beta → 1 - P.upperEnd < beta →
          (∀ j, M.length j < eta) →
            ∀ i, |M.rowResidual i| < target := by
  obtain ⟨C, hC, hKernel⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernelQuotient_bound
  have hrho : 0 < target / 10 := div_pos htarget (by norm_num)
  obtain ⟨eta, heta, hFmod, hKmod⟩ :=
    exists_uniform_cell_oscillation_modulus hrho hrho
  let beta := target / (5 * (C + 1))
  have hCplus : 0 < C + 1 := by linarith
  have hbeta : 0 < beta := div_pos htarget (mul_pos (by norm_num) hCplus)
  refine ⟨eta, heta, beta, hbeta, ?_⟩
  intro P hbase htop hdiam i
  have hFosc (j : Band) (s : ℝ)
      (hs : s ∈ Icc (M.lower j) (M.upper j)) :
      |F s - F (M.lower j)| ≤ target / 10 := by
    apply (hFmod s (M.cell_mem_unit hs) (M.lower j)
      ⟨(M.lower_pos j).le,
        (M.lower_lt_upper j).le.trans (M.upper_le_one j)⟩ ?_).le
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have : s - M.lower j ≤ M.length j := by
      unfold length
      linarith [hs.2]
    exact this.trans_lt (hdiam j)
  have hKosc (j : Band) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (M.lower j) (M.upper j)) :
      |covarianceKernelQuotient t s -
        covarianceKernelQuotient (M.lower j) s| ≤ target / 10 := by
    apply (hKmod s hs t (M.cell_mem_unit ht) (M.lower j)
      ⟨(M.lower_pos j).le,
        (M.lower_lt_upper j).le.trans (M.upper_le_one j)⟩ ?_).le
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have : t - M.lower j ≤ M.length j := by
      unfold length
      linarith [ht.2]
    exact this.trans_lt (hdiam j)
  have hraw := M.abs_rowResidual_le_twoTails P hFosc hKosc
    (fun s hs t ht => hKernel t ht s hs) i
  have hmiddle : P.upperEnd - P.base ≤ 1 := by
    linarith [P.base_nonneg, P.upperEnd_le_one]
  have hkernelTerm :
      2 * (target / 10) * (P.upperEnd - P.base) ≤ target / 5 := by
    have hcoef : 0 ≤ 2 * (target / 10) := by positivity
    calc
      2 * (target / 10) * (P.upperEnd - P.base) ≤
          2 * (target / 10) * 1 :=
        mul_le_mul_of_nonneg_left hmiddle hcoef
      _ = target / 5 := by ring
  have hlow : C * P.base < target / 5 := by
    have hfirst : C * P.base ≤ (C + 1) * P.base :=
      mul_le_mul_of_nonneg_right (by linarith) P.base_nonneg
    have hsecond : (C + 1) * P.base < (C + 1) * beta :=
      mul_lt_mul_of_pos_left hbase hCplus
    have heq : (C + 1) * beta = target / 5 := by
      unfold beta
      field_simp [ne_of_gt hCplus]
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  have hhigh : C * (1 - P.upperEnd) < target / 5 := by
    have hnonneg : 0 ≤ 1 - P.upperEnd := sub_nonneg.mpr P.upperEnd_le_one
    have hfirst : C * (1 - P.upperEnd) ≤
        (C + 1) * (1 - P.upperEnd) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    have hsecond : (C + 1) * (1 - P.upperEnd) < (C + 1) * beta :=
      mul_lt_mul_of_pos_left htop hCplus
    have heq : (C + 1) * beta = target / 5 := by
      unfold beta
      field_simp [ne_of_gt hCplus]
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  calc
    |M.rowResidual i| ≤
        2 * (target / 10) +
          2 * (target / 10) * (P.upperEnd - P.base) +
          C * P.base + C * (1 - P.upperEnd) := hraw
    _ < target := by
      have hdiag : 2 * (target / 10) = target / 5 := by ring
      rw [hdiag]
      linarith

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
