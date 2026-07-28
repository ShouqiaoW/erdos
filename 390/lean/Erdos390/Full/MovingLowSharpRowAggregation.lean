import Erdos390.Full.ContinuumTwoTailResidualBound

/-!
# Moving-low sharp row aggregation

Relative centre errors, rather than absolute centre-ratio errors, are the
correct uniform quantities when the low centre tends to zero.  This file
proves that their contribution is controlled by the positive sharp graph
row, whose total mass is bounded independently of the mesh.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

private theorem continuous_innerSharpKernel (j : Band) :
    Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) := by
  let d : ℝ → ℝ := fun t => max t (M.lower j / 2)
  have hdcont : Continuous d := continuous_id.max
    (continuous_const : Continuous fun _ : ℝ => M.lower j / 2)
  have hd0 (t : ℝ) : d t ≠ 0 := by
    apply ne_of_gt
    exact (half_pos (M.lower_pos j)).trans_le (le_max_right _ _)
  have hsurrogate : Continuous (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / d t) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (a₀ := M.lower j) (b₀ := M.upper j)
    exact (continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).neg.div
        (hdcont.comp continuous_snd) (fun z => hd0 z.2)
  have heq : (fun s : ℝ =>
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
      (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / d t) := by
    funext s
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    have hhalf : M.lower j / 2 ≤ t := by
      linarith [M.lower_pos j, htcc.1]
    change (-covarianceKernelQuotient t s) / t =
      (-covarianceKernelQuotient t s) / d t
    rw [show d t = t by simp [d, max_eq_left hhalf]]
  rw [heq]
  exact hsurrogate

theorem sharpKernelEdge_le_kernelBound_mul_length
    {C : ℝ}
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C)
    (i j : Band) :
    M.sharpKernelEdge i j ≤ C * M.length j := by
  have hC : 0 ≤ C :=
    (abs_nonneg (covarianceKernelQuotient (M.lower j) (M.lower i))).trans
      (hKernel (M.lower i)
        ⟨(M.lower_pos i).le,
          (M.lower_lt_upper i).le.trans (M.upper_le_one i)⟩
        (M.lower j)
        ⟨(M.lower_pos j).le,
          (M.lower_lt_upper j).le.trans (M.upper_le_one j)⟩)
  have hinner (s : ℝ) (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      (∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) ≤
        C * M.harmonicMass j := by
    have hleft : IntervalIntegrable
        (fun t : ℝ => (-covarianceKernelQuotient t s) / t) volume
        (M.lower j) (M.upper j) := by
      apply ContinuousOn.intervalIntegrable_of_Icc
        (le_of_lt (M.lower_lt_upper j))
      intro t ht
      exact ((continuous_uncurry_covarianceKernelQuotient.comp
        (continuous_id.prodMk continuous_const)).neg.continuousAt.div
          continuousAt_id
          (ne_of_gt ((M.lower_pos j).trans_le ht.1))).continuousWithinAt
    have hright : IntervalIntegrable (fun t : ℝ => C / t) volume
        (M.lower j) (M.upper j) := by
      apply ContinuousOn.intervalIntegrable_of_Icc
        (le_of_lt (M.lower_lt_upper j))
      intro t ht
      exact (continuousAt_const.div continuousAt_id
        (ne_of_gt ((M.lower_pos j).trans_le ht.1))).continuousWithinAt
    have hmono := intervalIntegral.integral_mono_on
      (le_of_lt (M.lower_lt_upper j)) hleft hright (fun t ht => by
        have htpos : 0 < t := (M.lower_pos j).trans_le ht.1
        apply div_le_div_of_nonneg_right _ htpos.le
        exact (neg_le_abs _).trans
          (hKernel s (M.cell_mem_unit hs) t (M.cell_mem_unit ht)))
    calc
      _ ≤ ∫ t in M.lower j..M.upper j, C / t := hmono
      _ = C * M.harmonicMass j := by
        unfold harmonicMass
        rw [show (fun t : ℝ => C / t) = fun t : ℝ => C * (1 / t) by
          funext t; ring, intervalIntegral.integral_const_mul]
  have houter :
      (∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / t) ≤
        M.length i * (C * M.harmonicMass j) := by
    have hleft : IntervalIntegrable (fun s : ℝ =>
        ∫ t in M.lower j..M.upper j,
          (-covarianceKernelQuotient t s) / t) volume
        (M.lower i) (M.upper i) :=
      (M.continuous_innerSharpKernel j).intervalIntegrable _ _
    have hright : IntervalIntegrable
        (fun _s : ℝ => C * M.harmonicMass j) volume
        (M.lower i) (M.upper i) := continuous_const.intervalIntegrable _ _
    have hmono := intervalIntegral.integral_mono_on
      (le_of_lt (M.lower_lt_upper i)) hleft hright hinner
    calc
      _ ≤ ∫ _s in M.lower i..M.upper i,
          C * M.harmonicMass j := hmono
      _ = M.length i * (C * M.harmonicMass j) := by
        simp only [intervalIntegral.integral_const, smul_eq_mul, length]
  unfold sharpKernelEdge
  calc
    (M.center j / M.length i) *
        (∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j,
            (-covarianceKernelQuotient t s) / t) ≤
      (M.center j / M.length i) *
        (M.length i * (C * M.harmonicMass j)) :=
      mul_le_mul_of_nonneg_left houter
        (div_nonneg (M.center_pos j).le (M.length_pos i).le)
    _ = C * M.length j := by
      unfold center
      field_simp [ne_of_gt (M.length_pos i), ne_of_gt (M.harmonicMass_pos j)]

theorem sharpKernelEdge_rowSum_le
    (P : M.TwoTailPartitionCertificate) {C : ℝ}
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C)
    (i : Band) :
    (∑ j, M.sharpKernelEdge i j) ≤ C := by
  have hC : 0 ≤ C := by
    have h := M.sharpKernelEdge_le_kernelBound_mul_length hKernel i i
    exact le_of_not_gt (fun hneg => by
      have hright : C * M.length i < 0 := mul_neg_of_neg_of_pos hneg (M.length_pos i)
      exact (not_lt_of_ge (M.sharpKernelEdge_nonneg i i)) (h.trans_lt hright))
  calc
    (∑ j, M.sharpKernelEdge i j) ≤
        ∑ j, C * M.length j :=
      Finset.sum_le_sum (fun j hj =>
        M.sharpKernelEdge_le_kernelBound_mul_length hKernel i j)
    _ = C * (P.upperEnd - P.base) := by
      rw [← Finset.mul_sum, P.totalLength]
    _ ≤ C := by
      have hspan : P.upperEnd - P.base ≤ 1 := by
        linarith [P.base_nonneg, P.upperEnd_le_one]
      nlinarith

/-- Relative individual centre errors imply a sharp-weighted pair-ratio
bound, even when the low centre tends to zero. -/
theorem abs_centerRatio_sub_le_of_relative
    (alpha : Band → ℝ) {e : ℝ}
    (he : 0 ≤ e) (heHalf : e ≤ 1 / 2)
    (hrel : ∀ k, |alpha k / M.center k - 1| ≤ e)
    (i j : Band) :
    |alpha j / alpha i - M.center j / M.center i| ≤
      4 * e * |M.center j / M.center i| := by
  let ri := alpha i / M.center i
  let rj := alpha j / M.center j
  have hriLower : 1 / 2 ≤ ri := by
    have := (abs_le.mp (hrel i)).1
    dsimp only [ri] at this ⊢
    linarith
  have hriPos : 0 < ri := lt_of_lt_of_le (by norm_num) hriLower
  have hdiff : |rj - ri| ≤ 2 * e := by
    calc
      |rj - ri| = |(rj - 1) - (ri - 1)| := by ring_nf
      _ ≤ |rj - 1| + |ri - 1| := abs_sub _ _
      _ ≤ e + e := add_le_add (hrel j) (hrel i)
      _ = 2 * e := by ring
  have hquot : |rj / ri - 1| ≤ 4 * e := by
    have hid : rj / ri - 1 = (rj - ri) / ri := by
      field_simp [ne_of_gt hriPos]
    rw [hid, abs_div, abs_of_pos hriPos]
    apply (div_le_iff₀ hriPos).2
    have hmul : 4 * e * (1 / 2) ≤ 4 * e * ri :=
      mul_le_mul_of_nonneg_left hriLower (by positivity)
    nlinarith
  have hAlphaI : alpha i ≠ 0 := by
    have hcenter := M.center_pos i
    have : alpha i = ri * M.center i := by
      dsimp only [ri]
      field_simp [ne_of_gt hcenter]
    rw [this]
    exact mul_ne_zero (ne_of_gt hriPos) (ne_of_gt hcenter)
  have hid : alpha j / alpha i - M.center j / M.center i =
      (M.center j / M.center i) * (rj / ri - 1) := by
    dsimp only [ri, rj]
    field_simp [hAlphaI, ne_of_gt (M.center_pos i),
      ne_of_gt (M.center_pos j)]
  rw [hid, abs_mul]
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hquot (abs_nonneg (M.center j / M.center i))

theorem centerRatio_weightedRow_le
    (P : M.TwoTailPartitionCertificate)
    (alpha : Band → ℝ) {e C : ℝ}
    (he : 0 ≤ e) (heHalf : e ≤ 1 / 2)
    (hrel : ∀ k, |alpha k / M.center k - 1| ≤ e)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernelQuotient t s| ≤ C)
    (i : Band) :
    (∑ j, |M.normalizedKernelCell i j| *
      |alpha j / alpha i - M.center j / M.center i|) ≤
      4 * e * C := by
  have hedgeIdentity (j : Band) :
      |M.normalizedKernelCell i j| *
          |M.center j / M.center i| = M.sharpKernelEdge i j := by
    have hratio : 0 < M.center j / M.center i :=
      div_pos (M.center_pos j) (M.center_pos i)
    have hedge := M.sharpKernelEdge_eq_normalizedKernelCell i j
    calc
      |M.normalizedKernelCell i j| * |M.center j / M.center i| =
          |-M.normalizedKernelCell i j *
            (M.center j / M.center i)| := by
          rw [abs_mul, abs_neg]
      _ = |M.sharpKernelEdge i j| := by rw [hedge]
      _ = M.sharpKernelEdge i j := abs_of_nonneg (M.sharpKernelEdge_nonneg i j)
  calc
    (∑ j, |M.normalizedKernelCell i j| *
        |alpha j / alpha i - M.center j / M.center i|) ≤
      ∑ j, 4 * e * M.sharpKernelEdge i j := by
        apply Finset.sum_le_sum
        intro j hj
        calc
          |M.normalizedKernelCell i j| *
              |alpha j / alpha i - M.center j / M.center i| ≤
            |M.normalizedKernelCell i j| *
              (4 * e * |M.center j / M.center i|) :=
            mul_le_mul_of_nonneg_left
              (M.abs_centerRatio_sub_le_of_relative alpha he heHalf hrel i j)
              (abs_nonneg _)
          _ = 4 * e * M.sharpKernelEdge i j := by
            rw [← hedgeIdentity]
            ring
    _ = 4 * e * (∑ j, M.sharpKernelEdge i j) := by rw [Finset.mul_sum]
    _ ≤ 4 * e * C := mul_le_mul_of_nonneg_left
      (M.sharpKernelEdge_rowSum_le P hKernel i) (by positivity)

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
