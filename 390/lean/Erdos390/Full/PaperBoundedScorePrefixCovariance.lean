import Erdos390.Full.OmittedScoreTilt
import Erdos390.Full.LocalizedMarkedTiltCovariance

/-!
# Localized covariance transport on an arbitrary fixed score box

The Taylor wrapper used previously normalized the pointwise score to one.
For the paper's parameter order the coefficient box is chosen after `W`, so
that normalization must not survive as a terminal hypothesis.  The lemmas
below instead use the exact exponential change of measure.  A fixed score
box contributes only `exp K`; the small quantity is the first absolute
score moment.  Marked first moments retain their reciprocal-prime scale.
-/

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- A nonnegative mark need not be pointwise bounded.  Under an arbitrary
fixed score box, its expectation changes on the scale of its marked first
score moment plus its mean times the unmarked first score moment. -/
theorem abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
    (mu : FiniteProbability Omega) (F S : Omega → ℝ)
    {K a MF RF : ℝ}
    (hF0 : ∀ omega, 0 ≤ F omega)
    (hscore : ∀ omega, |S omega| ≤ K)
    (ha0 : 0 ≤ a) (hMF0 : 0 ≤ MF) (hRF0 : 0 ≤ RF)
    (hsmall : Real.exp K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hmeanF : mu.expect F ≤ MF)
    (hmarked : mu.expect (fun omega ↦ F omega * |S omega|) ≤ RF) :
    |(mu.exponentialTilt S).expect F - mu.expect F| ≤
      2 * Real.exp K * (RF + MF * a) := by
  let Z := mu.expPartition S
  let m := mu.expect F
  let N := mu.expect (fun omega ↦ F omega * Real.exp (S omega))
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation F S
  have hm0 : 0 ≤ m := by
    dsimp only [m]
    exact mu.expect_nonneg F hF0
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have heta0 : 0 ≤ eta :=
    mu.markedExponentialDeviation_nonneg F S hF0
  have hdelta : delta ≤ Real.exp K * a := by
    exact (mu.exponentialDeviation_le_exp_mul_expect_abs S hscore).trans
      (mul_le_mul_of_nonneg_left habsScore (Real.exp_pos K).le)
  have hdeltaHalf : delta ≤ (1 : ℝ) / 2 := hdelta.trans hsmall
  have hdeltaOne : delta < 1 := hdeltaHalf.trans_lt (by norm_num)
  have hZpos : 0 < Z := mu.expPartition_pos S
  have hZhalf : (1 : ℝ) / 2 ≤ Z := by
    have hlower := mu.expPartition_lower_bound S
    dsimp only [Z]
    linarith
  have hN : |N - m| ≤ eta := by
    dsimp only [N, m]
    exact mu.abs_expWeighted_expect_sub_expect_le F S hF0
  have hZ : |Z - 1| ≤ delta := by
    dsimp only [Z, delta]
    exact mu.abs_expPartition_sub_one_le_deviation S
  have heta : eta ≤ Real.exp K * RF := by
    exact (mu.markedExponentialDeviation_le_exp_mul_expect_abs
      F S hF0 hscore).trans
        (mul_le_mul_of_nonneg_left hmarked (Real.exp_pos K).le)
  rw [mu.exponentialTilt_expect_eq F S]
  change |N / Z - m| ≤ _
  have hid : N / Z - m = ((N - m) + m * (1 - Z)) / Z := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hZpos]
  have hnum : |(N - m) + m * (1 - Z)| ≤
      Real.exp K * (RF + MF * a) := by
    calc
      |(N - m) + m * (1 - Z)| ≤ |N - m| + |m * (1 - Z)| :=
        abs_add_le _ _
      _ = |N - m| + m * |Z - 1| := by
        rw [abs_mul, abs_of_nonneg hm0, abs_sub_comm 1 Z]
      _ ≤ eta + MF * delta := by
        exact add_le_add hN
          (mul_le_mul hmeanF hZ (abs_nonneg _) hMF0)
      _ ≤ Real.exp K * RF + MF * (Real.exp K * a) := by
        exact add_le_add heta
          (mul_le_mul_of_nonneg_left hdelta hMF0)
      _ = Real.exp K * (RF + MF * a) := by ring
  have htarget0 : 0 ≤ Real.exp K * (RF + MF * a) := by positivity
  calc
    |(N - m) + m * (1 - Z)| / Z ≤
        (Real.exp K * (RF + MF * a)) / Z :=
      div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (Real.exp K * (RF + MF * a)) / ((1 : ℝ) / 2) := by
      exact div_le_div_of_nonneg_left htarget0 (by norm_num) hZhalf
    _ = 2 * Real.exp K * (RF + MF * a) := by ring

/-- Covariance with a `[0,1]` prefix is stable on the same marked scale.
The conclusion displays the exact two expectation-loss coefficients used
downstream; no pointwise-small relation between `K` and the prime cutoff is
assumed. -/
theorem abs_exponentialTilt_covariance_prefix_sub_covariance_le_of_bounded_score
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ)
    {K a MF RF : ℝ}
    (hF0 : ∀ omega, 0 ≤ F omega)
    (hG0 : ∀ omega, 0 ≤ G omega)
    (hG1 : ∀ omega, G omega ≤ 1)
    (hscore : ∀ omega, |S omega| ≤ K)
    (ha0 : 0 ≤ a) (hMF0 : 0 ≤ MF) (hRF0 : 0 ≤ RF)
    (hsmall : Real.exp K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hmeanF : mu.expect F ≤ MF)
    (hmarkedF : mu.expect (fun omega ↦ F omega * |S omega|) ≤ RF) :
    let DF := 2 * Real.exp K * (RF + MF * a)
    let DG := 4 * Real.exp K * a
    |(mu.exponentialTilt S).covariance F G - mu.covariance F G| ≤
      DF + (MF + DF) * DG + DF := by
  dsimp only
  let DF : ℝ := 2 * Real.exp K * (RF + MF * a)
  let DG : ℝ := 4 * Real.exp K * a
  have hDF0 : 0 ≤ DF := by dsimp only [DF]; positivity
  have hDG0 : 0 ≤ DG := by dsimp only [DG]; positivity
  have hmeanG : mu.expect G ≤ 1 := by
    calc
      mu.expect G ≤ mu.expect (fun _ ↦ (1 : ℝ)) :=
        mu.expect_mono G _ hG1
      _ = 1 := by
        unfold expect
        rw [← Finset.sum_mul, mu.mass_sum, one_mul]
  have hmarkedG : mu.expect (fun omega ↦ G omega * |S omega|) ≤ a := by
    calc
      mu.expect (fun omega ↦ G omega * |S omega|) ≤
          mu.expect (fun omega ↦ |S omega|) := by
        apply mu.expect_mono
        intro omega
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hG1 omega) (abs_nonneg (S omega))
      _ ≤ a := habsScore
  have hFG0 : ∀ omega, 0 ≤ F omega * G omega := fun omega ↦
    mul_nonneg (hF0 omega) (hG0 omega)
  have hFGle : ∀ omega, F omega * G omega ≤ F omega := by
    intro omega
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hG1 omega) (hF0 omega)
  have hmeanFG : mu.expect (fun omega ↦ F omega * G omega) ≤ MF :=
    (mu.expect_mono _ F hFGle).trans hmeanF
  have hmarkedFG : mu.expect
      (fun omega ↦ (F omega * G omega) * |S omega|) ≤ RF := by
    calc
      mu.expect (fun omega ↦ (F omega * G omega) * |S omega|) ≤
          mu.expect (fun omega ↦ F omega * |S omega|) := by
        apply mu.expect_mono
        intro omega
        exact mul_le_mul_of_nonneg_right (hFGle omega) (abs_nonneg _)
      _ ≤ RF := hmarkedF
  have hFperturb :
      |(mu.exponentialTilt S).expect F - mu.expect F| ≤ DF := by
    simpa only [DF] using
      mu.abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
        F S hF0 hscore ha0 hMF0 hRF0 hsmall habsScore hmeanF hmarkedF
  have hGperturb :
      |(mu.exponentialTilt S).expect G - mu.expect G| ≤ DG := by
    have hraw :=
      mu.abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
        G S hG0 hscore ha0 (by norm_num : (0 : ℝ) ≤ 1) ha0
        hsmall habsScore hmeanG hmarkedG
    convert hraw using 1
    dsimp only [DG]
    ring
  have hFGperturb :
      |(mu.exponentialTilt S).expect (fun omega ↦ F omega * G omega) -
          mu.expect (fun omega ↦ F omega * G omega)| ≤ DF := by
    simpa only [DF] using
      mu.abs_exponentialTilt_expect_sub_expect_le_of_bounded_score_moments
        (fun omega ↦ F omega * G omega) S hFG0 hscore ha0 hMF0 hRF0
        hsmall habsScore hmeanFG hmarkedFG
  simpa only [DF, DG, one_mul] using
    (abs_covariance_sub_covariance_le_of_expectation_perturbations
      mu (mu.exponentialTilt S) F G hF0 hG0 hmeanF hmeanG hDF0
        hFperturb hGperturb hFGperturb)

end FiniteProbability

end

end Erdos390.Full
