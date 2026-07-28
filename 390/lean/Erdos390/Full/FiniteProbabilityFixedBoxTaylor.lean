import Erdos390.Full.PaperMediumNuisanceInputReduction

/-!
# Finite exponential Taylor estimates on an arbitrary fixed box

The moving-prefix argument must allow the exponential score to lie in an
arbitrary fixed box.  Requiring `|S| ≤ 1` would force the prime cutoff to be
chosen after the later ODE box.  This file replaces that normalization by
explicit constants depending on the fixed score bound `K`.

Only the eventual ambient threshold will depend on these constants.  No
smallness relation between `K` and the prime cutoff is present.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Linear exponential-remainder constant on `[-K,K]`. -/
def fixedBoxLinearConstant (K : ℝ) : ℝ := Real.exp K + 1

/-- Quadratic exponential-remainder constant on `[-K,K]`. -/
def fixedBoxQuadraticConstant (K : ℝ) : ℝ := Real.exp K + 1 + K

theorem fixedBoxLinearConstant_nonneg (K : ℝ) :
    0 ≤ fixedBoxLinearConstant K := by
  unfold fixedBoxLinearConstant
  positivity

theorem two_le_fixedBoxLinearConstant {K : ℝ} (hK : 0 ≤ K) :
    2 ≤ fixedBoxLinearConstant K := by
  unfold fixedBoxLinearConstant
  have hexp : 1 ≤ Real.exp K := by
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hK
  linarith

theorem one_le_fixedBoxQuadraticConstant {K : ℝ} (hK : 0 ≤ K) :
    1 ≤ fixedBoxQuadraticConstant K := by
  unfold fixedBoxQuadraticConstant
  have hexp : 0 < Real.exp K := Real.exp_pos K
  linarith

/-- The first exponential remainder is Lipschitz on every fixed box, with
an explicit constant. -/
theorem abs_exp_sub_one_le_fixedBox {K x : ℝ} (hK : 0 ≤ K)
    (hx : |x| ≤ K) :
    |Real.exp x - 1| ≤ fixedBoxLinearConstant K * |x| := by
  by_cases hxone : |x| ≤ 1
  · calc
      |Real.exp x - 1| ≤ 2 * |x| := Real.abs_exp_sub_one_le hxone
      _ ≤ fixedBoxLinearConstant K * |x| :=
        mul_le_mul_of_nonneg_right (two_le_fixedBoxLinearConstant hK)
          (abs_nonneg x)
  · have hone : 1 ≤ |x| := le_of_lt (lt_of_not_ge hxone)
    have hxK : x ≤ K := (le_abs_self x).trans hx
    have hexp : Real.exp x ≤ Real.exp K := Real.exp_le_exp.mpr hxK
    have hC : 0 ≤ fixedBoxLinearConstant K :=
      fixedBoxLinearConstant_nonneg K
    calc
      |Real.exp x - 1| ≤ |Real.exp x| + |(1 : ℝ)| := abs_sub _ _
      _ = Real.exp x + 1 := by rw [abs_of_pos (Real.exp_pos x)]; norm_num
      _ ≤ Real.exp K + 1 := by linarith
      _ = fixedBoxLinearConstant K := rfl
      _ ≤ fixedBoxLinearConstant K * |x| := by
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hone hC

/-- The second exponential remainder is quadratic on every fixed box, with
an explicit constant. -/
theorem abs_exp_sub_one_sub_id_le_fixedBox {K x : ℝ} (hK : 0 ≤ K)
    (hx : |x| ≤ K) :
    |Real.exp x - 1 - x| ≤ fixedBoxQuadraticConstant K * x ^ 2 := by
  by_cases hxone : |x| ≤ 1
  · have hbase := Real.abs_exp_sub_one_sub_id_le hxone
    have hC := one_le_fixedBoxQuadraticConstant hK
    calc
      |Real.exp x - 1 - x| ≤ x ^ 2 := hbase
      _ = 1 * x ^ 2 := by ring
      _ ≤ fixedBoxQuadraticConstant K * x ^ 2 :=
        mul_le_mul_of_nonneg_right hC (sq_nonneg x)
  · have honeAbs : 1 ≤ |x| := le_of_lt (lt_of_not_ge hxone)
    have honeSq : 1 ≤ x ^ 2 := by
      rw [← sq_abs]
      nlinarith [abs_nonneg x]
    have hxK : x ≤ K := (le_abs_self x).trans hx
    have hexp : Real.exp x ≤ Real.exp K := Real.exp_le_exp.mpr hxK
    have hC0 : 0 ≤ fixedBoxQuadraticConstant K :=
      (one_le_fixedBoxQuadraticConstant hK).trans' zero_le_one
    calc
      |Real.exp x - 1 - x| ≤ |Real.exp x - 1| + |x| := abs_sub _ _
      _ ≤ (|Real.exp x| + |(1 : ℝ)|) + |x| :=
        add_le_add (abs_sub _ _) le_rfl
      _ = Real.exp x + 1 + |x| := by
        rw [abs_of_pos (Real.exp_pos x)]
        norm_num
      _ ≤ Real.exp K + 1 + K := by linarith
      _ = fixedBoxQuadraticConstant K := rfl
      _ = fixedBoxQuadraticConstant K * 1 := by ring
      _ ≤ fixedBoxQuadraticConstant K * x ^ 2 :=
        mul_le_mul_of_nonneg_left honeSq hC0

/-- Integrated first-remainder bound on a fixed score box. -/
theorem exponentialDeviation_le_fixedBox_expect_abs
    (mu : FiniteProbability Omega) (S : Omega → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hscore : ∀ omega, |S omega| ≤ K) :
    mu.exponentialDeviation S ≤
      fixedBoxLinearConstant K * mu.expect (fun omega ↦ |S omega|) := by
  unfold exponentialDeviation expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega homega
  calc
    mu.mass omega * |Real.exp (S omega) - 1| ≤
        mu.mass omega * (fixedBoxLinearConstant K * |S omega|) :=
      mul_le_mul_of_nonneg_left
        (abs_exp_sub_one_le_fixedBox hK (hscore omega))
        (mu.mass_nonneg omega)
    _ = fixedBoxLinearConstant K *
        (mu.mass omega * |S omega|) := by ring

/-- Integrated second-remainder bound against an arbitrary signed mark. -/
theorem abs_expect_exp_sub_one_sub_score_le_fixedBox
    (mu : FiniteProbability Omega) (H S : Omega → ℝ) {K : ℝ}
    (hK : 0 ≤ K) (hscore : ∀ omega, |S omega| ≤ K) :
    |mu.expect (fun omega ↦
        H omega * (Real.exp (S omega) - 1 - S omega))| ≤
      fixedBoxQuadraticConstant K *
        mu.expect (fun omega ↦ |H omega| * S omega ^ 2) := by
  calc
    |mu.expect (fun omega ↦
        H omega * (Real.exp (S omega) - 1 - S omega))| ≤
      mu.expect (fun omega ↦
        |H omega * (Real.exp (S omega) - 1 - S omega)|) :=
      mu.abs_expect_le_expect_abs _
    _ ≤ mu.expect (fun omega ↦
        fixedBoxQuadraticConstant K * (|H omega| * S omega ^ 2)) := by
      apply mu.expect_mono
      intro omega
      rw [abs_mul]
      calc
        |H omega| * |Real.exp (S omega) - 1 - S omega| ≤
            |H omega| *
              (fixedBoxQuadraticConstant K * S omega ^ 2) :=
          mul_le_mul_of_nonneg_left
            (abs_exp_sub_one_sub_id_le_fixedBox hK (hscore omega))
            (abs_nonneg (H omega))
        _ = fixedBoxQuadraticConstant K *
            (|H omega| * S omega ^ 2) := by ring
    _ = fixedBoxQuadraticConstant K *
        mu.expect (fun omega ↦ |H omega| * S omega ^ 2) := by
      unfold expect
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro omega homega
      ring

/-- Mean-sensitive normalized Taylor estimate on an arbitrary fixed score
box.  The normalization denominator is controlled by the first fixed-box
constant, while every second-order remainder carries the second constant. -/
theorem abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound_fixedBox
    (mu : FiniteProbability Omega) (H S : Omega → ℝ)
    {K a Rone MH RH CH : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hRone : 0 ≤ Rone)
    (hMH : 0 ≤ MH) (hRH : 0 ≤ RH) (hCH : 0 ≤ CH)
    (hscore : ∀ omega, |S omega| ≤ K)
    (hsmall : fixedBoxLinearConstant K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hmean : |mu.expect H| ≤ MH)
    (hmarkedSq :
      mu.expect (fun omega ↦ |H omega| * S omega ^ 2) ≤ RH)
    (hcov : |mu.covariance H S| ≤ CH) :
    |(mu.exponentialTilt S).expect H -
        (mu.expect H + mu.covariance H S)| ≤
      2 * fixedBoxQuadraticConstant K *
        (RH + CH * a + (MH + CH) * Rone) := by
  let Z := mu.expPartition S
  let m := mu.expect H
  let c := mu.covariance H S
  let s := mu.expect S
  let r := mu.expect (fun omega ↦
    H omega * (Real.exp (S omega) - 1 - S omega))
  let rone := mu.expect (fun omega ↦
    Real.exp (S omega) - 1 - S omega)
  let D := fixedBoxQuadraticConstant K
  have hD : 0 ≤ D := by
    dsimp only [D]
    exact zero_le_one.trans (one_le_fixedBoxQuadraticConstant hK)
  have hdelta := mu.exponentialDeviation_le_fixedBox_expect_abs
    S hK hscore
  have hdeltaHalf : mu.exponentialDeviation S ≤ (1 : ℝ) / 2 :=
    hdelta.trans ((mul_le_mul_of_nonneg_left habsScore
      (fixedBoxLinearConstant_nonneg K)).trans hsmall)
  have hZhalf : (1 : ℝ) / 2 ≤ Z := by
    have hlower := mu.expPartition_lower_bound S
    dsimp only [Z]
    linarith
  have hZpos : 0 < Z := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hZhalf
  have hm : |m| ≤ MH := by simpa only [m] using hmean
  have hc : |c| ≤ CH := by simpa only [c] using hcov
  have hs : |s| ≤ a := by
    dsimp only [s]
    exact (mu.abs_expect_le_expect_abs S).trans habsScore
  have hr : |r| ≤ D * RH := by
    dsimp only [r, D]
    exact (mu.abs_expect_exp_sub_one_sub_score_le_fixedBox
      H S hK hscore).trans
        (mul_le_mul_of_nonneg_left hmarkedSq
          (zero_le_one.trans (one_le_fixedBoxQuadraticConstant hK)))
  have hrone : |rone| ≤ D * Rone := by
    have hraw := mu.abs_expect_exp_sub_one_sub_score_le_fixedBox
      (fun _ ↦ (1 : ℝ)) S hK hscore
    have hrewrite :
        (fun omega ↦ |(1 : ℝ)| * S omega ^ 2) =
          fun omega ↦ S omega ^ 2 := by
      funext omega
      norm_num
    dsimp only [rone, D]
    rw [hrewrite] at hraw
    simpa only [one_mul] using
      hraw.trans (mul_le_mul_of_nonneg_left hscoreSq
        (zero_le_one.trans (one_le_fixedBoxQuadraticConstant hK)))
  have hpartition : Z = 1 + s + rone := by
    dsimp only [Z, s, rone]
    unfold expPartition expect
    rw [show (∑ omega, mu.mass omega * Real.exp (S omega)) =
        (∑ omega, mu.mass omega * (1 + S omega +
          (Real.exp (S omega) - 1 - S omega))) by
      apply Finset.sum_congr rfl
      intro omega homega
      ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ omega, mu.mass omega * 1) = 1 by
      simpa only [mul_one] using mu.mass_sum]
  have hnumerator :
      mu.expect (fun omega ↦ H omega * Real.exp (S omega)) =
        m + mu.expect (fun omega ↦ H omega * S omega) + r := by
    dsimp only [m, r]
    unfold expect
    rw [show (∑ omega, mu.mass omega *
        (H omega * Real.exp (S omega))) =
      ∑ omega, mu.mass omega *
        (H omega + H omega * S omega +
          H omega * (Real.exp (S omega) - 1 - S omega)) by
      apply Finset.sum_congr rfl
      intro omega homega
      ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcovIdentity :
      mu.expect (fun omega ↦ H omega * S omega) = c + m * s := by
    dsimp only [c, m, s]
    unfold covariance
    ring
  have hdiffIdentity :
      mu.expect (fun omega ↦ H omega * Real.exp (S omega)) -
          (m + c) * Z = r - c * s - (m + c) * rone := by
    rw [hnumerator, hcovIdentity, hpartition]
    ring
  rw [mu.exponentialTilt_expect_eq H S]
  change |mu.expect (fun omega ↦ H omega * Real.exp (S omega)) / Z -
      (m + c)| ≤ _
  rw [show mu.expect (fun omega ↦ H omega * Real.exp (S omega)) / Z -
      (m + c) =
      (mu.expect (fun omega ↦ H omega * Real.exp (S omega)) -
        (m + c) * Z) / Z by field_simp]
  rw [hdiffIdentity, abs_div, abs_of_pos hZpos]
  have hnum : |r - c * s - (m + c) * rone| ≤
      D * (RH + CH * a + (MH + CH) * Rone) := by
    calc
      |r - c * s - (m + c) * rone| ≤
          |r| + |c| * |s| + (|m| + |c|) * |rone| := by
        calc
          |r - c * s - (m + c) * rone| ≤
              |r - c * s| + |(m + c) * rone| := abs_sub _ _
          _ ≤ (|r| + |c * s|) + |(m + c) * rone| :=
            add_le_add (abs_sub _ _) le_rfl
          _ ≤ |r| + |c| * |s| + (|m| + |c|) * |rone| := by
            rw [abs_mul, abs_mul]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg rone))
      _ ≤ D * RH + CH * a + (MH + CH) * (D * Rone) := by
        exact add_le_add
          (add_le_add hr (mul_le_mul hc hs (abs_nonneg s) hCH))
          (mul_le_mul (add_le_add hm hc) hrone (abs_nonneg rone)
            (add_nonneg hMH hCH))
      _ ≤ D * (RH + CH * a + (MH + CH) * Rone) := by
        have hDone : 1 ≤ D := by
          dsimp only [D]
          exact one_le_fixedBoxQuadraticConstant hK
        have hcha : 0 ≤ CH * a := mul_nonneg hCH ha
        nlinarith [mul_le_mul_of_nonneg_right hDone hcha]
  have htarget0 :
      0 ≤ D * (RH + CH * a + (MH + CH) * Rone) := by positivity
  calc
    |r - c * s - (m + c) * rone| / Z ≤
      (D * (RH + CH * a + (MH + CH) * Rone)) / Z :=
        div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (D * (RH + CH * a + (MH + CH) * Rone)) /
        ((1 : ℝ) / 2) :=
      div_le_div_of_nonneg_left htarget0 (by norm_num) hZhalf
    _ = 2 * fixedBoxQuadraticConstant K *
        (RH + CH * a + (MH + CH) * Rone) := by
      dsimp only [D]
      ring

/-- Centered covariance Taylor estimate on an arbitrary fixed score box.
The only change from the unit-box formula is the explicit quadratic
remainder factor `fixedBoxQuadraticConstant K`. -/
theorem abs_exponentialTilt_covariance_le_of_centeredTaylor_expect_bounds_fixedBox
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ)
    {K a Rone MF MG MFG RF RG RFG CF CG CFG Czero Cthird : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hRone : 0 ≤ Rone)
    (hMF : 0 ≤ MF) (hMG : 0 ≤ MG) (hMFG : 0 ≤ MFG)
    (hRF : 0 ≤ RF) (hRG : 0 ≤ RG) (hRFG : 0 ≤ RFG)
    (hCF : 0 ≤ CF) (hCG : 0 ≤ CG) (hCFG : 0 ≤ CFG)
    (hscore : ∀ omega, |S omega| ≤ K)
    (hsmall : fixedBoxLinearConstant K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hmeanF : |mu.expect F| ≤ MF)
    (hmeanG : |mu.expect G| ≤ MG)
    (hmeanFG : |mu.expect (fun omega ↦ F omega * G omega)| ≤ MFG)
    (hmarkedSqF :
      mu.expect (fun omega ↦ |F omega| * S omega ^ 2) ≤ RF)
    (hmarkedSqG :
      mu.expect (fun omega ↦ |G omega| * S omega ^ 2) ≤ RG)
    (hmarkedSqFG :
      mu.expect (fun omega ↦ |F omega * G omega| * S omega ^ 2) ≤ RFG)
    (hcovF : |mu.covariance F S| ≤ CF)
    (hcovG : |mu.covariance G S| ≤ CG)
    (hcovFG : |mu.covariance (fun omega ↦ F omega * G omega) S| ≤ CFG)
    (hbase : |mu.covariance F G| ≤ Czero)
    (hthird : |mu.covarianceThirdCentered F G S| ≤ Cthird) :
    let D := fixedBoxQuadraticConstant K
    let EF := 2 * D * (RF + CF * a + (MF + CF) * Rone)
    let EG := 2 * D * (RG + CG * a + (MG + CG) * Rone)
    let EFG := 2 * D * (RFG + CFG * a + (MFG + CFG) * Rone)
    |(mu.exponentialTilt S).covariance F G| ≤
      Czero + Cthird + CF * CG + EFG +
        (MF + CF) * EG + (MG + CG) * EF + EF * EG := by
  dsimp only
  let D := fixedBoxQuadraticConstant K
  let EF := 2 * D * (RF + CF * a + (MF + CF) * Rone)
  let EG := 2 * D * (RG + CG * a + (MG + CG) * Rone)
  let EFG := 2 * D * (RFG + CFG * a + (MFG + CFG) * Rone)
  let mF := mu.expect F
  let mG := mu.expect G
  let cF := mu.covariance F S
  let cG := mu.covariance G S
  let eF := (mu.exponentialTilt S).expect F - (mF + cF)
  let eG := (mu.exponentialTilt S).expect G - (mG + cG)
  let eFG := (mu.exponentialTilt S).expect
      (fun omega ↦ F omega * G omega) -
    (mu.expect (fun omega ↦ F omega * G omega) +
      mu.covariance (fun omega ↦ F omega * G omega) S)
  have hEF : |eF| ≤ EF := by
    dsimp only [eF, mF, cF, EF, D]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound_fixedBox
      F S hK ha hRone hMF hRF hCF hscore hsmall habsScore hscoreSq
        hmeanF hmarkedSqF hcovF
  have hEG : |eG| ≤ EG := by
    dsimp only [eG, mG, cG, EG, D]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound_fixedBox
      G S hK ha hRone hMG hRG hCG hscore hsmall habsScore hscoreSq
        hmeanG hmarkedSqG hcovG
  have hEFG : |eFG| ≤ EFG := by
    dsimp only [eFG, EFG, D]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound_fixedBox
      (fun omega ↦ F omega * G omega) S hK ha hRone hMFG hRFG hCFG
        hscore hsmall habsScore hscoreSq hmeanFG hmarkedSqFG hcovFG
  have hmF : |mF| ≤ MF := by simpa only [mF] using hmeanF
  have hmG : |mG| ≤ MG := by simpa only [mG] using hmeanG
  have hcF : |cF| ≤ CF := by simpa only [cF] using hcovF
  have hcG : |cG| ≤ CG := by simpa only [cG] using hcovG
  have htiltF : (mu.exponentialTilt S).expect F = mF + cF + eF := by
    dsimp only [eF]
    ring
  have htiltG : (mu.exponentialTilt S).expect G = mG + cG + eG := by
    dsimp only [eG]
    ring
  have htiltFG : (mu.exponentialTilt S).expect
      (fun omega ↦ F omega * G omega) =
      mu.expect (fun omega ↦ F omega * G omega) +
        mu.covariance (fun omega ↦ F omega * G omega) S + eFG := by
    dsimp only [eFG]
    ring
  have hexpand :
      (mu.exponentialTilt S).covariance F G =
        mu.covariance F G + mu.covarianceThirdCentered F G S -
          cF * cG + eFG - (mF + cF) * eG -
          (mG + cG) * eF - eF * eG := by
    unfold covariance covarianceThirdCentered
    rw [htiltFG, htiltF, htiltG]
    dsimp only [mF, mG, cF, cG]
    ring
  have hD0 : 0 ≤ D := by
    dsimp only [D]
    exact zero_le_one.trans (one_le_fixedBoxQuadraticConstant hK)
  have hEF0 : 0 ≤ EF := by dsimp only [EF]; positivity
  have hEG0 : 0 ≤ EG := by dsimp only [EG]; positivity
  have hEFG0 : 0 ≤ EFG := by dsimp only [EFG]; positivity
  rw [hexpand]
  let x0 := mu.covariance F G
  let x1 := mu.covarianceThirdCentered F G S
  let x2 := -(cF * cG)
  let x3 := eFG
  let x4 := -((mF + cF) * eG)
  let x5 := -((mG + cG) * eF)
  let x6 := -(eF * eG)
  have hrepack :
      mu.covariance F G + mu.covarianceThirdCentered F G S -
          cF * cG + eFG - (mF + cF) * eG -
          (mG + cG) * eF - eF * eG =
        x0 + x1 + x2 + x3 + x4 + x5 + x6 := by
    dsimp only [x0, x1, x2, x3, x4, x5, x6]
    ring
  rw [hrepack]
  have htri : |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
      |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by
    calc
      |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
          |x0| + |x1 + x2 + x3 + x4 + x5 + x6| := by
        convert abs_add_le x0 (x1 + x2 + x3 + x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + |x2 + x3 + x4 + x5 + x6|) := by
        gcongr
        convert abs_add_le x1 (x2 + x3 + x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + |x3 + x4 + x5 + x6|)) := by
        gcongr
        convert abs_add_le x2 (x3 + x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| + |x4 + x5 + x6|))) := by
        gcongr
        convert abs_add_le x3 (x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| +
          (|x4| + |x5 + x6|)))) := by
        gcongr
        convert abs_add_le x4 (x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| +
          (|x4| + (|x5| + |x6|))))) := by
        gcongr
        exact abs_add_le x5 x6
      _ = |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by ring
  have htriExpanded :
      |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| =
      |mu.covariance F G| + |mu.covarianceThirdCentered F G S| +
        |cF| * |cG| + |eFG| + |mF + cF| * |eG| +
        |mG + cG| * |eF| + |eF| * |eG| := by
    dsimp only [x0, x1, x2, x3, x4, x5, x6]
    simp only [abs_neg, abs_mul]
  have hcc : |cF| * |cG| ≤ CF * CG :=
    mul_le_mul hcF hcG (abs_nonneg cG) hCF
  have hmFeG : (|mF| + |cF|) * |eG| ≤ (MF + CF) * EG :=
    mul_le_mul (add_le_add hmF hcF) hEG (abs_nonneg eG)
      (add_nonneg hMF hCF)
  have hmGeF : (|mG| + |cG|) * |eF| ≤ (MG + CG) * EF :=
    mul_le_mul (add_le_add hmG hcG) hEF (abs_nonneg eF)
      (add_nonneg hMG hCG)
  have heFeG : |eF| * |eG| ≤ EF * EG :=
    mul_le_mul hEF hEG (abs_nonneg eG) hEF0
  calc
    |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
      |mu.covariance F G| + |mu.covarianceThirdCentered F G S| +
        |cF| * |cG| + |eFG| + (|mF| + |cF|) * |eG| +
        (|mG| + |cG|) * |eF| + |eF| * |eG| := by
      calc
        _ ≤ |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := htri
        _ = |mu.covariance F G| +
            |mu.covarianceThirdCentered F G S| +
            |cF| * |cG| + |eFG| + |mF + cF| * |eG| +
            |mG + cG| * |eF| + |eF| * |eG| := htriExpanded
        _ ≤ |mu.covariance F G| +
            |mu.covarianceThirdCentered F G S| +
            |cF| * |cG| + |eFG| + (|mF| + |cF|) * |eG| +
            (|mG| + |cG|) * |eF| + |eF| * |eG| := by
          have h4 := mul_le_mul_of_nonneg_right (abs_add_le mF cF)
            (abs_nonneg eG)
          have h5 := mul_le_mul_of_nonneg_right (abs_add_le mG cG)
            (abs_nonneg eF)
          linarith
    _ ≤ Czero + Cthird + CF * CG + EFG +
        (MF + CF) * EG + (MG + CG) * EF + EF * EG := by
      linarith

/-- Explicit fixed-box analogue of the raw moving-prefix Taylor ledger. -/
def rawTiltPrefixTaylorBoundFixedBox
    (K a MF RFone Czero Cthird : ℝ) : ℝ :=
  let D := fixedBoxQuadraticConstant K
  let Rone := K * a
  let RF := K * RFone
  let CF := RFone + MF * a
  let CG := 2 * a
  let EF := 2 * D * (RF + CF * a + (MF + CF) * Rone)
  let EG := 2 * D * (Rone + CG * a + (1 + CG) * Rone)
  let EFG := EF
  Czero + Cthird + CF * CG + EFG +
    (MF + CF) * EG + (1 + CG) * EF + EF * EG

theorem rawTiltPrefixTaylorBoundFixedBox_nonneg
    {K a MF RFone Czero Cthird : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hMF : 0 ≤ MF)
    (hRFone : 0 ≤ RFone) (hCzero : 0 ≤ Czero)
    (hCthird : 0 ≤ Cthird) :
    0 ≤ rawTiltPrefixTaylorBoundFixedBox
      K a MF RFone Czero Cthird := by
  unfold rawTiltPrefixTaylorBoundFixedBox
  dsimp only
  have hD : 0 ≤ fixedBoxQuadraticConstant K :=
    zero_le_one.trans (one_le_fixedBoxQuadraticConstant hK)
  positivity

/-- Ready-to-use fixed-box Taylor estimate for a nonnegative marked
statistic and a prefix indicator.  All second moments are derived from
`|S| ≤ K`; no unit-box restriction remains. -/
theorem abs_exponentialTilt_covariance_nonneg_prefix_le_of_moments_fixedBox
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ)
    {K a MF RFone Czero Cthird : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hMF : 0 ≤ MF)
    (hRFone : 0 ≤ RFone)
    (hscore : ∀ omega, |S omega| ≤ K)
    (hsmall : fixedBoxLinearConstant K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hF0 : ∀ omega, 0 ≤ F omega)
    (hmeanF : mu.expect F ≤ MF)
    (hG0 : ∀ omega, 0 ≤ G omega)
    (hG1 : ∀ omega, G omega ≤ 1)
    (hmarkedFirst :
      mu.expect (fun omega ↦ |F omega| * |S omega|) ≤ RFone)
    (hbase : |mu.covariance F G| ≤ Czero)
    (hthird : |mu.covarianceThirdCentered F G S| ≤ Cthird) :
    |(mu.exponentialTilt S).covariance F G| ≤
      rawTiltPrefixTaylorBoundFixedBox
        K a MF RFone Czero Cthird := by
  let Rone := K * a
  let RF := K * RFone
  let CF := RFone + MF * a
  let CG := 2 * a
  have hRone : 0 ≤ Rone := by dsimp only [Rone]; positivity
  have hRF : 0 ≤ RF := by dsimp only [RF]; positivity
  have hCF : 0 ≤ CF := by dsimp only [CF]; positivity
  have hCG : 0 ≤ CG := by dsimp only [CG]; positivity
  have hmeanF0 : 0 ≤ mu.expect F := mu.expect_nonneg F hF0
  have hmeanFabs : |mu.expect F| ≤ MF := by
    rw [abs_of_nonneg hmeanF0]
    exact hmeanF
  have hmeanG0 : 0 ≤ mu.expect G := mu.expect_nonneg G hG0
  have hmeanGle : mu.expect G ≤ 1 := by
    calc
      mu.expect G ≤ mu.expect (fun _ ↦ (1 : ℝ)) :=
        mu.expect_mono G _ hG1
      _ = 1 := by
        unfold expect
        rw [← Finset.sum_mul, mu.mass_sum, one_mul]
  have hmeanGabs : |mu.expect G| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hmeanG0]
    exact hmeanGle
  have hFG0 : ∀ omega, 0 ≤ F omega * G omega := fun omega ↦
    mul_nonneg (hF0 omega) (hG0 omega)
  have hFGle : ∀ omega, F omega * G omega ≤ F omega := by
    intro omega
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hG1 omega) (hF0 omega)
  have hmeanFG0 : 0 ≤ mu.expect (fun omega ↦ F omega * G omega) :=
    mu.expect_nonneg _ hFG0
  have hmeanFGle : mu.expect (fun omega ↦ F omega * G omega) ≤ MF :=
    (mu.expect_mono _ F hFGle).trans hmeanF
  have hmeanFGabs :
      |mu.expect (fun omega ↦ F omega * G omega)| ≤ MF := by
    rw [abs_of_nonneg hmeanFG0]
    exact hmeanFGle
  have hFabsPoint : (fun omega ↦ |F omega|) = F := by
    funext omega
    exact abs_of_nonneg (hF0 omega)
  have hGabsPoint : (fun omega ↦ |G omega|) = G := by
    funext omega
    exact abs_of_nonneg (hG0 omega)
  have hcovF : |mu.covariance F S| ≤ CF := by
    have hraw := mu.abs_covariance_le_expect_abs_mul_add F S
    rw [hFabsPoint] at hraw
    calc
      |mu.covariance F S| ≤
          mu.expect (fun omega ↦ |F omega| * |S omega|) +
            mu.expect F * mu.expect (fun omega ↦ |S omega|) := hraw
      _ ≤ RFone + MF * a := by
        exact add_le_add hmarkedFirst
          (mul_le_mul hmeanF habsScore
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) hMF)
      _ = CF := by rfl
  have hmarkedG : mu.expect (fun omega ↦ |G omega| * |S omega|) ≤ a := by
    calc
      mu.expect (fun omega ↦ |G omega| * |S omega|) ≤
          mu.expect (fun omega ↦ |S omega|) := by
        apply mu.expect_mono
        intro omega
        rw [abs_of_nonneg (hG0 omega)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hG1 omega) (abs_nonneg (S omega))
      _ ≤ a := habsScore
  have hcovG : |mu.covariance G S| ≤ CG := by
    have hraw := mu.abs_covariance_le_expect_abs_mul_add G S
    rw [hGabsPoint] at hraw
    calc
      |mu.covariance G S| ≤
          mu.expect (fun omega ↦ |G omega| * |S omega|) +
            mu.expect G * mu.expect (fun omega ↦ |S omega|) := hraw
      _ ≤ a + 1 * a := by
        exact add_le_add hmarkedG
          (mul_le_mul hmeanGle habsScore
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) zero_le_one)
      _ = CG := by dsimp only [CG]; ring
  have hmarkedFG :
      mu.expect (fun omega ↦ |F omega * G omega| * |S omega|) ≤
        RFone := by
    calc
      mu.expect (fun omega ↦ |F omega * G omega| * |S omega|) ≤
          mu.expect (fun omega ↦ |F omega| * |S omega|) := by
        apply mu.expect_mono
        intro omega
        rw [abs_mul, abs_of_nonneg (hG0 omega)]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hG1 omega) (abs_nonneg (F omega)))
          (abs_nonneg (S omega))
      _ ≤ RFone := hmarkedFirst
  have hcovFG :
      |mu.covariance (fun omega ↦ F omega * G omega) S| ≤ CF := by
    have hraw := mu.abs_covariance_le_expect_abs_mul_add
      (fun omega ↦ F omega * G omega) S
    calc
      |mu.covariance (fun omega ↦ F omega * G omega) S| ≤
          mu.expect (fun omega ↦ |F omega * G omega| * |S omega|) +
            mu.expect (fun omega ↦ |F omega * G omega|) *
              mu.expect (fun omega ↦ |S omega|) := hraw
      _ ≤ RFone + MF * a := by
        rw [show (fun omega ↦ |F omega * G omega|) =
            fun omega ↦ F omega * G omega by
          funext omega
          exact abs_of_nonneg (hFG0 omega)]
        exact add_le_add hmarkedFG
          (mul_le_mul hmeanFGle habsScore
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) hMF)
      _ = CF := by rfl
  have hscoreSqPoint (omega : Omega) : S omega ^ 2 ≤ K * |S omega| := by
    calc
      S omega ^ 2 = |S omega| ^ 2 := (sq_abs (S omega)).symm
      _ = |S omega| * |S omega| := pow_two _
      _ ≤ K * |S omega| :=
        mul_le_mul_of_nonneg_right (hscore omega) (abs_nonneg (S omega))
  have hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone := by
    calc
      mu.expect (fun omega ↦ S omega ^ 2) ≤
          mu.expect (fun omega ↦ K * |S omega|) :=
        mu.expect_mono _ _ hscoreSqPoint
      _ = K * mu.expect (fun omega ↦ |S omega|) := by
        unfold expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro omega homega
        ring
      _ ≤ K * a := mul_le_mul_of_nonneg_left habsScore hK
      _ = Rone := rfl
  have hmarkedSqF :
      mu.expect (fun omega ↦ |F omega| * S omega ^ 2) ≤ RF := by
    calc
      mu.expect (fun omega ↦ |F omega| * S omega ^ 2) ≤
          mu.expect (fun omega ↦ K * (|F omega| * |S omega|)) := by
        apply mu.expect_mono
        intro omega
        calc
          |F omega| * S omega ^ 2 ≤
              |F omega| * (K * |S omega|) :=
            mul_le_mul_of_nonneg_left (hscoreSqPoint omega)
              (abs_nonneg (F omega))
          _ = K * (|F omega| * |S omega|) := by ring
      _ = K * mu.expect (fun omega ↦ |F omega| * |S omega|) := by
        unfold expect
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro omega homega
        ring
      _ ≤ K * RFone := mul_le_mul_of_nonneg_left hmarkedFirst hK
      _ = RF := rfl
  have hmarkedSqG :
      mu.expect (fun omega ↦ |G omega| * S omega ^ 2) ≤ Rone := by
    calc
      mu.expect (fun omega ↦ |G omega| * S omega ^ 2) ≤
          mu.expect (fun omega ↦ S omega ^ 2) := by
        apply mu.expect_mono
        intro omega
        rw [abs_of_nonneg (hG0 omega)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hG1 omega) (sq_nonneg (S omega))
      _ ≤ Rone := hscoreSq
  have hmarkedSqFG :
      mu.expect (fun omega ↦ |F omega * G omega| * S omega ^ 2) ≤ RF := by
    calc
      mu.expect (fun omega ↦ |F omega * G omega| * S omega ^ 2) ≤
          mu.expect (fun omega ↦ |F omega| * S omega ^ 2) := by
        apply mu.expect_mono
        intro omega
        rw [abs_mul, abs_of_nonneg (hG0 omega)]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hG1 omega) (abs_nonneg (F omega)))
          (sq_nonneg (S omega))
      _ ≤ RF := hmarkedSqF
  have hresult :=
    mu.abs_exponentialTilt_covariance_le_of_centeredTaylor_expect_bounds_fixedBox
      F G S hK ha hRone hMF zero_le_one hMF hRF hRone hRF
      hCF hCG hCF hscore hsmall habsScore hscoreSq hmeanFabs
      hmeanGabs hmeanFGabs hmarkedSqF hmarkedSqG hmarkedSqFG
      hcovF hcovG hcovFG hbase hthird
  simpa only [rawTiltPrefixTaylorBoundFixedBox, Rone, RF, CF, CG]
    using hresult

end FiniteProbability

end

end Erdos390.Full
