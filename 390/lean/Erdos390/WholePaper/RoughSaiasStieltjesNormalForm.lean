import Erdos390.WholePaper.RoughSaiasContinuousBuchstab
import Erdos390.WholePaper.RoughSaiasBaseChange

/-!
# Identification of the finite signed functional with the Saias normal form

This file performs the finite integration-by-parts calculation that was
deliberately absent from `RoughSaiasNormalization`.  The atom part is
handled by the corner-safe right-derivative Abel theorem.  Its density term
cancels the quotient-rule part of that derivative before any estimate is
taken.  What remains splits exactly as

* a smooth Dickman FTC term, and
* the signed base-free fractional correction already formalized in
  `RoughSaiasBaseChange`.

Thus the explicit atom-minus-density functional is identified with the
existing normal form at a positive natural endpoint without assuming any
defect or endpoint estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## The exact density cancellation -/

/-- The single floor kernel left after the Abel derivative and the
absolutely continuous Stieltjes density are combined. -/
noncomputable def roughSaiasStieltjesFloorCorrection
    (X : ℕ) (y t : ℝ) : ℝ :=
  (X : ℝ) * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
    (((⌊t⌋₊ : ℕ) : ℝ)) /
      (t ^ 2 * Real.log y)

/-- Its smooth part, obtained by replacing `floor t` by `t`. -/
noncomputable def roughSaiasStieltjesSmoothCorrection
    (X : ℕ) (y t : ℝ) : ℝ :=
  (X : ℝ) * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate (X : ℝ) y t) /
    (t * Real.log y)

/-- Its signed fractional part.  This is subtracted from the smooth part. -/
noncomputable def roughSaiasStieltjesFractionalCorrection
    (X : ℕ) (y t : ℝ) : ℝ :=
  (X : ℝ) * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
    Int.fract t / (t ^ 2 * Real.log y)

theorem roughSaiasNatFloor_cast_eq_sub_fract
    {t : ℝ} (ht : 0 ≤ t) :
    (((⌊t⌋₊ : ℕ) : ℝ)) = t - Int.fract t := by
  rw [Int.self_sub_fract,
    ← natCast_floor_eq_intCast_floor ht]

/-- Pointwise `floor = t - fract` inside the remaining signed kernel. -/
theorem roughSaiasStieltjesFloorCorrection_eq_smooth_sub_fractional
    {X : ℕ} {y t : ℝ} (ht : 0 < t) (hy : 1 < y) :
    roughSaiasStieltjesFloorCorrection X y t =
      roughSaiasStieltjesSmoothCorrection X y t -
        roughSaiasStieltjesFractionalCorrection X y t := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have ht0 : t ≠ 0 := ht.ne'
  unfold roughSaiasStieltjesFloorCorrection
    roughSaiasStieltjesSmoothCorrection
    roughSaiasStieltjesFractionalCorrection
  rw [roughSaiasNatFloor_cast_eq_sub_fract ht.le]
  field_simp [ht0, hlogy]

/-- The quotient-rule `rho/t²` term in the right Abel derivative cancels
the entire absolutely continuous floor density. -/
theorem roughSaiasStieltjesDerivativeFloor_add_density
    {X : ℕ} {y t : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (ht : 0 < t) (htX : t ≤ (X : ℝ)) :
    roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
          (((⌊t⌋₊ : ℕ) : ℝ)) +
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
          roughSaiasFloorDensity t =
      -roughSaiasStieltjesFloorCorrection X y t := by
  have hXR : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have ht0 : t ≠ 0 := ht.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_test
    hXR hy ht htX]
  unfold roughSaiasStieltjesTestRightDerivative
    roughSaiasStieltjesTest roughSaiasFloorDensity
    roughSaiasStieltjesFloorCorrection
  field_simp [ht0, hlogy]
  ring

theorem roughSaiasPositiveIncrement_prefix (N : ℕ) :
    (∑ k ∈ Finset.Icc 0 N,
      FriableAsymptotic.positiveIncrement k) = (N : ℝ) := by
  have hfin : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hfin]
  exact FriableAsymptotic.sum_range_positiveIncrement N

/-- Integrability of the derivative-times-floor term follows directly from
the generic Abel-summation integrability lemma. -/
theorem integrableOn_roughSaiasStieltjesDerivative_mul_floor
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
          (((⌊t⌋₊ : ℕ) : ℝ)))
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hint := integrableOn_roughSaiasStieltjesTestRightDerivative
    hX hy hu5
  have hmul := integrableOn_mul_sum_Icc
    FriableAsymptotic.positiveIncrement (a := (1 : ℝ))
      (b := (X : ℝ)) (m := 0) (by norm_num) hint
  have hmul' := hmul.mono_set Set.Ioc_subset_Icc_self
  simpa only [roughSaiasPositiveIncrement_prefix] using hmul'

/-- The density is measurable and bounded by the natural endpoint on its
compact support. -/
theorem integrableOn_roughSaiasStieltjesProfile_mul_floorDensity
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
          roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXnonneg : (0 : ℝ) ≤ (X : ℝ) := by positivity
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
        roughSaiasFloorDensity t) :=
    (measurable_roughSaiasStieltjesDickmanProfile (X : ℝ) y).mul
      measurable_roughSaiasFloorDensity
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ (X : ℝ))
      volume (1 : ℝ) (X : ℝ) :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
        roughSaiasFloorDensity t) volume (1 : ℝ) (X : ℝ) := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa only [Set.uIcc_of_le hXR] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hcoord5 := hcoord.2.trans hu5
    have hcoordEq := roughSaiasStieltjesCoordinate_eq_log_div
      (x := (X : ℝ)) (y := y) (t := t)
      (by exact_mod_cast (show 0 < X by omega)) htpos
    have hcoordLog5 :
        Real.log ((X : ℝ) / t) / Real.log y ≤ 5 := by
      rw [← hcoordEq]
      exact hcoord5
    have hzeroRho :=
      roughSaiasZeroExtendedRho_mem_unitInterval hcoordLog5
    have hprofile0 : 0 ≤
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t := by
      unfold roughSaiasStieltjesDickmanProfile
      exact mul_nonneg hXnonneg hzeroRho.1
    have hprofileX :
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t ≤ (X : ℝ) := by
      unfold roughSaiasStieltjesDickmanProfile
      exact (mul_le_mul_of_nonneg_left hzeroRho.2 hXnonneg).trans_eq
        (mul_one _)
    have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by
      positivity
    have hfloorLe : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t :=
      Nat.floor_le htpos.le
    have hdenom : 0 < t ^ 2 := sq_pos_of_pos htpos
    have hdensity0 : 0 ≤ roughSaiasFloorDensity t := by
      unfold roughSaiasFloorDensity
      exact div_nonneg hfloor0 hdenom.le
    have hdensity1 : roughSaiasFloorDensity t ≤ 1 := by
      unfold roughSaiasFloorDensity
      apply (div_le_one hdenom).2
      have hquad : 0 ≤ t * (t - 1) :=
        mul_nonneg htpos.le (sub_nonneg.mpr htI.1)
      exact hfloorLe.trans (by nlinarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hprofile0 hdensity0)]
    calc
      roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
          roughSaiasFloorDensity t ≤
        roughSaiasStieltjesDickmanProfile (X : ℝ) y t * 1 :=
          mul_le_mul_of_nonneg_left hdensity1 hprofile0
      _ ≤ (X : ℝ) * 1 :=
        mul_le_mul_of_nonneg_right hprofileX (by norm_num)
      _ = (X : ℝ) := mul_one _
  have hintIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hint
  exact hintIcc.mono_set Set.Ioc_subset_Icc_self

/-- The capped signed functional is the natural endpoint plus the one
remaining signed floor correction. -/
theorem roughSaiasLambdaStieltjesWithCutoff_nat_eq_add_floorCorrection
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) y =
      (X : ℝ) +
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          roughSaiasStieltjesFloorCorrection X y t := by
  have hderiv := integrableOn_roughSaiasStieltjesDerivative_mul_floor
    hX hy hu5
  have hdensity := integrableOn_roughSaiasStieltjesProfile_mul_floorDensity
    hX hy hu5
  rw [roughSaiasLambdaStieltjesWithCutoff_nat_eq_test_sub_density hX hy,
    roughSaiasStieltjesTest_sum_eq_endpoint_sub_integral hX hy hu5]
  unfold roughSaiasStieltjesDensityPart
  have hadd := MeasureTheory.integral_add hderiv hdensity
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          (roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
              (((⌊t⌋₊ : ℕ) : ℝ)) +
            roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
              roughSaiasFloorDensity t)) =
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          -roughSaiasStieltjesFloorCorrection X y t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasStieltjesDerivativeFloor_add_density hX hy
      (zero_lt_one.trans ht.1) ht.2
  calc
    (X : ℝ) -
          (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
              (((⌊t⌋₊ : ℕ) : ℝ))) -
          (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
              roughSaiasFloorDensity t) =
        (X : ℝ) -
          ((∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
              roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
                (((⌊t⌋₊ : ℕ) : ℝ))) +
            (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
              roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
                roughSaiasFloorDensity t)) := by ring
    _ = (X : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            (roughSaiasStieltjesTestRightDerivative (X : ℝ) y t *
                (((⌊t⌋₊ : ℕ) : ℝ)) +
              roughSaiasStieltjesDickmanProfile (X : ℝ) y t *
                roughSaiasFloorDensity t) := by rw [hadd]
    _ = (X : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            -roughSaiasStieltjesFloorCorrection X y t := by rw [hpoint]
    _ = (X : ℝ) +
          ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
            roughSaiasStieltjesFloorCorrection X y t := by
      rw [MeasureTheory.integral_neg]
      ring

/-! ## Evaluation of the smooth part -/

/-- Multiplying the Abel test by `t/x` recovers `rho` and transfers its
corner-safe right derivative to the logarithmic coordinate. -/
theorem hasDerivWithinAt_roughSaiasRhoCoordinate_right
    {x y t : ℝ} (hy : 1 < y) (ht1 : 1 ≤ t) (htx : t ≤ x)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    HasDerivWithinAt
      (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
      (roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y)))
      (Set.Ioi t) t := by
  have htpos : 0 < t := zero_lt_one.trans_le ht1
  have ht0 : t ≠ 0 := htpos.ne'
  have hxpos : 0 < x := htpos.trans_le htx
  have hx0 : x ≠ 0 := hxpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have htest := hasDerivWithinAt_roughSaiasStieltjesTest_right
    hy ht1 htx hu5
  have hprod := (hasDerivAt_id t).hasDerivWithinAt.mul htest
  have hquot := hprod.div_const x
  have heq :
      (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        =ᶠ[nhdsWithin t (Set.Ioi t)]
      (fun s : ℝ ↦ s * roughSaiasStieltjesTest x y s / x) := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hspos : 0 < s := htpos.trans hs
    unfold roughSaiasStieltjesTest
    field_simp [hspos.ne', hx0]
  have hvalue :
      rho (roughSaiasStieltjesCoordinate x y t) =
        t * roughSaiasStieltjesTest x y t / x := by
    unfold roughSaiasStieltjesTest
    field_simp [ht0, hx0]
  have hcongr := hquot.congr_of_eventuallyEq heq hvalue
  convert hcongr using 1
  simp only [id_eq]
  unfold roughSaiasStieltjesTest
    roughSaiasStieltjesTestRightDerivative
  field_simp [ht0, hx0, hlogy]
  ring

theorem continuousOn_roughSaiasRhoCoordinate
    {x y A B : ℝ} (_hy : 1 < y) (hA : 0 < A) :
    ContinuousOn
      (fun t : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y t))
      (Set.Icc A B) := by
  intro t ht
  have ht0 : t ≠ 0 := (hA.trans_le ht.1).ne'
  have hcoord : ContinuousAt (roughSaiasStieltjesCoordinate x y) t := by
    unfold roughSaiasStieltjesCoordinate
    exact (continuousAt_const.sub (Real.continuousAt_log ht0)).div_const _
  exact (continuous_rho.continuousAt.comp hcoord).continuousWithinAt

/-- The logarithmic-coordinate right derivative is integrable on the
compact natural interval. -/
theorem integrableOn_roughSaiasRhoCoordinateRightDerivative
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y)))
      (Set.Icc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
        (-1 / (t * Real.log y))) :=
    (measurable_roughSaiasOpenFaceDickmanDerivative.comp
      (measurable_roughSaiasStieltjesCoordinate (X : ℝ) y)).mul
        (measurable_const.div (measurable_id.mul measurable_const))
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ 1 / Real.log y)
      volume (1 : ℝ) (X : ℝ) :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
        (-1 / (t * Real.log y)))
      volume (1 : ℝ) (X : ℝ) := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa only [Set.uIcc_of_le hXR] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hD := roughSaiasOpenFaceDickmanDerivative_abs_le_one
      (hcoord.2.trans hu5)
    have hdenom : 0 < t * Real.log y := mul_pos htpos hlogy
    have hinv : 1 / (t * Real.log y) ≤ 1 / Real.log y := by
      apply one_div_le_one_div_of_le hlogy
      nlinarith [mul_le_mul_of_nonneg_right htI.1 hlogy.le]
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_neg, abs_one,
      abs_of_pos hdenom]
    calc
      |roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate (X : ℝ) y t)| *
          (1 / (t * Real.log y)) ≤
        1 * (1 / (t * Real.log y)) :=
          mul_le_mul_of_nonneg_right hD (by positivity)
      _ ≤ 1 * (1 / Real.log y) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 1 / Real.log y := one_mul _
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hint

/-- FTC for the Dickman coordinate, with the corner at coordinate `1`
handled by the right derivative rather than discarded. -/
theorem integral_roughSaiasRhoCoordinateRightDerivative
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    (∫ t in (1 : ℝ)..(X : ℝ),
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y))) =
      1 - rho (Real.log (X : ℝ) / Real.log y) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcont := continuousOn_roughSaiasRhoCoordinate
    (x := (X : ℝ)) (y := y) (A := (1 : ℝ)) (B := (X : ℝ))
    hy (by norm_num)
  have hright : ∀ t ∈ Set.Ioo (1 : ℝ) (X : ℝ),
      HasDerivWithinAt
        (fun s : ℝ ↦ rho
          (roughSaiasStieltjesCoordinate (X : ℝ) y s))
        (roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y)))
        (Set.Ioi t) t := by
    intro t ht
    exact hasDerivWithinAt_roughSaiasRhoCoordinate_right hy ht.1.le
      ht.2.le hu5
  have hintIcc := integrableOn_roughSaiasRhoCoordinateRightDerivative
    hX hy hu5
  have hint : IntervalIntegrable
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
          (-1 / (t * Real.log y)))
      volume (1 : ℝ) (X : ℝ) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mpr hintIcc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hXR hcont hright hint
  simpa [roughSaiasStieltjesCoordinate] using hftc

/-- Exact value of the smooth contribution to the floor correction. -/
theorem integral_roughSaiasStieltjesSmoothCorrection
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
        roughSaiasStieltjesSmoothCorrection X y t) =
      (X : ℝ) *
        (rho (Real.log (X : ℝ) / Real.log y) - 1) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [← intervalIntegral.integral_of_le hXR]
  have heq :
      (∫ t in (1 : ℝ)..(X : ℝ),
          roughSaiasStieltjesSmoothCorrection X y t) =
        ∫ t in (1 : ℝ)..(X : ℝ),
          (-(X : ℝ)) *
            (roughSaiasOpenFaceDickmanDerivative
                (roughSaiasStieltjesCoordinate (X : ℝ) y t) *
              (-1 / (t * Real.log y))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa [Set.uIcc_of_le hXR] using ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le htI.1).ne'
    unfold roughSaiasStieltjesSmoothCorrection
    field_simp [ht0, hlogy]
  rw [heq, intervalIntegral.integral_const_mul,
    integral_roughSaiasRhoCoordinateRightDerivative hX hy hu5]
  ring

theorem integrableOn_roughSaiasStieltjesSmoothCorrection
    {X : ℕ} {y : ℝ} (hX : 1 ≤ X) (hy : 1 < y)
    (hu5 : Real.log (X : ℝ) / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasStieltjesSmoothCorrection X y)
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hbase :=
    (integrableOn_roughSaiasRhoCoordinateRightDerivative hX hy hu5).mono_set
      Set.Ioc_subset_Icc_self
  have hmul := hbase.const_mul (-(X : ℝ))
  apply IntegrableOn.congr_fun_ae hmul
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have htpos : 0 < t := zero_lt_one.trans ht.1
  have ht0 : t ≠ 0 := htpos.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  unfold roughSaiasStieltjesSmoothCorrection
  field_simp [ht0, hlogy]

/-! ## Identification of the signed fractional part -/

/-- The five-face hypothesis places the natural endpoint below the
artificial base-change cap `Y^5`. -/
theorem roughSaias_natCast_le_rpow_five
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    (X : ℝ) ≤ (Y : ℝ) ^ (5 : ℝ) := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hYpos : 0 < (Y : ℝ) := by positivity
  have hYone : 1 < (Y : ℝ) := by exact_mod_cast (show 1 < Y by omega)
  have hlogY : 0 < Real.log (Y : ℝ) := Real.log_pos hYone
  have hlogX : Real.log (X : ℝ) ≤
      5 * Real.log (Y : ℝ) := (div_le_iff₀ hlogY).mp hu5
  have hpowpos : 0 < (Y : ℝ) ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos hYpos 5
  apply (Real.log_le_log_iff hXpos hpowpos).mp
  rw [Real.log_rpow hYpos]
  exact hlogX

/-- The base-free correction may be capped at `X` rather than `Y^5`, since
its Dickman derivative is already zero above `X/Y`. -/
theorem roughSaiasBaseFreeFractionalIntegral_eq_natCap
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral X Y =
      ∫ t in (1 : ℝ)..(X : ℝ),
        roughSaiasBaseFreeFractionalKernel X Y t := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcap := roughSaias_natCast_le_rpow_five hX hY hu5
  have h1cap : (1 : ℝ) ≤ (Y : ℝ) ^ (5 : ℝ) :=
    hXR.trans hcap
  have hXmem : (X : ℝ) ∈
      Set.uIcc (1 : ℝ) ((Y : ℝ) ^ (5 : ℝ)) := by
    rw [Set.uIcc_of_le h1cap]
    exact ⟨hXR, hcap⟩
  have hint := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X) (m := Y) hY hu5
  have hparts := (IntervalIntegrable.trans_iff hXmem).mp hint
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hYone : 1 < (Y : ℝ) := by exact_mod_cast (show 1 < Y by omega)
  have hdivlt : (X : ℝ) / (Y : ℝ) < (X : ℝ) :=
    div_lt_self hXpos hYone
  have htail :
      (∫ t in (X : ℝ)..(Y : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel X Y t) = 0 := by
    calc
      _ = ∫ _t in (X : ℝ)..(Y : ℝ) ^ (5 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈
            Set.Icc (X : ℝ) ((Y : ℝ) ^ (5 : ℝ)) := by
          rw [Set.uIcc_of_le hcap] at ht
          exact ht
        exact roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt
          hX hY (hdivlt.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hparts.1 hparts.2
  unfold roughSaiasBaseFreeFractionalIntegral
  rw [← hsplit, htail, add_zero]

/-- Away from the unique point `t=X/Y`, the open-face fractional
integrand is exactly `X` times the existing base-free kernel. -/
theorem roughSaiasStieltjesFractionalCorrection_eq_baseFree_of_ne
    {X Y : ℕ} {t : ℝ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (ht : 0 < t) (hne : t ≠ (X : ℝ) / (Y : ℝ)) :
    roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t =
      (X : ℝ) * roughSaiasBaseFreeFractionalKernel X Y t := by
  have hXpos : 0 < (X : ℝ) := by
    exact_mod_cast (show 0 < X by omega)
  have hYpos : 0 < (Y : ℝ) := by positivity
  have hlogY : Real.log (Y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
  have hcoordEq : roughSaiasStieltjesCoordinate (X : ℝ) (Y : ℝ) t =
      roughSaiasBaseFreeDickmanCoordinate X Y t := by
    rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
    rfl
  have hcoordNe :
      roughSaiasStieltjesCoordinate (X : ℝ) (Y : ℝ) t ≠ 1 := by
    intro hcoord
    have hlogEq : Real.log (X : ℝ) - Real.log t =
        Real.log (Y : ℝ) := by
      unfold roughSaiasStieltjesCoordinate at hcoord
      field_simp [hlogY] at hcoord
      linarith
    have hlogDiv : Real.log ((X : ℝ) / (Y : ℝ)) =
        Real.log (X : ℝ) - Real.log (Y : ℝ) := by
      rw [Real.log_div hXpos.ne' hYpos.ne']
    have hlogs : Real.log t =
        Real.log ((X : ℝ) / (Y : ℝ)) := by
      rw [hlogDiv]
      linarith
    have hexp := congrArg Real.exp hlogs
    rw [Real.exp_log ht,
      Real.exp_log (div_pos hXpos hYpos)] at hexp
    exact hne hexp
  unfold roughSaiasStieltjesFractionalCorrection
    roughSaiasBaseFreeFractionalKernel
  rw [hcoordEq,
    roughSaiasOpenFaceDickmanDerivative_eq_roughSaias
      (hcoordEq ▸ hcoordNe)]
  unfold roughSaiasBaseFreeDickmanCoordinate
  field_simp [ht.ne', hlogY]

theorem integrableOn_roughSaiasStieltjesFractionalCorrection
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    IntegrableOn (roughSaiasStieltjesFractionalCorrection X (Y : ℝ))
      (Set.Ioc (1 : ℝ) (X : ℝ)) := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hcap := roughSaias_natCast_le_rpow_five hX hY hu5
  have hfull := roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    (q := X) (m := Y) hY hu5
  have hcapInt : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel X Y) volume
      (1 : ℝ) (X : ℝ) := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hXR,
      Set.uIcc_of_le (hXR.trans hcap)]
    exact Set.Icc_subset_Icc le_rfl hcap
  have hbaseIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hXR).mp hcapInt
  have hbaseIccMul : IntegrableOn
      (fun t : ℝ => (X : ℝ) * roughSaiasBaseFreeFractionalKernel X Y t)
      (Set.Icc (1 : ℝ) (X : ℝ)) :=
    hbaseIcc.const_mul (X : ℝ)
  have hbase := hbaseIccMul.mono_set Set.Ioc_subset_Icc_self
  apply IntegrableOn.congr_fun_ae hbase
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [((volume : Measure ℝ).ae_ne
    ((X : ℝ) / (Y : ℝ)))] with t hne ht
  exact (roughSaiasStieltjesFractionalCorrection_eq_baseFree_of_ne
    hX hY (zero_lt_one.trans ht.1) hne).symm

/-- Exact value of the fractional contribution. -/
theorem integral_roughSaiasStieltjesFractionalCorrection
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
        roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t) =
      (X : ℝ) * roughSaiasBaseFreeFractionalIntegral X Y := by
  have hXR : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  rw [← intervalIntegral.integral_of_le hXR]
  have heq :
      (∫ t in (1 : ℝ)..(X : ℝ),
          roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t) =
        ∫ t in (1 : ℝ)..(X : ℝ),
          (X : ℝ) * roughSaiasBaseFreeFractionalKernel X Y t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [((volume : Measure ℝ).ae_ne
      ((X : ℝ) / (Y : ℝ)))] with t hne ht
    have htI : t ∈ Set.Icc (1 : ℝ) (X : ℝ) := by
      simpa only [Set.uIcc_of_le hXR] using Set.uIoc_subset_uIcc ht
    exact roughSaiasStieltjesFractionalCorrection_eq_baseFree_of_ne
      hX hY (zero_lt_one.trans_le htI.1) hne
  rw [heq, intervalIntegral.integral_const_mul,
    ← roughSaiasBaseFreeFractionalIntegral_eq_natCap hX hY hu5]

/-! ## Final natural-endpoint identification -/

/-- The compact atom-minus-density definition and the existing finite
Saias normal form are exactly equal at every positive natural endpoint on
the five constructed faces. -/
theorem roughSaiasLambdaStieltjesWithCutoff_nat_eq_normalForm
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjesWithCutoff X (X : ℝ) (Y : ℝ) =
      roughSaiasLambdaNormalForm (X : ℝ) Y := by
  have hsmooth := integrableOn_roughSaiasStieltjesSmoothCorrection
    hX (by exact_mod_cast (show 1 < Y by omega)) hu5
  have hfract := integrableOn_roughSaiasStieltjesFractionalCorrection
    hX hY hu5
  have hsplit := MeasureTheory.integral_sub hsmooth hfract
  rw [roughSaiasLambdaStieltjesWithCutoff_nat_eq_add_floorCorrection
      hX (by exact_mod_cast (show 1 < Y by omega)) hu5]
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          roughSaiasStieltjesFloorCorrection X (Y : ℝ) t) =
        ∫ t in Set.Ioc (1 : ℝ) (X : ℝ),
          (roughSaiasStieltjesSmoothCorrection X (Y : ℝ) t -
            roughSaiasStieltjesFractionalCorrection X (Y : ℝ) t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasStieltjesFloorCorrection_eq_smooth_sub_fractional
      (zero_lt_one.trans ht.1)
      (by exact_mod_cast (show 1 < Y by omega))
  rw [hpoint, hsplit,
    integral_roughSaiasStieltjesSmoothCorrection hX
      (by exact_mod_cast (show 1 < Y by omega)) hu5,
    integral_roughSaiasStieltjesFractionalCorrection hX hY hu5]
  rw [← roughSaiasNaturalMain_eq_lambdaNormalForm,
    roughSaiasNaturalMain_eq_rho_sub_baseFree hY]
  ring

/-- Canonical-cap version of the same natural-endpoint identity. -/
theorem roughSaiasLambdaStieltjes_nat_eq_normalForm
    {X Y : ℕ} (hX : 1 ≤ X) (hY : 2 ≤ Y)
    (hu5 : Real.log (X : ℝ) / Real.log (Y : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjes (X : ℝ) (Y : ℝ) =
      roughSaiasLambdaNormalForm (X : ℝ) Y := by
  rw [roughSaiasLambdaStieltjes_nat]
  exact roughSaiasLambdaStieltjesWithCutoff_nat_eq_normalForm hX hY hu5

end

end Erdos390.WholePaper
