import Erdos390.WholePaper.RoughSaiasContinuousBuchstab
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Lifting pointwise continuous Buchstab through the finite signed functional

The pointwise identity in `RoughSaiasContinuousBuchstab` is now lifted
through the finite atom-minus-density functional.  The finite atomic swap is
proved unconditionally.  The density swap is stated with its exact compact
Fubini datum; that datum is ordinary product integrability of an explicit
bounded measurable kernel, not an endpoint or defect estimate.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full.DickmanBasic

noncomputable section

/-- The compact two-variable density kernel in the Fubini step. -/
noncomputable def roughSaiasBuchstabDensityKernel
    (x : ℝ) (s t : ℝ) : ℝ :=
  roughSaiasContinuousBuchstabProfile x s t *
    roughSaiasFloorDensity t

/-- The precise ordinary-integrability datum needed for the density
Fubini swap.  No counting function, normal-form defect, or error bound
occurs here. -/
def RoughSaiasBuchstabDensityFubini
    (R : ℕ) (x y z : ℝ) : Prop :=
  IntegrableOn
      (fun t ↦ roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)) ∧
    IntegrableOn
      (fun t ↦ roughSaiasStieltjesDickmanProfile x z t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)) ∧
    Integrable (Function.uncurry (roughSaiasBuchstabDensityKernel x))
      ((volume.restrict (Set.Ioc y z)).prod
        (volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ))))

/-- The endpoint face bound propagates from `t=1` to every positive
Stieltjes variable `t≥1`. -/
theorem roughSaias_log_div_t_ratio_le
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y) (ht : 1 ≤ t)
    {A : ℝ} (hu : Real.log x / Real.log y ≤ A) :
    Real.log (x / t) / Real.log y ≤ A := by
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogt : 0 ≤ Real.log t := Real.log_nonneg ht
  rw [Real.log_div hx.ne' htpos.ne']
  apply (div_le_iff₀ hlogy).2
  have hu' := (div_le_iff₀ hlogy).1 hu
  linarith

/-! ## Discharging the compact Fubini datum -/

theorem measurable_uncurry_roughSaiasBuchstabDensityKernel (x : ℝ) :
    Measurable (Function.uncurry (roughSaiasBuchstabDensityKernel x)) := by
  have hxs : Measurable (fun p : ℝ × ℝ ↦ x / p.1) :=
    measurable_const.div measurable_fst
  have hquot : Measurable (fun p : ℝ × ℝ ↦ (x / p.1) / p.2) :=
    hxs.div measurable_snd
  have hcoord : Measurable (fun p : ℝ × ℝ ↦
      Real.log ((x / p.1) / p.2) / Real.log p.1) :=
    (Real.measurable_log.comp hquot).div
      (Real.measurable_log.comp measurable_fst)
  have hprofile : Measurable (fun p : ℝ × ℝ ↦
      (x / p.1) * roughSaiasZeroExtendedRho
        (Real.log ((x / p.1) / p.2) / Real.log p.1)) :=
    hxs.mul (measurable_roughSaiasZeroExtendedRho.comp hcoord)
  have hcontinuous : Measurable (fun p : ℝ × ℝ ↦
      ((x / p.1) * roughSaiasZeroExtendedRho
        (Real.log ((x / p.1) / p.2) / Real.log p.1)) /
          Real.log p.1) :=
    hprofile.div (Real.measurable_log.comp measurable_fst)
  simpa [Function.uncurry, roughSaiasBuchstabDensityKernel,
    roughSaiasContinuousBuchstabProfile,
    roughSaiasStieltjesDickmanProfile] using
      hcontinuous.mul (measurable_roughSaiasFloorDensity.comp measurable_snd)

/-- One finite constant controls the zero-extended finite Dickman profile
through the sixth face.  No positivity estimate on the sixth face is
needed: this is only compact boundedness of the continuous function `rho`.
-/
theorem exists_roughSaiasZeroExtendedRho_abs_bound_six :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ, u ≤ 6 →
      |roughSaiasZeroExtendedRho u| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_rho.continuousOn (s := Set.Icc (0 : ℝ) 6)
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 6 := by norm_num
  have hC0 : 0 ≤ C :=
    (norm_nonneg (rho 0)).trans (hC 0 hzero)
  use C, hC0
  intro u hu6
  by_cases hu0 : u < 0
  · simp [roughSaiasZeroExtendedRho_of_neg hu0, hC0]
  · rw [roughSaiasZeroExtendedRho_of_nonneg (le_of_not_gt hu0)]
    simpa only [Real.norm_eq_abs] using
      hC u ⟨le_of_not_gt hu0, hu6⟩

theorem roughSaiasFloorDensity_mem_unitInterval
    {t : ℝ} (ht1 : 1 ≤ t) :
    0 ≤ roughSaiasFloorDensity t ∧ roughSaiasFloorDensity t ≤ 1 := by
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
  have hfloort : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t := Nat.floor_le ht.le
  have ht2 : 0 < t ^ 2 := sq_pos_of_pos ht
  unfold roughSaiasFloorDensity
  constructor
  · exact div_nonneg hfloor0 ht2.le
  · apply (div_le_one ht2).2
    exact hfloort.trans (by nlinarith)

/-- If the base is enlarged from `y` to `b` and `t ≥ 1`, the supported
Dickman coordinate stays below the original sixth-face endpoint. -/
theorem roughSaias_profile_coordinate_le_six
    {x y b t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyb : y ≤ b) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) :
    Real.log (x / t) / Real.log b ≤ 6 := by
  have hb : 1 < b := hy.trans_le hyb
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hq : 0 < x / t := div_pos hx ht
  by_cases hq1 : x / t ≤ 1
  · have hlogq : Real.log (x / t) ≤ 0 := Real.log_nonpos hq.le hq1
    have hlogb : 0 < Real.log b := Real.log_pos hb
    exact (div_nonpos_of_nonpos_of_nonneg hlogq hlogb.le).trans (by norm_num)
  · have hqone : 1 < x / t := lt_of_not_ge hq1
    have hlogq : 0 ≤ Real.log (x / t) := (Real.log_pos hqone).le
    have hlogyb : Real.log y ≤ Real.log b :=
      Real.log_le_log (zero_lt_one.trans hy) hyb
    calc
      Real.log (x / t) / Real.log b ≤
          Real.log (x / t) / Real.log y :=
        div_le_div_of_nonneg_left hlogq (Real.log_pos hy) hlogyb
      _ ≤ 6 := roughSaias_log_div_t_ratio_le hx hy ht1 hu6

theorem roughSaias_inner_profile_coordinate_le_six
    {x y s t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hys : y ≤ s) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) :
    Real.log ((x / s) / t) / Real.log s ≤ 6 := by
  have hs : 1 < s := hy.trans_le hys
  have hspos : 0 < s := zero_lt_one.trans hs
  have ht : 0 < t := zero_lt_one.trans_le ht1
  have hq : 0 < x / t := div_pos hx ht
  have hquotient : (x / s) / t = (x / t) / s := by
    field_simp [hspos.ne', ht.ne']
  have hcoord :
      Real.log ((x / s) / t) / Real.log s =
        Real.log (x / t) / Real.log s - 1 := by
    rw [hquotient, Real.log_div hq.ne' hspos.ne']
    field_simp [(Real.log_pos hs).ne']
  rw [hcoord]
  have hbase := roughSaias_profile_coordinate_le_six
    hx hy hys ht1 hu6
  linarith

theorem integrableOn_roughSaiasProfile_mul_floorDensity_six
    {R : ℕ} {x y b : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyb : y ≤ b) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntegrableOn
      (fun t ↦ roughSaiasStieltjesDickmanProfile x b t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) (R : ℝ)) := by
  by_cases hR : 1 ≤ R
  · obtain ⟨C, hC0, hC⟩ :=
      exists_roughSaiasZeroExtendedRho_abs_bound_six
    have hRreal : (1 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
    have hmeas : Measurable (fun t ↦
        roughSaiasStieltjesDickmanProfile x b t *
          roughSaiasFloorDensity t) :=
      (measurable_roughSaiasStieltjesDickmanProfile x b).mul
        measurable_roughSaiasFloorDensity
    have hconst : IntervalIntegrable (fun _ : ℝ ↦ x * C)
        volume (1 : ℝ) (R : ℝ) :=
      continuous_const.intervalIntegrable _ _
    have hint : IntervalIntegrable
        (fun t ↦ roughSaiasStieltjesDickmanProfile x b t *
          roughSaiasFloorDensity t)
        volume (1 : ℝ) (R : ℝ) := by
      apply hconst.mono_fun' hmeas.aestronglyMeasurable
      filter_upwards [ae_restrict_mem measurableSet_uIoc] with t htU
      have htI : t ∈ Set.Icc (1 : ℝ) (R : ℝ) := by
        rw [← Set.uIcc_of_le hRreal]
        exact Set.uIoc_subset_uIcc htU
      have hcoord := roughSaias_profile_coordinate_le_six
        hx hy hyb htI.1 hu6
      have hdensity := roughSaiasFloorDensity_mem_unitInterval htI.1
      have hprofile :
          |roughSaiasStieltjesDickmanProfile x b t| ≤ x * C := by
        unfold roughSaiasStieltjesDickmanProfile
        rw [abs_mul, abs_of_pos hx]
        exact mul_le_mul_of_nonneg_left (hC _ hcoord) hx.le
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hdensity.1]
      calc
        |roughSaiasStieltjesDickmanProfile x b t| *
            roughSaiasFloorDensity t ≤
          (x * C) * 1 := mul_le_mul hprofile hdensity.2 hdensity.1
            (mul_nonneg hx.le hC0)
        _ = x * C := mul_one _
    have hintIcc :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hRreal).mp hint
    exact hintIcc.mono_set Set.Ioc_subset_Icc_self
  · have hR0 : R = 0 := by omega
    subst R
    simp

theorem roughSaiasBuchstabDensityKernel_abs_le
    {x y s t C : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hys : y ≤ s) (ht1 : 1 ≤ t)
    (hu6 : Real.log x / Real.log y ≤ 6) (hC0 : 0 ≤ C)
    (hC : ∀ u : ℝ, u ≤ 6 → |roughSaiasZeroExtendedRho u| ≤ C) :
    |roughSaiasBuchstabDensityKernel x s t| ≤
      x * C / Real.log y := by
  have hs : 1 < s := hy.trans_le hys
  have hspos : 0 < s := zero_lt_one.trans hs
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogs : 0 < Real.log s := Real.log_pos hs
  have hlogys : Real.log y ≤ Real.log s :=
    Real.log_le_log (zero_lt_one.trans hy) hys
  have hxs : 0 ≤ x / s := (div_pos hx hspos).le
  have hxsle : x / s ≤ x := div_le_self hx.le hs.le
  have hcoord := roughSaias_inner_profile_coordinate_le_six
    hx hy hys ht1 hu6
  have hprofile :
      |roughSaiasStieltjesDickmanProfile (x / s) s t| ≤ x * C := by
    unfold roughSaiasStieltjesDickmanProfile
    rw [abs_mul, abs_of_nonneg hxs]
    calc
      (x / s) *
          |roughSaiasZeroExtendedRho
            (Real.log ((x / s) / t) / Real.log s)| ≤
        (x / s) * C := mul_le_mul_of_nonneg_left (hC _ hcoord) hxs
      _ ≤ x * C := mul_le_mul_of_nonneg_right hxsle hC0
  have hcontinuous :
      |roughSaiasContinuousBuchstabProfile x s t| ≤
        x * C / Real.log y := by
    unfold roughSaiasContinuousBuchstabProfile
    rw [abs_div, abs_of_pos hlogs]
    calc
      |roughSaiasStieltjesDickmanProfile (x / s) s t| / Real.log s ≤
          (x * C) / Real.log s :=
        div_le_div_of_nonneg_right hprofile hlogs.le
      _ ≤ x * C / Real.log y :=
        div_le_div_of_nonneg_left (mul_nonneg hx.le hC0) hlogy hlogys
  have hdensity := roughSaiasFloorDensity_mem_unitInterval ht1
  unfold roughSaiasBuchstabDensityKernel
  rw [abs_mul, abs_of_nonneg hdensity.1]
  calc
    |roughSaiasContinuousBuchstabProfile x s t| *
        roughSaiasFloorDensity t ≤
      (x * C / Real.log y) * 1 :=
        mul_le_mul hcontinuous hdensity.2 hdensity.1
          (div_nonneg (mul_nonneg hx.le hC0) hlogy.le)
    _ = x * C / Real.log y := mul_one _

theorem integrable_roughSaiasBuchstabDensityKernel
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (_hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    Integrable (Function.uncurry (roughSaiasBuchstabDensityKernel x))
      ((volume.restrict (Set.Ioc y z)).prod
        (volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ)))) := by
  obtain ⟨C, hC0, hC⟩ :=
    exists_roughSaiasZeroExtendedRho_abs_bound_six
  let μ : Measure ℝ := volume.restrict (Set.Ioc y z)
  let ν : Measure ℝ := volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ))
  let K : ℝ × ℝ → ℝ :=
    Function.uncurry (roughSaiasBuchstabDensityKernel x)
  have hmeas : Measurable K := by
    simpa [K] using measurable_uncurry_roughSaiasBuchstabDensityKernel x
  have hconst : Integrable
      (fun _ : ℝ × ℝ ↦ x * C / Real.log y) (μ.prod ν) := by
    exact integrable_const _
  have hbound : ∀ᵐ p ∂(μ.prod ν),
      ‖K p‖ ≤ x * C / Real.log y := by
    rw [Measure.ae_prod_iff_ae_ae
      (measurableSet_le hmeas.norm measurable_const)]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs]
    simpa [K, Function.uncurry] using
      roughSaiasBuchstabDensityKernel_abs_le hx hy hs.1.le ht.1.le
        hu6 hC0 hC
  have hK : Integrable K (μ.prod ν) :=
    hconst.mono' hmeas.aestronglyMeasurable hbound
  simpa [μ, ν, K] using hK

/-- The compact Fubini datum is automatic under the pointwise sixth-face
hypotheses used by continuous Buchstab. -/
theorem roughSaiasBuchstabDensityFubini_of_compact
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    RoughSaiasBuchstabDensityFubini R x y z := by
  exact ⟨integrableOn_roughSaiasProfile_mul_floorDensity_six
      hx hy le_rfl hu6,
    integrableOn_roughSaiasProfile_mul_floorDensity_six
      hx hy hyz hu6,
    integrable_roughSaiasBuchstabDensityKernel hx hy hyz hu6⟩

/-- Division by a scalar commutes exactly with the finite signed
functional. -/
theorem roughSaiasFiniteStieltjesFunctional_div
    (R : ℕ) (f : ℝ → ℝ) (c : ℝ) :
    roughSaiasFiniteStieltjesFunctional R (fun t ↦ f t / c) =
      roughSaiasFiniteStieltjesFunctional R f / c := by
  have hatom : roughSaiasStieltjesAtomPart R (fun t ↦ f t / c) =
      roughSaiasStieltjesAtomPart R f / c := by
    unfold roughSaiasStieltjesAtomPart
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hdensity :
      roughSaiasStieltjesDensityPart R (fun t ↦ f t / c) =
        roughSaiasStieltjesDensityPart R f / c := by
    unfold roughSaiasStieltjesDensityPart
    calc
      (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          (f t / c) * roughSaiasFloorDensity t) =
        ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          c⁻¹ * (f t * roughSaiasFloorDensity t) := by
            apply integral_congr_ae
            filter_upwards with t
            ring
      _ = c⁻¹ * ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          f t * roughSaiasFloorDensity t := by
            rw [MeasureTheory.integral_const_mul]
      _ = (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          f t * roughSaiasFloorDensity t) / c := by ring
  unfold roughSaiasFiniteStieltjesFunctional
  rw [hatom, hdensity]
  ring

/-- At a fixed Buchstab base, the functional of the pointwise kernel is
the capped Stieltjes Lambda at `x/s`, divided by `log s`. -/
theorem roughSaiasFiniteStieltjesFunctional_buchstabProfile
    (R : ℕ) (x s : ℝ) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasContinuousBuchstabProfile x s) =
      roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
        Real.log s := by
  unfold roughSaiasContinuousBuchstabProfile
    roughSaiasLambdaStieltjesWithCutoff
  exact roughSaiasFiniteStieltjesFunctional_div R
    (roughSaiasStieltjesDickmanProfile (x / s) s) (Real.log s)

/-! ## The finite atomic lift -/

/-- Finite atoms commute with continuous Buchstab, including the finite
sum/integral interchange. -/
theorem roughSaiasStieltjesAtomPart_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasStieltjesAtomPart R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasStieltjesAtomPart R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasStieltjesAtomPart R
            (roughSaiasContinuousBuchstabProfile x s) := by
  have hface (n : ℕ) (hn : n ∈ Finset.Icc 1 R) :
      Real.log (x / (n : ℝ)) / Real.log y ≤ 6 :=
    roughSaias_log_div_t_ratio_le hx hy
      (by exact_mod_cast (Finset.mem_Icc.mp hn).1) hu6
  have hnpos (n : ℕ) (hn : n ∈ Finset.Icc 1 R) : 0 < n := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    omega
  have hint (n : ℕ) (hn : n ∈ Finset.Icc 1 R) :
      IntervalIntegrable
        (fun s ↦ roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
          (n : ℝ)) volume y z :=
    (intervalIntegrable_roughSaiasContinuousBuchstabProfile hx
      (by exact_mod_cast (hnpos n hn)) hy hyz (hface n hn)).div_const _
  unfold roughSaiasStieltjesAtomPart
  calc
    (∑ n ∈ Finset.Icc 1 R,
        roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ)) =
      ∑ n ∈ Finset.Icc 1 R,
        (roughSaiasStieltjesDickmanProfile x z (n : ℝ) / (n : ℝ) -
          ∫ s in y..z,
            roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
              (n : ℝ)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [roughSaiasStieltjesDickmanProfile_buchstab hx
        (by exact_mod_cast (hnpos n hn)) hy hyz (hface n hn),
        intervalIntegral.integral_div]
      ring
    _ = (∑ n ∈ Finset.Icc 1 R,
          roughSaiasStieltjesDickmanProfile x z (n : ℝ) / (n : ℝ)) -
        ∑ n ∈ Finset.Icc 1 R,
          ∫ s in y..z,
            roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
              (n : ℝ) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ n ∈ Finset.Icc 1 R,
          roughSaiasStieltjesDickmanProfile x z (n : ℝ) / (n : ℝ)) -
        ∫ s in y..z,
          ∑ n ∈ Finset.Icc 1 R,
            roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
              (n : ℝ) := by
      rw [intervalIntegral.integral_finset_sum hint]

/-! ## The density Fubini lift -/

/-- The absolutely continuous density commutes with continuous Buchstab
under its explicit compact Fubini datum. -/
theorem roughSaiasStieltjesDensityPart_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasStieltjesDensityPart R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasStieltjesDensityPart R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasStieltjesDensityPart R
            (roughSaiasContinuousBuchstabProfile x s) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc y z)
  let ν : Measure ℝ :=
    volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ))
  let K : ℝ × ℝ → ℝ :=
    Function.uncurry (roughSaiasBuchstabDensityKernel x)
  have hK : Integrable K (μ.prod ν) := by
    simpa [μ, ν, K] using hFubini.2.2
  have hinnerT : Integrable
      (fun t ↦ ∫ s, K (s, t) ∂μ) ν := hK.integral_prod_right
  have hzInt := hFubini.2.1
  have hpoint : ∀ᵐ t ∂ν,
      roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t =
        roughSaiasStieltjesDickmanProfile x z t *
            roughSaiasFloorDensity t -
          ∫ s, K (s, t) ∂μ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have htpos : 0 < t := zero_lt_one.trans ht.1
    have hface := roughSaias_log_div_t_ratio_le hx hy ht.1.le hu6
    have hbuch := roughSaiasStieltjesDickmanProfile_buchstab
      hx htpos hy hyz hface
    rw [intervalIntegral.integral_of_le hyz] at hbuch
    change roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t =
      roughSaiasStieltjesDickmanProfile x z t *
          roughSaiasFloorDensity t -
        ∫ s in Set.Ioc y z,
          roughSaiasBuchstabDensityKernel x s t
    rw [hbuch]
    unfold roughSaiasBuchstabDensityKernel
    rw [MeasureTheory.integral_mul_const]
    ring
  unfold roughSaiasStieltjesDensityPart
  have hleft :
      (∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          roughSaiasStieltjesDickmanProfile x y t *
            roughSaiasFloorDensity t) =
        ∫ t in Set.Ioc (1 : ℝ) (R : ℝ),
          (roughSaiasStieltjesDickmanProfile x z t *
              roughSaiasFloorDensity t -
            ∫ s, K (s, t) ∂μ) :=
    by simpa [ν] using integral_congr_ae hpoint
  rw [hleft, MeasureTheory.integral_sub hzInt
    (by simpa [ν] using hinnerT)]
  have hswap : (∫ s, ∫ t, K (s, t) ∂ν ∂μ) =
      ∫ t, ∫ s, K (s, t) ∂μ ∂ν := by
    apply integral_integral_swap
    simpa only [Function.uncurry_apply_pair, Prod.eta] using hK
  rw [← hswap]
  rw [intervalIntegral.integral_of_le hyz]
  rfl

/-! ## Functional continuous Buchstab -/

private theorem intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesAtomPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z := by
  unfold roughSaiasStieltjesAtomPart
  have hterm (n : ℕ) (hn : n ∈ Finset.Icc 1 R) :
      IntervalIntegrable
        (fun s ↦ roughSaiasContinuousBuchstabProfile x s (n : ℝ) /
          (n : ℝ)) volume y z := by
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hn1real : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn1
    have hface := roughSaias_log_div_t_ratio_le hx hy
      hn1real hu6
    have hnposreal : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    exact (intervalIntegrable_roughSaiasContinuousBuchstabProfile hx
      hnposreal hy hyz hface).div_const _
  apply (IntervalIntegrable.sum (Finset.Icc 1 R) hterm).congr
  intro s _hs
  simp only [Finset.sum_apply]

/-- The capped Lambda integrand occurring in functional Buchstab is
interval-integrable; the product-kernel proof discharges the density part. -/
theorem intervalIntegrable_roughSaiasLambdaStieltjesWithCutoff_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    IntervalIntegrable
      (fun s ↦ roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
        Real.log s) volume y z := by
  have hAtom :=
    intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
      (R := R) hx hy hyz hu6
  have hK := integrable_roughSaiasBuchstabDensityKernel
    (R := R) hx hy hyz hu6
  have hDensityOn : IntegrableOn
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) (Set.Ioc y z) := by
    simpa [roughSaiasStieltjesDensityPart,
      roughSaiasBuchstabDensityKernel, Function.uncurry] using
        hK.integral_prod_left
  have hDensity : IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hyz).mpr hDensityOn
  have hFunctional : IntervalIntegrable
      (fun s ↦ roughSaiasFiniteStieltjesFunctional R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z := by
    unfold roughSaiasFiniteStieltjesFunctional
    exact hAtom.sub hDensity
  apply hFunctional.congr
  intro s _hs
  exact roughSaiasFiniteStieltjesFunctional_buchstabProfile R x s

/-- Exact continuous Buchstab identity for the finite signed functional. -/
theorem roughSaiasFiniteStieltjesFunctional_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasFiniteStieltjesFunctional R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasFiniteStieltjesFunctional R
            (roughSaiasContinuousBuchstabProfile x s) := by
  have hatom := roughSaiasStieltjesAtomPart_buchstab
    (R := R) hx hy hyz hu6
  have hdensity := roughSaiasStieltjesDensityPart_buchstab
    (R := R) hx hy hyz hu6 hFubini
  have hAtomInt :=
    intervalIntegrable_roughSaiasStieltjesAtomPart_buchstab
      (R := R) hx hy hyz hu6
  have hK : Integrable
      (Function.uncurry (roughSaiasBuchstabDensityKernel x))
      ((volume.restrict (Set.Ioc y z)).prod
        (volume.restrict (Set.Ioc (1 : ℝ) (R : ℝ)))) := hFubini.2.2
  have hDensityOn : IntegrableOn
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) (Set.Ioc y z) := by
    simpa [roughSaiasStieltjesDensityPart,
      roughSaiasBuchstabDensityKernel, Function.uncurry] using
        hK.integral_prod_left
  have hDensityInt : IntervalIntegrable
      (fun s ↦ roughSaiasStieltjesDensityPart R
        (roughSaiasContinuousBuchstabProfile x s)) volume y z :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hyz).mpr hDensityOn
  unfold roughSaiasFiniteStieltjesFunctional
  rw [hatom, hdensity,
    intervalIntegral.integral_sub hAtomInt hDensityInt]
  ring

/-- The usual Lambda-shaped form of functional Buchstab. -/
theorem roughSaiasLambdaStieltjesWithCutoff_buchstab
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6)
    (hFubini : RoughSaiasBuchstabDensityFubini R x y z) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff R x z -
        ∫ s in y..z,
          roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
            Real.log s := by
  unfold roughSaiasLambdaStieltjesWithCutoff
  rw [roughSaiasFiniteStieltjesFunctional_buchstab
    hx hy hyz hu6 hFubini]
  apply congrArg (fun q : ℝ ↦
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasStieltjesDickmanProfile x z) - q)
  apply intervalIntegral.integral_congr
  intro s hs
  exact roughSaiasFiniteStieltjesFunctional_buchstabProfile R x s

/-- Density Buchstab with the compact Fubini datum discharged. -/
theorem roughSaiasStieltjesDensityPart_buchstab_unconditional
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasStieltjesDensityPart R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasStieltjesDensityPart R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasStieltjesDensityPart R
            (roughSaiasContinuousBuchstabProfile x s) := by
  exact roughSaiasStieltjesDensityPart_buchstab hx hy hyz hu6
    (roughSaiasBuchstabDensityFubini_of_compact hx hy hyz hu6)

/-- Finite-functional Buchstab with no auxiliary Fubini premise. -/
theorem roughSaiasFiniteStieltjesFunctional_buchstab_unconditional
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasFiniteStieltjesFunctional R
        (roughSaiasStieltjesDickmanProfile x y) =
      roughSaiasFiniteStieltjesFunctional R
          (roughSaiasStieltjesDickmanProfile x z) -
        ∫ s in y..z,
          roughSaiasFiniteStieltjesFunctional R
            (roughSaiasContinuousBuchstabProfile x s) := by
  exact roughSaiasFiniteStieltjesFunctional_buchstab hx hy hyz hu6
    (roughSaiasBuchstabDensityFubini_of_compact hx hy hyz hu6)

/-- Continuous Buchstab for the capped Stieltjes Lambda, with every
compact integrability and Fubini obligation proved internally. -/
theorem roughSaiasLambdaStieltjesWithCutoff_buchstab_unconditional
    {R : ℕ} {x y z : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hyz : y ≤ z) (hu6 : Real.log x / Real.log y ≤ 6) :
    roughSaiasLambdaStieltjesWithCutoff R x y =
      roughSaiasLambdaStieltjesWithCutoff R x z -
        ∫ s in y..z,
          roughSaiasLambdaStieltjesWithCutoff R (x / s) s /
            Real.log s := by
  exact roughSaiasLambdaStieltjesWithCutoff_buchstab hx hy hyz hu6
    (roughSaiasBuchstabDensityFubini_of_compact hx hy hyz hu6)

end

end Erdos390.WholePaper
