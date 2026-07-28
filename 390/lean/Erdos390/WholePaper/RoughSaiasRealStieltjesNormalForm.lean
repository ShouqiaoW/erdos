import Erdos390.WholePaper.RoughSaiasRealBaseChange

/-!
# Real-endpoint identification of the Stieltjes and Saias normal forms

The natural-endpoint calculation in `RoughSaiasStieltjesNormalForm` is
extended here to every real outer endpoint `x ≥ 1`.  Abel summation now
produces `floor x`, and the elementary identity

`floor x = x - fract x`

supplies exactly the terminal sawtooth in `roughSaiasLambdaNormalForm`.
This real version is needed in continuous Buchstab at the inner endpoints
`x/s`.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Real floor-correction kernels -/

noncomputable def roughSaiasRealStieltjesFloorCorrection
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate x y t) *
    (((⌊t⌋₊ : ℕ) : ℝ)) /
      (t ^ 2 * Real.log y)

noncomputable def roughSaiasRealStieltjesSmoothCorrection
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate x y t) /
    (t * Real.log y)

noncomputable def roughSaiasRealStieltjesFractionalCorrection
    (x y t : ℝ) : ℝ :=
  x * roughSaiasOpenFaceDickmanDerivative
      (roughSaiasStieltjesCoordinate x y t) *
    Int.fract t / (t ^ 2 * Real.log y)

theorem roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
    {x y t : ℝ} (ht : 0 < t) (hy : 1 < y) :
    roughSaiasRealStieltjesFloorCorrection x y t =
      roughSaiasRealStieltjesSmoothCorrection x y t -
        roughSaiasRealStieltjesFractionalCorrection x y t := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have ht0 : t ≠ 0 := ht.ne'
  unfold roughSaiasRealStieltjesFloorCorrection
    roughSaiasRealStieltjesSmoothCorrection
    roughSaiasRealStieltjesFractionalCorrection
  rw [roughSaiasNatFloor_cast_eq_sub_fract ht.le]
  field_simp [ht0, hlogy]

theorem roughSaiasRealStieltjesDerivativeFloor_add_density
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (htx : t ≤ x) :
    roughSaiasStieltjesTestRightDerivative x y t *
          (((⌊t⌋₊ : ℕ) : ℝ)) +
        roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t =
      -roughSaiasRealStieltjesFloorCorrection x y t := by
  have ht0 : t ≠ 0 := ht.ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [roughSaiasStieltjesDickmanProfile_eq_mul_test hx hy ht htx]
  unfold roughSaiasStieltjesTestRightDerivative
    roughSaiasStieltjesTest roughSaiasFloorDensity
    roughSaiasRealStieltjesFloorCorrection
  field_simp [ht0, hlogy]
  ring

/-! ## Real compact integrability -/

theorem integrableOn_roughSaiasRealStieltjesTestRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasStieltjesTestRightDerivative x y)
      (Set.Icc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hC : 0 ≤ x * (1 / Real.log y + 1) := by
    have hlogy : 0 < Real.log y := Real.log_pos hy
    positivity
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ x * (1 / Real.log y + 1))
      volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable
      (roughSaiasStieltjesTestRightDerivative x y)
      volume (1 : ℝ) x := by
    apply hconst.mono_fun'
      (measurable_roughSaiasStieltjesTestRightDerivative x y).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    rw [Real.norm_eq_abs]
    exact roughSaiasStieltjesTestRightDerivative_abs_le
      hy htI.1 htI.2 hu5
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint

theorem integrableOn_roughSaiasRealStieltjesDerivative_mul_floor
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦ roughSaiasStieltjesTestRightDerivative x y t *
        (((⌊t⌋₊ : ℕ) : ℝ)))
      (Set.Ioc (1 : ℝ) x) := by
  have hint := integrableOn_roughSaiasRealStieltjesTestRightDerivative
    hx1 hy hu5
  have hmul := integrableOn_mul_sum_Icc
    FriableAsymptotic.positiveIncrement (a := (1 : ℝ))
      (b := x) (m := 0) (by norm_num) hint
  have hmul' := hmul.mono_set Set.Ioc_subset_Icc_self
  simpa only [roughSaiasPositiveIncrement_prefix] using hmul'

theorem integrableOn_roughSaiasRealStieltjesProfile_mul_floorDensity
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦ roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t)
      (Set.Ioc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hx0 : 0 ≤ x := hx.le
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t) :=
    (measurable_roughSaiasStieltjesDickmanProfile x y).mul
      measurable_roughSaiasFloorDensity
  have hconst : IntervalIntegrable (fun _ : ℝ ↦ x)
      volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasStieltjesDickmanProfile x y t *
        roughSaiasFloorDensity t) volume (1 : ℝ) x := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    have htpos : 0 < t := zero_lt_one.trans_le htI.1
    have hcoord := roughSaiasStieltjesCoordinate_mem hy htI.1 htI.2
    have hcoordLog5 : Real.log (x / t) / Real.log y ≤ 5 := by
      rw [← roughSaiasStieltjesCoordinate_eq_log_div hx htpos]
      exact hcoord.2.trans hu5
    have hrho := roughSaiasZeroExtendedRho_mem_unitInterval hcoordLog5
    have hprofile0 : 0 ≤ roughSaiasStieltjesDickmanProfile x y t := by
      unfold roughSaiasStieltjesDickmanProfile
      exact mul_nonneg hx0 hrho.1
    have hprofilex : roughSaiasStieltjesDickmanProfile x y t ≤ x := by
      unfold roughSaiasStieltjesDickmanProfile
      exact (mul_le_mul_of_nonneg_left hrho.2 hx0).trans_eq (mul_one _)
    have hfloor0 : (0 : ℝ) ≤ (((⌊t⌋₊ : ℕ) : ℝ)) := by positivity
    have hfloort : (((⌊t⌋₊ : ℕ) : ℝ)) ≤ t := Nat.floor_le htpos.le
    have ht2 : 0 < t ^ 2 := sq_pos_of_pos htpos
    have hdensity0 : 0 ≤ roughSaiasFloorDensity t := by
      unfold roughSaiasFloorDensity
      exact div_nonneg hfloor0 ht2.le
    have hdensity1 : roughSaiasFloorDensity t ≤ 1 := by
      unfold roughSaiasFloorDensity
      apply (div_le_one ht2).2
      have hquad : 0 ≤ t * (t - 1) :=
        mul_nonneg htpos.le (sub_nonneg.mpr htI.1)
      exact hfloort.trans (by nlinarith)
    rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hprofile0 hdensity0)]
    calc
      roughSaiasStieltjesDickmanProfile x y t * roughSaiasFloorDensity t ≤
          roughSaiasStieltjesDickmanProfile x y t * 1 :=
        mul_le_mul_of_nonneg_left hdensity1 hprofile0
      _ ≤ x * 1 := mul_le_mul_of_nonneg_right hprofilex (by norm_num)
      _ = x := mul_one _
  have hintIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint
  exact hintIcc.mono_set Set.Ioc_subset_Icc_self

/-! ## Abel summation at a real endpoint -/

theorem roughSaiasStieltjesAtomPart_ceil_profile_eq_floor_test
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y) :
    roughSaiasStieltjesAtomPart ⌈x⌉₊
        (roughSaiasStieltjesDickmanProfile x y) =
      ∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        roughSaiasStieltjesTest x y (n : ℝ) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hfloorceil : ⌊x⌋₊ ≤ ⌈x⌉₊ := by
    have h := Nat.floor_le_floor (Nat.le_ceil x)
    simpa using h
  have hsubset : Finset.Icc 1 ⌊x⌋₊ ⊆ Finset.Icc 1 ⌈x⌉₊ := by
    intro n hn
    rw [Finset.mem_Icc] at hn ⊢
    exact ⟨hn.1, hn.2.trans hfloorceil⟩
  have hsum :
      (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ)) =
        ∑ n ∈ Finset.Icc 1 ⌈x⌉₊,
          roughSaiasStieltjesDickmanProfile x y (n : ℝ) / (n : ℝ) := by
    apply Finset.sum_subset hsubset
    intro n hnceil hnfloor
    have hnData := Finset.mem_Icc.mp hnceil
    have hfloorlt : ⌊x⌋₊ < n := by
      by_contra hnot
      exact hnfloor (Finset.mem_Icc.mpr
        ⟨hnData.1, le_of_not_gt hnot⟩)
    have hxt : x < (n : ℝ) :=
      (Nat.floor_lt' (by omega)).mp hfloorlt
    rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
      hx hy (by exact_mod_cast (show 0 < n by omega)) hxt, zero_div]
  unfold roughSaiasStieltjesAtomPart
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro n hn
  have hnData := Finset.mem_Icc.mp hn
  have hnx : (n : ℝ) ≤ x :=
    (by exact_mod_cast hnData.2 : (n : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans
      (Nat.floor_le hx.le)
  exact roughSaiasStieltjesDickmanProfile_div_eq_test
    hx hy (by exact_mod_cast (show 0 < n by omega)) hnx

theorem roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
        roughSaiasStieltjesTest x y (n : ℝ)) =
      (⌊x⌋₊ : ℝ) -
        ∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasStieltjesTestRightDerivative x y t *
            (((⌊t⌋₊ : ℕ) : ℝ)) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcont := continuousOn_roughSaiasStieltjesTest
    (x := x) (y := y) (A := (1 : ℝ)) (B := x) hy (by norm_num)
  have hright := roughSaiasStieltjesTest_hasRightDerivOn
    (x := x) (y := y) (R := x) hy hx1 le_rfl hu5
  have hint := integrableOn_roughSaiasRealStieltjesTestRightDerivative
    hx1 hy hu5
  have hAbel :=
    RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right
      FriableAsymptotic.positiveIncrement
      (a := (1 : ℝ)) (b := x) (by norm_num) hx1
      hcont hright hint
  have hweighted :
      (∑ k ∈ Finset.Ioc 1 ⌊x⌋₊,
          roughSaiasStieltjesTest x y (k : ℝ) *
            FriableAsymptotic.positiveIncrement k) =
        ∑ k ∈ Finset.Ioc 1 ⌊x⌋₊,
          roughSaiasStieltjesTest x y (k : ℝ) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk0 : k ≠ 0 := by
      rw [Finset.mem_Ioc] at hk
      omega
    simp [FriableAsymptotic.positiveIncrement, hk0]
  have hfloor1 : 1 ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    simpa only [Nat.cast_one] using hx1
  simp only [Nat.floor_one] at hAbel
  rw [hweighted] at hAbel
  simp_rw [roughSaiasPositiveIncrement_prefix] at hAbel
  rw [roughSaiasStieltjesTest_self hx.ne'] at hAbel
  nth_rewrite 1 [Finset.Icc_eq_cons_Ioc hfloor1]
  rw [Finset.sum_cons, hAbel]
  ring

theorem roughSaiasStieltjesDensityPart_ceil_profile_eq_realCap
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y) :
    roughSaiasStieltjesDensityPart ⌈x⌉₊
        (roughSaiasStieltjesDickmanProfile x y) =
      ∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasStieltjesDickmanProfile x y t *
          roughSaiasFloorDensity t := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hsubset : Set.Ioc (1 : ℝ) x ⊆
      Set.Ioc (1 : ℝ) (⌈x⌉₊ : ℝ) := by
    rintro t ⟨ht1, htx⟩
    exact ⟨ht1, htx.trans (Nat.le_ceil x)⟩
  unfold roughSaiasStieltjesDensityPart
  apply setIntegral_eq_of_subset_of_forall_diff_eq_zero
    measurableSet_Ioc hsubset
  intro t ht
  have hxt : x < t := by
    by_contra hnot
    exact ht.2 ⟨ht.1.1, le_of_not_gt hnot⟩
  rw [roughSaiasStieltjesDickmanProfile_eq_zero_of_lt
    hx hy (zero_lt_one.trans ht.1.1) hxt, zero_mul]

theorem roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjes x y =
      (⌊x⌋₊ : ℝ) +
        ∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasRealStieltjesFloorCorrection x y t := by
  have hderiv := integrableOn_roughSaiasRealStieltjesDerivative_mul_floor
    hx1 hy hu5
  have hdensity :=
    integrableOn_roughSaiasRealStieltjesProfile_mul_floorDensity
      hx1 hy hu5
  unfold roughSaiasLambdaStieltjes roughSaiasLambdaStieltjesWithCutoff
    roughSaiasFiniteStieltjesFunctional
  rw [roughSaiasStieltjesAtomPart_ceil_profile_eq_floor_test hx1 hy,
    roughSaiasStieltjesTest_floor_sum_eq_endpoint_sub_integral hx1 hy hu5,
    roughSaiasStieltjesDensityPart_ceil_profile_eq_realCap hx1 hy]
  have hadd := MeasureTheory.integral_add hderiv hdensity
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) x,
          (roughSaiasStieltjesTestRightDerivative x y t *
              (((⌊t⌋₊ : ℕ) : ℝ)) +
            roughSaiasStieltjesDickmanProfile x y t *
              roughSaiasFloorDensity t)) =
        ∫ t in Set.Ioc (1 : ℝ) x,
          -roughSaiasRealStieltjesFloorCorrection x y t := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasRealStieltjesDerivativeFloor_add_density
      (zero_lt_one.trans_le hx1) hy (zero_lt_one.trans ht.1) ht.2
  calc
    (⌊x⌋₊ : ℝ) -
          (∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasStieltjesTestRightDerivative x y t *
              (((⌊t⌋₊ : ℕ) : ℝ))) -
          (∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasStieltjesDickmanProfile x y t *
              roughSaiasFloorDensity t) =
        (⌊x⌋₊ : ℝ) -
          ((∫ t in Set.Ioc (1 : ℝ) x,
              roughSaiasStieltjesTestRightDerivative x y t *
                (((⌊t⌋₊ : ℕ) : ℝ))) +
            (∫ t in Set.Ioc (1 : ℝ) x,
              roughSaiasStieltjesDickmanProfile x y t *
                roughSaiasFloorDensity t)) := by ring
    _ = (⌊x⌋₊ : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) x,
            (roughSaiasStieltjesTestRightDerivative x y t *
                (((⌊t⌋₊ : ℕ) : ℝ)) +
              roughSaiasStieltjesDickmanProfile x y t *
                roughSaiasFloorDensity t) := by rw [hadd]
    _ = (⌊x⌋₊ : ℝ) -
          ∫ t in Set.Ioc (1 : ℝ) x,
            -roughSaiasRealStieltjesFloorCorrection x y t := by rw [hpoint]
    _ = (⌊x⌋₊ : ℝ) +
          ∫ t in Set.Ioc (1 : ℝ) x,
            roughSaiasRealStieltjesFloorCorrection x y t := by
      rw [MeasureTheory.integral_neg]
      ring

/-! ## Smooth real contribution -/

theorem integrableOn_roughSaiasRealRhoCoordinateRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
      (Set.Icc (1 : ℝ) x) := by
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hmeas : Measurable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y))) :=
    (measurable_roughSaiasOpenFaceDickmanDerivative.comp
      (measurable_roughSaiasStieltjesCoordinate x y)).mul
        (measurable_const.div (measurable_id.mul measurable_const))
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ 1 / Real.log y) volume (1 : ℝ) x :=
    continuous_const.intervalIntegrable _ _
  have hint : IntervalIntegrable (fun t : ℝ ↦
      roughSaiasOpenFaceDickmanDerivative
          (roughSaiasStieltjesCoordinate x y t) *
        (-1 / (t * Real.log y))) volume (1 : ℝ) x := by
    apply hconst.mono_fun' hmeas.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
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
          (roughSaiasStieltjesCoordinate x y t)| *
          (1 / (t * Real.log y)) ≤
        1 * (1 / (t * Real.log y)) :=
          mul_le_mul_of_nonneg_right hD (by positivity)
      _ ≤ 1 * (1 / Real.log y) :=
        mul_le_mul_of_nonneg_left hinv (by norm_num)
      _ = 1 / Real.log y := one_mul _
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hint

theorem integral_roughSaiasRealRhoCoordinateRightDerivative
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in (1 : ℝ)..x,
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y))) =
      1 - rho (Real.log x / Real.log y) := by
  have hcont := continuousOn_roughSaiasRhoCoordinate
    (x := x) (y := y) (A := (1 : ℝ)) (B := x) hy (by norm_num)
  have hright : ∀ t ∈ Set.Ioo (1 : ℝ) x,
      HasDerivWithinAt
        (fun s : ℝ ↦ rho (roughSaiasStieltjesCoordinate x y s))
        (roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
        (Set.Ioi t) t := by
    intro t ht
    exact hasDerivWithinAt_roughSaiasRhoCoordinate_right
      hy ht.1.le ht.2.le hu5
  have hintIcc := integrableOn_roughSaiasRealRhoCoordinateRightDerivative
    hx1 hy hu5
  have hint : IntervalIntegrable
      (fun t : ℝ ↦
        roughSaiasOpenFaceDickmanDerivative
            (roughSaiasStieltjesCoordinate x y t) *
          (-1 / (t * Real.log y)))
      volume (1 : ℝ) x :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mpr hintIcc
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le
    hx1 hcont hright hint
  simpa [roughSaiasStieltjesCoordinate] using hftc

theorem integral_roughSaiasRealStieltjesSmoothCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasRealStieltjesSmoothCorrection x y t) =
      x * (rho (Real.log x / Real.log y) - 1) := by
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  rw [← intervalIntegral.integral_of_le hx1]
  have heq :
      (∫ t in (1 : ℝ)..x,
          roughSaiasRealStieltjesSmoothCorrection x y t) =
        ∫ t in (1 : ℝ)..x,
          (-x) *
            (roughSaiasOpenFaceDickmanDerivative
                (roughSaiasStieltjesCoordinate x y t) *
              (-1 / (t * Real.log y))) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa [Set.uIcc_of_le hx1] using ht
    have ht0 : t ≠ 0 := (zero_lt_one.trans_le htI.1).ne'
    unfold roughSaiasRealStieltjesSmoothCorrection
    field_simp [ht0, hlogy]
  rw [heq, intervalIntegral.integral_const_mul,
    integral_roughSaiasRealRhoCoordinateRightDerivative hx1 hy hu5]
  ring

theorem integrableOn_roughSaiasRealStieltjesSmoothCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasRealStieltjesSmoothCorrection x y)
      (Set.Ioc (1 : ℝ) x) := by
  have hbase :=
    (integrableOn_roughSaiasRealRhoCoordinateRightDerivative
      hx1 hy hu5).mono_set Set.Ioc_subset_Icc_self
  have hmul := hbase.const_mul (-x)
  apply IntegrableOn.congr_fun_ae hmul
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have ht0 : t ≠ 0 := (zero_lt_one.trans ht.1).ne'
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  unfold roughSaiasRealStieltjesSmoothCorrection
  field_simp [ht0, hlogy]

/-! ## Fractional real contribution -/

theorem roughSaiasRealStieltjesFractionalCorrection_eq_baseFree_of_ne
    {x t : ℝ} {m : ℕ} (hx : 0 < x) (hm2 : 2 ≤ m)
    (ht : 0 < t) (hne : t ≠ x / (m : ℝ)) :
    roughSaiasRealStieltjesFractionalCorrection x (m : ℝ) t =
      x * roughSaiasRealBaseFreeFractionalKernel x m t := by
  have hmpos : 0 < (m : ℝ) := by positivity
  have hlogm : Real.log (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < m by omega)))
  have hcoordNe :
      roughSaiasStieltjesCoordinate x (m : ℝ) t ≠ 1 := by
    intro hcoord
    have hlogEq : Real.log x - Real.log t = Real.log (m : ℝ) := by
      unfold roughSaiasStieltjesCoordinate at hcoord
      field_simp [hlogm] at hcoord
      linarith
    have hlogDiv : Real.log (x / (m : ℝ)) =
        Real.log x - Real.log (m : ℝ) := by
      rw [Real.log_div hx.ne' hmpos.ne']
    have hlogs : Real.log t = Real.log (x / (m : ℝ)) := by
      rw [hlogDiv]
      linarith
    have hexp := congrArg Real.exp hlogs
    rw [Real.exp_log ht, Real.exp_log (div_pos hx hmpos)] at hexp
    exact hne hexp
  unfold roughSaiasRealStieltjesFractionalCorrection
    roughSaiasRealBaseFreeFractionalKernel
  rw [roughSaiasOpenFaceDickmanDerivative_eq_roughSaias hcoordNe]
  unfold roughSaiasStieltjesCoordinate
  field_simp [ht.ne', hlogm]

theorem integrableOn_roughSaiasRealStieltjesFractionalCorrection
    {x : ℝ} {m : ℕ} (hx1 : 1 ≤ x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    IntegrableOn
      (roughSaiasRealStieltjesFractionalCorrection x (m : ℝ))
      (Set.Ioc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasReal_le_rpow_five hx hm2 hu5
  have hfull := roughSaiasRealBaseFreeFractionalKernel_intervalIntegrable
    (x := x) (m := m) hm2 hu5
  have hcapInt : IntervalIntegrable
      (roughSaiasRealBaseFreeFractionalKernel x m)
      volume (1 : ℝ) x := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hx1, Set.uIcc_of_le (hx1.trans hcap)]
    exact Set.Icc_subset_Icc le_rfl hcap
  have hbaseIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hcapInt
  have hbaseIccMul : IntegrableOn
      (fun t : ℝ => x * roughSaiasRealBaseFreeFractionalKernel x m t)
      (Set.Icc (1 : ℝ) x) :=
    hbaseIcc.const_mul x
  have hbase := hbaseIccMul.mono_set Set.Ioc_subset_Icc_self
  apply IntegrableOn.congr_fun_ae hbase
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [((volume : Measure ℝ).ae_ne
    (x / (m : ℝ)))] with t hne ht
  exact (roughSaiasRealStieltjesFractionalCorrection_eq_baseFree_of_ne
    hx hm2 (zero_lt_one.trans ht.1) hne).symm

theorem integral_roughSaiasRealStieltjesFractionalCorrection
    {x : ℝ} {m : ℕ} (hx1 : 1 ≤ x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasRealStieltjesFractionalCorrection x (m : ℝ) t) =
      x * roughSaiasRealBaseFreeFractionalIntegral x m := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  rw [← intervalIntegral.integral_of_le hx1]
  have heq :
      (∫ t in (1 : ℝ)..x,
          roughSaiasRealStieltjesFractionalCorrection x (m : ℝ) t) =
        ∫ t in (1 : ℝ)..x,
          x * roughSaiasRealBaseFreeFractionalKernel x m t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [((volume : Measure ℝ).ae_ne
      (x / (m : ℝ)))] with t hne ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    exact roughSaiasRealStieltjesFractionalCorrection_eq_baseFree_of_ne
      hx hm2 (zero_lt_one.trans_le htI.1) hne
  rw [heq, intervalIntegral.integral_const_mul,
    ← roughSaiasRealBaseFreeFractionalIntegral_eq_realCap hx1 hm2 hu5]

/-! ## Exact real-endpoint identification -/

theorem roughSaiasLambdaStieltjes_eq_normalForm
    {x : ℝ} {m : ℕ} (hx1 : 1 ≤ x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjes x (m : ℝ) =
      roughSaiasLambdaNormalForm x m := by
  have hsmooth := integrableOn_roughSaiasRealStieltjesSmoothCorrection
    hx1 (by exact_mod_cast (show 1 < m by omega)) hu5
  have hfract := integrableOn_roughSaiasRealStieltjesFractionalCorrection
    hx1 hm2 hu5
  have hsplit := MeasureTheory.integral_sub hsmooth hfract
  rw [roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
      hx1 (by exact_mod_cast (show 1 < m by omega)) hu5]
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasRealStieltjesFloorCorrection x (m : ℝ) t) =
        ∫ t in Set.Ioc (1 : ℝ) x,
          (roughSaiasRealStieltjesSmoothCorrection x (m : ℝ) t -
            roughSaiasRealStieltjesFractionalCorrection x (m : ℝ) t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
      (zero_lt_one.trans ht.1)
      (by exact_mod_cast (show 1 < m by omega))
  rw [hpoint, hsplit,
    integral_roughSaiasRealStieltjesSmoothCorrection hx1
      (by exact_mod_cast (show 1 < m by omega)) hu5,
    integral_roughSaiasRealStieltjesFractionalCorrection hx1 hm2 hu5]
  unfold roughSaiasLambdaNormalForm
  rw [roughSaiasG_at_realEndpoint_eq_realBaseFree hm2,
    roughSaiasNatFloor_cast_eq_sub_fract
      (zero_lt_one.trans_le hx1).le]
  ring

end

end Erdos390.WholePaper
