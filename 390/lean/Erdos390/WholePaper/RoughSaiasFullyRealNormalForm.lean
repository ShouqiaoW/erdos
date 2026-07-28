import Erdos390.WholePaper.RoughSaiasRealStieltjesNormalForm
import Erdos390.WholePaper.RoughCompactBVTranslation

/-!
# The Saias normal form with a genuinely real base

Continuous Buchstab produces inner terms `Lambda(x/s,s)` with a real base
`s`.  The project's original `roughSaiasG` takes a natural base, so it
cannot state that identity directly.  This file supplies the literal real
analogue, proves the same signed base-free substitution, and identifies it
exactly with the finite Stieltjes functional.  At natural bases it reduces
definitionally to the existing normal form.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Fully real Saias data -/

noncomputable def roughSaiasFullyRealFractionalWeight
    (y v : ℝ) : ℝ :=
  Int.fract (y ^ v) * y ^ (-v)

noncomputable def roughSaiasFullyRealG (y u : ℝ) : ℝ :=
  rho u - ∫ v in (0 : ℝ)..5,
    roughSaiasDickmanDerivative (u - v) *
      roughSaiasFullyRealFractionalWeight y v

noncomputable def roughSaiasFullyRealLambdaNormalForm
    (x y : ℝ) : ℝ :=
  x * roughSaiasFullyRealG y (Real.log x / Real.log y) - Int.fract x

noncomputable def roughSaiasFullyRealBaseFreeFractionalKernel
    (x y t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      ((Real.log x - Real.log t) / Real.log y) *
    Int.fract t / (Real.log y * t ^ (2 : ℕ))

noncomputable def roughSaiasFullyRealBaseFreeFractionalIntegral
    (x y : ℝ) : ℝ :=
  ∫ t in (1 : ℝ)..y ^ (5 : ℝ),
    roughSaiasFullyRealBaseFreeFractionalKernel x y t

theorem measurable_roughSaiasFullyRealFractionalWeight
    {y : ℝ} (hy : 0 < y) :
    Measurable (roughSaiasFullyRealFractionalWeight y) := by
  have hpow : Continuous (fun v : ℝ ↦ y ^ v) :=
    Real.continuous_const_rpow hy.ne'
  have hpowNeg : Continuous (fun v : ℝ ↦ y ^ (-v)) :=
    hpow.comp continuous_neg
  exact hpow.measurable.fract.mul hpowNeg.measurable

theorem roughSaiasFullyRealFractionalWeight_mem_unitInterval
    {y v : ℝ} (hy : 1 ≤ y) (hv : 0 ≤ v) :
    0 ≤ roughSaiasFullyRealFractionalWeight y v ∧
      roughSaiasFullyRealFractionalWeight y v ≤ 1 := by
  have hpowNonneg : 0 ≤ y ^ (-v) := Real.rpow_nonneg (by positivity) _
  have hpowLe : y ^ (-v) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hy (by linarith)
  have hfractNonneg : 0 ≤ Int.fract (y ^ v) := Int.fract_nonneg _
  have hfractLe : Int.fract (y ^ v) ≤ 1 := (Int.fract_lt_one _).le
  unfold roughSaiasFullyRealFractionalWeight
  constructor
  · exact mul_nonneg hfractNonneg hpowNonneg
  · calc
      Int.fract (y ^ v) * y ^ (-v) ≤ 1 * y ^ (-v) :=
        mul_le_mul_of_nonneg_right hfractLe hpowNonneg
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hpowLe (by norm_num)
      _ = 1 := mul_one _

theorem roughSaiasFullyRealIntegrand_intervalIntegrable
    {y u : ℝ} (hy : 1 < y) (hu5 : u ≤ 5) :
    IntervalIntegrable
      (fun v : ℝ ↦ roughSaiasDickmanDerivative (u - v) *
        roughSaiasFullyRealFractionalWeight y v)
      volume 0 5 := by
  have hmeas : Measurable
      (fun v : ℝ ↦ roughSaiasDickmanDerivative (u - v) *
        roughSaiasFullyRealFractionalWeight y v) :=
    (measurable_roughSaiasDickmanDerivative.comp
      (measurable_const.sub measurable_id)).mul
        (measurable_roughSaiasFullyRealFractionalWeight
          (zero_lt_one.trans hy))
  have hone : IntervalIntegrable (fun _ : ℝ ↦ (1 : ℝ)) volume 0 5 :=
    continuous_const.intervalIntegrable 0 5
  apply hone.mono_fun' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_uIoc] with v hv
  have hv' : v ∈ Set.Icc (0 : ℝ) 5 := by
    simpa only [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using
      Set.uIoc_subset_uIcc hv
  have hderiv := roughSaiasDickmanDerivative_abs_le_one
    (u := u - v) (by linarith [hv'.1])
  have hweight := roughSaiasFullyRealFractionalWeight_mem_unitInterval
    hy.le hv'.1
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight.1]
  calc
    |roughSaiasDickmanDerivative (u - v)| *
        roughSaiasFullyRealFractionalWeight y v ≤
      1 * roughSaiasFullyRealFractionalWeight y v :=
        mul_le_mul_of_nonneg_right hderiv hweight.1
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hweight.2 (by norm_num)
    _ = 1 := mul_one _

/-! ## Exact real-base substitution -/

theorem roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
    {x y : ℝ} (hy : 1 < y) (v : ℝ) :
    (Real.log y * y ^ v) *
        roughSaiasFullyRealBaseFreeFractionalKernel x y (y ^ v) =
      roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
        roughSaiasFullyRealFractionalWeight y v := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hrpow : y ^ v ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hypos v)
  have hcancel : v * Real.log y / Real.log y = v := by
    field_simp [hlogy]
  have hcoord :
      (Real.log x - v * Real.log y) / Real.log y =
        Real.log x / Real.log y - v := by
    rw [sub_div, hcancel]
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
    roughSaiasFullyRealFractionalWeight
  rw [Real.log_rpow hypos, hcoord, Real.rpow_neg hypos.le]
  field_simp [hlogy, hrpow]

theorem roughSaiasFullyRealFractionalIntegral_eq_baseFree
    {x y : ℝ} (hy : 1 < y) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v) =
      roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  let f : ℝ → ℝ := fun v ↦ y ^ v
  let f' : ℝ → ℝ := fun v ↦ Real.log y * y ^ v
  have hypos : 0 < y := zero_lt_one.trans hy
  have hfderiv : ∀ v ∈ Set.Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Set.Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hypos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hy).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hypos.ne').continuousOn
  have hfimage : f '' Set.Icc (0 : ℝ) 5 =
      Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by
    calc
      f '' Set.Icc (0 : ℝ) 5 = Set.Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by simp [f]
  have hchange :
      (∫ t in f '' Set.Icc (0 : ℝ) 5,
          roughSaiasFullyRealBaseFreeFractionalKernel x y t) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasFullyRealBaseFreeFractionalKernel x y)
  have hpoint (v : ℝ) :
      f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) =
        roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v := by
    simpa [f, f', smul_eq_mul] using
      roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
        (x := x) hy v
  have hu : (1 : ℝ) ≤ y ^ (5 : ℝ) :=
    Real.one_le_rpow hy.le (by norm_num)
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  calc
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          roughSaiasDickmanDerivative (Real.log x / Real.log y - v) *
            roughSaiasFullyRealFractionalWeight y v := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ t in Set.Icc (1 : ℝ) (y ^ (5 : ℝ)),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
      rw [← hfimage]
      exact hchange.symm
    _ = ∫ t in (1 : ℝ)..y ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
      rw [intervalIntegral.integral_of_le hu,
        MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    {x y : ℝ} (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      volume (1 : ℝ) (y ^ (5 : ℝ)) := by
  let f : ℝ → ℝ := fun v ↦ y ^ v
  let f' : ℝ → ℝ := fun v ↦ Real.log y * y ^ v
  have hypos : 0 < y := zero_lt_one.trans hy
  have hfderiv : ∀ v ∈ Set.Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Set.Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hypos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hy).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hypos.ne').continuousOn
  have hfimage : f '' Set.Icc (0 : ℝ) 5 =
      Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by
    calc
      f '' Set.Icc (0 : ℝ) 5 = Set.Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Set.Icc (1 : ℝ) (y ^ (5 : ℝ)) := by simp [f]
  have horiginal : IntervalIntegrable
      (fun v : ℝ ↦
        roughSaiasDickmanDerivative
            (Real.log x / Real.log y - v) *
          roughSaiasFullyRealFractionalWeight y v)
      volume 0 5 :=
    roughSaiasFullyRealIntegrand_intervalIntegrable hy hu5
  have horiginalIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 5)).mp horiginal
  have hjacobianIcc : IntegrableOn
      (fun v : ℝ ↦
        f' v • roughSaiasFullyRealBaseFreeFractionalKernel x y (f v))
      (Set.Icc (0 : ℝ) 5) := by
    apply horiginalIcc.congr_fun _ measurableSet_Icc
    intro v _hv
    simpa [f, f', smul_eq_mul] using
      (roughSaiasFullyRealBaseFreeKernel_rpow_mul_jacobian
        (x := x) hy v).symm
  have hkernelImage : IntegrableOn
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      (f '' Set.Icc (0 : ℝ) 5) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasFullyRealBaseFreeFractionalKernel x y)).mpr hjacobianIcc
  rw [hfimage] at hkernelImage
  have hu : (1 : ℝ) ≤ y ^ (5 : ℝ) :=
    Real.one_le_rpow hy.le (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mpr hkernelImage

theorem roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : x / y < t) :
    roughSaiasFullyRealBaseFreeFractionalKernel x y t = 0 := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have htpos : 0 < t := (div_pos hx hypos).trans ht
  have hx_lt_ty : x < t * y := (div_lt_iff₀ hypos).mp ht
  have hloglt : Real.log x < Real.log t + Real.log y := by
    have h := Real.strictMonoOn_log hx (mul_pos htpos hypos) hx_lt_ty
    rwa [Real.log_mul htpos.ne' hypos.ne'] at h
  have harg : (Real.log x - Real.log t) / Real.log y < 1 := by
    rw [div_lt_one (Real.log_pos hy)]
    linarith
  unfold roughSaiasFullyRealBaseFreeFractionalKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp

theorem roughSaiasFullyReal_le_rpow_five
    {x y : ℝ} (hx : 0 < x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    x ≤ y ^ (5 : ℝ) := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : 0 < Real.log y := Real.log_pos hy
  have hlogx : Real.log x ≤ 5 * Real.log y :=
    (div_le_iff₀ hlogy).mp hu5
  have hcappos : 0 < y ^ (5 : ℝ) := Real.rpow_pos_of_pos hypos 5
  apply (Real.log_le_log_iff hx hcappos).mp
  rw [Real.log_rpow hypos]
  exact hlogx

theorem roughSaiasFullyRealBaseFreeIntegral_eq_realCap
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasFullyRealBaseFreeFractionalIntegral x y =
      ∫ t in (1 : ℝ)..x,
        roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasFullyReal_le_rpow_five hx hy hu5
  have hxmem : x ∈ Set.uIcc (1 : ℝ) (y ^ (5 : ℝ)) := by
    rw [Set.uIcc_of_le (hx1.trans hcap)]
    exact ⟨hx1, hcap⟩
  have hint := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := x) hy hu5
  have hparts := (IntervalIntegrable.trans_iff hxmem).mp hint
  have hdivlt : x / y < x := div_lt_self hx hy
  have htail :
      (∫ t in x..y ^ (5 : ℝ),
          roughSaiasFullyRealBaseFreeFractionalKernel x y t) = 0 := by
    calc
      _ = ∫ _t in x..y ^ (5 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc x (y ^ (5 : ℝ)) := by
          rw [Set.uIcc_of_le hcap] at ht
          exact ht
        exact roughSaiasFullyRealBaseFreeKernel_eq_zero_of_div_lt
          hx hy (hdivlt.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hparts.1 hparts.2
  unfold roughSaiasFullyRealBaseFreeFractionalIntegral
  rw [← hsplit, htail, add_zero]

theorem roughSaiasFullyRealG_eq_rho_sub_baseFree
    {x y : ℝ} (hy : 1 < y) :
    roughSaiasFullyRealG y (Real.log x / Real.log y) =
      rho (Real.log x / Real.log y) -
        roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  unfold roughSaiasFullyRealG
  rw [roughSaiasFullyRealFractionalIntegral_eq_baseFree hy]

/-- The fully real normalizer is exactly one on its initial Dickman face. -/
theorem roughSaiasFullyRealG_eq_one_of_le_one
    {y u : ℝ} (hu : u ≤ 1) :
    roughSaiasFullyRealG y u = 1 := by
  have hzero :
      (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative (u - v) *
          roughSaiasFullyRealFractionalWeight y v) = 0 := by
    have hcongr :
        (∫ v in (0 : ℝ)..5,
          roughSaiasDickmanDerivative (u - v) *
            roughSaiasFullyRealFractionalWeight y v) =
          ∫ _v in (0 : ℝ)..5, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro v hv
      have hv' : v ∈ Set.Icc (0 : ℝ) 5 := by
        simpa [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 5)] using hv
      by_cases huv : u - v < 1
      · simp [roughSaiasDickmanDerivative_of_lt_one huv]
      · have huEq : u = 1 := by linarith [hv'.1]
        have hvEq : v = 0 := by linarith [hv'.1]
        subst u
        subst v
        simp [roughSaiasFullyRealFractionalWeight]
    simpa using hcongr
  rw [roughSaiasFullyRealG, hzero, sub_zero, rho_eq_one_of_le_one hu]

/-- The compact `3`-Lipschitz estimate is independent of whether the base
is natural: its proof uses only that the fractional weight lies in `[0,1]`.
-/
theorem roughSaiasFullyRealG_lipschitz_three
    {y : ℝ} (hy : 1 < y) {a b : ℝ}
    (ha : a ∈ Set.Icc (0 : ℝ) 5) (hb : b ∈ Set.Icc (0 : ℝ) 5) :
    |roughSaiasFullyRealG y a - roughSaiasFullyRealG y b| ≤
      3 * |a - b| := by
  let Fa : ℝ → ℝ := fun v ↦
    roughSaiasDickmanDerivative (a - v) *
      roughSaiasFullyRealFractionalWeight y v
  let Fb : ℝ → ℝ := fun v ↦
    roughSaiasDickmanDerivative (b - v) *
      roughSaiasFullyRealFractionalWeight y v
  let qa : ℝ → ℝ := fun v ↦ roughSaiasDickmanDerivative (a - v)
  let qb : ℝ → ℝ := fun v ↦ roughSaiasDickmanDerivative (b - v)
  have hFa : IntervalIntegrable Fa volume 0 5 := by
    simpa only [Fa] using
      roughSaiasFullyRealIntegrand_intervalIntegrable hy ha.2
  have hFb : IntervalIntegrable Fb volume 0 5 := by
    simpa only [Fb] using
      roughSaiasFullyRealIntegrand_intervalIntegrable hy hb.2
  have hqa : IntervalIntegrable qa volume 0 5 := by
    simpa only [qa] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable ha.2
  have hqb : IntervalIntegrable qb volume 0 5 := by
    simpa only [qb] using
      roughSaiasDickmanDerivative_translate_intervalIntegrable hb.2
  have hdiff :
      (∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v =
        ∫ v in (0 : ℝ)..5, Fa v - Fb v :=
    (intervalIntegral.integral_sub hFa hFb).symm
  have hintegral :
      |(∫ v in (0 : ℝ)..5, Fa v) - ∫ v in (0 : ℝ)..5, Fb v| ≤
        ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
    rw [hdiff]
    calc
      |(∫ v in (0 : ℝ)..5, Fa v - Fb v)| ≤
          ∫ v in (0 : ℝ)..5, |Fa v - Fb v| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
      _ ≤ ∫ v in (0 : ℝ)..5, |qa v - qb v| := by
        apply intervalIntegral.integral_mono_on (by norm_num)
          (hFa.sub hFb).abs (hqa.sub hqb).abs
        intro v hv
        have hweight := roughSaiasFullyRealFractionalWeight_mem_unitInterval
          hy.le hv.1
        change
          |qa v * roughSaiasFullyRealFractionalWeight y v -
              qb v * roughSaiasFullyRealFractionalWeight y v| ≤
            |qa v - qb v|
        rw [← sub_mul, abs_mul, abs_of_nonneg hweight.1]
        exact mul_le_of_le_one_right (abs_nonneg (qa v - qb v)) hweight.2
  have htranslate :
      (∫ v in (0 : ℝ)..5, |qa v - qb v|) ≤ 2 * |a - b| := by
    simpa only [qa, qb] using
      roughSaiasDickmanDerivative_translation_le_two_unconditional ha hb
  have hrho : |rho a - rho b| ≤ |a - b| :=
    roughRho_abs_sub_le_abs_of_le_five ha.2 hb.2
  change
    |(rho a - ∫ v in (0 : ℝ)..5, Fa v) -
      (rho b - ∫ v in (0 : ℝ)..5, Fb v)| ≤ 3 * |a - b|
  calc
    _ = |(rho a - rho b) -
        ((∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v)| := by
      congr 1
      ring
    _ ≤ |rho a - rho b| +
        |(∫ v in (0 : ℝ)..5, Fa v) -
          ∫ v in (0 : ℝ)..5, Fb v| := abs_sub _ _
    _ ≤ |a - b| + ∫ v in (0 : ℝ)..5, |qa v - qb v| :=
      add_le_add hrho hintegral
    _ ≤ |a - b| + 2 * |a - b| := add_le_add le_rfl htranslate
    _ = 3 * |a - b| := by ring

theorem roughSaiasFullyRealG_abs_le_sixteen
    {y u : ℝ} (hy : 1 < y) (hu : u ∈ Set.Icc (0 : ℝ) 5) :
    |roughSaiasFullyRealG y u| ≤ 16 := by
  have hzero : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 5 := by norm_num
  have hlip := roughSaiasFullyRealG_lipschitz_three hy hu hzero
  rw [roughSaiasFullyRealG_eq_one_of_le_one (by norm_num : (0 : ℝ) ≤ 1)]
    at hlip
  calc
    |roughSaiasFullyRealG y u| =
        |(roughSaiasFullyRealG y u - 1) + 1| := by
      congr 1
      ring
    _ ≤ |roughSaiasFullyRealG y u - 1| + |(1 : ℝ)| := abs_add_le _ _
    _ ≤ 3 * |u - 0| + 1 := by
      rw [abs_one]
      exact add_le_add hlip le_rfl
    _ ≤ 3 * 5 + 1 := by
      have huabs : |u - 0| ≤ 5 := by
        rw [sub_zero, abs_of_nonneg hu.1]
        exact hu.2
      gcongr
    _ = 16 := by norm_num

/-- On the initial face the fully real normal form is exactly the natural
floor of its first argument. -/
theorem roughSaiasFullyRealLambdaNormalForm_eq_floor_of_le_one
    {x y : ℝ} (hx : 0 ≤ x)
    (hu1 : Real.log x / Real.log y ≤ 1) :
    roughSaiasFullyRealLambdaNormalForm x y = (((⌊x⌋₊ : ℕ) : ℝ)) := by
  unfold roughSaiasFullyRealLambdaNormalForm
  rw [roughSaiasFullyRealG_eq_one_of_le_one hu1,
    roughSaiasNatFloor_cast_eq_sub_fract hx]
  ring

@[simp]
theorem roughSaiasFullyRealFractionalWeight_nat (m : ℕ) (v : ℝ) :
    roughSaiasFullyRealFractionalWeight (m : ℝ) v =
      roughSaiasFractionalWeight m v := rfl

@[simp]
theorem roughSaiasFullyRealG_nat (m : ℕ) (u : ℝ) :
    roughSaiasFullyRealG (m : ℝ) u = roughSaiasG m u := by
  rfl

@[simp]
theorem roughSaiasFullyRealLambdaNormalForm_nat
    (x : ℝ) (m : ℕ) :
    roughSaiasFullyRealLambdaNormalForm x (m : ℝ) =
      roughSaiasLambdaNormalForm x m := by
  rfl

@[simp]
theorem roughSaiasFullyRealBaseFreeKernel_nat
    (x : ℝ) (m : ℕ) (t : ℝ) :
    roughSaiasFullyRealBaseFreeFractionalKernel x (m : ℝ) t =
      roughSaiasRealBaseFreeFractionalKernel x m t := by
  rfl

/-! ## Exact Stieltjes identification at a real base -/

theorem roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
    {x y t : ℝ} (hx : 0 < x) (hy : 1 < y)
    (ht : 0 < t) (hne : t ≠ x / y) :
    roughSaiasRealStieltjesFractionalCorrection x y t =
      x * roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
  have hypos : 0 < y := zero_lt_one.trans hy
  have hlogy : Real.log y ≠ 0 := ne_of_gt (Real.log_pos hy)
  have hcoordNe : roughSaiasStieltjesCoordinate x y t ≠ 1 := by
    intro hcoord
    have hlogEq : Real.log x - Real.log t = Real.log y := by
      unfold roughSaiasStieltjesCoordinate at hcoord
      field_simp [hlogy] at hcoord
      linarith
    have hlogDiv : Real.log (x / y) = Real.log x - Real.log y := by
      rw [Real.log_div hx.ne' hypos.ne']
    have hlogs : Real.log t = Real.log (x / y) := by
      rw [hlogDiv]
      linarith
    have hexp := congrArg Real.exp hlogs
    rw [Real.exp_log ht, Real.exp_log (div_pos hx hypos)] at hexp
    exact hne hexp
  unfold roughSaiasRealStieltjesFractionalCorrection
    roughSaiasFullyRealBaseFreeFractionalKernel
  rw [roughSaiasOpenFaceDickmanDerivative_eq_roughSaias hcoordNe]
  unfold roughSaiasStieltjesCoordinate
  field_simp [ht.ne', hlogy]

theorem integrableOn_roughSaiasFullyRealStieltjesFractionalCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    IntegrableOn (roughSaiasRealStieltjesFractionalCorrection x y)
      (Set.Ioc (1 : ℝ) x) := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasFullyReal_le_rpow_five hx hy hu5
  have hfull := roughSaiasFullyRealBaseFreeKernel_intervalIntegrable
    (x := x) hy hu5
  have hcapInt : IntervalIntegrable
      (roughSaiasFullyRealBaseFreeFractionalKernel x y)
      volume (1 : ℝ) x := by
    apply hfull.mono_set
    rw [Set.uIcc_of_le hx1, Set.uIcc_of_le (hx1.trans hcap)]
    exact Set.Icc_subset_Icc le_rfl hcap
  have hbaseIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hx1).mp hcapInt
  have hbaseIccMul : IntegrableOn
      (fun t : ℝ => x * roughSaiasFullyRealBaseFreeFractionalKernel x y t)
      (Set.Icc (1 : ℝ) x) :=
    hbaseIcc.const_mul x
  have hbase := hbaseIccMul.mono_set Set.Ioc_subset_Icc_self
  apply IntegrableOn.congr_fun_ae hbase
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioc]
  filter_upwards [((volume : Measure ℝ).ae_ne (x / y))] with t hne ht
  exact (roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
    hx hy (zero_lt_one.trans ht.1) hne).symm

theorem integral_roughSaiasFullyRealStieltjesFractionalCorrection
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    (∫ t in Set.Ioc (1 : ℝ) x,
        roughSaiasRealStieltjesFractionalCorrection x y t) =
      x * roughSaiasFullyRealBaseFreeFractionalIntegral x y := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  rw [← intervalIntegral.integral_of_le hx1]
  have heq :
      (∫ t in (1 : ℝ)..x,
          roughSaiasRealStieltjesFractionalCorrection x y t) =
        ∫ t in (1 : ℝ)..x,
          x * roughSaiasFullyRealBaseFreeFractionalKernel x y t := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [((volume : Measure ℝ).ae_ne (x / y))]
      with t hne ht
    have htI : t ∈ Set.Icc (1 : ℝ) x := by
      simpa only [Set.uIcc_of_le hx1] using Set.uIoc_subset_uIcc ht
    exact roughSaiasRealStieltjesFractionalCorrection_eq_fullyRealBaseFree_of_ne
      hx hy (zero_lt_one.trans_le htI.1) hne
  rw [heq, intervalIntegral.integral_const_mul,
    ← roughSaiasFullyRealBaseFreeIntegral_eq_realCap hx1 hy hu5]

/-- Every inner real-base Lambda produced by continuous Buchstab is the
literal fully real Saias normal form. -/
theorem roughSaiasLambdaStieltjes_eq_fullyRealNormalForm
    {x y : ℝ} (hx1 : 1 ≤ x) (hy : 1 < y)
    (hu5 : Real.log x / Real.log y ≤ 5) :
    roughSaiasLambdaStieltjes x y =
      roughSaiasFullyRealLambdaNormalForm x y := by
  have hsmooth := integrableOn_roughSaiasRealStieltjesSmoothCorrection
    hx1 hy hu5
  have hfract :=
    integrableOn_roughSaiasFullyRealStieltjesFractionalCorrection
      hx1 hy hu5
  have hsplit := MeasureTheory.integral_sub hsmooth hfract
  rw [roughSaiasLambdaStieltjes_eq_floor_add_floorCorrection
    hx1 hy hu5]
  have hpoint :
      (∫ t in Set.Ioc (1 : ℝ) x,
          roughSaiasRealStieltjesFloorCorrection x y t) =
        ∫ t in Set.Ioc (1 : ℝ) x,
          (roughSaiasRealStieltjesSmoothCorrection x y t -
            roughSaiasRealStieltjesFractionalCorrection x y t) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact roughSaiasRealStieltjesFloorCorrection_eq_smooth_sub_fractional
      (zero_lt_one.trans ht.1) hy
  rw [hpoint, hsplit,
    integral_roughSaiasRealStieltjesSmoothCorrection hx1 hy hu5,
    integral_roughSaiasFullyRealStieltjesFractionalCorrection hx1 hy hu5]
  unfold roughSaiasFullyRealLambdaNormalForm
  rw [roughSaiasFullyRealG_eq_rho_sub_baseFree hy,
    roughSaiasNatFloor_cast_eq_sub_fract
      (zero_lt_one.trans_le hx1).le]
  ring

/-- Natural bases recover both the old normal form and the new fully real
identification in one exact statement. -/
theorem roughSaiasLambdaStieltjes_eq_normalForm_via_fullyReal
    {x : ℝ} {m : ℕ} (hx1 : 1 ≤ x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    roughSaiasLambdaStieltjes x (m : ℝ) =
      roughSaiasLambdaNormalForm x m := by
  rw [← roughSaiasFullyRealLambdaNormalForm_nat]
  exact roughSaiasLambdaStieltjes_eq_fullyRealNormalForm hx1
    (by exact_mod_cast (show 1 < m by omega)) hu5

end

end Erdos390.WholePaper
