import Erdos390.WholePaper.RoughSaiasStieltjesNormalForm

/-!
# Base-free Saias substitution at a real endpoint

`RoughSaiasBaseChange` carries a natural quotient because that is what the
hyperbola blocks need.  The continuous Buchstab functional also evaluates
the same normal form at real endpoints such as `X/p`.  This file records the
identical monotone substitution with a real first argument.
-/

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section

noncomputable def roughSaiasRealBaseFreeFractionalKernel
    (x : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      ((Real.log x - Real.log t) / Real.log (m : ℝ)) *
    Int.fract t /
      (Real.log (m : ℝ) * t ^ (2 : ℕ))

noncomputable def roughSaiasRealBaseFreeFractionalIntegral
    (x : ℝ) (m : ℕ) : ℝ :=
  ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
    roughSaiasRealBaseFreeFractionalKernel x m t

theorem roughSaiasRealBaseFreeFractionalKernel_rpow_mul_jacobian
    {x : ℝ} {m : ℕ} (hm2 : 2 ≤ m) (v : ℝ) :
    (Real.log (m : ℝ) * (m : ℝ) ^ v) *
        roughSaiasRealBaseFreeFractionalKernel x m ((m : ℝ) ^ v) =
      roughSaiasDickmanDerivative
          (Real.log x / Real.log (m : ℝ) - v) *
        roughSaiasFractionalWeight m v := by
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogm : Real.log (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hmone)
  have hrpow : (m : ℝ) ^ v ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hmpos v)
  have hcancel :
      v * Real.log (m : ℝ) / Real.log (m : ℝ) = v := by
    field_simp [hlogm]
  have hcoord :
      (Real.log x - v * Real.log (m : ℝ)) / Real.log (m : ℝ) =
        Real.log x / Real.log (m : ℝ) - v := by
    rw [sub_div, hcancel]
  unfold roughSaiasRealBaseFreeFractionalKernel
    roughSaiasFractionalWeight
  rw [Real.log_rpow hmpos, hcoord, Real.rpow_neg hmpos.le]
  field_simp [hlogm, hrpow]

/-- Exact signed substitution `t=m^v` at a real endpoint. -/
theorem roughSaiasFractionalIntegral_eq_realBaseFree
    {x : ℝ} {m : ℕ} (hm2 : 2 ≤ m) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log x / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
      roughSaiasRealBaseFreeFractionalIntegral x m := by
  let f : ℝ → ℝ := fun v ↦ (m : ℝ) ^ v
  let f' : ℝ → ℝ := fun v ↦
    Real.log (m : ℝ) * (m : ℝ) ^ v
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hfderiv : ∀ v ∈ Set.Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Set.Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hmpos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hmone).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hmpos.ne').continuousOn
  have hfimage : f '' Set.Icc (0 : ℝ) 5 =
      Set.Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    calc
      f '' Set.Icc (0 : ℝ) 5 = Set.Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Set.Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
        simp [f]
  have hchange :
      (∫ t in f '' Set.Icc (0 : ℝ) 5,
          roughSaiasRealBaseFreeFractionalKernel x m t) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasRealBaseFreeFractionalKernel x m (f v) :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasRealBaseFreeFractionalKernel x m)
  have hpoint (v : ℝ) :
      f' v • roughSaiasRealBaseFreeFractionalKernel x m (f v) =
        roughSaiasDickmanDerivative
            (Real.log x / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v := by
    simpa [f, f', smul_eq_mul] using
      roughSaiasRealBaseFreeFractionalKernel_rpow_mul_jacobian
        (x := x) hm2 v
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega))
      (by norm_num)
  unfold roughSaiasRealBaseFreeFractionalIntegral
  calc
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log x / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
        ∫ v in Set.Icc (0 : ℝ) 5,
          roughSaiasDickmanDerivative
              (Real.log x / Real.log (m : ℝ) - v) *
            roughSaiasFractionalWeight m v := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ v in Set.Icc (0 : ℝ) 5,
          f' v • roughSaiasRealBaseFreeFractionalKernel x m (f v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ t in Set.Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)),
          roughSaiasRealBaseFreeFractionalKernel x m t := by
      rw [← hfimage]
      exact hchange.symm
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasRealBaseFreeFractionalKernel x m t := by
      rw [intervalIntegral.integral_of_le hu,
        MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem roughSaiasRealBaseFreeFractionalKernel_intervalIntegrable
    {x : ℝ} {m : ℕ} (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable (roughSaiasRealBaseFreeFractionalKernel x m)
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
  let f : ℝ → ℝ := fun v ↦ (m : ℝ) ^ v
  let f' : ℝ → ℝ := fun v ↦
    Real.log (m : ℝ) * (m : ℝ) ^ v
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hfderiv : ∀ v ∈ Set.Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Set.Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hmpos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hmone).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Set.Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hmpos.ne').continuousOn
  have hfimage : f '' Set.Icc (0 : ℝ) 5 =
      Set.Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    calc
      f '' Set.Icc (0 : ℝ) 5 = Set.Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Set.Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by simp [f]
  have horiginal : IntervalIntegrable
      (fun v : ℝ ↦
        roughSaiasDickmanDerivative
            (Real.log x / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) volume 0 5 :=
    roughSaiasIntegrand_intervalIntegrable hm2 hu5
  have horiginalIcc :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le
      (by norm_num : (0 : ℝ) ≤ 5)).mp horiginal
  have hjacobianIcc : IntegrableOn
      (fun v : ℝ ↦
        f' v • roughSaiasRealBaseFreeFractionalKernel x m (f v))
      (Set.Icc (0 : ℝ) 5) := by
    apply horiginalIcc.congr_fun _ measurableSet_Icc
    intro v _hv
    simpa [f, f', smul_eq_mul] using
      (roughSaiasRealBaseFreeFractionalKernel_rpow_mul_jacobian
        (x := x) hm2 v).symm
  have hkernelImage : IntegrableOn
      (roughSaiasRealBaseFreeFractionalKernel x m)
      (f '' Set.Icc (0 : ℝ) 5) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasRealBaseFreeFractionalKernel x m)).mpr hjacobianIcc
  rw [hfimage] at hkernelImage
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega))
      (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mpr hkernelImage

/-- The real-endpoint base-free kernel is supported below `x/m`. -/
theorem roughSaiasRealBaseFreeFractionalKernel_eq_zero_of_div_lt
    {x : ℝ} {m : ℕ} (hx : 0 < x) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : x / (m : ℝ) < t) :
    roughSaiasRealBaseFreeFractionalKernel x m t = 0 := by
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have htpos : 0 < t := (div_pos hx hmpos).trans ht
  have hx_lt_tm : x < t * (m : ℝ) :=
    (div_lt_iff₀ hmpos).mp ht
  have hloglt : Real.log x < Real.log t + Real.log (m : ℝ) := by
    have h := Real.strictMonoOn_log hx (mul_pos htpos hmpos) hx_lt_tm
    rwa [Real.log_mul htpos.ne' hmpos.ne'] at h
  have harg :
      (Real.log x - Real.log t) / Real.log (m : ℝ) < 1 := by
    rw [div_lt_one (Real.log_pos hmone)]
    linarith
  unfold roughSaiasRealBaseFreeFractionalKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp

/-- The five-face condition puts a positive real endpoint below the fixed
base-change cap. -/
theorem roughSaiasReal_le_rpow_five
    {x : ℝ} {m : ℕ} (hx : 0 < x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    x ≤ (m : ℝ) ^ (5 : ℝ) := by
  have hmpos : 0 < (m : ℝ) := by positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
  have hlogx : Real.log x ≤ 5 * Real.log (m : ℝ) :=
    (div_le_iff₀ hlogm).mp hu5
  have hcappos : 0 < (m : ℝ) ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos hmpos 5
  apply (Real.log_le_log_iff hx hcappos).mp
  rw [Real.log_rpow hmpos]
  exact hlogx

/-- The real base-free correction can be capped at its outer endpoint. -/
theorem roughSaiasRealBaseFreeFractionalIntegral_eq_realCap
    {x : ℝ} {m : ℕ} (hx1 : 1 ≤ x) (hm2 : 2 ≤ m)
    (hu5 : Real.log x / Real.log (m : ℝ) ≤ 5) :
    roughSaiasRealBaseFreeFractionalIntegral x m =
      ∫ t in (1 : ℝ)..x,
        roughSaiasRealBaseFreeFractionalKernel x m t := by
  have hx : 0 < x := zero_lt_one.trans_le hx1
  have hcap := roughSaiasReal_le_rpow_five hx hm2 hu5
  have hxmem : x ∈ Set.uIcc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    rw [Set.uIcc_of_le (hx1.trans hcap)]
    exact ⟨hx1, hcap⟩
  have hint := roughSaiasRealBaseFreeFractionalKernel_intervalIntegrable
    (x := x) (m := m) hm2 hu5
  have hparts := (IntervalIntegrable.trans_iff hxmem).mp hint
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hdivlt : x / (m : ℝ) < x := div_lt_self hx hmone
  have htail :
      (∫ t in x..(m : ℝ) ^ (5 : ℝ),
          roughSaiasRealBaseFreeFractionalKernel x m t) = 0 := by
    calc
      _ = ∫ _t in x..(m : ℝ) ^ (5 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have htI : t ∈ Set.Icc x ((m : ℝ) ^ (5 : ℝ)) := by
          rw [Set.uIcc_of_le hcap] at ht
          exact ht
        exact roughSaiasRealBaseFreeFractionalKernel_eq_zero_of_div_lt
          hx hm2 (hdivlt.trans_le htI.1)
      _ = 0 := by simp
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hparts.1 hparts.2
  unfold roughSaiasRealBaseFreeFractionalIntegral
  rw [← hsplit, htail, add_zero]

/-- At a real endpoint, `G_m` is `rho` minus the real base-free integral. -/
theorem roughSaiasG_at_realEndpoint_eq_realBaseFree
    {x : ℝ} {m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasG m (Real.log x / Real.log (m : ℝ)) =
      Erdos390.Full.DickmanBasic.rho
          (Real.log x / Real.log (m : ℝ)) -
        roughSaiasRealBaseFreeFractionalIntegral x m := by
  unfold roughSaiasG
  rw [roughSaiasFractionalIntegral_eq_realBaseFree hm2]

end

end Erdos390.WholePaper
