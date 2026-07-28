import Erdos390.WholePaper.RoughSaiasSignedFractionalAbel
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Base-free sawtooth coordinates for the Saias correction

The difficult base variation in `roughSaiasG m` contains
`fract(m^v) * m^(-v)`.  This file records the exact substitution `t=m^v`
before any absolute value is taken.  After multiplication by the Jacobian,
the sawtooth is `fract(t)`, independent of `m`; all base dependence is left
in the logarithmic Dickman kernel and the factor `1 / log m`.

This is an exact identity for the finite `[0,5]` integral.  The one-variable
Jacobian theorem is used because its monotone form permits the discontinuous
fractional-part integrand.
-/

open scoped Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-- Dickman coordinate after `t=m^v`. -/
noncomputable def roughSaiasBaseFreeDickmanCoordinate
    (q m : ℕ) (t : ℝ) : ℝ :=
  Real.log (q : ℝ) / Real.log (m : ℝ) -
    Real.log t / Real.log (m : ℝ)

/-- The base-dependent part of the transformed kernel. -/
noncomputable def roughSaiasScaledDickmanKernel
    (q m : ℕ) (t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      (roughSaiasBaseFreeDickmanCoordinate q m t) /
    Real.log (m : ℝ)

/-- The Saias fractional kernel after the exact change of variables
`t=m^v`.  In particular, its sawtooth factor `fract(t)` is base-free. -/
noncomputable def roughSaiasBaseFreeFractionalKernel
    (q m : ℕ) (t : ℝ) : ℝ :=
  roughSaiasDickmanDerivative
      (Real.log (q : ℝ) / Real.log (m : ℝ) -
        Real.log t / Real.log (m : ℝ)) *
    Int.fract t /
      (Real.log (m : ℝ) * t ^ (2 : ℕ))

/-- The transformed coordinate is a single log difference divided by the
base logarithm. -/
theorem roughSaiasBaseFreeDickmanCoordinate_eq_sub_div
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeDickmanCoordinate q m t =
      (Real.log (q : ℝ) - Real.log t) / Real.log (m : ℝ) := by
  unfold roughSaiasBaseFreeDickmanCoordinate
  ring

/-- On the positive segment `t ≤ q`, increasing the base decreases the
transformed Dickman coordinate.  This is the monotone piece relevant on the
effective support `t ≤ q/m`. -/
theorem roughSaiasBaseFreeDickmanCoordinate_succ_le
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t) (htq : t ≤ (q : ℝ)) :
    roughSaiasBaseFreeDickmanCoordinate q (m + 1) t ≤
      roughSaiasBaseFreeDickmanCoordinate q m t := by
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogNumerator : 0 ≤ Real.log (q : ℝ) - Real.log t :=
    sub_nonneg.mpr (Real.log_le_log htpos htq)
  have hlogBase :
      Real.log (m : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log hmpos
      (by exact_mod_cast (show m ≤ m + 1 by omega))
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
    roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
  exact div_le_div_of_nonneg_left hlogNumerator
    (Real.log_pos hmone) hlogBase

/-- Exact size of the coordinate displacement between consecutive bases. -/
theorem roughSaiasBaseFreeDickmanCoordinate_sub_succ
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeDickmanCoordinate q m t -
        roughSaiasBaseFreeDickmanCoordinate q (m + 1) t =
      (Real.log (q : ℝ) - Real.log t) *
        (1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
    roughSaiasBaseFreeDickmanCoordinate_eq_sub_div]
  ring

/-- Throughout the effective support `t ≤ q/m`, the transformed coordinate
lies on the non-initial Dickman faces (`u ≥ 1`). -/
theorem one_le_roughSaiasBaseFreeDickmanCoordinate_of_le_div
    {q m : ℕ} (hm2 : 2 ≤ m) {t : ℝ}
    (htpos : 0 < t) (ht : t ≤ (q : ℝ) / (m : ℝ)) :
    1 ≤ roughSaiasBaseFreeDickmanCoordinate q m t := by
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have htmq : t * (m : ℝ) ≤ (q : ℝ) :=
    (le_div_iff₀ hmpos).mp ht
  have hlogProduct :
      Real.log t + Real.log (m : ℝ) ≤ Real.log (q : ℝ) := by
    have h := Real.log_le_log (mul_pos htpos hmpos) htmq
    rwa [Real.log_mul htpos.ne' hmpos.ne'] at h
  rw [roughSaiasBaseFreeDickmanCoordinate_eq_sub_div,
    one_le_div (Real.log_pos hmone)]
  linarith

/-- The sawtooth factor is common to all bases.  Every base-dependent term
is confined to `roughSaiasScaledDickmanKernel`. -/
theorem roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeFractionalKernel q m t =
      (Int.fract t / t ^ (2 : ℕ)) *
        roughSaiasScaledDickmanKernel q m t := by
  unfold roughSaiasBaseFreeFractionalKernel
    roughSaiasScaledDickmanKernel
    roughSaiasBaseFreeDickmanCoordinate
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Exact signed base difference with the base-free sawtooth factored only
once. -/
theorem roughSaiasBaseFreeFractionalKernel_succ_sub
    (q m : ℕ) (t : ℝ) :
    roughSaiasBaseFreeFractionalKernel q (m + 1) t -
        roughSaiasBaseFreeFractionalKernel q m t =
      (Int.fract t / t ^ (2 : ℕ)) *
        (roughSaiasScaledDickmanKernel q (m + 1) t -
          roughSaiasScaledDickmanKernel q m t) := by
  rw [roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled,
    roughSaiasBaseFreeFractionalKernel_eq_sawtooth_mul_scaled]
  ring

/-- The remaining smooth-kernel variation splits exactly into a Dickman
translation at the next logarithmic scale and the change of the `1/log m`
coefficient.  Both pieces remain under the one common sawtooth integral. -/
theorem roughSaiasScaledDickmanKernel_succ_sub
    (q m : ℕ) (t : ℝ) :
    roughSaiasScaledDickmanKernel q (m + 1) t -
        roughSaiasScaledDickmanKernel q m t =
      (roughSaiasDickmanDerivative
          (roughSaiasBaseFreeDickmanCoordinate q (m + 1) t) -
        roughSaiasDickmanDerivative
          (roughSaiasBaseFreeDickmanCoordinate q m t)) /
          Real.log ((m + 1 : ℕ) : ℝ) +
        roughSaiasDickmanDerivative
            (roughSaiasBaseFreeDickmanCoordinate q m t) *
          (1 / Real.log ((m + 1 : ℕ) : ℝ) -
            1 / Real.log (m : ℝ)) := by
  unfold roughSaiasScaledDickmanKernel
  ring

/-- The transformed kernel is supported below the natural quotient scale
`q/m`.  Above that scale the Dickman-derivative argument is strictly below
one.  The statement is pointwise, so no regularity of `fract` is needed. -/
theorem roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) {t : ℝ}
    (ht : (q : ℝ) / (m : ℝ) < t) :
    roughSaiasBaseFreeFractionalKernel q m t = 0 := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have htpos : 0 < t :=
    (div_pos hqpos hmpos).trans ht
  have hq_lt_tm : (q : ℝ) < t * (m : ℝ) :=
    (div_lt_iff₀ hmpos).mp ht
  have hloglt :
      Real.log (q : ℝ) < Real.log t + Real.log (m : ℝ) := by
    have h := Real.strictMonoOn_log hqpos (mul_pos htpos hmpos) hq_lt_tm
    rwa [Real.log_mul htpos.ne' hmpos.ne'] at h
  have harg :
      Real.log (q : ℝ) / Real.log (m : ℝ) -
          Real.log t / Real.log (m : ℝ) < 1 := by
    rw [← sub_div, div_lt_one (Real.log_pos hmone)]
    linarith
  unfold roughSaiasBaseFreeFractionalKernel
  rw [roughSaiasDickmanDerivative_of_lt_one harg]
  simp

/-- For a positive natural quotient, its logarithmic coordinate decreases
when the base is incremented. -/
theorem roughSaiasNatQuotientLogRatio_succ_le
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m) :
    Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤
      Real.log (q : ℝ) / Real.log (m : ℝ) := by
  have h := roughSaiasBaseFreeDickmanCoordinate_succ_le
    (q := q) hm2 (t := (1 : ℝ)) (by norm_num)
      (by exact_mod_cast hq1)
  simpa [roughSaiasBaseFreeDickmanCoordinate] using h

/-- The five-face condition places the next-base support cutoff strictly
below the old artificial endpoint `m^5`. -/
theorem roughSaiasNatQuotient_div_succ_lt_rpow_five
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    (q : ℝ) / ((m + 1 : ℕ) : ℝ) < (m : ℝ) ^ (5 : ℝ) := by
  have hqpos : 0 < (q : ℝ) := by
    exact_mod_cast (show 0 < q by omega)
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos hmone
  have hlogq :
      Real.log (q : ℝ) ≤ 5 * Real.log (m : ℝ) :=
    (div_le_iff₀ hlogm).mp hu5
  have hpowpos : 0 < (m : ℝ) ^ (5 : ℝ) :=
    Real.rpow_pos_of_pos hmpos 5
  have hqpow : (q : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) := by
    apply (Real.log_le_log_iff hqpos hpowpos).mp
    rw [Real.log_rpow hmpos]
    exact hlogq
  have hdivle :
      (q : ℝ) / ((m + 1 : ℕ) : ℝ) ≤
        (m : ℝ) ^ (5 : ℝ) / ((m + 1 : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hqpow (by positivity)
  have hdivlt :
      (m : ℝ) ^ (5 : ℝ) / ((m + 1 : ℕ) : ℝ) <
        (m : ℝ) ^ (5 : ℝ) :=
    div_lt_self hpowpos
      (by exact_mod_cast (show 1 < m + 1 by omega))
  exact hdivle.trans_lt hdivlt

/-- On five faces the upper-endpoint tail created by changing from `m^5`
to `(m+1)^5` is identically zero, because it lies beyond the transformed
support. -/
theorem roughSaiasBaseFreeFractionalKernel_succ_tail_eq_zero
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    (∫ t in (m : ℝ) ^ (5 : ℝ)..
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
      roughSaiasBaseFreeFractionalKernel q (m + 1) t) = 0 := by
  have hcut := roughSaiasNatQuotient_div_succ_lt_rpow_five
    hq1 hm2 hu5
  have hupper :
      (m : ℝ) ^ (5 : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show m ≤ m + 1 by omega)) (by norm_num)
  calc
    (∫ t in (m : ℝ) ^ (5 : ℝ)..
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
      roughSaiasBaseFreeFractionalKernel q (m + 1) t) =
        ∫ _t in (m : ℝ) ^ (5 : ℝ)..
          ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ), (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htI :
          t ∈ Icc ((m : ℝ) ^ (5 : ℝ))
            (((m + 1 : ℕ) : ℝ) ^ (5 : ℝ)) := by
        rw [uIcc_of_le hupper] at ht
        exact ht
      exact roughSaiasBaseFreeFractionalKernel_eq_zero_of_div_lt
        hq1 (by omega) (hcut.trans_le htI.1)
    _ = 0 := by simp

/-- Pointwise Jacobian cancellation for `t=m^v`.  This is the algebraic
heart of the base-free representation and retains the signed sawtooth. -/
theorem roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
    {q m : ℕ} (hm2 : 2 ≤ m) (v : ℝ) :
    (Real.log (m : ℝ) * (m : ℝ) ^ v) *
        roughSaiasBaseFreeFractionalKernel q m ((m : ℝ) ^ v) =
      roughSaiasDickmanDerivative
          (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
        roughSaiasFractionalWeight m v := by
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hlogm : Real.log (m : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos hmone)
  have hrpow : (m : ℝ) ^ v ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos hmpos v)
  have hcancel :
      v * Real.log (m : ℝ) / Real.log (m : ℝ) = v := by
    field_simp [hlogm]
  unfold roughSaiasBaseFreeFractionalKernel
    roughSaiasFractionalWeight
  rw [Real.log_rpow hmpos, hcancel, Real.rpow_neg hmpos.le]
  field_simp [hlogm, hrpow]

/-- The transformed finite correction integral. -/
noncomputable def roughSaiasBaseFreeFractionalIntegral
    (q m : ℕ) : ℝ :=
  ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
    roughSaiasBaseFreeFractionalKernel q m t

/-- Exact change of variables in the signed Saias correction integral.
Unlike the usual continuous substitution lemma, this proof does not require
continuity of `fract`: monotonicity of `v ↦ m^v` is sufficient. -/
theorem roughSaiasFractionalIntegral_eq_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
      roughSaiasBaseFreeFractionalIntegral q m := by
  let f : ℝ → ℝ := fun v => (m : ℝ) ^ v
  let f' : ℝ → ℝ := fun v =>
    Real.log (m : ℝ) * (m : ℝ) ^ v
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hfderiv : ∀ v ∈ Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hmpos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hmone).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hmpos.ne').continuousOn
  have hfimage :
      f '' Icc (0 : ℝ) 5 =
        Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    calc
      f '' Icc (0 : ℝ) 5 = Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
        simp [f]
  have hchange :
      (∫ t in f '' Icc (0 : ℝ) 5,
          roughSaiasBaseFreeFractionalKernel q m t) =
        ∫ v in Icc (0 : ℝ) 5,
          f' v • roughSaiasBaseFreeFractionalKernel q m (f v) :=
    MeasureTheory.integral_image_eq_integral_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasBaseFreeFractionalKernel q m)
  have hpoint (v : ℝ) :
      f' v • roughSaiasBaseFreeFractionalKernel q m (f v) =
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v := by
    simpa [f, f', smul_eq_mul] using
      roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
        (q := q) hm2 v
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  unfold roughSaiasBaseFreeFractionalIntegral
  calc
    (∫ v in (0 : ℝ)..5,
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v) =
        ∫ v in Icc (0 : ℝ) 5,
          roughSaiasDickmanDerivative
              (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
            roughSaiasFractionalWeight m v := by
      rw [intervalIntegral.integral_of_le (by norm_num),
        MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = ∫ v in Icc (0 : ℝ) 5,
          f' v • roughSaiasBaseFreeFractionalKernel q m (f v) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v _hv
      exact (hpoint v).symm
    _ = ∫ t in Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)),
          roughSaiasBaseFreeFractionalKernel q m t := by
      rw [← hfimage]
      exact hchange.symm
    _ = ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q m t := by
      rw [intervalIntegral.integral_of_le hu,
        MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- Integrability of the transformed kernel on its finite interval, obtained
from the already proved integrability of the original Saias integrand and
the same monotone Jacobian. -/
theorem roughSaiasBaseFreeFractionalKernel_intervalIntegrable
    {q m : ℕ} (hm2 : 2 ≤ m)
    (hu5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    IntervalIntegrable (roughSaiasBaseFreeFractionalKernel q m)
      volume (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
  let f : ℝ → ℝ := fun v => (m : ℝ) ^ v
  let f' : ℝ → ℝ := fun v =>
    Real.log (m : ℝ) * (m : ℝ) ^ v
  have hmpos : 0 < (m : ℝ) := by
    positivity
  have hmone : 1 < (m : ℝ) := by
    exact_mod_cast (show 1 < m by omega)
  have hfderiv : ∀ v ∈ Icc (0 : ℝ) 5,
      HasDerivWithinAt f (f' v) (Icc (0 : ℝ) 5) v := by
    intro v _hv
    simpa [f, f'] using
      ((hasDerivAt_id v).const_rpow hmpos).hasDerivWithinAt
  have hfmono : MonotoneOn f (Icc (0 : ℝ) 5) :=
    (Real.strictMono_rpow_of_base_gt_one hmone).monotone.monotoneOn _
  have hfcont : ContinuousOn f (Icc (0 : ℝ) 5) :=
    (Real.continuous_const_rpow hmpos.ne').continuousOn
  have hfimage :
      f '' Icc (0 : ℝ) 5 =
        Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    calc
      f '' Icc (0 : ℝ) 5 = Icc (f 0) (f 5) :=
        hfcont.image_Icc_of_monotoneOn (by norm_num) hfmono
      _ = Icc (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
        simp [f]
  have horiginal : IntervalIntegrable
      (fun v : ℝ =>
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v)
      volume 0 5 :=
    roughSaiasIntegrand_intervalIntegrable hm2 hu5
  have horiginalIcc : IntegrableOn
      (fun v : ℝ =>
        roughSaiasDickmanDerivative
            (Real.log (q : ℝ) / Real.log (m : ℝ) - v) *
          roughSaiasFractionalWeight m v)
      (Icc (0 : ℝ) 5) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mp
      horiginal
  have hjacobianIcc : IntegrableOn
      (fun v : ℝ =>
        f' v • roughSaiasBaseFreeFractionalKernel q m (f v))
      (Icc (0 : ℝ) 5) := by
    apply horiginalIcc.congr_fun _ measurableSet_Icc
    intro v _hv
    simpa [f, f', smul_eq_mul] using
      (roughSaiasBaseFreeFractionalKernel_rpow_mul_jacobian
        (q := q) hm2 v).symm
  have hkernelImage : IntegrableOn
      (roughSaiasBaseFreeFractionalKernel q m)
      (f '' Icc (0 : ℝ) 5) :=
    (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
      measurableSet_Icc hfderiv hfmono
        (roughSaiasBaseFreeFractionalKernel q m)).mpr hjacobianIcc
  rw [hfimage] at hkernelImage
  have hu : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le hu).mpr hkernelImage

/-- Exact consecutive-base variation of the transformed correction integral.
The common-range integral keeps the two kernels together under one signed
`fract(t)` factor; the only extra term is the literal upper-endpoint tail. -/
theorem roughSaiasBaseFreeFractionalIntegral_succ_sub
    {q m : ℕ} (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5)
    (husucc5 :
      Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (roughSaiasBaseFreeFractionalKernel q (m + 1) t -
            roughSaiasBaseFreeFractionalKernel q m t)) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t := by
  have hnow :=
    roughSaiasBaseFreeFractionalKernel_intervalIntegrable hm2 hum5
  have hnext :=
    roughSaiasBaseFreeFractionalKernel_intervalIntegrable
      (m := m + 1) (by omega) husucc5
  have huNow : (1 : ℝ) ≤ (m : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ m by omega)) (by norm_num)
  have huNext :
      (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.one_le_rpow
      (by exact_mod_cast (show 1 ≤ m + 1 by omega)) (by norm_num)
  have hupper :
      (m : ℝ) ^ (5 : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ) :=
    Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast (show m ≤ m + 1 by omega)) (by norm_num)
  have hnextCommon : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel q (m + 1)) volume
      (1 : ℝ) ((m : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le huNow, uIcc_of_le huNext]
    exact Icc_subset_Icc le_rfl hupper
  have hnextTail : IntervalIntegrable
      (roughSaiasBaseFreeFractionalKernel q (m + 1)) volume
      ((m : ℝ) ^ (5 : ℝ))
      (((m + 1 : ℕ) : ℝ) ^ (5 : ℝ)) := by
    apply hnext.mono_set
    rw [uIcc_of_le hupper, uIcc_of_le huNext]
    exact Icc_subset_Icc huNow le_rfl
  have hsplit := intervalIntegral.integral_add_adjacent_intervals
    hnextCommon hnextTail
  have hdiff := intervalIntegral.integral_sub hnextCommon hnow
  unfold roughSaiasBaseFreeFractionalIntegral
  calc
    (∫ t in (1 : ℝ)..((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
        roughSaiasBaseFreeFractionalKernel q (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q m t =
      ((∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q m t := by
      rw [hsplit]
    _ =
      ((∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q m t) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t := by
      ring
    _ =
      (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (roughSaiasBaseFreeFractionalKernel q (m + 1) t -
            roughSaiasBaseFreeFractionalKernel q m t)) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t := by
      rw [hdiff]

/-- The same exact consecutive-base identity with the common sawtooth
factored once throughout the common range. -/
theorem roughSaiasBaseFreeFractionalIntegral_succ_sub_factored
    {q m : ℕ} (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5)
    (husucc5 :
      Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q (m + 1) t -
              roughSaiasScaledDickmanKernel q m t)) +
        ∫ t in (m : ℝ) ^ (5 : ℝ)..
            ((m + 1 : ℕ) : ℝ) ^ (5 : ℝ),
          roughSaiasBaseFreeFractionalKernel q (m + 1) t := by
  have hcommon :
      (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (roughSaiasBaseFreeFractionalKernel q (m + 1) t -
            roughSaiasBaseFreeFractionalKernel q m t)) =
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q (m + 1) t -
              roughSaiasScaledDickmanKernel q m t) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    exact roughSaiasBaseFreeFractionalKernel_succ_sub q m t
  rw [roughSaiasBaseFreeFractionalIntegral_succ_sub hm2 hum5 husucc5,
    hcommon]

/-- On the five Dickman faces the exact base variation has no endpoint
tail at all: it is one common-range signed integral with the base-free
sawtooth factored once. -/
theorem roughSaiasBaseFreeFractionalIntegral_succ_sub_eq_common
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q (m + 1) t -
            roughSaiasScaledDickmanKernel q m t) := by
  have husucc5 :
      Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ) ≤ 5 :=
    (roughSaiasNatQuotientLogRatio_succ_le hq1 hm2).trans hum5
  rw [roughSaiasBaseFreeFractionalIntegral_succ_sub_factored
      hm2 hum5 husucc5,
    roughSaiasBaseFreeFractionalKernel_succ_tail_eq_zero hq1 hm2 hum5,
    add_zero]

/-- Fully expanded signed base variation on five faces.  The Dickman
translation and inverse-log coefficient change are added inside the same
base-free-sawtooth integral. -/
theorem roughSaiasBaseFreeFractionalIntegral_succ_sub_eq_translation
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasBaseFreeFractionalIntegral q (m + 1) -
        roughSaiasBaseFreeFractionalIntegral q m =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (((roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q (m + 1) t) -
              roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q m t)) /
              Real.log ((m + 1 : ℕ) : ℝ)) +
            roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q m t) *
              (1 / Real.log ((m + 1 : ℕ) : ℝ) -
                1 / Real.log (m : ℝ))) := by
  have hexpand :
      (∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (roughSaiasScaledDickmanKernel q (m + 1) t -
            roughSaiasScaledDickmanKernel q m t)) =
      ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
        (Int.fract t / t ^ (2 : ℕ)) *
          (((roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q (m + 1) t) -
              roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q m t)) /
              Real.log ((m + 1 : ℕ) : ℝ)) +
            roughSaiasDickmanDerivative
                (roughSaiasBaseFreeDickmanCoordinate q m t) *
              (1 / Real.log ((m + 1 : ℕ) : ℝ) -
                1 / Real.log (m : ℝ))) := by
    apply intervalIntegral.integral_congr
    intro t _ht
    simp only [roughSaiasScaledDickmanKernel_succ_sub]
  rw [roughSaiasBaseFreeFractionalIntegral_succ_sub_eq_common
      hq1 hm2 hum5,
    hexpand]

/-- At a natural quotient, `G_m` is exactly `rho` minus the transformed
base-free-sawtooth integral. -/
theorem roughSaiasG_at_natQuotient_eq_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasG m
        (Real.log (q : ℝ) / Real.log (m : ℝ)) =
      rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
        roughSaiasBaseFreeFractionalIntegral q m := by
  unfold roughSaiasG
  rw [roughSaiasFractionalIntegral_eq_baseFree hm2]

/-- Exact consecutive-base structure of
`m ↦ G_m(log q / log m)` on five faces.  The rho displacement and the
single common-sawtooth correction remain signed against one another. -/
theorem roughSaiasG_at_natQuotient_succ_sub_eq_common
    {q m : ℕ} (hq1 : 1 ≤ q) (hm2 : 2 ≤ m)
    (hum5 : Real.log (q : ℝ) / Real.log (m : ℝ) ≤ 5) :
    roughSaiasG (m + 1)
          (Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ)) -
        roughSaiasG m
          (Real.log (q : ℝ) / Real.log (m : ℝ)) =
      (rho (Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ)) -
        rho (Real.log (q : ℝ) / Real.log (m : ℝ))) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q (m + 1) t -
              roughSaiasScaledDickmanKernel q m t) := by
  have hI := roughSaiasBaseFreeFractionalIntegral_succ_sub_eq_common
    hq1 hm2 hum5
  rw [roughSaiasG_at_natQuotient_eq_baseFree (m := m + 1) (by omega),
    roughSaiasG_at_natQuotient_eq_baseFree (m := m) hm2]
  calc
    (rho (Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ)) -
          roughSaiasBaseFreeFractionalIntegral q (m + 1)) -
        (rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
          roughSaiasBaseFreeFractionalIntegral q m) =
      (rho (Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ)) -
        rho (Real.log (q : ℝ) / Real.log (m : ℝ))) -
        (roughSaiasBaseFreeFractionalIntegral q (m + 1) -
          roughSaiasBaseFreeFractionalIntegral q m) := by
      ring
    _ =
      (rho (Real.log (q : ℝ) / Real.log ((m + 1 : ℕ) : ℝ)) -
        rho (Real.log (q : ℝ) / Real.log (m : ℝ))) -
        ∫ t in (1 : ℝ)..(m : ℝ) ^ (5 : ℝ),
          (Int.fract t / t ^ (2 : ℕ)) *
            (roughSaiasScaledDickmanKernel q (m + 1) t -
              roughSaiasScaledDickmanKernel q m t) := by
      rw [hI]

/-! ## Exact floor/base pairing in the transformed coordinate -/

/-- Natural main term at a fixed quotient, written with the base-free
sawtooth integral. -/
theorem roughSaiasNaturalMain_eq_rho_sub_baseFree
    {q m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalMain q m =
      (q : ℝ) *
        (rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
          roughSaiasBaseFreeFractionalIntegral q m) := by
  unfold roughSaiasNaturalMain FriableAsymptotic.dickmanU
  rw [roughSaiasG_at_natQuotient_eq_baseFree hm2]

/-- The natural theta weight in base-free sawtooth coordinates.  The
quotient parameter is explicit, so it can be held fixed on a hyperbola
block while the base varies. -/
noncomputable def roughSaiasBaseFreeNaturalThetaWeight
    (q m : ℕ) : ℝ :=
  ((q : ℝ) *
      (rho (Real.log (q : ℝ) / Real.log (m : ℝ)) -
        roughSaiasBaseFreeFractionalIntegral q m)) /
    Real.log (m : ℝ)

/-- Exact identification of the floor/frac-paired natural weight with the
base-free-sawtooth representation. -/
theorem roughSaiasNaturalQuotientThetaWeight_eq_baseFree
    {X m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight (X / m) m := by
  unfold roughSaiasNaturalQuotientThetaWeight
    roughSaiasBaseFreeNaturalThetaWeight
  rw [roughSaiasNaturalMain_eq_rho_sub_baseFree hm2]

/-- Exact consecutive-base variation with quotient jumps retained.  On a
block where `X/(m+1)=X/m`, both terms use the same quotient and the same
base-free sawtooth variable `t`. -/
theorem roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree
    {X m : ℕ} (hm2 : 2 ≤ m) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight (X / (m + 1)) (m + 1) -
        roughSaiasBaseFreeNaturalThetaWeight (X / m) m := by
  rw [roughSaiasNaturalQuotientThetaWeight_eq_baseFree (by omega),
    roughSaiasNaturalQuotientThetaWeight_eq_baseFree hm2]

/-- Stable-quotient specialization of the preceding exact variation. -/
theorem roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree_on_block
    {X q m : ℕ} (hm2 : 2 ≤ m)
    (hnext : X / (m + 1) = q) (hnow : X / m = q) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      roughSaiasBaseFreeNaturalThetaWeight q (m + 1) -
        roughSaiasBaseFreeNaturalThetaWeight q m := by
  rw [roughSaiasNaturalQuotientThetaWeight_diff_eq_baseFree hm2,
    hnext, hnow]

/-! ## The signed center as a base-free quotient-block sum -/

/-- Integer Abel consistency with every summand already written in the
base-free sawtooth coordinate. -/
noncomputable def roughSaiasBaseFreeIntegerConsistency
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    ∑ m ∈ Finset.Ioc y Z,
      roughSaiasBaseFreeNaturalThetaWeight (X / m) m

/-- Exact conversion of the natural integer consistency term into the
base-free quotient-block sum. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_eq_baseFree
    {X y Z : ℕ} (hy1 : 1 ≤ y) (hyZ : y < Z) :
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      roughSaiasBaseFreeIntegerConsistency X y Z := by
  unfold roughSaiasNaturalIntegerAbelConsistencyDefect
    roughSaiasBaseFreeIntegerConsistency
  rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hm2 : 2 ≤ m := by
    rw [Finset.mem_Ioc] at hm
    omega
  exact roughSaiasNaturalQuotientThetaWeight_eq_baseFree hm2

/-- Exact signed-center representation below the theta step: an explicit
base-free quotient-block consistency sum plus the still-signed fractional
theta transfer. -/
theorem roughSaiasSignedAbelCenter_eq_baseFree_add_fractionalTheta
    {X y Z : ℕ} (hy1 : 1 ≤ y) (hyZ : y < Z) :
    roughSaiasSignedAbelCenter X y Z =
      roughSaiasBaseFreeIntegerConsistency X y Z +
        roughSaiasFractionalThetaErrorTransfer X y Z := by
  rw [roughSaiasSignedAbelCenter_eq_natural_add_fractionalTheta hyZ,
    roughSaiasNaturalIntegerAbelConsistencyDefect_eq_baseFree hy1 hyZ]

end

end Erdos390.WholePaper
