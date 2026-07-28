import Erdos390.Full.FriableAsymptotic
import Erdos390.Full.PrimeSums

/-!
# Audited harmonic prime quadrature on moving positive cells

The continuum transfer in Lemma 8.4 uses prime cells whose endpoints are
powers of the smoothness scale.  This file starts the required arithmetic
quadrature from the actual Chebyshev function.  The key identity below has no
Mertens constant: it subtracts Abel summation at two endpoints and isolates
the quantitative PNT remainder exactly.
-/

open scoped BigOperators
open Set
open Filter Topology Asymptotics

noncomputable section

namespace Erdos390.Full.PrimeBandQuadrature

open MeasureTheory
open Erdos390.Full.PrimeSums
open Erdos390.Full.FriableAsymptotic

/-- The main primitive in Abel summation for the prime harmonic sum. -/
def mertensMainPrimitive (x : ℝ) : ℝ :=
  Real.log (Real.log x) - (Real.log x)⁻¹

/-- The corresponding main integrand. -/
def mertensMainKernel (x : ℝ) : ℝ :=
  (Real.log x + 1) / (x * Real.log x ^ 2)

/-- The PNT error occurring after Abel summation. -/
def thetaError (x : ℝ) : ℝ :=
  Chebyshev.theta x - x

/-- The exact error integrand for harmonic prime quadrature. -/
def mertensErrorKernel (x : ℝ) : ℝ :=
  thetaError x * (Real.log x + 1) /
    (x ^ 2 * Real.log x ^ 2)

lemma hasDerivAt_mertensMainPrimitive {x : ℝ} (hx : 1 < x) :
    HasDerivAt mertensMainPrimitive (mertensMainKernel x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
  have hloglog := (Real.hasDerivAt_log hx0).log hlog0
  have hinv := (Real.hasDerivAt_log hx0).inv hlog0
  have hsub := hloglog.sub hinv
  convert hsub using 1
  unfold mertensMainKernel
  field_simp [hx0, hlog0]
  ring

lemma continuousOn_mertensMainKernel {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn mertensMainKernel (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold mertensMainKernel
  exact (((Real.continuousAt_log hx0).add continuousAt_const).div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 2))
    (mul_ne_zero hx0 (pow_ne_zero 2 hlog0))).continuousWithinAt

/-- Exact integral of the Mertens main kernel. -/
lemma integral_mertensMainKernel {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, mertensMainKernel x) =
      mertensMainPrimitive Y - mertensMainPrimitive A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_mertensMainPrimitive (by linarith [hx.1, hA])
  · exact (continuousOn_mertensMainKernel (by linarith [hA]))
      |>.intervalIntegrable_of_Icc hAY

private def mertensAbelKernel (x : ℝ) : ℝ :=
  Chebyshev.theta x * (Real.log x + 1) /
    (x ^ 2 * Real.log x ^ 2)

private lemma mertensAbelKernel_eq_main_add_error {x : ℝ} (hx : 1 < x) :
    mertensAbelKernel x =
      mertensMainKernel x + mertensErrorKernel x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  unfold mertensAbelKernel mertensMainKernel mertensErrorKernel thetaError
  field_simp [hx0, hlog0]
  ring

private lemma intervalIntegrable_mertensAbelKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable mertensAbelKernel volume A Y := by
  have h2Y : (2 : ℝ) ≤ Y := hA.trans hAY
  have hfull :=
    Erdos390.Full.PrimeSums.intervalIntegrable_mertensIntegrand h2Y
  apply hfull.mono_set
  rw [uIcc_of_le hAY, uIcc_of_le h2Y]
  intro x hx
  exact ⟨hA.trans hx.1, hx.2⟩

private lemma integral_mertensAbelKernel_sub {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (2 : ℝ)..Y, mertensAbelKernel x) -
        (∫ x in (2 : ℝ)..A, mertensAbelKernel x) =
      ∫ x in (A : ℝ)..Y, mertensAbelKernel x := by
  have h2A : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hleft : IntervalIntegrable mertensAbelKernel volume 2 (A : ℝ) := by
    simpa only [mertensAbelKernel] using
      (Erdos390.Full.PrimeSums.intervalIntegrable_mertensIntegrand h2A)
  have hright : IntervalIntegrable mertensAbelKernel volume (A : ℝ) (Y : ℝ) :=
    intervalIntegrable_mertensAbelKernel h2A hAYR
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

private lemma intervalIntegrable_mertensErrorKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable mertensErrorKernel volume A Y := by
  have habel := intervalIntegrable_mertensAbelKernel hA hAY
  have hmain : IntervalIntegrable mertensMainKernel volume A Y :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_mertensMainKernel (A := A) (Y := Y)
        (by linarith [hA]))
  have hsub := habel.sub hmain
  apply hsub.congr
  intro x hx
  change mertensAbelKernel x - mertensMainKernel x =
    mertensErrorKernel x
  rw [mertensAbelKernel_eq_main_add_error (by
    rw [uIoc_of_le hAY] at hx
    linarith [hx.1, hA])]
  ring

/-- Exact two-endpoint harmonic-prime identity.  All nonconstant arithmetic
content is isolated in thetaError; in particular no Mertens constant is
introduced or assumed. -/
theorem fullReciprocalSum_interval_error_identity {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) =
      thetaError (Y : ℝ) /
          ((Y : ℝ) * Real.log (Y : ℝ)) -
      thetaError (A : ℝ) /
          ((A : ℝ) * Real.log (A : ℝ)) +
      ∫ x in (A : ℝ)..Y, mertensErrorKernel x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hmain := integral_mertensMainKernel hAR hAYR
  have herrInt := intervalIntegrable_mertensErrorKernel hAR hAYR
  have hmainInt : IntervalIntegrable mertensMainKernel volume (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAYR
      (continuousOn_mertensMainKernel
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have hsplit :
      (∫ x in (A : ℝ)..Y, mertensAbelKernel x) =
        (∫ x in (A : ℝ)..Y, mertensMainKernel x) +
          ∫ x in (A : ℝ)..Y, mertensErrorKernel x := by
    rw [← intervalIntegral.integral_add hmainInt herrInt]
    apply intervalIntegral.integral_congr
    intro x hx
    exact mertensAbelKernel_eq_main_add_error (by
      rw [uIcc_of_le hAYR] at hx
      linarith [hx.1, hAR])
  rw [Erdos390.Full.PrimeSums.fullReciprocalSum_eq Y hY,
    Erdos390.Full.PrimeSums.fullReciprocalSum_eq A hA]
  have habelSub := integral_mertensAbelKernel_sub hA hAY
  calc
    (Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) +
          (∫ x in (2 : ℝ)..Y, mertensAbelKernel x)) -
        (Chebyshev.theta (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
          ∫ x in (2 : ℝ)..A, mertensAbelKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) =
      Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
        Chebyshev.theta (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
        ((∫ x in (2 : ℝ)..Y, mertensAbelKernel x) -
          ∫ x in (2 : ℝ)..A, mertensAbelKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) := by ring
    _ = Chebyshev.theta (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
        Chebyshev.theta (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
        (∫ x in (A : ℝ)..Y, mertensMainKernel x) +
        (∫ x in (A : ℝ)..Y, mertensErrorKernel x) -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ))) := by
      rw [habelSub, hsplit]
      ring
    _ = _ := by
      rw [hmain]
      unfold mertensMainPrimitive thetaError
      have hA0 : (A : ℝ) ≠ 0 := by positivity
      have hY0 : (Y : ℝ) ≠ 0 := by positivity
      have hlogA0 : Real.log (A : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < A by omega)))
      have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
        ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
      field_simp [hA0, hY0, hlogA0, hlogY0]
      ring

/-! ## The first logarithmic moment -/

/-- PNT remainder in Abel summation for `sum (log p)/p`. -/
def logReciprocalErrorKernel (x : ℝ) : ℝ :=
  thetaError x / x ^ 2

private lemma intervalIntegrable_thetaDivSq_segment {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable (fun x : ℝ => Chebyshev.theta x / x ^ 2)
      volume A Y := by
  have h2Y : (2 : ℝ) ≤ Y := hA.trans hAY
  have hfull :=
    Erdos390.Full.PrimeSums.intervalIntegrable_theta_div_sq h2Y
  apply hfull.mono_set
  rw [uIcc_of_le hAY, uIcc_of_le h2Y]
  intro x hx
  exact ⟨hA.trans hx.1, hx.2⟩

private lemma integral_thetaDivSq_sub {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
        (∫ x in (2 : ℝ)..A, Chebyshev.theta x / x ^ 2) =
      ∫ x in (A : ℝ)..Y, Chebyshev.theta x / x ^ 2 := by
  have h2A : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hleft :=
    Erdos390.Full.PrimeSums.intervalIntegrable_theta_div_sq h2A
  have hright := intervalIntegrable_thetaDivSq_segment h2A hAYR
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

private lemma intervalIntegrable_oneDiv_segment {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable (fun x : ℝ => 1 / x) volume A Y := by
  apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hA, hx.1]
  exact (continuousAt_const.div continuousAt_id hx0).continuousWithinAt

private lemma intervalIntegrable_logReciprocalErrorKernel {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable logReciprocalErrorKernel volume A Y := by
  have htheta := intervalIntegrable_thetaDivSq_segment hA hAY
  have hmain := intervalIntegrable_oneDiv_segment hA hAY
  apply (htheta.sub hmain).congr
  intro x hx
  have hx0 : x ≠ 0 := by
    rw [uIoc_of_le hAY] at hx
    linarith [hA, hx.1]
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]

private lemma integral_thetaDivSq_split {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, Chebyshev.theta x / x ^ 2) =
      (∫ x in A..Y, 1 / x) +
        ∫ x in A..Y, logReciprocalErrorKernel x := by
  have hmain := intervalIntegrable_oneDiv_segment hA hAY
  have herr := intervalIntegrable_logReciprocalErrorKernel hA hAY
  rw [← intervalIntegral.integral_add hmain herr]
  apply intervalIntegral.integral_congr
  intro x hx
  have hx0 : x ≠ 0 := by
    rw [uIcc_of_le hAY] at hx
    linarith [hA, hx.1]
  unfold logReciprocalErrorKernel thetaError
  field_simp [hx0]
  ring

/-- Exact two-endpoint identity for the first logarithmic prime moment.
It is the arithmetic source of `H_j alpha_j` in the paper. -/
theorem fullLogReciprocalSum_interval_error_identity {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) =
      thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  rw [Erdos390.Full.PrimeSums.fullLogReciprocalSum_eq Y hY,
    Erdos390.Full.PrimeSums.fullLogReciprocalSum_eq A hA]
  have hsub := integral_thetaDivSq_sub hA hAY
  have hsplit := integral_thetaDivSq_split hAR hAYR
  have hmain : (∫ x in (A : ℝ)..Y, 1 / x) =
      Real.log (Y : ℝ) - Real.log (A : ℝ) := by
    rw [integral_one_div_of_pos hApos hYpos,
      Real.log_div (ne_of_gt hYpos) (ne_of_gt hApos)]
  calc
    (Chebyshev.theta (Y : ℝ) / (Y : ℝ) +
          ∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
        (Chebyshev.theta (A : ℝ) / (A : ℝ) +
          ∫ x in (2 : ℝ)..A, Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) =
      Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        ((∫ x in (2 : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
          ∫ x in (2 : ℝ)..A, Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by ring
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        (∫ x in (A : ℝ)..Y, Chebyshev.theta x / x ^ 2) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by rw [hsub]
    _ = Chebyshev.theta (Y : ℝ) / (Y : ℝ) -
        Chebyshev.theta (A : ℝ) / (A : ℝ) +
        ((∫ x in (A : ℝ)..Y, 1 / x) +
          ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x) -
        (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by rw [hsplit]
    _ = thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x := by
      rw [hmain]
      unfold thetaError
      field_simp [ne_of_gt hApos, ne_of_gt hYpos]
      ring

/-! ## Quantitative PNT remainder -/

/-- An elementary majorant for the Abel-summed PNT error. -/
def mertensErrorMajorant (C x : ℝ) : ℝ :=
  3 * C / (x * Real.log x ^ 4)

/-- Primitive of the preceding majorant. -/
def mertensErrorPrimitive (C x : ℝ) : ℝ :=
  -C / Real.log x ^ 3

lemma hasDerivAt_mertensErrorPrimitive (C : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (mertensErrorPrimitive C)
      (mertensErrorMajorant C x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hpow := (Real.hasDerivAt_log hx0).pow 3
  have hinv := hpow.inv (pow_ne_zero 3 hlog0)
  have hmul := (hasDerivAt_const x (-C)).mul hinv
  convert hmul using 1
  unfold mertensErrorMajorant
  simp only [Pi.pow_apply]
  field_simp [hx0, hlog0]
  ring

lemma continuousOn_mertensErrorMajorant (C : ℝ) {A Y : ℝ}
    (hA : 1 < A) :
    ContinuousOn (mertensErrorMajorant C) (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlog0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold mertensErrorMajorant
  exact continuousAt_const.div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 4))
    (mul_ne_zero hx0 (pow_ne_zero 4 hlog0))
    |>.continuousWithinAt

lemma integral_mertensErrorMajorant (C : ℝ) {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, mertensErrorMajorant C x) =
      mertensErrorPrimitive C Y - mertensErrorPrimitive C A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_mertensErrorPrimitive C (by linarith [hx.1, hA])
  · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_mertensErrorMajorant C (A := A) (Y := Y)
        (by linarith [hA]))

/-- A log-power-three PNT bound gives a positive-cell Abel error bounded by
the integrable log-power-four majorant. -/
lemma abs_mertensErrorKernel_le (C : ℝ) (hC : 0 ≤ C)
    {A Y x : ℝ} (hA : 2 ≤ A) (hx : x ∈ Icc A Y)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |mertensErrorKernel x| ≤ mertensErrorMajorant C x := by
  have hx2 : 2 ≤ x := hA.trans hx.1
  have hx0 : 0 < x := by linarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx2
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log x := by linarith
  have hlog0 : Real.log x ≠ 0 := ne_of_gt hlogpos
  have hlogplus : 0 ≤ Real.log x + 1 := by linarith
  have hlogthree : Real.log x + 1 ≤ 3 * Real.log x := by linarith
  unfold mertensErrorKernel mertensErrorMajorant
  rw [abs_div, abs_mul, abs_of_nonneg hlogplus,
    abs_of_pos (mul_pos (sq_pos_of_pos hx0) (sq_pos_of_pos hlogpos))]
  calc
    |thetaError x| * (Real.log x + 1) /
        (x ^ 2 * Real.log x ^ 2) ≤
      (C * x / Real.log x ^ 3) * (3 * Real.log x) /
        (x ^ 2 * Real.log x ^ 2) := by
      gcongr
    _ = 3 * C / (x * Real.log x ^ 4) := by
      field_simp [ne_of_gt hx0, hlog0]

/-- The same PNT input controls the first logarithmic moment after one
Abel summation.  The lower endpoint is retained explicitly because this
is the form used on power-scale prime cells. -/
lemma abs_logReciprocalErrorKernel_le (C : ℝ) (hC : 0 ≤ C)
    {A Y x : ℝ} (hA : 2 ≤ A) (hx : x ∈ Icc A Y)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |logReciprocalErrorKernel x| ≤
      C / (x * Real.log A ^ 3) := by
  have hxpos : 0 < x := by linarith [hA, hx.1]
  have hApos : 0 < A := by linarith
  have hlogApos : 0 < Real.log A := Real.log_pos (by linarith)
  have hlogxpos : 0 < Real.log x := Real.log_pos (by linarith [hx.1, hA])
  have hlogAx : Real.log A ≤ Real.log x :=
    Real.log_le_log hApos hx.1
  have hlogpow : Real.log A ^ 3 ≤ Real.log x ^ 3 := by gcongr
  unfold logReciprocalErrorKernel
  rw [abs_div, abs_of_pos (sq_pos_of_pos hxpos)]
  calc
    |thetaError x| / x ^ 2 ≤
        (C * x / Real.log x ^ 3) / x ^ 2 := by gcongr
    _ = C / (x * Real.log x ^ 3) := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogxpos]
    _ ≤ C / (x * Real.log A ^ 3) := by
      apply div_le_div_of_nonneg_left hC
      · exact mul_pos hxpos (pow_pos hlogApos 3)
      · exact mul_le_mul_of_nonneg_left hlogpow hxpos.le

private lemma intervalIntegrable_logErrorMajorant (C : ℝ) {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable (fun x => C / (x * Real.log A ^ 3))
      volume A Y := by
  have hlogA0 : Real.log A ≠ 0 :=
    ne_of_gt (Real.log_pos (by linarith [hA]))
  apply ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
  intro x hx
  have hx0 : x ≠ 0 := by linarith [hA, hx.1]
  exact (continuousAt_const.div
    (continuousAt_id.mul continuousAt_const)
    (mul_ne_zero hx0 (pow_ne_zero 3 hlogA0))).continuousWithinAt

private lemma integral_logErrorMajorant (C : ℝ) {A Y : ℝ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, C / (x * Real.log A ^ 3)) =
      C / Real.log A ^ 3 * (Real.log Y - Real.log A) := by
  have hApos : 0 < A := by linarith
  have hYpos : 0 < Y := by linarith
  calc
    (∫ x in A..Y, C / (x * Real.log A ^ 3)) =
        ∫ x in A..Y, (C / Real.log A ^ 3) * (1 / x) := by
      apply intervalIntegral.integral_congr
      intro x hx
      ring
    _ = (C / Real.log A ^ 3) * (∫ x in A..Y, 1 / x) :=
      intervalIntegral.integral_const_mul _ _
    _ = C / Real.log A ^ 3 * (Real.log Y - Real.log A) := by
      rw [integral_one_div_of_pos hApos hYpos,
        Real.log_div (ne_of_gt hYpos) (ne_of_gt hApos)]

/-- Explicit positive-cell estimate for the arithmetic first moment
`sum (log p)/p`.  Dividing this estimate by `log y` gives the convergence
of `H_j alpha_j` used in Lemma 8.4. -/
theorem fullLogReciprocalSum_interval_error_bound {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullLogReciprocalSum Y - fullLogReciprocalSum A -
        (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
      C * (2 + (Real.log (Y : ℝ) - Real.log (A : ℝ))) /
        Real.log (A : ℝ) ^ 3 := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogApos : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogYpos : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have herrInt := intervalIntegrable_logReciprocalErrorKernel hAR hAYR
  have hmajorInt := intervalIntegrable_logErrorMajorant C hAR hAYR
  have hIntBound :
      |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
        C / Real.log (A : ℝ) ^ 3 *
          (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by
    calc
      |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
          ∫ x in (A : ℝ)..Y, |logReciprocalErrorKernel x| :=
        intervalIntegral.abs_integral_le_integral_abs hAYR
      _ ≤ ∫ x in (A : ℝ)..Y,
          C / (x * Real.log (A : ℝ) ^ 3) := by
        exact intervalIntegral.integral_mono_on hAYR herrInt.abs hmajorInt
          (fun x hx => abs_logReciprocalErrorKernel_le
            C hC hAR hx (hTheta x hx))
      _ = _ := integral_logErrorMajorant C hAR hAYR
  rw [fullLogReciprocalSum_interval_error_identity hA hAY]
  have hThetaA := hTheta (A : ℝ) ⟨le_rfl, hAYR⟩
  have hThetaY := hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩
  have hAterm :
      |thetaError (A : ℝ) / (A : ℝ)| ≤
        C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hApos]
    calc
      _ ≤ (C * (A : ℝ) / Real.log (A : ℝ) ^ 3) / (A : ℝ) := by
        gcongr
      _ = _ := by field_simp [ne_of_gt hApos]
  have hYterm :
      |thetaError (Y : ℝ) / (Y : ℝ)| ≤
        C / Real.log (A : ℝ) ^ 3 := by
    rw [abs_div, abs_of_pos hYpos]
    calc
      _ ≤ (C * (Y : ℝ) / Real.log (Y : ℝ) ^ 3) / (Y : ℝ) := by
        gcongr
      _ = C / Real.log (Y : ℝ) ^ 3 := by
        field_simp [ne_of_gt hYpos]
      _ ≤ C / Real.log (A : ℝ) ^ 3 := by gcongr
  calc
    |thetaError (Y : ℝ) / (Y : ℝ) -
        thetaError (A : ℝ) / (A : ℝ) +
        ∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| ≤
      |thetaError (Y : ℝ) / (Y : ℝ)| +
        |thetaError (A : ℝ) / (A : ℝ)| +
        |∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x| := by
      have h₁ := abs_add_le
        (thetaError (Y : ℝ) / (Y : ℝ) -
          thetaError (A : ℝ) / (A : ℝ))
        (∫ x in (A : ℝ)..Y, logReciprocalErrorKernel x)
      have h₂ := abs_sub
        (thetaError (Y : ℝ) / (Y : ℝ))
        (thetaError (A : ℝ) / (A : ℝ))
      linarith
    _ ≤ C / Real.log (A : ℝ) ^ 3 +
        C / Real.log (A : ℝ) ^ 3 +
        C / Real.log (A : ℝ) ^ 3 *
          (Real.log (Y : ℝ) - Real.log (A : ℝ)) := by linarith
    _ = C * (2 + (Real.log (Y : ℝ) - Real.log (A : ℝ))) /
        Real.log (A : ℝ) ^ 3 := by ring

/-! ## Exact alignment with the paper's logarithmic coordinate -/

/-- The coordinate `t = log p / log z`, allowing the real smoothness scale
`z` rather than replacing it by its integer floor. -/
def logCoordinate (z : ℝ) (X : ℕ) : ℝ :=
  Real.log (X : ℝ) / Real.log z

lemma logCoordinate_pos {z : ℝ} {X : ℕ} (hz : 1 < z) (hX : 2 ≤ X) :
    0 < logCoordinate z X := by
  exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < X by omega)))
    (Real.log_pos hz)

/-- Rescaling both endpoints by `log z` leaves their harmonic-coordinate
length unchanged. -/
lemma log_logCoordinate_sub {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y) :
    Real.log (logCoordinate z Y) - Real.log (logCoordinate z A) =
      Real.log (Real.log (Y : ℝ)) -
        Real.log (Real.log (A : ℝ)) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  have hlogA0 : Real.log (A : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < A by omega)))
  have hlogY0 : Real.log (Y : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < Y by omega)))
  unfold logCoordinate
  rw [Real.log_div hlogY0 hlogz0, Real.log_div hlogA0 hlogz0]
  ring

/-- The first continuum moment on a logarithmic cell is its ordinary
coordinate length. -/
lemma logCoordinate_sub {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) :
    logCoordinate z Y - logCoordinate z A =
      (Real.log (Y : ℝ) - Real.log (A : ℝ)) / Real.log z := by
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold logCoordinate
  field_simp [hlogz0]

/-- Positive-cell first moment written directly as
`sum (log p)/(p log z)`, with continuum main term `t_Y-t_A`. -/
theorem firstMomentCell_coordinate_error_bound {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y)
    {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |(fullLogReciprocalSum Y - fullLogReciprocalSum A) /
          Real.log z -
        (logCoordinate z Y - logCoordinate z A)| ≤
      (C * (2 + (Real.log (Y : ℝ) - Real.log (A : ℝ))) /
          Real.log (A : ℝ) ^ 3) / Real.log z := by
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hbase :=
    fullLogReciprocalSum_interval_error_bound hA hAY hC hTheta
  rw [logCoordinate_sub hz]
  have hrearrange :
      (fullLogReciprocalSum Y - fullLogReciprocalSum A) /
            Real.log z -
          (Real.log (Y : ℝ) - Real.log (A : ℝ)) / Real.log z =
        (fullLogReciprocalSum Y - fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))) / Real.log z := by ring
  rw [hrearrange, abs_div, abs_of_pos hlogzpos]
  exact div_le_div_of_nonneg_right hbase hlogzpos.le

/-- Explicit two-endpoint quadrature error, later specialized to moving
power-scale endpoints. -/
theorem fullReciprocalSum_interval_error_bound {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * C / Real.log (A : ℝ) ^ 3 := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by linarith
  have hlogYpos : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast
    (show 1 < Y by omega))
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have herrInt := intervalIntegrable_mertensErrorKernel hAR hAYR
  have hmajorInt : IntervalIntegrable (mertensErrorMajorant C) volume
      (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAYR
      (continuousOn_mertensErrorMajorant C
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have habsInt : IntervalIntegrable (fun x => |mertensErrorKernel x|)
      volume (A : ℝ) (Y : ℝ) := herrInt.abs
  have hIntBound :
      |∫ x in (A : ℝ)..Y, mertensErrorKernel x| ≤
        C / Real.log (A : ℝ) ^ 3 := by
    calc
      |∫ x in (A : ℝ)..Y, mertensErrorKernel x| ≤
          ∫ x in (A : ℝ)..Y, |mertensErrorKernel x| :=
        intervalIntegral.abs_integral_le_integral_abs hAYR
      _ ≤ ∫ x in (A : ℝ)..Y, mertensErrorMajorant C x := by
        exact intervalIntegral.integral_mono_on hAYR habsInt hmajorInt
          (fun x hx => abs_mertensErrorKernel_le C hC hAR hx (hTheta x hx))
      _ = mertensErrorPrimitive C (Y : ℝ) -
          mertensErrorPrimitive C (A : ℝ) :=
        integral_mertensErrorMajorant C hAR hAYR
      _ ≤ C / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg : 0 ≤ C / Real.log (Y : ℝ) ^ 3 := by positivity
        have heq :
            -C / Real.log (Y : ℝ) ^ 3 -
                (-C / Real.log (A : ℝ) ^ 3) =
              C / Real.log (A : ℝ) ^ 3 -
                C / Real.log (Y : ℝ) ^ 3 := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  rw [fullReciprocalSum_interval_error_identity hA hAY]
  have hThetaA := hTheta (A : ℝ) ⟨le_rfl, hAYR⟩
  have hThetaY := hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩
  have hAterm :
      |thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ))| ≤
        C / Real.log (A : ℝ) ^ 4 := by
    rw [abs_div, abs_of_pos (mul_pos hApos hlogApos)]
    calc
      _ ≤ (C * (A : ℝ) / Real.log (A : ℝ) ^ 3) /
          ((A : ℝ) * Real.log (A : ℝ)) := by gcongr
      _ = C / Real.log (A : ℝ) ^ 4 := by
        field_simp [ne_of_gt hApos, ne_of_gt hlogApos]
  have hYterm :
      |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ))| ≤
        C / Real.log (A : ℝ) ^ 4 := by
    rw [abs_div, abs_of_pos (mul_pos hYpos hlogYpos)]
    calc
      _ ≤ (C * (Y : ℝ) / Real.log (Y : ℝ) ^ 3) /
          ((Y : ℝ) * Real.log (Y : ℝ)) := by gcongr
      _ = C / Real.log (Y : ℝ) ^ 4 := by
        field_simp [ne_of_gt hYpos, ne_of_gt hlogYpos]
      _ ≤ C / Real.log (A : ℝ) ^ 4 := by gcongr
  calc
    |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
        thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)) +
        ∫ x in (A : ℝ)..Y, mertensErrorKernel x| ≤
      |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ))| +
        |thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ))| +
        |∫ x in (A : ℝ)..Y, mertensErrorKernel x| := by
          calc
            _ ≤
                |thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)) -
                  thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ))| +
                  |∫ x in (A : ℝ)..Y, mertensErrorKernel x| :=
              abs_add_le _ _
            _ ≤ _ := by
              have hsub := abs_sub
                (thetaError (Y : ℝ) / ((Y : ℝ) * Real.log (Y : ℝ)))
                (thetaError (A : ℝ) / ((A : ℝ) * Real.log (A : ℝ)))
              linarith
    _ ≤ C / Real.log (A : ℝ) ^ 4 +
        C / Real.log (A : ℝ) ^ 4 +
        C / Real.log (A : ℝ) ^ 3 := by linarith
    _ ≤ 5 * C / Real.log (A : ℝ) ^ 3 := by
      have hinv4 :
          1 / Real.log (A : ℝ) ^ 4 ≤
            2 / Real.log (A : ℝ) ^ 3 := by
        have hone : 1 ≤ 2 * Real.log (A : ℝ) := by linarith
        have hpowNonneg : 0 ≤ Real.log (A : ℝ) ^ 3 :=
          pow_nonneg hlogApos.le 3
        have hmul := mul_le_mul_of_nonneg_right hone hpowNonneg
        apply (div_le_div_iff₀ (pow_pos hlogApos 4)
          (pow_pos hlogApos 3)).2
        calc
          1 * Real.log (A : ℝ) ^ 3 ≤
              (2 * Real.log (A : ℝ)) * Real.log (A : ℝ) ^ 3 := hmul
          _ = 2 * Real.log (A : ℝ) ^ 4 := by ring
      have hscaled :
          C / Real.log (A : ℝ) ^ 4 ≤
            2 * C / Real.log (A : ℝ) ^ 3 := by
        calc
          C / Real.log (A : ℝ) ^ 4 =
              C * (1 / Real.log (A : ℝ) ^ 4) := by ring
          _ ≤ C * (2 / Real.log (A : ℝ) ^ 3) :=
            mul_le_mul_of_nonneg_left hinv4 hC
          _ = 2 * C / Real.log (A : ℝ) ^ 3 := by ring
      have hscaled' :
          C / Real.log (A : ℝ) ^ 4 ≤
            2 * (C / Real.log (A : ℝ) ^ 3) := by
        calc
          C / Real.log (A : ℝ) ^ 4 ≤
              2 * C / Real.log (A : ℝ) ^ 3 := hscaled
          _ = 2 * (C / Real.log (A : ℝ) ^ 3) := by ring
      calc
        C / Real.log (A : ℝ) ^ 4 +
              C / Real.log (A : ℝ) ^ 4 +
              C / Real.log (A : ℝ) ^ 3 ≤
            2 * (C / Real.log (A : ℝ) ^ 3) +
              2 * (C / Real.log (A : ℝ) ^ 3) +
              C / Real.log (A : ℝ) ^ 3 :=
          add_le_add (add_le_add hscaled' hscaled') le_rfl
        _ = 5 * C / Real.log (A : ℝ) ^ 3 := by ring

/-- Positive-cell harmonic mass written directly in the paper's `t`
coordinate. -/
theorem harmonicCell_coordinate_error_bound {z : ℝ} {A Y : ℕ}
    (hz : 1 < z) (hA : 2 ≤ A) (hAY : A ≤ Y)
    {C : ℝ} (hC : 0 ≤ C)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (logCoordinate z Y) -
          Real.log (logCoordinate z A))| ≤
      5 * C / Real.log (A : ℝ) ^ 3 := by
  rw [log_logCoordinate_sub hz hA hAY]
  exact fullReciprocalSum_interval_error_bound hA hAY hC hTheta

/-- The genuine PNT supplies the log-cube hypothesis in the preceding
estimate, with one constant and one threshold valid for every later
interval. -/
theorem exists_thetaError_log_cube_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℝ, ∀ x, X₀ ≤ x →
      |thetaError x| ≤ C * x / Real.log x ^ 3 := by
  obtain ⟨C, hC, hbound⟩ :=
    (theta_error_isBigO_log_power (3 : ℝ)).exists_pos
  rw [IsBigOWith, eventually_atTop] at hbound
  obtain ⟨X₀, hX₀⟩ := hbound
  refine ⟨C, hC, max X₀ 2, fun x hx => ?_⟩
  have hxX₀ : X₀ ≤ x := (le_max_left X₀ 2).trans hx
  have hx2 : (2 : ℝ) ≤ x := (le_max_right X₀ 2).trans hx
  have htargetR : 0 ≤ x / Real.log x ^ ((3 : ℕ) : ℝ) := by
    have hxpos : 0 < x := by linarith
    have hlogpos : 0 < Real.log x := Real.log_pos (by linarith)
    positivity
  have hb := hX₀ x hxX₀
  simp only [Pi.sub_apply, id_eq, Real.norm_eq_abs] at hb
  calc
    |thetaError x| = |Chebyshev.theta x - x| := rfl
    _ ≤ C * |x / Real.log x ^ ((3 : ℕ) : ℝ)| := by
      exact hb
    _ = C * (x / Real.log x ^ ((3 : ℕ) : ℝ)) := by
      congr 1
      exact abs_of_nonneg htargetR
    _ = C * x / Real.log x ^ 3 := by
      rw [Real.rpow_natCast]
      ring

/-- Unconditional positive-cell harmonic-prime quadrature.  Unlike a bare
Mertens asymptotic, the same `C` and `X₀` work simultaneously for every
pair of moving endpoints beyond the threshold. -/
theorem exists_fullReciprocalSum_interval_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ,
      X₀ ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀
  refine ⟨C, hC, max N 2, fun A Y hA hAY => ?_⟩
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  apply fullReciprocalSum_interval_error_bound hA2 hAY hC.le
  intro x hx
  apply hTheta x
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  linarith [hx.1]

/-- Named global witnesses for reciprocal-prime mass quadrature. -/
noncomputable def fullReciprocalSumUniformConstant : ℝ :=
  Classical.choose exists_fullReciprocalSum_interval_error_bound

theorem fullReciprocalSumUniformConstant_pos :
    0 < fullReciprocalSumUniformConstant :=
  (Classical.choose_spec
    exists_fullReciprocalSum_interval_error_bound).1

noncomputable def fullReciprocalSumUniformCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      exists_fullReciprocalSum_interval_error_bound).2

theorem fullReciprocalSumUniform_bound
    (A Y : ℕ) (hA : fullReciprocalSumUniformCutoff ≤ A)
    (hAY : A ≤ Y) :
    |fullReciprocalSum Y - fullReciprocalSum A -
        (Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)))| ≤
      5 * fullReciprocalSumUniformConstant / Real.log (A : ℝ) ^ 3 :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_fullReciprocalSum_interval_error_bound).2) A Y hA hAY

/-- Unconditional positive-cell quadrature for the first logarithmic
moment, with the same uniformity in both moving endpoints. -/
theorem exists_fullLogReciprocalSum_interval_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ, ∀ A Y : ℕ,
      X₀ ≤ A → A ≤ Y →
      |fullLogReciprocalSum Y - fullLogReciprocalSum A -
          (Real.log (Y : ℝ) - Real.log (A : ℝ))| ≤
        C * (2 + (Real.log (Y : ℝ) - Real.log (A : ℝ))) /
          Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀
  refine ⟨C, hC, max N 2, fun A Y hA hAY => ?_⟩
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  apply fullLogReciprocalSum_interval_error_bound hA2 hAY hC.le
  intro x hx
  apply hTheta x
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  linarith [hx.1]

end Erdos390.Full.PrimeBandQuadrature
