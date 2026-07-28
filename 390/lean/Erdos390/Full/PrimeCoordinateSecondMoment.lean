import Erdos390.Full.KernelPrimeQuadrature

/-!
# Prime quadrature for the second logarithmic coordinate moment

The compensated-score geometry uses
`sum (log p / log z)^2 / p`.  This file derives its interval quadrature
directly from the genuine Chebyshev error, with a remainder uniform in the
moving upper endpoint.  It is the missing second-moment companion to the
mass and first-moment estimates in `PrimeBandQuadrature`.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Erdos390.Full.PrimeCoordinateSecondMoment

open PrimeSums PrimeBandQuadrature KernelPrimeQuadrature

noncomputable section

def squareCoordinate (t : ℝ) : ℝ := t ^ 2

def squareCoordinateDerivative (t : ℝ) : ℝ := 2 * t

lemma continuous_squareCoordinate : Continuous squareCoordinate := by
  unfold squareCoordinate
  fun_prop

lemma continuous_squareCoordinateDerivative :
    Continuous squareCoordinateDerivative := by
  unfold squareCoordinateDerivative
  fun_prop

lemma hasDerivAt_squareCoordinate (t : ℝ) :
    HasDerivAt squareCoordinate (squareCoordinateDerivative t) t := by
  simpa [squareCoordinate, squareCoordinateDerivative] using
    (hasDerivAt_id t).pow 2

lemma hasDerivAt_squareWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    HasDerivAt (weightedAbelCoefficient squareCoordinate z)
      (weightedAbelCoefficientDerivative squareCoordinate
        squareCoordinateDerivative z x) x := by
  exact hasDerivAt_weightedAbelCoefficient squareCoordinate
    squareCoordinateDerivative hz hx
      (hasDerivAt_squareCoordinate (realLogCoordinate z x))

lemma deriv_squareWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    deriv (weightedAbelCoefficient squareCoordinate z) x =
      weightedAbelCoefficientDerivative squareCoordinate
        squareCoordinateDerivative z x :=
  (hasDerivAt_squareWeightedAbelCoefficient hz hx).deriv

lemma continuousOn_squareWeightedAbelDerivative
    {z A Y : ℝ} (hz : 1 < z) (hA : 1 < A) :
    ContinuousOn
      (weightedAbelCoefficientDerivative squareCoordinate
        squareCoordinateDerivative z) (Icc A Y) := by
  intro x hx
  exact (continuousAt_weightedAbelCoefficientDerivative
    squareCoordinate squareCoordinateDerivative
    continuous_squareCoordinate continuous_squareCoordinateDerivative
    hz (hA.trans_le hx.1)).continuousWithinAt

lemma integrableOn_deriv_squareWeightedAbelCoefficient
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hY : 2 ≤ Y) :
    IntegrableOn (deriv (weightedAbelCoefficient squareCoordinate z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hcont := continuousOn_squareWeightedAbelDerivative
    (z := z) (A := (2 : ℝ)) (Y := (Y : ℝ)) hz (by norm_num)
  apply hcont.integrableOn_Icc.congr_fun
  · intro x hx
    symm
    exact deriv_squareWeightedAbelCoefficient hz (by linarith [hx.1])
  · exact measurableSet_Icc

lemma intervalIntegrable_deriv_squareWeighted_mul_theta
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hY : 2 ≤ Y) :
    IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x *
          Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := weightedAbelCoefficientDerivative squareCoordinate
      squareCoordinateDerivative z)
    (A := (2 : ℝ)) (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_squareWeightedAbelDerivative hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change weightedAbelCoefficientDerivative squareCoordinate
      squareCoordinateDerivative z x * Chebyshev.theta x =
    deriv (weightedAbelCoefficient squareCoordinate z) x *
      Chebyshev.theta x
  rw [deriv_squareWeightedAbelCoefficient hz (by linarith [hx'.1])]

lemma intervalIntegrable_deriv_squareWeighted_mul_id
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ ↦
        weightedAbelCoefficientDerivative squareCoordinate
          squareCoordinateDerivative z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_squareWeightedAbelDerivative hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase := hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change weightedAbelCoefficientDerivative squareCoordinate
      squareCoordinateDerivative z x * x =
    deriv (weightedAbelCoefficient squareCoordinate z) x * x
  rw [deriv_squareWeightedAbelCoefficient hz (by linarith [hAR, hx'.1])]

lemma intervalIntegrable_deriv_squareWeighted_mul_thetaError
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hthetaFull := intervalIntegrable_deriv_squareWeighted_mul_theta hz
    (hA.trans hAY)
  have htheta : IntervalIntegrable
      (fun x : ℝ ↦
        deriv (weightedAbelCoefficient squareCoordinate z) x *
          Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
    apply hthetaFull.mono_set
    rw [uIcc_of_le hAYR]
    have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
    rw [uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hmain := intervalIntegrable_deriv_squareWeighted_mul_id hz hA hAY
  have hsub := htheta.sub hmain
  apply hsub.congr
  intro x hx
  unfold thetaError
  ring

/-- Exact actual-prime second-moment quadrature with the literal PNT
remainder still displayed. -/
theorem squarePrimeCell_sub_continuum_eq_remainder
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullWeightedReciprocalSum squareCoordinate z Y -
        fullWeightedReciprocalSum squareCoordinate z A -
        (∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), squareCoordinate t / t) =
      weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ) := by
  have hY := hA.trans hAY
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient squareCoordinate z) x := by
    intro x hx
    exact (hasDerivAt_squareWeightedAbelCoefficient hz
      (by linarith [hx.1])).differentiableAt
  have hint := integrableOn_deriv_squareWeightedAbelCoefficient hz hY
  have hdecomp := fullWeightedReciprocalSum_interval_sub_main_eq_remainder
    squareCoordinate z hA hAY hdiff hint
    (intervalIntegrable_deriv_squareWeighted_mul_theta hz hY)
    (intervalIntegrable_deriv_squareWeighted_mul_id hz hA hAY)
    (intervalIntegrable_deriv_squareWeighted_mul_thetaError hz hA hAY)
  rw [weightedAbelMain_eq_logCoordinateIntegral squareCoordinate
    continuous_squareCoordinate hz hA hAY hdiff hint] at hdecomp
  exact hdecomp

lemma squareCoordinate_integral_formula
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ t in realLogCoordinate z (A : ℝ)..
      realLogCoordinate z (Y : ℝ), squareCoordinate t / t) =
      (realLogCoordinate z (Y : ℝ) ^ 2 -
        realLogCoordinate z (A : ℝ) ^ 2) / 2 := by
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogA : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have ha : 0 < realLogCoordinate z (A : ℝ) := by
    unfold realLogCoordinate
    exact div_pos hlogA hlogz
  have hApos : (0 : ℝ) < (A : ℝ) := by positivity
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos (by exact_mod_cast hAY)
  have hab : realLogCoordinate z (A : ℝ) ≤
      realLogCoordinate z (Y : ℝ) := by
    unfold realLogCoordinate
    exact div_le_div_of_nonneg_right hlogAY hlogz.le
  calc
    (∫ t in realLogCoordinate z (A : ℝ)..
        realLogCoordinate z (Y : ℝ), squareCoordinate t / t) =
        ∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Icc (realLogCoordinate z (A : ℝ))
          (realLogCoordinate z (Y : ℝ)) := by
        simpa only [uIcc_of_le hab] using ht
      have ht0 : t ≠ 0 := ne_of_gt (ha.trans_le htIcc.1)
      unfold squareCoordinate
      field_simp
    _ = _ := integral_id

/-- Closed-form exact decomposition for the actual second-coordinate prime
sum on `(A,Y]`. -/
theorem squarePrimeCell_sub_formula_eq_remainder
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) :
    fullWeightedReciprocalSum squareCoordinate z Y -
        fullWeightedReciprocalSum squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2) =
      weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ) := by
  rw [← squareCoordinate_integral_formula hz hA hAY]
  exact squarePrimeCell_sub_continuum_eq_remainder hz hA hAY

lemma squareWeightedAbelCoefficient_eq
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    weightedAbelCoefficient squareCoordinate z x =
      Real.log x / (x * Real.log z ^ 2) := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold weightedAbelCoefficient squareCoordinate realLogCoordinate
  field_simp

lemma squareWeightedAbelDerivative_eq
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    deriv (weightedAbelCoefficient squareCoordinate z) x =
      (1 - Real.log x) / (x ^ 2 * Real.log z ^ 2) := by
  rw [deriv_squareWeightedAbelCoefficient hz hx]
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold weightedAbelCoefficientDerivative squareCoordinate
    squareCoordinateDerivative realLogCoordinate
  field_simp
  ring

/-- Integrable majorant for the square-coordinate PNT remainder. -/
def squareMomentTailMajorant (C z x : ℝ) : ℝ :=
  C / Real.log z ^ 2 / (x * Real.log x ^ 2)

def squareMomentTailPrimitive (C z x : ℝ) : ℝ :=
  -(C / Real.log z ^ 2) / Real.log x

lemma hasDerivAt_squareMomentTailPrimitive
    (C z : ℝ) {x : ℝ} (hx : 1 < x) :
    HasDerivAt (squareMomentTailPrimitive C z)
      (squareMomentTailMajorant C z x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hinv := (Real.hasDerivAt_log hx0).inv hlogx
  have hmul := (hasDerivAt_const x (-(C / Real.log z ^ 2))).mul hinv
  convert hmul using 1
  · unfold squareMomentTailMajorant
    field_simp [hx0, hlogx]
    ring

lemma continuousOn_squareMomentTailMajorant
    (C z : ℝ) {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn (squareMomentTailMajorant C z) (Icc A Y) := by
  intro x hx
  have hx1 : 1 < x := hA.trans_le hx.1
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx1)
  have hlogx : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx1)
  unfold squareMomentTailMajorant
  exact (continuousAt_const.div_const (Real.log z ^ 2)).div
    (continuousAt_id.mul ((Real.continuousAt_log hx0).pow 2))
    (mul_ne_zero hx0 (pow_ne_zero 2 hlogx)) |>.continuousWithinAt

lemma integral_squareMomentTailMajorant
    (C z : ℝ) {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in A..Y, squareMomentTailMajorant C z x) =
      squareMomentTailPrimitive C z Y -
        squareMomentTailPrimitive C z A := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    rw [uIcc_of_le hAY] at hx
    exact hasDerivAt_squareMomentTailPrimitive C z
      (by linarith [hA, hx.1])
  · exact ContinuousOn.intervalIntegrable_of_Icc (μ := volume) hAY
      (continuousOn_squareMomentTailMajorant C z (by linarith [hA]))

lemma one_le_log_of_eight_le {x : ℝ} (hx : 8 ≤ x) :
    1 ≤ Real.log x := by
  have h8pos : (0 : ℝ) < 8 := by norm_num
  have hlog := Real.log_le_log h8pos hx
  have hlog8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    ring
  rw [hlog8] at hlog
  nlinarith [Real.log_two_gt_d9]

lemma abs_squareWeightedCoefficient_mul_thetaError_le
    {C z x : ℝ} (hz : 1 < z) (hx : 8 ≤ x)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelCoefficient squareCoordinate z x * thetaError x| ≤
      C / (Real.log z ^ 2 * Real.log x ^ 2) := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogz : 0 < Real.log z := Real.log_pos hz
  rw [squareWeightedAbelCoefficient_eq hz hx1, abs_mul, abs_div,
    abs_of_pos hlogx, abs_of_pos
      (mul_pos hx0 (sq_pos_of_pos hlogz))]
  calc
    Real.log x / (x * Real.log z ^ 2) * |thetaError x| ≤
        (Real.log x / (x * Real.log z ^ 2)) *
          (C * x / Real.log x ^ 3) := by
      exact mul_le_mul_of_nonneg_left hTheta (by positivity)
    _ = C / (Real.log z ^ 2 * Real.log x ^ 2) := by
      field_simp [ne_of_gt hx0, ne_of_gt hlogx, ne_of_gt hlogz]

lemma abs_squareWeightedDerivative_mul_thetaError_le
    {C z x : ℝ} (hz : 1 < z) (hx : 8 ≤ x)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |deriv (weightedAbelCoefficient squareCoordinate z) x * thetaError x| ≤
      squareMomentTailMajorant C z x := by
  have hx1 : 1 < x := by linarith
  have hx0 : 0 < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogOne : 1 ≤ Real.log x := one_le_log_of_eight_le hx
  have habs : |1 - Real.log x| ≤ Real.log x := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  rw [squareWeightedAbelDerivative_eq hz hx1, abs_mul, abs_div,
    abs_of_pos (mul_pos (sq_pos_of_pos hx0) (sq_pos_of_pos hlogz))]
  calc
    |1 - Real.log x| / (x ^ 2 * Real.log z ^ 2) * |thetaError x| ≤
        (Real.log x / (x ^ 2 * Real.log z ^ 2)) *
          (C * x / Real.log x ^ 3) := by
      exact mul_le_mul
        (div_le_div_of_nonneg_right habs (by positivity)) hTheta
        (abs_nonneg _) (by positivity)
    _ = squareMomentTailMajorant C z x := by
      unfold squareMomentTailMajorant
      field_simp [ne_of_gt hx0, ne_of_gt hlogx, ne_of_gt hlogz]

/-- Uniform quantitative PNT bound for the square-coordinate remainder.
The lower endpoint alone controls the error; the upper endpoint may move all
the way to the ambient scale. -/
theorem abs_squareWeightedAbelRemainder_le
    {C z : ℝ} (hC : 0 ≤ C) (hz : 1 < z)
    {A Y : ℕ} (hA : 8 ≤ A) (hAY : A ≤ Y)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ)| ≤
      3 * C / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
  have hAR : (8 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := hApos.trans_le hAYR
  have hlogA : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogY : 0 < Real.log (Y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
  have hlogz : 0 < Real.log z := Real.log_pos hz
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have hlogAOne : 1 ≤ Real.log (A : ℝ) :=
    one_le_log_of_eight_le hAR
  let K : ℝ := C / Real.log z ^ 2
  have hK0 : 0 ≤ K := by dsimp only [K]; positivity
  have hmajorInt : IntervalIntegrable (squareMomentTailMajorant C z)
      volume (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_squareMomentTailMajorant C z (by linarith [hAR]))
  have herrorInt :=
    intervalIntegrable_deriv_squareWeighted_mul_thetaError hz
      (show 2 ≤ A by omega) hAY
  have hIntBound :
      (∫ x in (A : ℝ)..Y,
        |deriv (weightedAbelCoefficient squareCoordinate z) x *
          thetaError x|) ≤ K / Real.log (A : ℝ) := by
    calc
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient squareCoordinate z) x *
            thetaError x|) ≤
          ∫ x in (A : ℝ)..Y, squareMomentTailMajorant C z x := by
        exact intervalIntegral.integral_mono_on hAYR herrorInt.abs hmajorInt
          (fun x hx ↦ abs_squareWeightedDerivative_mul_thetaError_le
            hz (hAR.trans hx.1) (hTheta x hx))
      _ = squareMomentTailPrimitive C z (Y : ℝ) -
          squareMomentTailPrimitive C z (A : ℝ) :=
        integral_squareMomentTailMajorant C z (by linarith [hAR]) hAYR
      _ ≤ K / Real.log (A : ℝ) := by
        have hnonneg : 0 ≤ K /
            Real.log (Y : ℝ) := by positivity
        have heq :
            squareMomentTailPrimitive C z (Y : ℝ) -
                squareMomentTailPrimitive C z (A : ℝ) =
              K / Real.log (A : ℝ) - K / Real.log (Y : ℝ) := by
          dsimp only [squareMomentTailPrimitive, K]
          ring
        rw [heq]
        exact sub_le_self _ hnonneg
  have hAterm :
      |weightedAbelCoefficient squareCoordinate z (A : ℝ) *
        thetaError (A : ℝ)| ≤
        K / Real.log (A : ℝ) ^ 2 := by
    simpa only [K, div_div] using
      abs_squareWeightedCoefficient_mul_thetaError_le hz hAR
        (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩)
  have hYterm :
      |weightedAbelCoefficient squareCoordinate z (Y : ℝ) *
        thetaError (Y : ℝ)| ≤
        K / Real.log (A : ℝ) ^ 2 := by
    have hyRaw := abs_squareWeightedCoefficient_mul_thetaError_le hz
      (hAR.trans hAYR) (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩)
    calc
      _ ≤ C / (Real.log z ^ 2 * Real.log (Y : ℝ) ^ 2) := hyRaw
      _ ≤ C / (Real.log z ^ 2 * Real.log (A : ℝ) ^ 2) := by
        gcongr
      _ = K / Real.log (A : ℝ) ^ 2 := by
        dsimp only [K]
        ring
  have hinvSq : K / Real.log (A : ℝ) ^ 2 ≤
      K / Real.log (A : ℝ) := by
    have hsq : Real.log (A : ℝ) ≤ Real.log (A : ℝ) ^ 2 := by
      nlinarith
    exact div_le_div_of_nonneg_left hK0 hlogA hsq
  calc
    |weightedAbelRemainder squareCoordinate z (A : ℝ) (Y : ℝ)| ≤
        |weightedAbelCoefficient squareCoordinate z (Y : ℝ)| *
            |thetaError (Y : ℝ)| +
          |weightedAbelCoefficient squareCoordinate z (A : ℝ)| *
            |thetaError (A : ℝ)| +
          ∫ x in (A : ℝ)..Y,
            |deriv (weightedAbelCoefficient squareCoordinate z) x *
              thetaError x| :=
      abs_weightedAbelRemainder_le squareCoordinate z hAYR
    _ ≤ K / Real.log (A : ℝ) ^ 2 +
        K / Real.log (A : ℝ) ^ 2 +
          K / Real.log (A : ℝ) := by
      exact add_le_add (add_le_add (by simpa [abs_mul] using hYterm)
        (by simpa [abs_mul] using hAterm)) hIntBound
    _ ≤ 3 * (K / Real.log (A : ℝ)) := by linarith
    _ = 3 * C / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
      dsimp only [K]
      ring

/-- The genuine PNT supplies one constant and one lower threshold before
the ambient scale and both moving endpoints are chosen. -/
theorem exists_uniform_squarePrimeCell_error_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
        X₀ ≤ A → A ≤ Y →
        |fullWeightedReciprocalSum squareCoordinate z Y -
            fullWeightedReciprocalSum squareCoordinate z A -
            ((realLogCoordinate z (Y : ℝ) ^ 2 -
              realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
          3 * C / (Real.log z ^ 2 * Real.log (A : ℝ)) := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨C, hC, max N 8, ?_⟩
  intro z hz A Y hA hAY
  have hA8 : 8 ≤ A := (le_max_right N 8).trans hA
  have hNA : N ≤ A := (le_max_left N 8).trans hA
  rw [squarePrimeCell_sub_formula_eq_remainder hz (show 2 ≤ A by omega) hAY]
  apply abs_squareWeightedAbelRemainder_le hC.le hz hA8 hAY
  intro x hx
  apply hTheta x
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  exact (le_of_lt hX₀N).trans (hNAR.trans hx.1)

/-- Named global witnesses for the square-coordinate prime quadrature. -/
noncomputable def squarePrimeCellUniformConstant : ℝ :=
  Classical.choose exists_uniform_squarePrimeCell_error_bound

noncomputable def squarePrimeCellUniformCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      exists_uniform_squarePrimeCell_error_bound).2

theorem squarePrimeCellUniform_bound
    (z : ℝ) (hz : 1 < z) (A Y : ℕ)
    (hA : squarePrimeCellUniformCutoff ≤ A) (hAY : A ≤ Y) :
    |fullWeightedReciprocalSum squareCoordinate z Y -
        fullWeightedReciprocalSum squareCoordinate z A -
        ((realLogCoordinate z (Y : ℝ) ^ 2 -
          realLogCoordinate z (A : ℝ) ^ 2) / 2)| ≤
      3 * squarePrimeCellUniformConstant /
        (Real.log z ^ 2 * Real.log (A : ℝ)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      exists_uniform_squarePrimeCell_error_bound).2) z hz A Y hA hAY

end

end Erdos390.Full.PrimeCoordinateSecondMoment
