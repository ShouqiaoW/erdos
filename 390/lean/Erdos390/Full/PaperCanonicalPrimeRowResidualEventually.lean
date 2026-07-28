import Erdos390.Full.PrimeSquarefreeDirichletGeometry
import Erdos390.Full.KernelPrimeQuadrature
import Erdos390.Full.DoubleKernelPrimeQuadrature
import Erdos390.Full.RegularMeshActualMomentBoundsEventually

/-!
# Relative prime-row residual for the squarefree Dickman reference

The prime-level anchored Dirichlet proof needs a *relative* row estimate.
An additive estimate for the Dickman kernel is not enough when the marked
prime coordinate tends to zero.  We therefore apply weighted Abel summation
to

`phi_s(t) = t * K(s,t)`.

Both `phi_s` and its derivative in `t` are `O(s)` uniformly on the unit
square.  Consequently the PNT remainder is `O(s / log(W)^3)`.  Kernel
symmetry and the removable quotient row-sum identity then turn this into the
literal bound

`|R_p| <= (D / log(W)^3 + two endpoint tails) * t_p`.

All constants below are chosen before `W`, the ambient integer, and the
marked prime.
-/

open scoped BigOperators
open Set Filter Topology

noncomputable section

namespace Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

open ArithmeticModel PrimeSums PrimeBandQuadrature
open KernelPrimeQuadrature ConditionedPoissonLimit DickmanBasic
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open MeasureTheory
open DoubleKernelPrimeQuadrature

/-- The test function whose prime sum occurs after conjugating the reference
row by `t_p / p`. -/
def firstMomentKernel (s t : ℝ) : ℝ :=
  t * covarianceKernel s t

/-- Continuous extension of the derivative of `firstMomentKernel s` in its
second coordinate. -/
def firstMomentKernelDerivative (s t : ℝ) : ℝ :=
  covarianceKernel s t +
    t * covarianceKernelDerivativeSecondExtension s t

lemma continuous_firstMomentKernel (s : ℝ) :
    Continuous (firstMomentKernel s) := by
  exact continuous_id.mul (continuous_covarianceKernel_left s)

lemma continuous_firstMomentKernelDerivative (s : ℝ) :
    Continuous (firstMomentKernelDerivative s) := by
  exact (continuous_covarianceKernel_left s).add
    (continuous_id.mul
      (continuous_covarianceKernelDerivativeSecondExtension_left s))

lemma hasDerivAt_firstMomentKernel_second {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (firstMomentKernel s)
      (firstMomentKernelDerivative s t) t := by
  have hK := hasDerivAt_covarianceKernel_second hs ht
  have hExt := covarianceKernelDerivativeSecondExtension_eq hs ht
  simpa only [firstMomentKernel, firstMomentKernelDerivative, id_eq,
    one_mul, hExt] using (hasDerivAt_id t).mul hK

/-- Explicit Abel coefficient for `firstMomentKernel`. -/
def firstMomentAbelCoefficient (s z x : ℝ) : ℝ :=
  weightedAbelCoefficient (firstMomentKernel s) z x

/-- Explicit derivative of the preceding Abel coefficient. -/
def firstMomentAbelDerivative (s z x : ℝ) : ℝ :=
  weightedAbelCoefficientDerivative (firstMomentKernel s)
    (firstMomentKernelDerivative s) z x

lemma hasDerivAt_firstMomentAbelCoefficient
    {s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    HasDerivAt (firstMomentAbelCoefficient s z)
      (firstMomentAbelDerivative s z x) x := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  exact hasDerivAt_weightedAbelCoefficient
    (firstMomentKernel s) (firstMomentKernelDerivative s) hz hx
      (hasDerivAt_firstMomentKernel_second hs ht)

lemma deriv_firstMomentAbelCoefficient
    {s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    deriv (firstMomentAbelCoefficient s z) x =
      firstMomentAbelDerivative s z x := by
  exact (hasDerivAt_firstMomentAbelCoefficient hs hz hx hxz).deriv

lemma continuousOn_firstMomentAbelDerivative
    (s z : ℝ) (hz : 1 < z) {A Y : ℝ} (hA : 1 < A) :
    ContinuousOn (firstMomentAbelDerivative s z) (Icc A Y) := by
  intro x hx
  exact continuousAt_weightedAbelCoefficientDerivative
    (firstMomentKernel s) (firstMomentKernelDerivative s)
    (continuous_firstMomentKernel s)
    (continuous_firstMomentKernelDerivative s) hz
      (hA.trans_le hx.1) |>.continuousWithinAt

lemma integrableOn_deriv_firstMomentAbelCoefficient
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hYz : (Y : ℝ) ≤ z) :
    IntegrableOn (deriv (firstMomentAbelCoefficient s z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have hcont : ContinuousOn (firstMomentAbelDerivative s z)
      (Icc (2 : ℝ) (Y : ℝ)) :=
    continuousOn_firstMomentAbelDerivative s z hz (by norm_num)
  apply (hcont.integrableOn_Icc).congr_fun
  · intro x hx
    symm
    exact deriv_firstMomentAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)
  · exact measurableSet_Icc

lemma intervalIntegrable_deriv_firstMoment_mul_theta
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := firstMomentAbelDerivative s z) (A := (2 : ℝ))
    (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_firstMomentAbelDerivative s z hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change firstMomentAbelDerivative s z x * Chebyshev.theta x =
    deriv (firstMomentAbelCoefficient s z) x * Chebyshev.theta x
  congr 1
  exact (deriv_firstMomentAbelCoefficient hs hz
    (by linarith [hx'.1]) (hx'.2.trans hYz)).symm

lemma intervalIntegrable_deriv_firstMoment_mul_id
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ => firstMomentAbelDerivative s z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_firstMomentAbelDerivative s z hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase := hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change firstMomentAbelDerivative s z x * x =
    deriv (firstMomentAbelCoefficient s z) x * x
  congr 1
  exact (deriv_firstMomentAbelCoefficient hs hz
    (by linarith [hAR, hx'.1]) (hx'.2.trans hYz)).symm

/-- Exact prime-cell identity before estimating the PNT remainder. -/
theorem firstMomentKernel_primeCell_sub_continuum_eq_remainder
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    fullWeightedReciprocalSum (firstMomentKernel s) z Y -
        fullWeightedReciprocalSum (firstMomentKernel s) z A -
        (∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), firstMomentKernel s t / t) =
      weightedAbelRemainder (firstMomentKernel s) z (A : ℝ) (Y : ℝ) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ
        (weightedAbelCoefficient (firstMomentKernel s) z) x := by
    intro x hx
    change DifferentiableAt ℝ (firstMomentAbelCoefficient s z) x
    exact (hasDerivAt_firstMomentAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)).differentiableAt
  have hint : IntegrableOn
      (deriv (weightedAbelCoefficient (firstMomentKernel s) z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
    simpa only [firstMomentAbelCoefficient] using
      integrableOn_deriv_firstMomentAbelCoefficient hs hz hYz
  have hThetaInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
          Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
    simpa only [firstMomentAbelCoefficient] using
      intervalIntegrable_deriv_firstMoment_mul_theta hs hz hY hYz
  have hMainInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
    simpa only [firstMomentAbelCoefficient] using
      intervalIntegrable_deriv_firstMoment_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (firstMomentKernel s) z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hThetaCell : IntervalIntegrable
        (fun x : ℝ =>
          deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
      apply hThetaInt.mono_set
      rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
      intro x hx
      exact ⟨hAR.trans hx.1, hx.2⟩
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hdecomp :=
    fullWeightedReciprocalSum_interval_sub_main_eq_remainder
      (firstMomentKernel s) z hA hAY hdiff hint hThetaInt hMainInt hErrorInt
  rw [weightedAbelMain_eq_logCoordinateIntegral
    (firstMomentKernel s) (continuous_firstMomentKernel s)
    hz hA hAY hdiff hint] at hdecomp
  exact hdecomp

lemma abs_firstMomentAbelCoefficient_le
    {M s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u) :
    |firstMomentAbelCoefficient s z x| ≤
      (M * s) / (x * Real.log x) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hdenpos : 0 < x * Real.log x := mul_pos hxpos hlogxpos
  unfold firstMomentAbelCoefficient weightedAbelCoefficient
  rw [abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hPhi s hs _ ht) hdenpos.le

lemma abs_firstMomentAbelDerivative_le
    {M s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u) :
    |firstMomentAbelDerivative s z x| ≤
      (M * s) / (x ^ 2 * Real.log x * Real.log z) +
        (M * s) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
  have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
  have hplus : 0 ≤ Real.log x + 1 := by linarith
  unfold firstMomentAbelDerivative weightedAbelCoefficientDerivative
  calc
    |firstMomentKernelDerivative s (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z) -
        firstMomentKernel s (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| ≤
      |firstMomentKernelDerivative s (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z)| +
        |firstMomentKernel s (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| := abs_sub _ _
    _ = |firstMomentKernelDerivative s (realLogCoordinate z x)| /
          (x ^ 2 * Real.log x * Real.log z) +
        |firstMomentKernel s (realLogCoordinate z x)| * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
      rw [abs_div, abs_div]
      simp only [abs_mul]
      rw [abs_of_nonneg (sq_nonneg x), abs_of_pos hlogxpos,
        abs_of_pos hlogzpos, abs_of_nonneg hplus,
        abs_of_nonneg (sq_nonneg (Real.log x))]
    _ ≤ (M * s) / (x ^ 2 * Real.log x * Real.log z) +
        (M * s) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
      exact add_le_add
        (div_le_div_of_nonneg_right (hPhiPrime s hs _ ht) hden₁.le)
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hPhi s hs _ ht) hplus) hden₂.le)

lemma abs_firstMomentAbelCoefficient_mul_thetaError_le
    {C M s z x : ℝ} (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |firstMomentAbelCoefficient s z x * thetaError x| ≤
      C * (M * s) / Real.log x ^ 4 := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hcoeff := abs_firstMomentAbelCoefficient_le hs hz hx1 hxz hPhi
  rw [abs_mul]
  calc
    |firstMomentAbelCoefficient s z x| * |thetaError x| ≤
        ((M * s) / (x * Real.log x)) *
          (C * x / Real.log x ^ 3) := by
      apply mul_le_mul hcoeff hTheta (abs_nonneg _)
      exact div_nonneg (mul_nonneg hM hs.1) (by positivity)
    _ = C * (M * s) / Real.log x ^ 4 := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]

lemma abs_firstMomentAbelDerivative_mul_thetaError_le
    {C M s z x : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |firstMomentAbelDerivative s z x * thetaError x| ≤
      mertensErrorMajorant (2 * C * (M * s)) x := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log x := by linarith
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.log_le_log hxpos hxz
  have hplus : Real.log x + 1 ≤ 3 * Real.log x := by linarith
  have hderiv := abs_firstMomentAbelDerivative_le hs hz hx1 hxz
    hPhi hPhiPrime
  have hsimplified :
      (M * s) / (x ^ 2 * Real.log x * Real.log z) +
          (M * s) * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2) ≤
        5 * (M * s) / (x ^ 2 * Real.log x) := by
    have hMs : 0 ≤ M * s := mul_nonneg hM hs.1
    have hdenx : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
    have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
    have hden₃ : 0 < x ^ 2 * Real.log x := by positivity
    have hfirst :
        (M * s) / (x ^ 2 * Real.log x * Real.log z) ≤
          (M * s) / (x ^ 2 * Real.log x ^ 2) := by
      apply (div_le_div_iff₀ hden₁ hden₂).2
      apply mul_le_mul_of_nonneg_left _ hMs
      nlinarith [mul_pos hdenx hlogpos]
    have hsecond :
        (M * s) * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
          3 * (M * s) / (x ^ 2 * Real.log x) := by
      calc
        _ ≤ (M * s) * (3 * Real.log x) /
              (x ^ 2 * Real.log x ^ 2) := by gcongr
        _ = 3 * (M * s) / (x ^ 2 * Real.log x) := by
          field_simp [ne_of_gt hlogpos]
    have hfirst' :
        (M * s) / (x ^ 2 * Real.log x ^ 2) ≤
          2 * (M * s) / (x ^ 2 * Real.log x) := by
      have hone : 1 ≤ 2 * Real.log x := by linarith
      apply (div_le_div_iff₀ hden₂ hden₃).2
      nlinarith [mul_nonneg hMs hden₃.le]
    calc
      (M * s) / (x ^ 2 * Real.log x * Real.log z) +
          (M * s) * (Real.log x + 1) /
            (x ^ 2 * Real.log x ^ 2) ≤
          (M * s) / (x ^ 2 * Real.log x ^ 2) +
            3 * (M * s) / (x ^ 2 * Real.log x) :=
        add_le_add hfirst hsecond
      _ ≤ 2 * (M * s) / (x ^ 2 * Real.log x) +
            3 * (M * s) / (x ^ 2 * Real.log x) :=
        add_le_add hfirst' le_rfl
      _ = 5 * (M * s) / (x ^ 2 * Real.log x) := by ring
  rw [abs_mul]
  calc
    |firstMomentAbelDerivative s z x| * |thetaError x| ≤
        (5 * (M * s) / (x ^ 2 * Real.log x)) *
          (C * x / Real.log x ^ 3) := by
      exact mul_le_mul (hderiv.trans hsimplified) hTheta (abs_nonneg _)
        (div_nonneg (mul_nonneg (by norm_num)
          (mul_nonneg hM hs.1)) (by positivity))
    _ ≤ mertensErrorMajorant (2 * C * (M * s)) x := by
      unfold mertensErrorMajorant
      have hCMs : 0 ≤ C * (M * s) :=
        mul_nonneg hC (mul_nonneg hM hs.1)
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]
      nlinarith

/-- Uniform Abel remainder for the first-moment kernel.  The factor `s` is
kept literal; it is never absorbed into a global compactness constant. -/
theorem abs_firstMomentWeightedAbelRemainder_le
    {C M s z : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u)
    (hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelRemainder (firstMomentKernel s) z (A : ℝ) (Y : ℝ)| ≤
      6 * (C * M) * s / Real.log (A : ℝ) ^ 3 := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by linarith
  have hCMs : 0 ≤ C * (M * s) :=
    mul_nonneg hC (mul_nonneg hM hs.1)
  have hThetaCell : IntervalIntegrable
      (fun x : ℝ =>
        deriv (firstMomentAbelCoefficient s z) x * Chebyshev.theta x)
      volume (A : ℝ) (Y : ℝ) := by
    have hfull := intervalIntegrable_deriv_firstMoment_mul_theta
      hs hz hY hYz
    apply hfull.mono_set
    rw [uIcc_of_le hAYR]
    have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    rw [uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hMainInt : IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) :=
    intervalIntegrable_deriv_firstMoment_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (firstMomentAbelCoefficient s z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hmajorInt : IntervalIntegrable
      (mertensErrorMajorant (2 * C * (M * s))) volume
      (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_mertensErrorMajorant (2 * C * (M * s))
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have hIntBound :
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x|) ≤
        2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
    have habsInt : IntervalIntegrable
        (fun x : ℝ =>
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x|) volume (A : ℝ) (Y : ℝ) := by
      simpa only [firstMomentAbelCoefficient] using hErrorInt.abs
    calc
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x|) ≤
          ∫ x in (A : ℝ)..Y,
            mertensErrorMajorant (2 * C * (M * s)) x := by
        exact intervalIntegral.integral_mono_on hAYR habsInt hmajorInt
          (fun x hx => by
            have hx2 : 2 ≤ x := hAR.trans hx.1
            have hxz : x ≤ z := hx.2.trans hYz
            rw [show deriv
                (weightedAbelCoefficient (firstMomentKernel s) z) x =
                  firstMomentAbelDerivative s z x by
              simpa only [firstMomentAbelCoefficient] using
                deriv_firstMomentAbelCoefficient hs hz (by linarith) hxz]
            exact abs_firstMomentAbelDerivative_mul_thetaError_le
              hC hM hs hz hx2 hxz hPhi hPhiPrime (hTheta x hx))
      _ = mertensErrorPrimitive (2 * C * (M * s)) (Y : ℝ) -
          mertensErrorPrimitive (2 * C * (M * s)) (A : ℝ) :=
        integral_mertensErrorMajorant (2 * C * (M * s)) hAR hAYR
      _ ≤ 2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg :
            0 ≤ 2 * (C * (M * s)) / Real.log (Y : ℝ) ^ 3 := by
          positivity
        have heq :
            -(2 * C * (M * s)) / Real.log (Y : ℝ) ^ 3 -
                (-(2 * C * (M * s)) / Real.log (A : ℝ) ^ 3) =
              2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 -
                2 * (C * (M * s)) / Real.log (Y : ℝ) ^ 3 := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  have hAterm :
      |firstMomentAbelCoefficient s z (A : ℝ)| *
          |thetaError (A : ℝ)| ≤
        C * (M * s) / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    exact abs_firstMomentAbelCoefficient_mul_thetaError_le hM hs hz hAR
      (hAYR.trans hYz) hPhi (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩)
  have hYterm :
      |firstMomentAbelCoefficient s z (Y : ℝ)| *
          |thetaError (Y : ℝ)| ≤
        C * (M * s) / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    calc
      |firstMomentAbelCoefficient s z (Y : ℝ) * thetaError (Y : ℝ)| ≤
          C * (M * s) / Real.log (Y : ℝ) ^ 4 := by
        exact abs_firstMomentAbelCoefficient_mul_thetaError_le hM hs hz
          (by exact_mod_cast hY) hYz hPhi
          (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩)
      _ ≤ C * (M * s) / Real.log (A : ℝ) ^ 4 := by
        have hlogYpos : 0 < Real.log (Y : ℝ) := by
          exact Real.log_pos (by exact_mod_cast (show 1 < Y by omega))
        have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
          Real.log_le_log hApos hAYR
        gcongr
  have hinv4 :
      C * (M * s) / Real.log (A : ℝ) ^ 4 ≤
        2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
    have hone : 1 ≤ 2 * Real.log (A : ℝ) := by linarith
    have hpowNonneg : 0 ≤ Real.log (A : ℝ) ^ 3 :=
      pow_nonneg hlogApos.le 3
    have hmul := mul_le_mul_of_nonneg_right hone hpowNonneg
    have hinv :
        1 / Real.log (A : ℝ) ^ 4 ≤
          2 / Real.log (A : ℝ) ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hlogApos 4)
        (pow_pos hlogApos 3)).2
      calc
        1 * Real.log (A : ℝ) ^ 3 ≤
            (2 * Real.log (A : ℝ)) * Real.log (A : ℝ) ^ 3 := hmul
        _ = 2 * Real.log (A : ℝ) ^ 4 := by ring
    calc
      C * (M * s) / Real.log (A : ℝ) ^ 4 =
          (C * (M * s)) * (1 / Real.log (A : ℝ) ^ 4) := by ring
      _ ≤ (C * (M * s)) * (2 / Real.log (A : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hinv hCMs
      _ = 2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by ring
  calc
    |weightedAbelRemainder (firstMomentKernel s) z
        (A : ℝ) (Y : ℝ)| ≤
      |firstMomentAbelCoefficient s z (Y : ℝ)| * |thetaError (Y : ℝ)| +
        |firstMomentAbelCoefficient s z (A : ℝ)| * |thetaError (A : ℝ)| +
        ∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (firstMomentKernel s) z) x *
            thetaError x| :=
      abs_weightedAbelRemainder_le (firstMomentKernel s) z hAYR
    _ ≤ C * (M * s) / Real.log (A : ℝ) ^ 4 +
        C * (M * s) / Real.log (A : ℝ) ^ 4 +
        2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 := by
      linarith
    _ ≤ 6 * (C * M) * s / Real.log (A : ℝ) ^ 3 := by
      calc
        _ ≤ 2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 +
            2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 +
            2 * (C * (M * s)) / Real.log (A : ℝ) ^ 3 :=
          add_le_add (add_le_add hinv4 hinv4) le_rfl
        _ = 6 * (C * M) * s / Real.log (A : ℝ) ^ 3 := by ring

/-- Box-independent, relative one-index quadrature for the exact test
function occurring in the prime row. -/
theorem exists_uniform_firstMomentKernel_primeCell_relative_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 1 < z →
      ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        |fullWeightedReciprocalSum (firstMomentKernel s) z Y -
            fullWeightedReciprocalSum (firstMomentKernel s) z A -
            (∫ t in realLogCoordinate z (A : ℝ)..
              realLogCoordinate z (Y : ℝ), firstMomentKernel s t / t)| ≤
          (D / Real.log (A : ℝ) ^ 3) * s := by
  obtain ⟨Ctheta, hCtheta, Xtheta, hTheta⟩ :=
    exists_thetaError_log_cube_bound
  obtain ⟨Ckernel, hCkernel, hKernelProduct⟩ := kernel_product_bound
  obtain ⟨Cderiv, hCderiv, hDerivative⟩ :=
    kernel_secondDerivative_first_bound
  let M : ℝ := Ckernel + Cderiv
  have hM : 0 < M := add_pos hCkernel hCderiv
  have hPhi : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernel u t| ≤ M * u := by
    intro u hu t ht
    have hK : |covarianceKernel u t| ≤ Ckernel * u * t := by
      simpa only [covarianceKernel] using hKernelProduct u hu t ht
    rw [firstMomentKernel, abs_mul, abs_of_nonneg ht.1]
    calc
      t * |covarianceKernel u t| ≤ t * (Ckernel * u * t) :=
        mul_le_mul_of_nonneg_left hK ht.1
      _ = (Ckernel * u) * t ^ 2 := by ring
      _ ≤ (Ckernel * u) * 1 := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg hCkernel.le hu.1)
        nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
      _ ≤ M * u := by
        dsimp only [M]
        nlinarith [mul_nonneg hCderiv.le hu.1]
  have hPhiPrime : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |firstMomentKernelDerivative u t| ≤ M * u := by
    intro u hu t ht
    have hK : |covarianceKernel u t| ≤ Ckernel * u * t := by
      simpa only [covarianceKernel] using hKernelProduct u hu t ht
    have hExt := covarianceKernelDerivativeSecondExtension_eq hu ht
    have hD : |covarianceKernelDerivativeSecondExtension u t| ≤
        Cderiv * u := by
      rw [hExt]
      exact hDerivative u hu t ht
    unfold firstMomentKernelDerivative
    calc
      |covarianceKernel u t +
          t * covarianceKernelDerivativeSecondExtension u t| ≤
        |covarianceKernel u t| +
          |t * covarianceKernelDerivativeSecondExtension u t| :=
        abs_add_le _ _
      _ = |covarianceKernel u t| +
          t * |covarianceKernelDerivativeSecondExtension u t| := by
        rw [abs_mul, abs_of_nonneg ht.1]
      _ ≤ Ckernel * u * t + t * (Cderiv * u) := by
        exact add_le_add hK (mul_le_mul_of_nonneg_left hD ht.1)
      _ ≤ M * u := by
        dsimp only [M]
        have hk : Ckernel * u * t ≤ Ckernel * u := by
          exact mul_le_of_le_one_right
            (mul_nonneg hCkernel.le hu.1) ht.2
        have hd : t * (Cderiv * u) ≤ Cderiv * u := by
          rw [mul_comm]
          exact mul_le_of_le_one_right
            (mul_nonneg hCderiv.le hu.1) ht.2
        linarith
  obtain ⟨N, hN⟩ := exists_nat_gt Xtheta
  let D : ℝ := 6 * (Ctheta * M)
  refine ⟨D, by dsimp only [D]; positivity, max N 2, ?_⟩
  intro s hs z hz A Y hA hAY hYz
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hThetaCell : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ Ctheta * x / Real.log x ^ 3 := by
    intro x hx
    apply hTheta x
    exact le_trans (le_of_lt hN) (by exact_mod_cast hNA) |>.trans hx.1
  rw [firstMomentKernel_primeCell_sub_continuum_eq_remainder
    hs hz hA2 hAY hYz]
  have hbound := abs_firstMomentWeightedAbelRemainder_le
    hCtheta.le hM.le hs hz hA2 hAY hYz hPhi hPhiPrime hThetaCell
  calc
    _ ≤ 6 * (Ctheta * M) * s / Real.log (A : ℝ) ^ 3 := hbound
    _ = (D / Real.log (A : ℝ) ^ 3) * s := by
      dsimp only [D]
      ring

/-- The finite prime sum in the conjugated reference row is exactly the
weighted prime-cell sum for `firstMomentKernel`. -/
theorem sum_primeWeight_mul_primeKernel_eq_primeCell
    {n W : ℕ} (hWY : W ≤ yNat n)
    (p : PrimeIndex n W) :
    (∑ q : PrimeIndex n W,
        primeWeight n q * primeKernel n p q) =
      primeCellOperator (y n) W (yNat n)
        (firstMomentKernel (tPrime n p.1)) := by
  have hsets : intervalPrimes W (yNat n) = primeBand n W := by
    ext q
    rw [mem_intervalPrimes_iff, mem_primeBand]
  rw [primeCellOperator_eq_sum (y n) hWY, hsets]
  symm
  apply Finset.sum_bij
      (fun q hq => (⟨q, hq⟩ : PrimeIndex n W))
  · intro q hq
    simp only [Finset.mem_univ]
  · intro q₁ hq₁ q₂ hq₂ heq
    exact congrArg Subtype.val heq
  · intro q hq
    exact ⟨q.1, q.2, Subtype.ext rfl⟩
  · intro q hq
    unfold primeWeight primeKernel firstMomentKernel tPrime realLogCoordinate
    ring

lemma firstMomentKernel_div_eq_kernel
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    firstMomentKernel s t / t = covarianceKernel s t := by
  by_cases ht0 : t = 0
  · subst t
    have hzero := mul_covarianceKernelQuotient_eq_kernel hs
      (show (0 : ℝ) ∈ Icc (0 : ℝ) 1 by norm_num)
    have hkzero : covarianceKernel s 0 = 0 := by
      simpa only [zero_mul] using hzero.symm
    unfold firstMomentKernel
    rw [hkzero]
    norm_num
  · unfold firstMomentKernel
    field_simp [ht0]

/-- Symmetry identifies the full continuum main term with the removable
quotient row. -/
theorem integral_covarianceKernel_eq_mul_quotient
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (∫ t in (0 : ℝ)..1, covarianceKernel s t) =
      s * (∫ t in (0 : ℝ)..1, covarianceKernelQuotient t s) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t ht
  have htUnit : t ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using ht
  calc
    covarianceKernel s t = covarianceKernel t s := covarianceKernel_comm _ _
    _ = s * covarianceKernelQuotient t s :=
      (mul_covarianceKernelQuotient_eq_kernel htUnit hs).symm

theorem primeDiagonal_add_fullKernelIntegral_eq_zero
    {n W : ℕ} (hn : 1 < n) (p : PrimeIndex n W) :
    primeDiagonal n p +
        (∫ t in (0 : ℝ)..1,
          covarianceKernel (tPrime n p.1) t) = 0 := by
  have hs := tPrime_mem_unit hn p
  rw [integral_covarianceKernel_eq_mul_quotient _ hs]
  unfold primeDiagonal
  have hrow := PoissonDickmanWeightedInverse.weightedKernel_rowSum
    (tPrime n p.1) hs
  calc
    DickmanBasic.F (tPrime n p.1) * tPrime n p.1 +
        tPrime n p.1 *
          (∫ t in (0 : ℝ)..1,
            covarianceKernelQuotient t (tPrime n p.1)) =
      tPrime n p.1 *
        (DickmanBasic.F (tPrime n p.1) +
          ∫ t in (0 : ℝ)..1,
            covarianceKernelQuotient t (tPrime n p.1)) := by ring
    _ = 0 := by rw [hrow, mul_zero]

lemma abs_covarianceKernel_integral_le
    {C s a b : ℝ} (hC : 0 ≤ C)
    (hs : s ∈ Icc (0 : ℝ) 1) (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 1)
    (hKernel : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t) :
    |∫ t in a..b, covarianceKernel s t| ≤ (C * s) * (b - a) := by
  have hCs : 0 ≤ C * s := mul_nonneg hC hs.1
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (C := C * s)
    (f := fun t : ℝ => covarianceKernel s t) (fun t ht => by
      have ht' : t ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using uIoc_subset_uIcc ht
      have htUnit : t ∈ Icc (0 : ℝ) 1 :=
        ⟨ha.trans ht'.1, ht'.2.trans hb⟩
      rw [Real.norm_eq_abs]
      calc
        |covarianceKernel s t| ≤ C * s * t := hKernel s hs t htUnit
        _ ≤ C * s := mul_le_of_le_one_right hCs htUnit.2)
  rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab)] at hnorm
  exact hnorm

/-- Explicit relative row-error budget: the PNT term plus the two literal
endpoint tails. -/
def primeRowRelativeError (D C : ℝ) (n W : ℕ) : ℝ :=
  D / Real.log (W : ℝ) ^ 3 +
    C * (realLogCoordinate (y n) (W : ℝ) +
      (1 - realLogCoordinate (y n) (yNat n : ℝ)))

set_option maxHeartbeats 1200000 in
/-- Deterministic attachment of relative first-moment quadrature to the
literal finite prime row. -/
theorem abs_primeRowResidual_le_of_relative_quadrature
    {D C : ℝ} (hC : 0 ≤ C)
    {n W : ℕ} (hn : 1 < n) (hW2 : 2 ≤ W) (hWY : W ≤ yNat n)
    (hKernel : ∀ u ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u t| ≤ C * u * t)
    (hquad : ∀ s ∈ Icc (0 : ℝ) 1,
      |primeCellOperator (y n) W (yNat n) (firstMomentKernel s) -
          (∫ t in realLogCoordinate (y n) (W : ℝ)..
            realLogCoordinate (y n) (yNat n : ℝ),
              firstMomentKernel s t / t)| ≤
        (D / Real.log (W : ℝ) ^ 3) * s)
    (p : PrimeIndex n W) :
    |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
      primeRowRelativeError D C n W * tPrime n p.1 := by
  let s : ℝ := tPrime n p.1
  let a : ℝ := realLogCoordinate (y n) (W : ℝ)
  let b : ℝ := realLogCoordinate (y n) (yNat n : ℝ)
  let primeMain : ℝ :=
    primeCellOperator (y n) W (yNat n) (firstMomentKernel s)
  let continuumMain : ℝ := ∫ t in a..b, covarianceKernel s t
  let lowTail : ℝ := ∫ t in (0 : ℝ)..a, covarianceKernel s t
  let topTail : ℝ := ∫ t in b..1, covarianceKernel s t
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hyNatY : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hWNat : (W : ℝ) ≤ (yNat n : ℝ) := by exact_mod_cast hWY
  have hWOne : (1 : ℝ) ≤ W := by exact_mod_cast hW2.trans' (by omega)
  have hyNatOne : (1 : ℝ) ≤ yNat n := hWOne.trans hWNat
  have haUnit : a ∈ Icc (0 : ℝ) 1 := by
    dsimp only [a]
    exact realLogCoordinate_mem_unit hy hWOne (hWNat.trans hyNatY)
  have hbUnit : b ∈ Icc (0 : ℝ) 1 := by
    dsimp only [b]
    exact realLogCoordinate_mem_unit hy hyNatOne hyNatY
  have hab : a ≤ b := by
    dsimp only [a, b]
    exact realLogCoordinate_mono_nat hy hW2 hWY
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    dsimp only [s]
    exact tPrime_mem_unit hn p
  have hcontinuum :
      (∫ t in a..b, firstMomentKernel s t / t) = continuumMain := by
    dsimp only [continuumMain]
    apply intervalIntegral.integral_congr
    intro t ht
    have htUnit : t ∈ Icc (0 : ℝ) 1 := by
      have ht' : t ∈ Icc a b := by
        simpa only [uIcc_of_le hab] using ht
      exact ⟨haUnit.1.trans ht'.1, ht'.2.trans hbUnit.2⟩
    exact firstMomentKernel_div_eq_kernel hs htUnit
  have hPrime :
      |primeMain - continuumMain| ≤
        (D / Real.log (W : ℝ) ^ 3) * s := by
    dsimp only [primeMain]
    rw [← hcontinuum]
    exact hquad s hs
  have hLow : |lowTail| ≤ (C * s) * a := by
    dsimp only [lowTail]
    simpa only [sub_zero] using
      abs_covarianceKernel_integral_le hC hs haUnit.1 (by norm_num)
        haUnit.2 hKernel
  have hTop : |topTail| ≤ (C * s) * (1 - b) := by
    dsimp only [topTail]
    exact abs_covarianceKernel_integral_le hC hs hbUnit.2 hbUnit.1
      (by norm_num) hKernel
  have hsplit :
      (∫ t in (0 : ℝ)..1, covarianceKernel s t) =
        lowTail + continuumMain + topTail := by
    have hIntLow : IntervalIntegrable (covarianceKernel s) volume
        (0 : ℝ) a := (continuous_covarianceKernel_left s).intervalIntegrable _ _
    have hIntMid : IntervalIntegrable (covarianceKernel s) volume
        a b := (continuous_covarianceKernel_left s).intervalIntegrable _ _
    have hIntTop : IntervalIntegrable (covarianceKernel s) volume
        b 1 := (continuous_covarianceKernel_left s).intervalIntegrable _ _
    have hfirst := intervalIntegral.integral_add_adjacent_intervals
      hIntLow hIntMid
    have hsecond := intervalIntegral.integral_add_adjacent_intervals
      (hIntLow.trans hIntMid) hIntTop
    dsimp only [lowTail, continuumMain, topTail]
    linarith
  have hzero : primeDiagonal n p +
      (∫ t in (0 : ℝ)..1, covarianceKernel s t) = 0 := by
    simpa only [s] using primeDiagonal_add_fullKernelIntegral_eq_zero hn p
  have hrow :
      rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p =
        primeDiagonal n p + primeMain := by
    unfold rowResidual
    rw [sum_primeWeight_mul_primeKernel_eq_primeCell hWY p]
  have hdecomp :
      rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p =
        (primeMain - continuumMain) - lowTail - topTail := by
    rw [hrow]
    rw [hsplit] at hzero
    linarith
  rw [hdecomp]
  calc
    |(primeMain - continuumMain) - lowTail - topTail| ≤
        |primeMain - continuumMain| + |lowTail| + |topTail| := by
      have h₁ := abs_sub (primeMain - continuumMain) lowTail
      have h₂ := abs_sub ((primeMain - continuumMain) - lowTail) topTail
      linarith
    _ ≤ (D / Real.log (W : ℝ) ^ 3) * s +
        (C * s) * a + (C * s) * (1 - b) :=
      add_le_add (add_le_add hPrime hLow) hTop
    _ = primeRowRelativeError D C n W * tPrime n p.1 := by
      dsimp only [primeRowRelativeError, s, a, b]
      ring

/-- Uniform literal prime-row theorem.  The constant multiplying
`log(W)^{-3}` is selected before the cutoff and before the ambient integer. -/
theorem exists_uniform_primeRowResidual_relative_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ C : ℝ, 0 < C ∧ ∃ X₀ : ℕ,
      ∀ {n W : ℕ}, 1 < n → X₀ ≤ W → W ≤ yNat n →
        ∀ p : PrimeIndex n W,
          |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
            primeRowRelativeError D C n W * tPrime n p.1 := by
  obtain ⟨D, hD, Xquad, hquad⟩ :=
    exists_uniform_firstMomentKernel_primeCell_relative_bound
  obtain ⟨C, hC, hKernel⟩ := kernel_product_bound
  refine ⟨D, hD, C, hC, max Xquad 2, ?_⟩
  intro n W hn hW hWY p
  have hW2 : 2 ≤ W := (le_max_right Xquad 2).trans hW
  have hXquad : Xquad ≤ W := (le_max_left Xquad 2).trans hW
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hyNatY : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le (Scale.y_pos (Nat.zero_lt_of_lt hn)).le
  have hrelative : ∀ s ∈ Icc (0 : ℝ) 1,
      |primeCellOperator (y n) W (yNat n) (firstMomentKernel s) -
          (∫ t in realLogCoordinate (y n) (W : ℝ)..
            realLogCoordinate (y n) (yNat n : ℝ),
              firstMomentKernel s t / t)| ≤
        (D / Real.log (W : ℝ) ^ 3) * s := by
    intro s hs
    simpa only [primeCellOperator] using
      hquad s hs (y n) hy W (yNat n) hXquad hWY hyNatY
  exact abs_primeRowResidual_le_of_relative_quadrature hC.le hn hW2 hWY
    (by
      intro u hu t ht
      simpa only [covarianceKernel] using hKernel u hu t ht)
    hrelative p

theorem tendsto_primeRowRelativeError_fixedCutoff
    (D C : ℝ) (W : ℕ) :
    Tendsto (fun n : ℕ ↦ primeRowRelativeError D C n W)
      atTop (nhds (D / Real.log (W : ℝ) ^ 3)) := by
  have hbase : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (W : ℝ)) atTop (nhds 0) := by
    simpa only using
      _root_.Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_fixed_cutoffCoordinate_zero W
  have htopRaw :=
    _root_.Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.tendsto_floor_scalePoint_coordinate
      (t := (1 : ℝ)) (by norm_num)
  have htop : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (yNat n : ℝ)) atTop (nhds 1) := by
    apply htopRaw.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    unfold yNat RegularMeshPrimeCutoffs.scalePoint
    rw [one_mul, Real.exp_log (Scale.y_pos hn)]
  have htail : Tendsto (fun n : ℕ ↦
      realLogCoordinate (y n) (W : ℝ) +
        (1 - realLogCoordinate (y n) (yNat n : ℝ)))
      atTop (nhds 0) := by
    simpa only [sub_self, add_zero] using
      hbase.add ((tendsto_const_nhds : Tendsto
        (fun _n : ℕ ↦ (1 : ℝ)) atTop (nhds 1)).sub htop)
  have hscaled := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ C) atTop (nhds C)).mul htail
  have hconst : Tendsto (fun _n : ℕ ↦
      D / Real.log (W : ℝ) ^ 3) atTop
      (nhds (D / Real.log (W : ℝ) ^ 3)) := tendsto_const_nhds
  simpa only [primeRowRelativeError, mul_zero, add_zero] using
    hconst.add hscaled

/-- Fully eventual relative row terminal.  Given any prescribed positive
row tolerance, one cutoff threshold works for every larger cutoff; after
that choice the literal row bound holds for every sufficiently large
ambient integer and every marked prime. -/
theorem exists_cutoff_eventually_primeRowResidual_le
    {target : ℝ} (htarget : 0 < target) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ p : PrimeIndex n W,
        |rowResidual (primeWeight n) (primeDiagonal n) (primeKernel n) p| ≤
          target * tPrime n p.1 := by
  obtain ⟨D, hD, C, hC, Xrow, hrow⟩ :=
    exists_uniform_primeRowResidual_relative_bound
  have hLogTop : Tendsto (fun W : ℕ ↦ Real.log (W : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hInv : Tendsto (fun W : ℕ ↦ (Real.log (W : ℝ))⁻¹)
      atTop (nhds 0) := tendsto_inv_atTop_zero.comp hLogTop
  have hFixed : Tendsto (fun W : ℕ ↦
      D / Real.log (W : ℝ) ^ 3) atTop (nhds 0) := by
    have hmain := (tendsto_const_nhds : Tendsto
      (fun _W : ℕ ↦ D) atTop (nhds D)).mul (hInv.pow 3)
    simpa only [div_eq_mul_inv, inv_pow, mul_zero,
      zero_pow (by norm_num : 3 ≠ 0)] using hmain
  have hFixedSmall : ∀ᶠ W : ℕ in atTop,
      D / Real.log (W : ℝ) ^ 3 < target / 2 :=
    hFixed.eventually (eventually_lt_nhds (half_pos htarget))
  obtain ⟨Wsmall, hWsmall⟩ := eventually_atTop.1 hFixedSmall
  refine ⟨max Xrow Wsmall, ?_⟩
  intro W hW
  have hXrow : Xrow ≤ W := (le_max_left Xrow Wsmall).trans hW
  have hWsmall' : Wsmall ≤ W := (le_max_right Xrow Wsmall).trans hW
  have hfixedW : D / Real.log (W : ℝ) ^ 3 < target / 2 :=
    hWsmall W hWsmall'
  have herrorT := tendsto_primeRowRelativeError_fixedCutoff D C W
  have herrorSmall : ∀ᶠ n : ℕ in atTop,
      primeRowRelativeError D C n W < target :=
    herrorT.eventually (eventually_lt_nhds (by linarith))
  have hyNatTop : Tendsto (fun n : ℕ ↦ yNat n) atTop atTop := by
    unfold yNat
    exact tendsto_nat_floor_atTop.comp
      Erdos390.Full.RegularMeshPrimeCutoffs.tendsto_y_atTop
  have hWY : ∀ᶠ n : ℕ in atTop, W ≤ yNat n :=
    hyNatTop.eventually (eventually_ge_atTop W)
  filter_upwards [eventually_gt_atTop 1, hWY, herrorSmall] with
      n hn hWYn herrorN
  intro p
  have hraw := hrow hn hXrow hWYn p
  exact hraw.trans (mul_le_mul_of_nonneg_right herrorN.le
    (tPrime_mem_unit hn p).1)

end Erdos390.Full.PaperCanonicalPrimeRowResidualEventually
