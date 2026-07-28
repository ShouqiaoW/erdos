import Erdos390.Full.PrimeBandQuadrature
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Weighted prime quadrature for the Poisson--Dickman kernel

This file generalizes the scalar Abel summation used for `H_j` to a smooth
test function on logarithmic prime coordinates.  The first layer is an exact
finite identity for the actual primes; later declarations specialize it to
the Poisson--Dickman covariance kernel and its compact derivative bounds.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.KernelPrimeQuadrature

open MeasureTheory
open ArithmeticModel PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit

/-- Ordinary derivative of the covariance kernel in its second coordinate. -/
def covarianceKernelDerivativeSecond (s t : ℝ) : ℝ :=
  deriv F (s + t) - F s * deriv F t

/-- Globally continuous extension of the second-coordinate derivative. -/
def covarianceKernelDerivativeSecondExtension (s t : ℝ) : ℝ :=
  derivFExtension (s + t) - F s * derivFExtension t

lemma continuous_covarianceKernelDerivativeSecondExtension_left (s : ℝ) :
    Continuous (covarianceKernelDerivativeSecondExtension s) := by
  unfold covarianceKernelDerivativeSecondExtension
  exact (continuous_derivFExtension.comp
      (continuous_const.add continuous_id)).sub
    (continuous_const.mul continuous_derivFExtension)

lemma continuous_uncurry_covarianceKernelDerivativeSecondExtension :
    Continuous (Function.uncurry covarianceKernelDerivativeSecondExtension) := by
  unfold covarianceKernelDerivativeSecondExtension Function.uncurry
  exact (continuous_derivFExtension.comp
      (continuous_fst.add continuous_snd)).sub
    ((continuous_F.comp continuous_fst).mul
      (continuous_derivFExtension.comp continuous_snd))

/-- Uniform `C¹` bound for the actual kernel family on the unit square. -/
theorem exists_covarianceKernel_uniform_C1_bound :
    ∃ M : ℝ, 0 < M ∧
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
        |covarianceKernel s t| ≤ M ∧
        |covarianceKernelDerivativeSecondExtension s t| ≤ M := by
  let S : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1
  have hScompact : IsCompact S := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C₀, hC₀⟩ := hScompact.exists_bound_of_continuousOn
    continuous_covarianceKernel.continuousOn
  obtain ⟨C₁, hC₁⟩ := hScompact.exists_bound_of_continuousOn
    continuous_uncurry_covarianceKernelDerivativeSecondExtension.continuousOn
  have hmem : ((0 : ℝ), (0 : ℝ)) ∈ S := ⟨by norm_num, by norm_num⟩
  have hC₀nonneg : 0 ≤ C₀ :=
    (norm_nonneg (covarianceKernel 0 0)).trans (hC₀ (0, 0) hmem)
  have hC₁nonneg : 0 ≤ C₁ :=
    (norm_nonneg (covarianceKernelDerivativeSecondExtension 0 0)).trans
      (hC₁ (0, 0) hmem)
  refine ⟨1 + C₀ + C₁, by linarith, ?_⟩
  intro s hs t ht
  constructor
  · have h := hC₀ (s, t) ⟨hs, ht⟩
    rw [Real.norm_eq_abs] at h
    change |covarianceKernel s t| ≤ C₀ at h
    linarith
  · have h := hC₁ (s, t) ⟨hs, ht⟩
    rw [Real.norm_eq_abs] at h
    change |covarianceKernelDerivativeSecondExtension s t| ≤ C₁ at h
    linarith

lemma covarianceKernelDerivativeSecondExtension_eq {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    covarianceKernelDerivativeSecondExtension s t =
      covarianceKernelDerivativeSecond s t := by
  have hst : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  unfold covarianceKernelDerivativeSecondExtension
  unfold covarianceKernelDerivativeSecond
  rw [derivFExtension_eq_deriv_of_mem hst,
    derivFExtension_eq_deriv_of_mem
      ⟨ht.1, ht.2.trans (by norm_num)⟩]

lemma continuous_covarianceKernel_left (s : ℝ) :
    Continuous (covarianceKernel s) := by
  exact continuous_covarianceKernel.comp
    (continuous_const.prodMk continuous_id)

lemma hasDerivAt_covarianceKernel_second {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (covarianceKernel s)
      (covarianceKernelDerivativeSecond s t) t := by
  have ht₂ : t ∈ Icc (0 : ℝ) 2 :=
    ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hst₂ : s + t ∈ Icc (0 : ℝ) 2 := by
    constructor <;> linarith [hs.1, hs.2, ht.1, ht.2]
  have hshift : HasDerivAt (fun u : ℝ => s + u) 1 t := by
    simpa only [zero_add] using
      (hasDerivAt_const t s).add (hasDerivAt_id t)
  have hfirst := (differentiableAt_F hst₂).hasDerivAt.comp t hshift
  have hsecond := (differentiableAt_F ht₂).hasDerivAt.const_mul (F s)
  convert hfirst.sub hsecond using 1
  unfold covarianceKernelDerivativeSecond
  ring

/-- Logarithmic coordinate at a positive real scale. -/
def realLogCoordinate (z x : ℝ) : ℝ := Real.log x / Real.log z

lemma realLogCoordinate_mem_unit {z x : ℝ}
    (hz : 1 < z) (hx : 1 ≤ x) (hxz : x ≤ z) :
    realLogCoordinate z x ∈ Icc (0 : ℝ) 1 := by
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxnonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogxz : Real.log x ≤ Real.log z :=
    Real.log_le_log (zero_lt_one.trans_le hx) hxz
  unfold realLogCoordinate
  constructor
  · exact div_nonneg hlogxnonneg hlogzpos.le
  · exact (div_le_one hlogzpos).2 hlogxz

/-- The Abel coefficient whose multiplication by `log p` gives
`phi(log p / log z) / p`. -/
def weightedAbelCoefficient (phi : ℝ → ℝ) (z x : ℝ) : ℝ :=
  phi (realLogCoordinate z x) / (x * Real.log x)

/-- Explicit derivative of the weighted Abel coefficient. -/
def weightedAbelCoefficientDerivative
    (phi phiPrime : ℝ → ℝ) (z x : ℝ) : ℝ :=
  phiPrime (realLogCoordinate z x) /
      (x ^ 2 * Real.log x * Real.log z) -
    phi (realLogCoordinate z x) * (Real.log x + 1) /
      (x ^ 2 * Real.log x ^ 2)

lemma hasDerivAt_weightedAbelCoefficient
    (phi phiPrime : ℝ → ℝ) {z x : ℝ}
    (hz : 1 < z) (hx : 1 < x)
    (hphi : HasDerivAt phi (phiPrime (realLogCoordinate z x))
      (realLogCoordinate z x)) :
    HasDerivAt (weightedAbelCoefficient phi z)
      (weightedAbelCoefficientDerivative phi phiPrime z x) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  have hcoord : HasDerivAt (realLogCoordinate z)
      (1 / (x * Real.log z)) x := by
    have h := (Real.hasDerivAt_log hx0).div_const (Real.log z)
    convert h using 1
    field_simp [hx0, hlogz0]
  have hnum := hphi.comp x hcoord
  have hden : HasDerivAt (fun u : ℝ => u * Real.log u)
      (Real.log x + 1) x := by
    have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log hx0)
    convert h using 1
    simp only [id_eq]
    field_simp [hx0]
  have hquot := hnum.div hden (mul_ne_zero hx0 hlogx0)
  convert hquot using 1
  unfold weightedAbelCoefficientDerivative
  simp only [Function.comp_apply]
  field_simp [hx0, hlogx0, hlogz0]

lemma continuousAt_weightedAbelCoefficientDerivative
    (phi phiPrime : ℝ → ℝ)
    (hphi : Continuous phi) (hphiPrime : Continuous phiPrime)
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (weightedAbelCoefficientDerivative phi phiPrime z) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  have hcoord : ContinuousAt (realLogCoordinate z) x := by
    unfold realLogCoordinate
    exact (Real.continuousAt_log hx0).div_const (Real.log z)
  have hnumPrime : ContinuousAt
      (fun u : ℝ => phiPrime (realLogCoordinate z u)) x :=
    hphiPrime.continuousAt.comp hcoord
  have hnum : ContinuousAt
      (fun u : ℝ => phi (realLogCoordinate z u)) x :=
    hphi.continuousAt.comp hcoord
  have hdenPrime : ContinuousAt
      (fun u : ℝ => u ^ 2 * Real.log u * Real.log z) x :=
    ((continuousAt_id.pow 2).mul (Real.continuousAt_log hx0)).mul
      continuousAt_const
  have hdenPrime0 : x ^ 2 * Real.log x * Real.log z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hx0) hlogx0) hlogz0
  have hfactor : ContinuousAt (fun u : ℝ => Real.log u + 1) x :=
    (Real.continuousAt_log hx0).add continuousAt_const
  have hden : ContinuousAt
      (fun u : ℝ => u ^ 2 * Real.log u ^ 2) x :=
    (continuousAt_id.pow 2).mul ((Real.continuousAt_log hx0).pow 2)
  have hden0 : x ^ 2 * Real.log x ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 2 hx0) (pow_ne_zero 2 hlogx0)
  unfold weightedAbelCoefficientDerivative
  exact (hnumPrime.div hdenPrime hdenPrime0).sub
    ((hnum.mul hfactor).div hden hden0)

/-- Actual weighted harmonic prime sum up to a natural endpoint. -/
def fullWeightedReciprocalSum (phi : ℝ → ℝ) (z : ℝ) (Y : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo Y, phi (realLogCoordinate z (p : ℝ)) / (p : ℝ)

/-- Actual Abel coefficient for one fixed first kernel coordinate. -/
def kernelWeightedAbelCoefficient (s z x : ℝ) : ℝ :=
  weightedAbelCoefficient (covarianceKernel s) z x

/-- Its continuous explicit derivative on the physical range. -/
def kernelWeightedAbelDerivative (s z x : ℝ) : ℝ :=
  weightedAbelCoefficientDerivative (covarianceKernel s)
    (covarianceKernelDerivativeSecondExtension s) z x

lemma hasDerivAt_kernelWeightedAbelCoefficient {s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z) :
    HasDerivAt (kernelWeightedAbelCoefficient s z)
      (kernelWeightedAbelDerivative s z x) x := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hkernel := hasDerivAt_covarianceKernel_second hs ht
  have hext := covarianceKernelDerivativeSecondExtension_eq hs ht
  have hkernel' : HasDerivAt (covarianceKernel s)
      (covarianceKernelDerivativeSecondExtension s
        (realLogCoordinate z x)) (realLogCoordinate z x) :=
    hkernel.congr_deriv hext.symm
  exact hasDerivAt_weightedAbelCoefficient
    (covarianceKernel s) (covarianceKernelDerivativeSecondExtension s)
    hz hx hkernel'

lemma deriv_kernelWeightedAbelCoefficient {s z x : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z) :
    deriv (kernelWeightedAbelCoefficient s z) x =
      kernelWeightedAbelDerivative s z x :=
  (hasDerivAt_kernelWeightedAbelCoefficient hs hz hx hxz).deriv

lemma continuousAt_kernelWeightedAbelDerivative (s : ℝ)
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (kernelWeightedAbelDerivative s z) x := by
  exact continuousAt_weightedAbelCoefficientDerivative
    (covarianceKernel s) (covarianceKernelDerivativeSecondExtension s)
    (continuous_covarianceKernel_left s)
    (continuous_covarianceKernelDerivativeSecondExtension_left s) hz hx

lemma continuousOn_kernelWeightedAbelDerivative (s : ℝ)
    {z A Y : ℝ} (hz : 1 < z) (hA : 1 < A) :
    ContinuousOn (kernelWeightedAbelDerivative s z) (Icc A Y) := by
  intro x hx
  exact (continuousAt_kernelWeightedAbelDerivative s hz
    (hA.trans_le hx.1)).continuousWithinAt

lemma abs_kernelWeightedAbelCoefficient_le
    {M s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u v| ≤ M) :
    |kernelWeightedAbelCoefficient s z x| ≤
      M / (x * Real.log x) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hdenpos : 0 < x * Real.log x := mul_pos hxpos hlogxpos
  unfold kernelWeightedAbelCoefficient weightedAbelCoefficient
  rw [abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hK s hs _ ht) hdenpos.le

lemma abs_kernelWeightedAbelDerivative_le
    {M s z x : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 1 < x) (hxz : x ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u v| ≤ M ∧
      |covarianceKernelDerivativeSecondExtension u v| ≤ M) :
    |kernelWeightedAbelDerivative s z x| ≤
      M / (x ^ 2 * Real.log x * Real.log z) +
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
  have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
  have hplus : 0 ≤ Real.log x + 1 := by linarith
  unfold kernelWeightedAbelDerivative weightedAbelCoefficientDerivative
  calc
    |covarianceKernelDerivativeSecondExtension s (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z) -
        covarianceKernel s (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| ≤
      |covarianceKernelDerivativeSecondExtension s (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z)| +
        |covarianceKernel s (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| := abs_sub _ _
    _ = |covarianceKernelDerivativeSecondExtension s (realLogCoordinate z x)| /
          (x ^ 2 * Real.log x * Real.log z) +
        |covarianceKernel s (realLogCoordinate z x)| * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
      rw [abs_div, abs_div]
      simp only [abs_mul]
      rw [abs_of_nonneg (sq_nonneg x), abs_of_pos hlogxpos,
        abs_of_pos hlogzpos, abs_of_nonneg hplus,
        abs_of_nonneg (sq_nonneg (Real.log x))]
    _ ≤ M / (x ^ 2 * Real.log x * Real.log z) +
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (hK s hs _ ht).2 hden₁.le
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hK s hs _ ht).1 hplus) hden₂.le

/-- The endpoint term in the weighted Abel remainder has the expected
log-power-four decay. -/
lemma abs_kernelWeightedAbelCoefficient_mul_thetaError_le
    {C M s z x : ℝ} (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u v| ≤ M)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |kernelWeightedAbelCoefficient s z x * thetaError x| ≤
      C * M / Real.log x ^ 4 := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hcoeff := abs_kernelWeightedAbelCoefficient_le hs hz hx1 hxz hK
  rw [abs_mul]
  calc
    |kernelWeightedAbelCoefficient s z x| * |thetaError x| ≤
        (M / (x * Real.log x)) *
          (C * x / Real.log x ^ 3) := by gcongr
    _ = C * M / Real.log x ^ 4 := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]

/-- The derivative term in the kernel Abel remainder is dominated by the
same integrable majorant as in scalar Mertens quadrature.  The factor `2`
leaves room for both the kernel and its first derivative. -/
lemma abs_kernelWeightedAbelDerivative_mul_thetaError_le
    {C M s z x : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u v| ≤ M ∧
      |covarianceKernelDerivativeSecondExtension u v| ≤ M)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |kernelWeightedAbelDerivative s z x * thetaError x| ≤
      mertensErrorMajorant (2 * C * M) x := by
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
  have hderiv := abs_kernelWeightedAbelDerivative_le hs hz hx1 hxz hK
  have hsimplified :
      M / (x ^ 2 * Real.log x * Real.log z) +
          M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
        5 * M / (x ^ 2 * Real.log x) := by
    have hdenx : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
    have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
    have hden₃ : 0 < x ^ 2 * Real.log x := by positivity
    have hfirst :
        M / (x ^ 2 * Real.log x * Real.log z) ≤
          M / (x ^ 2 * Real.log x ^ 2) := by
      apply (div_le_div_iff₀ hden₁ hden₂).2
      apply mul_le_mul_of_nonneg_left _ hM
      nlinarith [mul_pos hdenx hlogpos]
    have hsecond :
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
          3 * M / (x ^ 2 * Real.log x) := by
      calc
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
            M * (3 * Real.log x) /
              (x ^ 2 * Real.log x ^ 2) := by gcongr
        _ = 3 * M / (x ^ 2 * Real.log x) := by
          field_simp [ne_of_gt hlogpos]
    have hfirst' :
        M / (x ^ 2 * Real.log x ^ 2) ≤
          2 * M / (x ^ 2 * Real.log x) := by
      have : 1 ≤ 2 * Real.log x := by linarith
      apply (div_le_div_iff₀ hden₂ hden₃).2
      calc
        M * (x ^ 2 * Real.log x) ≤
            M * (x ^ 2 * Real.log x) * (2 * Real.log x) := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left this
              (mul_nonneg hM hden₃.le))
        _ = 2 * M * (x ^ 2 * Real.log x ^ 2) := by ring
    calc
      M / (x ^ 2 * Real.log x * Real.log z) +
          M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) ≤
        M / (x ^ 2 * Real.log x ^ 2) +
          3 * M / (x ^ 2 * Real.log x) :=
            add_le_add hfirst hsecond
      _ ≤ 2 * M / (x ^ 2 * Real.log x) +
          3 * M / (x ^ 2 * Real.log x) :=
            add_le_add hfirst' (le_refl _)
      _ = 5 * M / (x ^ 2 * Real.log x) := by ring
  rw [abs_mul]
  calc
    |kernelWeightedAbelDerivative s z x| * |thetaError x| ≤
        (5 * M / (x ^ 2 * Real.log x)) *
          (C * x / Real.log x ^ 3) := by
      apply mul_le_mul
      · exact hderiv.trans hsimplified
      · exact hTheta
      · positivity
      · have := abs_nonneg (kernelWeightedAbelDerivative s z x)
        positivity
    _ ≤ mertensErrorMajorant (2 * C * M) x := by
      unfold mertensErrorMajorant
      have hCM : 0 ≤ C * M := mul_nonneg hC hM
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]
      nlinarith

/-- On an actual prime range below `z`, the ordinary derivative is the
explicit continuous kernel derivative. -/
theorem integrableOn_deriv_kernelWeightedAbelCoefficient
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hYz : (Y : ℝ) ≤ z) :
    IntegrableOn (deriv (kernelWeightedAbelCoefficient s z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have hcont : ContinuousOn (kernelWeightedAbelDerivative s z)
      (Icc (2 : ℝ) (Y : ℝ)) :=
    continuousOn_kernelWeightedAbelDerivative s hz (by norm_num)
  apply (hcont.integrableOn_Icc).congr_fun
  · intro x hx
    symm
    apply deriv_kernelWeightedAbelCoefficient hs hz
    · linarith [hx.1]
    · exact hx.2.trans hYz
  · exact measurableSet_Icc

/-- A continuous coefficient times the actual Chebyshev step function is
interval-integrable on every positive compact interval. -/
theorem intervalIntegrable_continuous_mul_theta
    {g : ℝ → ℝ} {A Y : ℝ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hg : ContinuousOn g (Icc A Y)) :
    IntervalIntegrable (fun x => g x * Chebyshev.theta x) volume A Y := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAY]
  conv =>
    arg 1
    ext x
    rw [Chebyshev.theta, Finset.sum_filter]
  refine integrableOn_mul_sum_Icc _ (by linarith [hA]) ?_
  exact hg.integrableOn_Icc

lemma intervalIntegrable_deriv_kernelWeighted_mul_theta
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {Y : ℕ} (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (kernelWeightedAbelCoefficient s z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := kernelWeightedAbelDerivative s z) (A := (2 : ℝ))
    (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_kernelWeightedAbelDerivative s hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change kernelWeightedAbelDerivative s z x * Chebyshev.theta x =
    deriv (kernelWeightedAbelCoefficient s z) x * Chebyshev.theta x
  congr 1
  exact (deriv_kernelWeightedAbelCoefficient hs hz
    (by linarith [hx'.1]) (hx'.2.trans hYz)).symm

lemma intervalIntegrable_deriv_kernelWeighted_mul_id
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (kernelWeightedAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ => kernelWeightedAbelDerivative s z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_kernelWeightedAbelDerivative s hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase : IntervalIntegrable
      (fun x : ℝ => kernelWeightedAbelDerivative s z x * x)
      volume (A : ℝ) (Y : ℝ) :=
    hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change kernelWeightedAbelDerivative s z x * x =
    deriv (kernelWeightedAbelCoefficient s z) x * x
  congr 1
  exact (deriv_kernelWeightedAbelCoefficient hs hz
    (by linarith [hAR, hx'.1]) (hx'.2.trans hYz)).symm

lemma continuousAt_weightedAbelCoefficient (phi : ℝ → ℝ)
    (hphi : Continuous phi) {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (weightedAbelCoefficient phi z) x := by
  have hx0 : x ≠ 0 := ne_of_gt (zero_lt_one.trans hx)
  have hlogx0 : Real.log x ≠ 0 := ne_of_gt (Real.log_pos hx)
  have hlogz0 : Real.log z ≠ 0 := ne_of_gt (Real.log_pos hz)
  unfold weightedAbelCoefficient realLogCoordinate
  exact (hphi.continuousAt.comp
      ((Real.continuousAt_log hx0).div_const (Real.log z))).div
    (continuousAt_id.mul (Real.continuousAt_log hx0))
    (mul_ne_zero hx0 hlogx0)

/-- Change of variables from the real prime coordinate to `t=log x/log z`.
The statement is exact and keeps the actual natural endpoints. -/
theorem integral_weightedAbelCoefficient_eq_logCoordinate
    (phi : ℝ → ℝ) (hphi : Continuous phi) {z : ℝ} (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) :
    (∫ x in (A : ℝ)..Y, weightedAbelCoefficient phi z x) =
      ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
        phi t / t := by
  let a : ℝ := realLogCoordinate z (A : ℝ)
  let b : ℝ := realLogCoordinate z (Y : ℝ)
  let path : ℝ → ℝ := fun t => Real.exp (Real.log z * t)
  let path' : ℝ → ℝ := fun t => Real.log z * Real.exp (Real.log z * t)
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hApos : (0 : ℝ) < (A : ℝ) := by positivity
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    exact_mod_cast (show 0 < Y by omega)
  have hlogApos : 0 < Real.log (A : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) := by
    exact Real.log_le_log hApos (by exact_mod_cast hAY)
  have hab : a ≤ b := by
    dsimp [a, b, realLogCoordinate]
    exact div_le_div_of_nonneg_right hlogAY hlogzpos.le
  have hpath (t : ℝ) : HasDerivAt path (path' t) t := by
    have hlin : HasDerivAt (fun u : ℝ => Real.log z * u)
        (Real.log z) t := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id t).const_mul (Real.log z)
    simpa only [path, path', Function.comp_def, mul_comm] using
      (Real.hasDerivAt_exp (Real.log z * t)).comp t hlin
  have hpath' : ContinuousOn path' (uIcc a b) := by
    exact (continuous_const.mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id))).continuousOn
  have hcoeff : ContinuousOn (weightedAbelCoefficient phi z)
      (path '' uIcc a b) := by
    intro x hx
    obtain ⟨t, ht, rfl⟩ := hx
    have htIcc : t ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using ht
    have haPos : 0 < a := by
      dsimp [a, realLogCoordinate]
      exact div_pos hlogApos hlogzpos
    have htPos : 0 < t := haPos.trans_le htIcc.1
    have hpathOne : 1 < path t := by
      dsimp [path]
      rw [Real.one_lt_exp_iff]
      exact mul_pos hlogzpos htPos
    exact (continuousAt_weightedAbelCoefficient phi hphi hz hpathOne).continuousWithinAt
  have hsubst := intervalIntegral.integral_comp_mul_deriv'
    (a := a) (b := b) (f := path) (f' := path')
    (g := weightedAbelCoefficient phi z)
    (fun t _ht => hpath t) hpath' hcoeff
  have hpathA : path a = (A : ℝ) := by
    dsimp [path, a, realLogCoordinate]
    have hlogz0 : Real.log z ≠ 0 := ne_of_gt hlogzpos
    rw [mul_div_cancel₀ _ hlogz0, Real.exp_log hApos]
  have hpathY : path b = (Y : ℝ) := by
    dsimp [path, b, realLogCoordinate]
    have hlogz0 : Real.log z ≠ 0 := ne_of_gt hlogzpos
    rw [mul_div_cancel₀ _ hlogz0, Real.exp_log hYpos]
  have hintegrand :
      (∫ t in a..b,
        (weightedAbelCoefficient phi z ∘ path) t * path' t) =
      ∫ t in a..b, phi t / t := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Icc a b := by
      simpa only [uIcc_of_le hab] using ht
    have haPos : 0 < a := by
      dsimp [a, realLogCoordinate]
      exact div_pos hlogApos hlogzpos
    have ht0 : t ≠ 0 := ne_of_gt (haPos.trans_le htIcc.1)
    have hlogz0 : Real.log z ≠ 0 := ne_of_gt hlogzpos
    dsimp [Function.comp_def, weightedAbelCoefficient, realLogCoordinate,
      path, path']
    rw [Real.log_exp, mul_div_cancel_left₀ t hlogz0]
    field_simp [ht0, hlogz0, Real.exp_ne_zero]
  rw [hintegrand, hpathA, hpathY] at hsubst
  simpa only [a, b] using hsubst.symm

private noncomputable def primeLogCoefficient (k : ℕ) : ℝ :=
  if k.Prime then Real.log (k : ℝ) else 0

private theorem sum_primeLogCoefficient_Icc (x : ℝ) :
    (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, primeLogCoefficient k) =
      Chebyshev.theta x := by
  rw [Chebyshev.theta_eq_sum_Icc]
  rw [Finset.sum_filter]
  rfl

/-- Exact Abel summation for a smooth logarithmic test function.  This is a
finite identity; the PNT enters only when the `theta` term is estimated. -/
theorem fullWeightedReciprocalSum_eq_abel
    (phi : ℝ → ℝ) (z : ℝ) (Y : ℕ) (hY : 2 ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ))) :
    fullWeightedReciprocalSum phi z Y =
      weightedAbelCoefficient phi z (Y : ℝ) * Chebyshev.theta (Y : ℝ) -
        ∫ x in (2 : ℝ)..Y,
          deriv (weightedAbelCoefficient phi z) x * Chebyshev.theta x := by
  let c : ℕ → ℝ := primeLogCoefficient
  have hc0 : c 0 = 0 := by simp [c, primeLogCoefficient]
  have hc1 : c 1 = 0 := by simp [c, primeLogCoefficient]
  have habel := sum_mul_eq_sub_integral_mul₁
    (f := weightedAbelCoefficient phi z) c hc0 hc1 (Y : ℝ) hdiff hint
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hY)] at habel
  rw [show (⌊(Y : ℝ)⌋₊ : ℕ) = Y by simp] at habel
  have hcumY : (∑ k ∈ Finset.Icc 0 Y, c k) =
      Chebyshev.theta (Y : ℝ) := by
    simpa [c] using sum_primeLogCoefficient_Icc (Y : ℝ)
  have hcum : ∀ x : ℝ,
      (∑ k ∈ Finset.Icc 0 ⌊x⌋₊, c k) = Chebyshev.theta x := by
    intro x
    simpa [c] using sum_primeLogCoefficient_Icc x
  rw [hcumY] at habel
  simp_rw [hcum] at habel
  have hlhs :
      (∑ k ∈ Finset.Icc 0 Y,
        weightedAbelCoefficient phi z (k : ℝ) * c k) =
          fullWeightedReciprocalSum phi z Y := by
    rw [fullWeightedReciprocalSum, primesUpTo, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hkPrime : k.Prime
    · have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hkPrime.ne_zero
      have hlogk0 : Real.log (k : ℝ) ≠ 0 :=
        Real.log_ne_zero_of_pos_of_ne_one
          (by exact_mod_cast hkPrime.pos) (by exact_mod_cast hkPrime.ne_one)
      simp only [c, primeLogCoefficient, hkPrime, if_true,
        weightedAbelCoefficient]
      field_simp [hk0, hlogk0]
    · simp [c, primeLogCoefficient, hkPrime]
  rw [hlhs] at habel
  linarith

/-- Exact two-endpoint Abel formula on `(A,Y]`. -/
theorem fullWeightedReciprocalSum_interval_eq_abel
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ)))
    (hThetaInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ)) :
    fullWeightedReciprocalSum phi z Y -
        fullWeightedReciprocalSum phi z A =
      weightedAbelCoefficient phi z (Y : ℝ) * Chebyshev.theta (Y : ℝ) -
        weightedAbelCoefficient phi z (A : ℝ) * Chebyshev.theta (A : ℝ) -
        ∫ x in (A : ℝ)..Y,
          deriv (weightedAbelCoefficient phi z) x * Chebyshev.theta x := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
  have hdiffA : ∀ x ∈ Icc (2 : ℝ) (A : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x := by
    intro x hx
    exact hdiff x ⟨hx.1, hx.2.trans hAYR⟩
  have hintA : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (A : ℝ)) :=
    hint.mono_set (Icc_subset_Icc_right hAYR)
  rw [fullWeightedReciprocalSum_eq_abel phi z Y hY hdiff hint,
    fullWeightedReciprocalSum_eq_abel phi z A hA hdiffA hintA]
  have hleft : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (2 : ℝ) (A : ℝ) := by
    apply hThetaInt.mono_set
    rw [uIcc_of_le hAR, uIcc_of_le h2Y]
    intro x hx
    exact ⟨hx.1, hx.2.trans hAYR⟩
  have hright : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (A : ℝ) (Y : ℝ) := by
    apply hThetaInt.mono_set
    rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hadd := intervalIntegral.integral_add_adjacent_intervals hleft hright
  linarith

/-- The continuum term obtained by replacing `theta(x)` with `x` in the
weighted Abel formula. -/
def weightedAbelMain (phi : ℝ → ℝ) (z : ℝ) (A Y : ℝ) : ℝ :=
  weightedAbelCoefficient phi z Y * Y -
    weightedAbelCoefficient phi z A * A -
      ∫ x in A..Y, deriv (weightedAbelCoefficient phi z) x * x

/-- Exact PNT remainder in the weighted Abel formula. -/
def weightedAbelRemainder (phi : ℝ → ℝ) (z : ℝ) (A Y : ℝ) : ℝ :=
  weightedAbelCoefficient phi z Y * thetaError Y -
    weightedAbelCoefficient phi z A * thetaError A -
      ∫ x in A..Y,
        deriv (weightedAbelCoefficient phi z) x * thetaError x

/-- The Abel main term is exactly the integral of the coefficient.  This is
the integration-by-parts step before changing from `x` to logarithmic prime
coordinates. -/
theorem weightedAbelMain_eq_integral_coefficient
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ))) :
    weightedAbelMain phi z (A : ℝ) (Y : ℝ) =
      ∫ x in (A : ℝ)..Y, weightedAbelCoefficient phi z x := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hderivInt : IntervalIntegrable
      (deriv (weightedAbelCoefficient phi z)) volume (A : ℝ) (Y : ℝ) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hAYR]
    apply hint.mono_set
    exact Icc_subset_Icc hAR le_rfl
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (A : ℝ)) (b := (Y : ℝ))
    (u := id) (v := weightedAbelCoefficient phi z)
    (u' := fun _x : ℝ => 1)
    (v' := deriv (weightedAbelCoefficient phi z))
    (fun x _hx => hasDerivAt_id x)
    (fun x hx => by
      have hx' : x ∈ Icc (A : ℝ) (Y : ℝ) := by
        simpa only [uIcc_of_le hAYR] using hx
      exact (hdiff x ⟨hAR.trans hx'.1, hx'.2⟩).hasDerivAt)
    (continuous_const.intervalIntegrable _ _)
    hderivInt
  unfold weightedAbelMain
  have hone : (∫ x in (A : ℝ)..Y,
      (1 : ℝ) * weightedAbelCoefficient phi z x) =
      ∫ x in (A : ℝ)..Y, weightedAbelCoefficient phi z x := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hone] at hibp
  have hcomm : (∫ x in (A : ℝ)..Y,
      x * deriv (weightedAbelCoefficient phi z) x) =
      ∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x * x := by
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  simp only [id_eq] at hibp
  rw [hcomm] at hibp
  linarith

/-- The continuum Abel main term in the paper's logarithmic coordinate. -/
theorem weightedAbelMain_eq_logCoordinateIntegral
    (phi : ℝ → ℝ) (hphi : Continuous phi) {z : ℝ} (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ))) :
    weightedAbelMain phi z (A : ℝ) (Y : ℝ) =
      ∫ t in realLogCoordinate z (A : ℝ)..realLogCoordinate z (Y : ℝ),
        phi t / t := by
  rw [weightedAbelMain_eq_integral_coefficient phi z hA hAY hdiff hint]
  exact integral_weightedAbelCoefficient_eq_logCoordinate phi hphi hz hA hAY

/-- Exact decomposition of the actual weighted prime sum into its continuum
Abel term and a literal PNT remainder. -/
theorem fullWeightedReciprocalSum_interval_sub_main_eq_remainder
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient phi z) x)
    (hint : IntegrableOn (deriv (weightedAbelCoefficient phi z))
      (Icc (2 : ℝ) (Y : ℝ)))
    (hThetaInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
        Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ))
    (hMainInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x * x)
      volume (A : ℝ) (Y : ℝ))
    (hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ)) :
    fullWeightedReciprocalSum phi z Y -
        fullWeightedReciprocalSum phi z A -
          weightedAbelMain phi z (A : ℝ) (Y : ℝ) =
      weightedAbelRemainder phi z (A : ℝ) (Y : ℝ) := by
  rw [fullWeightedReciprocalSum_interval_eq_abel phi z hA hAY
    hdiff hint hThetaInt]
  unfold weightedAbelMain weightedAbelRemainder thetaError
  have hsplit :
      (∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x * Chebyshev.theta x) =
      (∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x * x) +
      ∫ x in (A : ℝ)..Y,
        deriv (weightedAbelCoefficient phi z) x *
          (Chebyshev.theta x - x) := by
    have hErrorInt' : IntervalIntegrable
        (fun x : ℝ => deriv (weightedAbelCoefficient phi z) x *
          (Chebyshev.theta x - x)) volume (A : ℝ) (Y : ℝ) := by
      simpa only [thetaError] using hErrorInt
    rw [← intervalIntegral.integral_add hMainInt hErrorInt']
    apply intervalIntegral.integral_congr
    intro x hx
    ring
  rw [hsplit]
  ring

/-- Triangle-inequality form of the exact weighted PNT remainder. -/
theorem abs_weightedAbelRemainder_le
    (phi : ℝ → ℝ) (z : ℝ) {A Y : ℝ} (hAY : A ≤ Y) :
    |weightedAbelRemainder phi z A Y| ≤
      |weightedAbelCoefficient phi z Y| * |thetaError Y| +
        |weightedAbelCoefficient phi z A| * |thetaError A| +
        ∫ x in A..Y,
          |deriv (weightedAbelCoefficient phi z) x * thetaError x| := by
  unfold weightedAbelRemainder
  calc
    |weightedAbelCoefficient phi z Y * thetaError Y -
        weightedAbelCoefficient phi z A * thetaError A -
        ∫ x in A..Y,
          deriv (weightedAbelCoefficient phi z) x * thetaError x| ≤
      |weightedAbelCoefficient phi z Y * thetaError Y| +
        |weightedAbelCoefficient phi z A * thetaError A| +
        |∫ x in A..Y,
          deriv (weightedAbelCoefficient phi z) x * thetaError x| := by
            have h₁ := abs_sub
              (weightedAbelCoefficient phi z Y * thetaError Y)
              (weightedAbelCoefficient phi z A * thetaError A)
            have h₂ := abs_sub
              (weightedAbelCoefficient phi z Y * thetaError Y -
                weightedAbelCoefficient phi z A * thetaError A)
              (∫ x in A..Y,
                deriv (weightedAbelCoefficient phi z) x * thetaError x)
            linarith
    _ ≤ |weightedAbelCoefficient phi z Y| * |thetaError Y| +
        |weightedAbelCoefficient phi z A| * |thetaError A| +
        ∫ x in A..Y,
          |deriv (weightedAbelCoefficient phi z) x * thetaError x| := by
      rw [abs_mul, abs_mul]
      exact add_le_add_right
        (intervalIntegral.abs_integral_le_integral_abs hAY) _

/-- Exact one-index prime-cell quadrature for the actual
Poisson--Dickman kernel.  The right side is the literal PNT remainder; no
asymptotic estimate or probability input is assumed. -/
theorem kernel_primeCell_sub_continuum_eq_remainder
    {s z : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    fullWeightedReciprocalSum (covarianceKernel s) z Y -
        fullWeightedReciprocalSum (covarianceKernel s) z A -
        (∫ t in realLogCoordinate z (A : ℝ)..
          realLogCoordinate z (Y : ℝ), covarianceKernel s t / t) =
      weightedAbelRemainder (covarianceKernel s) z (A : ℝ) (Y : ℝ) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := hAR.trans hAYR
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ
        (weightedAbelCoefficient (covarianceKernel s) z) x := by
    intro x hx
    change DifferentiableAt ℝ (kernelWeightedAbelCoefficient s z) x
    exact (hasDerivAt_kernelWeightedAbelCoefficient hs hz
      (by linarith [hx.1]) (hx.2.trans hYz)).differentiableAt
  have hint : IntegrableOn
      (deriv (weightedAbelCoefficient (covarianceKernel s) z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
    simpa only [kernelWeightedAbelCoefficient] using
      integrableOn_deriv_kernelWeightedAbelCoefficient hs hz hYz
  have hThetaInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
          Chebyshev.theta x) volume (2 : ℝ) (Y : ℝ) := by
    simpa only [kernelWeightedAbelCoefficient] using
      intervalIntegrable_deriv_kernelWeighted_mul_theta hs hz hY hYz
  have hMainInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (covarianceKernel s) z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
    simpa only [kernelWeightedAbelCoefficient] using
      intervalIntegrable_deriv_kernelWeighted_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ =>
        deriv (weightedAbelCoefficient (covarianceKernel s) z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hThetaCell : IntervalIntegrable
        (fun x : ℝ =>
          deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
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
      (covarianceKernel s) z hA hAY hdiff hint hThetaInt hMainInt hErrorInt
  rw [weightedAbelMain_eq_logCoordinateIntegral
    (covarianceKernel s) (continuous_covarianceKernel_left s)
    hz hA hAY hdiff hint] at hdecomp
  exact hdecomp

/-- Uniform quantitative bound for the literal PNT remainder in one kernel
cell.  All constants are independent of the first kernel coordinate and of
the moving endpoints. -/
theorem abs_kernelWeightedAbelRemainder_le
    {C M s z : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hs : s ∈ Icc (0 : ℝ) 1) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hK : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |covarianceKernel u v| ≤ M ∧
      |covarianceKernelDerivativeSecondExtension u v| ≤ M)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelRemainder (covarianceKernel s) z (A : ℝ) (Y : ℝ)| ≤
      6 * (C * M) / Real.log (A : ℝ) ^ 3 := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hYpos : (0 : ℝ) < Y := by positivity
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by linarith
  have hlogYpos : 0 < Real.log (Y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Y by omega)
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos hAYR
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hThetaCell : IntervalIntegrable
      (fun x : ℝ =>
        deriv (kernelWeightedAbelCoefficient s z) x * Chebyshev.theta x)
      volume (A : ℝ) (Y : ℝ) := by
    have hfull := intervalIntegrable_deriv_kernelWeighted_mul_theta
      hs hz hY hYz
    apply hfull.mono_set
    rw [uIcc_of_le hAYR]
    have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    rw [uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hMainInt : IntervalIntegrable
      (fun x : ℝ => deriv (kernelWeightedAbelCoefficient s z) x * x)
      volume (A : ℝ) (Y : ℝ) :=
    intervalIntegrable_deriv_kernelWeighted_mul_id hs hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (kernelWeightedAbelCoefficient s z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hmajorInt : IntervalIntegrable (mertensErrorMajorant (2 * C * M))
      volume (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc (hAYR)
      (continuousOn_mertensErrorMajorant (2 * C * M)
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have hIntBound :
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
            thetaError x|) ≤
        2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
    have habsInt : IntervalIntegrable
        (fun x : ℝ =>
          |deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
            thetaError x|) volume (A : ℝ) (Y : ℝ) := by
      simpa only [kernelWeightedAbelCoefficient] using hErrorInt.abs
    calc
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
            thetaError x|) ≤
          ∫ x in (A : ℝ)..Y, mertensErrorMajorant (2 * C * M) x := by
        exact intervalIntegral.integral_mono_on hAYR habsInt hmajorInt
          (fun x hx => by
            have hx2 : 2 ≤ x := hAR.trans hx.1
            have hxz : x ≤ z := hx.2.trans hYz
            rw [show deriv
                (weightedAbelCoefficient (covarianceKernel s) z) x =
                  kernelWeightedAbelDerivative s z x by
              simpa only [kernelWeightedAbelCoefficient] using
                deriv_kernelWeightedAbelCoefficient hs hz (by linarith) hxz]
            exact abs_kernelWeightedAbelDerivative_mul_thetaError_le
              hC hM hs hz hx2 hxz hK (hTheta x hx))
      _ = mertensErrorPrimitive (2 * C * M) (Y : ℝ) -
          mertensErrorPrimitive (2 * C * M) (A : ℝ) :=
        integral_mertensErrorMajorant (2 * C * M) hAR hAYR
      _ ≤ 2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg :
            0 ≤ 2 * (C * M) / Real.log (Y : ℝ) ^ 3 := by positivity
        have heq :
            -(2 * C * M) / Real.log (Y : ℝ) ^ 3 -
                (-(2 * C * M) / Real.log (A : ℝ) ^ 3) =
              2 * (C * M) / Real.log (A : ℝ) ^ 3 -
                2 * (C * M) / Real.log (Y : ℝ) ^ 3 := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  have hAterm :
      |weightedAbelCoefficient (covarianceKernel s) z (A : ℝ)| *
          |thetaError (A : ℝ)| ≤
        C * M / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    exact abs_kernelWeightedAbelCoefficient_mul_thetaError_le hM hs hz hAR
      (hAYR.trans hYz) (fun u hu v hv => (hK u hu v hv).1)
      (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩)
  have hYterm :
      |weightedAbelCoefficient (covarianceKernel s) z (Y : ℝ)| *
          |thetaError (Y : ℝ)| ≤
        C * M / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    calc
      |kernelWeightedAbelCoefficient s z (Y : ℝ) * thetaError (Y : ℝ)| ≤
          C * M / Real.log (Y : ℝ) ^ 4 := by
        exact abs_kernelWeightedAbelCoefficient_mul_thetaError_le hM hs hz
          (by exact_mod_cast hY) hYz
          (fun u hu v hv => (hK u hu v hv).1)
          (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩)
      _ ≤ C * M / Real.log (A : ℝ) ^ 4 := by gcongr
  have hinv4 :
      C * M / Real.log (A : ℝ) ^ 4 ≤
        2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
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
      C * M / Real.log (A : ℝ) ^ 4 =
          (C * M) * (1 / Real.log (A : ℝ) ^ 4) := by ring
      _ ≤ (C * M) * (2 / Real.log (A : ℝ) ^ 3) :=
        mul_le_mul_of_nonneg_left hinv hCM
      _ = 2 * (C * M) / Real.log (A : ℝ) ^ 3 := by ring
  calc
    |weightedAbelRemainder (covarianceKernel s) z (A : ℝ) (Y : ℝ)| ≤
        |weightedAbelCoefficient (covarianceKernel s) z (Y : ℝ)| *
            |thetaError (Y : ℝ)| +
          |weightedAbelCoefficient (covarianceKernel s) z (A : ℝ)| *
            |thetaError (A : ℝ)| +
          ∫ x in (A : ℝ)..Y,
            |deriv (weightedAbelCoefficient (covarianceKernel s) z) x *
              thetaError x| :=
      abs_weightedAbelRemainder_le (covarianceKernel s) z hAYR
    _ ≤ C * M / Real.log (A : ℝ) ^ 4 +
        C * M / Real.log (A : ℝ) ^ 4 +
        2 * (C * M) / Real.log (A : ℝ) ^ 3 := by linarith
    _ ≤ 6 * (C * M) / Real.log (A : ℝ) ^ 3 := by
      calc
        C * M / Real.log (A : ℝ) ^ 4 +
              C * M / Real.log (A : ℝ) ^ 4 +
              2 * (C * M) / Real.log (A : ℝ) ^ 3 ≤
            2 * (C * M) / Real.log (A : ℝ) ^ 3 +
              2 * (C * M) / Real.log (A : ℝ) ^ 3 +
              2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
          exact add_le_add (add_le_add hinv4 hinv4) (le_refl _)
        _ = 6 * (C * M) / Real.log (A : ℝ) ^ 3 := by ring

/-- Unconditional one-index kernel quadrature on every positive moving
prime cell.  A single constant and threshold work simultaneously for all
kernel coordinates, all later cell endpoints, and all ambient scales `z`.
This is the quantitative positive-cell input needed by the two-index
operator transfer. -/
theorem exists_uniform_kernel_primeCell_error_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ s ∈ Icc (0 : ℝ) 1, ∀ z : ℝ, 1 < z →
      ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        |fullWeightedReciprocalSum (covarianceKernel s) z Y -
            fullWeightedReciprocalSum (covarianceKernel s) z A -
            (∫ t in realLogCoordinate z (A : ℝ)..
              realLogCoordinate z (Y : ℝ), covarianceKernel s t / t)| ≤
          D / Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨M, hM, hK⟩ := exists_covarianceKernel_uniform_C1_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨6 * (C * M), by positivity, max N 2, ?_⟩
  intro s hs z hz A Y hA hAY hYz
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  rw [kernel_primeCell_sub_continuum_eq_remainder hs hz hA2 hAY hYz]
  apply abs_kernelWeightedAbelRemainder_le hC.le hM.le hs hz hA2 hAY hYz hK
  intro x hx
  apply hTheta x
  exact le_trans (le_of_lt hX₀N) (hNAR.trans hx.1)

end Erdos390.Full.KernelPrimeQuadrature
