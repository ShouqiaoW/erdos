import Erdos390.Full.DoubleKernelPrimeQuadrature

/-!
# Prime quadrature for the Poisson--Dickman diagonal multiplier

The compressed operator in Lemma 8.4 contains the multiplier `F(t)` in
addition to the double kernel.  This file proves its actual prime-cell
quadrature independently, including the normalization used on the moving
low output row.
-/

open Set

noncomputable section

namespace Erdos390.Full.DiagonalPrimeQuadrature

open MeasureTheory
open PrimeSums PrimeBandQuadrature
open DickmanBasic ConditionedPoissonLimit
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open PositiveCellTransfer

/-- Actual diagonal prime-cell numerator. -/
def diagonalPrimeCell (z : ℝ) (A Y : ℕ) : ℝ :=
  primeCellOperator z A Y F

/-- Continuum diagonal cell numerator. -/
def diagonalContinuumCell (z : ℝ) (A Y : ℕ) : ℝ :=
  continuumCellOperator z A Y F

/-- Explicit derivative of the diagonal Abel coefficient. -/
def diagonalWeightedAbelDerivative (z x : ℝ) : ℝ :=
  weightedAbelCoefficientDerivative F derivFExtension z x

lemma hasDerivAt_diagonalWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    HasDerivAt (weightedAbelCoefficient F z)
      (diagonalWeightedAbelDerivative z x) x := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have ht₂ : realLogCoordinate z x ∈ Icc (0 : ℝ) 2 :=
    ⟨ht.1, ht.2.trans (by norm_num)⟩
  have hF : HasDerivAt F
      (derivFExtension (realLogCoordinate z x)) (realLogCoordinate z x) := by
    exact (differentiableAt_F ht₂).hasDerivAt.congr_deriv
      (derivFExtension_eq_deriv_of_mem ht₂).symm
  exact hasDerivAt_weightedAbelCoefficient F derivFExtension hz hx hF

lemma deriv_diagonalWeightedAbelCoefficient
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z) :
    deriv (weightedAbelCoefficient F z) x =
      diagonalWeightedAbelDerivative z x :=
  (hasDerivAt_diagonalWeightedAbelCoefficient hz hx hxz).deriv

lemma continuousAt_diagonalWeightedAbelDerivative
    {z x : ℝ} (hz : 1 < z) (hx : 1 < x) :
    ContinuousAt (diagonalWeightedAbelDerivative z) x := by
  exact continuousAt_weightedAbelCoefficientDerivative F derivFExtension
    continuous_F continuous_derivFExtension hz hx

lemma continuousOn_diagonalWeightedAbelDerivative
    {z A Y : ℝ} (hz : 1 < z) (hA : 1 < A) :
    ContinuousOn (diagonalWeightedAbelDerivative z) (Icc A Y) := by
  intro x hx
  exact (continuousAt_diagonalWeightedAbelDerivative hz
    (hA.trans_le hx.1)).continuousWithinAt

/-- One compact constant bounds the diagonal and its first derivative. -/
theorem exists_diagonal_uniform_C1_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M := by
  obtain ⟨M₀, hM₀⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_F.continuousOn
  obtain ⟨M₁, hM₁⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_derivFExtension.continuousOn
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hM₀nonneg : 0 ≤ M₀ :=
    (norm_nonneg (F 0)).trans (hM₀ 0 hzero)
  have hM₁nonneg : 0 ≤ M₁ :=
    (norm_nonneg (derivFExtension 0)).trans (hM₁ 0 hzero)
  refine ⟨1 + M₀ + M₁, by linarith, ?_⟩
  intro t ht
  constructor
  · have h := hM₀ t ht
    rw [Real.norm_eq_abs] at h
    linarith
  · have h := hM₁ t ht
    rw [Real.norm_eq_abs] at h
    linarith

lemma abs_diagonalWeightedAbelCoefficient_le
    {M z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ M) :
    |weightedAbelCoefficient F z x| ≤ M / (x * Real.log x) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hdenpos : 0 < x * Real.log x := mul_pos hxpos hlogxpos
  unfold weightedAbelCoefficient
  rw [abs_div, abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hF _ ht) hdenpos.le

lemma abs_diagonalWeightedAbelDerivative_le
    {M z x : ℝ} (hz : 1 < z) (hx : 1 < x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M) :
    |diagonalWeightedAbelDerivative z x| ≤
      M / (x ^ 2 * Real.log x * Real.log z) +
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
  have ht := realLogCoordinate_mem_unit hz hx.le hxz
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hlogxpos : 0 < Real.log x := Real.log_pos hx
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hden₁ : 0 < x ^ 2 * Real.log x * Real.log z := by positivity
  have hden₂ : 0 < x ^ 2 * Real.log x ^ 2 := by positivity
  have hplus : 0 ≤ Real.log x + 1 := by linarith
  unfold diagonalWeightedAbelDerivative weightedAbelCoefficientDerivative
  calc
    |derivFExtension (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z) -
        F (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| ≤
      |derivFExtension (realLogCoordinate z x) /
          (x ^ 2 * Real.log x * Real.log z)| +
        |F (realLogCoordinate z x) * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2)| := abs_sub _ _
    _ = |derivFExtension (realLogCoordinate z x)| /
          (x ^ 2 * Real.log x * Real.log z) +
        |F (realLogCoordinate z x)| * (Real.log x + 1) /
          (x ^ 2 * Real.log x ^ 2) := by
      rw [abs_div, abs_div]
      simp only [abs_mul]
      rw [abs_of_nonneg (sq_nonneg x), abs_of_pos hlogxpos,
        abs_of_pos hlogzpos, abs_of_nonneg hplus,
        abs_of_nonneg (sq_nonneg (Real.log x))]
    _ ≤ M / (x ^ 2 * Real.log x * Real.log z) +
        M * (Real.log x + 1) / (x ^ 2 * Real.log x ^ 2) := by
      apply add_le_add
      · exact div_le_div_of_nonneg_right (hF _ ht).2 hden₁.le
      · exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hF _ ht).1 hplus) hden₂.le

lemma abs_diagonalWeightedAbelCoefficient_mul_thetaError_le
    {C M z x : ℝ} (hM : 0 ≤ M) (hz : 1 < z)
    (hx : 2 ≤ x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ M)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelCoefficient F z x * thetaError x| ≤
      C * M / Real.log x ^ 4 := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hlogpos : 0 < Real.log x := Real.log_pos hx1
  have hcoeff := abs_diagonalWeightedAbelCoefficient_le hz hx1 hxz hF
  rw [abs_mul]
  calc
    |weightedAbelCoefficient F z x| * |thetaError x| ≤
        (M / (x * Real.log x)) * (C * x / Real.log x ^ 3) := by gcongr
    _ = C * M / Real.log x ^ 4 := by
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]

lemma abs_diagonalWeightedAbelDerivative_mul_thetaError_le
    {C M z x : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hz : 1 < z) (hx : 2 ≤ x) (hxz : x ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M)
    (hTheta : |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |diagonalWeightedAbelDerivative z x * thetaError x| ≤
      mertensErrorMajorant (2 * C * M) x := by
  have hx1 : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hloghalf : (1 / 2 : ℝ) ≤ Real.log x := by
    have hmono : Real.log 2 ≤ Real.log x :=
      Real.log_le_log (by norm_num) hx
    nlinarith [Real.log_two_gt_d9]
  have hlogpos : 0 < Real.log x := by linarith
  have hlogzpos : 0 < Real.log z := Real.log_pos hz
  have hlogxz : Real.log x ≤ Real.log z := Real.log_le_log hxpos hxz
  have hplus : Real.log x + 1 ≤ 3 * Real.log x := by linarith
  have hderiv := abs_diagonalWeightedAbelDerivative_le hz hx1 hxz hF
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
            M * (3 * Real.log x) / (x ^ 2 * Real.log x ^ 2) := by gcongr
        _ = 3 * M / (x ^ 2 * Real.log x) := by
          field_simp [ne_of_gt hlogpos]
    have hfirst' :
        M / (x ^ 2 * Real.log x ^ 2) ≤
          2 * M / (x ^ 2 * Real.log x) := by
      have hone : 1 ≤ 2 * Real.log x := by linarith
      apply (div_le_div_iff₀ hden₂ hden₃).2
      calc
        M * (x ^ 2 * Real.log x) ≤
            M * (x ^ 2 * Real.log x) * (2 * Real.log x) := by
          simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left hone (mul_nonneg hM hden₃.le))
        _ = 2 * M * (x ^ 2 * Real.log x ^ 2) := by ring
    calc
      _ ≤ M / (x ^ 2 * Real.log x ^ 2) +
          3 * M / (x ^ 2 * Real.log x) := add_le_add hfirst hsecond
      _ ≤ 2 * M / (x ^ 2 * Real.log x) +
          3 * M / (x ^ 2 * Real.log x) := add_le_add hfirst' (le_refl _)
      _ = 5 * M / (x ^ 2 * Real.log x) := by ring
  rw [abs_mul]
  calc
    |diagonalWeightedAbelDerivative z x| * |thetaError x| ≤
        (5 * M / (x ^ 2 * Real.log x)) *
          (C * x / Real.log x ^ 3) := by
      apply mul_le_mul
      · exact hderiv.trans hsimplified
      · exact hTheta
      · positivity
      · have := abs_nonneg (diagonalWeightedAbelDerivative z x)
        positivity
    _ ≤ mertensErrorMajorant (2 * C * M) x := by
      unfold mertensErrorMajorant
      have hCM : 0 ≤ C * M := mul_nonneg hC hM
      field_simp [ne_of_gt hxpos, ne_of_gt hlogpos]
      nlinarith

lemma integrableOn_deriv_diagonalWeightedAbelCoefficient
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hYz : (Y : ℝ) ≤ z) :
    IntegrableOn (deriv (weightedAbelCoefficient F z))
      (Icc (2 : ℝ) (Y : ℝ)) := by
  have hcont : ContinuousOn (diagonalWeightedAbelDerivative z)
      (Icc (2 : ℝ) (Y : ℝ)) :=
    continuousOn_diagonalWeightedAbelDerivative hz (by norm_num)
  apply (hcont.integrableOn_Icc).congr_fun
  · intro x hx
    symm
    exact deriv_diagonalWeightedAbelCoefficient hz
      (by linarith [hx.1]) (hx.2.trans hYz)
  · exact measurableSet_Icc

lemma intervalIntegrable_deriv_diagonal_mul_theta
    {z : ℝ} (hz : 1 < z) {Y : ℕ} (hY : 2 ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x)
      volume (2 : ℝ) (Y : ℝ) := by
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hbase := intervalIntegrable_continuous_mul_theta
    (g := diagonalWeightedAbelDerivative z) (A := (2 : ℝ))
    (Y := (Y : ℝ)) (by norm_num) h2Y
    (continuousOn_diagonalWeightedAbelDerivative hz (by norm_num))
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (2 : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le h2Y] using hx
  change diagonalWeightedAbelDerivative z x * Chebyshev.theta x =
    deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x
  congr 1
  exact (deriv_diagonalWeightedAbelCoefficient hz
    (by linarith [hx'.1]) (hx'.2.trans hYz)).symm

lemma intervalIntegrable_deriv_diagonal_mul_id
    {z : ℝ} (hz : 1 < z) {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y)
    (hYz : (Y : ℝ) ≤ z) :
    IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * x)
      volume (A : ℝ) (Y : ℝ) := by
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hcont : ContinuousOn
      (fun x : ℝ => diagonalWeightedAbelDerivative z x * x)
      (Icc (A : ℝ) (Y : ℝ)) :=
    (continuousOn_diagonalWeightedAbelDerivative hz (by linarith [hAR])).mul
      continuousOn_id
  have hbase := hcont.intervalIntegrable_of_Icc (μ := volume) hAYR
  apply hbase.congr
  intro x hx
  have hx' : x ∈ Ioc (A : ℝ) (Y : ℝ) := by
    simpa only [uIoc_of_le hAYR] using hx
  change diagonalWeightedAbelDerivative z x * x =
    deriv (weightedAbelCoefficient F z) x * x
  congr 1
  exact (deriv_diagonalWeightedAbelCoefficient hz
    (by linarith [hAR, hx'.1]) (hx'.2.trans hYz)).symm

/-- Exact actual diagonal cell minus continuum cell equals its literal PNT
remainder. -/
theorem diagonalPrimeCell_sub_continuum_eq_remainder
    {z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z) :
    diagonalPrimeCell z A Y - diagonalContinuumCell z A Y =
      weightedAbelRemainder F z (A : ℝ) (Y : ℝ) := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
  have hdiff : ∀ x ∈ Icc (2 : ℝ) (Y : ℝ),
      DifferentiableAt ℝ (weightedAbelCoefficient F z) x := by
    intro x hx
    exact (hasDerivAt_diagonalWeightedAbelCoefficient hz
      (by linarith [hx.1]) (hx.2.trans hYz)).differentiableAt
  have hint := integrableOn_deriv_diagonalWeightedAbelCoefficient hz hYz
  have hThetaInt := intervalIntegrable_deriv_diagonal_mul_theta hz hY hYz
  have hMainInt := intervalIntegrable_deriv_diagonal_mul_id hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hThetaCell : IntervalIntegrable
        (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x)
        volume (A : ℝ) (Y : ℝ) := by
      apply hThetaInt.mono_set
      rw [uIcc_of_le hAYR, uIcc_of_le h2Y]
      intro x hx
      exact ⟨hAR.trans hx.1, hx.2⟩
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hdecomp := fullWeightedReciprocalSum_interval_sub_main_eq_remainder
    F z hA hAY hdiff hint hThetaInt hMainInt hErrorInt
  rw [weightedAbelMain_eq_logCoordinateIntegral F continuous_F
    hz hA hAY hdiff hint] at hdecomp
  exact hdecomp

theorem abs_diagonalWeightedAbelRemainder_le
    {C M z : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M) (hz : 1 < z)
    {A Y : ℕ} (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1,
      |F t| ≤ M ∧ |derivFExtension t| ≤ M)
    (hTheta : ∀ x ∈ Icc (A : ℝ) (Y : ℝ),
      |thetaError x| ≤ C * x / Real.log x ^ 3) :
    |weightedAbelRemainder F z (A : ℝ) (Y : ℝ)| ≤
      6 * (C * M) / Real.log (A : ℝ) ^ 3 := by
  have hY : 2 ≤ Y := hA.trans hAY
  have hAR : (2 : ℝ) ≤ (A : ℝ) := by exact_mod_cast hA
  have hAYR : (A : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hAY
  have hApos : (0 : ℝ) < A := by positivity
  have hlogAhalf : (1 / 2 : ℝ) ≤ Real.log (A : ℝ) := by
    have hmono : Real.log 2 ≤ Real.log (A : ℝ) :=
      Real.log_le_log (by norm_num) hAR
    nlinarith [Real.log_two_gt_d9]
  have hlogApos : 0 < Real.log (A : ℝ) := by linarith
  have hlogYpos : 0 < Real.log (Y : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (show 1 < Y by omega)
  have hlogAY : Real.log (A : ℝ) ≤ Real.log (Y : ℝ) :=
    Real.log_le_log hApos (by exact_mod_cast hAY)
  have hCM : 0 ≤ C * M := mul_nonneg hC hM
  have hThetaCell : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * Chebyshev.theta x)
      volume (A : ℝ) (Y : ℝ) := by
    have hfull := intervalIntegrable_deriv_diagonal_mul_theta hz hY hYz
    apply hfull.mono_set
    rw [uIcc_of_le hAYR]
    have h2Y : (2 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY
    rw [uIcc_of_le h2Y]
    intro x hx
    exact ⟨hAR.trans hx.1, hx.2⟩
  have hMainInt := intervalIntegrable_deriv_diagonal_mul_id hz hA hAY hYz
  have hErrorInt : IntervalIntegrable
      (fun x : ℝ => deriv (weightedAbelCoefficient F z) x * thetaError x)
      volume (A : ℝ) (Y : ℝ) := by
    have hsub := hThetaCell.sub hMainInt
    apply hsub.congr
    intro x hx
    unfold thetaError
    ring
  have hmajorInt : IntervalIntegrable (mertensErrorMajorant (2 * C * M))
      volume (A : ℝ) (Y : ℝ) :=
    ContinuousOn.intervalIntegrable_of_Icc hAYR
      (continuousOn_mertensErrorMajorant (2 * C * M)
        (A := (A : ℝ)) (Y := (Y : ℝ)) (by linarith [hAR]))
  have hIntBound :
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient F z) x * thetaError x|) ≤
        2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
    calc
      (∫ x in (A : ℝ)..Y,
          |deriv (weightedAbelCoefficient F z) x * thetaError x|) ≤
          ∫ x in (A : ℝ)..Y, mertensErrorMajorant (2 * C * M) x := by
        exact intervalIntegral.integral_mono_on hAYR hErrorInt.abs hmajorInt
          (fun x hx => by
            have hx2 : 2 ≤ x := hAR.trans hx.1
            have hxz : x ≤ z := hx.2.trans hYz
            rw [deriv_diagonalWeightedAbelCoefficient hz (by linarith) hxz]
            exact abs_diagonalWeightedAbelDerivative_mul_thetaError_le
              hC hM hz hx2 hxz hF (hTheta x hx))
      _ = mertensErrorPrimitive (2 * C * M) (Y : ℝ) -
          mertensErrorPrimitive (2 * C * M) (A : ℝ) :=
        integral_mertensErrorMajorant (2 * C * M) hAR hAYR
      _ ≤ 2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
        unfold mertensErrorPrimitive
        have hnonneg : 0 ≤ 2 * (C * M) / Real.log (Y : ℝ) ^ 3 := by positivity
        have heq :
            -(2 * C * M) / Real.log (Y : ℝ) ^ 3 -
                (-(2 * C * M) / Real.log (A : ℝ) ^ 3) =
              2 * (C * M) / Real.log (A : ℝ) ^ 3 -
                2 * (C * M) / Real.log (Y : ℝ) ^ 3 := by ring
        rw [heq]
        exact sub_le_self _ hnonneg
  have hAterm :
      |weightedAbelCoefficient F z (A : ℝ)| * |thetaError (A : ℝ)| ≤
        C * M / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    exact abs_diagonalWeightedAbelCoefficient_mul_thetaError_le hM hz hAR
      ((show (A : ℝ) ≤ (Y : ℝ) by exact_mod_cast hAY).trans hYz)
      (fun t ht => (hF t ht).1) (hTheta (A : ℝ) ⟨le_rfl, hAYR⟩)
  have hYterm :
      |weightedAbelCoefficient F z (Y : ℝ)| * |thetaError (Y : ℝ)| ≤
        C * M / Real.log (A : ℝ) ^ 4 := by
    rw [← abs_mul]
    calc
      |weightedAbelCoefficient F z (Y : ℝ) * thetaError (Y : ℝ)| ≤
          C * M / Real.log (Y : ℝ) ^ 4 := by
        exact abs_diagonalWeightedAbelCoefficient_mul_thetaError_le hM hz
          (by exact_mod_cast hY) hYz (fun t ht => (hF t ht).1)
          (hTheta (Y : ℝ) ⟨hAYR, le_rfl⟩)
      _ ≤ C * M / Real.log (A : ℝ) ^ 4 := by gcongr
  have hinv4 : C * M / Real.log (A : ℝ) ^ 4 ≤
      2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
    have hone : 1 ≤ 2 * Real.log (A : ℝ) := by linarith
    have hmul := mul_le_mul_of_nonneg_right hone
      (pow_nonneg hlogApos.le 3)
    have hinv : 1 / Real.log (A : ℝ) ^ 4 ≤
        2 / Real.log (A : ℝ) ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hlogApos 4) (pow_pos hlogApos 3)).2
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
    |weightedAbelRemainder F z (A : ℝ) (Y : ℝ)| ≤
        |weightedAbelCoefficient F z (Y : ℝ)| * |thetaError (Y : ℝ)| +
          |weightedAbelCoefficient F z (A : ℝ)| * |thetaError (A : ℝ)| +
          ∫ x in (A : ℝ)..Y,
            |deriv (weightedAbelCoefficient F z) x * thetaError x| :=
      abs_weightedAbelRemainder_le F z hAYR
    _ ≤ C * M / Real.log (A : ℝ) ^ 4 +
        C * M / Real.log (A : ℝ) ^ 4 +
        2 * (C * M) / Real.log (A : ℝ) ^ 3 := by linarith
    _ ≤ 6 * (C * M) / Real.log (A : ℝ) ^ 3 := by
      calc
        _ ≤ 2 * (C * M) / Real.log (A : ℝ) ^ 3 +
            2 * (C * M) / Real.log (A : ℝ) ^ 3 +
            2 * (C * M) / Real.log (A : ℝ) ^ 3 := by
          exact add_le_add (add_le_add hinv4 hinv4) (le_refl _)
        _ = 6 * (C * M) / Real.log (A : ℝ) ^ 3 := by ring

/-- Unconditional diagonal prime-cell quadrature, uniform in all moving
positive endpoints. -/
theorem exists_uniform_diagonalPrimeCell_error_bound :
    ∃ D : ℝ, 0 < D ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
        X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        |diagonalPrimeCell z A Y - diagonalContinuumCell z A Y| ≤
          D / Real.log (A : ℝ) ^ 3 := by
  obtain ⟨C, hC, X₀R, hTheta⟩ := exists_thetaError_log_cube_bound
  obtain ⟨M, hM, hF⟩ := exists_diagonal_uniform_C1_bound
  obtain ⟨N, hX₀N⟩ := exists_nat_gt X₀R
  refine ⟨6 * (C * M), by positivity, max N 2, ?_⟩
  intro z hz A Y hA hAY hYz
  have hA2 : 2 ≤ A := (le_max_right N 2).trans hA
  have hNA : N ≤ A := (le_max_left N 2).trans hA
  have hNAR : (N : ℝ) ≤ (A : ℝ) := by exact_mod_cast hNA
  rw [diagonalPrimeCell_sub_continuum_eq_remainder hz hA2 hAY hYz]
  apply abs_diagonalWeightedAbelRemainder_le hC.le hM.le hz hA2 hAY hYz hF
  intro x hx
  apply hTheta x
  exact (le_of_lt hX₀N).trans (hNAR.trans hx.1)

def normalizedDiagonalPrimeCell (z : ℝ) (A Y : ℕ) : ℝ :=
  diagonalPrimeCell z A Y / actualCellMass A Y

def normalizedDiagonalContinuumCell (z : ℝ) (A Y : ℕ) : ℝ :=
  diagonalContinuumCell z A Y / continuumCellMass z A Y

lemma abs_diagonalContinuumCell_le_mass
    {M z : ℝ} (hz : 1 < z) {A Y : ℕ}
    (hA : 2 ≤ A) (hAY : A ≤ Y) (hYz : (Y : ℝ) ≤ z)
    (hF : ∀ t ∈ Icc (0 : ℝ) 1, |F t| ≤ M) :
    |diagonalContinuumCell z A Y| ≤ M * continuumCellMass z A Y := by
  have hint : IntervalIntegrable (fun t => F t / t) volume
      (realLogCoordinate z (A : ℝ)) (realLogCoordinate z (Y : ℝ)) :=
    intervalIntegrable_div_of_continuous continuous_F
      (realLogCoordinate_pos_nat hz hA)
      (realLogCoordinate_mono_nat hz hA hAY)
  unfold diagonalContinuumCell
  apply abs_continuumCellOperator_le z hz hA hAY F hint
  intro t ht
  exact hF t (coordinateCell_mem_unit hz hA hAY hYz ht)

theorem normalizedDiagonalCell_error_le
    {z : ℝ} {A Y : ℕ} {eNumerator eMass : ℝ}
    (hActualMass : 0 < actualCellMass A Y)
    (hContinuumMass : continuumCellMass z A Y ≠ 0)
    (hNumerator : |diagonalPrimeCell z A Y - diagonalContinuumCell z A Y| ≤
      eNumerator)
    (hMass : |actualCellMass A Y - continuumCellMass z A Y| ≤ eMass) :
    |normalizedDiagonalPrimeCell z A Y - normalizedDiagonalContinuumCell z A Y| ≤
      eNumerator / actualCellMass A Y +
        |diagonalContinuumCell z A Y| * eMass /
          (actualCellMass A Y * |continuumCellMass z A Y|) := by
  unfold normalizedDiagonalPrimeCell normalizedDiagonalContinuumCell
  exact abs_div_sub_div_le hActualMass hContinuumMass hNumerator hMass

/-- Unconditional relative diagonal transfer on the moving low output row.
The actual and continuum masses remain explicit denominators; hence a fixed
lower-cutoff error is absorbed as those masses grow. -/
theorem exists_uniform_normalizedDiagonalCell_error_bound :
    ∃ M : ℝ, 0 < M ∧ ∃ DDiag : ℝ, 0 < DDiag ∧
    ∃ CMass : ℝ, 0 < CMass ∧ ∃ X₀ : ℕ,
      ∀ z : ℝ, 1 < z → ∀ A Y : ℕ,
        X₀ ≤ A → A ≤ Y → (Y : ℝ) ≤ z →
        0 < actualCellMass A Y → continuumCellMass z A Y ≠ 0 →
        |normalizedDiagonalPrimeCell z A Y -
            normalizedDiagonalContinuumCell z A Y| ≤
          (DDiag / Real.log (A : ℝ) ^ 3) / actualCellMass A Y +
            (M * continuumCellMass z A Y) *
              (5 * CMass / Real.log (A : ℝ) ^ 3) /
              (actualCellMass A Y * |continuumCellMass z A Y|) := by
  obtain ⟨M, hM, hF⟩ := exists_diagonal_uniform_C1_bound
  obtain ⟨DDiag, hDDiag, XDiag, hDiag⟩ :=
    exists_uniform_diagonalPrimeCell_error_bound
  obtain ⟨CMass, hCMass, XMass, hMass⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  refine ⟨M, hM, DDiag, hDDiag, CMass, hCMass,
    max (max XDiag XMass) 2, ?_⟩
  intro z hz A Y hA hAY hYz hActualMass hContinuumMass
  have hADiag : XDiag ≤ A :=
    (le_max_left XDiag XMass).trans
      ((le_max_left (max XDiag XMass) 2).trans hA)
  have hAMass : XMass ≤ A :=
    (le_max_right XDiag XMass).trans
      ((le_max_left (max XDiag XMass) 2).trans hA)
  have hAtwo : 2 ≤ A := (le_max_right (max XDiag XMass) 2).trans hA
  have hNum := hDiag z hz A Y hADiag hAY hYz
  have hMassRaw := hMass A Y hAMass hAY
  have hMassCoord :
      |actualCellMass A Y - continuumCellMass z A Y| ≤
        5 * CMass / Real.log (A : ℝ) ^ 3 := by
    unfold actualCellMass continuumCellMass
    rw [show Real.log (realLogCoordinate z (Y : ℝ)) -
        Real.log (realLogCoordinate z (A : ℝ)) =
      Real.log (Real.log (Y : ℝ)) - Real.log (Real.log (A : ℝ)) by
        simpa only [realLogCoordinate, logCoordinate] using
          log_logCoordinate_sub hz hAtwo hAY]
    exact hMassRaw
  have hCont := abs_diagonalContinuumCell_le_mass hz hAtwo hAY hYz
    (fun t ht => (hF t ht).1)
  have hratio := normalizedDiagonalCell_error_le hActualMass hContinuumMass
    hNum hMassCoord
  exact hratio.trans (add_le_add le_rfl
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCont
        (by positivity : 0 ≤ 5 * CMass / Real.log (A : ℝ) ^ 3))
      (mul_nonneg hActualMass.le (abs_nonneg _))))

end Erdos390.Full.DiagonalPrimeQuadrature
