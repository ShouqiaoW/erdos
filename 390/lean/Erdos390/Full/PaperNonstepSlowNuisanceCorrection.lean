import Erdos390.Full.PaperActualCenterNuisanceRow
import Erdos390.Full.PaperNonstepSlowRightLedger

/-!
# Nuisance correction for the literal non-step slow score

The source covariance vector is estimated from the exact primewise
coefficients `g_p = alpha_{j(p)} - t_p`.  Its natural size is therefore
`Cmarked * sum |g_p|/p`, with no band-centre surrogate and no least-centre
division.  This is the finite statement needed before the sharp
`alpha_0 -> 0` eventual conversion.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Relative moving-low rate for the literal slow-score nuisance
correction after `primeDeviationL1 <= CL1 * w` and `amin <= alpha_i`. -/
def nonstepSlowNuisanceRate
    (Cmarked gamma CL1 amin : ℝ) : ℝ :=
  ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      (Cmarked * CL1)) / gamma) *
    (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
      Cmarked) / amin

/-- Reciprocal marked-prime estimates control the nuisance covariance vector
of the literal non-step slow score by its exact global weighted `L¹` norm. -/
theorem nuisanceCovarianceVector_slowScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {Cmarked : ℝ} (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCovarianceVector xi B.slowScore‖ ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.primeDeviationL1) := by
  have hL1 : 0 ≤ B.primeDeviationL1 := by
    unfold primeDeviationL1
    exact Finset.sum_nonneg fun p _hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  apply B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
    xi B.slowScore (mul_nonneg hCmarked hL1)
  intro c
  have hsum :
      (B.tiltedLaw xi).covariance
          (fun m ↦ B.nuisanceStatistic m c) B.slowScore =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation p *
            (B.tiltedLaw xi).covariance
              (fun m ↦ B.nuisanceStatistic m c)
              (fun m ↦ ArithmeticModel.valuation p.1
                (B.sampleData.value m)) := by
    unfold slowScore
    rw [show (fun m ↦ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m)) =
      fun m ↦ ∑ p ∈
          (Finset.univ : Finset
            (BandPrime B.sampleData.n B.sampleData.W)),
        B.primeDeviation p *
          ArithmeticModel.valuation p.1 (B.sampleData.value m) by simp]
    rw [FiniteProbability.covariance_sum_right]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [FiniteProbability.covariance_smul_right]
  rw [hsum]
  calc
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p *
          (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c)
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| ≤
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.primeDeviation p *
          (B.tiltedLaw xi).covariance
            (fun m ↦ B.nuisanceStatistic m c)
            (fun m ↦ ArithmeticModel.valuation p.1
              (B.sampleData.value m))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.primeDeviation p| *
          (Cmarked * (1 / (p.1 : ℝ))) := by
      apply Finset.sum_le_sum
      intro p _hp
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hmarked c p) (abs_nonneg _)
    _ = Cmarked * B.primeDeviationL1 := by
      unfold primeDeviationL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- Coercivity converts the preceding source-row estimate into a bound for
the exact nuisance regression coefficient of the slow score. -/
theorem nuisanceCoefficient_slowScore_norm_le_of_marked
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ))) :
    ‖B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        (Cmarked * B.primeDeviationL1)) / gamma := by
  exact (B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _).trans
    (div_le_div_of_nonneg_right
      (B.nuisanceCovarianceVector_slowScore_norm_le_of_marked
        xi hCmarked hmarked) hgamma.le)

/-- Coordinatewise normalized Schur correction for the literal slow score.
The input contributes `sum |g_p|/p`; the output band mass cancels exactly. -/
theorem abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (i : Band) :
    |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
          (B.nuisanceStatistic m)) i| ≤
      ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * B.primeDeviationL1)) / gamma) *
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked) := by
  let a : B.NuisanceSpace :=
    B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore
  let droot : ℝ :=
    Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  have hL1 : 0 ≤ B.primeDeviationL1 := by
    unfold primeDeviationL1
    exact Finset.sum_nonneg fun p _hp ↦
      mul_nonneg (by positivity) (abs_nonneg _)
  have hdroot : 0 ≤ droot := Real.sqrt_nonneg _
  have hupperA : 0 ≤ (droot * (Cmarked * B.primeDeviationL1)) / gamma :=
    div_nonneg (mul_nonneg hdroot (mul_nonneg hCmarked hL1)) hgamma.le
  have ha : ‖a‖ ≤
      (droot * (Cmarked * B.primeDeviationL1)) / gamma := by
    simpa only [a, droot] using
      B.nuisanceCoefficient_slowScore_norm_le_of_marked
        xi hgamma hgap hCmarked hmarked
  have hrow :
      ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖ ≤
        (droot * Cmarked) * B.harmonicMass i := by
    have h := B.nuisanceCovarianceVector_bandScore_norm_le_of_marked
      xi i hCmarked hmarked
    simpa only [droot, mul_assoc] using h
  have hH : 0 < B.harmonicMass i := B.harmonicMass_pos i
  change |B.normalizedBandCovarianceRow xi
    (fun m ↦ inner ℝ a (B.nuisanceStatistic m)) i| ≤ _
  unfold normalizedBandCovarianceRow
  rw [B.covariance_marked_nuisanceScore_eq_inner,
    abs_div, abs_of_pos hH]
  calc
    |inner ℝ a (B.nuisanceCovarianceVector xi (B.bandScore i))| /
          B.harmonicMass i ≤
        (‖a‖ * ‖B.nuisanceCovarianceVector xi (B.bandScore i)‖) /
          B.harmonicMass i :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hH.le
    _ ≤ (((droot * (Cmarked * B.primeDeviationL1)) / gamma) *
          ((droot * Cmarked) * B.harmonicMass i)) /
          B.harmonicMass i := by
      apply div_le_div_of_nonneg_right _ hH.le
      exact mul_le_mul ha hrow (norm_nonneg _) hupperA
    _ = ((droot * (Cmarked * B.primeDeviationL1)) / gamma) *
        (droot * Cmarked) := by
      field_simp [hH.ne']

/-- Paper-scale relative form of the literal slow nuisance correction. -/
theorem abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le_rate
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked CL1 w amin : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked) (hCL1 : 0 ≤ CL1) (hw : 0 ≤ w)
    (hamin : 0 < amin)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (hL1 : B.primeDeviationL1 ≤ CL1 * w)
    (hcenter : ∀ i : Band, amin ≤ B.bandCenter i)
    (i : Band) :
    |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
          (B.nuisanceStatistic m)) i| ≤
      B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin *
        w * B.bandCenter i := by
  have hraw :=
    B.abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le
      xi hgamma hgap hCmarked hmarked i
  have hdroot : 0 ≤
      Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sqrt_nonneg _
  have hgamma0 : 0 ≤ gamma := hgamma.le
  have hamin0 : 0 ≤ amin := hamin.le
  have hcenter0 : 0 ≤ B.bandCenter i := (B.bandCenter_pos i).le
  calc
    |B.normalizedBandCovarianceRow xi
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap B.slowScore)
          (B.nuisanceStatistic m)) i| ≤
      ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * B.primeDeviationL1)) / gamma) *
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked) := hraw
    _ ≤ ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (Cmarked * (CL1 * w))) / gamma) *
        (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          Cmarked) := by
      gcongr
    _ = (B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin * w) *
          amin := by
      unfold nonstepSlowNuisanceRate
      field_simp [hgamma.ne', hamin.ne']
    _ ≤ (B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin * w) *
          B.bandCenter i := by
      have hrate0 : 0 ≤
          B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin := by
        unfold nonstepSlowNuisanceRate
        positivity
      exact mul_le_mul_of_nonneg_left (hcenter i)
        (mul_nonneg hrate0 hw)
    _ = B.nonstepSlowNuisanceRate Cmarked gamma CL1 amin *
          w * B.bandCenter i := by ring

/-- Exact residual-row triangle using the literal raw slow row and the
literal slow-score nuisance correction. -/
theorem abs_normalizedBandCovarianceRow_nuisanceResidual_slow_le_of_raw
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma Cmarked R : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hCmarked : 0 ≤ Cmarked)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ ArithmeticModel.valuation p.1
          (B.sampleData.value m))| ≤
        Cmarked * (1 / (p.1 : ℝ)))
    (i : Band)
    (hraw : |B.normalizedBandCovarianceRow xi B.slowScore i| ≤ R) :
    |B.normalizedBandCovarianceRow xi
        (B.nuisanceResidualScore xi hgamma hgap B.slowScore) i| ≤
      R +
        ((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            (Cmarked * B.primeDeviationL1)) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked) := by
  unfold nuisanceResidualScore
  rw [B.normalizedBandCovarianceRow_sub]
  exact (abs_sub _ _).trans (add_le_add hraw
    (B.abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le
      xi hgamma hgap hCmarked hmarked i))

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
