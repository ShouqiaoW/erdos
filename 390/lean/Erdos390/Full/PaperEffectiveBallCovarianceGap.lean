import Erdos390.Full.FiniteTiltCovarianceDomination
import Erdos390.Full.PaperBridgeCellTiltDecomposition
import Erdos390.Full.PaperEffectiveScoreBound

/-!
# Passing a finite baseline covariance gap to the effective tilt box

This is a density-ratio argument, not a convergence-to-a-limiting-mixture
argument.  A gap proved for the actual finite baseline law survives on any
preselected effective box, with an explicit positive factor depending only
on the score envelope of that box.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact bounded-tilt transfer of the full covariance gap from the actual
finite baseline `xi = 0`. -/
theorem hasCovarianceGap_of_baseline_of_scaledScoreBound
    [Nonempty Head]
    {gamma K : ℝ} (hbase : B.vectorFamily.HasCovarianceGap gamma 0)
    (xi : B.ParamSpace)
    (hscore : ∀ m : B.sampleData.Sample,
      |B.scaledBridgeScore xi m| ≤ K) :
    B.vectorFamily.HasCovarianceGap
      (Real.exp (-2 * K) * gamma) xi := by
  intro x
  let F : B.sampleData.Sample → ℝ :=
    fun m ↦ inner ℝ x (B.statistic m)
  have hdom :=
    B.baselineSigmaProbability.exp_neg_two_mul_covariance_self_le_exponentialTilt
      F (B.scaledBridgeScore xi) K hscore
  have hbase' : gamma * ‖x‖ ^ 2 ≤
      B.baselineSigmaProbability.covariance F F := by
    have hx := hbase x
    rw [B.baselineSigmaProbability_eq_tiltedLaw_zero]
    simpa only [VectorExponentialFamily.tiltedMixture,
      PatternMixture.covarianceForm, PatternMixture.probability,
      VectorExponentialFamily.probabilityMass,
      FiniteExponentialFamily.tiltedProbability, F] using hx
  have hfactor : 0 ≤ Real.exp (-2 * K) := (Real.exp_pos _).le
  have hchain : Real.exp (-2 * K) * (gamma * ‖x‖ ^ 2) ≤
      ((B.baselineSigmaProbability).exponentialTilt
        (B.scaledBridgeScore xi)).covariance F F :=
    (mul_le_mul_of_nonneg_left hbase' hfactor).trans hdom
  rw [← B.tiltedLaw_eq_exponentialTilt_baseline] at hchain
  simpa only [VectorExponentialFamily.tiltedMixture,
    PatternMixture.covarianceForm, PatternMixture.probability,
    VectorExponentialFamily.probabilityMass,
    FiniteExponentialFamily.tiltedProbability, F, mul_assoc] using hchain

/-- Effective-box specialization.  The covariance constant is chosen after
the box radius and before solving the ODE, and remains strictly positive
regardless of how small the finite baseline gap is. -/
theorem hasCovarianceGap_on_effectiveSize_of_baseline
    [Nonempty Head]
    {gamma C a : ℝ}
    (hbase : B.vectorFamily.HasCovarianceGap gamma 0)
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a) :
    B.vectorFamily.HasCovarianceGap
      (Real.exp (-2 *
          ((PaperStatisticNorm.valuationLogCoefficient C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) * a)) * gamma) xi := by
  apply B.hasCovarianceGap_of_baseline_of_scaledScoreBound hbase xi
  intro m
  exact B.effectiveScoreBound_of_paperEffectiveSize
    hC hW hhi xi hxi m

/-- A full covariance gap restricts to the literal nuisance block with no
loss because the nuisance embedding is an isometry. -/
theorem nuisanceGap_of_fullCovarianceGap
    [Nonempty Head]
    {gamma : ℝ} (xi : B.ParamSpace)
    (hfull : B.vectorFamily.HasCovarianceGap gamma xi) :
    ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z) := by
  intro z
  have hz := hfull (B.nuisanceEmbed z)
  rw [B.norm_nuisanceEmbed] at hz
  rw [← B.inner_covarianceOperator_self,
    B.inner_nuisanceEmbed_covarianceOperator] at hz
  exact hz

/-- The same full gap controls the exact main Schur residual.  The residual
contains the main coordinate isometrically, so no inverse-regression norm is
needed for this direction. -/
theorem exactSchurGap_of_fullCovarianceGap
    [Nonempty Head]
    {gamma gammaNuisance : ℝ} (hgamma : 0 ≤ gamma)
    (xi : B.ParamSpace)
    (hfull : B.vectorFamily.HasCovarianceGap gamma xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    ∀ u, gamma * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)) := by
  intro u
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hresidualNorm : ‖u‖ ^ 2 ≤ ‖B.schurResidual R u‖ ^ 2 := by
    change ‖u‖ ^ 2 ≤ ‖B.combine u (-R u)‖ ^ 2
    rw [B.combine_norm_sq]
    exact le_add_of_nonneg_right (sq_nonneg ‖-R u‖)
  have hcov := hfull (B.schurResidual R u)
  rw [← B.inner_covarianceOperator_self] at hcov
  exact (mul_le_mul_of_nonneg_left hresidualNorm hgamma).trans hcov

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
