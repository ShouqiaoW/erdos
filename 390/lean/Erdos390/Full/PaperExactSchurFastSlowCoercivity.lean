import Erdos390.Full.PaperMainFastSlowCoordinates

/-!
# Closed finite fast/slow coercivity connector

The actual band inverse, the compensated slow variance, and the proved
first-stage regression bound now imply the literal augmented main Schur gap.
No Schur coercivity or coordinate-comparison conclusion remains as a
hypothesis.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

theorem exactSchurGap_of_fastSlow_of_regressionBound
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Creg : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgammaNuisance hGamma e) ≤
      Creg * B.w) :
    ∀ u,
      (min gammaFast gammaSlow /
        (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))) * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)) := by
  have hCcoord : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hA := B.gaugeCenterSquareSum_nonneg
    have hC2 : 0 ≤ Creg ^ 2 := sq_nonneg _
    positivity
  apply B.exactSchurGap_of_fastSlow
    xi hgammaNuisance hGamma e he hgammaFast hgammaSlow hCcoord
    hfast hslow
  intro u qFast lambda hq hstored
  exact B.main_norm_sq_le_fastSharp_add_storedSlow
    u qFast (B.actualBandRegression xi hgammaNuisance hGamma e)
      lambda Creg hCreg hreg hq hstored

/-- Full finite covariance gap obtained from the two closed Schur blocks.
This is the actual finite baseline gap which can subsequently be transferred
to a preselected effective tilt box by bounded-density domination. -/
theorem hasCovarianceGap_of_fastSlow_of_regressionBound
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q,
      e q = B.actualBandSchurLinearMap
        xi hgammaNuisance hGamma q)
    {gammaFast gammaSlow Creg : ℝ}
    (hgammaFast : 0 < gammaFast)
    (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg)
    (hfast : ∀ q,
      gammaFast *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) q ^ 2 ≤
        (B.tiltedLaw xi).covariance
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q))
          (B.nuisanceResidualScore xi hgammaNuisance hGamma
            (B.bandRegressionScore q)))
    (hslow : gammaSlow * B.w ^ 2 ≤
      (B.tiltedLaw xi).covariance
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e))
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgammaNuisance hGamma e) ≤
      Creg * B.w) :
    B.vectorFamily.HasCovarianceGap
      (min
          (min gammaFast gammaSlow /
            (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2)))
          gammaNuisance /
        (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)) xi := by
  let gammaMain := min gammaFast gammaSlow /
    (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2))
  have hden : 0 <
      1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2) := by
    have hA := B.gaugeCenterSquareSum_nonneg
    have hC2 : 0 ≤ Creg ^ 2 := sq_nonneg _
    positivity
  have hgammaMain : 0 < gammaMain :=
    div_pos (lt_min hgammaFast hgammaSlow) hden
  have hSchur := B.exactSchurGap_of_fastSlow_of_regressionBound
    xi hgammaNuisance hGamma e he hgammaFast hgammaSlow
      hCreg hfast hslow hreg
  simpa only [gammaMain] using
    B.hasCovarianceGap_of_uniform_exactSchur
      xi gammaMain gammaNuisance hgammaMain hgammaNuisance hGamma hSchur

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
