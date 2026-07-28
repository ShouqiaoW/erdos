import Erdos390.Full.PaperProposition87MarkedTwoStage

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Expanded statement audit for the exact marked-row assembly used by
Proposition 8.7.  No component or vector-field row is hidden by an alias. -/
theorem audit_vectorField_markedRow_le_of_twoStage_rows
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q =
      B.actualBandSchurLinearMap xi hgammaNuisance hGamma q)
    (p : ℕ) {Vlower Tslow Cfast Cslow rho : ℝ}
    (hVlower : 0 < Vlower) (hTslow : 0 ≤ Tslow)
    (hvariance : Vlower ≤
      B.actualTwoStageCompensatedVariance
        xi hgammaNuisance hGamma e)
    (htarget : |B.compensatedNormalizedTarget
      xi hgammaNuisance hGamma e Delta| ≤ Tslow)
    (hfast :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.nuisanceResidualScore xi hgammaNuisance hGamma
          (B.bandRegressionScore
            (e.symm (B.projectedNormalizedTargetBand Delta))))| ≤
        Cfast * rho)
    (hcompensated :
      |(B.tiltedLaw xi).covariance (B.markedValuation p)
        (B.actualTwoStageCompensatedScore
          xi hgammaNuisance hGamma e)| ≤
        (Cslow * rho) * B.w) :
    |B.vectorFamily.scalarFamily.covariance
        (B.markedValuation p)
        (fun m ↦ B.vectorFamily.scalarFamily.score m
          (B.vectorFamily.vectorField (B.targetVector Delta) xi)) xi| ≤
      (Cfast + (Tslow / Vlower) * (Cslow * B.w)) * rho := by
  exact B.vectorField_markedRow_le_of_twoStage_rows
    xi Delta hgammaFull hFull hgammaNuisance hGamma e he p hVlower
      hTslow hvariance htarget hfast hcompensated

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
