import Erdos390.Full.PaperProposition87CanonicalFullGap

/-! Expanded statement audit for the exact full covariance-gap connector. -/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap
      xi hgammaNuisance hGamma q)
    {Cinv gammaSlow Creg : ℝ}
    (hCinv : 0 < Cinv) (hgammaSlow : 0 < gammaSlow)
    (hCreg : 0 ≤ Creg)
    (hinv : ∀ v,
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
        Cinv * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) v)
    (hslow : gammaSlow * B.w ^ 2 ≤
      B.actualTwoStageCompensatedVariance
        xi hgammaNuisance hGamma e)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one)
        (B.actualBandRegression xi hgammaNuisance hGamma e) ≤
      Creg * B.w) :
    0 < B.canonicalTwoStageFullGap
        Cinv gammaSlow Creg gammaNuisance ∧
      B.vectorFamily.HasCovarianceGap
        (B.canonicalTwoStageFullGap
          Cinv gammaSlow Creg gammaNuisance) xi := by
  exact B.hasCovarianceGap_of_sameMap_sharpInverse_and_slow
    xi hgammaNuisance hGamma e he hCinv hgammaSlow hCreg
      hinv hslow hreg

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
