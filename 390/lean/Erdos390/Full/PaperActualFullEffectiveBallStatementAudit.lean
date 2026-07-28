import Erdos390.Full.PaperActualFullEffectiveBall

open Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example (B : BridgeData Head Band) [Nonempty Head]
    (a : NNReal) {Cfull : ℝ}
    (hpoint : ∀ (xi : B.ParamSpace),
      (∀ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p| ≤ 3 * (a : ℝ)) →
      |xi MomentCoord.physical| ≤ 3 * (a : ℝ) →
      ∃ actualEquiv :
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
        (∀ q, actualEquiv q = B.actualFullProjectedCLM xi q) ∧
        ∀ v, ‖actualEquiv.symm v‖ ≤ Cfull * ‖v‖) :
    ∃ fullEquiv : ∀ (z : B.EffectiveParamSpace),
        z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
            SharpGaugeSpace B.partition.mass B.partition.center,
      (∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
        fullEquiv z hz q =
          B.actualFullProjectedCLM (B.effectiveParamEquiv z) q) ∧
      ∀ (z : B.EffectiveParamSpace)
          (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
        ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖ := by
  exact B.exists_actualFullProjectedEquiv_on_closedBall_of_box a hpoint

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
