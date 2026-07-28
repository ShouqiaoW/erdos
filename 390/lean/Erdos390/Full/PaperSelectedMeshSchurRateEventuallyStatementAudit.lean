import Erdos390.Full.PaperSelectedMeshSchurRateEventually

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BridgeData

open ArithmeticBandGeometry PaperWeightedInverseExport MovingLowGaugeTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example (B : BridgeData Head Band) :
    (∑ j : Band, B.harmonicMass j * B.bandCenter j) =
      PrimeSums.bandTReciprocalSum B.sampleData.n B.sampleData.W := by
  exact B.sum_harmonicMass_mul_bandCenter_eq_bandTReciprocalSum

example (epsilon : ℕ → ℝ)
    (hepsilonNonneg : ∀ n, 0 ≤ epsilon n)
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0)) :
    Tendsto epsilon atTop (nhds 0) := by
  exact tendsto_zero_of_nonneg_mul_logL_zero epsilon
    hepsilonNonneg hepsilonRate

example (epsilon : ℕ → ℝ) {droot momentBound gammaFloor centerScale : ℝ}
    (hepsilon : Tendsto epsilon atTop (nhds 0))
    (hepsilonRate : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n))
        atTop (nhds 0))
    (hgamma : 0 < gammaFloor) (hcenter : 0 < centerScale) :
    Tendsto
      (selectedMeshSchurRateMajorant epsilon droot momentBound
        gammaFloor centerScale) atTop (nhds 0) := by
  exact tendsto_selectedMeshSchurRateMajorant_zero epsilon
    hepsilon hepsilonRate hgamma hcenter

example {C rate : ℝ} (hC : 0 < C)
    (hhalf : C * (2 * rate) ≤ 1 / 2) :
    C / (1 - C * (2 * rate)) ≤ 2 * C := by
  exact schurInverseConstant_le_two_mul hC hhalf

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
