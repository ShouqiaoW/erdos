import Erdos390.Full.PaperNonstepSlowNuisanceCorrection

/-!
Expanded statement audit for the exact moving-low relative nuisance
correction.  The conclusion is rowwise relative to the literal arithmetic
centre, including when the lowest centre tends to zero.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

example [Nonempty Head]
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
  exact B.abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le_rate
    xi hgamma hgap hCmarked hCL1 hw hamin hmarked hL1 hcenter i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

#print Erdos390.Full.PaperBridgeFit.BridgeData.abs_normalizedBandCovarianceRow_slow_nuisanceCorrection_le_rate
