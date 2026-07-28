import Erdos390.Full.PaperLemma86CommonConstants

/-!
# Expanded statement audit: common Lemma 8.6 coefficient constant

The complete type below verifies that `Ccmp` is selected before the bridge
data (and hence before its cutoff and tilt box) and that all three estimates
refer to the same literal `actualBandRegression ... e`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport

namespace BridgeData

theorem expanded_exists_paperLemma86CompensatedConstant
    (Creg : ℝ) (hCreg : 0 ≤ Creg) :
    ∃ Ccmp : ℝ, 0 < Ccmp ∧
      ∀ {Head Band : Type*} [Fintype Head] [DecidableEq Head]
        [Fintype Band] [DecidableEq Band]
        (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
        (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
        (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
          inner ℝ z (B.nuisanceCovarianceOperator xi z))
        (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
        (∀ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| ≤
              (1 + Creg) * B.w) →
        B.partition.compensatedL1
            (B.actualBandRegression xi hgamma hgap e) ≤
          slowL1Constant Creg paperLemma86BandTConstant * B.w →
        B.partition.compensatedL2Sq
            (B.actualBandRegression xi hgamma hgap e) ≤
          slowL2Constant Creg paperLemma86BandTConstant * B.w ^ 2 →
        (∀ p : BandPrime B.sampleData.n B.sampleData.W,
          |B.actualCompensatedCoefficient
            (B.actualBandRegression xi hgamma hgap e) p| ≤ Ccmp * B.w) ∧
        B.partition.compensatedL1
            (B.actualBandRegression xi hgamma hgap e) ≤ Ccmp * B.w ∧
        B.partition.compensatedL2Sq
            (B.actualBandRegression xi hgamma hgap e) ≤
          Ccmp * B.w ^ 2 :=
  exists_paperLemma86CompensatedConstant Creg hCreg

theorem expanded_lemma86_geometry_bounds_with_positive_varianceFactor
    {cMesh w gL1 V : ℝ} (hcMesh : 0 < cMesh)
    (hgL1 : gL1 ≤ 7 * w)
    (hVlower : w ^ 2 ≤ (456 / cMesh ^ 2) * V)
    (hVupper : V ≤ 4 * w ^ 2) :
    gL1 ≤ 7 * w ∧
      paperLemma86VarianceFactor cMesh * w ^ 2 ≤ V ∧
      V ≤ 4 * w ^ 2 :=
  lemma86_geometry_bounds_with_positive_varianceFactor
    hcMesh hgL1 hVlower hVupper

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
