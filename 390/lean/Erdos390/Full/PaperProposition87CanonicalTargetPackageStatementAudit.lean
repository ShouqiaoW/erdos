import Erdos390.Full.PaperProposition87CanonicalTargetPackage

/-!
# Expanded statement audit for the Proposition 8.7 target package

The conjunction is expanded literally so that the ordinary target, slow
target, compensated target, and factor-`w` conclusions cannot be hidden by
an auxiliary structure.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example
    (B : BridgeData Head Band) [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (Delta : Band → ℝ)
    {Ctarget Rproj Creg K : ℝ}
    (hCtarget : 0 ≤ Ctarget) (hRproj : 0 ≤ Rproj)
    (hCreg : 0 ≤ Creg)
    (henv : B.HasTargetEnvelopes Ctarget Delta)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * sharpWeightTotal B.harmonicMass B.bandCenter)
    (hmoment : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤ K)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression xi hgamma hgap e) ≤ Creg * B.w) :
    ‖B.projectedNormalizedTargetBand Delta‖ ≤
        (1 + Rproj) * Ctarget ∧
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤
        Ctarget ∧
      |B.compensatedNormalizedTarget xi hgamma hgap e Delta| ≤
        B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg ((1 + Rproj) * Ctarget) Ctarget ∧
      B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg ((1 + Rproj) * Ctarget) Ctarget ≤
        B.w *
          (K * Creg * ((1 + Rproj) * Ctarget) + Ctarget) := by
  exact B.canonicalTwoStageTargetPackage_of_envelopes
    xi hgamma hgap e Delta hCtarget hRproj hCreg henv hRatio hmoment hreg

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
