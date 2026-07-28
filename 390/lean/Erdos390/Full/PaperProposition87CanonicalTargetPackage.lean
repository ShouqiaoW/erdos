import Erdos390.Full.PaperProposition87SpeedRadius

/-!
# Canonical target package for Proposition 8.7

This file removes the target estimates from the eventual Proposition 8.7
call site.  The rough-stage hypothesis is the literal paper envelope
`HasTargetEnvelopes`.  The ordinary band target is controlled by the
arithmetic moment ratio (not by the vanishing low-cell centre), while the
slow coordinate uses the exact compensated compatibility bound.  The final
estimate records the factor `B.w` needed for a box radius chosen before the
ambient threshold.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport MovingLowGaugeTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- All target conclusions used in Proposition 8.7, derived from the exact
rough-stage envelopes and the two geometric estimates.  In particular,
none of the three displayed target bounds is an independent analytic
assumption. -/
theorem canonicalTwoStageTargetPackage_of_envelopes
    [Nonempty Head] [Nonempty Band]
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
  have htargetBand : ‖B.projectedNormalizedTargetBand Delta‖ ≤
      (1 + Rproj) * Ctarget :=
    B.projectedNormalizedTargetBand_norm_le_of_envelopes
      hCtarget hRproj Delta henv hRatio
  have htargetSlow :
      |B.mainPart (B.normalizedTarget Delta) MainCoord.slow| ≤ Ctarget :=
    B.abs_normalizedTarget_slow_le_of_envelopes Delta henv
  have htargetComp :=
    B.abs_compensatedNormalizedTarget_le_of_regression_ordinaryTarget
      xi hgamma hgap e Delta hCreg hreg htargetBand htargetSlow
  have hTband : 0 ≤ (1 + Rproj) * Ctarget := by positivity
  have hstage :=
    B.twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
      (Creg := Creg) (Tband := (1 + Rproj) * Ctarget)
      (Tslow := Ctarget) hCreg hTband hmoment
  exact ⟨htargetBand, htargetSlow, htargetComp, hstage⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
