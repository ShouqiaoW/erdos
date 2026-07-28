import Erdos390.WholePaper.RoughSaiasNaturalThetaLedgerBound

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

#check roughSaiasNaturalThetaPNTVariationLedger
#check roughSaiasNaturalThetaPNTEndpointEnvelope
#check roughSaiasNaturalQuotientThetaWeight_abs_le_sixteen
#check roughSaiasNaturalThetaPNTLedger_le_endpoint_add_variation
#check roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le
#check roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
#check roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation
#check roughSaiasNaturalThetaErrorTransfer_abs_le_endpoint_add_variation_fourthPower
#check roughSaiasReverseNormalFormDefect_abs_le_cells_endpoint_variation

example {C : ℝ} {X y Z : ℕ} (hC : 0 ≤ C) (hy3 : 3 ≤ y)
    (hyZ : y < Z) :
    roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ) C X y Z ≤
      32 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
  roughSaiasNaturalThetaPNTEndpointEnvelope_fourth_le_invLogSq
    hC hy3 hyZ

example {X y Z : ℕ} (hX : 0 < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        roughSaiasNaturalThetaPNTEndpointEnvelope (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z +
        roughSaiasNaturalThetaPNTVariationLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z :=
  roughSaiasReverseNormalFormDefect_abs_le_cells_endpoint_variation
    hX hY hy2 hyZ hZX hu5 hupper

end

end Erdos390.WholePaper
