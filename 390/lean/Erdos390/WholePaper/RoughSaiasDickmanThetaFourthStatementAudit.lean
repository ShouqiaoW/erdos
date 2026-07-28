import Erdos390.WholePaper.RoughSaiasDickmanThetaFourth

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

#check roughSaiasNaturalMinusDickmanThetaWeight
#check roughSaiasNaturalMinusDickmanThetaTransfer
#check roughSaiasDickmanThetaTransfer_abs_le_invLogSq
#check roughSaiasDickmanThetaTransfer_abs_le_invLogSq_fourthPower
#check roughSaiasNaturalThetaErrorTransfer_eq_dickman_add_residual
#check roughSaiasNaturalThetaErrorTransfer_abs_le_dickman_add_residual
#check roughSaiasReverseNormalFormDefect_abs_le_closedCore_add_residual

example {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasNaturalThetaErrorTransfer X y Z =
      (FriableAsymptotic.primeThetaWeightedInterval
          (FriableAsymptotic.dickmanThetaWeight X) y Z -
        FriableAsymptotic.integerAbelMain
          (FriableAsymptotic.dickmanThetaWeight X) y Z) +
      roughSaiasNaturalMinusDickmanThetaTransfer X y Z :=
  roughSaiasNaturalThetaErrorTransfer_eq_dickman_add_residual hyZ

example {X y Z : ℕ} (hX : 0 < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasNaturalMinusDickmanThetaTransfer X y Z| :=
  roughSaiasReverseNormalFormDefect_abs_le_closedCore_add_residual
    hX hY hy2 hyZ hZX hu5 hupper

end

end Erdos390.WholePaper
