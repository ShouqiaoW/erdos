import Erdos390.WholePaper.RoughSaiasCorrectionObstruction

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

#check roughSaiasDickmanBuchstabBlockRemainder
#check roughSaiasCanonicalCorrectionObstruction
#check roughSaiasDickmanBuchstabBlockRemainder_abs_le
#check roughSaiasReverseNormalFormDefect_self_eq_closedPieces_add_obstruction
#check roughSaiasReverseNormalFormDefect_self_abs_le_closed_add_riemann_add_obstruction

example {X y M : ℕ} (hX : 1 ≤ X) (hy2 : 2 ≤ y)
    (hyM : y ≤ M) (hMX : M ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasDickmanBuchstabBlockRemainder X y M| ≤
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) :=
  roughSaiasDickmanBuchstabBlockRemainder_abs_le
    hX hy2 hyM hMX hu5

example {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y X =
      (∑ m ∈ Finset.Ico (roughSaiasSelectorTransition X y) X,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      (FriableAsymptotic.primeThetaWeightedInterval
          (FriableAsymptotic.dickmanThetaWeight X) y X -
        FriableAsymptotic.integerAbelMain
          (FriableAsymptotic.dickmanThetaWeight X) y X) +
      roughSaiasDickmanBuchstabBlockRemainder X y
        (roughSaiasSelectorTransition X y) +
      roughSaiasCanonicalCorrectionObstruction X y :=
  roughSaiasReverseNormalFormDefect_self_eq_closedPieces_add_obstruction
    hy2 hyX hu5

example {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) +
      |roughSaiasCanonicalCorrectionObstruction X y| :=
  roughSaiasReverseNormalFormDefect_self_abs_le_closed_add_riemann_add_obstruction
    hy2 hyX hY hu5

end

end Erdos390.WholePaper
