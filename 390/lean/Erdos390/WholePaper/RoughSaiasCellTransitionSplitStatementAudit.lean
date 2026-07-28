import Erdos390.WholePaper.RoughSaiasCellTransitionSplit

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

#check roughSaiasSelectorTransition
#check le_roughSaiasSelectorTransition
#check roughSaiasSelectorTransition_sq_ge
#check roughSaiasSelectorTransition_le
#check sum_roughSaiasFullyRealNaturalCells_split
#check roughSaiasNaturalIntegerAbelConsistencyDefect_eq_splitCells
#check abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
#check roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_lowerCells_add_three
#check roughSaiasReverseNormalFormDefect_abs_le_lowerCells_closedCore_residual
#check roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerCells_closedCore_residual

example (X y : ℕ) : y ≤ roughSaiasSelectorTransition X y :=
  le_roughSaiasSelectorTransition X y

example (X y : ℕ) : X ≤ roughSaiasSelectorTransition X y ^ 2 :=
  roughSaiasSelectorTransition_sq_ge X y

example {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ m ∈ Finset.Ico y (roughSaiasSelectorTransition X y),
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
      |roughSaiasNaturalMinusDickmanThetaTransfer X y X| :=
  roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerCells_closedCore_residual
    hy2 hyX hY hu5

end

end Erdos390.WholePaper
