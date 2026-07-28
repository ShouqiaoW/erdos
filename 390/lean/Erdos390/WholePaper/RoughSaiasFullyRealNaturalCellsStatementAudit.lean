import Erdos390.WholePaper.RoughSaiasFullyRealNaturalCells

open scoped BigOperators Interval

namespace Erdos390.WholePaper

noncomputable section

#check roughSaiasFullyRealNaturalBuchstabCellRemainder
#check roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_continuous_add_fractional
#check roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_integral
#check roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
#check roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_selectorRemainder
#check roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
#check roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
#check roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le'
#check roughSaiasReverseNormalFormDefect_abs_le_three_invLogSq_add_naturalThetaLedger

example {X y Z m : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ico y Z) :
    roughSaiasFullyRealNaturalBuchstabCellRemainder X m =
      ∫ s in (m : ℝ)..(m + 1 : ℕ),
        (roughSaiasFullyRealBuchstabNormalIntegrand X s -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)) :=
  roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_integral
    hy2 hyZ hZX hu5 hm

example {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m :=
  roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
    hy2 hyZ hZX hu5

example {X y Z : ℕ} (hX : 0 < X) (hy2 : 2 ≤ y) (hyZ : y < Z)
    (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        roughSaiasNaturalThetaPNTLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z :=
  roughSaiasReverseNormalFormDefect_abs_le_three_invLogSq_add_naturalThetaLedger
    hX hy2 hyZ hZX hu5 hupper hY

end

end Erdos390.WholePaper
