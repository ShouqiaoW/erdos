import Erdos390.WholePaper.RoughSaiasFullyRealBuchstabCells

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Set MeasureTheory
open Erdos390.Full

noncomputable section

#check roughSaiasFullyRealBuchstabNormalIntegrand
#check roughSaiasRealQuotientSelectorIntegrand
#check roughSaiasFullyRealCellQuotientDrift
#check roughSaiasFullyRealCellBaseDrift
#check roughSaiasFullyRealBuchstabCellRemainder
#check roughSaiasSelectorCellLedger
#check roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector
#check roughSaiasFullyRealBuchstabNormalIntegrand_eq_selector_on_cell
#check roughSaiasLambdaStieltjesWithCutoff_inner_eq_fullyReal
#check roughSaiasNaturalMain_buchstab_fullyReal
#check intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
#check integral_roughSaiasFullyRealBuchstab_eq_sum_cells
#check roughSaiasFullyRealBuchstabNormalIntegrand_nat
#check roughSaiasNormalFormThetaWeight_eq_selector_of_sq_le
#check roughSaiasFullyReal_cell_integrand_sub_sample
#check roughSaiasFullyRealBuchstabCellRemainder_eq_selector
#check roughSaiasRealQuotientSelector_cell_sub_right_abs_le
#check roughSaiasFullyRealBuchstabCellRemainder_abs_le_selectorLedger
#check abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_selectorLedger
#check roughSaiasFullyRealBuchstabCellRemainder_eq_drifts
#check integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
#check roughSaiasNaturalMain_buchstab_sum_cells
#check roughSaiasIntegerAbelConsistencyDefect_eq_cellRemainders
#check roughSaiasSignedAbelCenter_eq_cellRemainders_add_signedFloor
#check roughSaiasReverseNormalFormDefect_eq_cells_add_floor_sub_theta

example {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    (∫ s in (y : ℝ)..(Z : ℝ),
        roughSaiasFullyRealBuchstabNormalIntegrand X s) =
      ∑ m ∈ Finset.Ico y Z,
        ∫ s in (m : ℝ)..(m + 1 : ℕ),
          roughSaiasFullyRealBuchstabNormalIntegrand X s :=
  integral_roughSaiasFullyRealBuchstab_eq_sum_cells
    hy2 hyZ hZX hu5

example {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealBuchstabCellRemainder X m) +
      (∑ p ∈ roughReversePrimeInterval y Z,
        roughSaiasSignedFractionalCorrectionTerm X p) -
      roughSaiasThetaErrorTransfer X y Z :=
  roughSaiasReverseNormalFormDefect_eq_cells_add_floor_sub_theta
    hy2 hyZ hZX hu5

end

end Erdos390.WholePaper
