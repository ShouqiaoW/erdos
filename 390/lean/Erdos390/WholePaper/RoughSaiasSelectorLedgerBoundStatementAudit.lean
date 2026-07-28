import Erdos390.WholePaper.RoughSaiasSelectorLedgerBound

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

#check roughSaiasNaturalQuotientDrop
#check roughSaiasNaturalQuotientDrop_nonneg
#check sum_roughSaiasNaturalQuotientDrop
#check sum_mul_roughSaiasNaturalQuotientDrop
#check sum_mul_roughSaiasNaturalQuotientDrop_le
#check roughSaias_invLog_succ_sub_nonneg
#check roughSaias_invLog_succ_sub_le
#check roughSaiasSelectorCellLedger_le_drop_add_invSq
#check sum_roughSaiasSelectorCellLedger_le
#check abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_explicit
#check abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
#check roughSaiasIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le

example (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        (m : ℝ) * roughSaiasNaturalQuotientDrop X m) =
      (M : ℝ) * ((X / M : ℕ) : ℝ) -
        (Z : ℝ) * ((X / Z : ℕ) : ℝ) +
        ∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ) :=
  sum_mul_roughSaiasNaturalQuotientDrop X hMZ

example (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        (m : ℝ) * roughSaiasNaturalQuotientDrop X m) ≤
      (X : ℝ) * (2 + Real.log (Z : ℝ)) :=
  sum_mul_roughSaiasNaturalQuotientDrop_le X hMZ

example {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
  abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
    hX hM2 hMZ hupper

example {X y Z : ℕ} (hX : 0 < X) (hy2 : 2 ≤ y) (hyZ : y < Z)
    (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2) :
    |roughSaiasIntegerAbelConsistencyDefect X y Z| ≤
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
  roughSaiasIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le
    hX hy2 hyZ hZX hu5 hupper

end

end Erdos390.WholePaper
