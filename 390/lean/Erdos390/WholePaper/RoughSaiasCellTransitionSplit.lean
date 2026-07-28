import Erdos390.WholePaper.RoughSaiasDickmanThetaFourth

/-!
# Splitting at the square-root selector transition

The upper selector cells and the Dickman core of the theta transfer are
already of inverse-log-square size.  This file records the exact split at
an arbitrary transition `M`.  It isolates precisely two remaining explicit
terms: the lower paired-cell block and the natural-minus-Dickman theta
residual.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Canonical natural transition just above `sqrt X`, enlarged to retain
the original left endpoint. -/
def roughSaiasSelectorTransition (X y : ℕ) : ℕ :=
  max y (Nat.sqrt X + 1)

theorem le_roughSaiasSelectorTransition (X y : ℕ) :
    y ≤ roughSaiasSelectorTransition X y := by
  exact le_max_left _ _

theorem roughSaiasSelectorTransition_sq_ge (X y : ℕ) :
    X ≤ roughSaiasSelectorTransition X y ^ 2 := by
  have hsqrt : X < (Nat.sqrt X + 1) ^ 2 := Nat.lt_succ_sqrt' X
  have htransition : Nat.sqrt X + 1 ≤ roughSaiasSelectorTransition X y := by
    exact le_max_right _ _
  exact (Nat.le_of_lt hsqrt).trans (Nat.pow_le_pow_left htransition 2)

theorem roughSaiasSelectorTransition_le
    {X y : ℕ} (hX2 : 2 ≤ X) (hyX : y ≤ X) :
    roughSaiasSelectorTransition X y ≤ X := by
  unfold roughSaiasSelectorTransition
  apply max_le hyX
  have hsqrt : Nat.sqrt X < X := Nat.sqrt_lt_self (by omega)
  omega

/-- Exact adjacent split of the paired fully real cell sum. -/
theorem sum_roughSaiasFullyRealNaturalCells_split
    (X : ℕ) {y M Z : ℕ} (hyM : y ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
      (∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) +
      ∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := by
  rw [← Finset.sum_Ico_consecutive _ hyM hMZ]

/-- The natural integer consistency defect split into lower cells and the
upper selector block. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_eq_splitCells
    {X y M Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) :
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      (∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) +
      ∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := by
  rw [roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
    hy2 hyZ hZX hu5,
    sum_roughSaiasFullyRealNaturalCells_split X hyM hMZ]

/-- Above any transition satisfying `X ≤ M²`, the paired natural cells
inherit the closed selector bound. -/
theorem abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
      3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by
  have hsum :
      (∑ m ∈ Finset.Ico M Z,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
        ∑ m ∈ Finset.Ico M Z,
          roughSaiasFullyRealBuchstabCellRemainder X m := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := hM2.trans hmData.1
    have hMmSq : M ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hmData.1 2
    exact roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_selectorRemainder
      hX hm2 (hupper.trans hMmSq)
  rw [hsum]
  exact abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
    hX hM2 hMZ hupper

/-- Quantitative transition split: the entire upper block is charged at
the original left-endpoint logarithm, so only the lower-cell sum remains. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_lowerCells_add_three
    {X y M Z : ℕ} (hX : 0 < X) (hy2 : 2 ≤ y) (hyZ : y < Z)
    (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hM2 : 2 ≤ M := hy2.trans hyM
  have hupperBound :=
    abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
      hX hM2 hMZ hupper
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogyM : Real.log (y : ℝ) ≤ Real.log (M : ℝ) :=
    Real.log_le_log hypos (by exact_mod_cast hyM)
  have hpowers : Real.log (y : ℝ) ^ 2 ≤ Real.log (M : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogy.le hlogyM 2
  have hupperAtY :
      |∑ m ∈ Finset.Ico M Z,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
        3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
    hupperBound.trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogy) hpowers)
  rw [roughSaiasNaturalIntegerAbelConsistencyDefect_eq_splitCells
    hy2 hyZ hZX hu5 hyM hMZ]
  exact (abs_add_le _ _).trans (add_le_add le_rfl hupperAtY)

/-- Final explicit reduction at an arbitrary square-root transition.  The
only two unclosed quantities are displayed literally on the right. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_lowerCells_closedCore_residual
    {X y M Z : ℕ} (hX : 0 < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hyM : y ≤ M) (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      |∑ m ∈ Finset.Ico y M,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
      |roughSaiasNaturalMinusDickmanThetaTransfer X y Z| := by
  have hnatural :=
    roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_lowerCells_add_three
      hX hy2 hyZ hZX hu5 hyM hMZ hupper
  have htheta :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_dickman_add_residual
      hY (show 1 ≤ X by omega) hy2 hyZ hZX hu5
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta]
  calc
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| +
        |roughSaiasNaturalThetaErrorTransfer X y Z| := abs_sub _ _
    _ ≤
      (|∑ m ∈ Finset.Ico y M,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
        3 * (X : ℝ) / Real.log (y : ℝ) ^ 2) +
      (500 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasNaturalMinusDickmanThetaTransfer X y Z|) :=
      add_le_add hnatural htheta
    _ = |∑ m ∈ Finset.Ico y M,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
        (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasNaturalMinusDickmanThetaTransfer X y Z| := by ring

/-- Canonical `Z=X` form.  Every already-closed contribution is explicit;
the lower-cell block ends exactly at `max(y,⌊√X⌋+1)`. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_canonicalLowerCells_closedCore_residual
    {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      |∑ m ∈ Finset.Ico y (roughSaiasSelectorTransition X y),
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
      |roughSaiasNaturalMinusDickmanThetaTransfer X y X| := by
  have hXpos : 0 < X := by omega
  have hX2 : 2 ≤ X := hy2.trans hyX.le
  have hyM : y ≤ roughSaiasSelectorTransition X y :=
    le_roughSaiasSelectorTransition X y
  have hMX : roughSaiasSelectorTransition X y ≤ X :=
    roughSaiasSelectorTransition_le hX2 hyX.le
  have hupper : X ≤ roughSaiasSelectorTransition X y ^ 2 :=
    roughSaiasSelectorTransition_sq_ge X y
  exact
    roughSaiasReverseNormalFormDefect_abs_le_lowerCells_closedCore_residual
      hXpos hY hy2 hyX le_rfl hu5 hyM hMX hupper

end

end Erdos390.WholePaper
