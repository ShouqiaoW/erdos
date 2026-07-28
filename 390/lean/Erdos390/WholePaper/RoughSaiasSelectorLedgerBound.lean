import Erdos390.WholePaper.RoughSaiasFullyRealBuchstabCells

/-!
# Summing the upper-cell quotient-selector ledger

On cells above the square-root transition the fully real Buchstab
integrand is the elementary quotient selector

`floor (X / s) / log s`.

The cell ledger from `RoughSaiasFullyRealBuchstabCells` has two pieces.
The natural quotient drops telescope exactly, while the reciprocal-log
variation is bounded by the convergent `sum 1 / m^2` tail.  This file makes
that summation quantitative without any asymptotic or defect premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- The natural quotient drop occurring in the upper selector ledger. -/
noncomputable def roughSaiasNaturalQuotientDrop (X m : ℕ) : ℝ :=
  ((X / m : ℕ) : ℝ) - ((X / (m + 1) : ℕ) : ℝ)

theorem roughSaiasNaturalQuotientDrop_nonneg
    (X : ℕ) {m : ℕ} (hm : 0 < m) :
    0 ≤ roughSaiasNaturalQuotientDrop X m := by
  unfold roughSaiasNaturalQuotientDrop
  apply sub_nonneg.mpr
  exact_mod_cast Nat.div_le_div_left (a := X) (Nat.le_succ m) hm

/-- The quotient-drop part telescopes before any estimate is taken. -/
theorem sum_roughSaiasNaturalQuotientDrop
    (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z, roughSaiasNaturalQuotientDrop X m) =
      ((X / M : ℕ) : ℝ) - ((X / Z : ℕ) : ℝ) := by
  induction Z, hMZ using Nat.le_induction with
  | base => simp
  | succ Z hMZ ih =>
      rw [Finset.sum_Ico_succ_top hMZ, ih]
      unfold roughSaiasNaturalQuotientDrop
      ring

/-- First-moment Abel identity for the natural quotient drops.  Weighting
each drop by its base costs only the harmonic sum of the remaining
quotients; no individual jump is charged independently. -/
theorem sum_mul_roughSaiasNaturalQuotientDrop
    (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        (m : ℝ) * roughSaiasNaturalQuotientDrop X m) =
      (M : ℝ) * ((X / M : ℕ) : ℝ) -
        (Z : ℝ) * ((X / Z : ℕ) : ℝ) +
        ∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ) := by
  induction Z, hMZ using Nat.le_induction with
  | base => simp
  | succ Z hMZ ih =>
      rw [Finset.sum_Ico_succ_top hMZ, ih,
        Finset.sum_Ioc_succ_top hMZ]
      unfold roughSaiasNaturalQuotientDrop
      push_cast
      ring

/-- Quantitative first-moment bound for quotient drops.  The right side is
the exact `X log Z` scale supplied by the hyperbola telescope. -/
theorem sum_mul_roughSaiasNaturalQuotientDrop_le
    (X : ℕ) {M Z : ℕ} (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z,
        (m : ℝ) * roughSaiasNaturalQuotientDrop X m) ≤
      (X : ℝ) * (2 + Real.log (Z : ℝ)) := by
  have hMterm :
      (M : ℝ) * ((X / M : ℕ) : ℝ) ≤ (X : ℝ) := by
    exact_mod_cast
      (show M * (X / M) ≤ X by
        simpa [Nat.mul_comm] using Nat.div_mul_le_self X M)
  have hquotientSum :
      (∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ)) ≤
        (X : ℝ) * ∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ) := by
    calc
      (∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ)) ≤
          ∑ m ∈ Finset.Ioc M Z,
            (X : ℝ) * (1 / (m : ℝ)) := by
              apply Finset.sum_le_sum
              intro m _hm
              calc
                ((X / m : ℕ) : ℝ) ≤ (X : ℝ) / (m : ℝ) :=
                  Nat.cast_div_le
                _ = (X : ℝ) * (1 / (m : ℝ)) := by ring
      _ = (X : ℝ) * ∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ) := by
        rw [Finset.mul_sum]
  have hharmonic :
      (∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ)) ≤
        1 + Real.log (Z : ℝ) :=
    FriableAsymptotic.harmonic_Ioc_le
  rw [sum_mul_roughSaiasNaturalQuotientDrop X hMZ]
  calc
    (M : ℝ) * ((X / M : ℕ) : ℝ) -
          (Z : ℝ) * ((X / Z : ℕ) : ℝ) +
          ∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ) ≤
        (M : ℝ) * ((X / M : ℕ) : ℝ) +
          ∑ m ∈ Finset.Ioc M Z, ((X / m : ℕ) : ℝ) := by
            have hnonneg :
                0 ≤ (Z : ℝ) * ((X / Z : ℕ) : ℝ) := by positivity
            linarith
    _ ≤ (X : ℝ) +
          (X : ℝ) * ∑ m ∈ Finset.Ioc M Z, 1 / (m : ℝ) :=
      add_le_add hMterm hquotientSum
    _ ≤ (X : ℝ) + (X : ℝ) * (1 + Real.log (Z : ℝ)) :=
      add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hharmonic (by positivity))
    _ = (X : ℝ) * (2 + Real.log (Z : ℝ)) := by ring

theorem roughSaias_invLog_succ_sub_nonneg
    {m : ℕ} (hm2 : 2 ≤ m) :
    0 ≤ 1 / Real.log (m : ℝ) -
      1 / Real.log ((m + 1 : ℕ) : ℝ) := by
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogmono : Real.log (m : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < m by omega))
      (by exact_mod_cast (Nat.le_succ m))
  exact sub_nonneg.mpr (one_div_le_one_div_of_le hlogm hlogmono)

/-- One reciprocal-log step costs at most
`1 / (m log(M)^2)` uniformly for `m ≥ M`. -/
theorem roughSaias_invLog_succ_sub_le
    {M m : ℕ} (hM2 : 2 ≤ M) (hMm : M ≤ m) :
    1 / Real.log (m : ℝ) -
        1 / Real.log ((m + 1 : ℕ) : ℝ) ≤
      1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2) := by
  have hm2 : 2 ≤ m := hM2.trans hMm
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < M by omega)
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hm1pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogm1 : 0 < Real.log ((m + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m + 1 by omega))
  have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hMpos (by exact_mod_cast hMm)
  have hlogMm1 : Real.log (M : ℝ) ≤
      Real.log ((m + 1 : ℕ) : ℝ) :=
    hlogMm.trans (Real.log_le_log hmpos (by exact_mod_cast (Nat.le_succ m)))
  have hgapNonneg :
      0 ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) :=
    sub_nonneg.mpr
      (Real.log_le_log hmpos (by exact_mod_cast (Nat.le_succ m)))
  have hgap :
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) ≤
        1 / (m : ℝ) := by
    have hratio : 0 < ((m + 1 : ℕ) : ℝ) / (m : ℝ) :=
      div_pos hm1pos hmpos
    have h := Real.log_le_sub_one_of_pos hratio
    calc
      Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ) =
          Real.log (((m + 1 : ℕ) : ℝ) / (m : ℝ)) := by
        rw [Real.log_div hm1pos.ne' hmpos.ne']
      _ ≤ ((m + 1 : ℕ) : ℝ) / (m : ℝ) - 1 := h
      _ = 1 / (m : ℝ) := by
        field_simp [hmpos.ne']
        norm_num
  have hdenom : Real.log (M : ℝ) ^ 2 ≤
      Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) := by
    rw [pow_two]
    exact mul_le_mul hlogMm hlogMm1 hlogM.le hlogm.le
  have hinvIdentity :
      1 / Real.log (m : ℝ) -
          1 / Real.log ((m + 1 : ℕ) : ℝ) =
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          (Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) := by
    field_simp [hlogm.ne', hlogm1.ne']
  rw [hinvIdentity]
  calc
    (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          (Real.log (m : ℝ) * Real.log ((m + 1 : ℕ) : ℝ)) ≤
        (Real.log ((m + 1 : ℕ) : ℝ) - Real.log (m : ℝ)) /
          Real.log (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_left hgapNonneg (sq_pos_of_pos hlogM) hdenom
    _ ≤ (1 / (m : ℝ)) / Real.log (M : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right hgap (sq_nonneg _)
    _ = 1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2) := by ring

/-- A cell ledger is a telescoping quotient drop at the fixed left-hand
logarithm, plus an inverse-square summable tail. -/
theorem roughSaiasSelectorCellLedger_le_drop_add_invSq
    (X : ℕ) {M m : ℕ} (hM2 : 2 ≤ M) (hMm : M ≤ m) :
    roughSaiasSelectorCellLedger X m ≤
      roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) * (1 / (m : ℝ) ^ 2) := by
  have hm2 : 2 ≤ m := hM2.trans hMm
  have hmpos : 0 < (m : ℝ) := by
    exact_mod_cast (show 0 < m by omega)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hlogm : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < m by omega))
  have hlogMm : Real.log (M : ℝ) ≤ Real.log (m : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < M by omega))
      (by exact_mod_cast hMm)
  have hdropNonneg : 0 ≤ roughSaiasNaturalQuotientDrop X m :=
    roughSaiasNaturalQuotientDrop_nonneg X (by omega)
  have hfirst :
      roughSaiasNaturalQuotientDrop X m / Real.log (m : ℝ) ≤
        roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) :=
    div_le_div_of_nonneg_left hdropNonneg hlogM hlogMm
  have hinvNonneg := roughSaias_invLog_succ_sub_nonneg hm2
  have hinvBound := roughSaias_invLog_succ_sub_le hM2 hMm
  have hquotient : ((X / (m + 1) : ℕ) : ℝ) ≤
      (X : ℝ) / (m : ℝ) := by
    calc
      ((X / (m + 1) : ℕ) : ℝ) ≤
          (X : ℝ) / ((m + 1 : ℕ) : ℝ) := Nat.cast_div_le
      _ ≤ (X : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hmpos
          (by exact_mod_cast (Nat.le_succ m))
  have hsecond :
      ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (1 / (m : ℝ) ^ 2) := by
    calc
      ((X / (m + 1) : ℕ) : ℝ) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) ≤
        ((X : ℝ) / (m : ℝ)) *
          (1 / Real.log (m : ℝ) -
            1 / Real.log ((m + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right hquotient hinvNonneg
      _ ≤ ((X : ℝ) / (m : ℝ)) *
          (1 / ((m : ℝ) * Real.log (M : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hinvBound (by positivity)
      _ = ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (1 / (m : ℝ) ^ 2) := by ring
  unfold roughSaiasSelectorCellLedger
    roughSaiasNaturalQuotientDrop
  exact add_le_add hfirst hsecond

/-- Explicit sum of all upper selector ledgers. -/
theorem sum_roughSaiasSelectorCellLedger_le
    (X : ℕ) {M Z : ℕ} (hM2 : 2 ≤ M) (hMZ : M ≤ Z) :
    (∑ m ∈ Finset.Ico M Z, roughSaiasSelectorCellLedger X m) ≤
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by
  have hMpos : 0 < (M : ℝ) := by
    exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hfirst :
      (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ)) ≤
        (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) := by
    calc
      (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ)) =
        (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m) / Real.log (M : ℝ) := by
            rw [Finset.sum_div]
      _ = (((X / M : ℕ) : ℝ) - ((X / Z : ℕ) : ℝ)) /
          Real.log (M : ℝ) := by
            rw [sum_roughSaiasNaturalQuotientDrop X hMZ]
      _ ≤ ((X / M : ℕ) : ℝ) / Real.log (M : ℝ) :=
        div_le_div_of_nonneg_right
          (sub_le_self _ (by positivity)) hlogM.le
      _ ≤ ((X : ℝ) / (M : ℝ)) / Real.log (M : ℝ) :=
        div_le_div_of_nonneg_right Nat.cast_div_le hlogM.le
      _ = (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) := by ring
  have hcoef : 0 ≤ (X : ℝ) / Real.log (M : ℝ) ^ 2 := by positivity
  have hsecond :
      (∑ m ∈ Finset.Ico M Z,
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2)) ≤
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by
    calc
      (∑ m ∈ Finset.Ico M Z,
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2)) =
        ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (∑ m ∈ Finset.Ico M Z, 1 / (m : ℝ) ^ 2) := by
            rw [Finset.mul_sum]
      _ ≤ ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
          (2 / (M : ℝ)) :=
        mul_le_mul_of_nonneg_left
          (FriableAsymptotic.sum_Ico_inv_sq_le (show 1 ≤ M by omega))
          hcoef
      _ = 2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by ring
  calc
    (∑ m ∈ Finset.Ico M Z, roughSaiasSelectorCellLedger X m) ≤
      ∑ m ∈ Finset.Ico M Z,
        (roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ) +
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2)) := by
        apply Finset.sum_le_sum
        intro m hm
        exact roughSaiasSelectorCellLedger_le_drop_add_invSq X hM2
          (Finset.mem_Ico.mp hm).1
    _ = (∑ m ∈ Finset.Ico M Z,
          roughSaiasNaturalQuotientDrop X m / Real.log (M : ℝ)) +
        ∑ m ∈ Finset.Ico M Z,
          ((X : ℝ) / Real.log (M : ℝ) ^ 2) *
            (1 / (m : ℝ) ^ 2) := by
      rw [Finset.sum_add_distrib]
    _ ≤ (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) :=
      add_le_add hfirst hsecond

/-- The complete upper-cell remainder block has the explicit elementary
bound obtained by summing its selector ledgers. -/
theorem abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_explicit
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) := by
  exact (abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_selectorLedger
    hX hM2 hupper).trans
      (sum_roughSaiasSelectorCellLedger_le X hM2 hMZ)

/-- At the square-root transition or above, the upper-cell block is already
of inverse-log-square size (with a deliberately coarse constant `3`). -/
theorem abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
    {X M Z : ℕ} (hX : 0 < X) (hM2 : 2 ≤ M)
    (hMZ : M ≤ Z) (hupper : X ≤ M ^ 2) :
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by
  have hlogM : 0 < Real.log (M : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hMone : (1 : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast (show 1 ≤ M by omega)
  have hlogMleM : Real.log (M : ℝ) ≤ (M : ℝ) := by
    have h := Real.log_le_sub_one_of_pos
      (by exact_mod_cast (show 0 < M by omega) : (0 : ℝ) < (M : ℝ))
    linarith
  have hdenomOne : Real.log (M : ℝ) ^ 2 ≤
      (M : ℝ) * Real.log (M : ℝ) := by
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hlogMleM hlogM.le
  have hdenomTwo : Real.log (M : ℝ) ^ 2 ≤
      (M : ℝ) * Real.log (M : ℝ) ^ 2 := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hMone (sq_nonneg (Real.log (M : ℝ)))
  have hfirst :
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) ≤
        (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogM) hdenomOne
  have hsecond :
      2 * (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ) ^ 2) ≤
        2 * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogM) hdenomTwo
  calc
    |∑ m ∈ Finset.Ico M Z,
        roughSaiasFullyRealBuchstabCellRemainder X m| ≤
      (X : ℝ) / ((M : ℝ) * Real.log (M : ℝ)) +
        2 * (X : ℝ) /
          ((M : ℝ) * Real.log (M : ℝ) ^ 2) :=
      abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_explicit
        hX hM2 hMZ hupper
    _ ≤ (X : ℝ) / Real.log (M : ℝ) ^ 2 +
        2 * (X : ℝ) / Real.log (M : ℝ) ^ 2 :=
      add_le_add hfirst hsecond
    _ = 3 * (X : ℝ) / Real.log (M : ℝ) ^ 2 := by ring

/-- Direct inverse-log-square estimate for the integer Abel consistency
defect when the whole interval lies on the upper selector face. -/
theorem roughSaiasIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le
    {X y Z : ℕ} (hX : 0 < X) (hy2 : 2 ≤ y) (hyZ : y < Z)
    (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2) :
    |roughSaiasIntegerAbelConsistencyDefect X y Z| ≤
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  rw [roughSaiasIntegerAbelConsistencyDefect_eq_cellRemainders
    hy2 hyZ hZX hu5]
  exact abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
    hX hy2 hyZ.le hupper

end

end Erdos390.WholePaper
