import Erdos390.WholePaper.RoughSaiasSelectorLedgerBound

/-!
# Fully real cells with the floor/frac-paired natural endpoint sample

Sampling a fully real Buchstab cell by the continuous real-quotient theta
weight leaves a separate signed floor correction.  Sampling instead by the
natural quotient theta weight pairs that correction inside the cell.  The
sum of these paired cells is therefore exactly the natural integer Abel
consistency defect, with no signed-floor term left over.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- Unit-cell quadrature remainder with the floor/frac-paired natural
endpoint sample. -/
noncomputable def roughSaiasFullyRealNaturalBuchstabCellRemainder
    (X m : ℕ) : ℝ :=
  roughSaiasFullyRealBuchstabCellRemainder X m +
    roughSaiasFractionalCorrectionThetaWeight X (m + 1)

/-- Exact pointwise pairing of the continuous cell remainder and the signed
fractional endpoint correction. -/
theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_continuous_add_fractional
    (X m : ℕ) :
    roughSaiasFullyRealNaturalBuchstabCellRemainder X m =
      roughSaiasFullyRealBuchstabCellRemainder X m +
        roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
  rfl

/-- On every cell occurring in the compact Buchstab interval, the paired
definition is literally the integral minus the natural endpoint sample. -/
theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_integral
    {X y Z m : ℕ} (hy2 : 2 ≤ y) (hyZ : y ≤ Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hm : m ∈ Finset.Ico y Z) :
    roughSaiasFullyRealNaturalBuchstabCellRemainder X m =
      ∫ s in (m : ℝ)..(m + 1 : ℕ),
        (roughSaiasFullyRealBuchstabNormalIntegrand X s -
          roughSaiasNaturalQuotientThetaWeight X (m + 1)) := by
  have hmData := Finset.mem_Ico.mp hm
  have hmle : m ≤ m + 1 := by omega
  have hym : y ≤ m := hmData.1
  have hmZ : m + 1 ≤ Z := by omega
  have hglobal :=
    intervalIntegrable_roughSaiasFullyRealBuchstabNormalIntegrand
      hy2 hyZ hZX hu5
  have hsubset : Set.uIcc (m : ℝ) (m + 1 : ℕ) ⊆
      Set.uIcc (y : ℝ) (Z : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hmle),
      Set.uIcc_of_le (by exact_mod_cast hyZ)]
    exact Set.Icc_subset_Icc (by exact_mod_cast hym) (by exact_mod_cast hmZ)
  have hcell := hglobal.mono_set hsubset
  have hconst : IntervalIntegrable
      (fun _ : ℝ ↦ roughSaiasNaturalQuotientThetaWeight X (m + 1))
      MeasureTheory.volume (m : ℝ) (m + 1 : ℕ) :=
    continuous_const.intervalIntegrable _ _
  have hsample :=
    integral_roughSaiasFullyRealBuchstab_cell_eq_sample_add_remainder
      hy2 hyZ hZX hu5 hm
  rw [intervalIntegral.integral_sub hcell hconst]
  simp
  have hsuccCast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    norm_num
  rw [hsuccCast] at hsample
  rw [hsample,
    roughSaiasNormalFormThetaWeight_eq_natural_add_fractional]
  unfold roughSaiasFullyRealNaturalBuchstabCellRemainder
  ring

/-- The paired natural endpoint sample is also the elementary quotient
selector on every upper cell. -/
theorem roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le
    {X m : ℕ} (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) =
      roughSaiasRealQuotientSelectorIntegrand X (m + 1 : ℕ) := by
  have hmpos : 0 < m := by omega
  have hquotientLe : X / (m + 1) ≤ m := by
    calc
      X / (m + 1) ≤ X / m :=
        Nat.div_le_div_left (a := X) (Nat.le_succ m) hmpos
      _ ≤ m ^ 2 / m := Nat.div_le_div_right hupper
      _ = m := by
        simpa only [pow_two] using Nat.mul_div_left m hmpos
  unfold roughSaiasNaturalQuotientThetaWeight
    roughSaiasRealQuotientSelectorIntegrand
  rw [Nat.floor_div_eq_div]
  congr 1
  unfold roughSaiasNaturalMain
  by_cases hquotientZero : X / (m + 1) = 0
  · simp [hquotientZero]
  · have hquotientPos : 0 < X / (m + 1) := Nat.pos_of_ne_zero hquotientZero
    have hcoord := FriableAsymptotic.dickmanU_le_one hquotientPos
      (show 1 < m + 1 by omega) (hquotientLe.trans (Nat.le_succ m))
    rw [roughSaiasG_eq_one_of_le_one hcoord, mul_one]

/-- Consequently, on an upper cell the paired natural remainder is exactly
the already bounded selector remainder. -/
theorem roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_selectorRemainder
    {X m : ℕ} (hX : 0 < X) (hm2 : 2 ≤ m) (hupper : X ≤ m ^ 2) :
    roughSaiasFullyRealNaturalBuchstabCellRemainder X m =
      roughSaiasFullyRealBuchstabCellRemainder X m := by
  have hcontinuous :=
    roughSaiasNormalFormThetaWeight_eq_selector_of_sq_le hX hm2 hupper
  have hnatural :=
    roughSaiasNaturalQuotientThetaWeight_eq_selector_of_sq_le hm2 hupper
  have hpair :=
    roughSaiasNormalFormThetaWeight_eq_natural_add_fractional X (m + 1)
  rw [hcontinuous, hnatural] at hpair
  have hfractional :
      roughSaiasFractionalCorrectionThetaWeight X (m + 1) = 0 := by
    linarith
  rw [roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_continuous_add_fractional,
    hfractional, add_zero]

/-- The natural integer Abel consistency defect is exactly the sum of the
floor/frac-paired fully real cell remainders. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      ∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := by
  have hcontinuous :=
    roughSaiasIntegerAbelConsistencyDefect_eq_cellRemainders
      hy2 hyZ hZX hu5
  have habel :=
    roughSaiasIntegerAbelMain_normalForm_eq_natural_add_fractional
      (X := X) hyZ
  have hfractional :
      FriableAsymptotic.integerAbelMain
          (roughSaiasFractionalCorrectionThetaWeight X) y Z =
        ∑ m ∈ Finset.Ico y Z,
          roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
    rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
      FriableAsymptotic.sum_Ioc_shift]
  have hcells :
      (∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
        (∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealBuchstabCellRemainder X m) +
        ∑ m ∈ Finset.Ico y Z,
          roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _hm
    exact
      roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_continuous_add_fractional
        X m
  calc
    roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
        roughSaiasIntegerAbelConsistencyDefect X y Z +
          FriableAsymptotic.integerAbelMain
            (roughSaiasFractionalCorrectionThetaWeight X) y Z := by
      unfold roughSaiasNaturalIntegerAbelConsistencyDefect
        roughSaiasIntegerAbelConsistencyDefect
      rw [habel]
      ring
    _ = (∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealBuchstabCellRemainder X m) +
        ∑ m ∈ Finset.Ico y Z,
          roughSaiasFractionalCorrectionThetaWeight X (m + 1) := by
      rw [hcontinuous, hfractional]
    _ = ∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m := hcells.symm

/-- Exact master identity with both the natural-base discrepancy and the
signed quotient floors absorbed into paired fully real unit cells. -/
theorem roughSaiasReverseNormalFormDefect_eq_naturalCells_sub_naturalTheta
    {X y Z : ℕ} (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    roughSaiasReverseNormalFormDefect X y Z =
      (∑ m ∈ Finset.Ico y Z,
        roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
      roughSaiasNaturalThetaErrorTransfer X y Z := by
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta,
    roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
      hy2 hyZ hZX hu5]

/-- If the entire interval is on the upper selector face, the paired
natural cell sum satisfies the same inverse-log-square estimate. -/
theorem roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le'
    {X y Z : ℕ} (hX : 0 < X) (hy2 : 2 ≤ y) (hyZ : y < Z)
    (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2) :
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| ≤
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  rw [roughSaiasNaturalIntegerAbelConsistencyDefect_eq_naturalCellRemainders
    hy2 hyZ hZX hu5]
  have hsum :
      (∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m) =
        ∑ m ∈ Finset.Ico y Z,
          roughSaiasFullyRealBuchstabCellRemainder X m := by
    apply Finset.sum_congr rfl
    intro m hm
    have hmData := Finset.mem_Ico.mp hm
    have hm2 : 2 ≤ m := hy2.trans hmData.1
    have hymSq : y ^ 2 ≤ m ^ 2 := Nat.pow_le_pow_left hmData.1 2
    exact roughSaiasFullyRealNaturalBuchstabCellRemainder_eq_selectorRemainder
      hX hm2 (hupper.trans hymSq)
  rw [hsum]
  exact abs_sum_roughSaiasFullyRealBuchstabCellRemainder_le_three_invLogSq
    hX hy2 hyZ.le hupper

/-- Closed reduction on the upper selector face: the only remaining term
is the already explicit fourth-power natural-theta PNT ledger.  In
particular there is no defect or signed-floor premise. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_three_invLogSq_add_naturalThetaLedger
    {X y Z : ℕ} (hX : 0 < X) (hy2 : 2 ≤ y) (hyZ : y < Z)
    (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        roughSaiasNaturalThetaPNTLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z := by
  have hnatural :=
    roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le'
      hX hy2 hyZ hZX hu5 hupper
  have htheta :=
    roughSaiasReverseNormalFormDefect_sub_naturalAbel_abs_le_fourthPower
      (X := X) hY hyZ
  calc
    |roughSaiasReverseNormalFormDefect X y Z| =
        |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z +
          (roughSaiasReverseNormalFormDefect X y Z -
            roughSaiasNaturalIntegerAbelConsistencyDefect X y Z)| := by
      congr 1
      ring
    _ ≤ |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| +
        |roughSaiasReverseNormalFormDefect X y Z -
          roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| :=
      abs_add_le _ _
    _ ≤ 3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        roughSaiasNaturalThetaPNTLedger (4 : ℝ)
          roughSaiasThetaFourthPowerConstant X y Z :=
      add_le_add hnatural htheta

end

end Erdos390.WholePaper
