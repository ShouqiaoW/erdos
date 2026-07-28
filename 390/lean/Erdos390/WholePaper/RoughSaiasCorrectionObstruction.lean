import Erdos390.WholePaper.RoughSaiasCellTransitionSplit

/-!
# The single remaining signed correction obstruction

The lower paired cells and the natural-minus-Dickman theta residual should
not be estimated separately.  After subtracting the ordinary Dickman
Riemann block, their signed combination is the sole genuinely new
correction term.  The ordinary Dickman Riemann block is bounded directly by
the existing cell-oscillation theorem.
-/

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- Ordinary Dickman right-endpoint Riemann error on `[y,M]`. -/
noncomputable def roughSaiasDickmanBuchstabBlockRemainder
    (X y M : ℕ) : ℝ :=
  (∫ s in (y : ℝ)..(M : ℝ),
      FriableAsymptotic.dickmanContinuousWeight (X : ℝ) s) -
    ∑ m ∈ Finset.Ioc y M, FriableAsymptotic.dickmanThetaWeight X m

/-- Signed lower correction after removing the Dickman Riemann block and
pairing with the residual theta transfer. -/
noncomputable def roughSaiasCanonicalCorrectionObstruction
    (X y : ℕ) : ℝ :=
  ((∑ m ∈ Finset.Ico y (roughSaiasSelectorTransition X y),
      roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
    roughSaiasDickmanBuchstabBlockRemainder X y
      (roughSaiasSelectorTransition X y)) -
  roughSaiasNaturalMinusDickmanThetaTransfer X y X

/-- The ordinary Dickman block has the existing explicit cell-oscillation
bound. -/
theorem roughSaiasDickmanBuchstabBlockRemainder_abs_le
    {X y M : ℕ} (hX : 1 ≤ X) (hy2 : 2 ≤ y)
    (hyM : y ≤ M) (hMX : M ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasDickmanBuchstabBlockRemainder X y M| ≤
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) := by
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hX)
  have hq : ∀ t ∈ Set.Icc (y : ℝ) (M : ℝ),
      1 ≤ FriableAsymptotic.logRatio (X : ℝ) t ∧
        FriableAsymptotic.logRatio (X : ℝ) t ≤ 6 := by
    intro t ht
    have htpos : 0 < t := hypos.trans_le ht.1
    have htX : t ≤ (X : ℝ) :=
      ht.2.trans (by exact_mod_cast hMX)
    have hlogt : 0 < Real.log t :=
      Real.log_pos ((by exact_mod_cast (show 1 < y by omega) :
        (1 : ℝ) < (y : ℝ)).trans_le ht.1)
    have hlogtX : Real.log t ≤ Real.log (X : ℝ) :=
      Real.log_le_log htpos htX
    have hlogyt : Real.log (y : ℝ) ≤ Real.log t :=
      Real.log_le_log hypos ht.1
    unfold FriableAsymptotic.logRatio
    constructor
    · exact (one_le_div hlogt).2 hlogtX
    · exact (div_le_div_of_nonneg_left hlogX0 hlogy hlogyt).trans
        (hu5.trans (by norm_num))
  have hbound := FriableAsymptotic.dickmanWeight_sum_integral_bound
    X hX hy2 hyM hq
  unfold roughSaiasDickmanBuchstabBlockRemainder
  rw [abs_sub_comm]
  exact hbound

/-- Exact master identity with the upper selector block, Dickman core,
ordinary Dickman Riemann error, and the one signed correction obstruction. -/
theorem roughSaiasReverseNormalFormDefect_self_eq_closedPieces_add_obstruction
    {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
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
      roughSaiasCanonicalCorrectionObstruction X y := by
  have hX2 : 2 ≤ X := hy2.trans hyX.le
  have hyM := le_roughSaiasSelectorTransition X y
  have hMX := roughSaiasSelectorTransition_le hX2 hyX.le
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta,
    roughSaiasNaturalIntegerAbelConsistencyDefect_eq_splitCells
      hy2 hyX le_rfl hu5 hyM hMX,
    roughSaiasNaturalThetaErrorTransfer_eq_dickman_add_residual hyX]
  unfold roughSaiasCanonicalCorrectionObstruction
  ring

/-- Final one-obstruction quantitative reduction.  The middle Riemann term
is elementary (`O(X log X / y)`), while every other displayed contribution
already has the target inverse-log-square scale. -/
theorem roughSaiasReverseNormalFormDefect_self_abs_le_closed_add_riemann_add_obstruction
    {X y : ℕ} (hy2 : 2 ≤ y) (hyX : y < X)
    (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasReverseNormalFormDefect X y X| ≤
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
      2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) +
      |roughSaiasCanonicalCorrectionObstruction X y| := by
  have hXpos : 0 < X := by omega
  have hXone : 1 ≤ X := by omega
  have hX2 : 2 ≤ X := hy2.trans hyX.le
  have hM2 : 2 ≤ roughSaiasSelectorTransition X y :=
    hy2.trans (le_roughSaiasSelectorTransition X y)
  have hMX := roughSaiasSelectorTransition_le hX2 hyX.le
  have hupper := roughSaiasSelectorTransition_sq_ge X y
  have hUpperCells :=
    abs_sum_roughSaiasFullyRealNaturalCells_upper_le_three_invLogSq
      hXpos hM2 hMX hupper
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hlogyM : Real.log (y : ℝ) ≤
      Real.log (roughSaiasSelectorTransition X y : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast (show 0 < y by omega))
      (by exact_mod_cast (le_roughSaiasSelectorTransition X y))
  have hpowers : Real.log (y : ℝ) ^ 2 ≤
      Real.log (roughSaiasSelectorTransition X y : ℝ) ^ 2 :=
    pow_le_pow_left₀ hlogy.le hlogyM 2
  have hUpperAtY :
      |∑ m ∈ Finset.Ico (roughSaiasSelectorTransition X y) X,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| ≤
        3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 :=
    hUpperCells.trans
      (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogy) hpowers)
  have hDickmanTheta :=
    roughSaiasDickmanThetaTransfer_abs_le_invLogSq_fourthPower
      hY hXone hy2 hyX le_rfl hu5
  have hRiemann := roughSaiasDickmanBuchstabBlockRemainder_abs_le
    hXone hy2 (le_roughSaiasSelectorTransition X y) hMX hu5
  rw [roughSaiasReverseNormalFormDefect_self_eq_closedPieces_add_obstruction
    hy2 hyX hu5]
  calc
    |(∑ m ∈ Finset.Ico (roughSaiasSelectorTransition X y) X,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
        (FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y X -
          FriableAsymptotic.integerAbelMain
            (FriableAsymptotic.dickmanThetaWeight X) y X) +
        roughSaiasDickmanBuchstabBlockRemainder X y
          (roughSaiasSelectorTransition X y) +
        roughSaiasCanonicalCorrectionObstruction X y| ≤
      |∑ m ∈ Finset.Ico (roughSaiasSelectorTransition X y) X,
          roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
        |FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y X -
          FriableAsymptotic.integerAbelMain
            (FriableAsymptotic.dickmanThetaWeight X) y X| +
        |roughSaiasDickmanBuchstabBlockRemainder X y
          (roughSaiasSelectorTransition X y)| +
        |roughSaiasCanonicalCorrectionObstruction X y| := by
      calc
        _ ≤ |(∑ m ∈ Finset.Ico (roughSaiasSelectorTransition X y) X,
                roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
              (FriableAsymptotic.primeThetaWeightedInterval
                  (FriableAsymptotic.dickmanThetaWeight X) y X -
                FriableAsymptotic.integerAbelMain
                  (FriableAsymptotic.dickmanThetaWeight X) y X)| +
            |roughSaiasDickmanBuchstabBlockRemainder X y
                (roughSaiasSelectorTransition X y) +
              roughSaiasCanonicalCorrectionObstruction X y| := by
          convert abs_add_le
            ((∑ m ∈ Finset.Ico (roughSaiasSelectorTransition X y) X,
                roughSaiasFullyRealNaturalBuchstabCellRemainder X m) -
              (FriableAsymptotic.primeThetaWeightedInterval
                  (FriableAsymptotic.dickmanThetaWeight X) y X -
                FriableAsymptotic.integerAbelMain
                  (FriableAsymptotic.dickmanThetaWeight X) y X))
            (roughSaiasDickmanBuchstabBlockRemainder X y
                (roughSaiasSelectorTransition X y) +
              roughSaiasCanonicalCorrectionObstruction X y) using 1; ring_nf
        _ ≤ (|∑ m ∈ Finset.Ico (roughSaiasSelectorTransition X y) X,
                roughSaiasFullyRealNaturalBuchstabCellRemainder X m| +
              |FriableAsymptotic.primeThetaWeightedInterval
                  (FriableAsymptotic.dickmanThetaWeight X) y X -
                FriableAsymptotic.integerAbelMain
                  (FriableAsymptotic.dickmanThetaWeight X) y X|) +
            (|roughSaiasDickmanBuchstabBlockRemainder X y
                (roughSaiasSelectorTransition X y)| +
              |roughSaiasCanonicalCorrectionObstruction X y|) :=
          add_le_add (abs_sub _ _) (abs_add_le _ _)
        _ = _ := by ring
    _ ≤ (3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
          500 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
            Real.log (y : ℝ) ^ 2) +
        2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) +
        |roughSaiasCanonicalCorrectionObstruction X y| := by
      exact add_le_add
        (add_le_add (add_le_add hUpperAtY hDickmanTheta) hRiemann)
        le_rfl
    _ = (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) +
        |roughSaiasCanonicalCorrectionObstruction X y| := by ring

end

end Erdos390.WholePaper
