import Erdos390.WholePaper.RoughSaiasNaturalThetaLedgerBound

/-!
# Fourth-power PNT transfer for the Dickman core

The existing Dickman theta-transfer theorem is stated for a cubic-log PNT
error and returns one reciprocal logarithm.  A fourth-power PNT estimate,
restricted at the left endpoint `y`, is a cubic estimate with constant
`C / log y`; hence the same theorem immediately returns the target
inverse-log-square scale.

The paired natural theta weight is then split exactly into this closed
Dickman core and one explicit residual weight.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-- Difference between the paired natural Saias theta weight and the
ordinary continuous Dickman theta weight. -/
noncomputable def roughSaiasNaturalMinusDickmanThetaWeight
    (X m : ℕ) : ℝ :=
  roughSaiasNaturalQuotientThetaWeight X m -
    FriableAsymptotic.dickmanThetaWeight X m

/-- Prime-minus-integer transfer of the preceding explicit residual. -/
noncomputable def roughSaiasNaturalMinusDickmanThetaTransfer
    (X y Z : ℕ) : ℝ :=
  FriableAsymptotic.primeThetaWeightedInterval
      (roughSaiasNaturalMinusDickmanThetaWeight X) y Z -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNaturalMinusDickmanThetaWeight X) y Z

/-- Fourth-power PNT input gives an inverse-log-square transfer for the
ordinary Dickman core by direct reuse of the existing cubic theorem. -/
theorem roughSaiasDickmanThetaTransfer_abs_le_invLogSq
    {C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ (4 : ℝ)))
    (hC : 0 ≤ C) (hX₀y : X₀ ≤ y) (hX : 1 ≤ X)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |FriableAsymptotic.primeThetaWeightedInterval
          (FriableAsymptotic.dickmanThetaWeight X) y Z -
        FriableAsymptotic.integerAbelMain
          (FriableAsymptotic.dickmanThetaWeight X) y Z| ≤
      500 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by
  have hypos : 0 < (y : ℝ) := by
    exact_mod_cast (show 0 < y by omega)
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hCubic : ∀ T, y ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        (C / Real.log (y : ℝ)) *
          ((T : ℝ) / Real.log (T : ℝ) ^ (3 : ℝ)) := by
    intro T hyT
    have hTpos : 0 < (T : ℝ) := by
      exact_mod_cast (show 0 < T by omega)
    have hlogT : 0 < Real.log (T : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < T by omega))
    have hlogyT : Real.log (y : ℝ) ≤ Real.log (T : ℝ) :=
      Real.log_le_log hypos (by exact_mod_cast hyT)
    have hfourth := htheta T (hX₀y.trans hyT)
    have hpowFour : Real.log (T : ℝ) ^ (4 : ℝ) =
        Real.log (T : ℝ) ^ (4 : ℕ) := by
      simpa only [Nat.cast_ofNat] using
        Real.rpow_natCast (Real.log (T : ℝ)) 4
    have hpowThree : Real.log (T : ℝ) ^ (3 : ℝ) =
        Real.log (T : ℝ) ^ (3 : ℕ) := by
      simpa only [Nat.cast_ofNat] using
        Real.rpow_natCast (Real.log (T : ℝ)) 3
    rw [hpowFour] at hfourth
    rw [hpowThree]
    calc
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
          C * ((T : ℝ) / Real.log (T : ℝ) ^ 4) := hfourth
      _ = (C / Real.log (T : ℝ)) *
          ((T : ℝ) / Real.log (T : ℝ) ^ 3) := by
        field_simp [hlogT.ne']
      _ ≤ (C / Real.log (y : ℝ)) *
          ((T : ℝ) / Real.log (T : ℝ) ^ 3) := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_left hC hlogy hlogyT) (by positivity)
  have hq : ∀ t ∈ Set.Icc (y : ℝ) (Z : ℝ),
      1 ≤ FriableAsymptotic.logRatio (X : ℝ) t ∧
        FriableAsymptotic.logRatio (X : ℝ) t ≤ 6 := by
    intro t ht
    have htpos : 0 < t := hypos.trans_le ht.1
    have htX : t ≤ (X : ℝ) :=
      ht.2.trans (by exact_mod_cast hZX)
    have hlogt : 0 < Real.log t :=
      Real.log_pos ((by exact_mod_cast (show 1 < y by omega) :
        (1 : ℝ) < (y : ℝ)).trans_le ht.1)
    have hlogtX : Real.log t ≤ Real.log (X : ℝ) :=
      Real.log_le_log htpos htX
    have hlogyt : Real.log (y : ℝ) ≤ Real.log t :=
      Real.log_le_log hypos ht.1
    have hlogX0 : 0 ≤ Real.log (X : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hX)
    unfold FriableAsymptotic.logRatio
    constructor
    · exact (one_le_div hlogt).2 hlogtX
    · exact (div_le_div_of_nonneg_left hlogX0 hlogy hlogyt).trans
        (hu5.trans (by norm_num))
  have hcore := FriableAsymptotic.dickmanWeight_pnt_bound
    X hX (C := C / Real.log (y : ℝ))
      (div_nonneg hC hlogy.le) hCubic (X₀ := y) le_rfl hy2 hyZ hq
  calc
    |FriableAsymptotic.primeThetaWeightedInterval
          (FriableAsymptotic.dickmanThetaWeight X) y Z -
        FriableAsymptotic.integerAbelMain
          (FriableAsymptotic.dickmanThetaWeight X) y Z| ≤
      500 * (C / Real.log (y : ℝ)) * (X : ℝ) /
        Real.log (y : ℝ) := hcore
    _ = 500 * C * (X : ℝ) / Real.log (y : ℝ) ^ 2 := by ring

/-- Fully closed fourth-power specialization of the Dickman core. -/
theorem roughSaiasDickmanThetaTransfer_abs_le_invLogSq_fourthPower
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hX : 1 ≤ X) (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |FriableAsymptotic.primeThetaWeightedInterval
          (FriableAsymptotic.dickmanThetaWeight X) y Z -
        FriableAsymptotic.integerAbelMain
          (FriableAsymptotic.dickmanThetaWeight X) y Z| ≤
      500 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
        Real.log (y : ℝ) ^ 2 := by
  exact roughSaiasDickmanThetaTransfer_abs_le_invLogSq
    roughSaiasThetaFourthPower_bound
      roughSaiasThetaFourthPowerConstant_pos.le hY hX hy2 hyZ hZX hu5

/-- Exact linear splitting of the paired natural theta transfer into the
closed Dickman core and the explicit residual transfer. -/
theorem roughSaiasNaturalThetaErrorTransfer_eq_dickman_add_residual
    {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasNaturalThetaErrorTransfer X y Z =
      (FriableAsymptotic.primeThetaWeightedInterval
          (FriableAsymptotic.dickmanThetaWeight X) y Z -
        FriableAsymptotic.integerAbelMain
          (FriableAsymptotic.dickmanThetaWeight X) y Z) +
      roughSaiasNaturalMinusDickmanThetaTransfer X y Z := by
  have hprime :
      FriableAsymptotic.primeThetaWeightedInterval
          (roughSaiasNaturalQuotientThetaWeight X) y Z =
        FriableAsymptotic.primeThetaWeightedInterval
            (FriableAsymptotic.dickmanThetaWeight X) y Z +
          FriableAsymptotic.primeThetaWeightedInterval
            (roughSaiasNaturalMinusDickmanThetaWeight X) y Z := by
    unfold FriableAsymptotic.primeThetaWeightedInterval
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    unfold roughSaiasNaturalMinusDickmanThetaWeight
    ring
  have hinteger :
      FriableAsymptotic.integerAbelMain
          (roughSaiasNaturalQuotientThetaWeight X) y Z =
        FriableAsymptotic.integerAbelMain
            (FriableAsymptotic.dickmanThetaWeight X) y Z +
          FriableAsymptotic.integerAbelMain
            (roughSaiasNaturalMinusDickmanThetaWeight X) y Z := by
    rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
      FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
      FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _hm
    unfold roughSaiasNaturalMinusDickmanThetaWeight
    ring
  unfold roughSaiasNaturalThetaErrorTransfer
    roughSaiasNaturalMinusDickmanThetaTransfer
  rw [hprime, hinteger]
  ring

/-- Quantitative theta reduction: the entire Dickman part is closed at the
target scale; only the explicit natural-minus-Dickman residual remains. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_dickman_add_residual
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hX : 1 ≤ X) (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      500 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasNaturalMinusDickmanThetaTransfer X y Z| := by
  rw [roughSaiasNaturalThetaErrorTransfer_eq_dickman_add_residual hyZ]
  exact (abs_add_le _ _).trans
    (add_le_add
      (roughSaiasDickmanThetaTransfer_abs_le_invLogSq_fourthPower
        hY hX hy2 hyZ hZX hu5)
      le_rfl)

/-- Corresponding full-defect reduction on the upper selector face. -/
theorem roughSaiasReverseNormalFormDefect_abs_le_closedCore_add_residual
    {X y Z : ℕ} (hX : 0 < X) (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hy2 : 2 ≤ y) (hyZ : y < Z) (hZX : Z ≤ X)
    (hu5 : Real.log (X : ℝ) / Real.log (y : ℝ) ≤ 5)
    (hupper : X ≤ y ^ 2) :
    |roughSaiasReverseNormalFormDefect X y Z| ≤
      (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasNaturalMinusDickmanThetaTransfer X y Z| := by
  have hnatural :=
    roughSaiasNaturalIntegerAbelConsistencyDefect_abs_le_three_invLogSq_of_sq_le'
      hX hy2 hyZ hZX hu5 hupper
  have htheta :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_dickman_add_residual
      hY (show 1 ≤ X by omega) hy2 hyZ hZX hu5
  rw [roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta]
  calc
    |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      |roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| +
        |roughSaiasNaturalThetaErrorTransfer X y Z| := abs_sub _ _
    _ ≤ 3 * (X : ℝ) / Real.log (y : ℝ) ^ 2 +
        (500 * roughSaiasThetaFourthPowerConstant * (X : ℝ) /
            Real.log (y : ℝ) ^ 2 +
          |roughSaiasNaturalMinusDickmanThetaTransfer X y Z|) :=
      add_le_add hnatural htheta
    _ = (3 + 500 * roughSaiasThetaFourthPowerConstant) * (X : ℝ) /
          Real.log (y : ℝ) ^ 2 +
        |roughSaiasNaturalMinusDickmanThetaTransfer X y Z| := by ring

end

end Erdos390.WholePaper
