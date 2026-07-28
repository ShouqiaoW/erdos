import Erdos390.WholePaper.RoughSaiasEndpointApproximation

/-!
# Signed fractional correction and finite Abel decomposition for the Saias defect

This file goes one level below
`RoughSaiasReverseNormalFormDefectInvLogSqBound`.  It never assumes a bound
for that defect.  Instead it keeps the quotient fractional correction with
its sign, separates the reverse defect into a continuous normal-form prime
sum and that signed correction, and applies the project's existing finite
theta Abel identity to the continuous prime sum.

The resulting quantitative theorem assumes only a cumulative theta-error
bound.  Its right side is the explicit endpoint-plus-variation ledger for the
Saias theta weight.  Thus the remaining inverse-log-square problem is a
deterministic estimate for the displayed signed Abel center, not a renamed
copy of the original defect bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

/-! ## One quotient: retain the fractional correction with its sign -/

/-- The formal normal form evaluated at the real quotient `X/m`, before the
quotient is replaced by its natural-number floor. -/
noncomputable def roughSaiasContinuousPrimeNormalForm
    (X m : ℕ) : ℝ :=
  roughSaiasLambdaNormalForm ((X : ℝ) / (m : ℝ)) m

/-- Signed discrepancy between the real-quotient normal form and the
natural-quotient main term. -/
noncomputable def roughSaiasSignedPrimeFloorCorrection
    (X m : ℕ) : ℝ :=
  roughSaiasContinuousPrimeNormalForm X m -
    roughSaiasNaturalMain (X / m) m

/-- The signed fractional correction after expanding
`LambdaNormalForm(X/m,m)`.  The first summand is the displacement of `G_m`;
the second is the exact cancellation contributed by `-fract(X/m)`. -/
noncomputable def roughSaiasSignedFractionalCorrectionTerm
    (X m : ℕ) : ℝ :=
  ((X / m : ℕ) : ℝ) *
      (roughSaiasG m
          (Real.log ((X : ℝ) / (m : ℝ)) /
            Real.log (m : ℝ)) -
        roughSaiasG m (FriableAsymptotic.dickmanU (X / m) m)) +
    Int.fract ((X : ℝ) / (m : ℝ)) *
      (roughSaiasG m
          (Real.log ((X : ℝ) / (m : ℝ)) /
            Real.log (m : ℝ)) - 1)

/-- Natural division is exactly the real quotient minus its fractional
part.  This includes the totalized `m=0` case. -/
theorem roughSaiasRealQuotient_sub_fract_eq_natQuotient
    (X m : ℕ) :
    (X : ℝ) / (m : ℝ) -
        Int.fract ((X : ℝ) / (m : ℝ)) =
      ((X / m : ℕ) : ℝ) := by
  rw [Int.self_sub_fract]
  rw [← natCast_floor_eq_intCast_floor (by positivity)]
  rw [Nat.floor_div_eq_div]

/-- Exact signed quotient correction.  No triangle inequality or absolute
value is used. -/
theorem roughSaiasSignedPrimeFloorCorrection_eq_fractional
    (X m : ℕ) :
    roughSaiasSignedPrimeFloorCorrection X m =
      roughSaiasSignedFractionalCorrectionTerm X m := by
  have hfloor := roughSaiasRealQuotient_sub_fract_eq_natQuotient X m
  unfold roughSaiasSignedPrimeFloorCorrection
    roughSaiasContinuousPrimeNormalForm
    roughSaiasSignedFractionalCorrectionTerm
    roughSaiasLambdaNormalForm roughSaiasNaturalMain
  linear_combination
    (roughSaiasG m
      (Real.log ((X : ℝ) / (m : ℝ)) / Real.log (m : ℝ))) * hfloor

/-! ## The reverse defect as continuous part plus signed correction -/

/-- Reverse normal-form consistency defect with every quotient kept at the
real endpoint `X/p`. -/
noncomputable def roughSaiasReverseContinuousNormalFormDefect
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    ∑ p ∈ roughReversePrimeInterval y Z,
      roughSaiasContinuousPrimeNormalForm X p

/-- The original defect is exactly the continuous defect plus all signed
floor corrections. -/
theorem roughSaiasReverseNormalFormDefect_eq_continuous_add_signedFloor
    (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasReverseContinuousNormalFormDefect X y Z +
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughSaiasSignedPrimeFloorCorrection X p := by
  unfold roughSaiasReverseNormalFormDefect
    roughSaiasReverseContinuousNormalFormDefect
    roughSaiasSignedPrimeFloorCorrection
  rw [Finset.sum_sub_distrib]
  ring

/-- Fully expanded signed fractional-correction identity for the reverse
normal-form defect. -/
theorem roughSaiasReverseNormalFormDefect_eq_continuous_add_fractional
    (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasReverseContinuousNormalFormDefect X y Z +
        ∑ p ∈ roughReversePrimeInterval y Z,
          roughSaiasSignedFractionalCorrectionTerm X p := by
  rw [roughSaiasReverseNormalFormDefect_eq_continuous_add_signedFloor]
  congr 1
  apply Finset.sum_congr rfl
  intro p _hp
  exact roughSaiasSignedPrimeFloorCorrection_eq_fractional X p

/-! ## Exact finite theta Abel identity -/

/-- Test weight whose theta mass at a prime is the continuous real-quotient
normal form. -/
noncomputable def roughSaiasNormalFormThetaWeight
    (X m : ℕ) : ℝ :=
  roughSaiasContinuousPrimeNormalForm X m / Real.log (m : ℝ)

/-- Multiplication by the prime theta atom `log p` cancels the denominator
in the Saias weight exactly. -/
theorem roughSaiasPrimeThetaWeightedInterval_eq_continuousSum
    (X y Z : ℕ) :
    FriableAsymptotic.primeThetaWeightedInterval
        (roughSaiasNormalFormThetaWeight X) y Z =
      ∑ p ∈ roughReversePrimeInterval y Z,
        roughSaiasContinuousPrimeNormalForm X p := by
  unfold FriableAsymptotic.primeThetaWeightedInterval
    roughReversePrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hpprime.one_lt))
  rw [roughSaiasNormalFormThetaWeight]
  exact div_mul_cancel₀ _ hlogp

/-- Difference between the natural main-term endpoints and the integer Abel
main term for the continuous Saias weight. -/
noncomputable def roughSaiasIntegerAbelConsistencyDefect
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNormalFormThetaWeight X) y Z

/-- Exact theta-error transfer for the same weight. -/
noncomputable def roughSaiasThetaErrorTransfer
    (X y Z : ℕ) : ℝ :=
  FriableAsymptotic.primeThetaWeightedInterval
      (roughSaiasNormalFormThetaWeight X) y Z -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNormalFormThetaWeight X) y Z

theorem roughSaiasReverseContinuousNormalFormDefect_eq_abel_sub_theta
    (X y Z : ℕ) :
    roughSaiasReverseContinuousNormalFormDefect X y Z =
      roughSaiasIntegerAbelConsistencyDefect X y Z -
        roughSaiasThetaErrorTransfer X y Z := by
  unfold roughSaiasReverseContinuousNormalFormDefect
    roughSaiasIntegerAbelConsistencyDefect roughSaiasThetaErrorTransfer
  rw [roughSaiasPrimeThetaWeightedInterval_eq_continuousSum]
  ring

/-- The exact signed Abel center: the integer-main consistency term and the
fractional quotient correction are intentionally added before taking any
absolute value. -/
noncomputable def roughSaiasSignedAbelCenter
    (X y Z : ℕ) : ℝ :=
  roughSaiasIntegerAbelConsistencyDefect X y Z +
    ∑ p ∈ roughReversePrimeInterval y Z,
      roughSaiasSignedFractionalCorrectionTerm X p

/-- Exact master identity.  The full reverse defect is the signed Abel
center minus the theta-error transfer. -/
theorem roughSaiasReverseNormalFormDefect_eq_signedAbelCenter_sub_theta
    (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasSignedAbelCenter X y Z -
        roughSaiasThetaErrorTransfer X y Z := by
  rw [roughSaiasReverseNormalFormDefect_eq_continuous_add_fractional,
    roughSaiasReverseContinuousNormalFormDefect_eq_abel_sub_theta]
  unfold roughSaiasSignedAbelCenter
  ring

/-- The theta transfer expanded into the two endpoint errors and the signed
discrete variation of the Saias weight. -/
theorem roughSaiasThetaErrorTransfer_eq_finiteAbel
    {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasThetaErrorTransfer X y Z =
      roughSaiasNormalFormThetaWeight X Z *
          (FriableAsymptotic.primeLogSumUpTo Z - (Z : ℝ)) -
        roughSaiasNormalFormThetaWeight X (y + 1) *
          (FriableAsymptotic.primeLogSumUpTo y - (y : ℝ)) -
        ∑ m ∈ Finset.Ioc y (Z - 1),
          (roughSaiasNormalFormThetaWeight X (m + 1) -
              roughSaiasNormalFormThetaWeight X m) *
            (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) := by
  unfold roughSaiasThetaErrorTransfer
  exact FriableAsymptotic.primeThetaWeightedInterval_error_identity
    (roughSaiasNormalFormThetaWeight X) hyZ

/-! ## The floor/frac-paired natural theta weight -/

/-- Theta weight with the natural quotient retained.  Its discrete
variation contains the quotient-floor jumps and the base variation of `G_m`
in one object. -/
noncomputable def roughSaiasNaturalQuotientThetaWeight
    (X m : ℕ) : ℝ :=
  roughSaiasNaturalMain (X / m) m / Real.log (m : ℝ)

/-- Theta weight of the signed fractional correction. -/
noncomputable def roughSaiasFractionalCorrectionThetaWeight
    (X m : ℕ) : ℝ :=
  roughSaiasSignedFractionalCorrectionTerm X m /
    Real.log (m : ℝ)

/-- Pointwise pairing: the continuous weight is the natural weight plus the
signed fractional correction. -/
theorem roughSaiasNormalFormThetaWeight_eq_natural_add_fractional
    (X m : ℕ) :
    roughSaiasNormalFormThetaWeight X m =
      roughSaiasNaturalQuotientThetaWeight X m +
        roughSaiasFractionalCorrectionThetaWeight X m := by
  unfold roughSaiasNormalFormThetaWeight
    roughSaiasNaturalQuotientThetaWeight
    roughSaiasFractionalCorrectionThetaWeight
  rw [← roughSaiasSignedPrimeFloorCorrection_eq_fractional]
  unfold
    roughSaiasSignedPrimeFloorCorrection
  ring

/-- Exact discrete-variation pairing.  In particular, the continuous and
fractional variations are not bounded separately. -/
theorem roughSaiasNaturalQuotientThetaWeight_diff_eq_paired
    (X m : ℕ) :
    roughSaiasNaturalQuotientThetaWeight X (m + 1) -
        roughSaiasNaturalQuotientThetaWeight X m =
      (roughSaiasNormalFormThetaWeight X (m + 1) -
          roughSaiasNormalFormThetaWeight X m) -
        (roughSaiasFractionalCorrectionThetaWeight X (m + 1) -
          roughSaiasFractionalCorrectionThetaWeight X m) := by
  rw [roughSaiasNormalFormThetaWeight_eq_natural_add_fractional,
    roughSaiasNormalFormThetaWeight_eq_natural_add_fractional]
  ring

/-- The natural theta mass is literally the prime sum in the original
normal-form defect. -/
theorem roughSaiasPrimeThetaWeightedInterval_eq_naturalSum
    (X y Z : ℕ) :
    FriableAsymptotic.primeThetaWeightedInterval
        (roughSaiasNaturalQuotientThetaWeight X) y Z =
      ∑ p ∈ roughReversePrimeInterval y Z,
        roughSaiasNaturalMain (X / p) p := by
  unfold FriableAsymptotic.primeThetaWeightedInterval
    roughReversePrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hpprime.one_lt))
  rw [roughSaiasNaturalQuotientThetaWeight]
  exact div_mul_cancel₀ _ hlogp

/-- The fractional theta mass is literally the signed correction sum. -/
theorem roughSaiasPrimeThetaWeightedInterval_eq_fractionalSum
    (X y Z : ℕ) :
    FriableAsymptotic.primeThetaWeightedInterval
        (roughSaiasFractionalCorrectionThetaWeight X) y Z =
      ∑ p ∈ roughReversePrimeInterval y Z,
        roughSaiasSignedFractionalCorrectionTerm X p := by
  unfold FriableAsymptotic.primeThetaWeightedInterval
    roughReversePrimeInterval
  apply Finset.sum_congr rfl
  intro p hp
  have hpprime : p.Prime :=
    Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  have hlogp : Real.log (p : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hpprime.one_lt))
  rw [roughSaiasFractionalCorrectionThetaWeight]
  exact div_mul_cancel₀ _ hlogp

/-- Integer Abel main terms respect the pointwise signed pairing. -/
theorem roughSaiasIntegerAbelMain_normalForm_eq_natural_add_fractional
    {X y Z : ℕ} (hyZ : y < Z) :
    FriableAsymptotic.integerAbelMain
        (roughSaiasNormalFormThetaWeight X) y Z =
      FriableAsymptotic.integerAbelMain
          (roughSaiasNaturalQuotientThetaWeight X) y Z +
        FriableAsymptotic.integerAbelMain
          (roughSaiasFractionalCorrectionThetaWeight X) y Z := by
  rw [FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
    FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ,
    FriableAsymptotic.integerAbelMain_eq_sum_Ioc _ hyZ]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _hm
  exact roughSaiasNormalFormThetaWeight_eq_natural_add_fractional X m

/-- Integer Abel consistency term for the floor/frac-paired natural weight. -/
noncomputable def roughSaiasNaturalIntegerAbelConsistencyDefect
    (X y Z : ℕ) : ℝ :=
  roughSaiasNaturalMain X Z - roughSaiasNaturalMain X y -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNaturalQuotientThetaWeight X) y Z

/-- Theta-error transfer for the paired natural weight. -/
noncomputable def roughSaiasNaturalThetaErrorTransfer
    (X y Z : ℕ) : ℝ :=
  FriableAsymptotic.primeThetaWeightedInterval
      (roughSaiasNaturalQuotientThetaWeight X) y Z -
    FriableAsymptotic.integerAbelMain
      (roughSaiasNaturalQuotientThetaWeight X) y Z

/-- Theta-error transfer for the signed fractional correction weight. -/
noncomputable def roughSaiasFractionalThetaErrorTransfer
    (X y Z : ℕ) : ℝ :=
  FriableAsymptotic.primeThetaWeightedInterval
      (roughSaiasFractionalCorrectionThetaWeight X) y Z -
    FriableAsymptotic.integerAbelMain
      (roughSaiasFractionalCorrectionThetaWeight X) y Z

/-- The signed Abel center is exactly the natural integer consistency term
plus the fractional theta transfer.  This is the summation-by-parts
cancellation that must be kept intact in a sharp estimate. -/
theorem roughSaiasSignedAbelCenter_eq_natural_add_fractionalTheta
    {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasSignedAbelCenter X y Z =
      roughSaiasNaturalIntegerAbelConsistencyDefect X y Z +
        roughSaiasFractionalThetaErrorTransfer X y Z := by
  have habel :=
    roughSaiasIntegerAbelMain_normalForm_eq_natural_add_fractional
      (X := X) hyZ
  have hprime :=
    roughSaiasPrimeThetaWeightedInterval_eq_fractionalSum X y Z
  unfold roughSaiasSignedAbelCenter
    roughSaiasIntegerAbelConsistencyDefect
    roughSaiasNaturalIntegerAbelConsistencyDefect
    roughSaiasFractionalThetaErrorTransfer
  rw [hprime]
  linarith

/-- Direct exact Abel formula for the original defect, now with every
floor/frac contribution paired inside the natural weight. -/
theorem roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta
    (X y Z : ℕ) :
    roughSaiasReverseNormalFormDefect X y Z =
      roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
        roughSaiasNaturalThetaErrorTransfer X y Z := by
  unfold roughSaiasReverseNormalFormDefect
    roughSaiasNaturalIntegerAbelConsistencyDefect
    roughSaiasNaturalThetaErrorTransfer
  rw [roughSaiasPrimeThetaWeightedInterval_eq_naturalSum]
  ring

/-- The natural theta transfer has the usual finite Abel expansion, but its
discrete variation is the paired variation above. -/
theorem roughSaiasNaturalThetaErrorTransfer_eq_finiteAbel
    {X y Z : ℕ} (hyZ : y < Z) :
    roughSaiasNaturalThetaErrorTransfer X y Z =
      roughSaiasNaturalQuotientThetaWeight X Z *
          (FriableAsymptotic.primeLogSumUpTo Z - (Z : ℝ)) -
        roughSaiasNaturalQuotientThetaWeight X (y + 1) *
          (FriableAsymptotic.primeLogSumUpTo y - (y : ℝ)) -
        ∑ m ∈ Finset.Ioc y (Z - 1),
          (roughSaiasNaturalQuotientThetaWeight X (m + 1) -
              roughSaiasNaturalQuotientThetaWeight X m) *
            (FriableAsymptotic.primeLogSumUpTo m - (m : ℝ)) := by
  unfold roughSaiasNaturalThetaErrorTransfer
  exact FriableAsymptotic.primeThetaWeightedInterval_error_identity
    (roughSaiasNaturalQuotientThetaWeight X) hyZ

/-! ## Quantitative theta transfer, without a defect-bound premise -/

/-- Explicit endpoint-plus-variation ledger obtained when a power-log theta
error is inserted into finite Abel summation. -/
noncomputable def roughSaiasThetaPNTLedger
    (A C : ℝ) (X y Z : ℕ) : ℝ :=
  |roughSaiasNormalFormThetaWeight X Z| *
      (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ A)) +
    |roughSaiasNormalFormThetaWeight X (y + 1)| *
      (C * ((y : ℝ) / Real.log (y : ℝ) ^ A)) +
    ∑ m ∈ Finset.Ioc y (Z - 1),
      |roughSaiasNormalFormThetaWeight X (m + 1) -
          roughSaiasNormalFormThetaWeight X m| *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ A))

/-- Quantitative Abel transfer specialized to the continuous Saias weight.
Its only analytic premise is the existing cumulative theta-error shape. -/
theorem roughSaiasThetaErrorTransfer_abs_le_pntLedger
    {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hX₀y : X₀ ≤ y) (hyZ : y < Z) :
    |roughSaiasThetaErrorTransfer X y Z| ≤
      roughSaiasThetaPNTLedger A C X y Z := by
  unfold roughSaiasThetaErrorTransfer roughSaiasThetaPNTLedger
  exact FriableAsymptotic.primeThetaWeightedInterval_pnt_bound
    (roughSaiasNormalFormThetaWeight X) htheta hX₀y hyZ

/-- The corresponding PNT ledger for the floor/frac-paired natural weight. -/
noncomputable def roughSaiasNaturalThetaPNTLedger
    (A C : ℝ) (X y Z : ℕ) : ℝ :=
  |roughSaiasNaturalQuotientThetaWeight X Z| *
      (C * ((Z : ℝ) / Real.log (Z : ℝ) ^ A)) +
    |roughSaiasNaturalQuotientThetaWeight X (y + 1)| *
      (C * ((y : ℝ) / Real.log (y : ℝ) ^ A)) +
    ∑ m ∈ Finset.Ioc y (Z - 1),
      |roughSaiasNaturalQuotientThetaWeight X (m + 1) -
          roughSaiasNaturalQuotientThetaWeight X m| *
        (C * ((m : ℝ) / Real.log (m : ℝ) ^ A))

/-- PNT transfer with the floor and fractional variations already paired.
Again the sole analytic premise is a cumulative theta-error bound. -/
theorem roughSaiasNaturalThetaErrorTransfer_abs_le_pntLedger
    {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hX₀y : X₀ ≤ y) (hyZ : y < Z) :
    |roughSaiasNaturalThetaErrorTransfer X y Z| ≤
      roughSaiasNaturalThetaPNTLedger A C X y Z := by
  unfold roughSaiasNaturalThetaErrorTransfer
    roughSaiasNaturalThetaPNTLedger
  exact FriableAsymptotic.primeThetaWeightedInterval_pnt_bound
    (roughSaiasNaturalQuotientThetaWeight X) htheta hX₀y hyZ

/-- Quantitative defect reduction with all floor/frac variation paired. -/
theorem roughSaiasReverseNormalFormDefect_sub_naturalAbel_abs_le
    {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hX₀y : X₀ ≤ y) (hyZ : y < Z) :
    |roughSaiasReverseNormalFormDefect X y Z -
        roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| ≤
      roughSaiasNaturalThetaPNTLedger A C X y Z := by
  have hidentity :=
    roughSaiasReverseNormalFormDefect_eq_naturalAbel_sub_theta X y Z
  have hthetaBound :=
    roughSaiasNaturalThetaErrorTransfer_abs_le_pntLedger
      (A := A) (C := C) (X₀ := X₀) (X := X) (y := y) (Z := Z)
      htheta hX₀y hyZ
  rw [hidentity]
  have hrearrange :
      (roughSaiasNaturalIntegerAbelConsistencyDefect X y Z -
          roughSaiasNaturalThetaErrorTransfer X y Z) -
        roughSaiasNaturalIntegerAbelConsistencyDefect X y Z =
      -roughSaiasNaturalThetaErrorTransfer X y Z := by
    ring
  rw [hrearrange, abs_neg]
  exact hthetaBound

/-- Consequently the full reverse defect differs from the explicit signed
Abel center by at most the theta PNT ledger.  This conclusion assumes a
theta error, not a bound for the reverse defect. -/
theorem roughSaiasReverseNormalFormDefect_sub_signedAbelCenter_abs_le
    {A C : ℝ} {X₀ X y Z : ℕ}
    (htheta : ∀ T, X₀ ≤ T →
      |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
        C * ((T : ℝ) / Real.log (T : ℝ) ^ A))
    (hX₀y : X₀ ≤ y) (hyZ : y < Z) :
    |roughSaiasReverseNormalFormDefect X y Z -
        roughSaiasSignedAbelCenter X y Z| ≤
      roughSaiasThetaPNTLedger A C X y Z := by
  have hidentity :=
    roughSaiasReverseNormalFormDefect_eq_signedAbelCenter_sub_theta X y Z
  have hthetaBound :=
    roughSaiasThetaErrorTransfer_abs_le_pntLedger
      (A := A) (C := C) (X₀ := X₀) (X := X) (y := y) (Z := Z)
      htheta hX₀y hyZ
  rw [hidentity]
  have hrearrange :
      (roughSaiasSignedAbelCenter X y Z -
          roughSaiasThetaErrorTransfer X y Z) -
        roughSaiasSignedAbelCenter X y Z =
      -roughSaiasThetaErrorTransfer X y Z := by
    ring
  rw [hrearrange, abs_neg]
  exact hthetaBound

/-! ## Closed fourth-power theta specialization -/

/-- A named constant from the already proved theta PNT with fourth-power
logarithmic saving. -/
noncomputable def roughSaiasThetaFourthPowerConstant : ℝ :=
  Classical.choose
    (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))

theorem roughSaiasThetaFourthPowerConstant_pos :
    0 < roughSaiasThetaFourthPowerConstant :=
  (Classical.choose_spec
    (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).1

noncomputable def roughSaiasThetaFourthPowerCutoff : ℕ :=
  Classical.choose
    (Classical.choose_spec
      (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).2

theorem roughSaiasThetaFourthPower_bound
    (T : ℕ) (hT : roughSaiasThetaFourthPowerCutoff ≤ T) :
    |FriableAsymptotic.primeLogSumUpTo T - (T : ℝ)| ≤
      roughSaiasThetaFourthPowerConstant *
        ((T : ℝ) / Real.log (T : ℝ) ^ (4 : ℝ)) :=
  (Classical.choose_spec
    (Classical.choose_spec
      (FriableAsymptotic.exists_primeLogSumUpTo_error_bound (4 : ℝ))).2)
    T hT

/-- Fully closed theta-transfer estimate at fourth-power logarithmic saving.
Only the deterministic signed Abel center remains to be estimated. -/
theorem roughSaiasReverseNormalFormDefect_sub_signedAbelCenter_abs_le_fourthPower
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hyZ : y < Z) :
    |roughSaiasReverseNormalFormDefect X y Z -
        roughSaiasSignedAbelCenter X y Z| ≤
      roughSaiasThetaPNTLedger (4 : ℝ)
        roughSaiasThetaFourthPowerConstant X y Z := by
  exact roughSaiasReverseNormalFormDefect_sub_signedAbelCenter_abs_le
    roughSaiasThetaFourthPower_bound hY hyZ

/-- Closed fourth-power transfer with the floor/frac variation paired inside
the natural weight. -/
theorem roughSaiasReverseNormalFormDefect_sub_naturalAbel_abs_le_fourthPower
    {X y Z : ℕ} (hY : roughSaiasThetaFourthPowerCutoff ≤ y)
    (hyZ : y < Z) :
    |roughSaiasReverseNormalFormDefect X y Z -
        roughSaiasNaturalIntegerAbelConsistencyDefect X y Z| ≤
      roughSaiasNaturalThetaPNTLedger (4 : ℝ)
        roughSaiasThetaFourthPowerConstant X y Z := by
  exact roughSaiasReverseNormalFormDefect_sub_naturalAbel_abs_le
    roughSaiasThetaFourthPower_bound hY hyZ

end

end Erdos390.WholePaper
