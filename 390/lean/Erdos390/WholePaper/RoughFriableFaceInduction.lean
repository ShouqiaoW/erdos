import Erdos390.WholePaper.RoughBalancedFriableResidualReduction

/-!
# Method of steps for local friable residual regularity

This file pushes the exact reverse-Buchstab finite-difference identity through
the five Dickman faces used in Section 6.  The induction hypothesis is always
on the strictly lower quotient coordinate: for `y < p`, division by `p`
changes the face bound from `m + 1` to `m`.

There is one remaining analytic input.  It is stated below as the exact
prime-transition cancellation between the deterministic Dickman defect and
the strictly lower-face quotient residual sum.  It contains no selector,
head, row, feasibility, or target-face residual assertion.  The cumulative
PNT and floor ledgers already available in the library are proved separately,
making precise why an endpoint estimate alone does not settle the local
transition ledger.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

/-! ## Elementary facts about the reverse prime interval -/

theorem roughReversePrimeInterval_prime
    {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    p.Prime := by
  exact Nat.prime_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1

theorem roughReversePrimeInterval_gt_left
    {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    y < p := by
  have hpprime : p.Prime := roughReversePrimeInterval_prime hp
  have hpout := (Finset.mem_sdiff.mp hp).2
  by_contra hnot
  apply hpout
  rw [Nat.mem_primesBelow]
  exact ⟨by omega, hpprime⟩

theorem roughReversePrimeInterval_le_right
    {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    p ≤ Z := by
  have hpbelow := Nat.lt_of_mem_primesBelow (Finset.mem_sdiff.mp hp).1
  omega

/-! ## Exact continuous/floor decomposition of the main defect -/

/-- The reverse Dickman defect before integer quotient floors are inserted. -/
noncomputable def roughFriableReverseContinuousDefect
    (X y Z : ℕ) : ℝ :=
  (X : ℝ) - roughFriableDickmanMain X y -
    ∑ p ∈ roughReversePrimeInterval y Z,
      FriableAsymptotic.dickmanPrimeSummand X p

/-- The entire discrepancy caused by replacing `X / p` with its integer
floor in the recursive Dickman main term. -/
noncomputable def roughFriableReverseFloorDiscrepancy
    (X y Z : ℕ) : ℝ :=
  ∑ p ∈ roughReversePrimeInterval y Z,
    (FriableAsymptotic.dickmanPrimeSummand X p -
      roughFriableDickmanMain (X / p) p)

/-- Exact separation of the continuous prime-sum defect from all quotient
floor errors. -/
theorem roughFriableReverseMainDefect_eq_continuous_add_floor
    (X y Z : ℕ) :
    roughFriableReverseMainDefect X y Z =
      roughFriableReverseContinuousDefect X y Z +
        roughFriableReverseFloorDiscrepancy X y Z := by
  unfold roughFriableReverseMainDefect
    roughFriableReverseContinuousDefect
    roughFriableReverseFloorDiscrepancy
  rw [Finset.sum_sub_distrib]
  ring

/-- Every individual quotient-floor discrepancy is at most three throughout
the compact `u ≤ 5` region. -/
theorem roughFriableReverseFloorDiscrepancy_abs_le_card
    {X y : ℕ} (hy2 : 2 ≤ y)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableReverseFloorDiscrepancy X y X| ≤
      3 * ((roughReversePrimeInterval y X).card : ℝ) := by
  unfold roughFriableReverseFloorDiscrepancy
  calc
    |∑ p ∈ roughReversePrimeInterval y X,
        (FriableAsymptotic.dickmanPrimeSummand X p -
          roughFriableDickmanMain (X / p) p)| ≤
      ∑ p ∈ roughReversePrimeInterval y X,
        |FriableAsymptotic.dickmanPrimeSummand X p -
          roughFriableDickmanMain (X / p) p| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ roughReversePrimeInterval y X, 3 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime : p.Prime := roughReversePrimeInterval_prime hp
      have hpX : p ≤ X := roughReversePrimeInterval_le_right hp
      have hyp : y < p := roughReversePrimeInterval_gt_left hp
      have hlogp : 0 < Real.log (p : ℝ) :=
        Real.log_pos (by exact_mod_cast hpprime.one_lt)
      have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
      have hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5 := by
        apply (div_le_iff₀ hlogp).2
        nlinarith
      have hfloor :=
        FriableAsymptotic.dickmanPrimeSummand_floor_stability
          X p hpprime.two_le hpX hq5
      rw [abs_sub_comm]
      simpa only [roughFriableDickmanMain] using hfloor
    _ = 3 * ((roughReversePrimeInterval y X).card : ℝ) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Strongest closed floor ledger currently obtained from the elementary
prime-count estimate.  It is cumulative in `X`, not local in `B - A`. -/
theorem roughFriableReverseFloorDiscrepancy_abs_le_endpointScale
    {X y : ℕ} (hy2 : 2 ≤ y)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableReverseFloorDiscrepancy X y X| ≤
      3 * Real.log 4 * (X : ℝ) / Real.log (y : ℝ) := by
  have hfloor :=
    roughFriableReverseFloorDiscrepancy_abs_le_card hy2 hlog
  have hcard := FriableAsymptotic.primeInterval_card_le y X hy2
  calc
    _ ≤ 3 * ((roughReversePrimeInterval y X).card : ℝ) := hfloor
    _ ≤ 3 * (Real.log 4 * (X : ℝ) / Real.log (y : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [roughReversePrimeInterval] using hcard)
        (by norm_num)
    _ = 3 * Real.log 4 * (X : ℝ) / Real.log (y : ℝ) := by ring

/-- A common cap may extend beyond the endpoint `X`.  Terms with `p ≤ X`
have the proved floor-stability cost `3`; terms with `X < p` have zero integer
quotient and real cost `< 1`, so the same constant remains valid. -/
theorem roughFriableReverseFloorTerm_abs_le_three
    {X y Z p : ℕ} (hy2 : 2 ≤ y)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ))
    (hp : p ∈ roughReversePrimeInterval y Z) :
    |FriableAsymptotic.dickmanPrimeSummand X p -
        roughFriableDickmanMain (X / p) p| ≤ 3 := by
  have hpprime : p.Prime := roughReversePrimeInterval_prime hp
  have hyp : y < p := roughReversePrimeInterval_gt_left hp
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast hpprime.one_lt)
  by_cases hX : X = 0
  · subst X
    simp [FriableAsymptotic.dickmanPrimeSummand]
  · have hXpos : 0 < X := Nat.pos_of_ne_zero hX
    by_cases hpX : p ≤ X
    · have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
        Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
      have hq5 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 5 := by
        apply (div_le_iff₀ hlogp).2
        nlinarith
      have hfloor :=
        FriableAsymptotic.dickmanPrimeSummand_floor_stability
          X p hpprime.two_le hpX hq5
      rw [abs_sub_comm]
      simpa only [roughFriableDickmanMain] using hfloor
    · have hXp : X < p := lt_of_not_ge hpX
      have hlogXp : Real.log (X : ℝ) ≤ Real.log (p : ℝ) :=
        Real.log_le_log (by exact_mod_cast hXpos) (by exact_mod_cast hXp.le)
      have hq1 : Real.log (X : ℝ) / Real.log (p : ℝ) ≤ 1 := by
        apply (div_le_iff₀ hlogp).2
        simpa using hlogXp
      have hrho : rho
          (Real.log (X : ℝ) / Real.log (p : ℝ) - 1) = 1 :=
        rho_eq_one_of_le_one (by linarith)
      have hpcast : (0 : ℝ) < (p : ℝ) := by
        exact_mod_cast hpprime.pos
      have hratio : (X : ℝ) / (p : ℝ) < 1 := by
        exact (div_lt_one hpcast).2 (by exact_mod_cast hXp)
      rw [Nat.div_eq_of_lt hXp, roughFriableDickmanMain_zero]
      unfold FriableAsymptotic.dickmanPrimeSummand
      rw [hrho, mul_one, sub_zero, abs_of_nonneg (by positivity)]
      linarith

/-- The fully verified common-cap floor finite difference.  Its explicit
constant is `6 * log 4`, but its scale is still the broad endpoint `B`. -/
theorem roughFriableReverseFloorDiscrepancy_difference_abs_le_endpointScale
    {A B y : ℕ} (hy2 : 2 ≤ y) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableReverseFloorDiscrepancy B y B -
        roughFriableReverseFloorDiscrepancy A y B| ≤
      6 * Real.log 4 * (B : ℝ) / Real.log (y : ℝ) := by
  have hlogA : Real.log (A : ℝ) ≤ 5 * Real.log (y : ℝ) := by
    by_cases hA : A = 0
    · subst A
      simpa only [Nat.cast_zero, Real.log_zero] using
        (mul_nonneg (show (0 : ℝ) ≤ 5 by norm_num)
          (Real.log_nonneg (by exact_mod_cast (show 1 ≤ y by omega))))
    · have hApos : 0 < A := Nat.pos_of_ne_zero hA
      exact (Real.log_le_log (by exact_mod_cast hApos)
        (by exact_mod_cast hAB)).trans hlogB
  have hBfloor : |roughFriableReverseFloorDiscrepancy B y B| ≤
      3 * ((roughReversePrimeInterval y B).card : ℝ) := by
    unfold roughFriableReverseFloorDiscrepancy
    calc
      _ ≤ ∑ p ∈ roughReversePrimeInterval y B,
          |FriableAsymptotic.dickmanPrimeSummand B p -
            roughFriableDickmanMain (B / p) p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ roughReversePrimeInterval y B, 3 := by
        apply Finset.sum_le_sum
        intro p hp
        exact roughFriableReverseFloorTerm_abs_le_three
          hy2 hlogB hp
      _ = 3 * ((roughReversePrimeInterval y B).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hAfloor : |roughFriableReverseFloorDiscrepancy A y B| ≤
      3 * ((roughReversePrimeInterval y B).card : ℝ) := by
    unfold roughFriableReverseFloorDiscrepancy
    calc
      _ ≤ ∑ p ∈ roughReversePrimeInterval y B,
          |FriableAsymptotic.dickmanPrimeSummand A p -
            roughFriableDickmanMain (A / p) p| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p ∈ roughReversePrimeInterval y B, 3 := by
        apply Finset.sum_le_sum
        intro p hp
        exact roughFriableReverseFloorTerm_abs_le_three
          hy2 hlogA hp
      _ = 3 * ((roughReversePrimeInterval y B).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        ring
  have hcard := FriableAsymptotic.primeInterval_card_le y B hy2
  calc
    |roughFriableReverseFloorDiscrepancy B y B -
        roughFriableReverseFloorDiscrepancy A y B| ≤
      |roughFriableReverseFloorDiscrepancy B y B| +
        |roughFriableReverseFloorDiscrepancy A y B| := abs_sub _ _
    _ ≤ 3 * ((roughReversePrimeInterval y B).card : ℝ) +
        3 * ((roughReversePrimeInterval y B).card : ℝ) :=
      add_le_add hBfloor hAfloor
    _ = 6 * ((roughReversePrimeInterval y B).card : ℝ) := by ring
    _ ≤ 6 * (Real.log 4 * (B : ℝ) / Real.log (y : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [roughReversePrimeInterval] using hcard)
        (by norm_num)
    _ = 6 * Real.log 4 * (B : ℝ) / Real.log (y : ℝ) := by ring

/-- The continuous prime-sum defect is also closed at the cumulative
endpoint scale, directly from the proved quantitative PNT and the proved
Dickman Riemann-sum remainder. -/
theorem exists_uniform_roughFriableReverseContinuousDefect_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → y ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughFriableReverseContinuousDefect X y X| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨C, hC, X₀, hbound⟩ :=
    FriableAsymptotic.exists_primeLogSumUpTo_error_bound (3 : ℝ)
  obtain ⟨Yᵣ, hremainder⟩ :=
    FriableAsymptotic.exists_dickmanRiemann_remainder_threshold
  let K : ℝ := 500 * C + 1
  let Y₀ : ℕ := max 2 (max X₀ Yᵣ)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, hK, Y₀, ?_⟩
  intro X y hY hyX hlogX
  have hy2 : 2 ≤ y :=
    (le_max_left 2 (max X₀ Yᵣ)).trans (by simpa only [Y₀] using hY)
  have hX₀y : X₀ ≤ y :=
    (le_max_left X₀ Yᵣ).trans
      ((le_max_right 2 (max X₀ Yᵣ)).trans
        (by simpa only [Y₀] using hY))
  have hYᵣy : Yᵣ ≤ y :=
    (le_max_right X₀ Yᵣ).trans
      ((le_max_right 2 (max X₀ Yᵣ)).trans
        (by simpa only [Y₀] using hY))
  have hX1 : 1 ≤ X := (show 1 ≤ y by omega).trans hyX
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  by_cases hyXeq : y = X
  · subst X
    have hlogne : Real.log (y : ℝ) ≠ 0 := hlogy.ne'
    have hdefzero : roughFriableReverseContinuousDefect y y y = 0 := by
      simp [roughFriableReverseContinuousDefect,
        roughReversePrimeInterval, roughFriableDickmanMain,
        FriableAsymptotic.dickmanU, hlogne, rho_one]
    rw [hdefzero, abs_zero]
    dsimp [K]
    positivity
  · have hyXlt : y < X := lt_of_le_of_ne hyX hyXeq
    have hq : ∀ t ∈ Set.Icc (y : ℝ) (X : ℝ),
        1 ≤ FriableAsymptotic.logRatio (X : ℝ) t ∧
          FriableAsymptotic.logRatio (X : ℝ) t ≤ 6 := by
      intro t ht
      have ht1 : 1 < t :=
        (by exact_mod_cast (show 1 < y by omega) : (1 : ℝ) < y).trans_le ht.1
      have hlogt : 0 < Real.log t := Real.log_pos ht1
      have hlogtX : Real.log t ≤ Real.log (X : ℝ) := by
        apply Real.log_le_log (by linarith)
        exact ht.2
      have hlogyt : Real.log (y : ℝ) ≤ Real.log t := by
        apply Real.log_le_log (by positivity)
        exact ht.1
      constructor
      · dsimp [FriableAsymptotic.logRatio]
        apply (le_div_iff₀ hlogt).2
        simpa using hlogtX
      · dsimp [FriableAsymptotic.logRatio]
        apply (div_le_iff₀ hlogt).2
        nlinarith
    have hpnt := FriableAsymptotic.dickmanPrimeSum_pnt_bound_closed_top
      X hX1 hC.le hbound hX₀y hy2 hyXlt hq
    have hpnt' :
        |(∑ p ∈ roughReversePrimeInterval y X,
            FriableAsymptotic.dickmanPrimeSummand X p) -
          (FriableAsymptotic.dickmanAntiderivative (X : ℝ) (X : ℝ) -
            FriableAsymptotic.dickmanAntiderivative (X : ℝ) (y : ℝ))| ≤
          500 * C * (X : ℝ) / Real.log (y : ℝ) +
            2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) := by
      simpa only [roughReversePrimeInterval] using hpnt
    have hrem := hremainder hYᵣy hy2 hX1 hlogX
    have hlogXpos : 0 < Real.log (X : ℝ) :=
      hlogy.trans_le (Real.log_le_log (by positivity) (by exact_mod_cast hyX))
    have htop :
        FriableAsymptotic.dickmanAntiderivative (X : ℝ) (X : ℝ) =
          (X : ℝ) := by
      unfold FriableAsymptotic.dickmanAntiderivative
      rw [div_self hlogXpos.ne', rho_one]
      ring
    have hbottom :
        FriableAsymptotic.dickmanAntiderivative (X : ℝ) (y : ℝ) =
          roughFriableDickmanMain X y := by
      rfl
    have hdefect : roughFriableReverseContinuousDefect X y X =
        -((∑ p ∈ roughReversePrimeInterval y X,
              FriableAsymptotic.dickmanPrimeSummand X p) -
          (FriableAsymptotic.dickmanAntiderivative (X : ℝ) (X : ℝ) -
            FriableAsymptotic.dickmanAntiderivative (X : ℝ) (y : ℝ))) := by
      unfold roughFriableReverseContinuousDefect
      rw [htop, hbottom]
      ring
    rw [hdefect, abs_neg]
    calc
      _ ≤ 500 * C * (X : ℝ) / Real.log (y : ℝ) +
            2 * (X : ℝ) * (6 + 8 * Real.log (X : ℝ)) / (y : ℝ) :=
        hpnt'
      _ ≤ 500 * C * (X : ℝ) / Real.log (y : ℝ) +
            (X : ℝ) / Real.log (y : ℝ) :=
        add_le_add le_rfl hrem
      _ = K * (X : ℝ) / Real.log (y : ℝ) := by
        dsimp [K]
        ring

/-- Consequently the complete deterministic reverse main defect has the
verified cumulative endpoint bound with the explicit additional constant
`3 * log 4` coming from quotient floors. -/
theorem exists_uniform_roughFriableReverseMainDefect_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → y ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughFriableReverseMainDefect X y X| ≤
        K * (X : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨Kₒ, hKₒ, Yₒ, hcontinuous⟩ :=
    exists_uniform_roughFriableReverseContinuousDefect_bound
  let K : ℝ := Kₒ + 3 * Real.log 4
  let Y₀ : ℕ := max 2 Yₒ
  have hK : 0 < K := by
    dsimp [K]
    have hlog4 : 0 < Real.log (4 : ℝ) := Real.log_pos (by norm_num)
    positivity
  refine ⟨K, hK, Y₀, ?_⟩
  intro X y hY hyX hlogX
  have hy2 : 2 ≤ y :=
    (le_max_left 2 Yₒ).trans (by simpa only [Y₀] using hY)
  have hYₒ : Yₒ ≤ y :=
    (le_max_right 2 Yₒ).trans (by simpa only [Y₀] using hY)
  rw [roughFriableReverseMainDefect_eq_continuous_add_floor]
  calc
    |roughFriableReverseContinuousDefect X y X +
        roughFriableReverseFloorDiscrepancy X y X| ≤
      |roughFriableReverseContinuousDefect X y X| +
        |roughFriableReverseFloorDiscrepancy X y X| := abs_add_le _ _
    _ ≤ Kₒ * (X : ℝ) / Real.log (y : ℝ) +
        3 * Real.log 4 * (X : ℝ) / Real.log (y : ℝ) :=
      add_le_add (hcontinuous hYₒ hyX hlogX)
        (roughFriableReverseFloorDiscrepancy_abs_le_endpointScale
          hy2 hlogX)
    _ = K * (X : ℝ) / Real.log (y : ℝ) := by
      dsimp [K]
      ring

/-! ## Face seminorm and the genuinely local prime ledger -/

/-- Local residual regularity on one specified Dickman face.  The zero lower
endpoint is included because a quotient interval is born at a prime. -/
def RoughFriableResidualFaceRegularity
    (m : ℕ) (C : ℝ) (Y₀ : ℕ) : Prop :=
  ∀ {A B y : ℕ},
    Y₀ ≤ y → 2 ≤ y → A ≤ B →
    Real.log (B : ℝ) ≤ (m : ℝ) * Real.log (y : ℝ) →
    |roughFriableResidual B y - roughFriableResidual A y| ≤
      C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) + 1

/-- The pointwise cost supplied by a lower-face induction hypothesis.  Equal
integer quotients cost exactly zero; this avoids charging all primes in the
reverse interval indiscriminately. -/
noncomputable def roughFriableResidualQuotientCost
    (C : ℝ) (A B p : ℕ) : ℝ :=
  if A / p = B / p then 0
  else C * (((B / p) - (A / p) : ℕ) : ℝ) /
      Real.log (p : ℝ) + 1

/-- The common-prime sum of residual increments.  Every summand is on a
strictly lower Dickman face. -/
noncomputable def roughFriableLowerFacePrimeIncrementSum
    (A B y : ℕ) : ℝ :=
  ∑ p ∈ roughReversePrimeInterval y B,
    (roughFriableResidual (B / p) p -
      roughFriableResidual (A / p) p)

/-- The exact local prime-transition ledger left by reverse Buchstab.  The
absolute value is taken only after the main defect and the lower-face prime
sum are combined, retaining precisely the cancellation that a termwise
triangle inequality would destroy. -/
noncomputable def roughFriablePrimeTransitionLedger
    (A B y : ℕ) : ℝ :=
  |(roughFriableReverseMainDefect B y B -
      roughFriableReverseMainDefect A y B) -
    roughFriableLowerFacePrimeIncrementSum A B y|

/-- The one analytic short-prime-sum cancellation estimate not supplied by
the current libraries.  Its premise is exactly the pointwise estimate
delivered by the lower-face induction hypothesis.  It is required only for
the four transitions `1→2→3→4→5`; its conclusion contains neither the
target residual increment nor a selector-level premise. -/
def RoughFriablePrimeTransitionEstimateUpToFive
    (C : ℝ) (Y₀ : ℕ) : Prop :=
  ∀ {m A B y : ℕ},
    1 ≤ m → m < 5 → Y₀ ≤ y → 2 ≤ y → y < B → A ≤ B →
    Real.log (B : ℝ) ≤ ((m + 1 : ℕ) : ℝ) * Real.log (y : ℝ) →
    (∀ p ∈ roughReversePrimeInterval y B,
      |roughFriableResidual (B / p) p -
          roughFriableResidual (A / p) p| ≤
        roughFriableResidualQuotientCost C A B p) →
    roughFriablePrimeTransitionLedger A B y ≤
      C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) + 1

/-- The transition ledger is exactly the target residual increment after the
common-cutoff recurrence is applied.  This identity is recorded to prevent
the open analytic estimate from being mistaken for a consequence of a
termwise triangle inequality. -/
theorem roughFriablePrimeTransitionLedger_eq_residualDifference
    {A B y : ℕ} (hyB : y ≤ B) (hAB : A ≤ B) :
    roughFriablePrimeTransitionLedger A B y =
      |roughFriableResidual B y - roughFriableResidual A y| := by
  unfold roughFriablePrimeTransitionLedger
    roughFriableLowerFacePrimeIncrementSum
  rw [roughFriableResidual_difference_reverseRecurrence_all
    (X₀ := A) (X₁ := B) (Z := B) hyB hAB le_rfl]

/-- Exact analytic decomposition of the local ledger: continuous PNT
finite difference, quotient-floor finite difference, and the lower-face
residual prime sum. -/
theorem roughFriablePrimeTransitionLedger_eq_continuous_floor_lower
    (A B y : ℕ) :
    roughFriablePrimeTransitionLedger A B y =
      |(roughFriableReverseContinuousDefect B y B -
          roughFriableReverseContinuousDefect A y B) +
        (roughFriableReverseFloorDiscrepancy B y B -
          roughFriableReverseFloorDiscrepancy A y B) -
        roughFriableLowerFacePrimeIncrementSum A B y| := by
  unfold roughFriablePrimeTransitionLedger
  rw [roughFriableReverseMainDefect_eq_continuous_add_floor,
    roughFriableReverseMainDefect_eq_continuous_add_floor]
  congr 1
  ring

/-- What the verified de Bruijn/PNT machinery gives for the exact local prime
ledger without a new short-transition argument: the broad two-endpoint scale
`(A+B)/log y`.  It does not replace the desired `(B-A)/log y + 1` bound. -/
theorem exists_uniform_roughFriablePrimeTransitionLedger_broad_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {A B y : ℕ},
      Y₀ ≤ y → 2 ≤ y → A ≤ B → y ≤ B →
      Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ) →
      roughFriablePrimeTransitionLedger A B y ≤
        K * ((A : ℝ) + (B : ℝ)) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₀, hresidual⟩ :=
    exists_uniform_roughFriableResidual_bound
  refine ⟨K, hK, Y₀, ?_⟩
  intro A B y hY hy2 hAB hyB hlogB
  have hBpos : 0 < B := (show 0 < y by omega).trans_le hyB
  have hBbound : |roughFriableResidual B y| ≤
      K * (B : ℝ) / Real.log (y : ℝ) :=
    hresidual hY hBpos hlogB
  rw [roughFriablePrimeTransitionLedger_eq_residualDifference hyB hAB]
  by_cases hA : A = 0
  · subst A
    simpa using hBbound
  · have hApos : 0 < A := Nat.pos_of_ne_zero hA
    have hlogA : Real.log (A : ℝ) ≤ Real.log (B : ℝ) :=
      Real.log_le_log (by exact_mod_cast hApos) (by exact_mod_cast hAB)
    have hAbound : |roughFriableResidual A y| ≤
        K * (A : ℝ) / Real.log (y : ℝ) :=
      hresidual hY hApos (hlogA.trans hlogB)
    calc
      |roughFriableResidual B y - roughFriableResidual A y| ≤
          |roughFriableResidual B y| + |roughFriableResidual A y| :=
        abs_sub _ _
      _ ≤ K * (B : ℝ) / Real.log (y : ℝ) +
          K * (A : ℝ) / Real.log (y : ℝ) :=
        add_le_add hBbound hAbound
      _ = K * ((A : ℝ) + (B : ℝ)) / Real.log (y : ℝ) := by
        ring

/-- The verified broad estimate already gives the desired gap scale away
from the diagonal.  Thus only pairs with `B < 2*A` require the new local
prime-transition input. -/
theorem exists_uniform_roughFriablePrimeTransitionLedger_wideGap_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ {A B y : ℕ},
      Y₀ ≤ y → 2 ≤ y → A ≤ B → 2 * A ≤ B → y ≤ B →
      Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ) →
      roughFriablePrimeTransitionLedger A B y ≤
        C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
  obtain ⟨K, hK, Y₀, hbroad⟩ :=
    exists_uniform_roughFriablePrimeTransitionLedger_broad_bound
  let C : ℝ := 3 * K
  refine ⟨C, by dsimp [C]; positivity, Y₀, ?_⟩
  intro A B y hY hy2 hAB hwide hyB hlogB
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hwideR : (2 : ℝ) * (A : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hwide
  have hgapCast : ((B - A : ℕ) : ℝ) = (B : ℝ) - (A : ℝ) := by
    rw [Nat.cast_sub hAB]
  have hsumGap : (A : ℝ) + (B : ℝ) ≤
      3 * ((B - A : ℕ) : ℝ) := by
    rw [hgapCast]
    linarith
  calc
    roughFriablePrimeTransitionLedger A B y ≤
        K * ((A : ℝ) + (B : ℝ)) / Real.log (y : ℝ) :=
      hbroad hY hy2 hAB hyB hlogB
    _ ≤ K * (3 * ((B - A : ℕ) : ℝ)) / Real.log (y : ℝ) := by
      apply div_le_div_of_nonneg_right _ hlogy.le
      exact mul_le_mul_of_nonneg_left hsumGap hK.le
    _ = C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) := by
      dsimp [C]
      ring

/-! ## The quotient really lies on the lower face -/

theorem roughReverseQuotient_log_le_lowerFace
    {m B y p : ℕ} (hy2 : 2 ≤ y) (hyp : y < p) (hpB : p ≤ B)
    (hlogB : Real.log (B : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * Real.log (y : ℝ)) :
    Real.log ((B / p : ℕ) : ℝ) ≤
      (m : ℝ) * Real.log (p : ℝ) := by
  have hp0 : 0 < p := by omega
  have hB0 : 0 < B := hp0.trans_le hpB
  have hquot : 1 ≤ B / p := by
    apply (Nat.le_div_iff_mul_le hp0).2
    simpa using hpB
  have hcast : ((B / p : ℕ) : ℝ) ≤ (B : ℝ) / (p : ℝ) :=
    Nat.cast_div_le
  have hlogFloor : Real.log ((B / p : ℕ) : ℝ) ≤
      Real.log ((B : ℝ) / (p : ℝ)) := by
    exact Real.log_le_log (by exact_mod_cast hquot) hcast
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < p by omega))
  have hlogyp : Real.log (y : ℝ) ≤ Real.log (p : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast hyp.le)
  have hlogB' : Real.log (B : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * Real.log (p : ℝ) :=
    hlogB.trans (mul_le_mul_of_nonneg_left hlogyp (by positivity))
  calc
    Real.log ((B / p : ℕ) : ℝ) ≤
        Real.log ((B : ℝ) / (p : ℝ)) := hlogFloor
    _ = Real.log (B : ℝ) - Real.log (p : ℝ) := by
      rw [Real.log_div (by exact_mod_cast hB0.ne')
        (by exact_mod_cast hp0.ne')]
    _ ≤ (m : ℝ) * Real.log (p : ℝ) := by
      norm_num only [Nat.cast_add, Nat.cast_one] at hlogB'
      linarith

/-! ## Literal method-of-steps induction -/

/-- Initial-face vanishing with the zero lower endpoint included. -/
theorem roughFriableResidual_localRegularity_initial_all
    {A B y : ℕ} (hAB : A ≤ B) (hy : 1 < y) (hBy : B ≤ y) :
    |roughFriableResidual B y - roughFriableResidual A y| = 0 := by
  by_cases hB : B = 0
  · have hA : A = 0 := by omega
    subst A
    subst B
    simp
  · have hBpos : 0 < B := Nat.pos_of_ne_zero hB
    have hBzero := roughFriableResidual_eq_zero_of_le hBpos hy hBy
    by_cases hA : A = 0
    · subst A
      rw [roughFriableResidual_zero, hBzero, sub_zero, abs_zero]
    · exact roughFriableResidual_localRegularity_initial
        (Nat.pos_of_ne_zero hA) hAB hy hBy

/-- Face one is closed with no analytic prime-sum input. -/
theorem roughFriableResidual_faceRegularity_one
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C) :
    RoughFriableResidualFaceRegularity 1 C Y₀ := by
  intro A B y _hY hy2 hAB hlogB
  have hBy : B ≤ y := by
    by_contra hnot
    have hyB : y < B := lt_of_not_ge hnot
    have hypos : (0 : ℝ) < (y : ℝ) := by positivity
    have hBpos : (0 : ℝ) < (B : ℝ) :=
      hypos.trans (by exact_mod_cast hyB)
    have hstrict : Real.log (y : ℝ) < Real.log (B : ℝ) :=
      Real.strictMonoOn_log hypos hBpos (by exact_mod_cast hyB)
    norm_num at hlogB
    linarith
  rw [roughFriableResidual_localRegularity_initial_all hAB
    (show 1 < y by omega) hBy]
  have hlogy : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  positivity

/-- One reverse-Buchstab step.  Every residual appearing in the prime sum
is discharged by the supplied lower-face hypothesis; the target face is
never assumed. -/
theorem roughFriableResidual_faceRegularity_step
    {m : ℕ} {C : ℝ} {Y₀ : ℕ}
    (hC : 0 ≤ C) (hm : 1 ≤ m) (hm5 : m < 5)
    (hprime : RoughFriablePrimeTransitionEstimateUpToFive C Y₀)
    (hlower : RoughFriableResidualFaceRegularity m C Y₀) :
    RoughFriableResidualFaceRegularity (m + 1) C Y₀ := by
  intro A B y hY hy2 hAB hlogB
  by_cases hBy : B ≤ y
  · rw [roughFriableResidual_localRegularity_initial_all hAB
      (show 1 < y by omega) hBy]
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity
  · have hyB : y < B := lt_of_not_ge hBy
    have hrec := roughFriableResidual_difference_reverseRecurrence_all
      (X₀ := A) (X₁ := B) (Z := B) hyB.le hAB le_rfl
    have hlowerPrime : ∀ p ∈ roughReversePrimeInterval y B,
        |roughFriableResidual (B / p) p -
            roughFriableResidual (A / p) p| ≤
          roughFriableResidualQuotientCost C A B p := by
      intro p hp
      by_cases heq : A / p = B / p
      · simp [roughFriableResidualQuotientCost, heq]
      · have hpprime : p.Prime := roughReversePrimeInterval_prime hp
        have hyp : y < p := roughReversePrimeInterval_gt_left hp
        have hpB : p ≤ B := roughReversePrimeInterval_le_right hp
        have hquotient : A / p ≤ B / p :=
          Nat.div_le_div_right hAB
        have hquotientLog : Real.log ((B / p : ℕ) : ℝ) ≤
            (m : ℝ) * Real.log (p : ℝ) :=
          roughReverseQuotient_log_le_lowerFace
            hy2 hyp hpB hlogB
        rw [roughFriableResidualQuotientCost, if_neg heq]
        exact hlower (hY.trans hyp.le) hpprime.two_le
          hquotient hquotientLog
    rw [hrec]
    simpa only [roughFriablePrimeTransitionLedger,
      roughFriableLowerFacePrimeIncrementSum] using
      hprime hm hm5 hY hy2 hyB hAB hlogB hlowerPrime

/-- The four transitions are expanded literally.  Thus the face-five
conclusion depends only on the unconditional face-one theorem and the single
prime-transition estimate, not on a face-five regularity premise. -/
theorem roughFriableResidual_faceRegularity_one_to_five
    {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hprime : RoughFriablePrimeTransitionEstimateUpToFive C Y₀) :
    RoughFriableResidualFaceRegularity 1 C Y₀ ∧
      RoughFriableResidualFaceRegularity 2 C Y₀ ∧
      RoughFriableResidualFaceRegularity 3 C Y₀ ∧
      RoughFriableResidualFaceRegularity 4 C Y₀ ∧
      RoughFriableResidualFaceRegularity 5 C Y₀ := by
  have h1 : RoughFriableResidualFaceRegularity 1 C Y₀ :=
    roughFriableResidual_faceRegularity_one hC
  have h2 : RoughFriableResidualFaceRegularity 2 C Y₀ := by
    exact roughFriableResidual_faceRegularity_step
      (m := 1) hC (by norm_num) (by norm_num) hprime h1
  have h3 : RoughFriableResidualFaceRegularity 3 C Y₀ := by
    exact roughFriableResidual_faceRegularity_step
      (m := 2) hC (by norm_num) (by norm_num) hprime h2
  have h4 : RoughFriableResidualFaceRegularity 4 C Y₀ := by
    exact roughFriableResidual_faceRegularity_step
      (m := 3) hC (by norm_num) (by norm_num) hprime h3
  have h5 : RoughFriableResidualFaceRegularity 5 C Y₀ := by
    exact roughFriableResidual_faceRegularity_step
      (m := 4) hC (by norm_num) (by norm_num) hprime h4
  exact ⟨h1, h2, h3, h4, h5⟩

/-- Conditional closure of the precise local regularity input used by the
four-endpoint Section 6 reduction. -/
theorem roughFriableResidual_localRegularity_of_primeTransition
    {C : ℝ} {Y₀ y : ℕ} (hC : 0 ≤ C)
    (hprime : RoughFriablePrimeTransitionEstimateUpToFive C Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y) :
    RoughFriableResidualLocalRegularity C y := by
  have h5 : RoughFriableResidualFaceRegularity 5 C Y₀ :=
    (roughFriableResidual_faceRegularity_one_to_five hC hprime).2.2.2.2
  intro A B _hA hAB hlogB
  exact h5 (A := A) (B := B) (y := y) hY hy2 hAB
    (by simpa using hlogB)

end

end Erdos390.WholePaper
