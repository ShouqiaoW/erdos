import Erdos390.WholePaper.RoughFriableFaceInduction

/-! # Expanded statement audit for five-face residual induction -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full

noncomputable section

example (X y Z : ℕ) :
    roughFriableReverseMainDefect X y Z =
      ((X : ℝ) - roughFriableDickmanMain X y -
        ∑ p ∈ ((Z + 1).primesBelow \ (y + 1).primesBelow),
          FriableAsymptotic.dickmanPrimeSummand X p) +
      ∑ p ∈ ((Z + 1).primesBelow \ (y + 1).primesBelow),
        (FriableAsymptotic.dickmanPrimeSummand X p -
          roughFriableDickmanMain (X / p) p) := by
  simpa only [roughFriableReverseContinuousDefect,
    roughFriableReverseFloorDiscrepancy, roughReversePrimeInterval] using
    roughFriableReverseMainDefect_eq_continuous_add_floor X y Z

example {X y : ℕ} (hy2 : 2 ≤ y)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |∑ p ∈ ((X + 1).primesBelow \ (y + 1).primesBelow),
        (FriableAsymptotic.dickmanPrimeSummand X p -
          roughFriableDickmanMain (X / p) p)| ≤
      3 * Real.log 4 * (X : ℝ) / Real.log (y : ℝ) := by
  simpa only [roughFriableReverseFloorDiscrepancy,
    roughReversePrimeInterval] using
    roughFriableReverseFloorDiscrepancy_abs_le_endpointScale hy2 hlog

example {A B y : ℕ} (hy2 : 2 ≤ y) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(∑ p ∈ ((B + 1).primesBelow \ (y + 1).primesBelow),
          (FriableAsymptotic.dickmanPrimeSummand B p -
            roughFriableDickmanMain (B / p) p)) -
        ∑ p ∈ ((B + 1).primesBelow \ (y + 1).primesBelow),
          (FriableAsymptotic.dickmanPrimeSummand A p -
            roughFriableDickmanMain (A / p) p)| ≤
      6 * Real.log 4 * (B : ℝ) / Real.log (y : ℝ) := by
  simpa only [roughFriableReverseFloorDiscrepancy,
    roughReversePrimeInterval] using
    roughFriableReverseFloorDiscrepancy_difference_abs_le_endpointScale
      hy2 hAB hlogB

example :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → y ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughFriableReverseMainDefect X y X| ≤
        K * (X : ℝ) / Real.log (y : ℝ) :=
  exists_uniform_roughFriableReverseMainDefect_bound

example {m B y p : ℕ} (hy2 : 2 ≤ y) (hyp : y < p) (hpB : p ≤ B)
    (hlogB : Real.log (B : ℝ) ≤
      ((m + 1 : ℕ) : ℝ) * Real.log (y : ℝ)) :
    Real.log ((B / p : ℕ) : ℝ) ≤
      (m : ℝ) * Real.log (p : ℝ) :=
  roughReverseQuotient_log_le_lowerFace hy2 hyp hpB hlogB

example {A B y : ℕ} (hyB : y ≤ B) (hAB : A ≤ B) :
    |(roughFriableReverseMainDefect B y B -
          roughFriableReverseMainDefect A y B) -
        ∑ p ∈ ((B + 1).primesBelow \ (y + 1).primesBelow),
          (roughFriableResidual (B / p) p -
            roughFriableResidual (A / p) p)| =
      |roughFriableResidual B y - roughFriableResidual A y| := by
  simpa only [roughFriablePrimeTransitionLedger,
    roughFriableLowerFacePrimeIncrementSum,
    roughReversePrimeInterval] using
    roughFriablePrimeTransitionLedger_eq_residualDifference hyB hAB

example (A B y : ℕ) :
    roughFriablePrimeTransitionLedger A B y =
      |(roughFriableReverseContinuousDefect B y B -
          roughFriableReverseContinuousDefect A y B) +
        (roughFriableReverseFloorDiscrepancy B y B -
          roughFriableReverseFloorDiscrepancy A y B) -
        roughFriableLowerFacePrimeIncrementSum A B y| :=
  roughFriablePrimeTransitionLedger_eq_continuous_floor_lower A B y

example :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {A B y : ℕ},
      Y₀ ≤ y → 2 ≤ y → A ≤ B → y ≤ B →
      Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ) →
      roughFriablePrimeTransitionLedger A B y ≤
        K * ((A : ℝ) + (B : ℝ)) / Real.log (y : ℝ) :=
  exists_uniform_roughFriablePrimeTransitionLedger_broad_bound

example :
    ∃ C : ℝ, 0 < C ∧ ∃ Y₀ : ℕ, ∀ {A B y : ℕ},
      Y₀ ≤ y → 2 ≤ y → A ≤ B → 2 * A ≤ B → y ≤ B →
      Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ) →
      roughFriablePrimeTransitionLedger A B y ≤
        C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) :=
  exists_uniform_roughFriablePrimeTransitionLedger_wideGap_bound

example {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C)
    (hprime :
      ∀ {m A B y : ℕ},
        1 ≤ m → m < 5 → Y₀ ≤ y → 2 ≤ y → y < B → A ≤ B →
        Real.log (B : ℝ) ≤
          ((m + 1 : ℕ) : ℝ) * Real.log (y : ℝ) →
        (∀ p ∈ ((B + 1).primesBelow \ (y + 1).primesBelow),
          |roughFriableResidual (B / p) p -
              roughFriableResidual (A / p) p| ≤
            (if A / p = B / p then 0
             else C * (((B / p) - (A / p) : ℕ) : ℝ) /
                Real.log (p : ℝ) + 1)) →
        |(roughFriableReverseMainDefect B y B -
            roughFriableReverseMainDefect A y B) -
          ∑ p ∈ ((B + 1).primesBelow \ (y + 1).primesBelow),
            (roughFriableResidual (B / p) p -
              roughFriableResidual (A / p) p)| ≤
          C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) + 1) :
    RoughFriableResidualFaceRegularity 1 C Y₀ ∧
      RoughFriableResidualFaceRegularity 2 C Y₀ ∧
      RoughFriableResidualFaceRegularity 3 C Y₀ ∧
      RoughFriableResidualFaceRegularity 4 C Y₀ ∧
      RoughFriableResidualFaceRegularity 5 C Y₀ := by
  apply roughFriableResidual_faceRegularity_one_to_five hC
  intro m A B y hm hm5 hY hy2 hyB hAB hlogB hlower
  simpa only [roughFriablePrimeTransitionLedger,
    roughFriableLowerFacePrimeIncrementSum,
    roughFriableResidualQuotientCost, roughReversePrimeInterval] using
    hprime hm hm5 hY hy2 hyB hAB hlogB (by
      intro p hp
      exact hlower p (by simpa only [roughReversePrimeInterval] using hp))

example {C : ℝ} {Y₀ y : ℕ} (hC : 0 ≤ C)
    (hprime : RoughFriablePrimeTransitionEstimateUpToFive C Y₀)
    (hY : Y₀ ≤ y) (hy2 : 2 ≤ y) :
    ∀ {A B : ℕ}, 0 < A → A ≤ B →
      Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughFriableResidual B y - roughFriableResidual A y| ≤
        C * ((B - A : ℕ) : ℝ) / Real.log (y : ℝ) + 1 := by
  exact roughFriableResidual_localRegularity_of_primeTransition
    hC hprime hY hy2

/-! ## Supporting public API -/

example {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    p.Prime :=
  roughReversePrimeInterval_prime hp

example {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    y < p :=
  roughReversePrimeInterval_gt_left hp

example {p y Z : ℕ} (hp : p ∈ roughReversePrimeInterval y Z) :
    p ≤ Z :=
  roughReversePrimeInterval_le_right hp

example {X y : ℕ} (hy2 : 2 ≤ y)
    (hlog : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableReverseFloorDiscrepancy X y X| ≤
      3 * ((roughReversePrimeInterval y X).card : ℝ) :=
  roughFriableReverseFloorDiscrepancy_abs_le_card hy2 hlog

example {X y Z p : ℕ} (hy2 : 2 ≤ y)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ))
    (hp : p ∈ roughReversePrimeInterval y Z) :
    |FriableAsymptotic.dickmanPrimeSummand X p -
        roughFriableDickmanMain (X / p) p| ≤ 3 :=
  roughFriableReverseFloorTerm_abs_le_three hy2 hlogX hp

example :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ {X y : ℕ},
      Y₀ ≤ y → y ≤ X →
      Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ) →
      |roughFriableReverseContinuousDefect X y X| ≤
        K * (X : ℝ) / Real.log (y : ℝ) :=
  exists_uniform_roughFriableReverseContinuousDefect_bound

example {A B y : ℕ} (hAB : A ≤ B) (hy : 1 < y) (hBy : B ≤ y) :
    |roughFriableResidual B y - roughFriableResidual A y| = 0 :=
  roughFriableResidual_localRegularity_initial_all hAB hy hBy

example {C : ℝ} {Y₀ : ℕ} (hC : 0 ≤ C) :
    RoughFriableResidualFaceRegularity 1 C Y₀ :=
  roughFriableResidual_faceRegularity_one hC

example {m : ℕ} {C : ℝ} {Y₀ : ℕ}
    (hC : 0 ≤ C) (hm : 1 ≤ m) (hm5 : m < 5)
    (hprime : RoughFriablePrimeTransitionEstimateUpToFive C Y₀)
    (hlower : RoughFriableResidualFaceRegularity m C Y₀) :
    RoughFriableResidualFaceRegularity (m + 1) C Y₀ :=
  roughFriableResidual_faceRegularity_step hC hm hm5 hprime hlower

end

end Erdos390.WholePaper
