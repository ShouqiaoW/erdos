import Erdos390.WholePaper.RoughSaiasSharpFixedHeadIntervalShift

/-! # Expanded statement audit for sharp fixed-head interval shifts -/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.DickmanBasic

noncomputable section

#check roughFriableContinuousFixedDivisorDefect
#check roughFriableMain_quotientFloor_stability
#check roughFriableContinuousFixedDivisorDefect_sub_abs_le
#check roughFriableDickmanMain_interval_fixedDivisorShift_abs_le
#check roughSaiasIntervalFixedDivisorShiftBudget
#check roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation
#check roughSaiasSharpIntervalFixedDivisorBudget
#check roughSaiasIntervalFixedDivisorShiftBudget_sharp_le
#check roughFriableInterval_fixedDivisorShift_abs_le_sharp
#check roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_sharp
#check roughSmoothPhysicalBlock_abs_le_rightEndpoint
#check roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_small
#check roughCanonicalSharpFixedHeadShiftBudget
#check roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget
#check roughCanonicalSharpFixedHeadShiftBudgetAllRows
#check roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget_allRows
#check roughCanonicalRawRowQuotaError_abs_le_three_mul_sharpAllowance

example {X y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdX : d ≤ X)
    (hlogX : Real.log (X : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableDickmanMain (X / d) y -
        (X : ℝ) / (d : ℝ) *
          rho (FriableAsymptotic.dickmanU X y -
            Real.log (d : ℝ) / Real.log (y : ℝ))| ≤ 3 :=
  roughFriableMain_quotientFloor_stability hy hd hdX hlogX

example {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughFriableContinuousFixedDivisorDefect B y d -
        roughFriableContinuousFixedDivisorDefect A y d| ≤
      ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) :=
  roughFriableContinuousFixedDivisorDefect_sub_abs_le
    hy hd hdA hAB hlogB

example {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |(roughFriableDickmanMain (B / d) y -
          roughFriableDickmanMain (A / d) y) -
        (roughFriableDickmanMain B y -
          roughFriableDickmanMain A y) / (d : ℝ)| ≤
      6 + ((B - A : ℕ) : ℝ) *
        (Real.log (d : ℝ) + 2) /
          ((d : ℝ) * Real.log (y : ℝ)) :=
  roughFriableDickmanMain_interval_fixedDivisorShift_abs_le
    hy hd hdA hAB hlogB

example (hBV : RoughCompactBVTranslationPrinciple)
    {eta : ℕ → ℝ} {Y₀ A B y d : ℕ}
    (happrox : RoughSaiasEndpointApproximationUpToFive eta Y₀)
    (hY : Y₀ ≤ y) (hy : 2 ≤ y)
    (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)| ≤
      roughSaiasIntervalFixedDivisorShiftBudget eta A B y d :=
  roughFriableInterval_fixedDivisorShift_abs_le_of_saiasEndpointApproximation
    hBV happrox hY hy hd hdA hAB hlogB

example {A B y d : ℕ}
    (hy : 2 ≤ y) (hd : 0 < d) (hAB : A ≤ B) :
    roughSaiasIntervalFixedDivisorShiftBudget
        (roughSaiasInvLogSqEndpointRate
          roughSaiasSharpDefectConstant) A B y d ≤
      roughSaiasSharpIntervalFixedDivisorBudget A B y d :=
  roughSaiasIntervalFixedDivisorShiftBudget_sharp_le hy hd hAB

example {A B y d : ℕ}
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hd : 0 < d) (hdA : d ≤ A) (hAB : A ≤ B)
    (hlogB : Real.log (B : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |((FriableAsymptotic.friableCount (B / d) y : ℝ) -
          (FriableAsymptotic.friableCount (A / d) y : ℝ)) -
        ((FriableAsymptotic.friableCount B y : ℝ) -
          (FriableAsymptotic.friableCount A y : ℝ)) / (d : ℝ)| ≤
      roughSaiasSharpIntervalFixedDivisorBudget A B y d :=
  roughFriableInterval_fixedDivisorShift_abs_le_sharp
    hY hy hd hdA hAB hlogB

example {lo split hi y d : ℕ} {alpha broad : ℝ}
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hd : 0 < d) (hdLo : d ≤ lo)
    (hloSplit : lo ≤ split) (hSplitHi : split ≤ hi)
    (hlogHi : Real.log (hi : ℝ) ≤ 5 * Real.log (y : ℝ)) :
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      |alpha| *
          roughSaiasSharpIntervalFixedDivisorBudget split hi y d +
        |broad| *
          roughSaiasSharpIntervalFixedDivisorBudget lo split y d :=
  roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_sharp
    hY hy hd hdLo hloSplit hSplitHi hlogHi

example {W n h K y : ℕ} {alpha beta L : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hKh : K * h ≤ n)
    (hheadLo : roughHeadModulus W ≤ n / row.1)
    (hlogHi :
      Real.log (((2 * n) / row.1 : ℕ) : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    roughCanonicalFixedHeadShiftLedger
        W n h K y alpha beta L row ≤
      roughCanonicalSharpFixedHeadShiftBudget
        W n h K y alpha beta L row :=
  roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget
    row hY hy hKh hheadLo hlogHi

example {lo split hi y : ℕ} {alpha broad : ℝ}
    (hSplitHi : split ≤ hi) :
    |roughSmoothPhysicalBlock lo split hi y alpha broad| ≤
      (|alpha| + |broad|) * (hi : ℝ) :=
  roughSmoothPhysicalBlock_abs_le_rightEndpoint hSplitHi

example {lo split hi y d : ℕ} {alpha broad : ℝ}
    (hd : 0 < d) (hloSplit : lo ≤ split) (hSplitHi : split ≤ hi)
    (hhi : hi ≤ 2 * d) :
    |roughSmoothPhysicalBlock (lo / d) (split / d) (hi / d) y
          alpha broad -
        roughSmoothPhysicalBlock lo split hi y alpha broad / (d : ℝ)| ≤
      4 * (|alpha| + |broad|) :=
  roughSmoothPhysicalBlock_fixedDivisorShift_abs_le_small
    hd hloSplit hSplitHi hhi

example {W n h K y : ℕ} {alpha beta L : ℝ}
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y) (hKh : K * h ≤ n)
    (hlogHi :
      Real.log (((2 * n) / row.1 : ℕ) : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    roughCanonicalFixedHeadShiftLedger
        W n h K y alpha beta L row ≤
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n h K y alpha beta L row :=
  roughCanonicalFixedHeadShiftLedger_le_sharpIntervalBudget_allRows
    row hY hy hKh hlogHi

example {W n h K y : ℕ} {alpha beta L E : ℝ}
    (hWy : W ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n h K))
    (hrowN : row.1 ≤ n) (hKh : K * h ≤ n)
    (hY :
      roughSaiasInvLogSqEndpointCutoff roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + h) / row.1) ((2 * n) / row.1)
          ((2 * n - K * h) / row.1) (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ))
    (hmain : roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W) alpha beta L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (htransition : roughPhysicalSaiasTransitionBudget
        (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
        (roughHeadDensity W) alpha beta L
        ((2 * n + h) / row.1) ((2 * n) / row.1)
        ((2 * n - K * h) / row.1) (n / row.1) y ≤ E)
    (hhead :
      roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n h K y alpha beta L row ≤ E) :
    |roughCanonicalRawRowQuotaError
        W n h K y alpha beta L row| ≤ 3 * E :=
  roughCanonicalRawRowQuotaError_abs_le_three_mul_sharpAllowance
    hWy row hrowN hKh hY hy hlogs hmain htransition hhead

end

end Erdos390.WholePaper
