import Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale

/-! # Expanded statement audit for the balanced canonical sharp row scale -/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

#check roughHeadDensity_le_one
#check roughHeadBalancedAlpha_abs_le_of_tail_lower
#check roughHeadBalancedAlpha_succ_abs_le
#check roughBalancedAlphaConstant
#check roughBalancedAlphaConstant_nonneg
#check roughCanonicalSharpMainRowScaleConstant
#check roughCanonicalSharpTransitionRowScaleConstant
#check roughCanonicalSharpHeadDivisorRowScaleConstant
#check roughCanonicalSharpHeadRowScaleConstant
#check roughCanonicalSharpUnifiedRowScaleConstant
#check roughNatQuotient_sub_realQuotient_abs_lt_one
#check roughRealQuotient_lt_natQuotient_add_one
#check roughQuotientGap_cast_le
#check roughTwoQuotient_le_three_halfQuotient
#check roughUpperQuotient_le_three_centralQuotient
#check roughLowerEndpoint_mul_logRatio_le_gap
#check roughUpperEndpoint_mul_logRatio_le_three_gap
#check roughDickmanUpperWeightedDisplacement_le_three_gap
#check roughDickmanLowerWeightedDisplacement_le_gap
#check roughTail_div_row_cast_le
#check roughRowScale_elementary
#check roughBalancedCanonicalContinuousFirstMoment_eq_zero
#check roughBalancedCanonicalNaturalFirstMoment_abs_le
#check sum_abs_roughPhysicalBlockCoefficient_le
#check roughPhysicalDickmanDisplacementSum_le_three_gaps
#check roughCanonicalBalancedDickmanTransitionLedger_le
#check roughCanonicalBalancedSaiasTransitionBudget_le
#check roughCanonicalBalancedSharpFixedHeadBudget_le
#check roughCanonicalSharpMainRowScaleConstant_nonneg
#check roughCanonicalSharpTransitionRowScaleConstant_nonneg
#check roughCanonicalSharpHeadDivisorRowScaleConstant_nonneg
#check roughCanonicalSharpHeadRowScaleConstant_nonneg
#check roughCanonicalSharpUnifiedRowScaleConstant_nonneg
#check roughCanonicalBalancedRawRowQuotaError_abs_le_unified

example
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n : ℕ} (hn : 2 ≤ n) :
    |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
        beta (L n)| ≤
      roughBalancedAlphaConstant W K0 c beta := by
  simpa only [roughBalancedAlphaConstant] using
    roughHeadBalancedAlpha_succ_abs_le W K0 hc hn

example
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n r y : ℕ} (hn : 2 ≤ n) (hr : 0 < r) (hrn : r ≤ n)
    (hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n)
    (htailPos : 0 < upperTailLength c n) :
    roughPhysicalDickmanTransitionLedger
        (roughHeadDensity W)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        ((2 * n + upperTailLength c n) / r)
        ((2 * n) / r)
        ((2 * n - (K0 + 1) * upperTailLength c n) / r)
        (n / r) y ≤
      roughCanonicalSharpMainRowScaleConstant W K0 c beta *
        (((n / r : ℕ) : ℝ) / L n ^ 2 + 1) :=
  roughCanonicalBalancedDickmanTransitionLedger_le
    W K0 hc hn hr hrn hy hLone hlogY htail hKh htailPos

example
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n r y : ℕ} (hn : 2 ≤ n) (hr : 0 < r) (hrn : r ≤ n)
    (hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n) :
    roughPhysicalSaiasTransitionBudget
        (roughSaiasInvLogSqEndpointRate roughSaiasSharpDefectConstant)
        (roughHeadDensity W)
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n)
        ((2 * n + upperTailLength c n) / r)
        ((2 * n) / r)
        ((2 * n - (K0 + 1) * upperTailLength c n) / r)
        (n / r) y ≤
      roughCanonicalSharpTransitionRowScaleConstant W K0 c beta *
        (((n / r : ℕ) : ℝ) / L n ^ 2 + 1) :=
  roughCanonicalBalancedSaiasTransitionBudget_le
    W K0 hc hn hr hrn hy hLone hlogY htail hKh

example
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n y : ℕ} (hn : 2 ≤ n) (hy : 2 ≤ y)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hrowN : row.1 ≤ n)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n) :
    roughCanonicalSharpFixedHeadShiftBudgetAllRows
        W n (upperTailLength c n) (K0 + 1) y
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) row ≤
      roughCanonicalSharpHeadRowScaleConstant W K0 c beta *
        (((n / row.1 : ℕ) : ℝ) / L n ^ 2 + 1) :=
  roughCanonicalBalancedSharpFixedHeadBudget_le
    W K0 hc hn hy row hrowN hLone hlogY htail hKh

example
    (W K0 : ℕ) {c beta : ℝ} (hc : 0 < c)
    {n y : ℕ} (hn : 2 ≤ n)
    (row : CanonicalCompleteRoughRow y
      (roughRawCandidateSet n (upperTailLength c n) (K0 + 1)))
    (hrowN : row.1 ≤ n)
    (hWy : W ≤ y)
    (hY :
      roughSaiasInvLogSqEndpointCutoff
        roughSaiasSharpDefectCutoff ≤ y)
    (hy : 2 ≤ y)
    (hLone : 1 ≤ L n)
    (hlogY : L n / 5 ≤ Real.log (y : ℝ))
    (htail :
      (upperTailLength c n : ℝ) ≤
        2 * c * (n : ℝ) / L n)
    (hKh :
      (K0 + 1) * upperTailLength c n ≤ n)
    (htailPos : 0 < upperTailLength c n)
    (hlogs : ∀ i : Fin 4,
      Real.log (roughPhysicalNatEndpoint
          ((2 * n + upperTailLength c n) / row.1)
          ((2 * n) / row.1)
          ((2 * n - (K0 + 1) * upperTailLength c n) / row.1)
          (n / row.1) i : ℝ) ≤
        5 * Real.log (y : ℝ)) :
    |roughCanonicalRawRowQuotaError
        W n (upperTailLength c n) (K0 + 1) y
        (roughHeadBalancedAlpha W n (upperTailLength c n)
          (K0 + 1) beta (L n))
        beta (L n) row| ≤
      3 * (roughCanonicalSharpUnifiedRowScaleConstant W K0 c beta *
        ((((n / row.1 : ℕ) : ℝ)) / L n ^ 2 + 1)) :=
  roughCanonicalBalancedRawRowQuotaError_abs_le_unified
    W K0 hc hn row hrowN hWy hY hy hLone hlogY htail hKh
      htailPos hlogs

end

end Erdos390.WholePaper
