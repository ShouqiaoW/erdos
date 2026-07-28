import Erdos390.WholePaper.BankPaperCanonicalSectionNineAbsorbed

/-! # Expanded statement audit for absorbed canonical Section 9 -/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperCanonicalSectionNineAbsorbedStatementAudit

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete public declaration census, in source order -/

#check Erdos390.WholePaper.BankPaperRealization.eventually_canonicalSectionNineCleanListLower_absorbed
#check Erdos390.WholePaper.BankPaperRealization.eventually_exists_canonicalSectionNinePostTangentOutput_absorbed

/-! This expanded terminal visibly contains no common-list interval premise,
candidate-floor/loss premise, or request-wise list-card premise. -/

example (W K : ℕ) {c r0 deltaStar : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (depth : ℕ),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
        (pivot : BankPaperCanonicalTangentPrime n W)
        (L sigma : ℝ),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        ((max
            (bankPaperCanonicalTangentRequestSource R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request)
            (bankPaperCanonicalTangentRequestTarget R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request) : ℕ) : ℝ) /
          ((min
            (bankPaperCanonicalTangentRequestSource R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request)
            (bankPaperCanonicalTangentRequestTarget R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request) : ℕ) : ℝ) ≤ r0) →
      K * upperTailLength c n ≤ n → 0 < n →
      (yNat n : ℝ) ≤ n → (yNat n : ℝ) ^ 2 ≤ n →
      0 < L → 0 < sigma →
      (∀ a ∈ fixed, 0 < a) →
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget →
      (∀ a ∈ roughRawCandidateSet n (upperTailLength c n) K,
        0 ≤ x a ∧ x a ≤ 1) →
      BankPaperCanonicalSelectorRowIntegral n
        (roughRawCandidateSet n (upperTailLength c n) K) x →
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed
          (roughRawCandidateSet n (upperTailLength c n) K) x →
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed
          (roughRawCandidateSet n (upperTailLength c n) K) x →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        ∀ multiplier,
          multiplier ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request →
          (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ∧
              x (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ∧
              x (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ≤ 1 - sigma / L)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        4 * (tangentSplitCensusTotalRequestUpper L sigma
              (tangentStarResidualL1
                (bankPaperCanonicalTangentResidual (W := W)
                  R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x))
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W)) / n) +
          ((bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request) / n) +
          ((bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request) / n) ≤
            tangentPaperCleanListDensity W r0 ^ 2 / 24) →
      ∃ multiplier : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma → ℕ,
        (∀ request,
          multiplier request ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot))
          (bankPaperCanonicalTangentRequestSource R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma)
          (bankPaperCanonicalTangentRequestTarget R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma)
          multiplier ∧
        ∃ output : BankPaperCanonicalPostTangentOutput R certificate
            (roughRawCandidateSet n (upperTailLength c n) K) fixed,
          output.selector =
            bankPaperCanonicalTangentUpdatedSelector R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot
                L sigma multiplier :=
  Erdos390.WholePaper.BankPaperRealization.eventually_exists_canonicalSectionNinePostTangentOutput_absorbed
      W K (c := c) (r0 := r0) (deltaStar := deltaStar)
      hc hr0one hr0three hdelta hdeltaUpper hmainSmall

end


end Erdos390.WholePaper.BankPaperCanonicalSectionNineAbsorbedStatementAudit
