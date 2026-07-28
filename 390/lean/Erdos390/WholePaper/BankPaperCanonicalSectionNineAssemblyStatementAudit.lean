import Erdos390.WholePaper.BankPaperCanonicalSectionNineAssembly

/-! # Expanded statement audit for the canonical Section 9 assembly -/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperCanonicalSectionNineAssemblyStatementAudit

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Complete public declaration census -/

#check bankPaperCanonicalTangentEdges
#check bankPaperCanonicalTangentEdgeFlow
#check BankPaperCanonicalTangentSplitRequest
#check bankPaperCanonicalTangentRequestSource
#check bankPaperCanonicalTangentRequestTarget
#check bankPaperCanonicalTangentLowerCard
#check bankPaperCanonicalTangentUpdatedSelector
#check tangentSplitCleanMultiplier_pos
#check tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
#check tangentSplitEndpoints_completeRoughLabel_eq
#check BankPaperRealization.exists_canonicalSectionNinePostTangentOutput_of_cleanListLower
#check BankPaperRealization.eventually_exists_canonicalSectionNinePostTangentOutput
#check BankPaperRealization.eventually_canonicalSectionNineCleanListLower
#check BankPaperRealization.canonicalPostTangentContinuationData_of_output

example
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) :
    bankPaperCanonicalTangentEdges
        R certificate fixed candidates x pivot =
      tangentStarPositiveEdges pivot
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates x) ∧
    (∀ edge,
      bankPaperCanonicalTangentEdgeFlow
          R certificate fixed candidates x pivot edge =
        tangentStarEdgeFlow pivot
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates x) edge) := by
  exact ⟨rfl, fun _edge ↦ rfl⟩

example
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) (L sigma : ℝ)
    (multiplier : BankPaperCanonicalTangentSplitRequest
      R certificate fixed candidates x pivot L sigma → ℕ) :
    bankPaperCanonicalTangentUpdatedSelector
        R certificate fixed candidates x pivot L sigma multiplier =
      tangentUpdate
        (tangentSplitRequests
          (bankPaperCanonicalTangentEdges
            R certificate fixed candidates x pivot)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed candidates x pivot))
        (bankPaperCanonicalTangentRequestSource
          R certificate fixed candidates x pivot L sigma)
        (bankPaperCanonicalTangentRequestTarget
          R certificate fixed candidates x pivot L sigma)
        multiplier tangentSplitRequestWeight x := rfl

example
    {E : Type*} {edges : Finset E} {source target : E → ℕ}
    {L sigma : ℝ} {flow : E → ℝ}
    {n K h Phead X0 y : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : ℕ}
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    0 < multiplier :=
  tangentSplitCleanMultiplier_pos request hmultiplier

example
    {E : Type*} {edges : Finset E} {source target : E → ℕ}
    {L sigma : ℝ} {flow : E → ℝ}
    {n K h Phead X0 y : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : ℕ}
    (hsourcePos : 0 < tangentSplitRequestSource source request)
    (htargetPos : 0 < tangentSplitRequestTarget target request)
    (hKh : K * h ≤ n)
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    tangentSplitRequestSource source request * multiplier ∈
        roughRawCandidateSet n h K ∧
      tangentSplitRequestTarget target request * multiplier ∈
        roughRawCandidateSet n h K :=
  tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
    request hsourcePos htargetPos hKh hmultiplier

example
    {y source target multiplier : ℕ}
    (hsourcePos : 0 < source) (htargetPos : 0 < target)
    (hsourceLe : source ≤ y) (htargetLe : target ≤ y)
    (hmultiplierPos : 0 < multiplier) :
    completeRoughLabel y (source * multiplier) =
      completeRoughLabel y (target * multiplier) :=
  tangentSplitEndpoints_completeRoughLabel_eq
    hsourcePos htargetPos hsourceLe htargetLe hmultiplierPos

example
    {c : ℝ} {depth n W K h X0 : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W)
    (density L sigma : ℝ)
    (hKh : K * h ≤ n)
    (hn : 0 < n) (hyLe : (yNat n : ℝ) ≤ n)
    (hySq : (yNat n : ℝ) ^ 2 ≤ n)
    (hdensity : 0 < density) (hL : 0 < L) (hsigma : 0 < sigma)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hfeasible : ∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ x a ∧ x a ≤ 1)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral n
      (roughRawCandidateSet n h K) x)
    (hbalance : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed (roughRawCandidateSet n h K) x)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed (roughRawCandidateSet n h K) x)
    (hlowerPos : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      0 < bankPaperCanonicalTangentLowerCard
        R certificate fixed (roughRawCandidateSet n h K) x pivot
          L sigma density request)
    (hlower : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      bankPaperCanonicalTangentLowerCard
          R certificate fixed (roughRawCandidateSet n h K) x pivot
            L sigma density request ≤
        (tangentSplitCleanMultiplierLists
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      ∀ side,
        density * n ≤
          (bankPaperCanonicalTangentLowerCard
            R certificate fixed (roughRawCandidateSet n h K) x pivot
              L sigma density request : ℝ) *
            tangentEndpointLabel
              (bankPaperCanonicalTangentRequestSource
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma)
              (bankPaperCanonicalTangentRequestTarget
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma) side request)
    (hslack : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      ∀ multiplier,
        multiplier ∈ tangentSplitCleanMultiplierLists
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request →
        (sigma / L ≤ x
              (bankPaperCanonicalTangentRequestSource
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ∧
            x (bankPaperCanonicalTangentRequestSource
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ≤ 1 - sigma / L) ∧
          (sigma / L ≤ x
              (bankPaperCanonicalTangentRequestTarget
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ∧
            x (bankPaperCanonicalTangentRequestTarget
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ≤ 1 - sigma / L))
    (hsmall : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      4 * (tangentSplitCensusTotalRequestUpper L sigma
            (tangentStarResidualL1
              (bankPaperCanonicalTangentResidual (W := W)
                R certificate fixed
                (roughRawCandidateSet n h K) x))
            (tangentStarSupportCount
              (BankPaperCanonicalTangentPrime n W)) / n) +
        ((bankPaperCanonicalTangentRequestSource
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentStarLabelIncidentTraffic pivot
              (bankPaperCanonicalTangentResidual R certificate fixed
                (roughRawCandidateSet n h K) x)
              bankPaperCanonicalTangentPrimeLabel)
            (tangentStarSupportCount
              (BankPaperCanonicalTangentPrime n W))
            (bankPaperCanonicalTangentRequestSource
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request) / n) +
        ((bankPaperCanonicalTangentRequestTarget
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentStarLabelIncidentTraffic pivot
              (bankPaperCanonicalTangentResidual R certificate fixed
                (roughRawCandidateSet n h K) x)
              bankPaperCanonicalTangentPrimeLabel)
            (tangentStarSupportCount
              (BankPaperCanonicalTangentPrime n W))
            (bankPaperCanonicalTangentRequestTarget
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request) / n) ≤ density ^ 2 / 24) :
    ∃ multiplier : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma → ℕ,
      (∀ request,
        multiplier request ∈ tangentSplitCleanMultiplierLists
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot))
        (bankPaperCanonicalTangentRequestSource
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma)
        (bankPaperCanonicalTangentRequestTarget
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma)
        multiplier ∧
      (∀ p : BankPaperCanonicalTangentPrime n W,
        tangentFlowDivergence
            (tangentStarFlow pivot
              (bankPaperCanonicalTangentResidual R certificate fixed
                (roughRawCandidateSet n h K) x)) p =
          bankPaperCanonicalTangentResidual R certificate fixed
            (roughRawCandidateSet n h K) x p) ∧
      (∀ q,
        (∑ request : BankPaperCanonicalTangentSplitRequest
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma,
            tangentSplitRequestWeight request *
              (((bankPaperCanonicalTangentRequestSource
                    R certificate fixed (roughRawCandidateSet n h K) x pivot
                      L sigma request).factorization q : ℝ) -
                ((bankPaperCanonicalTangentRequestTarget
                    R certificate fixed (roughRawCandidateSet n h K) x pivot
                      L sigma request).factorization q : ℝ))) =
          bankPaperCanonicalSelectorValuationDeficit R certificate fixed
            (roughRawCandidateSet n h K) x q) ∧
      ∃ output : BankPaperCanonicalPostTangentOutput R certificate
          (roughRawCandidateSet n h K) fixed,
        output.selector =
          bankPaperCanonicalTangentUpdatedSelector R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma multiplier := by
  exact R.exists_canonicalSectionNinePostTangentOutput_of_cleanListLower
    certificate fixedExceptional fixed x pivot density L sigma hKh hn hyLe
    hySq hdensity hL hsigma hfixedPositive hchargeDvd hfeasible hrowIntegral
    hbalance hsupport hlowerPos hlower hlowerScale hslack hsmall

example :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : ℝ) (depth W K h X0 : ℕ),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
        (pivot : BankPaperCanonicalTangentPrime n W)
        (density L sigma : ℝ),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        n /
            min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) ≤
          tangentBroadUpper n K h /
            max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        tangentEffectiveLowerCard density n
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) +
            tangentCanonicalExceptionalNatUpper n K h X0 (yNat n)
              (max
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request))
              (min
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)) +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K h
            (max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))) →
      K * h ≤ n → 0 < n →
      (yNat n : ℝ) ≤ n → (yNat n : ℝ) ^ 2 ≤ n →
      0 < density → 0 < L → 0 < sigma →
      (∀ a ∈ fixed, 0 < a) →
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget →
      (∀ a ∈ roughRawCandidateSet n h K, 0 ≤ x a ∧ x a ≤ 1) →
      BankPaperCanonicalSelectorRowIntegral n
        (roughRawCandidateSet n h K) x →
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed (roughRawCandidateSet n h K) x →
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed (roughRawCandidateSet n h K) x →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        ∀ multiplier,
          multiplier ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request →
          (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ∧
              x (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ∧
              x (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ≤ 1 - sigma / L)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        4 * (tangentSplitCensusTotalRequestUpper L sigma
              (tangentStarResidualL1
                (bankPaperCanonicalTangentResidual (W := W)
                  R certificate fixed
                  (roughRawCandidateSet n h K) x))
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W)) / n) +
          ((bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n h K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) / n) +
          ((bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n h K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) / n) ≤
            density ^ 2 / 24) →
      ∃ multiplier : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma →
            ℕ,
        (∀ request,
          multiplier request ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot))
          (bankPaperCanonicalTangentRequestSource R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma)
          (bankPaperCanonicalTangentRequestTarget R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma)
          multiplier ∧
        ∃ output : BankPaperCanonicalPostTangentOutput R certificate
            (roughRawCandidateSet n h K) fixed,
          output.selector =
            bankPaperCanonicalTangentUpdatedSelector R certificate fixed
              (roughRawCandidateSet n h K) x pivot L sigma multiplier := BankPaperRealization.eventually_exists_canonicalSectionNinePostTangentOutput

example :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : ℝ) (depth W K h X0 : ℕ)
        (left right : ℕ → ℕ) (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
        (pivot : BankPaperCanonicalTangentPrime n W)
        (L sigma density : ℝ),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      0 < density →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        n /
            min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) ≤
          tangentBroadUpper n K h /
            max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        tangentEffectiveLowerCard density n
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) +
            tangentCanonicalExceptionalNatUpper n K h X0 (yNat n)
              (max
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request))
              (min
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)) +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K h
            (max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        0 < bankPaperCanonicalTangentLowerCard R certificate fixed
          (roughRawCandidateSet n h K) x pivot L sigma density request) ∧
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        bankPaperCanonicalTangentLowerCard R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma density request ≤
          (tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card) ∧
      ∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        ∀ side,
          density * n ≤
            (bankPaperCanonicalTangentLowerCard R certificate fixed
              (roughRawCandidateSet n h K) x pivot L sigma density request :
                ℝ) *
              tangentEndpointLabel
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma)
                side request := BankPaperRealization.eventually_canonicalSectionNineCleanListLower

example
    {c : ℝ} {depth n : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (candidates fixed : Finset ℕ)
    (output : BankPaperCanonicalPostTangentOutput
      R certificate candidates fixed)
    (hcandidates : candidates ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hfixed : fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hfixedCandidate : Disjoint fixed candidates)
    (hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected))
    (hcandidateBank : ∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate : Disjoint certificate.anchors candidates) :
    ∃ candidates' : Finset ℕ, ∃ selector : ℕ → ℝ,
      ∃ fixed' : Finset ℕ,
        candidates' ⊆
            factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        fixed' ⊆
            factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        (∀ a ∈ candidates', 0 ≤ selector a ∧ selector a ≤ 1) ∧
        (∀ label ∈ completeRoughLabelSet (yNat n) candidates',
          ∃ k : ℤ,
            ∑ a ∈ completeRoughRowFiber
                (yNat n) candidates' label, selector a = (k : ℝ)) ∧
        R.selectorTailCharge fixed' ∣
          certificate.prechargedTailTarget ∧
        (∀ q,
          ∑ a ∈ candidates',
              selector a * (a.factorization q : ℝ) =
            ((certificate.selectorTailTarget R fixed').factorization q :
              ℝ)) ∧
        Disjoint fixed' candidates' ∧
        (∀ slot selected,
          Disjoint fixed' (R.exactificationState slot selected)) ∧
        (∀ slot selected,
          Disjoint candidates'
            (R.exactificationState slot selected)) ∧
        Disjoint certificate.anchors fixed' ∧
        Disjoint certificate.anchors candidates' := by
  exact R.canonicalPostTangentContinuationData_of_output certificate candidates
    fixed output hcandidates hfixed hchargeDvd hfixedCandidate hfixedBank
    hcandidateBank hanchorsFixed hanchorsCandidate

end

end Erdos390.WholePaper.BankPaperCanonicalSectionNineAssemblyStatementAudit
