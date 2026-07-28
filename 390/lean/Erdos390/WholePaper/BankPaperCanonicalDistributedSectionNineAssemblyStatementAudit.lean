import Erdos390.WholePaper.BankPaperCanonicalDistributedSectionNineAssembly

/-!
# Statement audit for the finite distributed Section 9 assembly

The public theorem below has the explicit ratio-cell earthmover in its
result, consumes the paper main/error/ceiling budgets, and returns an actual
`BankPaperCanonicalPostTangentOutput`.  In particular, its type contains no
pivot, star-locality datum, or requestwise final collision bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

#check BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets

namespace BankPaperRealization

/-! Expanded public terminal.  This repeats the complete quantifier order
and every surviving finite/analytic input rather than hiding them behind a
certificate alias. -/
example
    {c : Real} {depth n W K h X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed : Finset Nat)
    (selector : Nat -> Real)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed (roughRawCandidateSet n h K)
        bandOf cellIndex pointwiseUpper prefixUpper selector)
    (density L sigma N : Real)
    (trafficConstant incidentConstant tangentConstant width : Real)
    (trafficError incidentError weightedResidual weightedPort : Real)
    (hKh : K * h <= n)
    (hn : 0 < n)
    (hdensity : 0 < density) (hL : 0 < L) (hsigma : 0 < sigma)
    (hN : 0 < N) (hscale : L * N = (n : Real))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hresidual : forall p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          |bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector p| <=
        weightedResidual)
    (hport : forall p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex p <= weightedPort)
    (htotal : tangentDistributedTotalTrafficLedger
        (V := BankPaperCanonicalTangentPrime n W)
        (bankPaperCanonicalTangentResidual (W := W)
          R certificate fixed (roughRawCandidateSet n h K) selector)
        (tangentRatioCellCanonicalCutTraffic lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector)
          bandOf cellIndex) <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n (yNat n)
        (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W)) <= density ^ 2 / 96)
    (hlowerPos : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      0 < bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request)
    (hlower : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request <=
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex))
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex edge.1 edge.2)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      forall side,
        density * n <=
          (bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request : Real) *
            tangentEndpointLabel
              bankPaperCanonicalDistributedTangentRequestSource
              bankPaperCanonicalDistributedTangentRequestTarget
              side request)
    (hslack : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      forall multiplier,
        multiplier ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed (roughRawCandidateSet n h K)
                      selector)
                  bandOf cellIndex))
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed (roughRawCandidateSet n h K)
                      selector)
                  bandOf cellIndex edge.1 edge.2)
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request ->
          (sigma / L <= selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) <= 1 - sigma / L) ∧
            (sigma / L <= selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) <= 1 - sigma / L)) :
    ∃ multiplier : BankPaperCanonicalDistributedTangentSplitRequest
        (tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector)
          bandOf cellIndex) L sigma -> Nat,
      (forall request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed (roughRawCandidateSet n h K) selector)
                bandOf cellIndex))
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed (roughRawCandidateSet n h K) selector)
                bandOf cellIndex edge.1 edge.2)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests
          (tangentPositiveFlowEdges
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex)) L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex edge.1 edge.2))
        bankPaperCanonicalDistributedTangentRequestSource
        bankPaperCanonicalDistributedTangentRequestTarget multiplier ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        tangentFlowDivergence
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex) p =
          bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector p) ∧
      (forall q : Nat,
        (∑ request : BankPaperCanonicalDistributedTangentSplitRequest
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed (roughRawCandidateSet n h K) selector)
                bandOf cellIndex) L sigma,
            tangentSplitRequestWeight request *
              (((bankPaperCanonicalDistributedTangentRequestSource
                    request).factorization q : Real) -
                ((bankPaperCanonicalDistributedTangentRequestTarget
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed (roughRawCandidateSet n h K) selector q) ∧
      ∃ output : BankPaperCanonicalPostTangentOutput R certificate
          (roughRawCandidateSet n h K) fixed,
        output.selector =
          bankPaperCanonicalDistributedTangentUpdatedSelector
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex) L sigma multiplier selector := by
  exact R.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets
    certificate fixedExceptional fixed selector lastCell bandOf cellIndex
      pointwiseUpper prefixUpper S density L sigma N trafficConstant
      incidentConstant tangentConstant width trafficError incidentError
      weightedResidual weightedPort hKh hn hdensity hL hsigma hN hscale
      hfixedPositive hchargeDvd hindex hoccupied hresidual hport htotal
      hweightedIncident hmain herror hceiling hlowerPos hlower hlowerScale
      hslack

end BankPaperRealization

/-! The flow and update occurring in the assembly conclusion are the
literal public formulas, rather than certificate fields. -/
example {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    tangentRatioCellEarthmoverFlow lastCell residual bandOf cellIndex =
      fun source target =>
        tangentRatioCellBoundaryFlow lastCell residual bandOf cellIndex
            source target +
          tangentRatioCellInternalFlow lastCell residual bandOf cellIndex
            source target := by
  funext source target
  rfl

example {n W : Nat}
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (L sigma : Real)
    (multiplier : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma -> Nat)
    (selector : Nat -> Real) :
    bankPaperCanonicalDistributedTangentUpdatedSelector
        flow L sigma multiplier selector =
      tangentUpdate
        (tangentSplitRequests (tangentPositiveFlowEdges flow) L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2))
        bankPaperCanonicalDistributedTangentRequestSource
        bankPaperCanonicalDistributedTangentRequestTarget
        multiplier tangentSplitRequestWeight selector := by
  rfl

example (trafficConstant incidentConstant tangentConstant width sigma
    density : Real)
    (hmain : ((16 * trafficConstant + 8 * incidentConstant) *
        tangentConstant * width) / sigma <= density ^ 2 / 48) :
    tangentDistributedPaperMainBudget trafficConstant incidentConstant
        tangentConstant width sigma <= density ^ 2 / 48 := by
  simpa only [tangentDistributedPaperMainBudget] using hmain

example (trafficError incidentError sigma density : Real)
    (herror : (16 * trafficError + 8 * incidentError) / sigma <=
      density ^ 2 / 96) :
    tangentDistributedPaperErrorBudget trafficError incidentError sigma <=
      density ^ 2 / 96 := by
  simpa only [tangentDistributedPaperErrorBudget] using herror

example {n W : Nat} (density : Real)
    (hceiling : (4 + 2 * (yNat n : Real)) *
        ((Fintype.card (BankPaperCanonicalTangentPrime n W) ^ 2 : Nat) : Real) /
          n <=
      density ^ 2 / 96) :
    tangentDistributedPaperCeilingBudget n (yNat n)
        (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W)) <= density ^ 2 / 96 := by
  simpa only [tangentDistributedPaperCeilingBudget,
    tangentDistributedSupportCount] using hceiling

end

end Erdos390.WholePaper
