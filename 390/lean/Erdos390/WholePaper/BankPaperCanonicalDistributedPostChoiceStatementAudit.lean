import Erdos390.WholePaper.BankPaperCanonicalDistributedPostChoice

/-! # Expanded statement audit for the distributed post-choice socket -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! The socket consumes an actual distributed request multiplier, literal
clean-list membership, endpoint distinctness, and the two chosen-endpoint
slack bounds.  Its conclusion is the concrete distributed update; no pivot
or star-locality datum occurs in the interface. -/
example
    {c : Real} {depth n W K h Phead X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed : Finset Nat)
    (selector : Nat -> Real)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed (roughRawCandidateSet n h K)
        bandOf cellIndex pointwiseUpper prefixUpper selector)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflowNonneg : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed (roughRawCandidateSet n h K) selector p)
    (L sigma : Real)
    (hKh : K * h <= n)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (multiplier : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma -> Nat)
    (hmultiplierMem : forall request,
      multiplier request ∈
        tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request)
    (hdistinct : TangentEndpointsDistinct
      (tangentSplitRequests
        (tangentPositiveFlowEdges flow) L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2))
      (bankPaperCanonicalDistributedTangentRequestSource
        (flow := flow) (L := L) (sigma := sigma))
      (bankPaperCanonicalDistributedTangentRequestTarget
        (flow := flow) (L := L) (sigma := sigma))
      multiplier)
    (hsourceSlack : forall request,
      sigma / L <= selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) <= 1 - sigma / L)
    (htargetSlack : forall request,
      sigma / L <= selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) <= 1 - sigma / L) :
    ∃ output : BankPaperCanonicalPostTangentOutput R certificate
        (roughRawCandidateSet n h K) fixed,
      output.selector =
        bankPaperCanonicalDistributedTangentUpdatedSelector
          flow L sigma multiplier selector := by
  exact R.exists_canonicalDistributedPostTangentOutput_of_multiplier
    certificate fixedExceptional fixed selector bandOf cellIndex
      pointwiseUpper prefixUpper S flow hflowNonneg hdivergence L sigma hKh
      hL hsigma hfixedPositive hchargeDvd multiplier hmultiplierMem
      hdistinct hsourceSlack htargetSlack

#check exists_canonicalDistributedPostTangentOutput_of_multiplier

end BankPaperRealization

end


end Erdos390.WholePaper
