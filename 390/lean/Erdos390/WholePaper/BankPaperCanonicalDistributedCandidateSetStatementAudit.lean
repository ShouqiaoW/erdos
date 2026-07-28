import Erdos390.WholePaper.BankPaperCanonicalDistributedCandidateSet

/-!
# Statement audit for guarded-candidate distributed Section 9

The public candidate-generic sockets retain the candidate set itself and its
containment in the raw universe.  Post-choice takes membership of the selected
endpoints; pre-choice assembly takes universal clean-list endpoint closure.
Neither returns nor infers an unrelated disjointness statement.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

#check bankPaperCanonicalDistributedGuardedCandidates
#check bankPaperCanonicalDistributedGuardedCandidates_subset_raw
#check tangentSplitCleanMultiplier_endpoints_mem_guardedCandidates
#check bankPaperCanonicalDistributed_cleanEndpoints_mem_guardedCandidates
#check BankPaperRealization.exists_canonicalDistributedPostTangentOutput_of_multiplier
#check BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets
#check BankPaperRealization.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
#check BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates

example (n h K : Nat) (guards : Finset Nat) :
    bankPaperCanonicalDistributedGuardedCandidates n h K guards =
      roughRawCandidateSet n h K \ guards := rfl

example (n h K : Nat) (guards : Finset Nat) :
    bankPaperCanonicalDistributedGuardedCandidates n h K guards ⊆
      roughRawCandidateSet n h K :=
  bankPaperCanonicalDistributedGuardedCandidates_subset_raw n h K guards

/-! The concrete set-difference adapter produces precisely the universal
endpoint-closure premise consumed by the generic assembly. -/
example
    {n W K h Phead X0 : Nat}
    {flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real}
    {L sigma : Real} {dedicatedRows guards : Finset Nat}
    (hKh : K * h ≤ n) :
    ∀ request : BankPaperCanonicalDistributedTangentSplitRequest
        flow L sigma,
      ∀ {common : Nat},
        common ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges flow)
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                flow edge.1 edge.2)
              n K h Phead X0 (yNat n) dedicatedRows guards request →
          bankPaperCanonicalDistributedTangentRequestSource request * common ∈
              bankPaperCanonicalDistributedGuardedCandidates n h K guards ∧
            bankPaperCanonicalDistributedTangentRequestTarget request * common ∈
              bankPaperCanonicalDistributedGuardedCandidates n h K guards := by
  intro request common hcommon
  exact bankPaperCanonicalDistributed_cleanEndpoints_mem_guardedCandidates
    hKh request hcommon

namespace BankPaperRealization

/-! Expanded post-choice socket.  In particular, raw containment and selected
endpoint membership are premises, while the output remains indexed by the
supplied `candidates`. -/
example
    {c : Real} {depth n W K h Phead X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed candidates : Finset Nat)
    (selector : Nat → Real)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W → Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W → Real)
    (prefixUpper : Band → Nat → Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
        bandOf cellIndex pointwiseUpper prefixUpper selector)
    (flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real)
    (hflowNonneg : ∀ source target, 0 ≤ flow source target)
    (hdivergence : ∀ p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p)
    (L sigma : Real) (hL : 0 < L) (hsigma : 0 < sigma)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (multiplier : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma → Nat)
    (hmultiplierMem : ∀ request,
      multiplier request ∈
        tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2)
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request)
    (hselectedEndpoints : ∀ request,
      bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request ∈ candidates ∧
        bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request ∈ candidates)
    (hdistinct : TangentEndpointsDistinct
      (tangentSplitRequests
        (tangentPositiveFlowEdges flow) L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2))
      (bankPaperCanonicalDistributedTangentRequestSource
        (flow := flow) (L := L) (sigma := sigma))
      (bankPaperCanonicalDistributedTangentRequestTarget
        (flow := flow) (L := L) (sigma := sigma)) multiplier)
    (hsourceSlack : ∀ request,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ≤ 1 - sigma / L)
    (htargetSlack : ∀ request,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ≤ 1 - sigma / L) :
    ∃ output : BankPaperCanonicalPostTangentOutput R certificate
        candidates fixed,
      output.selector =
        bankPaperCanonicalDistributedTangentUpdatedSelector
          flow L sigma multiplier selector := by
  exact R.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
    certificate fixedExceptional fixed candidates selector
    bandOf cellIndex pointwiseUpper prefixUpper S flow hflowNonneg
    hdivergence L sigma hL hsigma hfixedPositive hchargeDvd multiplier
    hmultiplierMem hselectedEndpoints hdistinct hsourceSlack htargetSlack

end BankPaperRealization

end

end Erdos390.WholePaper
