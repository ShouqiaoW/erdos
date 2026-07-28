import Erdos390.WholePaper.BankPaperCanonicalDistributedTangentBridge
import Erdos390.WholePaper.BankPaperCanonicalSectionNineAssembly

/-!
# Deterministic post-choice assembly for the distributed tangent

The ratio-cell earthmover and the distributed collision census live upstream
of the actual selector update.  This file supplies the finite socket between
them and `BankPaperCanonicalPostTangentOutput`.

An actual common multiplier is supplied for every split request, together
with membership in the literal clean list, global endpoint distinctness, and
the two endpoint-slack bounds.  Everything after that choice is deterministic:
the endpoints lie in the raw candidate set, each move stays in one complete
rough row, feasibility is preserved, and the distributed boundary gives the
exact target valuation.

There is no pivot, star locality condition, request-count estimate, or
separate collision-budget premise in this theorem.  Actual endpoint
distinctness is supplied explicitly.  The only divisibility input is the
genuine combined selector-tail charge needed to turn the residual quotient
target back into the charged valuation certificate.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- Apply an already chosen collision-free family of clean common
multipliers to an arbitrary nonnegative distributed flow with the literal
canonical residual divergence.

The selector state is the honest pre-tangent predicate.  Clean-list
membership supplies positive multipliers and candidate closure; the supplied
endpoint slack and distinctness supply feasibility.  The exact distributed
boundary then furnishes the post-tangent valuation certificate. -/
theorem exists_canonicalDistributedPostTangentOutput_of_multiplier
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
  let candidates := roughRawCandidateSet n h K
  let edges := tangentPositiveFlowEdges flow
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let edgeFlow : BankPaperCanonicalTangentPrime n W ×
      BankPaperCanonicalTangentPrime n W -> Real :=
    fun edge => flow edge.1 edge.2
  let requests := tangentSplitRequests edges L sigma edgeFlow
  let requestSource : TangentSplitRequest edges L sigma edgeFlow → ℕ :=
    tangentSplitRequestSource source
  let requestTarget : TangentSplitRequest edges L sigma edgeFlow → ℕ :=
    tangentSplitRequestTarget target
  have hstate :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState S
  have hfeasible : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1 := by
    simpa only [candidates] using hstate.1
  have hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector := by
    simpa only [candidates] using hstate.2.1
  have hmultiplierMem' : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      multiplier request ∈
        tangentSplitCleanMultiplierLists edges source target L sigma edgeFlow
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request := by
    intro request
    simpa only [edges, source, target, edgeFlow] using
      hmultiplierMem request
  have hdistinct' : TangentEndpointsDistinct requests requestSource
      requestTarget multiplier := by
    simpa only [requests, requestSource, requestTarget, edges, source, target,
      edgeFlow, bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hdistinct
  have hsourceSlack' : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      sigma / L <= selector
          (requestSource request * multiplier request) ∧
        selector (requestSource request * multiplier request) <=
          1 - sigma / L := by
    intro request
    simpa only [requestSource, edges, source, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestSource] using
        hsourceSlack request
  have htargetSlack' : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      sigma / L <= selector
          (requestTarget request * multiplier request) ∧
        selector (requestTarget request * multiplier request) <=
          1 - sigma / L := by
    intro request
    simpa only [requestTarget, edges, target, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestTarget] using
        htargetSlack request
  have hrequestPrime : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      (requestSource request).Prime ∧
        (requestTarget request).Prime := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hrequestUpper : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      requestSource request <= yNat n ∧
        requestTarget request <= yNat n := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_le_yNat request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_le_yNat request.1.1.2
  have hmultiplierPos : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      0 < multiplier request := by
    intro request
    exact tangentSplitCleanMultiplier_pos request
      (hmultiplierMem' request)
  have hendpointMem : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      requestSource request * multiplier request ∈ candidates ∧
        requestTarget request * multiplier request ∈ candidates := by
    intro request
    simpa only [candidates] using
      tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
        request (hrequestPrime request).1.pos
          (hrequestPrime request).2.pos hKh (hmultiplierMem' request)
  have hsameRow : forall request :
      TangentSplitRequest edges L sigma edgeFlow,
      completeRoughLabel (yNat n)
          (requestSource request * multiplier request) =
        completeRoughLabel (yNat n)
          (requestTarget request * multiplier request) := by
    intro request
    exact tangentSplitEndpoints_completeRoughLabel_eq
      (hrequestPrime request).1.pos (hrequestPrime request).2.pos
      (hrequestUpper request).1 (hrequestUpper request).2
      (hmultiplierPos request)
  have hflowPos : ∀ edge ∈ edges, 0 < edgeFlow edge := by
    intro edge hedge
    simpa only [edgeFlow] using
      (mem_tangentPositiveFlowEdges.mp hedge)
  have hfeasibleUpdate := tangentSplitUpdate_feasible_and_margin
    edges source target edgeFlow hflowPos hL hsigma multiplier selector
      candidates hdistinct' hsourceSlack' htargetSlack' hfeasible
  have hrowPreserve : forall label,
      ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          tangentUpdate requests requestSource requestTarget multiplier
            tangentSplitRequestWeight selector a =
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a := by
    intro label
    simpa only [completeRoughRowFiber] using
      tangentUpdate_signatureRow requests requestSource requestTarget
        multiplier tangentSplitRequestWeight selector candidates
        (completeRoughLabel (yNat n)) label
        (fun request _hrequest => (hendpointMem request).1)
        (fun request _hrequest => (hendpointMem request).2)
        (fun request _hrequest => hsameRow request)
  have hrowIntegralUpdate :
      BankPaperCanonicalSelectorRowIntegral n candidates
        (tangentUpdate requests requestSource requestTarget multiplier
          tangentSplitRequestWeight selector) := by
    intro label hlabel
    obtain ⟨k, hk⟩ := hrowIntegral label hlabel
    exact ⟨k, (hrowPreserve label).trans hk⟩
  have hcanonical :=
    bankPaperCanonicalRoundedSelector_distributedBoundary
      R certificate fixed (roughRawCandidateSet n h K)
      bandOf cellIndex pointwiseUpper prefixUpper selector S flow
      hflowNonneg hdivergence L sigma
  have hboundary : forall q,
      ∑ request ∈ requests,
          tangentSplitRequestWeight request *
            ((requestSource request).factorization q -
              (requestTarget request).factorization q : Real) =
        ((certificate.selectorTailTarget R fixed).factorization q : Real) -
          ∑ a ∈ candidates,
            selector a * (a.factorization q : Real) := by
    intro q
    simpa only [requests, tangentSplitRequests, requestSource, requestTarget,
      source, target, edges, edgeFlow, candidates,
      bankPaperCanonicalSelectorValuationDeficit] using hcanonical.2 q
  have hresidualValuation : forall q,
      ∑ a ∈ candidates,
          tangentUpdate requests requestSource requestTarget multiplier
              tangentSplitRequestWeight selector a *
            (a.factorization q : Real) =
        ((certificate.selectorTailTarget R fixed).factorization q : Real) :=
    tangentUpdate_valuation_eq_target requests requestSource requestTarget
      multiplier tangentSplitRequestWeight selector candidates
      (fun q => ((certificate.selectorTailTarget R fixed).factorization q :
        Real))
      (fun request _hrequest => (hendpointMem request).1)
      (fun request _hrequest => (hendpointMem request).2)
      (fun request _hrequest => (hrequestPrime request).1.ne_zero)
      (fun request _hrequest => (hrequestPrime request).2.ne_zero)
      (fun request _hrequest => (hmultiplierPos request).ne') hboundary
  have hchargedValuation : forall q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q :
            Real) +
          ∑ a ∈ candidates,
            tangentUpdate requests requestSource requestTarget multiplier
                tangentSplitRequestWeight selector a *
              (a.factorization q : Real) =
        (certificate.prechargedTailTarget.factorization q : Real) := by
    apply (certificate.valuationCertificate_iff_selectorTailTarget
      R fixed
        (fun q => ∑ a ∈ candidates,
          tangentUpdate requests requestSource requestTarget multiplier
              tangentSplitRequestWeight selector a *
            (a.factorization q : Real))
        hfixedPositive hchargeDvd).2
    exact hresidualValuation
  let output : BankPaperCanonicalPostTangentOutput R certificate
      candidates fixed := {
    selector := tangentUpdate requests requestSource requestTarget multiplier
      tangentSplitRequestWeight selector
    feasible := fun a ha => hfeasibleUpdate.1 a ha
    rowIntegral := hrowIntegralUpdate
    valuationCertificate := hchargedValuation }
  refine ⟨output, ?_⟩
  rfl

end BankPaperRealization

end

end Erdos390.WholePaper
