import Erdos390.WholePaper.BankPaperCanonicalDistributedSectionNineAssembly

/-!
# Distributed Section 9 on a guarded candidate subset

The original distributed Section 9 API is intentionally retained verbatim:
it works on `roughRawCandidateSet n h K`.  This module adds a parallel,
backward-compatible interface for an arbitrary finite candidate set contained
in that raw universe.

Containment alone does not put the endpoints selected from a clean multiplier
list back into the smaller set.  The generic post-choice theorem therefore
takes selected-endpoint membership, while pre-choice assembly takes clean-list
endpoint closure.  A concrete guarded set obtained by subtracting the
numerical guards is supplied below; its endpoint closure is derived from the
defining set difference and the existing clean-list membership theorem.  No
disjointness conclusion is inferred merely from containment in the raw
candidate set.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## A concrete guarded candidate subset -/

/-- Remove a finite endpoint-guard set from the literal raw candidates. -/
def bankPaperCanonicalDistributedGuardedCandidates
    (n h K : Nat) (numericalGuards : Finset Nat) : Finset Nat :=
  roughRawCandidateSet n h K \ numericalGuards

/-- Guard deletion only shrinks the raw candidate universe. -/
theorem bankPaperCanonicalDistributedGuardedCandidates_subset_raw
    (n h K : Nat) (numericalGuards : Finset Nat) :
    bankPaperCanonicalDistributedGuardedCandidates n h K numericalGuards ⊆
      roughRawCandidateSet n h K := by
  exact Finset.sdiff_subset

/-- A clean multiplier has both endpoints in the guarded candidate set when
that set is literally the raw universe minus the same numerical guards used
in the clean list.

This is the only place where guard avoidance is turned into candidate
membership.  The conclusion follows from `Finset.mem_sdiff`; it is not a
disjointness consequence of raw-set containment. -/
theorem tangentSplitCleanMultiplier_endpoints_mem_guardedCandidates
    {E : Type*} {edges : Finset E} {source target : E → Nat}
    {L sigma : Real} {flow : E → Real}
    {n K h Phead X0 y : Nat}
    {dedicatedRows numericalGuards : Finset Nat}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : Nat}
    (hsourcePos : 0 < tangentSplitRequestSource source request)
    (htargetPos : 0 < tangentSplitRequestTarget target request)
    (hKh : K * h ≤ n)
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    tangentSplitRequestSource source request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards ∧
      tangentSplitRequestTarget target request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards := by
  let s := tangentSplitRequestSource source request
  let t := tangentSplitRequestTarget target request
  have hraw := tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
    request hsourcePos htargetPos hKh hmultiplier
  have hclean : multiplier ∈ tangentCleanCommonMultiplierList
      n K h Phead X0 y (max s t) (min s t)
        dedicatedRows numericalGuards := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists, s, t] using hmultiplier
  have hdata := mem_tangentCleanCommonMultiplierList.mp hclean
  have hmaxNot : max s t * multiplier ∉ numericalGuards :=
    hdata.2.2.2.2.1
  have hminNot : min s t * multiplier ∉ numericalGuards :=
    hdata.2.2.2.2.2
  have hsNot : s * multiplier ∉ numericalGuards := by
    rcases le_total s t with hst | hts
    · simpa only [min_eq_left hst] using hminNot
    · simpa only [max_eq_left hts] using hmaxNot
  have htNot : t * multiplier ∉ numericalGuards := by
    rcases le_total s t with hst | hts
    · simpa only [max_eq_right hst] using hmaxNot
    · simpa only [min_eq_right hts] using hminNot
  unfold bankPaperCanonicalDistributedGuardedCandidates
  constructor
  · exact Finset.mem_sdiff.mpr ⟨hraw.1, by simpa only [s] using hsNot⟩
  · exact Finset.mem_sdiff.mpr ⟨hraw.2, by simpa only [t] using htNot⟩

/-- Canonical distributed requests satisfy the preceding guarded endpoint
closure automatically.  This is the adapter used when the generic assembly
is instantiated with `raw candidates \ numericalGuards`. -/
theorem bankPaperCanonicalDistributed_cleanEndpoints_mem_guardedCandidates
    {n W K h Phead X0 : Nat}
    {flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real}
    {L sigma : Real} {dedicatedRows numericalGuards : Finset Nat}
    (hKh : K * h ≤ n)
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) {multiplier : Nat}
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
        (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
        L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2)
        n K h Phead X0 (yNat n) dedicatedRows numericalGuards request) :
    bankPaperCanonicalDistributedTangentRequestSource request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards ∧
      bankPaperCanonicalDistributedTangentRequestTarget request * multiplier ∈
        bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards := by
  have hsourcePrime :
      (bankPaperCanonicalDistributedTangentRequestSource request).Prime := by
    simpa only [bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
  have htargetPrime :
      (bankPaperCanonicalDistributedTangentRequestTarget request).Prime := by
    simpa only [bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  exact tangentSplitCleanMultiplier_endpoints_mem_guardedCandidates
    request hsourcePrime.pos htargetPrime.pos hKh hmultiplier

namespace BankPaperRealization

/-! ## Generic deterministic post-choice socket -/

/-- Apply a chosen collision-free distributed multiplier family on an
arbitrary guarded candidate set.

The candidate set may be arbitrary.  The explicit `hselectedEndpoints` premise
is the exact closure fact needed to keep the update supported on `candidates`;
no redundant inclusion in the paper's raw candidate universe is required.

The result is otherwise identical to the raw-candidate post-choice socket.
In particular it returns the literal update, row integrality, feasibility,
and the charged valuation certificate on the supplied candidate set. -/
theorem exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
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
    (L sigma : Real)
    (hL : 0 < L) (hsigma : 0 < sigma)
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
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
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
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2))
      (bankPaperCanonicalDistributedTangentRequestSource
        (flow := flow) (L := L) (sigma := sigma))
      (bankPaperCanonicalDistributedTangentRequestTarget
        (flow := flow) (L := L) (sigma := sigma))
      multiplier)
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
  let edges := tangentPositiveFlowEdges flow
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let edgeFlow : BankPaperCanonicalTangentPrime n W ×
      BankPaperCanonicalTangentPrime n W → Real :=
    fun edge => flow edge.1 edge.2
  let requests := tangentSplitRequests edges L sigma edgeFlow
  let requestSource : TangentSplitRequest edges L sigma edgeFlow → ℕ :=
    tangentSplitRequestSource source
  let requestTarget : TangentSplitRequest edges L sigma edgeFlow → ℕ :=
    tangentSplitRequestTarget target
  have hstate :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState S
  have hfeasible : ∀ a ∈ candidates,
      0 ≤ selector a ∧ selector a ≤ 1 := hstate.1
  have hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector := hstate.2.1
  have hmultiplierMem' : ∀ request :
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
  have hsourceSlack' : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      sigma / L ≤ selector
          (requestSource request * multiplier request) ∧
        selector (requestSource request * multiplier request) ≤
          1 - sigma / L := by
    intro request
    simpa only [requestSource, edges, source, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestSource] using
        hsourceSlack request
  have htargetSlack' : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      sigma / L ≤ selector
          (requestTarget request * multiplier request) ∧
        selector (requestTarget request * multiplier request) ≤
          1 - sigma / L := by
    intro request
    simpa only [requestTarget, edges, target, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestTarget] using
        htargetSlack request
  have hrequestPrime : ∀ request :
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
  have hrequestUpper : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      requestSource request ≤ yNat n ∧
        requestTarget request ≤ yNat n := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_le_yNat request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_le_yNat request.1.1.2
  have hmultiplierPos : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      0 < multiplier request := by
    intro request
    exact tangentSplitCleanMultiplier_pos request
      (hmultiplierMem' request)
  have hendpointMem : ∀ request :
      TangentSplitRequest edges L sigma edgeFlow,
      requestSource request * multiplier request ∈ candidates ∧
        requestTarget request * multiplier request ∈ candidates := by
    intro request
    simpa only [requestSource, requestTarget, edges, source, target, edgeFlow,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using
        hselectedEndpoints request
  have hsameRow : ∀ request :
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
  have hrowPreserve : ∀ label,
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
      R certificate fixed candidates bandOf cellIndex pointwiseUpper
      prefixUpper selector S flow hflowNonneg hdivergence L sigma
  have hboundary : ∀ q,
      ∑ request ∈ requests,
          tangentSplitRequestWeight request *
            ((requestSource request).factorization q -
              (requestTarget request).factorization q : Real) =
        ((certificate.selectorTailTarget R fixed).factorization q : Real) -
          ∑ a ∈ candidates,
            selector a * (a.factorization q : Real) := by
    intro q
    simpa only [requests, tangentSplitRequests, requestSource, requestTarget,
      source, target, edges, edgeFlow,
      bankPaperCanonicalSelectorValuationDeficit] using hcanonical.2 q
  have hresidualValuation : ∀ q,
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
  have hchargedValuation : ∀ q,
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

/-! ## Generic finite distributed assembly -/

/-- Assemble the explicit ratio-cell earthmover and collision-free clean
multiplier choice on an arbitrary guarded candidate subset.

All analytic and collision hypotheses are the same as in
`exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets`,
with the selector residual evaluated on `candidates`.  The one additional
pre-choice law is `hendpointClosure`, which says that every multiplier the
collision census is allowed to choose has both numerical endpoints in the
guarded set. -/
theorem exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates
    {c : Real} {depth n W K h X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed candidates : Finset Nat)
    (selector : Nat → Real)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band → Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W → Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W → Real)
    (prefixUpper : Band → Nat → Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates
        bandOf cellIndex pointwiseUpper prefixUpper selector)
    (density L sigma N : Real)
    (trafficConstant incidentConstant tangentConstant width : Real)
    (trafficError incidentError weightedResidual weightedPort : Real)
    (hn : 0 < n)
    (hdensity : 0 < density) (hL : 0 < L) (hsigma : 0 < sigma)
    (hN : 0 < N) (hscale : L * N = (n : Real))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hindex : ∀ p, cellIndex p ≤ lastCell (bandOf p))
    (hoccupied : ∀ band cell,
      cell ≤ lastCell band →
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hresidual : ∀ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| ≤
        weightedResidual)
    (hport : ∀ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex p ≤ weightedPort)
    (htotal : tangentDistributedTotalTrafficLedger
        (V := BankPaperCanonicalTangentPrime n W)
        (bankPaperCanonicalTangentResidual (W := W)
          R certificate fixed candidates selector)
        (tangentRatioCellCanonicalCutTraffic lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex) ≤
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort ≤
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma ≤
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma ≤ density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n (yNat n)
        (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W)) ≤ density ^ 2 / 96)
    (hlowerPos : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      0 < bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request)
    (hlower : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request ≤
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex))
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex edge.1 edge.2)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      ∀ side,
        density * n ≤
          (bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request : Real) *
            tangentEndpointLabel
              bankPaperCanonicalDistributedTangentRequestSource
              bankPaperCanonicalDistributedTangentRequestTarget
              side request)
    (hendpointClosure : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      ∀ {common : Nat},
        common ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex))
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex edge.1 edge.2)
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request →
          bankPaperCanonicalDistributedTangentRequestSource request *
                common ∈ candidates ∧
            bankPaperCanonicalDistributedTangentRequestTarget request *
                common ∈ candidates)
    (hslack : ∀ request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) L sigma,
      ∀ multiplier,
        multiplier ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex))
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex edge.1 edge.2)
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request →
          (sigma / L ≤ selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) ≤ 1 - sigma / L)) :
    ∃ multiplier : BankPaperCanonicalDistributedTangentSplitRequest
        (tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex) L sigma → Nat,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates selector)
                bandOf cellIndex))
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates selector)
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
                R certificate fixed candidates selector)
              bandOf cellIndex)) L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex edge.1 edge.2))
        bankPaperCanonicalDistributedTangentRequestSource
        bankPaperCanonicalDistributedTangentRequestTarget multiplier ∧
      (∀ p : BankPaperCanonicalTangentPrime n W,
        tangentFlowDivergence
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex) p =
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) ∧
      (∀ q : Nat,
        (∑ request : BankPaperCanonicalDistributedTangentSplitRequest
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed candidates selector)
                bandOf cellIndex) L sigma,
            tangentSplitRequestWeight request *
              (((bankPaperCanonicalDistributedTangentRequestSource
                    request).factorization q : Real) -
                ((bankPaperCanonicalDistributedTangentRequestTarget
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector q) ∧
      ∃ output : BankPaperCanonicalPostTangentOutput R certificate
          candidates fixed,
        output.selector =
          bankPaperCanonicalDistributedTangentUpdatedSelector
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex) L sigma multiplier selector := by
  let residual := bankPaperCanonicalTangentResidual (W := W)
    R certificate fixed candidates selector
  let portLoad := tangentRatioCellUniformPortLoad residual bandOf cellIndex
  let cutTraffic := tangentRatioCellCanonicalCutTraffic
    lastCell residual bandOf cellIndex
  let flow := tangentRatioCellEarthmoverFlow
    lastCell residual bandOf cellIndex
  let lowerCard : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma → Nat :=
    fun request => bankPaperCanonicalDistributedTangentLowerCard
      (density := density) request
  have hspec := bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
    R certificate fixed candidates lastCell bandOf cellIndex
      pointwiseUpper prefixUpper selector S hindex hoccupied
  have hboundary :=
    bankPaperCanonicalRoundedSelector_ratioCellDistributedBoundary
      R certificate fixed candidates lastCell bandOf cellIndex
        pointwiseUpper prefixUpper selector S hindex hoccupied L sigma
  have hpositiveEndpoints : ∀ {source target},
      0 < flow source target → source ≠ target := by
    intro source target hpositive
    exact tangentRatioCellEarthmoverFlow_positive_endpoints_ne
      lastCell residual bandOf cellIndex hpositive
  have hpositiveIncident : ∀ p,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
          (bankPaperCanonicalTangentPrimeLabel p) ≤
        |residual p| + 2 * portLoad p := by
    intro p
    exact bankPaperCanonicalRoundedSelector_ratioCellEarthmover_positiveIncident
      R certificate fixed candidates lastCell bandOf cellIndex
        pointwiseUpper prefixUpper selector S hindex hoccupied p
  have hyLeNat : yNat n ≤ n := by
    have hthree : 3 * yNat n ≤ n := R.three_mul_yNat_le_n
    omega
  have hyLe : (yNat n : Real) ≤ (n : Real) := by
    exact_mod_cast hyLeNat
  have hySqNat : yNat n * yNat n ≤ n :=
    bankAnchor_yNat_mul_self_le_self hn
  have hySqMul : (yNat n : Real) * (yNat n : Real) ≤ (n : Real) := by
    exact_mod_cast hySqNat
  have hySq : (yNat n : Real) ^ 2 ≤ (n : Real) := by
    simpa only [pow_two] using hySqMul
  have hresidual' : ∀ p,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| ≤
        weightedResidual := by
    simpa only [residual] using hresidual
  have hport' : ∀ p,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * portLoad p ≤
        weightedPort := by
    simpa only [portLoad, residual] using hport
  have htotal' : tangentDistributedTotalTrafficLedger residual cutTraffic ≤
      trafficConstant * tangentConstant * N * width + trafficError * N := by
    simpa only [cutTraffic, residual] using htotal
  have hlowerPos' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      0 < lowerCard request := by
    simpa only [lowerCard, flow, residual] using hlowerPos
  have hlower' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card := by
    simpa only [lowerCard, flow, residual] using hlower
  have hlowerScale' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      ∀ side,
        density * n ≤ (lowerCard request : Real) *
          tangentEndpointLabel
            bankPaperCanonicalDistributedTangentRequestSource
            bankPaperCanonicalDistributedTangentRequestTarget side request := by
    simpa only [lowerCard, flow, residual] using hlowerScale
  have hcensus :=
    R.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus
      certificate fixedExceptional K h (roughHeadModulus W) X0
      bankPaperCanonicalTangentPrimeLabel residual portLoad cutTraffic flow
      hspec.1 hspec.2.1 hpositiveEndpoints hspec.2.2.2.1
      hpositiveIncident bankPaperCanonicalTangentPrimeLabel_injective
      bankPaperCanonicalTangentPrimeLabel_prime
      weightedResidual weightedPort hresidual' hport' (yNat n) density
      hn hdensity bankPaperCanonicalTangentPrimeLabel_le_yNat hyLe hySq
      hL hsigma hN hscale
      trafficConstant incidentConstant tangentConstant width
      trafficError incidentError htotal' hweightedIncident
      hmain herror hceiling lowerCard hlowerPos' hlower' hlowerScale'
  obtain ⟨multiplier, hmultiplierMem, hdistinct⟩ := hcensus.2.2
  have hendpointClosure' : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
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
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request →
          bankPaperCanonicalDistributedTangentRequestSource request * common ∈
              candidates ∧
            bankPaperCanonicalDistributedTangentRequestTarget request * common ∈
              candidates := by
    intro request common hcommon
    simpa only [flow, residual] using
      hendpointClosure request (by
        simpa only [flow, residual] using hcommon)
  have hselectedEndpoints : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request ∈ candidates ∧
        bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request ∈ candidates := by
    intro request
    exact hendpointClosure' request (hmultiplierMem request)
  have hsourceSlack : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ≤ 1 - sigma / L := by
    intro request
    have h := (hslack request (multiplier request) (by
      simpa only [flow, residual] using
        hmultiplierMem request)).1
    simpa only [flow, residual] using h
  have htargetSlack : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ≤ 1 - sigma / L := by
    intro request
    have h := (hslack request (multiplier request) (by
      simpa only [flow, residual] using
        hmultiplierMem request)).2
    simpa only [flow, residual] using h
  have hpost :=
    R.exists_canonicalDistributedPostTangentOutput_of_multiplier_on_candidates
      certificate fixedExceptional fixed candidates selector
      bandOf cellIndex pointwiseUpper prefixUpper S flow hspec.1 hspec.2.1
      L sigma hL hsigma hfixedPositive hchargeDvd multiplier
      hmultiplierMem hselectedEndpoints
      hdistinct hsourceSlack htargetSlack
  obtain ⟨output, houtput⟩ := hpost
  refine ⟨multiplier, ?_, ?_, ?_, ?_, output, ?_⟩
  · simpa only [flow, residual] using hmultiplierMem
  · simpa only [flow, residual,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hdistinct
  · exact hboundary.1
  · simpa only [
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hboundary.2
  · simpa only [flow, residual] using houtput

end BankPaperRealization

end

end Erdos390.WholePaper
