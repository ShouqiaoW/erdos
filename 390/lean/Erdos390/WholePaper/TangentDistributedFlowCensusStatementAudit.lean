import Erdos390.WholePaper.TangentDistributedFlowCensus

/-! # Expanded statement audit for the distributed tangent census -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {V : Type*} [Fintype V]
    (residual : V -> Real) (cutTraffic : Real) :
    tangentDistributedTotalTrafficLedger residual cutTraffic =
      (∑ v : V, |residual v|) / 2 + 2 * cutTraffic := by
  rfl

example {V : Type*} [Fintype V]
    (label : V -> Nat) (residual portLoad : V -> Real) (q : Nat) :
    tangentDistributedLabelIncidentLedger label residual portLoad q =
      ∑ v : V,
        if label v = q then |residual v| + 2 * portLoad v else 0 := by
  rfl

example {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cut : Nat) :
    tangentRatioCellPrefixMass residual bandOf cellIndex band cut =
      ∑ v : V,
        if bandOf v = band ∧ cellIndex v <= cut then residual v else 0 := by
  rfl

example {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (hpointwise : forall v, |residual v| <= pointwiseUpper v)
    (band : Band) (cut : Nat) :
    |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
      ∑ v : V,
        if bandOf v = band ∧ cut < cellIndex v then pointwiseUpper v else 0 := by
  simpa only [tangentRatioCellTailPointwiseUpper] using
    abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
      residual pointwiseUpper bandOf cellIndex hbalance hpointwise band cut

example {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (hpointwise : forall v, |residual v| <= pointwiseUpper v)
    (v : V) :
    tangentRatioCellUniformPortLoad residual bandOf cellIndex v <=
      ((if cellIndex v = 0 then 0
          else tangentRatioCellTailPointwiseUpper
            pointwiseUpper bandOf cellIndex (bandOf v) (cellIndex v - 1)) +
        tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex (bandOf v) (cellIndex v)) /
        tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v) := by
  simpa only [tangentRatioCellPointwisePortUpper] using
    tangentRatioCellUniformPortLoad_le_pointwisePortUpper
      residual pointwiseUpper bandOf cellIndex hbalance hpointwise v

example {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) :
    |tangentRatioCellInternalResidual residual bandOf cellIndex v| +
        tangentRatioCellUniformPortLoad residual bandOf cellIndex v <=
      |residual v| +
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v :=
  abs_internalResidual_add_portLoad_le residual bandOf cellIndex v

example {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) :
    tangentRatioCellUniformPortLoad residual bandOf cellIndex v =
      (|tangentRatioCellLeftPrefixMass residual bandOf cellIndex v| +
          |tangentRatioCellPrefixMass residual bandOf cellIndex
            (bandOf v) (cellIndex v)|) /
        tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v) := by
  rfl

example {V Band : Type*} [Fintype V] [DecidableEq V] [DecidableEq Band]
    (label : V -> Nat) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (flow : V -> V -> Real) (ratioUpper : Real)
    (hrespect : TangentFlowRespectsRatioCells bandOf cellIndex flow)
    (hgeometry : TangentRatioCellGeometry
      label bandOf cellIndex ratioUpper)
    {edge : V × V} (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    (((max (label edge.1) (label edge.2) : Nat) : Real) /
      ((min (label edge.1) (label edge.2) : Nat) : Real)) <= ratioUpper := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    tangentPositiveEdge_locality_of_ratioCells
      label bandOf cellIndex flow ratioUpper hrespect hgeometry hedge

example {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) :
    (tangentPositiveFlowEdges flow).card <= Fintype.card V ^ 2 := by
  simpa only [tangentDistributedSupportCount] using
    card_tangentPositiveFlowEdges_le_distributedSupportCount flow

example {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (L sigma : Real) (p : Nat) :
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p :=
  tangentDistributedSplitRequest_factorizationBoundary_eq_residual
    flow label residual hflow hdivergence L sigma p

example {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real) (cutTraffic : Real)
    (hflow : forall source target, 0 <= flow source target)
    (htraffic : tangentFlowTraffic flow <=
      (∑ v : V, |residual v|) / 2 + 2 * cutTraffic)
    {L sigma : Real} (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentTotalRequestCount
      (TangentSplitRequest (tangentPositiveFlowEdges flow) L sigma
        (fun edge : V × V => flow edge.1 edge.2)) : Real) <=
      (4 * L / sigma) *
          ((∑ v : V, |residual v|) / 2 + 2 * cutTraffic) +
        Fintype.card V ^ 2 := by
  simpa only [tangentDistributedTotalTrafficLedger,
    tangentDistributedSupportCount,
    tangentSplitCensusTotalRequestUpper, Nat.cast_pow] using
      tangentDistributedTotalRequestCount_le
        flow residual cutTraffic hflow htraffic hL hsigma

example {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hincident : forall v,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => flow edge.1 edge.2) (label v) <=
        |residual v| + 2 * portLoad v)
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    {labelUpper : Nat} (hlabelUpper : forall v, label v <= labelUpper)
    {L sigma : Real} (hL : 0 < L) (hsigma : 0 < sigma) (v : V) :
    (label v : Real) *
        (tangentRequestLabelLoad
          (tangentSplitRequestSource
            (edges := tangentPositiveFlowEdges flow) (L := L)
            (sigma := sigma) (flow := fun edge : V × V => flow edge.1 edge.2)
            (tangentStarEdgeSource label))
          (tangentSplitRequestTarget
            (edges := tangentPositiveFlowEdges flow) (L := L)
            (sigma := sigma) (flow := fun edge : V × V => flow edge.1 edge.2)
            (tangentStarEdgeTarget label))
          (label v) : Real) <=
      (4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
        (labelUpper : Real) * Fintype.card V ^ 2 := by
  simpa only [tangentDistributedSupportCount, Nat.cast_pow] using
    tangentDistributedWeightedLabelRequestLoad_le
      flow label residual portLoad hflow hincident hlabel
      hresidual hport hlabelUpper hL hsigma v

/-! The old final traffic premise is a conclusion of three genuinely
upstream budgets: fixed width, eventual analytic error, and eventual dense
support ceiling. -/
example {V : Type*} [Fintype V]
    (residual : V -> Real) (cutTraffic weightedResidual weightedPort : Real)
    {n labelUpper : Nat} {L sigma N density : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hincident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : ((16 * trafficConstant + 8 * incidentConstant) *
        tangentConstant * width) / sigma <= density ^ 2 / 48)
    (herror : (16 * trafficError + 8 * incidentError) / sigma <=
      density ^ 2 / 96)
    (hceiling : (4 + 2 * (labelUpper : Real)) *
        Fintype.card V ^ 2 / n <= density ^ 2 / 96) :
    tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort <=
      density ^ 2 / 24 := by
  apply tangentDistributedResidualCollisionUpper_le_of_paperSmallness
    residual cutTraffic weightedResidual weightedPort hL hsigma hN hscale
    htotal hincident
  · simpa only [tangentDistributedPaperMainBudget] using hmain
  · simpa only [tangentDistributedPaperErrorBudget] using herror
  · simpa only [tangentDistributedPaperCeilingBudget,
      tangentDistributedSupportCount, Nat.cast_pow] using hceiling

/-! The paper-level connector is restated literally so that its complete
quantifier order and every quantitative dependency are visible in the audit. -/
example
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : Real} {depth n M : Nat}
    {left right : Nat -> Nat} {changed : Finset Nat}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset Nat)
    (K h Phead X0 : Nat)
    (label : V -> Nat) (residual portLoad : V -> Real)
    (cutTraffic : Real) (vertexFlow : V -> V -> Real)
    (hflowNonneg : forall source target,
      0 <= vertexFlow source target)
    (hdivergence : forall v,
      tangentFlowDivergence vertexFlow v = residual v)
    (hpositiveEndpoints : forall {source target},
      0 < vertexFlow source target -> source ≠ target)
    (htrafficFull : tangentFlowTraffic vertexFlow <=
      tangentDistributedTotalTrafficLedger residual cutTraffic)
    (hincidentVertex : forall v,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges vertexFlow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => vertexFlow edge.1 edge.2) (label v) <=
        |residual v| + 2 * portLoad v)
    (hlabelInjective : Function.Injective label)
    (hlabelPrime : forall v, (label v).Prime)
    (weightedResidual weightedPort : Real)
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    (labelUpper : Nat) (density : Real)
    (hn : 0 < n) (hdensity : 0 < density)
    (hlabelUpper : forall v, label v <= labelUpper)
    (hlabelUpperLe : (labelUpper : Real) <= n)
    (hlabelUpperSq : (labelUpper : Real) ^ 2 <= n)
    {L sigma N : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
    (trafficConstant incidentConstant tangentConstant width : Real)
    (trafficError incidentError : Real)
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n labelUpper
        (tangentDistributedSupportCount V) <= density ^ 2 / 96)
    (lowerCard : TangentSplitRequest
      (tangentPositiveFlowEdges vertexFlow) L sigma
        (fun edge : V × V => vertexFlow edge.1 edge.2) -> Nat)
    (hlowerPos : forall request, 0 < lowerCard request)
    (hlower : forall request,
      lowerCard request <=
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges vertexFlow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (fun edge : V × V => vertexFlow edge.1 edge.2)
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : forall request side,
      density * n <= (lowerCard request : Real) *
        tangentEndpointLabel
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          side request) :
    (forall v, tangentFlowDivergence vertexFlow v = residual v) ∧
      (forall p,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges vertexFlow) L sigma
                (fun edge : V × V => vertexFlow edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource (tangentStarEdgeSource label)
                    request).factorization p : Real) -
                ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                    request).factorization p : Real))) =
          ∑ v : V, residual v * (label v).factorization p) ∧
      ∃ multiplier : TangentSplitRequest
          (tangentPositiveFlowEdges vertexFlow) L sigma
            (fun edge : V × V => vertexFlow edge.1 edge.2) -> Nat,
        (forall request,
          multiplier request ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges vertexFlow)
              (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
              L sigma (fun edge : V × V => vertexFlow edge.1 edge.2)
              n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (tangentPositiveFlowEdges vertexFlow) L sigma
              (fun edge : V × V => vertexFlow edge.1 edge.2))
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          multiplier :=
  R.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus
    certificate fixedExceptional K h Phead X0 label residual portLoad
      cutTraffic vertexFlow hflowNonneg hdivergence hpositiveEndpoints
      htrafficFull hincidentVertex hlabelInjective hlabelPrime
      weightedResidual weightedPort hresidual hport labelUpper density
      hn hdensity hlabelUpper hlabelUpperLe hlabelUpperSq hL hsigma hN
      hscale trafficConstant incidentConstant tangentConstant width
      trafficError incidentError htotal hweightedIncident hmain herror
      hceiling lowerCard hlowerPos hlower hlowerScale

/-! ## Complete public declaration census -/

#check @tangentDistributedTotalTrafficLedger
#check @tangentDistributedLabelIncidentLedger
#check @tangentDistributedSupportCount
#check @tangentDistributedResidualCollisionUpper
#check TangentSameOrAdjacentRatioCell
#check @TangentFlowRespectsRatioCells
#check @TangentRatioCellGeometry
#check @tangentRatioCellPrefixMass
#check @tangentRatioCellTailPointwiseUpper
#check @tangentRatioCellCard
#check @tangentRatioCellLeftPrefixMass
#check tangentRatioCellCutTraffic
#check @tangentRatioCellUniformPortLoad
#check @tangentRatioCellPointwisePortUpper
#check @tangentRatioCellInternalResidual
#check tangentRatioCellBoundaryDivergence
#check tangentPositiveEdge_sameOrAdjacentRatioCell
#check @tangentPositiveEdge_locality_of_ratioCells
#check tangentRatioCellCutTraffic_nonneg
#check tangentRatioCellUniformPortLoad_nonneg
#check tangentRatioCellPrefixMass_add_tail_eq_bandSum
#check @abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
#check @tangentRatioCellUniformPortLoad_le_pointwisePortUpper
#check @abs_internalResidual_add_portLoad_le
#check abs_tangentRatioCellBoundaryDivergence_le_portLoad
#check tangentDistributedPositiveEdge_labels_ne
#check tangentDistributedPositiveEdge_locality
#check sum_tangentDistributedPositiveEdges_le_trafficLedger
#check @card_tangentPositiveFlowEdges_le_distributedSupportCount
#check sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
#check tangentDistributedPositiveEdges_boundary_eq_residual
#check tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
#check @tangentDistributedSplitRequest_factorizationBoundary_eq_residual
#check tangentDistributedLabelIncidentLedger_at_label
#check tangentDistributedLabelIncidentLedger_mul_le
#check tangentDistributedWeightedIncident_le
#check tangentDistributedIncidentTraffic_le_ledger
#check @tangentDistributedTotalRequestCount_le
#check tangentDistributedLabelRequestLoad_le
#check @tangentDistributedWeightedLabelRequestLoad_le
#check tangentDistributedWeightedLabelCensusUpper_le
#check @tangentDistributedPaperMainBudget
#check @tangentDistributedPaperErrorBudget
#check @tangentDistributedPaperCeilingBudget
#check tangentDistributedResidualCollisionUpper_le_paperBudgets
#check @tangentDistributedResidualCollisionUpper_le_of_paperSmallness
#check tangentDistributedRequest_census_small_of_paperBounds
#check tangentDistributedCollisionCensusBudget_le_eighth_of_paperBounds

#check BankPaperRealization.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus

end

end Erdos390.WholePaper
