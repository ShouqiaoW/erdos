import Erdos390.WholePaper.TangentSplitRequestLoads

/-! # Expanded statement audit for actual tangent split-request loads -/

/-!
This audit expands only the load identities and their substitution into the
counting bound.  It does not certify the analytic clean-list lower bound,
the pair-charge comparison, a paper earthmover traffic/support census, or
the final `≤ 1/8` arithmetic.  Those remain explicit premises of the
paper-specialized terminals in `TangentSplitRequestLoads`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! The paper's total request load is the literal sum of the ceiling split
counts. -/
example {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) :
    tangentTotalRequestCount (TangentSplitRequest edges L sigma flow) =
      ∑ edge ∈ edges,
        max 1 (Nat.ceil (4 * L * flow edge / sigma)) := by
  simpa only [tangentRequestTotal, tangentRequestCount] using
    tangentSplitTotalRequestCount_eq_requestTotal edges L sigma flow

/-! The label load is the same sum restricted to incident support edges. -/
example {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ) (label : ℕ) :
    tangentRequestLabelLoad
        (tangentSplitRequestSource
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
        (tangentSplitRequestTarget
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
        label =
      ∑ edge ∈ edges.filter
          (fun edge ↦ source edge = label ∨ target edge = label),
        max 1 (Nat.ceil (4 * L * flow edge / sigma)) := by
  simpa only [tangentIncidentRequestCount, tangentRequestTotal,
    tangentRequestCount, tangentIncidentEdges] using
      tangentSplitRequestLabelLoad_eq_incidentRequestCount
        edges source target L sigma flow label

/-! Neither of the following two request-load bounds is assumed: both are
the direct ceiling estimates on the actual split family. -/
example {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) (label : ℕ) :
    (tangentTotalRequestCount
        (TangentSplitRequest edges L sigma flow) : ℝ) ≤
        (4 * L / sigma) * (∑ edge ∈ edges, flow edge) + edges.card ∧
      (tangentRequestLabelLoad
        (tangentSplitRequestSource
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
        (tangentSplitRequestTarget
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
        label : ℝ) ≤
        (4 * L / sigma) *
            (∑ edge ∈ edges.filter
              (fun edge ↦ source edge = label ∨ target edge = label),
                flow edge) +
          (edges.filter
            (fun edge ↦ source edge = label ∨ target edge = label)).card := by
  constructor
  · simpa only [tangentSplitTotalRequestUpper] using
      cast_tangentSplitTotalRequestCount_le_upper
        edges flow hflow hL hsigma
  · simpa only [tangentSplitLabelRequestUpper,
      tangentIncidentFlowMass, tangentSupportDegree,
      tangentIncidentEdges] using
      cast_tangentSplitRequestLabelLoad_le_upper
        edges source target flow hflow hL hsigma label

/-! Expanded paper normalization of the final flow-side arithmetic. -/
example {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request =
      (((4 * L / sigma) * (∑ edge ∈ edges, flow edge) + edges.card) / n) *
          disjointCoefficient +
        (((tangentSplitRequestSource source request : ℕ) : ℝ) *
          ((4 * L / sigma) *
              (∑ edge ∈ edges.filter
                (fun edge ↦ source edge =
                    tangentSplitRequestSource source request ∨
                  target edge = tangentSplitRequestSource source request),
                flow edge) +
            (edges.filter
              (fun edge ↦ source edge =
                  tangentSplitRequestSource source request ∨
                target edge =
                  tangentSplitRequestSource source request)).card) / n) *
          sharedCoefficient +
        (((tangentSplitRequestTarget target request : ℕ) : ℝ) *
          ((4 * L / sigma) *
              (∑ edge ∈ edges.filter
                (fun edge ↦ source edge =
                    tangentSplitRequestTarget target request ∨
                  target edge = tangentSplitRequestTarget target request),
                flow edge) +
            (edges.filter
              (fun edge ↦ source edge =
                  tangentSplitRequestTarget target request ∨
                target edge =
                  tangentSplitRequestTarget target request)).card) / n) *
          sharedCoefficient := by
  rfl

/-! The abstract full-load theorem now consumes the proved split-request
loads and returns precisely the expanded normalized flow budget. -/
example {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (lists : TangentSplitRequest edges L sigma flow → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpair : ∀ left right, left ≠ right →
      tangentPairCollisionProbability lists hlist
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source left) right
            then sharedCoefficient *
                tangentSplitRequestSource source left / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target left) right
            then sharedCoefficient *
                tangentSplitRequestTarget target left / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentRequestCollisionMass lists hlist
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) request ≤
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request :=
  tangentSplitRequestCollisionMass_le_normalizedFlowBudget
    n edges source target flow lists hlist
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpair
      hflow hL hsigma request

/-! Given proofs of the displayed external flow/support census inequalities,
the ceiling ledger proves both paper-normalized load parameters; neither
normalized request load is itself a premise. -/
example {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount) :
    (tangentTotalRequestCount
        (TangentSplitRequest edges L sigma flow) : ℝ) / n ≤
        tangentSplitCensusTotalRequestUpper
          L sigma totalTraffic supportCount / n ∧
      ∀ label : ℕ,
        (label : ℝ) *
            (tangentRequestLabelLoad
              (tangentSplitRequestSource
                (edges := edges) (L := L) (sigma := sigma) (flow := flow)
                source)
              (tangentSplitRequestTarget
                (edges := edges) (L := L) (sigma := sigma) (flow := flow)
                target)
              label : ℝ) / n ≤
          (label : ℝ) *
            tangentSplitCensusLabelRequestUpper
              L sigma incidentTraffic supportCount label / n := by
  constructor
  · exact tangentSplitNormalizedTotalRequestCount_le_census
      n edges flow totalTraffic supportCount hflow hL hsigma
        htraffic hsupport
  · intro label
    exact tangentSplitNormalizedRequestLabelLoad_le_census
      n edges source target flow incidentTraffic supportCount label
        hflow hL hsigma hincident hsupport

/-! ## Supporting public API -/

#check tangentIncidentSplitRequestEquiv
#check tangentSupportDegree_le_edges_card
#check tangentIncidentFlowMass_le_totalFlowMass
#check tangentPositiveFlowEdges
#check mem_tangentPositiveFlowEdges
#check sum_tangentPositiveFlowEdges_eq_traffic
#check cast_tangentSplitRequestLabelLoad_le_totalFlowMass
#check cast_tangentPositiveFlowTotalRequestCount_le_traffic
#check cast_tangentPositiveFlowRequestLabelLoad_le_traffic
#check tangentSplitNormalizedTotalRequestUpper
#check tangentSplitNormalizedLabelRequestUpper
#check tangentSplitNormalizedTotalRequestCount_le_upper
#check tangentSplitNormalizedRequestLabelLoad_le_upper
#check cast_tangentSplitTotalRequestCount_le_census
#check cast_tangentSplitRequestLabelLoad_le_census
#check tangentSplitNormalizedCollisionCensusBudget
#check tangentSplitNormalizedCollisionFlowBudget_le_censusBudget
#check tangentSplitRequestCollisionMass_le_normalizedCensusBudget
#check tangentCleanSplitRequestCollisionMass_le_normalizedFlowBudget
#check tangentCleanSplitRequestCollisionMass_le_eighth_of_flowBudget
#check tangentCleanSplitRequestCollisionMass_le_eighth_of_censusBudget
#check tangentSplitEndpointsDistinct_of_normalizedFlowBudget
#check tangentSplitEndpointsDistinct_of_normalizedCensusBudget
#check BankPaperRealization.tangentPaperSplitRequest_sharp_finite_deletion_ledger
#check BankPaperRealization.tangentPaperSplitEndpointsDistinct_of_normalizedFlowBudget
#check BankPaperRealization.tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget

end

end Erdos390.WholePaper
