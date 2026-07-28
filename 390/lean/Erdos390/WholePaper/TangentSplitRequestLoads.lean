import Erdos390.WholePaper.TangentCollisionCounting
import Erdos390.WholePaper.BankPaperSharpCensus
import Erdos390.WholePaper.TangentStarTransport

/-!
# Actual request loads for the split tangent flow

This file instantiates the abstract collision-counting loads on the literal
request type

`Sigma e : edges, Fin (max 1 (ceil (4 * L * flow e / sigma)))`.

There are no request-count or collision-mass hypotheses below.  The total
load `K_req` is identified with the sum of the edge splitting counts, and
the label load `k_p` is identified with the same sum restricted to edges
incident to `p`.  The ceiling estimates then express both loads in terms of
the actual total/incident flow masses and support census.

The last layer substitutes those proved loads into
`tangentRequestCollisionMass_le_fullLoadBudget`.  It is deliberately
normalized in the paper's form

`K_req / n`, `p * k_p / n`.

For the actual paper guard set, the sharp bank census is recorded alongside
this load calculation.  The only list input retained by the collision
terminal is the exact request-wise cardinality lower bound; no analytic
density estimate is hidden here.

The paper-specialized terminals deliberately retain the following separate
mathematical inputs.  The sharp finite-deletion ledger does **not** itself
prove them.

* `hlowerPos` and `hlower`: a positive exact lower bound for every clean
  request list;
* `hpairArithmetic`: the explicit four-equation quotient comparison with
  the chosen shared/disjoint charges;
* either the literal flow-budget inequality, or proved total-traffic,
  incident-traffic, and support censuses;
* the final displayed flow/census budget inequality `≤ 1/8`.

Thus this module derives request loads from those flow censuses and passes
them to the proved counting/LLL terminal, but does not claim the still
missing analytic list density, earthmover census, or final parameter
arithmetic.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Exact reindexing of split requests -/

/-- Restricting split requests to those incident to one label is equivalent
to first restricting the edge finset and then splitting every retained
edge. -/
def tangentIncidentSplitRequestEquiv
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ) (label : ℕ) :
    {request : TangentSplitRequest edges L sigma flow //
      tangentRequestHasLabel
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) label request} ≃
      TangentSplitRequest
        (tangentIncidentEdges edges source target label) L sigma flow where
  toFun request :=
    ⟨⟨request.1.1.1, Finset.mem_filter.mpr
      ⟨request.1.1.2, by
        simpa only [tangentRequestHasLabel, tangentSplitRequestSource,
          tangentSplitRequestTarget, tangentSplitRequestEdge] using
            request.2⟩⟩, request.1.2⟩
  invFun request :=
    ⟨⟨⟨request.1.1, (Finset.mem_filter.mp request.1.2).1⟩,
        request.2⟩,
      by
        simpa only [tangentRequestHasLabel, tangentSplitRequestSource,
          tangentSplitRequestTarget, tangentSplitRequestEdge] using
            (Finset.mem_filter.mp request.1.2).2⟩
  left_inv request := by
    rcases request with ⟨⟨⟨edge, hedge⟩, index⟩, hlabel⟩
    rfl
  right_inv request := by
    rcases request with ⟨⟨edge, hedge⟩, index⟩
    rfl

/-- The abstract paper load `K_req`, on the actual split-request type, is
literally the sum of the edge splitting counts. -/
theorem tangentSplitTotalRequestCount_eq_requestTotal
    {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) :
    tangentTotalRequestCount (TangentSplitRequest edges L sigma flow) =
      tangentRequestTotal edges L sigma flow := by
  unfold tangentTotalRequestCount
  exact card_tangentSplitRequest edges L sigma flow

/-- The abstract label load `k_p`, on the actual split-request type, is
literally the sum of splitting counts over edges incident to `p`. -/
theorem tangentSplitRequestLabelLoad_eq_incidentRequestCount
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ) (label : ℕ) :
    tangentRequestLabelLoad
        (tangentSplitRequestSource
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
        (tangentSplitRequestTarget
          (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
        label =
      tangentIncidentRequestCount edges source target L sigma flow label := by
  classical
  rw [tangentRequestLabelLoad, ← Fintype.card_subtype]
  calc
    Fintype.card
        {request : TangentSplitRequest edges L sigma flow //
          tangentRequestHasLabel
            (tangentSplitRequestSource source)
            (tangentSplitRequestTarget target) label request} =
        Fintype.card
          (TangentSplitRequest
            (tangentIncidentEdges edges source target label)
              L sigma flow) :=
      Fintype.card_congr
        (tangentIncidentSplitRequestEquiv
          edges source target L sigma flow label)
    _ = tangentRequestTotal
          (tangentIncidentEdges edges source target label) L sigma flow :=
      card_tangentSplitRequest
        (tangentIncidentEdges edges source target label) L sigma flow
    _ = tangentIncidentRequestCount
          edges source target L sigma flow label := rfl

/-- The incident support degree is bounded by the complete support census.
This is the exact finite version of the harmless `+1`-per-edge ledger. -/
theorem tangentSupportDegree_le_edges_card
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P) (label : P) :
    tangentSupportDegree edges source target label ≤ edges.card := by
  unfold tangentSupportDegree tangentIncidentEdges
  exact Finset.card_filter_le _ _

/-- For a nonnegative edge flow, every incident-flow mass is bounded by the
complete flow mass on the supplied support. -/
theorem tangentIncidentFlowMass_le_totalFlowMass
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P) (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge) (label : P) :
    tangentIncidentFlowMass edges source target flow label ≤
      ∑ edge ∈ edges, flow edge := by
  unfold tangentIncidentFlowMass tangentIncidentEdges
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset _ _)
    (fun edge hedge _hnotIncident ↦ hflow edge hedge)

/-! ## The literal strictly-positive flow support -/

/-- Paper convention for the directed support: exactly the edges carrying
strictly positive flow. -/
def tangentPositiveFlowEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V → V → ℝ) : Finset (V × V) :=
  Finset.univ.filter fun edge ↦ 0 < flow edge.1 edge.2

/-- Membership in the positive-flow support is exactly strict positivity of
the corresponding directed edge flow. -/
@[simp]
theorem mem_tangentPositiveFlowEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {flow : V → V → ℝ} {edge : V × V} :
    edge ∈ tangentPositiveFlowEdges flow ↔ 0 < flow edge.1 edge.2 := by
  simp [tangentPositiveFlowEdges]

/-- On a globally nonnegative directed flow, restricting to the strictly
positive support preserves total traffic exactly. -/
theorem sum_tangentPositiveFlowEdges_eq_traffic
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V → V → ℝ) (hflow : ∀ source target, 0 ≤ flow source target) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2) = tangentFlowTraffic flow := by
  classical
  calc
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2) =
      ∑ edge : V × V, flow edge.1 edge.2 := by
        apply Finset.sum_subset
          (Finset.subset_univ (tangentPositiveFlowEdges flow))
        intro edge _hedge hedge
        have hnotPos : ¬0 < flow edge.1 edge.2 := by
          simpa only [mem_tangentPositiveFlowEdges] using hedge
        have hzero : flow edge.1 edge.2 = 0 :=
          le_antisymm (le_of_not_gt hnotPos) (hflow edge.1 edge.2)
        exact hzero
    _ = tangentFlowTraffic flow := by
      rw [tangentFlowTraffic, Fintype.sum_prod_type]

/-! ## The actual total and incident request upper bounds -/

/-- Real upper ledger for the total number of split requests. -/
def tangentSplitTotalRequestUpper
    {E : Type*} (edges : Finset E) (L sigma : ℝ) (flow : E → ℝ) : ℝ :=
  (4 * L / sigma) * (∑ edge ∈ edges, flow edge) + edges.card

/-- Real upper ledger for the number of split requests incident to one
label. -/
def tangentSplitLabelRequestUpper
    {E P : Type*} [DecidableEq E] [DecidableEq P]
    (edges : Finset E) (source target : E → P)
    (L sigma : ℝ) (flow : E → ℝ) (label : P) : ℝ :=
  (4 * L / sigma) *
      tangentIncidentFlowMass edges source target flow label +
    tangentSupportDegree edges source target label

/-- The literal split-request count is bounded by its real ceiling ledger. -/
theorem cast_tangentSplitTotalRequestCount_le_upper
    {E : Type*} (edges : Finset E) {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentTotalRequestCount
      (TangentSplitRequest edges L sigma flow) : ℝ) ≤
        tangentSplitTotalRequestUpper edges L sigma flow := by
  rw [tangentSplitTotalRequestCount_eq_requestTotal]
  exact cast_tangentRequestTotal_le edges flow hflow hL hsigma

/-- The literal load at one label is bounded by its incident-flow ceiling
ledger. -/
theorem cast_tangentSplitRequestLabelLoad_le_upper
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) (label : ℕ) :
    (tangentRequestLabelLoad
      (tangentSplitRequestSource
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
      (tangentSplitRequestTarget
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
      label : ℝ) ≤
        tangentSplitLabelRequestUpper
          edges source target L sigma flow label := by
  rw [tangentSplitRequestLabelLoad_eq_incidentRequestCount]
  exact cast_tangentIncidentRequestCount_le
    edges source target flow hflow hL hsigma label

/-- Coarser endpoint-label load bound needing no separate incident-flow
census: it uses only total flow mass and the complete support census. -/
theorem cast_tangentSplitRequestLabelLoad_le_totalFlowMass
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) (label : ℕ) :
    (tangentRequestLabelLoad
      (tangentSplitRequestSource
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
      (tangentSplitRequestTarget
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
      label : ℝ) ≤
        (4 * L / sigma) * (∑ edge ∈ edges, flow edge) +
          edges.card := by
  apply (cast_tangentSplitRequestLabelLoad_le_upper
    edges source target flow hflow hL hsigma label).trans
  unfold tangentSplitLabelRequestUpper
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (tangentIncidentFlowMass_le_totalFlowMass
        edges source target flow hflow label)
      (by positivity))
    (by
      exact_mod_cast tangentSupportDegree_le_edges_card
        edges source target label)

/-- The total request count on the literal positive support is bounded by
the paper's actual directed traffic plus one for every support edge. -/
theorem cast_tangentPositiveFlowTotalRequestCount_le_traffic
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V → V → ℝ) (hflow : ∀ source target, 0 ≤ flow source target)
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentTotalRequestCount
      (TangentSplitRequest (tangentPositiveFlowEdges flow) L sigma
        (fun edge ↦ flow edge.1 edge.2)) : ℝ) ≤
      (4 * L / sigma) * tangentFlowTraffic flow +
        (tangentPositiveFlowEdges flow).card := by
  have hcount := cast_tangentSplitTotalRequestCount_le_upper
    (tangentPositiveFlowEdges flow) (fun edge ↦ flow edge.1 edge.2)
      (by
        intro edge hedge
        exact (mem_tangentPositiveFlowEdges.mp hedge).le)
      hL hsigma
  simpa only [tangentSplitTotalRequestUpper,
    sum_tangentPositiveFlowEdges_eq_traffic flow hflow] using hcount

/-- Every endpoint-label request load on the literal positive support is
bounded by the same total directed traffic ledger.  A sharper caller may
replace this by its own incident-traffic census. -/
theorem cast_tangentPositiveFlowRequestLabelLoad_le_traffic
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V → V → ℝ)
    (hflow : ∀ source target, 0 ≤ flow source target)
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 0 < sigma)
    (vertexLabel : V → ℕ) (label : ℕ) :
    (tangentRequestLabelLoad
      (tangentSplitRequestSource
        (edges := tangentPositiveFlowEdges flow) (L := L) (sigma := sigma)
        (flow := fun edge : V × V ↦ flow edge.1 edge.2)
        (fun edge : V × V ↦ vertexLabel edge.1))
      (tangentSplitRequestTarget
        (edges := tangentPositiveFlowEdges flow) (L := L) (sigma := sigma)
        (flow := fun edge : V × V ↦ flow edge.1 edge.2)
        (fun edge : V × V ↦ vertexLabel edge.2))
      label : ℝ) ≤
      (4 * L / sigma) * tangentFlowTraffic flow +
        (tangentPositiveFlowEdges flow).card := by
  have hload := cast_tangentSplitRequestLabelLoad_le_totalFlowMass
    (tangentPositiveFlowEdges flow)
      (fun edge : V × V ↦ vertexLabel edge.1)
      (fun edge : V × V ↦ vertexLabel edge.2)
      (fun edge ↦ flow edge.1 edge.2)
      (by
        intro edge hedge
        exact (mem_tangentPositiveFlowEdges.mp hedge).le)
      hL hsigma label
  simpa only [sum_tangentPositiveFlowEdges_eq_traffic flow hflow] using hload

/-! ## Paper normalization `K_req/n` and `p*k_p/n` -/

/-- Proved upper ledger for `K_req/n`. -/
def tangentSplitNormalizedTotalRequestUpper
    {E : Type*} (n : ℕ) (edges : Finset E)
    (L sigma : ℝ) (flow : E → ℝ) : ℝ :=
  tangentSplitTotalRequestUpper edges L sigma flow / n

/-- Proved upper ledger for `p*k_p/n`. -/
def tangentSplitNormalizedLabelRequestUpper
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ) (label : ℕ) : ℝ :=
  (label : ℝ) *
      tangentSplitLabelRequestUpper
        edges source target L sigma flow label / n

/-- Dividing the total request-count estimate by the paper parameter preserves
the proved upper ledger. -/
theorem tangentSplitNormalizedTotalRequestCount_le_upper
    {E : Type*} (n : ℕ) (edges : Finset E)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentTotalRequestCount
        (TangentSplitRequest edges L sigma flow) : ℝ) / n ≤
      tangentSplitNormalizedTotalRequestUpper n edges L sigma flow := by
  unfold tangentSplitNormalizedTotalRequestUpper
  exact div_le_div_of_nonneg_right
    (cast_tangentSplitTotalRequestCount_le_upper
      edges flow hflow hL hsigma) (Nat.cast_nonneg n)

/-- The paper-normalized load at one label is bounded by its normalized
incident-flow ledger. -/
theorem tangentSplitNormalizedRequestLabelLoad_le_upper
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma) (label : ℕ) :
    (label : ℝ) *
        (tangentRequestLabelLoad
          (tangentSplitRequestSource
            (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
          (tangentSplitRequestTarget
            (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
          label : ℝ) / n ≤
      tangentSplitNormalizedLabelRequestUpper
        n edges source target L sigma flow label := by
  unfold tangentSplitNormalizedLabelRequestUpper
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact mul_le_mul_of_nonneg_left
    (cast_tangentSplitRequestLabelLoad_le_upper
      edges source target flow hflow hL hsigma label)
    (Nat.cast_nonneg label)

/-! ## Substitution of literal flow and support censuses -/

/-- Total request upper bound after substituting a proved traffic bound and
an edge-support census. -/
def tangentSplitCensusTotalRequestUpper
    (L sigma totalTraffic : ℝ) (supportCount : ℕ) : ℝ :=
  (4 * L / sigma) * totalTraffic + supportCount

/-- Label request upper bound after substituting a proved incident-traffic
bound and the global support census.  The global census is valid because an
incident support is a filter of the edge support. -/
def tangentSplitCensusLabelRequestUpper
    (L sigma : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount label : ℕ) : ℝ :=
  (4 * L / sigma) * incidentTraffic label + supportCount

/-- A traffic and support census bounds the literal total split-request
count. -/
theorem cast_tangentSplitTotalRequestCount_le_census
    {E : Type*} (edges : Finset E) {L sigma : ℝ} (flow : E → ℝ)
    (totalTraffic : ℝ) (supportCount : ℕ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hsupport : edges.card ≤ supportCount) :
    (tangentTotalRequestCount
      (TangentSplitRequest edges L sigma flow) : ℝ) ≤
        tangentSplitCensusTotalRequestUpper
          L sigma totalTraffic supportCount := by
  apply (cast_tangentSplitTotalRequestCount_le_upper
    edges flow hflow hL hsigma).trans
  unfold tangentSplitTotalRequestUpper
    tangentSplitCensusTotalRequestUpper
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left htraffic (by positivity)
  · exact_mod_cast hsupport

/-- Incident-traffic and support censuses bound the literal load at one
label. -/
theorem cast_tangentSplitRequestLabelLoad_le_census
    {E : Type*} [DecidableEq E]
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (incidentTraffic : ℕ → ℝ) (supportCount label : ℕ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (hincident : ∀ p,
      tangentIncidentFlowMass edges source target flow p ≤
        incidentTraffic p)
    (hsupport : edges.card ≤ supportCount) :
    (tangentRequestLabelLoad
      (tangentSplitRequestSource
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
      (tangentSplitRequestTarget
        (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
      label : ℝ) ≤
        tangentSplitCensusLabelRequestUpper
          L sigma incidentTraffic supportCount label := by
  apply (cast_tangentSplitRequestLabelLoad_le_upper
    edges source target flow hflow hL hsigma label).trans
  unfold tangentSplitLabelRequestUpper
    tangentSplitCensusLabelRequestUpper
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left (hincident label) (by positivity)
  · exact_mod_cast
      (tangentSupportDegree_le_edges_card
        edges source target label).trans hsupport

/-- Paper-normalized census bound for the actual total split-request load
`K_req / n`.  The request count is still a conclusion of the ceiling
ledger, not an input. -/
theorem tangentSplitNormalizedTotalRequestCount_le_census
    {E : Type*} (n : ℕ) (edges : Finset E)
    {L sigma : ℝ} (flow : E → ℝ)
    (totalTraffic : ℝ) (supportCount : ℕ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hsupport : edges.card ≤ supportCount) :
    (tangentTotalRequestCount
        (TangentSplitRequest edges L sigma flow) : ℝ) / n ≤
      tangentSplitCensusTotalRequestUpper
        L sigma totalTraffic supportCount / n := by
  exact div_le_div_of_nonneg_right
    (cast_tangentSplitTotalRequestCount_le_census
      edges flow totalTraffic supportCount hflow hL hsigma
        htraffic hsupport)
    (Nat.cast_nonneg n)

/-- Paper-normalized census bound for the actual endpoint-label load
`p * k_p / n`. -/
theorem tangentSplitNormalizedRequestLabelLoad_le_census
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (incidentTraffic : ℕ → ℝ) (supportCount label : ℕ)
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (hincident : ∀ p,
      tangentIncidentFlowMass edges source target flow p ≤
        incidentTraffic p)
    (hsupport : edges.card ≤ supportCount) :
    (label : ℝ) *
        (tangentRequestLabelLoad
          (tangentSplitRequestSource
            (edges := edges) (L := L) (sigma := sigma) (flow := flow) source)
          (tangentSplitRequestTarget
            (edges := edges) (L := L) (sigma := sigma) (flow := flow) target)
          label : ℝ) / n ≤
      (label : ℝ) *
        tangentSplitCensusLabelRequestUpper
          L sigma incidentTraffic supportCount label / n := by
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact mul_le_mul_of_nonneg_left
    (cast_tangentSplitRequestLabelLoad_le_census
      edges source target flow incidentTraffic supportCount label
        hflow hL hsigma hincident hsupport)
    (Nat.cast_nonneg label)

/-! ## Substitution in the full collision-load budget -/

/-- The fully expanded flow-side budget for one split request.  The two
coefficients are the constants in the pair estimate

`P(E_rs) ≤ disjointCoefficient/n`

plus `sharedCoefficient*p/n` for each shared endpoint label `p`. -/
def tangentSplitNormalizedCollisionFlowBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (request : TangentSplitRequest edges L sigma flow) : ℝ :=
  tangentSplitNormalizedTotalRequestUpper n edges L sigma flow *
      disjointCoefficient +
    tangentSplitNormalizedLabelRequestUpper
        n edges source target L sigma flow
          (tangentSplitRequestSource source request) *
      sharedCoefficient +
    tangentSplitNormalizedLabelRequestUpper
        n edges source target L sigma flow
          (tangentSplitRequestTarget target request) *
      sharedCoefficient

/-- Paper-normalized collision budget after substituting literal total
traffic, incident traffic, and support bounds. -/
def tangentSplitNormalizedCollisionCensusBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {flow : E → ℝ}
    (L sigma totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (request : TangentSplitRequest edges L sigma flow) : ℝ :=
  (tangentSplitCensusTotalRequestUpper
      L sigma totalTraffic supportCount / n) * disjointCoefficient +
    (((tangentSplitRequestSource (P := ℕ) source request : ℕ) : ℝ) *
        tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
          supportCount (tangentSplitRequestSource source request) / n) *
      sharedCoefficient +
    (((tangentSplitRequestTarget (P := ℕ) target request : ℕ) : ℝ) *
        tangentSplitCensusLabelRequestUpper L sigma incidentTraffic
          supportCount (tangentSplitRequestTarget target request) / n) *
      sharedCoefficient

/-- Substituting larger traffic and support censuses can only increase the
normalized collision budget. -/
theorem tangentSplitNormalizedCollisionFlowBudget_le_censusBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request ≤
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request := by
  have htotal : tangentSplitTotalRequestUpper edges L sigma flow ≤
      tangentSplitCensusTotalRequestUpper
        L sigma totalTraffic supportCount := by
    unfold tangentSplitTotalRequestUpper
      tangentSplitCensusTotalRequestUpper
    exact add_le_add
      (mul_le_mul_of_nonneg_left htraffic (by positivity))
      (by exact_mod_cast hsupport)
  have hlabel : ∀ label,
      tangentSplitLabelRequestUpper
          edges source target L sigma flow label ≤
        tangentSplitCensusLabelRequestUpper
          L sigma incidentTraffic supportCount label := by
    intro label
    unfold tangentSplitLabelRequestUpper
      tangentSplitCensusLabelRequestUpper
    exact add_le_add
      (mul_le_mul_of_nonneg_left (hincident label) (by positivity))
      (by
        exact_mod_cast
          (tangentSupportDegree_le_edges_card
            edges source target label).trans hsupport)
  unfold tangentSplitNormalizedCollisionFlowBudget
    tangentSplitNormalizedTotalRequestUpper
    tangentSplitNormalizedLabelRequestUpper
    tangentSplitNormalizedCollisionCensusBudget
  apply add_le_add
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ hdisjointCoefficient
      exact div_le_div_of_nonneg_right htotal (Nat.cast_nonneg n)
    · apply mul_le_mul_of_nonneg_right _ hsharedCoefficient
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact mul_le_mul_of_nonneg_left
        (hlabel (tangentSplitRequestSource source request))
        (Nat.cast_nonneg _)
  · apply mul_le_mul_of_nonneg_right _ hsharedCoefficient
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact mul_le_mul_of_nonneg_left
      (hlabel (tangentSplitRequestTarget target request))
      (Nat.cast_nonneg _)

/-- The abstract full-load collision estimate specialized to the literal
split request family.  Both `K_req` and the two `k_p` terms are eliminated
in favor of the proved edge-flow ledgers above. -/
theorem tangentSplitRequestCollisionMass_le_normalizedFlowBudget
    {E : Type*} [DecidableEq E]
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
          disjointCoefficient sharedCoefficient request := by
  let disjointCharge : ℝ := disjointCoefficient / n
  let sharedCharge : ℕ → ℝ := fun label ↦
    sharedCoefficient * label / n
  have hdisjointCharge : 0 ≤ disjointCharge := by
    exact div_nonneg hdisjointCoefficient (Nat.cast_nonneg n)
  have hsharedCharge : ∀ label, 0 ≤ sharedCharge label := by
    intro label
    exact div_nonneg
      (mul_nonneg hsharedCoefficient (Nat.cast_nonneg label))
      (Nat.cast_nonneg n)
  have hfull := tangentRequestCollisionMass_le_fullLoadBudget
    lists hlist
      (tangentSplitRequestSource source)
      (tangentSplitRequestTarget target)
      disjointCharge sharedCharge hdisjointCharge hsharedCharge
      (by
        intro left right hne
        simpa only [disjointCharge, sharedCharge] using
          hpair left right hne)
      request
  have htotal := cast_tangentSplitTotalRequestCount_le_upper
    edges flow hflow hL hsigma
  have hsource := cast_tangentSplitRequestLabelLoad_le_upper
    edges source target flow hflow hL hsigma
      (tangentSplitRequestSource source request)
  have htarget := cast_tangentSplitRequestLabelLoad_le_upper
    edges source target flow hflow hL hsigma
      (tangentSplitRequestTarget target request)
  calc
    tangentRequestCollisionMass lists hlist
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) request ≤
      (tangentTotalRequestCount
          (TangentSplitRequest edges L sigma flow) : ℝ) *
          disjointCharge +
        (tangentRequestLabelLoad
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          (tangentSplitRequestSource source request) : ℝ) *
            sharedCharge (tangentSplitRequestSource source request) +
        (tangentRequestLabelLoad
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          (tangentSplitRequestTarget target request) : ℝ) *
            sharedCharge (tangentSplitRequestTarget target request) := hfull
    _ ≤ tangentSplitTotalRequestUpper edges L sigma flow *
          disjointCharge +
        tangentSplitLabelRequestUpper edges source target L sigma flow
            (tangentSplitRequestSource source request) *
          sharedCharge (tangentSplitRequestSource source request) +
        tangentSplitLabelRequestUpper edges source target L sigma flow
            (tangentSplitRequestTarget target request) *
          sharedCharge (tangentSplitRequestTarget target request) := by
      exact add_le_add
        (add_le_add
          (mul_le_mul_of_nonneg_right htotal hdisjointCharge)
          (mul_le_mul_of_nonneg_right hsource
            (hsharedCharge (tangentSplitRequestSource source request))))
        (mul_le_mul_of_nonneg_right htarget
          (hsharedCharge (tangentSplitRequestTarget target request)))
    _ = tangentSplitNormalizedCollisionFlowBudget
          n edges source target L sigma flow
            disjointCoefficient sharedCoefficient request := by
      simp only [disjointCharge, sharedCharge,
        tangentSplitNormalizedCollisionFlowBudget,
        tangentSplitNormalizedTotalRequestUpper,
        tangentSplitNormalizedLabelRequestUpper]
      ring

/-- Flow-bound-facing form of the preceding theorem.  Its quantitative
inputs are total traffic, incident traffic, and support size; request counts
are still derived internally. -/
theorem tangentSplitRequestCollisionMass_le_normalizedCensusBudget
    {E : Type*} [DecidableEq E]
    (n : ℕ) (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (lists : TangentSplitRequest edges L sigma flow → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
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
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (request : TangentSplitRequest edges L sigma flow) :
    tangentRequestCollisionMass lists hlist
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) request ≤
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request := by
  exact (tangentSplitRequestCollisionMass_le_normalizedFlowBudget
    n edges source target flow lists hlist
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpair
      hflow hL hsigma request).trans
    (tangentSplitNormalizedCollisionFlowBudget_le_censusBudget
      n edges source target flow totalTraffic incidentTraffic supportCount
        disjointCoefficient sharedCoefficient
        hdisjointCoefficient hsharedCoefficient hL hsigma
        htraffic hincident hsupport request)

/-! ## Exact clean-list counting plus the proved load ledger -/

/-- For the literal clean common lists, exact list cardinality lower bounds
and four-equation arithmetic imply the expanded flow-side collision bound.
The actual `K_req` and `k_p` bounds are proved by the preceding theorem and
are not premises here. -/
theorem tangentCleanSplitRequestCollisionMass_le_normalizedFlowBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
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
    tangentRequestCollisionMass
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards)
        (fun request ↦ Finset.card_pos.mp
          ((hlowerPos request).trans_le (hlower request)))
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) request ≤
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request := by
  let lists := tangentSplitCleanMultiplierLists
    edges source target L sigma flow n K h Phead X0 y
      dedicatedRows numericalGuards
  let hlist : ∀ request, (lists request).Nonempty := fun request ↦
    Finset.card_pos.mp ((hlowerPos request).trans_le (hlower request))
  apply tangentSplitRequestCollisionMass_le_normalizedFlowBudget
    n edges source target flow lists hlist
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient
  · intro left right hne
    apply (tangentPairCollisionProbability_le_budgetQuotient
      lists hlist lowerCard hlowerPos
        (by
          intro request
          simpa only [lists] using hlower request)
        (tangentBroadUpper n K h)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target)
        (by
          intro request side
          cases side with
          | source =>
              simpa only [tangentEndpointLabel,
                tangentSplitRequestSource, tangentSplitRequestEdge] using
                (hprime request.1.1 request.1.2).1
          | target =>
              simpa only [tangentEndpointLabel,
                tangentSplitRequestTarget, tangentSplitRequestEdge] using
                (hprime request.1.1 request.1.2).2)
        (by
          intro request side multiplier hmultiplier
          simpa only [lists, tangentSplitCleanMultiplierLists] using
            tangentCleanMultiplierLists_endpoint_le_broadUpper
              n K h Phead X0 y
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              dedicatedRows numericalGuards
              (by
                intro splitRequest
                exact ⟨
                  (hprime splitRequest.1.1 splitRequest.1.2).1.pos,
                  (hprime splitRequest.1.1 splitRequest.1.2).2.pos⟩)
              request side multiplier hmultiplier)
        left right).trans
    rw [tangentPairEndpointBudgetQuotient, dif_pos hne]
    exact hpairArithmetic left right hne
  · exact hflow
  · exact hL
  · exact hsigma

/-- The literal `1/8` terminal.  Its last premise is the displayed
flow/degree arithmetic, not a request-load bound and not a collision-mass
bound. -/
theorem tangentCleanSplitRequestCollisionMass_le_eighth_of_flowBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
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
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∀ request,
      tangentRequestCollisionMass
          (tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 y
              dedicatedRows numericalGuards)
          (fun request ↦ Finset.card_pos.mp
            ((hlowerPos request).trans_le (hlower request)))
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) request ≤ 1 / 8 := by
  intro request
  exact (tangentCleanSplitRequestCollisionMass_le_normalizedFlowBudget
    n K h Phead X0 y edges source target flow
      dedicatedRows numericalGuards lowerCard hlowerPos hlower hprime
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma request).trans (hbudget request)

/-- `1/8` terminal after substituting the paper-facing traffic and support
census.  In particular, its premises still contain no total request count,
incident request count, or collision mass. -/
theorem tangentCleanSplitRequestCollisionMass_le_eighth_of_censusBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
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
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∀ request,
      tangentRequestCollisionMass
          (tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 y
              dedicatedRows numericalGuards)
          (fun request ↦ Finset.card_pos.mp
            ((hlowerPos request).trans_le (hlower request)))
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) request ≤ 1 / 8 := by
  intro request
  apply (tangentCleanSplitRequestCollisionMass_le_normalizedFlowBudget
    n K h Phead X0 y edges source target flow
      dedicatedRows numericalGuards lowerCard hlowerPos hlower hprime
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma request).trans
  exact (tangentSplitNormalizedCollisionFlowBudget_le_censusBudget
    n edges source target flow totalTraffic incidentTraffic supportCount
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hL hsigma
      htraffic hincident hsupport request).trans (hbudget request)

/-- Collision-free common multipliers for the actual split request type,
with all request-load bounds discharged by the flow ledger. -/
theorem tangentSplitEndpointsDistinct_of_normalizedFlowBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
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
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 y
              dedicatedRows numericalGuards request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  let hlist : ∀ request,
      (tangentSplitCleanMultiplierLists
        edges source target L sigma flow n K h Phead X0 y
          dedicatedRows numericalGuards request).Nonempty := fun request ↦
    Finset.card_pos.mp ((hlowerPos request).trans_le (hlower request))
  apply tangentSplitEndpointsDistinct_of_cleanRequestMass
    edges source target L sigma flow n K h Phead X0 y
      dedicatedRows numericalGuards
  · intro request
    simpa only [tangentSplitRequestSource, tangentSplitRequestTarget,
      tangentSplitRequestEdge] using
        hsourceTarget request.1.1 request.1.2
  · exact tangentCleanSplitRequestCollisionMass_le_eighth_of_flowBudget
      n K h Phead X0 y edges source target flow
        dedicatedRows numericalGuards lowerCard hlowerPos hlower hprime
        disjointCoefficient sharedCoefficient
        hdisjointCoefficient hsharedCoefficient hpairArithmetic
        hflow hL hsigma hbudget

/-- Collision-free split endpoints after replacing the literal flow ledger
by proved total-traffic, incident-traffic, and sparse-support censuses.  No
request-count or collision-mass bound occurs among the premises. -/
theorem tangentSplitEndpointsDistinct_of_normalizedCensusBudget
    {E : Type*} [DecidableEq E]
    (n K h Phead X0 y : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 y
            dedicatedRows numericalGuards request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) left right : ℝ) /
          (lowerCard left * lowerCard right) ≤
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
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 y
              dedicatedRows numericalGuards request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  apply tangentSplitEndpointsDistinct_of_normalizedFlowBudget
    n K h Phead X0 y edges source target flow
      dedicatedRows numericalGuards hsourceTarget
      lowerCard hlowerPos hlower hprime
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma
  intro request
  exact (tangentSplitNormalizedCollisionFlowBudget_le_censusBudget
    n edges source target flow totalTraffic incidentTraffic supportCount
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hL hsigma
      htraffic hincident hsupport request).trans (hbudget request)

/-! ## The actual sharp paper bank and row census -/

namespace BankPaperRealization

set_option maxHeartbeats 800000 in
/-- The existing sharp bank census, reindexed by one literal split request.
This records that the paper's dedicated-row loss is zero and that numerical
guards cost at most `4 + 4 * bankPaperSharpMarkerBudget n`. -/
theorem tangentPaperSplitRequest_sharp_finite_deletion_ledger
    {c : ℝ} {depth n M W K h Phead X0 : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    {E : Type*} [DecidableEq E]
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (edges : Finset E) (source target : E → ℕ)
    (L sigma : ℝ) (flow : E → ℝ)
    (request : TangentSplitRequest edges L sigma flow)
    (hfixedTail : fixedExceptional ⊆ Finset.Ioc (2 * n) M)
    (hTwoW : 2 ≤ W) (hPrefix : 2 * depth + 1 ≤ W)
    (hWmin : W < min
      (tangentSplitRequestSource source request)
      (tangentSplitRequestTarget target request))
    (hmaxY : max
      (tangentSplitRequestSource source request)
      (tangentSplitRequestTarget target request) ≤ yNat n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hmaxPrime : (max
      (tangentSplitRequestSource source request)
      (tangentSplitRequestTarget target request)).Prime)
    (hminPrime : (min
      (tangentSplitRequestSource source request)
      (tangentSplitRequestTarget target request)).Prime) :
    (tangentCommonMultiplierInterval n K h
      (max (tangentSplitRequestSource source request)
        (tangentSplitRequestTarget target request))
      (min (tangentSplitRequestSource source request)
        (tangentSplitRequestTarget target request))).card ≤
      (tangentSplitCleanMultiplierLists
        edges source target L sigma flow n K h Phead X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h
          (max (tangentSplitRequestSource source request)
            (tangentSplitRequestTarget target request))
          (min (tangentSplitRequestSource source request)
            (tangentSplitRequestTarget target request)))).card +
      (tangentExceptionalMultipliers n X0 (yNat n)
        (tangentCommonMultiplierInterval n K h
          (max (tangentSplitRequestSource source request)
            (tangentSplitRequestTarget target request))
          (min (tangentSplitRequestSource source request)
            (tangentSplitRequestTarget target request)))).card +
      4 + 4 * bankPaperSharpMarkerBudget n := by
  simpa only [tangentSplitCleanMultiplierLists,
    tangentCleanMultiplierLists] using
    R.tangentPaperCommonMultiplier_sharp_finite_deletion_ledger
      certificate fixedExceptional hfixedTail hTwoW hPrefix hWmin
        min_le_max hmaxY hyCutoff hmaxPrime hminPrime

/-- Actual-paper guard/row specialization of the collision-free split
terminal.  The request-wise exact list-cardinality lower bound is the only
remaining list-density input. -/
theorem tangentPaperSplitEndpointsDistinct_of_normalizedFlowBudget
    {c : ℝ} {depth n M : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    {E : Type*} [DecidableEq E]
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (K h Phead X0 : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ leftRequest rightRequest,
      ∀ _hne : leftRequest ≠ rightRequest,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          leftRequest rightRequest : ℝ) /
          (lowerCard leftRequest * lowerCard rightRequest) ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source leftRequest) rightRequest
            then sharedCoefficient *
                tangentSplitRequestSource source leftRequest / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target leftRequest) rightRequest
            then sharedCoefficient *
                tangentSplitRequestTarget target leftRequest / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionFlowBudget
        n edges source target L sigma flow
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  exact tangentSplitEndpointsDistinct_of_normalizedFlowBudget
    n K h Phead X0 (yNat n) edges source target flow
      R.tangentPaperDedicatedRows
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      hsourceTarget lowerCard hlowerPos hlower hprime
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma hbudget

/-- Actual-paper bank/guard specialization with the split-request loads
discharged by external total-traffic, incident-traffic, and sparse-support
censuses.  The exact request-wise list lower bound remains explicit. -/
theorem tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget
    {c : ℝ} {depth n M : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    {E : Type*} [DecidableEq E]
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (K h Phead X0 : ℕ)
    (edges : Finset E) (source target : E → ℕ)
    {L sigma : ℝ} (flow : E → ℝ)
    (hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge)
    (lowerCard : TangentSplitRequest edges L sigma flow → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          edges source target L sigma flow n K h Phead X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card)
    (hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime)
    (totalTraffic : ℝ) (incidentTraffic : ℕ → ℝ)
    (supportCount : ℕ)
    (disjointCoefficient sharedCoefficient : ℝ)
    (hdisjointCoefficient : 0 ≤ disjointCoefficient)
    (hsharedCoefficient : 0 ≤ sharedCoefficient)
    (hpairArithmetic : ∀ leftRequest rightRequest,
      ∀ _hne : leftRequest ≠ rightRequest,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          leftRequest rightRequest : ℝ) /
          (lowerCard leftRequest * lowerCard rightRequest) ≤
        disjointCoefficient / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source leftRequest) rightRequest
            then sharedCoefficient *
                tangentSplitRequestSource source leftRequest / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target leftRequest) rightRequest
            then sharedCoefficient *
                tangentSplitRequestTarget target leftRequest / n
            else 0))
    (hflow : ∀ edge ∈ edges, 0 ≤ flow edge)
    (hL : 0 < L) (hsigma : 0 < sigma)
    (htraffic : (∑ edge ∈ edges, flow edge) ≤ totalTraffic)
    (hincident : ∀ label,
      tangentIncidentFlowMass edges source target flow label ≤
        incidentTraffic label)
    (hsupport : edges.card ≤ supportCount)
    (hbudget : ∀ request,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          totalTraffic incidentTraffic supportCount
          disjointCoefficient sharedCoefficient request ≤ 1 / 8) :
    ∃ multiplier : TangentSplitRequest edges L sigma flow → ℕ,
      (∀ request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            edges source target L sigma flow n K h Phead X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests edges L sigma flow)
        (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) multiplier := by
  exact tangentSplitEndpointsDistinct_of_normalizedCensusBudget
    n K h Phead X0 (yNat n) edges source target flow
      R.tangentPaperDedicatedRows
      (R.tangentPaperNumericalGuardSet certificate fixedExceptional)
      hsourceTarget lowerCard hlowerPos hlower hprime
      totalTraffic incidentTraffic supportCount
      disjointCoefficient sharedCoefficient
      hdisjointCoefficient hsharedCoefficient hpairArithmetic
      hflow hL hsigma htraffic hincident hsupport hbudget

end BankPaperRealization

end

end Erdos390.WholePaper
