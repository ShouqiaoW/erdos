import Erdos390.WholePaper.TangentStarTransport
import Erdos390.WholePaper.TangentPairArithmetic

/-!
# Star-transport bridge to the paper split-request terminal

The current post-Saias development does not yet expose one literal finite
type of medium-prime residual coordinates.  This file therefore keeps a
finite vertex type `V`, an injective prime-label map, and its zero-sum
residual explicit.  It does not assert selector or collision existence.

For those honest inputs, the already-proved star transport is restricted to
its strictly positive directed support.  The restriction preserves its
factorization boundary, has the prescribed residual divergence, has total
and every label-incident traffic bounded by the residual `ℓ¹` mass, and has
at most twice as many support edges as vertices.  These proved censuses are
then supplied to
`tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget`.

The final theorem leaves visible exactly the estimates that a literal
post-Saias instantiation must still provide: zero residual mass in the
chosen band, injective prime labels and their cutoff bounds, a sharp enough
per-label incident-traffic estimate, clean-list cardinality/density, and the
displayed residual-`ℓ¹` collision smallness.
No selector, local earthmover estimate, or collision-free multiplier is
fabricated outside the existing terminal.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Literal positive star support and its census quantities -/

/-- Strictly positive directed edges of the star transport. -/
def tangentStarPositiveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) : Finset (V × V) :=
  tangentPositiveFlowEdges (tangentStarFlow pivot residual)

/-- Natural-number source label on a star edge. -/
def tangentStarEdgeSource
    {V : Type*} (label : V → ℕ) (edge : V × V) : ℕ :=
  label edge.1

/-- Natural-number target label on a star edge. -/
def tangentStarEdgeTarget
    {V : Type*} (label : V → ℕ) (edge : V × V) : ℕ :=
  label edge.2

/-- Actual mass carried by one directed star edge. -/
def tangentStarEdgeFlow
    {V : Type*} [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (edge : V × V) : ℝ :=
  tangentStarFlow pivot residual edge.1 edge.2

/-- Full residual `ℓ¹` mass used as a total- and incident-traffic census. -/
def tangentStarResidualL1
    {V : Type*} [Fintype V] (residual : V → ℝ) : ℝ :=
  ∑ v : V, |residual v|

/-- Honest coarse per-label census.  A future local earthmover may replace
this constant bound by the sharper paper label-load estimate. -/
def tangentStarResidualL1IncidentTraffic
    {V : Type*} [Fintype V] (residual : V → ℝ) (_label : ℕ) : ℝ :=
  tangentStarResidualL1 residual

/-- Literal incident mass of the positive star support at one natural-number
label.  This is the quantity to which a sharp paper label-load estimate
should be applied. -/
def tangentStarLabelIncidentTraffic
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (label : V → ℕ) (q : ℕ) : ℝ :=
  tangentIncidentFlowMass
    (tangentStarPositiveEdges pivot residual)
    (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
    (tangentStarEdgeFlow pivot residual) q

/-- Coarse support census allowing the two pivot orientations per vertex. -/
def tangentStarSupportCount (V : Type*) [Fintype V] : ℕ :=
  2 * Fintype.card V

/-- Membership in the positive star support is equivalent to strict positivity
of the corresponding star-edge flow. -/
@[simp]
theorem mem_tangentStarPositiveEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {pivot : V} {residual : V → ℝ} {edge : V × V} :
    edge ∈ tangentStarPositiveEdges pivot residual ↔
      0 < tangentStarEdgeFlow pivot residual edge := by
  simp [tangentStarPositiveEdges, tangentStarEdgeFlow]

/-- Every directed star-edge flow is nonnegative. -/
theorem tangentStarEdgeFlow_nonneg
    {V : Type*} [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (edge : V × V) :
    0 ≤ tangentStarEdgeFlow pivot residual edge := by
  exact tangentStarFlow_nonneg pivot residual edge.1 edge.2

/-- Injective vertex labels make the endpoints of every positive star edge
distinct as natural numbers. -/
theorem tangentStarPositiveEdge_labels_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {pivot : V} {residual : V → ℝ} {label : V → ℕ}
    (hlabel : Function.Injective label) {edge : V × V}
    (hedge : edge ∈ tangentStarPositiveEdges pivot residual) :
    tangentStarEdgeSource label edge ≠ tangentStarEdgeTarget label edge := by
  intro hlabels
  have hvertices : edge.1 = edge.2 := by
    apply hlabel
    simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using hlabels
  have hpos : 0 < tangentStarEdgeFlow pivot residual edge :=
    mem_tangentStarPositiveEdges.mp hedge
  have hzero : tangentStarEdgeFlow pivot residual edge = 0 := by
    rw [tangentStarEdgeFlow, hvertices]
    exact tangentStarFlow_self pivot residual edge.2
  rw [hzero] at hpos
  exact (lt_irrefl 0 hpos).elim

/-- Restriction to the positive support preserves the exact star traffic. -/
theorem sum_tangentStarPositiveEdges_eq_traffic
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) :
    (∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge) =
      tangentFlowTraffic (tangentStarFlow pivot residual) := by
  simpa only [tangentStarPositiveEdges, tangentStarEdgeFlow] using
    sum_tangentPositiveFlowEdges_eq_traffic
      (tangentStarFlow pivot residual)
      (tangentStarFlow_nonneg pivot residual)

/-- Exact traffic on the literal positive support: one absolute residual
mass for every non-pivot vertex. -/
theorem sum_tangentStarPositiveEdges_eq_sum_erase_abs
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) :
    (∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge) =
      ∑ v ∈ (Finset.univ : Finset V).erase pivot, |residual v| := by
  rw [sum_tangentStarPositiveEdges_eq_traffic,
    tangentStarFlow_traffic_eq_sum_erase_abs]

/-- Total positive-support traffic is bounded by the full residual `ℓ¹`
mass. -/
theorem sum_tangentStarPositiveEdges_le_residualL1
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) :
    (∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge) ≤
      tangentStarResidualL1 residual := by
  rw [sum_tangentStarPositiveEdges_eq_traffic]
  exact tangentStarFlow_traffic_le_sum_abs pivot residual

/-- Every natural-number label sees at most the full residual `ℓ¹` traffic.
This follows from the literal incident-edge filter, not from an assumed
label census. -/
theorem tangentStarIncidentFlowMass_le_residualL1
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (label : V → ℕ) (q : ℕ) :
    tangentStarLabelIncidentTraffic pivot residual label q ≤
      tangentStarResidualL1IncidentTraffic residual q := by
  unfold tangentStarLabelIncidentTraffic
  calc
    tangentIncidentFlowMass
        (tangentStarPositiveEdges pivot residual)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (tangentStarEdgeFlow pivot residual) q ≤
      ∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge :=
      tangentIncidentFlowMass_le_totalFlowMass
        (tangentStarPositiveEdges pivot residual)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (tangentStarEdgeFlow pivot residual)
        (fun edge _hedge ↦ tangentStarEdgeFlow_nonneg pivot residual edge) q
    _ ≤ tangentStarResidualL1 residual :=
      sum_tangentStarPositiveEdges_le_residualL1 pivot residual
    _ = tangentStarResidualL1IncidentTraffic residual q := rfl

/-- The positive star support has at most two pivot-oriented edges per
vertex.  This deliberately simple finite bound is sufficient to discharge
the support premise of the census terminal. -/
theorem card_tangentStarPositiveEdges_le_supportCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) :
    (tangentStarPositiveEdges pivot residual).card ≤
      tangentStarSupportCount V := by
  classical
  let incoming : Finset (V × V) :=
    (Finset.univ : Finset V).product {pivot}
  let outgoing : Finset (V × V) :=
    ({pivot} : Finset V).product Finset.univ
  have hsubset : tangentStarPositiveEdges pivot residual ⊆
      incoming ∪ outgoing := by
    intro edge hedge
    rcases edge with ⟨source, target⟩
    have hpos : 0 < tangentStarFlow pivot residual source target := by
      simpa only [tangentStarEdgeFlow] using
        (mem_tangentStarPositiveEdges.mp hedge)
    rcases tangentStarFlow_pos_incident_pivot hpos with
      ⟨hsource, _htarget⟩ | ⟨_hsource, htarget⟩
    · apply Finset.mem_union_right incoming
      change (source, target) ∈
        ({pivot} : Finset V).product Finset.univ
      exact Finset.mem_product.mpr
        ⟨Finset.mem_singleton.mpr hsource, Finset.mem_univ target⟩
    · apply Finset.mem_union_left outgoing
      change (source, target) ∈
        (Finset.univ : Finset V).product {pivot}
      exact Finset.mem_product.mpr
        ⟨Finset.mem_univ source, Finset.mem_singleton.mpr htarget⟩
  calc
    (tangentStarPositiveEdges pivot residual).card ≤
        (incoming ∪ outgoing).card := Finset.card_le_card hsubset
    _ ≤ incoming.card + outgoing.card :=
      Finset.card_union_le incoming outgoing
    _ = tangentStarSupportCount V := by
      simp [incoming, outgoing, tangentStarSupportCount, two_mul]

/-! ## Boundary preservation through positive support and request splitting -/

/-- Multiplying by an arbitrary edge test does not change a globally
nonnegative star sum when it is restricted to the strictly positive
support. -/
theorem sum_tangentStarPositiveEdges_mul_eq_full
    {V : Type*} [Fintype V] [DecidableEq V]
    (pivot : V) (residual : V → ℝ) (value : V × V → ℝ) :
    (∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge * value edge) =
      ∑ edge : V × V,
        tangentStarEdgeFlow pivot residual edge * value edge := by
  classical
  apply Finset.sum_subset
    (Finset.subset_univ (tangentStarPositiveEdges pivot residual))
  intro edge _hedge hedge
  have hnotPos : ¬0 < tangentStarEdgeFlow pivot residual edge := by
    simpa only [mem_tangentStarPositiveEdges] using hedge
  have hzero : tangentStarEdgeFlow pivot residual edge = 0 :=
    le_antisymm (le_of_not_gt hnotPos)
      (tangentStarEdgeFlow_nonneg pivot residual edge)
  simp only [hzero, zero_mul]

/-- The positive star support has exactly the factorization boundary of the
input residual vector. -/
theorem tangentStarPositiveEdges_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0)
    (label : V → ℕ) (p : ℕ) :
    (∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge *
          (((tangentStarEdgeSource label edge).factorization p : ℝ) -
            ((tangentStarEdgeTarget label edge).factorization p : ℝ))) =
      ∑ v : V, residual v * (label v).factorization p := by
  calc
    (∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge *
          (((tangentStarEdgeSource label edge).factorization p : ℝ) -
            ((tangentStarEdgeTarget label edge).factorization p : ℝ))) =
      ∑ edge : V × V,
        tangentStarEdgeFlow pivot residual edge *
          (((tangentStarEdgeSource label edge).factorization p : ℝ) -
            ((tangentStarEdgeTarget label edge).factorization p : ℝ)) :=
      sum_tangentStarPositiveEdges_mul_eq_full pivot residual
        (fun edge ↦
          (((tangentStarEdgeSource label edge).factorization p : ℝ) -
            ((tangentStarEdgeTarget label edge).factorization p : ℝ)))
    _ = ∑ v : V, residual v * (label v).factorization p := by
      simpa only [tangentStarEdgeFlow, tangentStarEdgeSource,
        tangentStarEdgeTarget] using
        tangentStarFlow_factorizationBoundary_eq_residual hsum label p

/-- Equal request splitting preserves the preceding residual boundary
exactly.  This is the direct star-to-`tangentUpdate_valuation` interface. -/
theorem tangentStarSplitRequest_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0)
    (label : V → ℕ) (L sigma : ℝ) (p : ℕ) :
    (∑ request : TangentSplitRequest
          (tangentStarPositiveEdges pivot residual) L sigma
            (tangentStarEdgeFlow pivot residual),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : ℝ) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : ℝ))) =
      ∑ v : V, residual v * (label v).factorization p := by
  calc
    (∑ request : TangentSplitRequest
          (tangentStarPositiveEdges pivot residual) L sigma
            (tangentStarEdgeFlow pivot residual),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : ℝ) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : ℝ))) =
      ∑ edge ∈ tangentStarPositiveEdges pivot residual,
        tangentStarEdgeFlow pivot residual edge *
          (((tangentStarEdgeSource label edge).factorization p : ℝ) -
            ((tangentStarEdgeTarget label edge).factorization p : ℝ)) := by
      simpa only using
        sum_tangentSplitRequestWeight_mul_sub
          (tangentStarPositiveEdges pivot residual)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (tangentStarEdgeFlow pivot residual)
          (fun q ↦ (q.factorization p : ℝ))
    _ = ∑ v : V, residual v * (label v).factorization p :=
      tangentStarPositiveEdges_factorizationBoundary_eq_residual
        hsum label p

/-! ## Conditional paper connector -/

namespace BankPaperRealization

/-- Minimal honest connector from a finite zero-sum residual to the paper
collision-free split requests.

The star supplies divergence, exact request boundary, total traffic,
incident traffic, and sparse support.  The explicit remaining hypotheses are
the prime-label geometry, a caller-proved label-incident bound, clean-list
density, and the final displayed residual-`ℓ¹` census smallness.  In
particular, `hlower` and `hlowerScale`
are not selector existence claims: they are the still-missing common-list
cardinality estimates for the actual post-Saias labels. -/
theorem tangentPaperStarSplitEndpointsDistinct_of_residualL1Census
    {V : Type*} [Fintype V] [DecidableEq V]
    {c : ℝ} {depth n M : ℕ}
    {left right : ℕ → ℕ} {changed : Finset ℕ}
    (R : BankPaperRealization n M)
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixedExceptional : Finset ℕ)
    (K h Phead X0 : ℕ)
    (pivot : V) (residual : V → ℝ) (label : V → ℕ)
    (hsum : (∑ v : V, residual v) = 0)
    (hlabelInjective : Function.Injective label)
    (hlabelPrime : ∀ v, (label v).Prime)
    (incidentTraffic : ℕ → ℝ)
    (hincidentTraffic : ∀ q,
      tangentStarLabelIncidentTraffic pivot residual label q ≤
        incidentTraffic q)
    (labelUpper : ℕ) (density : ℝ)
    (hn : 0 < n) (hdensity : 0 < density)
    (hlabelUpper : ∀ v, label v ≤ labelUpper)
    (hlabelUpperLe : (labelUpper : ℝ) ≤ n)
    (hlabelUpperSq : (labelUpper : ℝ) ^ 2 ≤ n)
    {L sigma : ℝ} (hL : 0 < L) (hsigma : 0 < sigma)
    (lowerCard : TangentSplitRequest
      (tangentStarPositiveEdges pivot residual) L sigma
        (tangentStarEdgeFlow pivot residual) → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists
          (tangentStarPositiveEdges pivot residual)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (tangentStarEdgeFlow pivot residual)
          n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : ∀ request side,
      density * n ≤ (lowerCard request : ℝ) *
        tangentEndpointLabel
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          side request)
    (hsmall : ∀ request : TangentSplitRequest
        (tangentStarPositiveEdges pivot residual) L sigma
          (tangentStarEdgeFlow pivot residual),
      4 * (tangentSplitCensusTotalRequestUpper L sigma
            (tangentStarResidualL1 residual)
            (tangentStarSupportCount V) / n) +
        (((tangentSplitRequestSource (P := ℕ)
              (tangentStarEdgeSource label) request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            incidentTraffic
            (tangentStarSupportCount V)
            (tangentSplitRequestSource (tangentStarEdgeSource label)
              request) / n) +
        (((tangentSplitRequestTarget (P := ℕ)
              (tangentStarEdgeTarget label) request : ℕ) : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            incidentTraffic
            (tangentStarSupportCount V)
            (tangentSplitRequestTarget (tangentStarEdgeTarget label)
              request) / n) ≤ density ^ 2 / 24) :
    (∀ v, tangentFlowDivergence (tangentStarFlow pivot residual) v =
        residual v) ∧
      (∀ p,
        (∑ request : TangentSplitRequest
              (tangentStarPositiveEdges pivot residual) L sigma
                (tangentStarEdgeFlow pivot residual),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource (tangentStarEdgeSource label)
                    request).factorization p : ℝ) -
                ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                    request).factorization p : ℝ))) =
          ∑ v : V, residual v * (label v).factorization p) ∧
      ∃ multiplier : TangentSplitRequest
          (tangentStarPositiveEdges pivot residual) L sigma
            (tangentStarEdgeFlow pivot residual) → ℕ,
        (∀ request,
          multiplier request ∈
            tangentSplitCleanMultiplierLists
              (tangentStarPositiveEdges pivot residual)
              (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
              L sigma (tangentStarEdgeFlow pivot residual)
              n K h Phead X0 (yNat n) R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (tangentStarPositiveEdges pivot residual) L sigma
              (tangentStarEdgeFlow pivot residual))
          (tangentSplitRequestSource (tangentStarEdgeSource label))
          (tangentSplitRequestTarget (tangentStarEdgeTarget label))
          multiplier := by
  let edges := tangentStarPositiveEdges pivot residual
  let source := tangentStarEdgeSource label
  let target := tangentStarEdgeTarget label
  let flow := tangentStarEdgeFlow pivot residual
  have hsourceTarget : ∀ edge ∈ edges, source edge ≠ target edge := by
    intro edge hedge
    exact tangentStarPositiveEdge_labels_ne hlabelInjective hedge
  have hflow : ∀ edge ∈ edges, 0 ≤ flow edge := by
    intro edge _hedge
    exact tangentStarEdgeFlow_nonneg pivot residual edge
  have hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime := by
    intro edge _hedge
    exact ⟨hlabelPrime edge.1, hlabelPrime edge.2⟩
  have hrequestDistinct : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentSplitRequestSource source request ≠
        tangentSplitRequestTarget target request := by
    intro request
    simpa only [tangentSplitRequestSource, tangentSplitRequestTarget,
      tangentSplitRequestEdge] using
        hsourceTarget request.1.1 request.1.2
  have hrequestPrime : ∀ request : TangentSplitRequest edges L sigma flow,
      ∀ side : TangentEndpointSide,
        (tangentEndpointLabel
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) side request).Prime := by
    intro request side
    have hp := hprime request.1.1 request.1.2
    cases side with
    | source =>
        simpa only [tangentEndpointLabel] using hp.1
    | target =>
        simpa only [tangentEndpointLabel] using hp.2
  have hrequestUpper : ∀ request : TangentSplitRequest edges L sigma flow,
      ∀ side : TangentEndpointSide,
        tangentEndpointLabel
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) side request ≤ labelUpper := by
    intro request side
    cases side with
    | source =>
        simpa only [tangentEndpointLabel, tangentSplitRequestSource,
          tangentSplitRequestEdge, source, tangentStarEdgeSource] using
            hlabelUpper request.1.1.1
    | target =>
        simpa only [tangentEndpointLabel, tangentSplitRequestTarget,
          tangentSplitRequestEdge, target, tangentStarEdgeTarget] using
            hlabelUpper request.1.1.2
  have hpairArithmetic : ∀ leftRequest rightRequest,
      ∀ _hne : leftRequest ≠ rightRequest,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          leftRequest rightRequest : ℝ) /
          (lowerCard leftRequest * lowerCard rightRequest) ≤
        tangentDensityDisjointCoefficient density / n +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestSource source leftRequest) rightRequest
            then tangentDensitySharedCoefficient density *
                tangentSplitRequestSource source leftRequest / n
            else 0) +
          (if tangentRequestHasLabel
              (tangentSplitRequestSource source)
              (tangentSplitRequestTarget target)
              (tangentSplitRequestTarget target leftRequest) rightRequest
            then tangentDensitySharedCoefficient density *
                tangentSplitRequestTarget target leftRequest / n
            else 0) := by
    intro leftRequest rightRequest _hne
    exact tangentOrderedPairEndpointBudget_div_le_densityCoefficients
      n K h labelUpper (tangentSplitRequestSource source)
        (tangentSplitRequestTarget target) lowerCard density hn hdensity
        hlowerPos hrequestDistinct hrequestPrime hrequestUpper
        hlabelUpperLe hlabelUpperSq hlowerScale leftRequest rightRequest
  have htraffic : (∑ edge ∈ edges, flow edge) ≤
      tangentStarResidualL1 residual := by
    exact sum_tangentStarPositiveEdges_le_residualL1 pivot residual
  have hincident : ∀ q,
      tangentIncidentFlowMass edges source target flow q ≤
        incidentTraffic q := by
    intro q
    simpa only [tangentStarLabelIncidentTraffic, edges, source, target,
      flow] using hincidentTraffic q
  have hsupport : edges.card ≤ tangentStarSupportCount V :=
    card_tangentStarPositiveEdges_le_supportCount pivot residual
  have hbudget : ∀ request : TangentSplitRequest edges L sigma flow,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          (tangentStarResidualL1 residual)
          incidentTraffic
          (tangentStarSupportCount V)
          (tangentDensityDisjointCoefficient density)
          (tangentDensitySharedCoefficient density) request ≤ 1 / 8 := by
    intro request
    exact tangentSplitNormalizedCollisionCensusBudget_le_eighth_of_density
      n edges source target L sigma (tangentStarResidualL1 residual)
        incidentTraffic (tangentStarSupportCount V)
        density hdensity request (hsmall request)
  constructor
  · exact tangentStarFlow_divergence_eq hsum
  · constructor
    · exact tangentStarSplitRequest_factorizationBoundary_eq_residual
        hsum label L sigma
    · exact R.tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget
        certificate fixedExceptional K h Phead X0 edges source target flow
          hsourceTarget lowerCard hlowerPos hlower hprime
          (tangentStarResidualL1 residual)
          incidentTraffic (tangentStarSupportCount V)
          (tangentDensityDisjointCoefficient density)
          (tangentDensitySharedCoefficient density)
          (tangentDensityDisjointCoefficient_nonneg hdensity.le)
          (tangentDensitySharedCoefficient_nonneg hdensity.le)
          hpairArithmetic hflow hL hsigma htraffic hincident hsupport hbudget

end BankPaperRealization

end

end Erdos390.WholePaper
