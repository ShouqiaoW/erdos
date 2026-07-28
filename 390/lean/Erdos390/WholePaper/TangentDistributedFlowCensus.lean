import Erdos390.WholePaper.TangentStarSplitRequestBridge

/-!
# Distributed finite-band flow census

This file isolates the quantitative interface needed between a genuine
finite-band earthmover and the already formalized split-request collision
terminal.  Unlike the one-pivot star, a distributed earthmover records a
separate port load at every vertex.  Its two analytic ledgers are

* `traffic <= (1/2) * ||residual||_1 + 2 * cutTraffic`;
* `incident(label v) <= |residual v| + 2 * portLoad v`.

These are the literal estimates produced by the cell-boundary construction
in the paper.  They are strictly stronger than the final collision target
and do not mention a density or the constant `1 / 24`.

The module proves all consequences after those construction ledgers:

* positive support has at most `|V|^2` edges;
* the total split-request count and every endpoint-label request load have
  explicit upper bounds;
* fixed main/error/ceiling parameter budgets imply the exact existing guard
  `4*T + I_source + I_target <= density^2/24` for every request;
* hence the already proved `1/8` collision-census conclusion follows.

Existence of the cell earthmover is deliberately not postulated here.  It
must be constructed from band balance, prefix-load bounds, cell cardinality,
and adjacent-cell ratio geometry.  The downstream theorems keep every
construction estimate as a visible
hypothesis, so the unfinished construction cannot be confused with a
selector theorem or with the final collision target.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Residual, cut, and port ledgers -/

/-- Traffic ledger furnished by the finite-band path construction. -/
def tangentDistributedTotalTrafficLedger
    {V : Type*} [Fintype V]
    (residual : V -> Real) (cutTraffic : Real) : Real :=
  (∑ v : V, |residual v|) / 2 + 2 * cutTraffic

/-- Per-label ledger obtained from pointwise residual mass and the two
adjacent boundary ports.  Injective labels make at most one summand nonzero.
-/
def tangentDistributedLabelIncidentLedger
    {V : Type*} [Fintype V]
    (label : V -> Nat) (residual portLoad : V -> Real) (q : Nat) : Real :=
  ∑ v : V, if label v = q then |residual v| + 2 * portLoad v else 0

/-- Quadratic support is already sufficient at the paper cutoff
`y = n^(2/9)`: the endpoint-weighted ceiling loss is then `O(y^3/n)`. -/
def tangentDistributedSupportCount (V : Type*) [Fintype V] : Nat :=
  Fintype.card V ^ 2

/-- The exact request-collision upper bound after replacing total traffic by
the residual/cut ledger and every weighted incident traffic by the uniform
residual/port ledger. -/
def tangentDistributedResidualCollisionUpper
    {V : Type*} [Fintype V]
    (n labelUpper : Nat) (L sigma : Real)
    (residual : V -> Real) (cutTraffic : Real)
    (weightedResidual weightedPort : Real) : Real :=
  4 *
      (tangentSplitCensusTotalRequestUpper L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedSupportCount V) /
        n) +
    2 *
      (((4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
          (labelUpper : Real) * tangentDistributedSupportCount V) /
        n)

/-! ## Literal ratio-cell cuts and uniform adjacent-cell ports -/

/-- Two vertices lie in the same exponent band and either the same
multiplicative cell or consecutive cells.  This is the exact combinatorial
support relation used in the paper's finite-band transport. -/
def TangentSameOrAdjacentRatioCell
    {V Band : Type*}
    (bandOf : V -> Band) (cellIndex : V -> Nat) (source target : V) : Prop :=
  bandOf source = bandOf target ∧
    (cellIndex source = cellIndex target ∨
      cellIndex source + 1 = cellIndex target ∨
      cellIndex target + 1 = cellIndex source)

/-- A flow uses only internal-cell or adjacent-cell edges. -/
def TangentFlowRespectsRatioCells
    {V Band : Type*}
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (flow : V -> V -> Real) : Prop :=
  forall {source target}, 0 < flow source target ->
    TangentSameOrAdjacentRatioCell bandOf cellIndex source target

/-- Fixed-ratio geometry for the chosen exponent bands and multiplicative
cells.  For the paper cells this is proved from `rho ^ 3 < r0`. -/
def TangentRatioCellGeometry
    {V Band : Type*}
    (label : V -> Nat) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (ratioUpper : Real) : Prop :=
  forall {source target},
    TangentSameOrAdjacentRatioCell bandOf cellIndex source target ->
      (((max (label source) (label target) : Nat) : Real) /
        ((min (label source) (label target) : Nat) : Real)) <= ratioUpper

/-- Signed prefix load `F_i` at one literal cell boundary. -/
def tangentRatioCellPrefixMass
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cut : Nat) : Real :=
  ∑ v : V,
    if bandOf v = band ∧ cellIndex v <= cut then residual v else 0

/-- The deterministic tail majorant attached to a pointwise residual
bound.  Unlike an independently supplied prefix estimate, this quantity
contains no rounding information: it is just the sum of the declared
pointwise bounds strictly to the right of the cut. -/
def tangentRatioCellTailPointwiseUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (pointwiseUpper : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat) : Real :=
  ∑ v : V,
    if bandOf v = band ∧ cut < cellIndex v then pointwiseUpper v else 0

/-- The paper cut ledger `sum_i |F_i|` over the declared nonterminal cell
boundaries. -/
def tangentRatioCellCutTraffic
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (cuts : Finset (Band × Nat)) : Real :=
  ∑ cut ∈ cuts,
    |tangentRatioCellPrefixMass residual bandOf cellIndex cut.1 cut.2|

/-- Number of vertices in one ratio cell. -/
def tangentRatioCellCard
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat) : Nat :=
  ((Finset.univ : Finset V).filter
    (fun v => bandOf v = band ∧ cellIndex v = cell)).card

/-- The signed prefix load at the left boundary of a vertex's cell. -/
def tangentRatioCellLeftPrefixMass
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  if cellIndex v = 0 then 0
  else tangentRatioCellPrefixMass residual bandOf cellIndex
    (bandOf v) (cellIndex v - 1)

/-- Uniform boundary traffic incident to one port, namely
`(|F_{i-1}|+|F_i|)/|Q_i|`. -/
def tangentRatioCellUniformPortLoad
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  (|tangentRatioCellLeftPrefixMass residual bandOf cellIndex v| +
      |tangentRatioCellPrefixMass residual bandOf cellIndex
        (bandOf v) (cellIndex v)|) /
    tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v)

/-- The two-sided uniform-port majorant obtained only from tail sums of a
pointwise residual bound.  At cell zero there is no left boundary. -/
def tangentRatioCellPointwisePortUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (pointwiseUpper : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (v : V) : Real :=
  ((if cellIndex v = 0 then 0
      else tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex
        (bandOf v) (cellIndex v - 1)) +
      tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex
        (bandOf v) (cellIndex v)) /
    tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v)

/-- Boundary-flow divergence at one uniformly distributed cell port.  The
right signed load is `F_i` and the left signed load is `F_{i-1}`. -/
def tangentRatioCellBoundaryDivergence
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  (tangentRatioCellPrefixMass residual bandOf cellIndex
        (bandOf v) (cellIndex v) -
      tangentRatioCellLeftPrefixMass residual bandOf cellIndex v) /
    tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v)

/-- Residual left for the within-cell matching after the two adjacent
boundary transports have been installed. -/
def tangentRatioCellInternalResidual
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) : Real :=
  residual v -
    tangentRatioCellBoundaryDivergence residual bandOf cellIndex v

/-- A positive edge of a cell-respecting flow joins equal or adjacent ratio
cells. -/
theorem tangentPositiveEdge_sameOrAdjacentRatioCell
    {V Band : Type*} [Fintype V] [DecidableEq V]
    {bandOf : V -> Band} {cellIndex : V -> Nat} {flow : V -> V -> Real}
    (hrespect : TangentFlowRespectsRatioCells bandOf cellIndex flow)
    {edge : V × V} (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    TangentSameOrAdjacentRatioCell bandOf cellIndex edge.1 edge.2 := by
  exact hrespect (mem_tangentPositiveFlowEdges.mp hedge)

/-- Ratio-cell geometry converts positive-edge adjacency into the required
endpoint-ratio bound. -/
theorem tangentPositiveEdge_locality_of_ratioCells
    {V Band : Type*} [Fintype V] [DecidableEq V]
    (label : V -> Nat) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (flow : V -> V -> Real) (ratioUpper : Real)
    (hrespect : TangentFlowRespectsRatioCells bandOf cellIndex flow)
    (hgeometry : TangentRatioCellGeometry
      label bandOf cellIndex ratioUpper)
    {edge : V × V} (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    (((max (tangentStarEdgeSource label edge)
          (tangentStarEdgeTarget label edge) : Nat) : Real) /
        ((min (tangentStarEdgeSource label edge)
          (tangentStarEdgeTarget label edge) : Nat) : Real)) <= ratioUpper := by
  exact hgeometry
    (tangentPositiveEdge_sameOrAdjacentRatioCell hrespect hedge)

/-- The sum of absolute prefix masses across declared cuts is nonnegative. -/
theorem tangentRatioCellCutTraffic_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (cuts : Finset (Band × Nat)) :
    0 <= tangentRatioCellCutTraffic residual bandOf cellIndex cuts := by
  unfold tangentRatioCellCutTraffic
  positivity

/-- Every uniformly distributed ratio-cell port load is nonnegative. -/
theorem tangentRatioCellUniformPortLoad_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) :
    0 <= tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  unfold tangentRatioCellUniformPortLoad
  positivity

/-- A band is the disjoint union of the prefix through `cut` and the
strict tail after `cut`. -/
theorem tangentRatioCellPrefixMass_add_tail_eq_bandSum
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cut : Nat) :
    tangentRatioCellPrefixMass residual bandOf cellIndex band cut +
        (∑ v : V,
          if bandOf v = band ∧ cut < cellIndex v then residual v else 0) =
      ∑ v : V, if bandOf v = band then residual v else 0 := by
  unfold tangentRatioCellPrefixMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hband : bandOf v = band
  · by_cases hcell : cellIndex v <= cut
    · have hnotTail : ¬cut < cellIndex v := Nat.not_lt_of_ge hcell
      simp [hband, hcell, hnotTail]
    · have htail : cut < cellIndex v := Nat.lt_of_not_ge hcell
      simp [hband, hcell, htail]
  · simp [hband]

/-- Exact band balance turns every prefix into the negative strict tail;
the pointwise residual estimate therefore supplies the paper's prefix
majorant without an additional selector-rounding assumption. -/
theorem abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (hpointwise : forall v, |residual v| <= pointwiseUpper v)
    (band : Band) (cut : Nat) :
    |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
      tangentRatioCellTailPointwiseUpper
        pointwiseUpper bandOf cellIndex band cut := by
  have hsplit := tangentRatioCellPrefixMass_add_tail_eq_bandSum
    residual bandOf cellIndex band cut
  have hprefix :
      tangentRatioCellPrefixMass residual bandOf cellIndex band cut =
        -(∑ v : V,
          if bandOf v = band ∧ cut < cellIndex v then residual v else 0) := by
    rw [hbalance band] at hsplit
    linarith
  rw [hprefix, abs_neg]
  calc
    |(∑ v : V,
        if bandOf v = band ∧ cut < cellIndex v then residual v else 0)| <=
        ∑ v : V,
          |if bandOf v = band ∧ cut < cellIndex v then residual v else 0| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ v : V,
        if bandOf v = band ∧ cut < cellIndex v then |residual v| else 0 := by
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases htail : bandOf v = band ∧ cut < cellIndex v <;>
        simp [htail]
    _ <= tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex band cut := by
      unfold tangentRatioCellTailPointwiseUpper
      apply Finset.sum_le_sum
      intro v _hv
      by_cases htail : bandOf v = band ∧ cut < cellIndex v
      · simpa only [if_pos htail] using hpointwise v
      · simp [htail]

/-- Consequently the literal two-port load is bounded by the explicit
pointwise tail majorant.  The cell denominator is never replaced by an
analytic lower bound here. -/
theorem tangentRatioCellUniformPortLoad_le_pointwisePortUpper
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual pointwiseUpper : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (hpointwise : forall v, |residual v| <= pointwiseUpper v)
    (v : V) :
    tangentRatioCellUniformPortLoad residual bandOf cellIndex v <=
      tangentRatioCellPointwisePortUpper
        pointwiseUpper bandOf cellIndex v := by
  unfold tangentRatioCellUniformPortLoad
    tangentRatioCellPointwisePortUpper tangentRatioCellLeftPrefixMass
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  by_cases hcell : cellIndex v = 0
  · simp only [hcell, if_true, abs_zero, zero_add]
    exact abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
      residual pointwiseUpper bandOf cellIndex hbalance hpointwise
        (bandOf v) 0
  · simp only [hcell, if_false]
    exact add_le_add
      (abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
        residual pointwiseUpper bandOf cellIndex hbalance hpointwise
          (bandOf v) (cellIndex v - 1))
      (abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
        residual pointwiseUpper bandOf cellIndex hbalance hpointwise
          (bandOf v) (cellIndex v))

/-- Uniform distribution makes the absolute boundary divergence at a port
no larger than its two-sided incident boundary traffic. -/
theorem abs_tangentRatioCellBoundaryDivergence_le_portLoad
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) :
    |tangentRatioCellBoundaryDivergence residual bandOf cellIndex v| <=
      tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  unfold tangentRatioCellBoundaryDivergence
    tangentRatioCellUniformPortLoad
  rw [abs_div]
  have hcardNonneg :
      0 ≤ (tangentRatioCellCard bandOf cellIndex
        (bandOf v) (cellIndex v) : Real) := Nat.cast_nonneg _
  rw [abs_of_nonneg hcardNonneg]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simpa only [add_comm] using
    abs_sub
      (tangentRatioCellPrefixMass residual bandOf cellIndex
        (bandOf v) (cellIndex v))
      (tangentRatioCellLeftPrefixMass residual bandOf cellIndex v)

/-- Once an internal matching realizes the adjusted residual with incident
mass `|q_p|`, adding the two boundary ports gives exactly the paper's
pointwise ledger `|q_p| + b_p <= |r_p| + 2 b_p`. -/
theorem abs_internalResidual_add_portLoad_le
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (v : V) :
    |tangentRatioCellInternalResidual residual bandOf cellIndex v| +
        tangentRatioCellUniformPortLoad residual bandOf cellIndex v <=
      |residual v| +
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  have hboundary :=
    abs_tangentRatioCellBoundaryDivergence_le_portLoad
      residual bandOf cellIndex v
  have hinternal :
      |tangentRatioCellInternalResidual residual bandOf cellIndex v| <=
        |residual v| +
          |tangentRatioCellBoundaryDivergence
            residual bandOf cellIndex v| := by
    simpa only [tangentRatioCellInternalResidual] using
      abs_sub (residual v)
        (tangentRatioCellBoundaryDivergence
          residual bandOf cellIndex v)
  linarith

/-! ## Visible hypotheses for a distributed construction -/

/- The construction estimates are deliberately *not* bundled into a
structure.  The repository audit discipline forbids hiding a claimed
traffic or incident estimate in a conclusion-bearing certificate.  Every
generic theorem below therefore displays the exact flow property that it
uses. -/

/-! ## Support, locality, and literal traffic consequences -/

/-- The positive support of a finite directed flow has at most the quadratic
distributed-support census. -/
theorem card_tangentPositiveFlowEdges_le_distributedSupportCount
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) :
    (tangentPositiveFlowEdges flow).card <=
      tangentDistributedSupportCount V := by
  unfold tangentPositiveFlowEdges tangentDistributedSupportCount
  calc
    ((Finset.univ : Finset (V × V)).filter
        (fun edge => 0 < flow edge.1 edge.2)).card <=
        (Finset.univ : Finset (V × V)).card :=
      Finset.card_filter_le _ _
    _ = Fintype.card V ^ 2 := by
      simp [pow_two]

/-- Injective vertex labels distinguish the endpoints of every positive
non-loop edge. -/
theorem tangentDistributedPositiveEdge_labels_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) {label : V -> Nat}
    (hpositiveEndpoints : forall {source target},
      0 < flow source target -> source ≠ target)
    (hlabel : Function.Injective label) {edge : V × V}
    (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    tangentStarEdgeSource label edge ≠ tangentStarEdgeTarget label edge := by
  intro heq
  have hvertices : edge.1 = edge.2 := by
    apply hlabel
    simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using heq
  exact hpositiveEndpoints
    (mem_tangentPositiveFlowEdges.mp hedge) hvertices

/-- A pointwise locality hypothesis transfers to every edge in the positive
support. -/
theorem tangentDistributedPositiveEdge_locality
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) {label : V -> Nat} {ratioUpper : Real}
    (hlocality : forall {source target},
      0 < flow source target ->
        (((max (label source) (label target) : Nat) : Real) /
          ((min (label source) (label target) : Nat) : Real)) <= ratioUpper)
    {edge : V × V} (hedge : edge ∈ tangentPositiveFlowEdges flow) :
    (((max (tangentStarEdgeSource label edge)
          (tangentStarEdgeTarget label edge) : Nat) : Real) /
        ((min (tangentStarEdgeSource label edge)
          (tangentStarEdgeTarget label edge) : Nat) : Real)) <= ratioUpper := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    hlocality (mem_tangentPositiveFlowEdges.mp hedge)

/-- The total mass on the positive support is bounded by the declared traffic
ledger. -/
theorem sum_tangentDistributedPositiveEdges_le_trafficLedger
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real) (cutTraffic : Real)
    (hflow : forall source target, 0 <= flow source target)
    (htraffic : tangentFlowTraffic flow <=
      tangentDistributedTotalTrafficLedger residual cutTraffic) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2) <=
      tangentDistributedTotalTrafficLedger residual cutTraffic := by
  rw [sum_tangentPositiveFlowEdges_eq_traffic flow hflow]
  exact htraffic

/-! ## Boundary preservation for an arbitrary distributed flow -/

/-- Restricting a nonnegative flow to its strictly positive support does not
change any weighted edge sum. -/
theorem sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (value : V × V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * value edge) =
      ∑ edge : V × V, flow edge.1 edge.2 * value edge := by
  classical
  apply Finset.sum_subset
    (Finset.subset_univ (tangentPositiveFlowEdges flow))
  intro edge _hedge hedge
  have hnotPos : ¬0 < flow edge.1 edge.2 := by
    simpa only [mem_tangentPositiveFlowEdges] using hedge
  have hzero : flow edge.1 edge.2 = 0 :=
    le_antisymm (le_of_not_gt hnotPos) (hflow edge.1 edge.2)
  simp only [hzero, zero_mul]

/-- The positive support of a distributed earthmover has exactly the
prescribed residual boundary against every vertex test function. -/
theorem tangentDistributedPositiveEdges_boundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (value : V -> Real) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ v : V, residual v * value v := by
  calc
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 * (value edge.1 - value edge.2)) =
      ∑ edge : V × V,
        flow edge.1 edge.2 * (value edge.1 - value edge.2) :=
      sum_tangentPositiveFlowEdges_mul_eq_full_of_nonneg
        flow hflow
          (fun edge => value edge.1 - value edge.2)
    _ = ∑ source : V, ∑ target : V,
        flow source target * (value source - value target) := by
      rw [Fintype.sum_prod_type]
    _ = ∑ v : V,
        tangentFlowDivergence flow v * value v :=
      tangentFlow_weightedBoundary_eq_divergence flow value
    _ = ∑ v : V, residual v * value v := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [hdivergence v]

/-- Factorization-coordinate form of the distributed boundary. -/
theorem tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat) (residual : V -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall v,
      tangentFlowDivergence flow v = residual v)
    (p : Nat) :
    (∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real))) =
      ∑ v : V, residual v * (label v).factorization p := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    tangentDistributedPositiveEdges_boundary_eq_residual
      flow residual hflow hdivergence
      (fun v => ((label v).factorization p : Real))

/-- Equal request splitting preserves the distributed residual boundary. -/
theorem tangentDistributedSplitRequest_factorizationBoundary_eq_residual
    {V : Type*} [Fintype V] [DecidableEq V]
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
      ∑ v : V, residual v * (label v).factorization p := by
  calc
    (∑ request : TangentSplitRequest
          (tangentPositiveFlowEdges flow) L sigma
            (fun edge : V × V => flow edge.1 edge.2),
        tangentSplitRequestWeight request *
          (((tangentSplitRequestSource (tangentStarEdgeSource label)
                request).factorization p : Real) -
            ((tangentSplitRequestTarget (tangentStarEdgeTarget label)
                request).factorization p : Real))) =
      ∑ edge ∈ tangentPositiveFlowEdges flow,
        flow edge.1 edge.2 *
          (((tangentStarEdgeSource label edge).factorization p : Real) -
            ((tangentStarEdgeTarget label edge).factorization p : Real)) := by
      simpa only using
        sum_tangentSplitRequestWeight_mul_sub
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          L sigma (fun edge : V × V => flow edge.1 edge.2)
          (fun q => (q.factorization p : Real))
    _ = ∑ v : V, residual v * (label v).factorization p :=
      tangentDistributedPositiveEdges_factorizationBoundary_eq_residual
        flow label residual hflow hdivergence p

/-! ## Weighted per-label port control -/

/-- With injective labels, the incident ledger at `label v` has exactly the
single contribution from `v`. -/
theorem tangentDistributedLabelIncidentLedger_at_label
    {V : Type*} [Fintype V]
    {label : V -> Nat} {residual portLoad : V -> Real}
    (hlabel : Function.Injective label) (v : V) :
    tangentDistributedLabelIncidentLedger label residual portLoad
        (label v) =
      |residual v| + 2 * portLoad v := by
  classical
  unfold tangentDistributedLabelIncidentLedger
  rw [Finset.sum_eq_single v]
  · simp
  · intro w _hw hwv
    have hwLabel : label w ≠ label v := by
      intro hwLabel
      exact hwv (hlabel hwLabel)
    simp [hwLabel]
  · simp

/-- Pointwise weighted residual and port bounds control the weighted label
ledger. -/
theorem tangentDistributedLabelIncidentLedger_mul_le
    {V : Type*} [Fintype V]
    {label : V -> Nat} {residual portLoad : V -> Real}
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    (v : V) :
    (label v : Real) *
        tangentDistributedLabelIncidentLedger label residual portLoad
          (label v) <=
      weightedResidual + 2 * weightedPort := by
  rw [tangentDistributedLabelIncidentLedger_at_label hlabel v]
  calc
    (label v : Real) * (|residual v| + 2 * portLoad v) =
        (label v : Real) * |residual v| +
          2 * ((label v : Real) * portLoad v) := by ring
    _ <= weightedResidual + 2 * weightedPort := by
      exact add_le_add (hresidual v)
        (mul_le_mul_of_nonneg_left (hport v) (by norm_num))

/-- The pointwise incident-flow estimate implies a uniform weighted incident
bound. -/
theorem tangentDistributedWeightedIncident_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real)
    (hincident : forall v,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => flow edge.1 edge.2) (label v) <=
        |residual v| + 2 * portLoad v)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    (v : V) :
    (label v : Real) *
        tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => flow edge.1 edge.2) (label v) <=
      weightedResidual + 2 * weightedPort := by
  calc
    (label v : Real) *
        tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => flow edge.1 edge.2) (label v) <=
        (label v : Real) * (|residual v| + 2 * portLoad v) :=
      mul_le_mul_of_nonneg_left (hincident v) (Nat.cast_nonneg _)
    _ <= weightedResidual + 2 * weightedPort := by
      calc
        (label v : Real) * (|residual v| + 2 * portLoad v) =
            (label v : Real) * |residual v| +
              2 * ((label v : Real) * portLoad v) := by ring
        _ <= weightedResidual + 2 * weightedPort :=
          add_le_add (hresidual v)
            (mul_le_mul_of_nonneg_left (hport v) (by norm_num))

/-- Injective labels promote the vertexwise incident estimate to every natural
label. -/
theorem tangentDistributedIncidentTraffic_le_ledger
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real)
    (hincident : forall v,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (fun edge : V × V => flow edge.1 edge.2) (label v) <=
        |residual v| + 2 * portLoad v)
    (hlabel : Function.Injective label) (q : Nat) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => flow edge.1 edge.2) q <=
      tangentDistributedLabelIncidentLedger label residual portLoad q := by
  classical
  by_cases hq : ∃ v : V, label v = q
  · obtain ⟨v, rfl⟩ := hq
    rw [tangentDistributedLabelIncidentLedger_at_label hlabel v]
    exact hincident v
  · have hnone : forall v : V, label v ≠ q := by
      intro v hv
      exact hq ⟨v, hv⟩
    have hzero :
        tangentIncidentFlowMass
            (tangentPositiveFlowEdges flow)
            (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
            (fun edge : V × V => flow edge.1 edge.2) q = 0 := by
      unfold tangentIncidentFlowMass tangentIncidentEdges
      apply Finset.sum_eq_zero
      intro edge hedge
      have hdata := Finset.mem_filter.mp hedge
      rcases hdata.2 with hsource | htarget
      · exact (hnone edge.1 hsource).elim
      · exact (hnone edge.2 htarget).elim
    rw [hzero]
    simp [tangentDistributedLabelIncidentLedger, hnone]

/-! ## Total and endpoint request counts -/

/-- The traffic and support ledgers bound the total number of distributed
split requests. -/
theorem tangentDistributedTotalRequestCount_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (residual : V -> Real) (cutTraffic : Real)
    (hflow : forall source target, 0 <= flow source target)
    (htraffic : tangentFlowTraffic flow <=
      tangentDistributedTotalTrafficLedger residual cutTraffic)
    {L sigma : Real} (hL : 0 < L) (hsigma : 0 < sigma) :
    (tangentTotalRequestCount
      (TangentSplitRequest (tangentPositiveFlowEdges flow) L sigma
        (fun edge : V × V => flow edge.1 edge.2)) : Real) <=
      tangentSplitCensusTotalRequestUpper L sigma
        (tangentDistributedTotalTrafficLedger residual cutTraffic)
        (tangentDistributedSupportCount V) := by
  apply cast_tangentSplitTotalRequestCount_le_census
  · intro edge _hedge
    exact hflow edge.1 edge.2
  · exact hL
  · exact hsigma
  · exact sum_tangentDistributedPositiveEdges_le_trafficLedger
      flow residual cutTraffic hflow htraffic
  · exact card_tangentPositiveFlowEdges_le_distributedSupportCount flow

/-- The incident and support ledgers bound the split-request load at every
label. -/
theorem tangentDistributedLabelRequestLoad_le
    {V : Type*} [Fintype V] [DecidableEq V]
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
    {L sigma : Real} (hL : 0 < L) (hsigma : 0 < sigma) (q : Nat) :
    (tangentRequestLabelLoad
      (tangentSplitRequestSource
        (edges := tangentPositiveFlowEdges flow) (L := L)
        (sigma := sigma) (flow := fun edge : V × V => flow edge.1 edge.2)
        (tangentStarEdgeSource label))
      (tangentSplitRequestTarget
        (edges := tangentPositiveFlowEdges flow) (L := L)
        (sigma := sigma) (flow := fun edge : V × V => flow edge.1 edge.2)
        (tangentStarEdgeTarget label)) q : Real) <=
      tangentSplitCensusLabelRequestUpper L sigma
        (tangentDistributedLabelIncidentLedger label residual portLoad)
        (tangentDistributedSupportCount V) q := by
  apply cast_tangentSplitRequestLabelLoad_le_census
  · intro edge _hedge
    exact hflow edge.1 edge.2
  · exact hL
  · exact hsigma
  · exact tangentDistributedIncidentTraffic_le_ledger
      flow label residual portLoad hincident hlabel
  · exact card_tangentPositiveFlowEdges_le_distributedSupportCount flow

/-- Weighted pointwise residual and port estimates bound the normalized label
census ledger. -/
theorem tangentDistributedWeightedLabelCensusUpper_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (label : V -> Nat) (residual portLoad : V -> Real)
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    {labelUpper : Nat} (hlabelUpper : forall v, label v <= labelUpper)
    {L sigma : Real} (hL : 0 < L) (hsigma : 0 < sigma)
    (v : V) :
    (label v : Real) *
        tangentSplitCensusLabelRequestUpper L sigma
          (tangentDistributedLabelIncidentLedger label residual portLoad)
          (tangentDistributedSupportCount V) (label v) <=
      (4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
        (labelUpper : Real) * tangentDistributedSupportCount V := by
  have hweighted := tangentDistributedLabelIncidentLedger_mul_le
    hlabel hresidual hport v
  have hA : 0 <= 4 * L / sigma := by positivity
  calc
    (label v : Real) *
        tangentSplitCensusLabelRequestUpper L sigma
          (tangentDistributedLabelIncidentLedger label residual portLoad)
          (tangentDistributedSupportCount V) (label v) =
      (4 * L / sigma) *
          ((label v : Real) *
            tangentDistributedLabelIncidentLedger label residual portLoad
              (label v)) +
        (label v : Real) * tangentDistributedSupportCount V := by
      unfold tangentSplitCensusLabelRequestUpper
      ring
    _ <= (4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
        (labelUpper : Real) * tangentDistributedSupportCount V := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hweighted hA)
        (mul_le_mul_of_nonneg_right
          (by exact_mod_cast hlabelUpper v)
          (Nat.cast_nonneg _))

/-- The actual number of split requests incident to one endpoint label,
after weighting by that label.  This combines the ceiling census with the
pointwise residual and uniform-port estimates. -/
theorem tangentDistributedWeightedLabelRequestLoad_le
    {V : Type*} [Fintype V] [DecidableEq V]
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
    {L sigma : Real} (hL : 0 < L) (hsigma : 0 < sigma)
    (v : V) :
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
        (labelUpper : Real) * tangentDistributedSupportCount V := by
  calc
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
      (label v : Real) *
        tangentSplitCensusLabelRequestUpper L sigma
          (tangentDistributedLabelIncidentLedger label residual portLoad)
          (tangentDistributedSupportCount V) (label v) :=
      mul_le_mul_of_nonneg_left
        (tangentDistributedLabelRequestLoad_le
          flow label residual portLoad hflow hincident hlabel
          hL hsigma (label v))
        (Nat.cast_nonneg _)
    _ <= (4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
        (labelUpper : Real) * tangentDistributedSupportCount V :=
      tangentDistributedWeightedLabelCensusUpper_le
        label residual portLoad hlabel hresidual hport hlabelUpper
        hL hsigma v

/-! ## Paper-parameter closure of the collision guard

The three budgets below mirror the actual parameter order in Section 9.
The main term is made small by the fixed band width `w`; the error and
ceiling terms are absorbed only after the mesh is fixed and `n` tends to
infinity.  None of them is a traffic or request-count hypothesis. -/

/-- Paper-scale main contribution to the distributed collision budget. -/
def tangentDistributedPaperMainBudget
    (trafficConstant incidentConstant tangentConstant width sigma : Real) :
    Real :=
  ((16 * trafficConstant + 8 * incidentConstant) *
      tangentConstant * width) / sigma

/-- Paper-scale analytic-error contribution to the distributed collision
budget. -/
def tangentDistributedPaperErrorBudget
    (trafficError incidentError sigma : Real) : Real :=
  (16 * trafficError + 8 * incidentError) / sigma

/-- Paper-scale finite-support ceiling contribution to the distributed
collision budget. -/
def tangentDistributedPaperCeilingBudget
    (n labelUpper supportCount : Nat) : Real :=
  (4 + 2 * (labelUpper : Real)) * supportCount / n

/-- Literal cancellation of `L * N = n` in the total- and incident-ledger
bounds.  This is the arithmetic step which prevents the final
`4*T+I_s+I_t` target from reappearing as an assembly premise. -/
theorem tangentDistributedResidualCollisionUpper_le_paperBudgets
    {V : Type*} [Fintype V]
    (residual : V -> Real) (cutTraffic weightedResidual weightedPort : Real)
    {n labelUpper : Nat} {L sigma N : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
    (htotal : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hincident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N) :
    tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort <=
      tangentDistributedPaperMainBudget trafficConstant incidentConstant
          tangentConstant width sigma +
        tangentDistributedPaperErrorBudget trafficError incidentError sigma +
        tangentDistributedPaperCeilingBudget n labelUpper
          (tangentDistributedSupportCount V) := by
  unfold tangentDistributedResidualCollisionUpper
  unfold tangentSplitCensusTotalRequestUpper
    tangentDistributedPaperMainBudget
    tangentDistributedPaperErrorBudget
    tangentDistributedPaperCeilingBudget
  calc
    4 *
          (((4 * L / sigma) *
                tangentDistributedTotalTrafficLedger residual cutTraffic +
              tangentDistributedSupportCount V) /
            (n : Real)) +
        2 *
          (((4 * L / sigma) * (weightedResidual + 2 * weightedPort) +
              (labelUpper : Real) * tangentDistributedSupportCount V) /
            (n : Real)) <=
      4 *
          (((4 * L / sigma) *
                (trafficConstant * tangentConstant * N * width +
                  trafficError * N) +
              tangentDistributedSupportCount V) /
            (n : Real)) +
        2 *
          (((4 * L / sigma) *
                (incidentConstant * tangentConstant * N * width +
                  incidentError * N) +
              (labelUpper : Real) * tangentDistributedSupportCount V) /
            (n : Real)) := by
      gcongr
    _ =
      ((16 * trafficConstant + 8 * incidentConstant) *
            tangentConstant * width) /
          sigma +
        (16 * trafficError + 8 * incidentError) / sigma +
        (4 + 2 * (labelUpper : Real)) *
            tangentDistributedSupportCount V /
          n := by
      rw [← hscale]
      field_simp [ne_of_gt hL, ne_of_gt hN, ne_of_gt hsigma]; ring

/-- Separate main, error, and ceiling smallness bounds imply the final
distributed residual-collision bound. -/
theorem tangentDistributedResidualCollisionUpper_le_of_paperSmallness
    {V : Type*} [Fintype V]
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
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n labelUpper
        (tangentDistributedSupportCount V) <= density ^ 2 / 96) :
    tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort <=
      density ^ 2 / 24 := by
  calc
    tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort <=
      tangentDistributedPaperMainBudget trafficConstant incidentConstant
          tangentConstant width sigma +
        tangentDistributedPaperErrorBudget trafficError incidentError sigma +
        tangentDistributedPaperCeilingBudget n labelUpper
          (tangentDistributedSupportCount V) :=
      tangentDistributedResidualCollisionUpper_le_paperBudgets
        residual cutTraffic weightedResidual weightedPort hL hsigma hN hscale
        htotal hincident
    _ <= density ^ 2 / 24 := by linarith

/-- The paper-scale budgets imply the exact per-request census inequality
consumed by the collision theorem. -/
theorem tangentDistributedRequest_census_small_of_paperBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real) (cutTraffic : Real)
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    {n labelUpper : Nat} (hlabelUpper : forall v, label v <= labelUpper)
    {L sigma N density : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hscale : L * N = (n : Real))
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
    (request : TangentSplitRequest
      (tangentPositiveFlowEdges flow) L sigma
        (fun edge : V × V => flow edge.1 edge.2)) :
    4 * (tangentSplitCensusTotalRequestUpper L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedSupportCount V) / n) +
        (((tangentSplitRequestSource (P := Nat)
              (tangentStarEdgeSource label) request : Nat) : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V)
            (tangentSplitRequestSource (tangentStarEdgeSource label)
              request) / n) +
        (((tangentSplitRequestTarget (P := Nat)
              (tangentStarEdgeTarget label) request : Nat) : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V)
            (tangentSplitRequestTarget (tangentStarEdgeTarget label)
              request) / n) <= density ^ 2 / 24 := by
  let sourceVertex : V := request.1.1.1
  let targetVertex : V := request.1.1.2
  have hsourceLabel :
      tangentSplitRequestSource (tangentStarEdgeSource label) request =
        label sourceVertex := by rfl
  have htargetLabel :
      tangentSplitRequestTarget (tangentStarEdgeTarget label) request =
        label targetVertex := by rfl
  have hsource := tangentDistributedWeightedLabelCensusUpper_le
    label residual portLoad hlabel hresidual hport hlabelUpper
      hL hsigma sourceVertex
  have htarget := tangentDistributedWeightedLabelCensusUpper_le
    label residual portLoad hlabel hresidual hport hlabelUpper
      hL hsigma targetVertex
  rw [hsourceLabel, htargetLabel]
  have hn : 0 <= (n : Real) := Nat.cast_nonneg n
  have hsourceDiv := div_le_div_of_nonneg_right hsource hn
  have htargetDiv := div_le_div_of_nonneg_right htarget hn
  calc
    4 * (tangentSplitCensusTotalRequestUpper L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedSupportCount V) / n) +
        ((label sourceVertex : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V) (label sourceVertex) / n) +
        ((label targetVertex : Real) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentDistributedLabelIncidentLedger label residual portLoad)
            (tangentDistributedSupportCount V) (label targetVertex) / n) <=
      tangentDistributedResidualCollisionUpper n labelUpper L sigma
        residual cutTraffic weightedResidual weightedPort := by
      unfold tangentDistributedResidualCollisionUpper
      linarith
    _ <= density ^ 2 / 24 :=
      tangentDistributedResidualCollisionUpper_le_of_paperSmallness
        residual cutTraffic weightedResidual weightedPort hL hsigma hN hscale
        htotal hweightedIncident hmain herror hceiling

/-- The paper-scale distributed bounds close the normalized collision census
at `1/8`. -/
theorem tangentDistributedCollisionCensusBudget_le_eighth_of_paperBounds
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (label : V -> Nat)
    (residual portLoad : V -> Real) (cutTraffic : Real)
    (hlabel : Function.Injective label)
    {weightedResidual weightedPort : Real}
    (hresidual : forall v,
      (label v : Real) * |residual v| <= weightedResidual)
    (hport : forall v,
      (label v : Real) * portLoad v <= weightedPort)
    {n labelUpper : Nat} (hlabelUpper : forall v, label v <= labelUpper)
    {L sigma N density : Real}
    {trafficConstant incidentConstant tangentConstant width : Real}
    {trafficError incidentError : Real}
    (hL : 0 < L) (hsigma : 0 < sigma) (hN : 0 < N)
    (hdensity : 0 < density) (hscale : L * N = (n : Real))
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
    (request : TangentSplitRequest
      (tangentPositiveFlowEdges flow) L sigma
        (fun edge : V × V => flow edge.1 edge.2)) :
    tangentSplitNormalizedCollisionCensusBudget
        (flow := fun edge : V × V => flow edge.1 edge.2)
        n (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        L sigma
        (tangentDistributedTotalTrafficLedger residual cutTraffic)
        (tangentDistributedLabelIncidentLedger label residual portLoad)
        (tangentDistributedSupportCount V)
        (tangentDensityDisjointCoefficient density)
        (tangentDensitySharedCoefficient density) request <= 1 / 8 := by
  exact tangentSplitNormalizedCollisionCensusBudget_le_eighth_of_density
    n (tangentPositiveFlowEdges flow)
      (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
      L sigma (tangentDistributedTotalTrafficLedger residual cutTraffic)
      (tangentDistributedLabelIncidentLedger label residual portLoad)
      (tangentDistributedSupportCount V) density hdensity request
      (tangentDistributedRequest_census_small_of_paperBounds
        flow label residual portLoad cutTraffic hlabel hresidual hport
        hlabelUpper hL hsigma hN hscale htotal hweightedIncident
        hmain herror hceiling request)

/-! ## Connector to the actual paper collision terminal -/

namespace BankPaperRealization

/-- Star-free connector from a distributed residual earthmover to the
actual paper split-request terminal.  Its earthmover-side quantitative
inputs are the literal residual/cut/port ledgers; the clean-list lower-card
and effective-density estimates and the paper's fixed main/error/ceiling
parameter budgets also remain explicit.  There is no request-wise or
aggregate final collision premise. -/
theorem tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus
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
          multiplier := by
  let edges := tangentPositiveFlowEdges vertexFlow
  let source := tangentStarEdgeSource label
  let target := tangentStarEdgeTarget label
  let flow : V × V -> Real :=
    fun edge => vertexFlow edge.1 edge.2
  have hsourceTarget : ∀ edge ∈ edges,
      source edge ≠ target edge := by
    intro edge hedge
    exact tangentDistributedPositiveEdge_labels_ne
      vertexFlow hpositiveEndpoints hlabelInjective hedge
  have hflow : ∀ edge ∈ edges, 0 <= flow edge := by
    intro edge _hedge
    exact hflowNonneg edge.1 edge.2
  have hprime : ∀ edge ∈ edges,
      (source edge).Prime ∧ (target edge).Prime := by
    intro edge _hedge
    exact ⟨hlabelPrime edge.1, hlabelPrime edge.2⟩
  have hrequestDistinct : forall request :
      TangentSplitRequest edges L sigma flow,
      tangentSplitRequestSource source request ≠
        tangentSplitRequestTarget target request := by
    intro request
    simpa only [tangentSplitRequestSource, tangentSplitRequestTarget,
      tangentSplitRequestEdge] using
        hsourceTarget request.1.1 request.1.2
  have hrequestPrime : forall request :
      TangentSplitRequest edges L sigma flow,
      forall side : TangentEndpointSide,
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
  have hrequestUpper : forall request :
      TangentSplitRequest edges L sigma flow,
      forall side : TangentEndpointSide,
        tangentEndpointLabel
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target) side request <= labelUpper := by
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
  have hpairArithmetic : forall leftRequest rightRequest,
      forall _hne : leftRequest ≠ rightRequest,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          (tangentSplitRequestSource source)
          (tangentSplitRequestTarget target)
          leftRequest rightRequest : Real) /
          (lowerCard leftRequest * lowerCard rightRequest) <=
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
  have htraffic : (∑ edge ∈ edges, flow edge) <=
      tangentDistributedTotalTrafficLedger residual cutTraffic := by
    exact sum_tangentDistributedPositiveEdges_le_trafficLedger
      vertexFlow residual cutTraffic hflowNonneg htrafficFull
  have hincident : forall q,
      tangentIncidentFlowMass edges source target flow q <=
        tangentDistributedLabelIncidentLedger label residual portLoad q := by
    intro q
    exact tangentDistributedIncidentTraffic_le_ledger
      vertexFlow label residual portLoad hincidentVertex hlabelInjective q
  have hsupport : edges.card <= tangentDistributedSupportCount V :=
    card_tangentPositiveFlowEdges_le_distributedSupportCount vertexFlow
  have hbudget : forall request : TangentSplitRequest edges L sigma flow,
      tangentSplitNormalizedCollisionCensusBudget
        (flow := flow) n edges source target L sigma
          (tangentDistributedTotalTrafficLedger residual cutTraffic)
          (tangentDistributedLabelIncidentLedger label residual portLoad)
          (tangentDistributedSupportCount V)
          (tangentDensityDisjointCoefficient density)
          (tangentDensitySharedCoefficient density) request <= 1 / 8 := by
    intro request
    exact tangentDistributedCollisionCensusBudget_le_eighth_of_paperBounds
      vertexFlow label residual portLoad cutTraffic hlabelInjective
      hresidual hport hlabelUpper hL hsigma hN hdensity hscale
      htotal hweightedIncident hmain herror hceiling request
  exact ⟨hdivergence,
    tangentDistributedSplitRequest_factorizationBoundary_eq_residual
      vertexFlow label residual hflowNonneg hdivergence L sigma,
    R.tangentPaperSplitEndpointsDistinct_of_normalizedCensusBudget
      certificate fixedExceptional K h Phead X0 edges source target flow
      hsourceTarget lowerCard hlowerPos hlower hprime
      (tangentDistributedTotalTrafficLedger residual cutTraffic)
      (tangentDistributedLabelIncidentLedger label residual portLoad)
      (tangentDistributedSupportCount V)
      (tangentDensityDisjointCoefficient density)
      (tangentDensitySharedCoefficient density)
      (tangentDensityDisjointCoefficient_nonneg hdensity.le)
      (tangentDensitySharedCoefficient_nonneg hdensity.le)
      hpairArithmetic hflow hL hsigma htraffic hincident hsupport hbudget⟩

end BankPaperRealization

end

end Erdos390.WholePaper
