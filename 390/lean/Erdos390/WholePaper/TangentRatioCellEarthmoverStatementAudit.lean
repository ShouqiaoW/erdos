import Erdos390.WholePaper.TangentRatioCellEarthmover

/-! # Expanded statement audit for the explicit ratio-cell earthmover -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Complete public declaration census -/

#check tangentRatioCellUniformWeight
#check tangentRatioCellCard_at_vertex_pos
#check tangentRatioCellCard_at_vertex_ne_zero
#check tangentRatioCellUniformWeight_eq_zero_of_card_eq_zero
#check tangentRatioCellUniformWeight_nonneg
#check sum_tangentRatioCellUniformWeight
#check tangentRatioCellUniformWeight_at_vertex
#check tangentRatioCellBoundaryCutFlow
#check tangentRatioCellBoundaryCutFlow_nonneg
#check tangentRatioCellBoundaryCutFlow_eq_zero_of_left_empty
#check tangentRatioCellBoundaryCutFlow_eq_zero_of_right_empty
#check tangentRatioCellBoundaryCutFlow_self
#check sum_tangentRatioCellBoundaryCutFlow_out
#check sum_tangentRatioCellBoundaryCutFlow_in
#check tangentRatioCellBoundaryCutFlow_divergence
#check tangentRatioCellBoundaryCutFlow_divergence_of_mem_left
#check tangentRatioCellBoundaryCutFlow_divergence_of_mem_right
#check tangentRatioCellBoundaryCutFlow_traffic
#check tangentRatioCellBoundaryCutFlow_incident
#check tangentFlowDivergence_finset_sum
#check tangentFlowTraffic_finset_sum
#check tangentVertexIncident_finset_sum
#check tangentRatioCellCanonicalCutTraffic
#check tangentRatioCellBoundaryFlow
#check tangentRatioCellBoundaryFlow_nonneg
#check tangentRatioCellBoundaryFlow_self
#check tangentRatioCellPrefixMass_lastCell
#check sum_tangentRatioCell_eq_prefix_sub_left
#check tangentRatioCellBoundaryFlow_divergence_cutSum
#check sum_prefix_mul_leftUniformWeight
#check sum_prefix_mul_rightUniformWeight
#check tangentRatioCellBoundaryFlow_divergence_eq
#check tangentRatioCellBoundaryFlow_traffic_eq
#check tangentRatioCellBoundaryFlow_incident_cutSum
#check sum_abs_prefix_mul_leftUniformWeight
#check sum_abs_prefix_mul_rightUniformWeight
#check tangentRatioCellBoundaryFlow_incident_eq_portLoad
#check tangentRatioCellMaskedInternalResidual
#check tangentRatioCellInternalFlow
#check tangentRatioCellInternalFlow_nonneg
#check tangentRatioCellInternalFlow_self
#check sum_tangentRatioCellBoundaryDivergence_eq_prefix_sub_left
#check sum_tangentRatioCellMaskedInternalResidual_eq_zero
#check tangentRatioCellInternalFlow_divergence_cutSum
#check sum_tangentRatioCellMaskedInternalResidual_at_vertex
#check tangentRatioCellInternalFlow_divergence_eq
#check tangentRatioCellInternalFlow_incident_cutSum
#check sum_abs_tangentRatioCellMaskedInternalResidual_at_vertex
#check tangentRatioCellInternalFlow_incident_eq_abs
#check tangentRatioCellInternalFlow_traffic_cutSum
#check sum_abs_tangentRatioCellMaskedInternalResidual_partition
#check tangentRatioCellInternalFlow_traffic_eq
#check tangentRatioCellBoundaryCutFlow_positive_cells
#check tangentRatioCellBoundaryCutFlow_respectsRatioCells
#check tangentRatioCellBoundaryFlow_respectsRatioCells
#check tangentBalancedProductFlow_masked_positive_cells
#check tangentRatioCellInternalFlow_respectsRatioCells
#check tangentRatioCellEarthmoverFlow
#check tangentFlowDivergence_add
#check tangentFlowTraffic_add
#check tangentVertexIncident_add
#check tangentRatioCellEarthmoverFlow_nonneg
#check tangentRatioCellEarthmoverFlow_self
#check tangentRatioCellEarthmoverFlow_positive_endpoints_ne
#check tangentRatioCellEarthmoverFlow_respectsRatioCells
#check tangentRatioCellEarthmoverFlow_divergence_eq
#check tangentRatioCellEarthmoverFlow_incident_eq
#check tangentRatioCellEarthmoverFlow_incident_le
#check sum_tangentVertexIncident_eq_two_traffic
#check sum_tangentRatioCellUniformPortLoad_eq_two_cutTraffic
#check sum_abs_tangentRatioCellInternalResidual_le
#check tangentRatioCellEarthmoverFlow_traffic_eq
#check tangentRatioCellEarthmoverFlow_traffic_le
#check sum_union_le_add_sum_of_nonneg_real
#check sum_source_filter_eq_outgoing
#check sum_target_filter_eq_incoming
#check tangentIncidentPositiveFlowMass_le_vertexIncident
#check tangentRatioCellEarthmoverFlow_positiveIncident_le
#check tangentRatioCellEarthmoverFlow_positiveEdge_locality
#check tangentRatioCellEarthmoverFlow_spec
#check tangentRatioCellCanonicalCutTraffic_le_prefixUpper

example {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    0 < tangentRatioCellCard bandOf cellIndex (bandOf v) (cellIndex v) :=
  tangentRatioCellCard_at_vertex_pos bandOf cellIndex v

example {V Band : Type*} [Fintype V] [Fintype Band]
    [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex source target =
      tangentRatioCellBoundaryFlow
          lastCell residual bandOf cellIndex source target +
        tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex source target := by
  rfl

example {V Band : Type*} [Fintype V] [Fintype Band]
    [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) v = residual v :=
  tangentRatioCellEarthmoverFlow_divergence_eq
    lastCell residual bandOf cellIndex hindex hoccupied hbalance v

example {V Band : Type*} [Fintype V] [Fintype Band]
    [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    tangentFlowTraffic
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) <=
      tangentDistributedTotalTrafficLedger residual
        (tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex) :=
  tangentRatioCellEarthmoverFlow_traffic_le
    lastCell residual bandOf cellIndex hindex hoccupied hbalance

example {V Band : Type*} [Fintype V] [Fintype Band]
    [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ w : V, tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex w v) <=
      |residual v| +
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v :=
  tangentRatioCellEarthmoverFlow_incident_le
    lastCell residual bandOf cellIndex hindex hoccupied hbalance v

example {V Band : Type*} [Fintype V] [Fintype Band]
    [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellEarthmoverFlow
      lastCell residual bandOf cellIndex source target) :
    source ≠ target :=
  tangentRatioCellEarthmoverFlow_positive_endpoints_ne
    lastCell residual bandOf cellIndex hflow

example {V Band : Type*} [Fintype V] [DecidableEq V]
    [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (label : V -> Nat) (bandOf : V -> Band) (cellIndex : V -> Nat)
    (ratioUpper : Real)
    (hgeometry : TangentRatioCellGeometry
      label bandOf cellIndex ratioUpper)
    {edge : V × V}
    (hedge : edge ∈ tangentPositiveFlowEdges
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex)) :
    (((max (label edge.1) (label edge.2) : Nat) : Real) /
      ((min (label edge.1) (label edge.2) : Nat) : Real)) <= ratioUpper :=
  tangentRatioCellEarthmoverFlow_positiveEdge_locality
    lastCell residual label bandOf cellIndex ratioUpper hgeometry hedge

example {V Band : Type*} [Fintype V] [Fintype Band]
    [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (prefixUpper : Band -> Nat -> Real)
    (hprefix : forall band cut,
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
        prefixUpper band cut) :
    tangentRatioCellCanonicalCutTraffic
        lastCell residual bandOf cellIndex <=
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        prefixUpper band cut :=
  tangentRatioCellCanonicalCutTraffic_le_prefixUpper
    lastCell residual bandOf cellIndex prefixUpper hprefix

end

end Erdos390.WholePaper
