import Erdos390.WholePaper.TangentDistributedFlowCensus
import Erdos390.WholePaper.TangentBalancedProductFlow

/-!
# Explicit ratio-cell earthmover

This file implements the missing finite transport layer behind
`TangentDistributedFlowCensus`.

Inside every exponent band the occupied ratio cells are numbered
`0, ..., lastCell b`.  At the cut after cell `i` the signed prefix mass
`F_i` is spread uniformly over the complete bipartite graph joining cells
`i` and `i+1`, in the direction determined by the sign of `F_i`.  After
these boundary transports, the adjusted residual `q_p` has sum zero in
each cell.  It is transported by the canonical proportional matching from
`TangentBalancedProductFlow`.

The resulting flow is a visible formula, not a conclusion-bearing
certificate.  Its divergence, locality, traffic, and pointwise incident
estimates are theorems.  In particular, no final collision smallness bound
is assumed or stored here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-! ## Uniform cell weights and one boundary cut -/

/-- Uniform probability weight on one ratio cell. -/
def tangentRatioCellUniformWeight
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat) (v : V) : Real :=
  if bandOf v = band ∧ cellIndex v = cell then
    1 / tangentRatioCellCard bandOf cellIndex band cell
  else 0

/-- A cell containing an actual vertex is never a zero denominator. -/
theorem tangentRatioCellCard_at_vertex_pos
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    0 < tangentRatioCellCard bandOf cellIndex
      (bandOf v) (cellIndex v) := by
  classical
  unfold tangentRatioCellCard
  apply Finset.card_pos.mpr
  exact ⟨v, by simp⟩

theorem tangentRatioCellCard_at_vertex_ne_zero
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellCard bandOf cellIndex
      (bandOf v) (cellIndex v) ≠ 0 :=
  (tangentRatioCellCard_at_vertex_pos bandOf cellIndex v).ne'

/-- Totalized division makes an empty cell's uniform weight identically
zero.  Correctness theorems separately require the cells on an active cut
to be occupied. -/
theorem tangentRatioCellUniformWeight_eq_zero_of_card_eq_zero
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat)
    (hcard : tangentRatioCellCard bandOf cellIndex band cell = 0)
    (v : V) :
    tangentRatioCellUniformWeight bandOf cellIndex band cell v = 0 := by
  unfold tangentRatioCellUniformWeight
  split_ifs <;> simp [hcard]

theorem tangentRatioCellUniformWeight_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat) (v : V) :
    0 <= tangentRatioCellUniformWeight bandOf cellIndex band cell v := by
  unfold tangentRatioCellUniformWeight
  split_ifs <;> positivity

theorem sum_tangentRatioCellUniformWeight
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (band : Band) (cell : Nat)
    (hcard : tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    (∑ v : V, tangentRatioCellUniformWeight
      bandOf cellIndex band cell v) = 1 := by
  classical
  unfold tangentRatioCellUniformWeight
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  change
    (tangentRatioCellCard bandOf cellIndex band cell : Real) *
        (1 / tangentRatioCellCard bandOf cellIndex band cell) = 1
  field_simp [Nat.cast_ne_zero.mpr hcard]

@[simp]
theorem tangentRatioCellUniformWeight_at_vertex
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellUniformWeight bandOf cellIndex
        (bandOf v) (cellIndex v) v =
      1 / tangentRatioCellCard bandOf cellIndex
        (bandOf v) (cellIndex v) := by
  simp [tangentRatioCellUniformWeight]

/-- Uniform directed transport attached to one signed prefix cut. -/
def tangentRatioCellBoundaryCutFlow
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (source target : V) : Real :=
  let F := tangentRatioCellPrefixMass residual bandOf cellIndex band cut
  let left := tangentRatioCellUniformWeight bandOf cellIndex band cut
  let right := tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1)
  max F 0 * left source * right target +
    max (-F) 0 * right source * left target

theorem tangentRatioCellBoundaryCutFlow_nonneg
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (source target : V) :
    0 <= tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target := by
  unfold tangentRatioCellBoundaryCutFlow
  exact add_nonneg
    (mul_nonneg
      (mul_nonneg (le_max_right _ _)
        (tangentRatioCellUniformWeight_nonneg
          bandOf cellIndex band cut source))
      (tangentRatioCellUniformWeight_nonneg
        bandOf cellIndex band (cut + 1) target))
    (mul_nonneg
      (mul_nonneg (le_max_right _ _)
        (tangentRatioCellUniformWeight_nonneg
          bandOf cellIndex band (cut + 1) source))
      (tangentRatioCellUniformWeight_nonneg
        bandOf cellIndex band cut target))

/-- If either endpoint cell is empty, the totalized cut formula is zero.
This is harmless for a zero prefix and explains the occupied-cut premise
used by the exact-divergence theorem. -/
theorem tangentRatioCellBoundaryCutFlow_eq_zero_of_left_empty
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut = 0)
    (source target : V) :
    tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target = 0 := by
  simp only [tangentRatioCellBoundaryCutFlow]
  rw [tangentRatioCellUniformWeight_eq_zero_of_card_eq_zero
      bandOf cellIndex band cut hleft source,
    tangentRatioCellUniformWeight_eq_zero_of_card_eq_zero
      bandOf cellIndex band cut hleft target]
  ring

theorem tangentRatioCellBoundaryCutFlow_eq_zero_of_right_empty
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) = 0)
    (source target : V) :
    tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target = 0 := by
  simp only [tangentRatioCellBoundaryCutFlow]
  rw [tangentRatioCellUniformWeight_eq_zero_of_card_eq_zero
      bandOf cellIndex band (cut + 1) hright source,
    tangentRatioCellUniformWeight_eq_zero_of_card_eq_zero
      bandOf cellIndex band (cut + 1) hright target]
  ring

@[simp]
theorem tangentRatioCellBoundaryCutFlow_self
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat) (v : V) :
    tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut v v = 0 := by
  unfold tangentRatioCellBoundaryCutFlow tangentRatioCellUniformWeight
  by_cases hleft : bandOf v = band ∧ cellIndex v = cut
  · simp [hleft]
  · by_cases hright : bandOf v = band ∧ cellIndex v = cut + 1
    · simp [hright]
    · simp [hleft, hright]

theorem sum_tangentRatioCellBoundaryCutFlow_out
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (source : V) :
    (∑ target : V, tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) =
      max (tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band cut source +
        max (-tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) source := by
  unfold tangentRatioCellBoundaryCutFlow
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) hright,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band cut hleft]
  ring

theorem sum_tangentRatioCellBoundaryCutFlow_in
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (target : V) :
    (∑ source : V, tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) =
      max (tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) target +
        max (-tangentRatioCellPrefixMass residual bandOf cellIndex band cut) 0 *
          tangentRatioCellUniformWeight bandOf cellIndex band cut target := by
  dsimp only [tangentRatioCellBoundaryCutFlow]
  rw [Finset.sum_add_distrib,
    ← Finset.sum_mul, ← Finset.sum_mul,
    ← Finset.mul_sum, ← Finset.mul_sum,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band cut hleft,
    sum_tangentRatioCellUniformWeight
      bandOf cellIndex band (cut + 1) hright]
  ring

theorem tangentRatioCellBoundaryCutFlow_divergence
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut) v =
      tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
        (tangentRatioCellUniformWeight bandOf cellIndex band cut v -
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) v) := by
  rw [tangentFlowDivergence,
    sum_tangentRatioCellBoundaryCutFlow_out
      residual bandOf cellIndex band cut hleft hright v,
    sum_tangentRatioCellBoundaryCutFlow_in
      residual bandOf cellIndex band cut hleft hright v]
  calc
    _ =
        (max (tangentRatioCellPrefixMass
            residual bandOf cellIndex band cut) 0 -
          max (-tangentRatioCellPrefixMass
            residual bandOf cellIndex band cut) 0) *
          (tangentRatioCellUniformWeight bandOf cellIndex band cut v -
            tangentRatioCellUniformWeight
              bandOf cellIndex band (cut + 1) v) := by
        ring
    _ = _ := by
      rw [max_zero_sub_max_neg_zero_eq_self]

/-- Sign audit: positive `F_i` leaves the left cell, so its divergence is
`+F_i / |Q_i|`. -/
theorem tangentRatioCellBoundaryCutFlow_divergence_of_mem_left
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (v : V) (hv : bandOf v = band ∧ cellIndex v = cut) :
    tangentFlowDivergence
        (tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut) v =
      tangentRatioCellPrefixMass residual bandOf cellIndex band cut /
        tangentRatioCellCard bandOf cellIndex band cut := by
  rw [tangentRatioCellBoundaryCutFlow_divergence
    residual bandOf cellIndex band cut hleft hright v]
  simp [tangentRatioCellUniformWeight, hv]
  ring

/-- Sign audit: the same cut enters the right cell, contributing
`-F_i / |Q_(i+1)|`. -/
theorem tangentRatioCellBoundaryCutFlow_divergence_of_mem_right
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (v : V) (hv : bandOf v = band ∧ cellIndex v = cut + 1) :
    tangentFlowDivergence
        (tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut) v =
      -tangentRatioCellPrefixMass residual bandOf cellIndex band cut /
        tangentRatioCellCard bandOf cellIndex band (cut + 1) := by
  rw [tangentRatioCellBoundaryCutFlow_divergence
    residual bandOf cellIndex band cut hleft hright v]
  simp [tangentRatioCellUniformWeight, hv]
  ring

theorem tangentRatioCellBoundaryCutFlow_traffic
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut) =
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| := by
  unfold tangentFlowTraffic
  simp_rw [sum_tangentRatioCellBoundaryCutFlow_out
    residual bandOf cellIndex band cut hleft hright]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band cut hleft,
    sum_tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) hright]
  simpa only [mul_one] using
    max_zero_add_max_neg_zero_eq_abs_self
      (tangentRatioCellPrefixMass residual bandOf cellIndex band cut)

theorem tangentRatioCellBoundaryCutFlow_incident
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    (hleft : tangentRatioCellCard bandOf cellIndex band cut ≠ 0)
    (hright : tangentRatioCellCard bandOf cellIndex band (cut + 1) ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellBoundaryCutFlow
        residual bandOf cellIndex band cut v w) +
      (∑ w : V, tangentRatioCellBoundaryCutFlow
        residual bandOf cellIndex band cut w v) =
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
        (tangentRatioCellUniformWeight bandOf cellIndex band cut v +
          tangentRatioCellUniformWeight bandOf cellIndex band (cut + 1) v) := by
  rw [sum_tangentRatioCellBoundaryCutFlow_out
      residual bandOf cellIndex band cut hleft hright v,
    sum_tangentRatioCellBoundaryCutFlow_in
      residual bandOf cellIndex band cut hleft hright v,
    ← max_zero_add_max_neg_zero_eq_abs_self
      (tangentRatioCellPrefixMass residual bandOf cellIndex band cut)]
  ring

/-! ## Finite-sum linearity for flows -/

theorem tangentFlowDivergence_finset_sum
    {V I : Type*} [Fintype V] (indices : Finset I)
    (flow : I -> V -> V -> Real) (v : V) :
    tangentFlowDivergence
        (fun source target => ∑ i ∈ indices, flow i source target) v =
      ∑ i ∈ indices, tangentFlowDivergence (flow i) v := by
  unfold tangentFlowDivergence
  have hout :
      (∑ w : V, ∑ i ∈ indices, flow i v w) =
        ∑ i ∈ indices, ∑ w : V, flow i v w := by
    exact Finset.sum_comm
  have hin :
      (∑ w : V, ∑ i ∈ indices, flow i w v) =
        ∑ i ∈ indices, ∑ w : V, flow i w v := by
    exact Finset.sum_comm
  rw [hout, hin]
  rw [← Finset.sum_sub_distrib]

theorem tangentFlowTraffic_finset_sum
    {V I : Type*} [Fintype V] (indices : Finset I)
    (flow : I -> V -> V -> Real) :
    tangentFlowTraffic
        (fun source target => ∑ i ∈ indices, flow i source target) =
      ∑ i ∈ indices, tangentFlowTraffic (flow i) := by
  unfold tangentFlowTraffic
  calc
    (∑ source : V, ∑ target : V,
        ∑ i ∈ indices, flow i source target) =
        ∑ source : V, ∑ i ∈ indices,
          ∑ target : V, flow i source target := by
      apply Finset.sum_congr rfl
      intro source _hsource
      exact Finset.sum_comm
    _ = ∑ i ∈ indices, ∑ source : V,
          ∑ target : V, flow i source target := by
      exact Finset.sum_comm

theorem tangentVertexIncident_finset_sum
    {V I : Type*} [Fintype V] (indices : Finset I)
    (flow : I -> V -> V -> Real) (v : V) :
    (∑ w : V, ∑ i ∈ indices, flow i v w) +
        (∑ w : V, ∑ i ∈ indices, flow i w v) =
      ∑ i ∈ indices,
        ((∑ w : V, flow i v w) + ∑ w : V, flow i w v) := by
  have hout :
      (∑ w : V, ∑ i ∈ indices, flow i v w) =
        ∑ i ∈ indices, ∑ w : V, flow i v w := by
    exact Finset.sum_comm
  have hin :
      (∑ w : V, ∑ i ∈ indices, flow i w v) =
        ∑ i ∈ indices, ∑ w : V, flow i w v := by
    exact Finset.sum_comm
  rw [hout, hin, ← Finset.sum_add_distrib]

/-! ## All canonical cuts in one finite band family -/

/-- Literal cut traffic over `0 <= i < lastCell b`. -/
def tangentRatioCellCanonicalCutTraffic
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) : Real :=
  ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
    |tangentRatioCellPrefixMass residual bandOf cellIndex band cut|

/-- Sum of all adjacent-cell uniform cut flows. -/
def tangentRatioCellBoundaryFlow
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) : Real :=
  ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
    tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target

theorem tangentRatioCellBoundaryFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellBoundaryFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellBoundaryFlow
  exact Finset.sum_nonneg fun band _hband =>
    Finset.sum_nonneg fun cut _hcut =>
      tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target

@[simp]
theorem tangentRatioCellBoundaryFlow_self
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellBoundaryFlow
      lastCell residual bandOf cellIndex v v = 0 := by
  unfold tangentRatioCellBoundaryFlow
  simp

/-! ## Prefix algebra and exact boundary divergence -/

/-- At the final cell of a band, the prefix is the full band sum. -/
theorem tangentRatioCellPrefixMass_lastCell
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (band : Band) :
    tangentRatioCellPrefixMass residual bandOf cellIndex
        band (lastCell band) =
      ∑ v : V, if bandOf v = band then residual v else 0 := by
  unfold tangentRatioCellPrefixMass
  apply Finset.sum_congr rfl
  intro v _hv
  by_cases hv : bandOf v = band
  · have hle : cellIndex v <= lastCell band := by
      simpa only [hv] using hindex v
    simp [hv, hle]
  · simp [hv]

/-- The residual mass of cell `i` is the difference of its right and left
prefixes. -/
theorem sum_tangentRatioCell_eq_prefix_sub_left
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat) :
    (∑ v : V,
        if bandOf v = band ∧ cellIndex v = cell then residual v else 0) =
      tangentRatioCellPrefixMass residual bandOf cellIndex band cell -
        (if cell = 0 then 0 else
          tangentRatioCellPrefixMass residual bandOf cellIndex
            band (cell - 1)) := by
  cases cell with
  | zero =>
      unfold tangentRatioCellPrefixMass
      simp
  | succ cell =>
      simp only [Nat.succ_ne_zero, if_false, Nat.succ_sub_one]
      unfold tangentRatioCellPrefixMass
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hband : bandOf v = band
      · simp only [hband, true_and]
        by_cases hlePrevious : cellIndex v <= cell
        · have hsucc : cellIndex v <= cell + 1 := by omega
          have hne : cellIndex v ≠ cell + 1 := by omega
          simp [hsucc, hlePrevious, hne]
        · by_cases hsucc : cellIndex v <= cell + 1
          · have heq : cellIndex v = cell + 1 := by omega
            simp [heq]
          · have hne : cellIndex v ≠ cell + 1 := by omega
            simp [hsucc, hlePrevious, hne]
      · simp [hband]

theorem tangentRatioCellBoundaryFlow_divergence_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellBoundaryFlow
          lastCell residual bandOf cellIndex) v =
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
          (tangentRatioCellUniformWeight bandOf cellIndex band cut v -
            tangentRatioCellUniformWeight bandOf cellIndex
              band (cut + 1) v) := by
  unfold tangentRatioCellBoundaryFlow
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro cut hcut
  have hcutlt : cut < lastCell band := Finset.mem_range.mp hcut
  rw [tangentRatioCellBoundaryCutFlow_divergence
    residual bandOf cellIndex band cut
      (hoccupied band cut (by omega))
      (hoccupied band (cut + 1) (by omega)) v]

/-- Only the cut immediately to the right of `v` contributes its left-port
weight; at a terminal cell its prefix is zero by band balance. -/
theorem sum_prefix_mul_leftUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
          tangentRatioCellUniformWeight bandOf cellIndex band cut v) =
      tangentRatioCellPrefixMass residual bandOf cellIndex
          (bandOf v) (cellIndex v) /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · have hle := hindex v
    by_cases hlt : cellIndex v < lastCell (bandOf v)
    · rw [Finset.sum_eq_single (cellIndex v)]
      · simp [tangentRatioCellUniformWeight, div_eq_mul_inv]
      · intro cut hcut hne
        have hcell : cellIndex v ≠ cut := Ne.symm hne
        simp [tangentRatioCellUniformWeight, hcell]
      · intro hnotmem
        exact (hnotmem (Finset.mem_range.mpr hlt)).elim
    · have heq : cellIndex v = lastCell (bandOf v) := by omega
      have hprefix :
          tangentRatioCellPrefixMass residual bandOf cellIndex
              (bandOf v) (cellIndex v) = 0 := by
        rw [heq, tangentRatioCellPrefixMass_lastCell
          lastCell residual bandOf cellIndex hindex]
        exact hbalance (bandOf v)
      rw [hprefix, zero_div]
      apply Finset.sum_eq_zero
      intro cut hcut
      have hcutlt := Finset.mem_range.mp hcut
      have hne : cellIndex v ≠ cut := by omega
      simp [tangentRatioCellUniformWeight, hne]
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

/-- Only the cut immediately to the left of `v` contributes its right-port
weight. -/
theorem sum_prefix_mul_rightUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellPrefixMass residual bandOf cellIndex band cut *
          tangentRatioCellUniformWeight bandOf cellIndex
            band (cut + 1) v) =
      tangentRatioCellLeftPrefixMass residual bandOf cellIndex v /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · cases hcell : cellIndex v with
    | zero =>
        rw [show tangentRatioCellLeftPrefixMass
            residual bandOf cellIndex v = 0 by
          simp [tangentRatioCellLeftPrefixMass, hcell], zero_div]
        apply Finset.sum_eq_zero
        intro cut hcut
        have hne : cellIndex v ≠ cut + 1 := by omega
        simp [tangentRatioCellUniformWeight, hne]
    | succ previous =>
        have hprevlt : previous < lastCell (bandOf v) := by
          have hle := hindex v
          omega
        rw [Finset.sum_eq_single previous]
        · simp [tangentRatioCellUniformWeight,
            tangentRatioCellLeftPrefixMass, hcell, div_eq_mul_inv]
        · intro cut hcut hne
          have hcellne : cellIndex v ≠ cut + 1 := by omega
          simp [tangentRatioCellUniformWeight, hcellne]
        · intro hnotmem
          exact (hnotmem (Finset.mem_range.mpr hprevlt)).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

/-- The sum of the uniform cut divergences is exactly the previously
declared boundary-divergence formula. -/
theorem tangentRatioCellBoundaryFlow_divergence_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
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
        (tangentRatioCellBoundaryFlow
          lastCell residual bandOf cellIndex) v =
      tangentRatioCellBoundaryDivergence
        residual bandOf cellIndex v := by
  rw [tangentRatioCellBoundaryFlow_divergence_cutSum
      lastCell residual bandOf cellIndex hoccupied v]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [sum_prefix_mul_leftUniformWeight
      lastCell residual bandOf cellIndex hindex hbalance v,
    sum_prefix_mul_rightUniformWeight
      lastCell residual bandOf cellIndex hindex v]
  unfold tangentRatioCellBoundaryDivergence
  ring

theorem tangentRatioCellBoundaryFlow_traffic_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellBoundaryFlow
          lastCell residual bandOf cellIndex) =
      tangentRatioCellCanonicalCutTraffic
        lastCell residual bandOf cellIndex := by
  unfold tangentRatioCellBoundaryFlow tangentRatioCellCanonicalCutTraffic
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro cut hcut
  have hcutlt := Finset.mem_range.mp hcut
  exact tangentRatioCellBoundaryCutFlow_traffic
    residual bandOf cellIndex band cut
      (hoccupied band cut (by omega))
      (hoccupied band (cut + 1) (by omega))

theorem tangentRatioCellBoundaryFlow_incident_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex w v) =
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
          (tangentRatioCellUniformWeight bandOf cellIndex band cut v +
            tangentRatioCellUniformWeight bandOf cellIndex
              band (cut + 1) v) := by
  unfold tangentRatioCellBoundaryFlow
  rw [tangentVertexIncident_finset_sum
    (Finset.univ : Finset Band)
    (fun band source target =>
      ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellBoundaryCutFlow residual bandOf cellIndex
          band cut source target) v]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentVertexIncident_finset_sum
    (Finset.range (lastCell band))
    (fun cut source target =>
      tangentRatioCellBoundaryCutFlow residual bandOf cellIndex
        band cut source target) v]
  apply Finset.sum_congr rfl
  intro cut hcut
  have hcutlt := Finset.mem_range.mp hcut
  exact tangentRatioCellBoundaryCutFlow_incident
    residual bandOf cellIndex band cut
      (hoccupied band cut (by omega))
      (hoccupied band (cut + 1) (by omega)) v

theorem sum_abs_prefix_mul_leftUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
          tangentRatioCellUniformWeight bandOf cellIndex band cut v) =
      |tangentRatioCellPrefixMass residual bandOf cellIndex
          (bandOf v) (cellIndex v)| /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · have hle := hindex v
    by_cases hlt : cellIndex v < lastCell (bandOf v)
    · rw [Finset.sum_eq_single (cellIndex v)]
      · simp [tangentRatioCellUniformWeight, div_eq_mul_inv]
      · intro cut hcut hne
        have hcell : cellIndex v ≠ cut := Ne.symm hne
        simp [tangentRatioCellUniformWeight, hcell]
      · intro hnotmem
        exact (hnotmem (Finset.mem_range.mpr hlt)).elim
    · have heq : cellIndex v = lastCell (bandOf v) := by omega
      have hprefix :
          tangentRatioCellPrefixMass residual bandOf cellIndex
              (bandOf v) (cellIndex v) = 0 := by
        rw [heq, tangentRatioCellPrefixMass_lastCell
          lastCell residual bandOf cellIndex hindex]
        exact hbalance (bandOf v)
      rw [hprefix, abs_zero, zero_div]
      apply Finset.sum_eq_zero
      intro cut hcut
      have hcutlt := Finset.mem_range.mp hcut
      have hne : cellIndex v ≠ cut := by omega
      simp [tangentRatioCellUniformWeight, hne]
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

theorem sum_abs_prefix_mul_rightUniformWeight
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| *
          tangentRatioCellUniformWeight bandOf cellIndex
            band (cut + 1) v) =
      |tangentRatioCellLeftPrefixMass residual bandOf cellIndex v| /
        tangentRatioCellCard bandOf cellIndex
          (bandOf v) (cellIndex v) := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · cases hcell : cellIndex v with
    | zero =>
        rw [show tangentRatioCellLeftPrefixMass
            residual bandOf cellIndex v = 0 by
          simp [tangentRatioCellLeftPrefixMass, hcell], abs_zero, zero_div]
        apply Finset.sum_eq_zero
        intro cut hcut
        have hne : cellIndex v ≠ cut + 1 := by omega
        simp [tangentRatioCellUniformWeight, hne]
    | succ previous =>
        have hprevlt : previous < lastCell (bandOf v) := by
          have hle := hindex v
          omega
        rw [Finset.sum_eq_single previous]
        · simp [tangentRatioCellUniformWeight,
            tangentRatioCellLeftPrefixMass, hcell, div_eq_mul_inv]
        · intro cut hcut hne
          have hcellne : cellIndex v ≠ cut + 1 := by omega
          simp [tangentRatioCellUniformWeight, hcellne]
        · intro hnotmem
          exact (hnotmem (Finset.mem_range.mpr hprevlt)).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cut hcut
    have hne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellUniformWeight, hne]

/-- Boundary traffic incident to a vertex is exactly its declared uniform
two-port load. -/
theorem tangentRatioCellBoundaryFlow_incident_eq_portLoad
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (v : V) :
    (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex w v) =
      tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  rw [tangentRatioCellBoundaryFlow_incident_cutSum
      lastCell residual bandOf cellIndex hoccupied v]
  simp_rw [mul_add, Finset.sum_add_distrib]
  rw [sum_abs_prefix_mul_leftUniformWeight
      lastCell residual bandOf cellIndex hindex hbalance v,
    sum_abs_prefix_mul_rightUniformWeight
      lastCell residual bandOf cellIndex hindex v]
  unfold tangentRatioCellUniformPortLoad
  ring

/-! ## The balanced residual inside each cell -/

/-- The internal residual masked to one literal ratio cell. -/
def tangentRatioCellMaskedInternalResidual
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat) (v : V) : Real :=
  if bandOf v = band ∧ cellIndex v = cell then
    tangentRatioCellInternalResidual residual bandOf cellIndex v
  else 0

/-- Sum of the canonical proportional matchings in all cells. -/
def tangentRatioCellInternalFlow
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) : Real :=
  ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
    tangentBalancedProductFlow
      (tangentRatioCellMaskedInternalResidual
        residual bandOf cellIndex band cell) source target

theorem tangentRatioCellInternalFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellInternalFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellInternalFlow
  exact Finset.sum_nonneg fun band _hband =>
    Finset.sum_nonneg fun cell _hcell =>
      tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target

@[simp]
theorem tangentRatioCellInternalFlow_self
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellInternalFlow
      lastCell residual bandOf cellIndex v v = 0 := by
  unfold tangentRatioCellInternalFlow
  simp

/-- Summing the uniform boundary divergence over one cell recovers the
difference of its two prefix masses. -/
theorem sum_tangentRatioCellBoundaryDivergence_eq_prefix_sub_left
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat)
    (hcard : tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    (∑ v : V,
        if bandOf v = band ∧ cellIndex v = cell then
          tangentRatioCellBoundaryDivergence residual bandOf cellIndex v
        else 0) =
      tangentRatioCellPrefixMass residual bandOf cellIndex band cell -
        (if cell = 0 then 0 else
          tangentRatioCellPrefixMass residual bandOf cellIndex
            band (cell - 1)) := by
  classical
  rw [← Finset.sum_filter]
  let numerator :=
    tangentRatioCellPrefixMass residual bandOf cellIndex band cell -
      (if cell = 0 then 0 else
        tangentRatioCellPrefixMass residual bandOf cellIndex
          band (cell - 1))
  calc
    (∑ v ∈ (Finset.univ : Finset V).filter
        (fun v => bandOf v = band ∧ cellIndex v = cell),
        tangentRatioCellBoundaryDivergence residual bandOf cellIndex v) =
        ∑ _v ∈ (Finset.univ : Finset V).filter
          (fun v => bandOf v = band ∧ cellIndex v = cell),
            numerator / tangentRatioCellCard bandOf cellIndex band cell := by
      apply Finset.sum_congr rfl
      intro v hv
      have hvdata := (Finset.mem_filter.mp hv).2
      rcases hvdata with ⟨hvband, hvcell⟩
      simp [tangentRatioCellBoundaryDivergence,
        tangentRatioCellLeftPrefixMass, hvband, hvcell, numerator]
    _ = (tangentRatioCellCard bandOf cellIndex band cell : Real) *
          (numerator / tangentRatioCellCard bandOf cellIndex band cell) := by
      simp [tangentRatioCellCard, Finset.sum_const, nsmul_eq_mul]
    _ = numerator := by
      field_simp [Nat.cast_ne_zero.mpr hcard]

/-- After removing the boundary divergence, each cell has zero internal
residual. -/
theorem sum_tangentRatioCellMaskedInternalResidual_eq_zero
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (band : Band) (cell : Nat) (hcell : cell <= lastCell band) :
    (∑ v : V, tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell v) = 0 := by
  calc
    (∑ v : V, tangentRatioCellMaskedInternalResidual
        residual bandOf cellIndex band cell v) =
        (∑ v : V,
          if bandOf v = band ∧ cellIndex v = cell then residual v else 0) -
        ∑ v : V,
          if bandOf v = band ∧ cellIndex v = cell then
            tangentRatioCellBoundaryDivergence residual bandOf cellIndex v
          else 0 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro v _hv
      by_cases hv : bandOf v = band ∧ cellIndex v = cell
      · simp [tangentRatioCellMaskedInternalResidual,
          tangentRatioCellInternalResidual, hv]
      · simp [tangentRatioCellMaskedInternalResidual, hv]
    _ = 0 := by
      rw [sum_tangentRatioCell_eq_prefix_sub_left,
        sum_tangentRatioCellBoundaryDivergence_eq_prefix_sub_left
          residual bandOf cellIndex band cell
            (hoccupied band cell hcell)]
      ring

/-- The cell sum of product-flow divergences is the masked internal
residual itself. -/
theorem tangentRatioCellInternalFlow_divergence_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) v =
      ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v := by
  unfold tangentRatioCellInternalFlow
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowDivergence_finset_sum]
  apply Finset.sum_congr rfl
  intro cell hcell
  have hcellle : cell <= lastCell band := by
    have := Finset.mem_range.mp hcell
    omega
  exact tangentBalancedProductFlow_divergence_eq
    (tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell)
    (sum_tangentRatioCellMaskedInternalResidual_eq_zero
      lastCell residual bandOf cellIndex hoccupied band cell hcellle) v

theorem sum_tangentRatioCellMaskedInternalResidual_at_vertex
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v) =
      tangentRatioCellInternalResidual residual bandOf cellIndex v := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · rw [Finset.sum_eq_single (cellIndex v)]
    · simp [tangentRatioCellMaskedInternalResidual]
    · intro cell hcell hne
      have hcellne : cellIndex v ≠ cell := Ne.symm hne
      simp [tangentRatioCellMaskedInternalResidual, hcellne]
    · intro hnotmem
      exact (hnotmem (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hindex v)))).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cell hcell
    have hbandne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellMaskedInternalResidual, hbandne]

theorem tangentRatioCellInternalFlow_divergence_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    tangentFlowDivergence
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) v =
      tangentRatioCellInternalResidual residual bandOf cellIndex v := by
  rw [tangentRatioCellInternalFlow_divergence_cutSum
      lastCell residual bandOf cellIndex hoccupied v,
    sum_tangentRatioCellMaskedInternalResidual_at_vertex
      lastCell residual bandOf cellIndex hindex v]

theorem tangentRatioCellInternalFlow_incident_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex w v) =
      ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        |tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v| := by
  unfold tangentRatioCellInternalFlow
  rw [tangentVertexIncident_finset_sum
    (Finset.univ : Finset Band)
    (fun band source target =>
      ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentBalancedProductFlow
          (tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell) source target) v]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentVertexIncident_finset_sum
    (Finset.range (lastCell band + 1))
    (fun cell source target =>
      tangentBalancedProductFlow
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target) v]
  apply Finset.sum_congr rfl
  intro cell hcell
  have hcellle : cell <= lastCell band := by
    have := Finset.mem_range.mp hcell
    omega
  exact tangentBalancedProductFlow_incident_eq_abs
    (tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell)
    (sum_tangentRatioCellMaskedInternalResidual_eq_zero
      lastCell residual bandOf cellIndex hoccupied band cell hcellle) v

theorem sum_abs_tangentRatioCellMaskedInternalResidual_at_vertex
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (v : V) :
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        |tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell v|) =
      |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  classical
  rw [Fintype.sum_eq_single (bandOf v)]
  · rw [Finset.sum_eq_single (cellIndex v)]
    · simp [tangentRatioCellMaskedInternalResidual]
    · intro cell hcell hne
      have hcellne : cellIndex v ≠ cell := Ne.symm hne
      simp [tangentRatioCellMaskedInternalResidual, hcellne]
    · intro hnotmem
      exact (hnotmem (Finset.mem_range.mpr
        (Nat.lt_succ_of_le (hindex v)))).elim
  · intro band hband
    apply Finset.sum_eq_zero
    intro cell hcell
    have hbandne : bandOf v ≠ band := Ne.symm hband
    simp [tangentRatioCellMaskedInternalResidual, hbandne]

/-- Internal incident traffic is exactly `|q_p|`. -/
theorem tangentRatioCellInternalFlow_incident_eq_abs
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (v : V) :
    (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex v w) +
      (∑ w : V, tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex w v) =
      |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  rw [tangentRatioCellInternalFlow_incident_cutSum
      lastCell residual bandOf cellIndex hoccupied v,
    sum_abs_tangentRatioCellMaskedInternalResidual_at_vertex
      lastCell residual bandOf cellIndex hindex v]

theorem tangentRatioCellInternalFlow_traffic_cutSum
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) =
      ∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        (∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) / 2 := by
  unfold tangentRatioCellInternalFlow
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro band _hband
  rw [tangentFlowTraffic_finset_sum]
  apply Finset.sum_congr rfl
  intro cell hcell
  have hcellle : cell <= lastCell band := by
    have := Finset.mem_range.mp hcell
    omega
  exact tangentBalancedProductFlow_traffic_eq_half_sum_abs
    (tangentRatioCellMaskedInternalResidual
      residual bandOf cellIndex band cell)
    (sum_tangentRatioCellMaskedInternalResidual_eq_zero
      lastCell residual bandOf cellIndex hoccupied band cell hcellle)

theorem sum_abs_tangentRatioCellMaskedInternalResidual_partition
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v)) :
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        ∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) =
      ∑ v : V,
        |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  calc
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        ∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) =
        ∑ band : Band, ∑ v : V,
          ∑ cell ∈ Finset.range (lastCell band + 1),
            |tangentRatioCellMaskedInternalResidual
              residual bandOf cellIndex band cell v| := by
      apply Finset.sum_congr rfl
      intro band _hband
      exact Finset.sum_comm
    _ = ∑ v : V, ∑ band : Band,
          ∑ cell ∈ Finset.range (lastCell band + 1),
            |tangentRatioCellMaskedInternalResidual
              residual bandOf cellIndex band cell v| := by
      exact Finset.sum_comm
    _ = ∑ v : V,
          |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
      apply Finset.sum_congr rfl
      intro v _hv
      exact sum_abs_tangentRatioCellMaskedInternalResidual_at_vertex
        lastCell residual bandOf cellIndex hindex v

/-- Internal traffic is exactly half the global `ell^1` mass of `q`. -/
theorem tangentRatioCellInternalFlow_traffic_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex) =
      (∑ v : V,
        |tangentRatioCellInternalResidual residual bandOf cellIndex v|) / 2 := by
  rw [tangentRatioCellInternalFlow_traffic_cutSum
      lastCell residual bandOf cellIndex hoccupied]
  calc
    (∑ band : Band, ∑ cell ∈ Finset.range (lastCell band + 1),
        (∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) / 2) =
        ∑ band : Band,
          (∑ cell ∈ Finset.range (lastCell band + 1),
            ∑ v : V,
              |tangentRatioCellMaskedInternalResidual
                residual bandOf cellIndex band cell v|) / 2 := by
      apply Finset.sum_congr rfl
      intro band _hband
      exact (Finset.sum_div
        (Finset.range (lastCell band + 1))
        (fun cell => ∑ v : V,
          |tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell v|) 2).symm
    _ = (∑ band : Band,
          ∑ cell ∈ Finset.range (lastCell band + 1),
            ∑ v : V,
              |tangentRatioCellMaskedInternalResidual
                residual bandOf cellIndex band cell v|) / 2 := by
      exact (Finset.sum_div (Finset.univ : Finset Band)
        (fun band =>
          ∑ cell ∈ Finset.range (lastCell band + 1),
            ∑ v : V,
              |tangentRatioCellMaskedInternalResidual
                residual bandOf cellIndex band cell v|) 2).symm
    _ = (∑ v : V,
          |tangentRatioCellInternalResidual residual bandOf cellIndex v|) /
        2 := by
      rw [sum_abs_tangentRatioCellMaskedInternalResidual_partition
        lastCell residual bandOf cellIndex hindex]

/-! ## Support locality -/

theorem tangentRatioCellBoundaryCutFlow_positive_cells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) :
    ((bandOf source = band ∧ cellIndex source = cut) ∧
        (bandOf target = band ∧ cellIndex target = cut + 1)) ∨
      ((bandOf source = band ∧ cellIndex source = cut + 1) ∧
        (bandOf target = band ∧ cellIndex target = cut)) := by
  by_cases hsourceLeft : bandOf source = band ∧ cellIndex source = cut
  · by_cases htargetRight :
        bandOf target = band ∧ cellIndex target = cut + 1
    · exact Or.inl ⟨hsourceLeft, htargetRight⟩
    · have hsourceRight :
          ¬(bandOf source = band ∧ cellIndex source = cut + 1) := by
        intro h
        omega
      simp [tangentRatioCellBoundaryCutFlow,
        tangentRatioCellUniformWeight, htargetRight, hsourceRight] at hflow
  · by_cases hsourceRight :
        bandOf source = band ∧ cellIndex source = cut + 1
    · by_cases htargetLeft :
          bandOf target = band ∧ cellIndex target = cut
      · exact Or.inr ⟨hsourceRight, htargetLeft⟩
      · simp [tangentRatioCellBoundaryCutFlow,
          tangentRatioCellUniformWeight, hsourceLeft, htargetLeft] at hflow
    · simp [tangentRatioCellBoundaryCutFlow,
        tangentRatioCellUniformWeight, hsourceLeft, hsourceRight] at hflow

theorem tangentRatioCellBoundaryCutFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cut : Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellBoundaryCutFlow
      residual bandOf cellIndex band cut source target) :
    TangentSameOrAdjacentRatioCell bandOf cellIndex source target := by
  rcases tangentRatioCellBoundaryCutFlow_positive_cells
      residual bandOf cellIndex band cut hflow with hforward | hbackward
  · rcases hforward with ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
    exact ⟨hsband.trans htband.symm, Or.inr (Or.inl (by omega))⟩
  · rcases hbackward with ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
    exact ⟨hsband.trans htband.symm, Or.inr (Or.inr (by omega))⟩

theorem tangentRatioCellBoundaryFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  unfold tangentRatioCellBoundaryFlow at hflow
  have houterNonneg : forall band : Band,
      0 <= ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellBoundaryCutFlow
          residual bandOf cellIndex band cut source target := by
    intro band
    exact Finset.sum_nonneg fun cut _hcut =>
      tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target
  obtain ⟨band, _hband, hbandPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun band _hband => houterNonneg band)).mp hflow
  obtain ⟨cut, hcut, hcutPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun cut _hcut => tangentRatioCellBoundaryCutFlow_nonneg
        residual bandOf cellIndex band cut source target)).mp hbandPos
  exact tangentRatioCellBoundaryCutFlow_respectsRatioCells
    residual bandOf cellIndex band cut hcutPos

theorem tangentBalancedProductFlow_masked_positive_cells
    {V Band : Type*} [Fintype V] [DecidableEq Band]
    (residual : V -> Real) (bandOf : V -> Band)
    (cellIndex : V -> Nat) (band : Band) (cell : Nat)
    {source target : V}
    (hflow : 0 < tangentBalancedProductFlow
      (tangentRatioCellMaskedInternalResidual
        residual bandOf cellIndex band cell) source target) :
    (bandOf source = band ∧ cellIndex source = cell) ∧
      (bandOf target = band ∧ cellIndex target = cell) := by
  by_cases hsource : bandOf source = band ∧ cellIndex source = cell
  · by_cases htarget : bandOf target = band ∧ cellIndex target = cell
    · exact ⟨hsource, htarget⟩
    · simp [tangentBalancedProductFlow,
        tangentRatioCellMaskedInternalResidual, htarget] at hflow
  · simp [tangentBalancedProductFlow,
      tangentRatioCellMaskedInternalResidual, hsource] at hflow

theorem tangentRatioCellInternalFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellInternalFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  unfold tangentRatioCellInternalFlow at hflow
  have houterNonneg : forall band : Band,
      0 <= ∑ cell ∈ Finset.range (lastCell band + 1),
        tangentBalancedProductFlow
          (tangentRatioCellMaskedInternalResidual
            residual bandOf cellIndex band cell) source target := by
    intro band
    exact Finset.sum_nonneg fun cell _hcell =>
      tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target
  obtain ⟨band, _hband, hbandPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun band _hband => houterNonneg band)).mp hflow
  obtain ⟨cell, hcell, hcellPos⟩ :=
    (Finset.sum_pos_iff_of_nonneg
      (fun cell _hcell => tangentBalancedProductFlow_nonneg
        (tangentRatioCellMaskedInternalResidual
          residual bandOf cellIndex band cell) source target)).mp hbandPos
  rcases tangentBalancedProductFlow_masked_positive_cells
      residual bandOf cellIndex band cell hcellPos with
    ⟨⟨hsband, hscell⟩, ⟨htband, htcell⟩⟩
  exact ⟨hsband.trans htband.symm, Or.inl (hscell.trans htcell.symm)⟩

/-! ## The complete explicit earthmover -/

/-- Boundary prefix transport plus the balanced within-cell matching. -/
def tangentRatioCellEarthmoverFlow
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) : Real :=
  tangentRatioCellBoundaryFlow
      lastCell residual bandOf cellIndex source target +
    tangentRatioCellInternalFlow
      lastCell residual bandOf cellIndex source target

theorem tangentFlowDivergence_add
    {V : Type*} [Fintype V] (flow₁ flow₂ : V -> V -> Real) (v : V) :
    tangentFlowDivergence
        (fun source target => flow₁ source target + flow₂ source target) v =
      tangentFlowDivergence flow₁ v + tangentFlowDivergence flow₂ v := by
  unfold tangentFlowDivergence
  simp_rw [Finset.sum_add_distrib]
  ring

theorem tangentFlowTraffic_add
    {V : Type*} [Fintype V] (flow₁ flow₂ : V -> V -> Real) :
    tangentFlowTraffic
        (fun source target => flow₁ source target + flow₂ source target) =
      tangentFlowTraffic flow₁ + tangentFlowTraffic flow₂ := by
  unfold tangentFlowTraffic
  simp_rw [Finset.sum_add_distrib]

theorem tangentVertexIncident_add
    {V : Type*} [Fintype V] (flow₁ flow₂ : V -> V -> Real) (v : V) :
    (∑ u : V, (flow₁ v u + flow₂ v u)) +
        (∑ u : V, (flow₁ u v + flow₂ u v)) =
      ((∑ u : V, flow₁ v u) + ∑ u : V, flow₁ u v) +
        ((∑ u : V, flow₂ v u) + ∑ u : V, flow₂ u v) := by
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem tangentRatioCellEarthmoverFlow_nonneg
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (source target : V) :
    0 <= tangentRatioCellEarthmoverFlow
      lastCell residual bandOf cellIndex source target := by
  unfold tangentRatioCellEarthmoverFlow
  exact add_nonneg
    (tangentRatioCellBoundaryFlow_nonneg
      lastCell residual bandOf cellIndex source target)
    (tangentRatioCellInternalFlow_nonneg
      lastCell residual bandOf cellIndex source target)

@[simp]
theorem tangentRatioCellEarthmoverFlow_self
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) (v : V) :
    tangentRatioCellEarthmoverFlow
      lastCell residual bandOf cellIndex v v = 0 := by
  simp [tangentRatioCellEarthmoverFlow]

theorem tangentRatioCellEarthmoverFlow_positive_endpoints_ne
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    {source target : V}
    (hflow : 0 < tangentRatioCellEarthmoverFlow
      lastCell residual bandOf cellIndex source target) :
    source ≠ target := by
  intro hst
  subst target
  rw [tangentRatioCellEarthmoverFlow_self] at hflow
  exact (lt_irrefl 0 hflow).elim

theorem tangentRatioCellEarthmoverFlow_respectsRatioCells
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat) :
    TangentFlowRespectsRatioCells bandOf cellIndex
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex) := by
  intro source target hflow
  have hboundaryNonneg := tangentRatioCellBoundaryFlow_nonneg
    lastCell residual bandOf cellIndex source target
  have hinternalNonneg := tangentRatioCellInternalFlow_nonneg
    lastCell residual bandOf cellIndex source target
  unfold tangentRatioCellEarthmoverFlow at hflow
  by_cases hboundary :
      0 < tangentRatioCellBoundaryFlow
        lastCell residual bandOf cellIndex source target
  · exact tangentRatioCellBoundaryFlow_respectsRatioCells
      lastCell residual bandOf cellIndex hboundary
  · have hinternal :
        0 < tangentRatioCellInternalFlow
          lastCell residual bandOf cellIndex source target := by
      have hboundaryZero :
          tangentRatioCellBoundaryFlow
            lastCell residual bandOf cellIndex source target = 0 :=
        le_antisymm (le_of_not_gt hboundary) hboundaryNonneg
      linarith
    exact tangentRatioCellInternalFlow_respectsRatioCells
      lastCell residual bandOf cellIndex hinternal

/-- The complete earthmover has divergence exactly the original residual. -/
theorem tangentRatioCellEarthmoverFlow_divergence_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
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
          lastCell residual bandOf cellIndex) v = residual v := by
  unfold tangentRatioCellEarthmoverFlow
  rw [tangentFlowDivergence_add,
    tangentRatioCellBoundaryFlow_divergence_eq
      lastCell residual bandOf cellIndex hindex hoccupied hbalance v,
    tangentRatioCellInternalFlow_divergence_eq
      lastCell residual bandOf cellIndex hindex hoccupied v]
  unfold tangentRatioCellInternalResidual
  ring

/-- The full incoming-plus-outgoing mass of the complete earthmover is the
sum of the boundary port load and `|q_p|`. -/
theorem tangentRatioCellEarthmoverFlow_incident_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
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
        lastCell residual bandOf cellIndex w v) =
      tangentRatioCellUniformPortLoad residual bandOf cellIndex v +
        |tangentRatioCellInternalResidual residual bandOf cellIndex v| := by
  unfold tangentRatioCellEarthmoverFlow
  rw [tangentVertexIncident_add,
    tangentRatioCellBoundaryFlow_incident_eq_portLoad
      lastCell residual bandOf cellIndex hindex hoccupied hbalance v,
    tangentRatioCellInternalFlow_incident_eq_abs
      lastCell residual bandOf cellIndex hindex hoccupied v]

/-- Pointwise endpoint ledger required by the collision census. -/
theorem tangentRatioCellEarthmoverFlow_incident_le
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
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
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  rw [tangentRatioCellEarthmoverFlow_incident_eq
      lastCell residual bandOf cellIndex hindex hoccupied hbalance v]
  simpa only [add_comm] using
    abs_internalResidual_add_portLoad_le residual bandOf cellIndex v

theorem sum_tangentVertexIncident_eq_two_traffic
    {V : Type*} [Fintype V] (flow : V -> V -> Real) :
    (∑ v : V,
        ((∑ w : V, flow v w) + ∑ w : V, flow w v)) =
      2 * tangentFlowTraffic flow := by
  unfold tangentFlowTraffic
  have hin :
      (∑ v : V, ∑ w : V, flow w v) =
        ∑ v : V, ∑ w : V, flow v w := by
    exact Finset.sum_comm
  rw [Finset.sum_add_distrib, hin]
  ring

/-- Globally, the uniform port loads count both endpoints of every cut. -/
theorem sum_tangentRatioCellUniformPortLoad_eq_two_cutTraffic
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    (∑ v : V,
        tangentRatioCellUniformPortLoad residual bandOf cellIndex v) =
      2 * tangentRatioCellCanonicalCutTraffic
        lastCell residual bandOf cellIndex := by
  calc
    (∑ v : V,
        tangentRatioCellUniformPortLoad residual bandOf cellIndex v) =
        ∑ v : V,
          ((∑ w : V, tangentRatioCellBoundaryFlow
              lastCell residual bandOf cellIndex v w) +
            ∑ w : V, tangentRatioCellBoundaryFlow
              lastCell residual bandOf cellIndex w v) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [tangentRatioCellBoundaryFlow_incident_eq_portLoad
        lastCell residual bandOf cellIndex hindex hoccupied hbalance v]
    _ = 2 * tangentFlowTraffic
          (tangentRatioCellBoundaryFlow
            lastCell residual bandOf cellIndex) :=
      sum_tangentVertexIncident_eq_two_traffic _
    _ = 2 * tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex := by
      rw [tangentRatioCellBoundaryFlow_traffic_eq
        lastCell residual bandOf cellIndex hoccupied]

/-- The cellwise `q` mass has the exact global bound forced by the boundary
ports. -/
theorem sum_abs_tangentRatioCellInternalResidual_le
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    (∑ v : V,
        |tangentRatioCellInternalResidual residual bandOf cellIndex v|) <=
      (∑ v : V, |residual v|) +
        2 * tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex := by
  have hpoint :
      (∑ v : V,
        (|tangentRatioCellInternalResidual residual bandOf cellIndex v| +
          tangentRatioCellUniformPortLoad residual bandOf cellIndex v)) <=
        ∑ v : V,
          (|residual v| +
            2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v) := by
    exact Finset.sum_le_sum (fun v _hv =>
      abs_internalResidual_add_portLoad_le residual bandOf cellIndex v)
  simp_rw [Finset.sum_add_distrib] at hpoint
  have hports := sum_tangentRatioCellUniformPortLoad_eq_two_cutTraffic
    lastCell residual bandOf cellIndex hindex hoccupied hbalance
  have htwice :
      (∑ v : V,
          2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v) =
        4 * tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex := by
    rw [← Finset.mul_sum, hports]
    ring
  rw [hports, htwice] at hpoint
  linarith

/-- Exact traffic before applying the `ell^1` estimate. -/
theorem tangentRatioCellEarthmoverFlow_traffic_eq
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    tangentFlowTraffic
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) =
      tangentRatioCellCanonicalCutTraffic
          lastCell residual bandOf cellIndex +
        (∑ v : V,
          |tangentRatioCellInternalResidual residual bandOf cellIndex v|) / 2 := by
  unfold tangentRatioCellEarthmoverFlow
  rw [tangentFlowTraffic_add,
    tangentRatioCellBoundaryFlow_traffic_eq
      lastCell residual bandOf cellIndex hoccupied,
    tangentRatioCellInternalFlow_traffic_eq
      lastCell residual bandOf cellIndex hindex hoccupied]

/-- The literal paper traffic ledger: half the original residual mass plus
twice the prefix-cut traffic. -/
theorem tangentRatioCellEarthmoverFlow_traffic_le
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
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
          lastCell residual bandOf cellIndex) := by
  rw [tangentRatioCellEarthmoverFlow_traffic_eq
      lastCell residual bandOf cellIndex hindex hoccupied]
  unfold tangentDistributedTotalTrafficLedger
  have hq := sum_abs_tangentRatioCellInternalResidual_le
    lastCell residual bandOf cellIndex hindex hoccupied hbalance
  linarith

/-! ## From full vertex incident mass to the positive-support census -/

theorem sum_union_le_add_sum_of_nonneg_real
    {E : Type*} [DecidableEq E] (s t : Finset E)
    (weight : E -> Real) (hweight : forall edge, 0 <= weight edge) :
    (∑ edge ∈ s ∪ t, weight edge) <=
      (∑ edge ∈ s, weight edge) + ∑ edge ∈ t, weight edge := by
  calc
    (∑ edge ∈ s ∪ t, weight edge) =
        ∑ edge ∈ s ∪ (t \ s), weight edge := by
      rw [Finset.union_sdiff_self_eq_union]
    _ = (∑ edge ∈ s, weight edge) +
          ∑ edge ∈ t \ s, weight edge := by
      rw [Finset.sum_union Finset.disjoint_sdiff]
    _ <= (∑ edge ∈ s, weight edge) +
          ∑ edge ∈ t, weight edge := by
      exact add_le_add (le_refl _)
        (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
          (fun edge _hedge _hnew => hweight edge))

theorem sum_source_filter_eq_outgoing
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (v : V) :
    (∑ edge ∈ (Finset.univ : Finset (V × V)).filter
        (fun edge => edge.1 = v), flow edge.1 edge.2) =
      ∑ w : V, flow v w := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  rw [Fintype.sum_eq_single v]
  · simp
  · intro source hsource
    simp [hsource]

theorem sum_target_filter_eq_incoming
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (v : V) :
    (∑ edge ∈ (Finset.univ : Finset (V × V)).filter
        (fun edge => edge.2 = v), flow edge.1 edge.2) =
      ∑ w : V, flow w v := by
  rw [Finset.sum_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro source _hsource
  rw [Fintype.sum_eq_single v]
  · simp
  · intro target htarget
    simp [htarget]

/-- A positive-support edge is counted only once by
`tangentIncidentFlowMass`, whereas the full row-plus-column expression may
count a loop twice.  Nonnegativity therefore gives this useful inequality
without needing a no-loop hypothesis. -/
theorem tangentIncidentPositiveFlowMass_le_vertexIncident
    {V : Type*} [Fintype V] [DecidableEq V]
    (flow : V -> V -> Real) (hflow : forall source target,
      0 <= flow source target)
    (label : V -> Nat) (hlabel : Function.Injective label) (v : V) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => flow edge.1 edge.2) (label v) <=
      (∑ w : V, flow v w) + ∑ w : V, flow w v := by
  classical
  let sourceEdges : Finset (V × V) :=
    (Finset.univ : Finset (V × V)).filter (fun edge => edge.1 = v)
  let targetEdges : Finset (V × V) :=
    (Finset.univ : Finset (V × V)).filter (fun edge => edge.2 = v)
  let allIncident : Finset (V × V) := sourceEdges ∪ targetEdges
  have hsubset :
      tangentIncidentEdges
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
          (label v) ⊆ allIncident := by
    intro edge hedge
    have hdata := Finset.mem_filter.mp hedge
    have hlabels := hdata.2
    unfold tangentStarEdgeSource tangentStarEdgeTarget at hlabels
    unfold allIncident sourceEdges targetEdges
    rw [Finset.mem_union]
    rcases hlabels with hsource | htarget
    · exact Or.inl (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlabel hsource⟩)
    · exact Or.inr (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hlabel htarget⟩)
  calc
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => flow edge.1 edge.2) (label v) <=
        ∑ edge ∈ allIncident, flow edge.1 edge.2 := by
      unfold tangentIncidentFlowMass
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun edge _hedge _hnew => hflow edge.1 edge.2)
    _ <= (∑ edge ∈ sourceEdges, flow edge.1 edge.2) +
          ∑ edge ∈ targetEdges, flow edge.1 edge.2 := by
      exact sum_union_le_add_sum_of_nonneg_real
        sourceEdges targetEdges (fun edge => flow edge.1 edge.2)
          (fun edge => hflow edge.1 edge.2)
    _ = (∑ w : V, flow v w) + ∑ w : V, flow w v := by
      rw [show sourceEdges =
          (Finset.univ : Finset (V × V)).filter
            (fun edge => edge.1 = v) by rfl,
        show targetEdges =
          (Finset.univ : Finset (V × V)).filter
            (fun edge => edge.2 = v) by rfl,
        sum_source_filter_eq_outgoing, sum_target_filter_eq_incoming]

/-- The pointwise ledger in exactly the positive-support form consumed by
`TangentDistributedFlowCensus`. -/
theorem tangentRatioCellEarthmoverFlow_positiveIncident_le
    {V Band : Type*} [Fintype V] [DecidableEq V]
    [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0)
    (label : V -> Nat) (hlabel : Function.Injective label) (v : V) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex))
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex edge.1 edge.2) (label v) <=
      |residual v| +
        2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  calc
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex))
        (tangentStarEdgeSource label) (tangentStarEdgeTarget label)
        (fun edge : V × V => tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex edge.1 edge.2) (label v) <=
        (∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex v w) +
          ∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex w v :=
      tangentIncidentPositiveFlowMass_le_vertexIncident
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex)
        (tangentRatioCellEarthmoverFlow_nonneg
          lastCell residual bandOf cellIndex) label hlabel v
    _ <= |residual v| +
          2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v :=
      tangentRatioCellEarthmoverFlow_incident_le
        lastCell residual bandOf cellIndex hindex hoccupied hbalance v

/-- Fixed-ratio geometry turns the proved cell support into the literal
edge-locality inequality. -/
theorem tangentRatioCellEarthmoverFlow_positiveEdge_locality
    {V Band : Type*} [Fintype V] [DecidableEq V]
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
      ((min (label edge.1) (label edge.2) : Nat) : Real)) <= ratioUpper := by
  simpa only [tangentStarEdgeSource, tangentStarEdgeTarget] using
    tangentPositiveEdge_locality_of_ratioCells
      label bandOf cellIndex
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex) ratioUpper
      (tangentRatioCellEarthmoverFlow_respectsRatioCells
        lastCell residual bandOf cellIndex) hgeometry hedge

/-- One theorem exposing the five construction outputs.  These facts are
kept as theorem conclusions about the visible flow formula, rather than as
fields of a certificate. -/
theorem tangentRatioCellEarthmoverFlow_spec
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (hindex : forall v, cellIndex v <= lastCell (bandOf v))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hbalance : forall band,
      (∑ v : V, if bandOf v = band then residual v else 0) = 0) :
    (forall source target,
      0 <= tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex source target) ∧
      (forall v,
        tangentFlowDivergence
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex) v = residual v) ∧
      TangentFlowRespectsRatioCells bandOf cellIndex
        (tangentRatioCellEarthmoverFlow
          lastCell residual bandOf cellIndex) ∧
      tangentFlowTraffic
          (tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex) <=
        tangentDistributedTotalTrafficLedger residual
          (tangentRatioCellCanonicalCutTraffic
            lastCell residual bandOf cellIndex) ∧
      forall v,
        (∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex v w) +
          (∑ w : V, tangentRatioCellEarthmoverFlow
            lastCell residual bandOf cellIndex w v) <=
        |residual v| +
          2 * tangentRatioCellUniformPortLoad residual bandOf cellIndex v := by
  exact ⟨tangentRatioCellEarthmoverFlow_nonneg
      lastCell residual bandOf cellIndex,
    tangentRatioCellEarthmoverFlow_divergence_eq
      lastCell residual bandOf cellIndex hindex hoccupied hbalance,
    tangentRatioCellEarthmoverFlow_respectsRatioCells
      lastCell residual bandOf cellIndex,
    tangentRatioCellEarthmoverFlow_traffic_le
      lastCell residual bandOf cellIndex hindex hoccupied hbalance,
    tangentRatioCellEarthmoverFlow_incident_le
      lastCell residual bandOf cellIndex hindex hoccupied hbalance⟩

/-- Prefix bounds from the rounded selector immediately bound the visible
canonical cut ledger. -/
theorem tangentRatioCellCanonicalCutTraffic_le_prefixUpper
    {V Band : Type*} [Fintype V] [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat) (residual : V -> Real)
    (bandOf : V -> Band) (cellIndex : V -> Nat)
    (prefixUpper : Band -> Nat -> Real)
    (hprefix : forall band cut,
      |tangentRatioCellPrefixMass residual bandOf cellIndex band cut| <=
        prefixUpper band cut) :
    tangentRatioCellCanonicalCutTraffic
        lastCell residual bandOf cellIndex <=
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        prefixUpper band cut := by
  unfold tangentRatioCellCanonicalCutTraffic
  exact Finset.sum_le_sum fun band _hband =>
    Finset.sum_le_sum fun cut _hcut => hprefix band cut

end

end Erdos390.WholePaper
