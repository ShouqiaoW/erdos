import Erdos390.WholePaper.TangentStarTransport

/-!
# Canonical balanced product transport

For a finite signed residual of total mass zero, this file gives the
explicit dense transport

`max (q u) 0 * max (-q v) 0 / sum_w max (q w) 0`.

Thus every positive coordinate sends its mass proportionally to all
negative coordinates.  The construction is nonnegative, has no loops,
has divergence exactly `q`, total traffic exactly half the `ell^1` mass,
and incident traffic at `v` exactly `|q v|`.  The last identity is why this
construction is used inside a ratio cell: a star or a deterministic chain
would concentrate the internal traffic at a pivot and would not give the
paper's pointwise endpoint ledger.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Total positive mass of a finite signed vector. -/
def tangentPositiveMass {V : Type*} [Fintype V]
    (q : V -> Real) : Real :=
  ∑ v : V, max (q v) 0

/-- Total absolute value of the negative mass of a finite signed vector. -/
def tangentNegativeMass {V : Type*} [Fintype V]
    (q : V -> Real) : Real :=
  ∑ v : V, max (-q v) 0

/-- The canonical proportional matching of the positive and negative
parts.  Division by zero is harmless: in that case the formula is zero. -/
def tangentBalancedProductFlow {V : Type*} [Fintype V]
    (q : V -> Real) (source target : V) : Real :=
  max (q source) 0 * max (-q target) 0 / tangentPositiveMass q

theorem tangentPositiveMass_nonneg
    {V : Type*} [Fintype V] (q : V -> Real) :
    0 <= tangentPositiveMass q := by
  unfold tangentPositiveMass
  exact Finset.sum_nonneg fun v _hv => le_max_right (q v) 0

theorem tangentNegativeMass_nonneg
    {V : Type*} [Fintype V] (q : V -> Real) :
    0 <= tangentNegativeMass q := by
  unfold tangentNegativeMass
  exact Finset.sum_nonneg fun v _hv => le_max_right (-q v) 0

/-- Zero total signed mass is equivalent to equality of the two Jordan
masses. -/
theorem tangentPositiveMass_eq_negativeMass
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) :
    tangentPositiveMass q = tangentNegativeMass q := by
  have hdiff :
      tangentPositiveMass q - tangentNegativeMass q =
        ∑ v : V, q v := by
    unfold tangentPositiveMass tangentNegativeMass
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro v _hv
    exact max_zero_sub_max_neg_zero_eq_self (q v)
  linarith

/-- The two Jordan masses add to the `ell^1` mass. -/
theorem tangentPositiveMass_add_negativeMass
    {V : Type*} [Fintype V] (q : V -> Real) :
    tangentPositiveMass q + tangentNegativeMass q =
      ∑ v : V, |q v| := by
  unfold tangentPositiveMass tangentNegativeMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _hv
  exact max_zero_add_max_neg_zero_eq_abs_self (q v)

theorem tangentBalancedProductFlow_nonneg
    {V : Type*} [Fintype V] (q : V -> Real)
    (source target : V) :
    0 <= tangentBalancedProductFlow q source target := by
  unfold tangentBalancedProductFlow
  exact div_nonneg
    (mul_nonneg (le_max_right (q source) 0)
      (le_max_right (-q target) 0))
    (tangentPositiveMass_nonneg q)

/-- The product formula is total at zero mass. -/
theorem tangentBalancedProductFlow_eq_zero_of_positiveMass_eq_zero
    {V : Type*} [Fintype V] (q : V -> Real)
    (hmass : tangentPositiveMass q = 0) (source target : V) :
    tangentBalancedProductFlow q source target = 0 := by
  simp [tangentBalancedProductFlow, hmass]

@[simp]
theorem tangentBalancedProductFlow_self
    {V : Type*} [Fintype V] (q : V -> Real) (v : V) :
    tangentBalancedProductFlow q v v = 0 := by
  by_cases hq : 0 <= q v
  · have hneg : -q v <= 0 := neg_nonpos.mpr hq
    simp [tangentBalancedProductFlow, max_eq_left hq,
      max_eq_right hneg]
  · have hq' : q v <= 0 := le_of_not_ge hq
    have hneg : 0 <= -q v := neg_nonneg.mpr hq'
    simp [tangentBalancedProductFlow, max_eq_right hq',
      max_eq_left hneg]

/-- If the common positive mass vanishes, every coordinate of a balanced
signed vector vanishes. -/
theorem tangentBalanced_eq_zero_of_positiveMass_eq_zero
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0)
    (hmass : tangentPositiveMass q = 0) :
    forall v, q v = 0 := by
  have hnegative : tangentNegativeMass q = 0 := by
    rw [← tangentPositiveMass_eq_negativeMass q hsum]
    exact hmass
  have hpositiveZero : (fun v ↦ max (q v) 0) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun w ↦ le_max_right (q w) 0)).mp hmass
  have hnegativeZero : (fun v ↦ max (-q v) 0) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun w ↦ le_max_right (-q w) 0)).mp hnegative
  have hpositivePoint : forall v, max (q v) 0 = 0 := by
    intro v
    exact congrFun hpositiveZero v
  have hnegativePoint : forall v, max (-q v) 0 = 0 := by
    intro v
    exact congrFun hnegativeZero v
  intro v
  have hparts := max_zero_sub_max_neg_zero_eq_self (q v)
  simpa only [hpositivePoint v, hnegativePoint v, sub_zero] using hparts.symm

/-- A row of the proportional matching is exactly the positive part of its
source coordinate. -/
theorem sum_tangentBalancedProductFlow_out
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0)
    (hmass : tangentPositiveMass q ≠ 0) (source : V) :
    (∑ target : V, tangentBalancedProductFlow q source target) =
      max (q source) 0 := by
  unfold tangentBalancedProductFlow
  rw [← Finset.sum_div, ← Finset.mul_sum]
  change max (q source) 0 * tangentNegativeMass q /
      tangentPositiveMass q = max (q source) 0
  rw [← tangentPositiveMass_eq_negativeMass q hsum]
  field_simp [hmass]

/-- A column of the proportional matching is exactly the negative part of
its target coordinate. -/
theorem sum_tangentBalancedProductFlow_in
    {V : Type*} [Fintype V] (q : V -> Real)
    (hmass : tangentPositiveMass q ≠ 0) (target : V) :
    (∑ source : V, tangentBalancedProductFlow q source target) =
      max (-q target) 0 := by
  unfold tangentBalancedProductFlow
  rw [← Finset.sum_div, ← Finset.sum_mul]
  change tangentPositiveMass q * max (-q target) 0 /
      tangentPositiveMass q = max (-q target) 0
  field_simp [hmass]

/-- The explicit proportional matching has the requested divergence. -/
theorem tangentBalancedProductFlow_divergence_eq
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) (v : V) :
    tangentFlowDivergence (tangentBalancedProductFlow q) v = q v := by
  by_cases hmass : tangentPositiveMass q = 0
  · have hq := tangentBalanced_eq_zero_of_positiveMass_eq_zero
      q hsum hmass
    simp [tangentFlowDivergence, tangentBalancedProductFlow,
      hmass, hq v]
  · rw [tangentFlowDivergence,
      sum_tangentBalancedProductFlow_out q hsum hmass v,
      sum_tangentBalancedProductFlow_in q hmass v]
    exact max_zero_sub_max_neg_zero_eq_self (q v)

/-- Total traffic is the common positive/negative mass. -/
theorem tangentBalancedProductFlow_traffic_eq_positiveMass
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) :
    tangentFlowTraffic (tangentBalancedProductFlow q) =
      tangentPositiveMass q := by
  by_cases hmass : tangentPositiveMass q = 0
  · simp [tangentFlowTraffic, tangentBalancedProductFlow, hmass]
  · unfold tangentFlowTraffic
    simp_rw [sum_tangentBalancedProductFlow_out q hsum hmass]
    exact rfl

/-- Hence total traffic is exactly half the `ell^1` residual mass. -/
theorem tangentBalancedProductFlow_traffic_eq_half_sum_abs
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) :
    tangentFlowTraffic (tangentBalancedProductFlow q) =
      (∑ v : V, |q v|) / 2 := by
  rw [tangentBalancedProductFlow_traffic_eq_positiveMass q hsum]
  have hmass := tangentPositiveMass_eq_negativeMass q hsum
  have habs := tangentPositiveMass_add_negativeMass q
  linarith

/-- Full incoming plus outgoing traffic at a vertex is exactly the absolute
value of its signed residual. -/
theorem tangentBalancedProductFlow_incident_eq_abs
    {V : Type*} [Fintype V] (q : V -> Real)
    (hsum : (∑ v : V, q v) = 0) (v : V) :
    (∑ w : V, tangentBalancedProductFlow q v w) +
        (∑ w : V, tangentBalancedProductFlow q w v) = |q v| := by
  by_cases hmass : tangentPositiveMass q = 0
  · have hq := tangentBalanced_eq_zero_of_positiveMass_eq_zero
      q hsum hmass
    simp [tangentBalancedProductFlow, hmass, hq v]
  · rw [sum_tangentBalancedProductFlow_out q hsum hmass v,
      sum_tangentBalancedProductFlow_in q hmass v]
    exact max_zero_add_max_neg_zero_eq_abs_self (q v)

/-- Every positive transport edge has distinct endpoints. -/
theorem tangentBalancedProductFlow_positive_endpoints_ne
    {V : Type*} [Fintype V] (q : V -> Real)
    {source target : V}
    (hflow : 0 < tangentBalancedProductFlow q source target) :
    source ≠ target := by
  intro hst
  subst target
  rw [tangentBalancedProductFlow_self] at hflow
  exact (lt_irrefl 0 hflow).elim

end

end Erdos390.WholePaper
