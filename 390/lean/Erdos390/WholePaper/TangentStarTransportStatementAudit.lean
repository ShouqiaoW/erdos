import Erdos390.WholePaper.TangentStarTransport

/-! # Expanded statement audit for exact finite star transport -/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (pivot : V) (residual : V → ℝ) (source target : V) :
    0 ≤ tangentStarFlow pivot residual source target :=
  tangentStarFlow_nonneg pivot residual source target

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (pivot : V) (residual : V → ℝ) (v : V) :
    tangentStarFlow pivot residual v v = 0 :=
  tangentStarFlow_self pivot residual v

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {pivot source target : V} {residual : V → ℝ}
    (hflow : 0 < tangentStarFlow pivot residual source target) :
    (source = pivot ∧ target ≠ pivot) ∨
      (source ≠ pivot ∧ target = pivot) :=
  tangentStarFlow_pos_incident_pivot hflow

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0) (v : V) :
    tangentFlowDivergence (tangentStarFlow pivot residual) v =
      residual v :=
  tangentStarFlow_divergence_eq hsum v

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (pivot : V) (residual : V → ℝ) :
    tangentFlowTraffic (tangentStarFlow pivot residual) =
      ∑ v ∈ (Finset.univ : Finset V).erase pivot, |residual v| :=
  tangentStarFlow_traffic_eq_sum_erase_abs pivot residual

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (pivot : V) (residual : V → ℝ) :
    tangentFlowTraffic (tangentStarFlow pivot residual) ≤
      ∑ v : V, |residual v| :=
  tangentStarFlow_traffic_le_sum_abs pivot residual

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0) (value : V → ℝ) :
    (∑ edge : V × V,
        tangentStarFlow pivot residual edge.1 edge.2 *
          (value edge.1 - value edge.2)) =
      ∑ v : V, residual v * value v :=
  tangentStarFlow_pairBoundary_eq_residual hsum value

example {V P : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0)
    (coordinate : V → P → ℝ) :
    ∀ p : P,
      (∑ edge : V × V,
          tangentStarFlow pivot residual edge.1 edge.2 *
            (coordinate edge.1 p - coordinate edge.2 p)) =
        ∑ v : V, residual v * coordinate v p :=
  tangentStarFlow_residualVector hsum coordinate

example {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    {pivot : V} {residual : V → ℝ}
    (hsum : (∑ v : V, residual v) = 0)
    (label : V → ℕ) (p : ℕ) :
    (∑ edge : V × V,
        tangentStarFlow pivot residual edge.1 edge.2 *
          (((label edge.1).factorization p : ℝ) -
            ((label edge.2).factorization p : ℝ))) =
      ∑ v : V, residual v * (label v).factorization p :=
  tangentStarFlow_factorizationBoundary_eq_residual hsum label p

end

end Erdos390.WholePaper
