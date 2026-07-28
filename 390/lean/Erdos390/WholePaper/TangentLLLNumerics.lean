import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Numerical bookkeeping for the tangent-stage local lemma

The collision argument uses only one deterministic product estimate before
the asymmetric Lovasz local lemma is invoked.  For numbers in the unit
interval, the product of their complements is at least one minus their sum.
Consequently, if the doubled probability mass in every dependency
neighborhood is at most one half, the choice `x_E = 2 * P(E)` satisfies the
entire numerical inequality required by the asymmetric local lemma.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Finite union-bound product inequality in the precise orientation used by
the asymmetric local lemma. -/
theorem one_sub_sum_le_prod_one_sub
    {I : Type*} (s : Finset I) (x : I → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have hxa := hx a (Finset.mem_insert_self a s)
      have hxs : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1 := by
        intro i hi
        exact hx i (Finset.mem_insert_of_mem hi)
      have hsumNonneg : 0 ≤ ∑ i ∈ s, x i := by
        exact Finset.sum_nonneg fun i hi ↦ (hxs i hi).1
      have hbase :
          1 - (x a + ∑ i ∈ s, x i) ≤
            (1 - x a) * (1 - ∑ i ∈ s, x i) := by
        nlinarith
      have hmul :
          (1 - x a) * (1 - ∑ i ∈ s, x i) ≤
            (1 - x a) * ∏ i ∈ s, (1 - x i) :=
        mul_le_mul_of_nonneg_left (ih hxs) (sub_nonneg.mpr hxa.2)
      simpa only [Finset.sum_insert ha, Finset.prod_insert ha] using
        hbase.trans hmul

/-- If a finite family of nonnegative numbers has sum at most one half,
then the product of their doubled complements is at least one half. -/
theorem half_le_prod_one_sub_two_mul
    {I : Type*} [DecidableEq I]
    (s : Finset I) (probability : I → ℝ)
    (hprobability : ∀ i ∈ s, 0 ≤ probability i)
    (hmass : ∑ i ∈ s, 2 * probability i ≤ 1 / 2) :
    1 / 2 ≤ ∏ i ∈ s, (1 - 2 * probability i) := by
  have hterm : ∀ i ∈ s, 0 ≤ 2 * probability i ∧
      2 * probability i ≤ 1 := by
    intro i hi
    have hnonneg : 0 ≤ 2 * probability i := by
      exact mul_nonneg (by norm_num) (hprobability i hi)
    have hleSum : 2 * probability i ≤
        ∑ j ∈ s, 2 * probability j := by
      exact Finset.single_le_sum
        (fun j hj ↦ mul_nonneg (by norm_num) (hprobability j hj)) hi
    exact ⟨hnonneg, hleSum.trans (hmass.trans (by norm_num))⟩
  have hprod := one_sub_sum_le_prod_one_sub s
    (fun i ↦ 2 * probability i) hterm
  linarith

/-- The factor-two/factor-four bookkeeping used in the paper: neighborhood
mass at most `1/8` gives doubled `x`-mass at most `1/2`, and hence the
asymmetric-LLL inequality for the distinguished event. -/
theorem probability_le_two_mul_probability_mul_neighborProduct
    {I : Type*} [DecidableEq I]
    (neighbors : Finset I) (probability : I → ℝ)
    (event : I)
    (hprobability : ∀ i ∈ insert event neighbors,
      0 ≤ probability i)
    (hneighborhood : ∑ i ∈ neighbors, probability i ≤ 1 / 4) :
    probability event ≤
      (2 * probability event) *
        ∏ i ∈ neighbors, (1 - 2 * probability i) := by
  have hneighborNonneg : ∀ i ∈ neighbors, 0 ≤ probability i := by
    intro i hi
    exact hprobability i (Finset.mem_insert_of_mem hi)
  have hdoubleMass : ∑ i ∈ neighbors, 2 * probability i ≤ 1 / 2 := by
    rw [← Finset.mul_sum]
    nlinarith
  have hprod := half_le_prod_one_sub_two_mul neighbors probability
    hneighborNonneg hdoubleMass
  have heventNonneg : 0 ≤ probability event :=
    hprobability event (Finset.mem_insert_self event neighbors)
  nlinarith [mul_le_mul_of_nonneg_left hprod
    (show 0 ≤ 2 * probability event by positivity)]

/-- Paper-facing form.  A per-request collision sum at most `1/8` bounds a
bad event's dependency-neighborhood probability mass by `1/4`, so the
previous theorem applies verbatim. -/
theorem probability_le_two_mul_probability_mul_neighborProduct_of_requestMass
    {I : Type*} [DecidableEq I]
    (neighbors : Finset I) (probability : I → ℝ)
    (event : I)
    (hprobability : ∀ i ∈ insert event neighbors,
      0 ≤ probability i)
    (requestMass : ℝ)
    (hrequestMass : requestMass ≤ 1 / 8)
    (hneighborhood : ∑ i ∈ neighbors, probability i ≤
      2 * requestMass) :
    probability event ≤
      (2 * probability event) *
        ∏ i ∈ neighbors, (1 - 2 * probability i) := by
  apply probability_le_two_mul_probability_mul_neighborProduct
    neighbors probability event hprobability
  nlinarith

end

end Erdos390.WholePaper
