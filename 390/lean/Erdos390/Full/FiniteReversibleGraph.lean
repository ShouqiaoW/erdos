import Erdos390.Full.FiniteGraphQuotientInverse

/-!
# Reversible finite graph rows

The continuum cell graph used in the moving-low argument is reversible for
its harmonic-centre weight.  This file records the finite algebra needed to
turn detailed balance into the exact statement that projection to the gauge
does not change the graph row.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteReversibleGraph

open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

/-- Detailed balance makes the weighted integral of a graph Laplacian
vanish.  No symmetry of `edge` itself is required. -/
theorem weighted_sum_graphOperator_eq_zero
    (edge : Band → Band → ℝ) (omega q : Band → ℝ)
    (hbalance : ∀ i j, omega i * edge i j = omega j * edge j i) :
    ∑ i, omega i * graphOperator edge q i = 0 := by
  classical
  unfold graphOperator
  have hswap :
      (∑ i, ∑ j, omega i * edge i j * q j) =
        ∑ i, ∑ j, omega i * edge i j * q i := by
    calc
      (∑ i, ∑ j, omega i * edge i j * q j) =
          ∑ j, ∑ i, omega i * edge i j * q j := Finset.sum_comm
      _ = ∑ j, ∑ i, omega j * edge j i * q j := by
        apply Finset.sum_congr rfl
        intro j _hj
        apply Finset.sum_congr rfl
        intro i _hi
        rw [hbalance]
      _ = ∑ i, ∑ j, omega i * edge i j * q i := by
        rfl
  calc
    (∑ i, omega i * ∑ j, edge i j * (q i - q j)) =
        (∑ i, ∑ j, omega i * edge i j * q i) -
          ∑ i, ∑ j, omega i * edge i j * q j := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = 0 := sub_eq_zero.mpr hswap.symm

/-- On a reversible graph the weighted mean of the graph row is exactly
zero. -/
theorem weightedMean_graphOperator_eq_zero
    (edge : Band → Band → ℝ) (omega q : Band → ℝ)
    (hbalance : ∀ i j, omega i * edge i j = omega j * edge j i) :
    weightedMean omega (graphOperator edge q) = 0 := by
  unfold weightedMean weightTotal
  rw [weighted_sum_graphOperator_eq_zero edge omega q hbalance]
  exact zero_div _

/-- Consequently the gauge projection fixes every graph row. -/
theorem meanProjection_graphOperator_eq
    (edge : Band → Band → ℝ) (omega q : Band → ℝ)
    (hbalance : ∀ i j, omega i * edge i j = omega j * edge j i) :
    meanProjection omega (graphOperator edge q) = graphOperator edge q := by
  funext i
  unfold meanProjection
  rw [weightedMean_graphOperator_eq_zero edge omega q hbalance]
  exact sub_zero _

end Erdos390.Full.FiniteReversibleGraph
