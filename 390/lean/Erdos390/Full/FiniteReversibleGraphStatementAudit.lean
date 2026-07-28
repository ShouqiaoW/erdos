import Erdos390.Full.FiniteReversibleGraph

open scoped BigOperators

namespace Erdos390.Full.FiniteReversibleGraphStatementAudit

open Erdos390.Full.FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

example (edge : Band → Band → ℝ) (omega q : Band → ℝ)
    (hbalance : ∀ i j, omega i * edge i j = omega j * edge j i) :
    ∑ i, omega i * graphOperator edge q i = 0 := by
  exact Erdos390.Full.FiniteReversibleGraph.weighted_sum_graphOperator_eq_zero
    edge omega q hbalance

end Erdos390.Full.FiniteReversibleGraphStatementAudit
