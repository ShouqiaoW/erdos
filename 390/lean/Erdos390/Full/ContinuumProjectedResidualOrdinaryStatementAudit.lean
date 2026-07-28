import Erdos390.Full.ContinuumProjectedResidualOrdinary

/-! Expanded audit of the projected-to-unprojected ordinary row transfer. -/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.ContinuumProjectedResidualOrdinaryStatementAudit

open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ}

theorem projected_row_controls_unprojected_row_without_least_center
    (M : IntervalMesh epsilon Band)
    {rho R B G : ℝ}
    (hRho : 0 ≤ rho) (hB : 0 ≤ B)
    (hTotal : 0 < ∑ j : Band, M.continuumSharpWeight j)
    (hMomentRatio : ∀ i : Band,
      M.center i * (∑ j : Band, M.continuumFirstWeight j) ≤
        R * (∑ j : Band, M.continuumSharpWeight j))
    (q : Band → ℝ)
    (hResidual : ∀ j : Band, |M.rowResidual j| ≤ rho)
    (hPoint : ∀ j : Band, |M.center j * q j| ≤ B)
    (hProjected : ∀ i : Band,
      |M.center i * meanProjection M.continuumSharpWeight
        (M.continuumSharpOperator q) i| ≤ G) :
    (∀ i : Band,
      |M.center i * graphOperator M.sharpKernelEdge q i| ≤
        G + rho * (1 + R) * B) ∧
    (∀ i : Band,
      |M.center i * M.continuumSharpOperator q i| ≤
        G + rho * R * B) := by
  constructor
  · intro i
    exact M.abs_center_mul_graph_le_of_projectedContinuum hRho hB
      hTotal hMomentRatio q hResidual hPoint hProjected i
  · intro i
    exact M.abs_center_mul_continuumSharp_le_of_projected hRho hB
      hTotal hMomentRatio q hResidual hPoint hProjected i

end Erdos390.Full.ContinuumProjectedResidualOrdinaryStatementAudit
