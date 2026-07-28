import Erdos390.Full.ContinuumCellGraphReversible

namespace Erdos390.Full.ContinuumCellGraphReversibleStatementAudit

open Erdos390.Full.ContinuumCellGraph

variable {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

example (i j : Band) :
    (M.harmonicMass i * M.center i ^ 2) * M.sharpKernelEdge i j =
      (M.harmonicMass j * M.center j ^ 2) * M.sharpKernelEdge j i := by
  exact M.sharpKernelEdge_detailedBalance i j

end Erdos390.Full.ContinuumCellGraphReversibleStatementAudit
