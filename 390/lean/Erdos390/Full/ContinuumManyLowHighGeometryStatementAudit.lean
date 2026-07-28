import Erdos390.Full.ContinuumManyLowHighGeometry

/-!
Independent statement audit for the two estimates in which uniformity in the
number and least endpoint of the moving low cells is essential.  These
wrappers deliberately restate all hypotheses and conclusions rather than
merely checking a theorem name.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumManyLowHighGeometryStatementAudit

open ConditionedPoissonLimit
open ContinuumCellGraph

variable {Band Low High : Type*}
  [Fintype Band] [Fintype Low]
variable {epsilon : ℝ}

theorem productKernel_crossRow_uniform_in_low_mesh
    (M : ContinuumCellGraph.IntervalMesh epsilon Band)
    (e : Sum Low High ≃ Band)
    {C lowCenter lowLength amin B lowBudget : ℝ}
    (hC : 0 ≤ C) (hLowCenterNonneg : 0 ≤ lowCenter)
    (hBNonneg : 0 ≤ B) (hLowBudgetNonneg : 0 ≤ lowBudget)
    (hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤ C * M.center i * M.length j)
    (hLowCenter : ∀ l : Low, M.center (e (.inl l)) ≤ lowCenter)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (hAmin : 0 < amin)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (q : Sum Low High → ℝ)
    (hB : ∀ x, |M.center (e x) * q x| ≤ B)
    (hLowBudget : ∀ l : Low,
      |M.center (e (.inl l)) * q (.inl l)| ≤ lowBudget)
    (i : High) :
    |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
        (q (.inr i) - q (.inl l))| ≤
      (C * lowCenter * lowLength) * B / amin +
        (C * lowLength) * lowBudget := by
  exact M.abs_splitSharpEdge_cross_low_le e hC hLowCenterNonneg
    hBNonneg hLowBudgetNonneg hCell hLowCenter hLowLength hAmin
    hHighCenter q hB hLowBudget i

theorem exactGauge_lowContribution_uniform_in_low_mesh
    [DecidableEq Band] [Fintype High]
    (M : ContinuumCellGraph.IntervalMesh epsilon Band)
    (e : Sum Low High ≃ Band)
    {amin anchorFloor lowLength gaugeRatio lowBudget : ℝ}
    (hAmin : 0 < amin)
    (hGaugeRatio : 0 ≤ gaugeRatio) (hLowBudgetNonneg : 0 ≤ lowBudget)
    (hHighCenter : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (hAnchor : anchorFloor ≤
      ∑ i : High, M.splitHighAnchor e i)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (hRatio : lowLength ≤ gaugeRatio * (amin * anchorFloor))
    (q : Sum Low High → ℝ)
    (hLowBudget : ∀ l : Low,
      |M.center (e (.inl l)) * q (.inl l)| ≤ lowBudget) :
    |∑ l : Low, M.splitSharpWeight e (.inl l) * q (.inl l)| ≤
      gaugeRatio * (∑ i : High, M.splitSharpWeight e (.inr i)) *
        lowBudget := by
  exact M.abs_lowSharpGaugeSum_le e hAmin hGaugeRatio
    hLowBudgetNonneg hHighCenter hAnchor hLowLength hRatio q hLowBudget

end Erdos390.Full.ContinuumManyLowHighGeometryStatementAudit
