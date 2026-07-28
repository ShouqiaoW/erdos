import Erdos390.Full.RegularRelativeMeshInteriorAnchors

/-! Independent expanded statement audit for the fixed-mass anchor block. -/

open scoped BigOperators

namespace Erdos390.Full.RegularRelativeMeshInteriorAnchorsStatementAudit

open Erdos390.Full.RegularRelativeMesh

noncomputable section

example {delta eta : ℝ} (M : Mesh delta eta)
    (hdelta : 0 < delta) (hdeltaSmall : delta < 1 / 16)
    (hwidth : ∀ k : Fin M.cellCount, M.width k < (1 / 16 : ℝ)) :
    ∃ anchors : Finset (Fin M.cellCount), ∃ anchor : Fin M.cellCount,
      anchor ∈ anchors ∧
      (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) ∧
      (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) ∧
      (1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2 := by
  exact M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidth

end

end Erdos390.Full.RegularRelativeMeshInteriorAnchorsStatementAudit
