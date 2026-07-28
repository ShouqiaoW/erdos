import Erdos390.Full.PaperPermittedRegularMesh

/-! Independent expansion of the paper/actual mesh-scale comparison. -/

namespace Erdos390.Full.PaperPermittedRegularMeshStatementAudit

open Erdos390.Full.RegularRelativeMesh

example {delta eta cMesh V K : ℝ} (M : Mesh delta eta)
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh)
    (hregular : cMesh * eta ≤ M.ratio)
    (hV : (delta + M.ratio) ^ 2 ≤ K * V) :
    (delta + eta) ^ 2 ≤ (K / cMesh ^ 2) * V := by
  exact
    PaperPermittedRegularMesh.IsPermitted.paperScale_sq_le_of_actualScale_sq_le_of_pos
      hdelta hc hregular hV

example {delta eta cMesh V : ℝ} (M : Mesh delta eta)
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh)
    (hregular : cMesh * eta ≤ M.ratio)
    (hlow : delta ^ 2 / 4 ≤ V)
    (hpositive : M.ratio ^ 2 / 224 ≤ V) :
    (delta + eta) ^ 2 ≤ (456 / cMesh ^ 2) * V := by
  exact
    PaperPermittedRegularMesh.IsPermitted.paperScale_sq_le_of_low_and_positive
      hdelta hc hregular hlow hpositive

end Erdos390.Full.PaperPermittedRegularMeshStatementAudit
