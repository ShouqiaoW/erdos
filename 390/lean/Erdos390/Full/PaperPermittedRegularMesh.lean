import Erdos390.Full.RegularMeshMomentBounds

/-!
# The paper's two-sided relative-mesh condition

`RegularRelativeMesh.Mesh delta eta` records an exact common relative width
`M.ratio` and the upper estimate `M.ratio ≤ eta`.  The permitted meshes in
Section 8.4 of the paper also satisfy the lower estimate

`cMesh * eta ≤ M.ratio`.

Keeping that second estimate as a named proposition prevents an arbitrary
upper-width parameter from being confused with the actual mesh scale.  The
elementary lemmas below convert estimates at the actual scale
`delta + M.ratio` to the paper scale `delta + eta`, with constants depending
only on the fixed structural regularity constant `cMesh`.
-/

namespace Erdos390.Full.PaperPermittedRegularMesh

open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-- The lower half of the paper's two-sided relative regularity condition.
The upper half is already the field `M.ratio_le_eta`. -/
def IsPermitted {delta eta cMesh : ℝ} (M : Mesh delta eta) : Prop :=
  cMesh * eta ≤ M.ratio

namespace IsPermitted

variable {delta eta cMesh : ℝ} {M : Mesh delta eta}

theorem eta_pos (M : Mesh delta eta) : 0 < eta :=
  lt_of_lt_of_le M.ratio_pos M.ratio_le_eta

theorem eta_le_ratio_div
    (hc : 0 < cMesh) (h : IsPermitted (cMesh := cMesh) M) :
    eta ≤ M.ratio / cMesh := by
  change cMesh * eta ≤ M.ratio at h
  exact (le_div_iff₀ hc).2 (by nlinarith [h])

/-- The normalization `cMesh ≤ 1` is a consequence of the two-sided
mesh condition, not an additional paper hypothesis. -/
theorem cMesh_le_one (h : IsPermitted (cMesh := cMesh) M) : cMesh ≤ 1 := by
  change cMesh * eta ≤ M.ratio at h
  have heta : 0 < eta := eta_pos M
  have hupper : M.ratio ≤ eta := M.ratio_le_eta
  nlinarith

/-- For the usual normalization `cMesh ≤ 1`, the actual scale controls the
paper scale without any relation between `delta` and `eta`. -/
theorem cMesh_mul_paperScale_le_actualScale
    (hdelta : 0 ≤ delta) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M) :
    cMesh * (delta + eta) ≤ delta + M.ratio := by
  change cMesh * eta ≤ M.ratio at h
  have hcdelta : cMesh * delta ≤ delta := by
    nlinarith
  calc
    cMesh * (delta + eta) = cMesh * delta + cMesh * eta := by ring
    _ ≤ delta + M.ratio := add_le_add hcdelta h

theorem paperScale_le_inv_mul_actualScale
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M) :
    delta + eta ≤ (1 / cMesh) * (delta + M.ratio) := by
  have hscale := cMesh_mul_paperScale_le_actualScale
    hdelta hcOne h
  calc
    delta + eta ≤ (delta + M.ratio) / cMesh :=
      (le_div_iff₀ hc).2 (by simpa [mul_comm] using hscale)
    _ = (1 / cMesh) * (delta + M.ratio) := by
      field_simp [ne_of_gt hc]

theorem paperScale_sq_le_invSq_mul_actualScale_sq
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M) :
    (delta + eta) ^ 2 ≤
      (1 / cMesh ^ 2) * (delta + M.ratio) ^ 2 := by
  have hpaperNonneg : 0 ≤ delta + eta :=
    add_nonneg hdelta (eta_pos M).le
  have hactualNonneg : 0 ≤ delta + M.ratio :=
    add_nonneg hdelta M.ratio_pos.le
  have hscale := paperScale_le_inv_mul_actualScale
    hdelta hc hcOne h
  have hinvNonneg : 0 ≤ 1 / cMesh := by positivity
  have hsquare := (sq_le_sq₀ hpaperNonneg
    (mul_nonneg hinvNonneg hactualNonneg)).2 hscale
  calc
    (delta + eta) ^ 2 ≤ ((1 / cMesh) * (delta + M.ratio)) ^ 2 := hsquare
    _ = (1 / cMesh ^ 2) * (delta + M.ratio) ^ 2 := by
      field_simp [ne_of_gt hc]

/-- Paper-scale comparison with only the hypotheses literally present in
the two-sided regular-mesh definition. -/
theorem paperScale_sq_le_invSq_mul_actualScale_sq_of_pos
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh)
    (h : IsPermitted (cMesh := cMesh) M) :
    (delta + eta) ^ 2 ≤
      (1 / cMesh ^ 2) * (delta + M.ratio) ^ 2 :=
  paperScale_sq_le_invSq_mul_actualScale_sq
    hdelta hc (cMesh_le_one h) h

/-- A lower quadratic estimate at the actual mesh scale implies the
corresponding paper-scale estimate. -/
theorem paperScale_sq_le_of_actualScale_sq_le
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh) (hcOne : cMesh ≤ 1)
    (h : IsPermitted (cMesh := cMesh) M)
    {V K : ℝ}
    (hV : (delta + M.ratio) ^ 2 ≤ K * V) :
    (delta + eta) ^ 2 ≤ (K / cMesh ^ 2) * V := by
  have hscale := paperScale_sq_le_invSq_mul_actualScale_sq
    hdelta hc hcOne h
  calc
    (delta + eta) ^ 2 ≤
        (1 / cMesh ^ 2) * (delta + M.ratio) ^ 2 := hscale
    _ ≤ (1 / cMesh ^ 2) * (K * V) := by
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    _ = (K / cMesh ^ 2) * V := by ring

/-- The preceding transfer without a separately supplied `cMesh ≤ 1`
premise. -/
theorem paperScale_sq_le_of_actualScale_sq_le_of_pos
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh)
    (h : IsPermitted (cMesh := cMesh) M)
    {V K : ℝ}
    (hV : (delta + M.ratio) ^ 2 ≤ K * V) :
    (delta + eta) ^ 2 ≤ (K / cMesh ^ 2) * V :=
  paperScale_sq_le_of_actualScale_sq_le
    hdelta hc (cMesh_le_one h) h hV

/-- The actual scale is always bounded above by the paper scale. -/
theorem actualScale_le_paperScale :
    delta + M.ratio ≤ delta + eta := by
  linarith [M.ratio_le_eta]

/-- Coarse but uniform combination of the low-cell and positive-cell
quadratic lower bounds used in Lemma 8.6. -/
theorem actualScale_sq_le_456_mul_of_low_and_positive
    {V : ℝ}
    (hlow : delta ^ 2 / 4 ≤ V)
    (hpositive : M.ratio ^ 2 / 224 ≤ V) :
    (delta + M.ratio) ^ 2 ≤ 456 * V := by
  have hcross : (delta + M.ratio) ^ 2 ≤
      2 * delta ^ 2 + 2 * M.ratio ^ 2 := by
    nlinarith [sq_nonneg (delta - M.ratio)]
  have hdeltaV : delta ^ 2 ≤ 4 * V := by linarith
  have hratioV : M.ratio ^ 2 ≤ 224 * V := by linarith
  nlinarith

/-- The exact paper-scale consequence of the two complementary arithmetic
variance estimates.  Only the stated two-sided regularity and
`0 < cMesh` are required. -/
theorem paperScale_sq_le_of_low_and_positive
    (hdelta : 0 ≤ delta) (hc : 0 < cMesh)
    (h : IsPermitted (cMesh := cMesh) M) {V : ℝ}
    (hlow : delta ^ 2 / 4 ≤ V)
    (hpositive : M.ratio ^ 2 / 224 ≤ V) :
    (delta + eta) ^ 2 ≤ (456 / cMesh ^ 2) * V := by
  apply paperScale_sq_le_of_actualScale_sq_le_of_pos hdelta hc h
  exact actualScale_sq_le_456_mul_of_low_and_positive
    hlow hpositive

end IsPermitted

end

end Erdos390.Full.PaperPermittedRegularMesh
