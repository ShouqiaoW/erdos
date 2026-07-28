import Erdos390.Full.PaperCanonicalNonstepLocalDiagonalEventually
import Erdos390.Full.PaperNonstepSlowRightLedger
import Erdos390.Full.PaperPermittedRegularMesh

/-!
# Canonical BridgeData wrapper for the non-step local diagonal

This is the paper-facing form: no endpoint, moment, or rate estimate is a
caller premise.  The only geometric input is the exact assertion that the
bridge partition is the canonical arithmetic partition, and the only scale
input identifies `B.w` with `delta + M.ratio`.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry RegularRelativeMesh
open RegularMeshPrimeCutoffs

namespace BridgeData

/-- Structural cutoff and canonical specialization at the *actual* mesh
scale.  This is the stronger reusable internal form; the following theorem
performs the separate conversion to the paper scale. -/
theorem exists_cutoff_eventually_canonical_bandDeviationReciprocalSquare
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta),
      ∀ r : ℝ, 0 < r →
        ∀ᶠ n : ℕ in atTop,
          ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
            (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + M.ratio →
            ∀ i : Fin (M.cellCount + 1),
              B.bandDeviationReciprocalSquare i ≤
                r * B.w * B.bandCenter i := by
  obtain ⟨W₀, hmain⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_nonstepLocalDiagonal
      (delta := delta) hdelta
  refine ⟨W₀, ?_⟩
  intro W hW eta M r hr
  have hEvent := hmain W hW M r hr
  filter_upwards [hEvent] with n hdiag
  intro Head _instFintype _instDecEq B hBn hBW hpartition hscale i
  subst n
  subst W
  obtain ⟨hWne, S, hpart⟩ := hpartition
  have hcanonical := hdiag B.n_gt_one hWne S i
  change B.partition.normalizedDeviationReciprocalSquare i ≤
    r * B.w * B.partition.center i
  rw [hpart, hscale]
  exact hcanonical

/-- Final paper-scale specialization.  The two scales remain syntactically
distinct: the analytic theorem is first applied at `delta + M.ratio`, and
only then is `M.ratio ≤ eta` used to reach `delta + eta = B.w`.  The paper's
two-sided permitted-mesh hypothesis is kept explicit for compatibility with
the rest of Lemma 8.6, even though this one-sided conversion uses only its
upper half stored in `Mesh`. -/
theorem exists_cutoff_eventually_permitted_bandDeviationReciprocalSquare
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {cMesh eta : ℝ}
        (_hcMesh : 0 < cMesh)
        (M : RegularRelativeMesh.Mesh delta eta),
        PaperPermittedRegularMesh.IsPermitted (cMesh := cMesh) M →
      ∀ r : ℝ, 0 < r →
        ∀ᶠ n : ℕ in atTop,
          ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
            (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ i : Fin (M.cellCount + 1),
              B.bandDeviationReciprocalSquare i ≤
                r * B.w * B.bandCenter i := by
  obtain ⟨W₀, hmain⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_cutoff_eventually_canonical_nonstepLocalDiagonal
      (delta := delta) hdelta
  refine ⟨W₀, ?_⟩
  intro W hW cMesh eta _hcMesh M _hpermitted r hr
  have hEvent := hmain W hW M r hr
  filter_upwards [hEvent] with n hdiag
  intro Head _instFintype _instDecEq B hBn hBW hpartition hscale i
  subst n
  subst W
  obtain ⟨hWne, S, hpart⟩ := hpartition
  have hactual := hdiag B.n_gt_one hWne S i
  have hcenter : 0 <
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one hWne S).center i :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta B.n_gt_one hWne S).center_pos B.n_gt_one i
  have hscaleLe : delta + M.ratio ≤ delta + eta :=
    PaperPermittedRegularMesh.IsPermitted.actualScale_le_paperScale
  have hscaled :
      r * (delta + M.ratio) *
          (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
            M hdelta B.n_gt_one hWne S).center i ≤
        r * (delta + eta) *
          (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
            M hdelta B.n_gt_one hWne S).center i := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscaleLe hr.le) hcenter.le
  change B.partition.normalizedDeviationReciprocalSquare i ≤
    r * B.w * B.partition.center i
  rw [hpart, hscale]
  exact hactual.trans hscaled

/-- Final global-order paper wrapper.  This is the interface to be used by
Lemma 8.6 and Proposition 8.7: `W₀,W` occur before `delta`, `eta`, the
permitted mesh, the head space, and the accuracy request. -/
theorem exists_global_cutoff_eventually_permitted_bandDeviationReciprocalSquare :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta cMesh eta : ℝ} (hdelta : 0 < delta)
        (_hcMesh : 0 < cMesh)
        (M : RegularRelativeMesh.Mesh delta eta),
        PaperPermittedRegularMesh.IsPermitted (cMesh := cMesh) M →
      ∀ r : ℝ, 0 < r →
        ∀ᶠ n : ℕ in atTop,
          ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
            (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ i : Fin (M.cellCount + 1),
              B.bandDeviationReciprocalSquare i ≤
                r * B.w * B.bandCenter i := by
  obtain ⟨W₀, hmain⟩ :=
    RegularMeshPrimeCutoffs.Mesh.exists_global_cutoff_eventually_canonical_nonstepLocalDiagonal
  refine ⟨W₀, ?_⟩
  intro W hW delta _cMesh eta hdelta _hcMesh M
    _hpermitted r hr
  have hEvent := hmain W hW M hdelta r hr
  filter_upwards [hEvent] with n hdiag
  intro Head _instFintype _instDecEq B hBn hBW hpartition hscale i
  subst n
  subst W
  obtain ⟨hWne, S, hpart⟩ := hpartition
  have hactual := hdiag B.n_gt_one hWne S i
  have hcenter : 0 <
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one hWne S).center i :=
    (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta B.n_gt_one hWne S).center_pos B.n_gt_one i
  have hscaleLe : delta + M.ratio ≤ delta + eta :=
    PaperPermittedRegularMesh.IsPermitted.actualScale_le_paperScale
  have hscaled :
      r * (delta + M.ratio) *
          (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
            M hdelta B.n_gt_one hWne S).center i ≤
        r * (delta + eta) *
          (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
            M hdelta B.n_gt_one hWne S).center i := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hscaleLe hr.le) hcenter.le
  change B.partition.normalizedDeviationReciprocalSquare i ≤
    r * B.w * B.partition.center i
  rw [hpart, hscale]
  exact hactual.trans hscaled

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
