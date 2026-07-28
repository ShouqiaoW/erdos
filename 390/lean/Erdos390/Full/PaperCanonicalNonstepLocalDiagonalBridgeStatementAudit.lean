import Erdos390.Full.PaperCanonicalNonstepLocalDiagonalBridge

open Filter

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticBandGeometry RegularRelativeMesh
open RegularMeshPrimeCutoffs

noncomputable section

/- Expanded audit of the final paper-scale wrapper.  The conclusion displays
the literal local sum and the hypotheses display both `IsPermitted` and the
separate identity `B.w = delta + eta`. -/
example {delta : ℝ} (hdelta : 0 < delta) :
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
              (1 / B.harmonicMass i) *
                  ∑ p ∈ B.partition.data.fiber i,
                    |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2 ≤
                r * B.w * B.bandCenter i := by
  simpa only [bandDeviationReciprocalSquare] using
    exists_cutoff_eventually_permitted_bandDeviationReciprocalSquare
      (delta := delta) hdelta

/- The final interface also expands with the global parameter order and no
separate `cMesh ≤ 1` premise (that inequality follows from `IsPermitted`). -/
example :
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
              (1 / B.harmonicMass i) *
                  ∑ p ∈ B.partition.data.fiber i,
                    |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2 ≤
                r * B.w * B.bandCenter i := by
  simpa only [bandDeviationReciprocalSquare] using
    exists_global_cutoff_eventually_permitted_bandDeviationReciprocalSquare

end

end Erdos390.Full.PaperBridgeFit.BridgeData
