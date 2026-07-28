import Erdos390.Full.PaperCanonicalReferenceSlowEventually

/-!
Expanded statement audit for the universal canonical reference-row bound.
The constants and structural cutoff precede the paper scale and mesh.
-/

open Filter

namespace Erdos390.Full.PaperBridgeFit.BridgeData

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularMeshPrimeCutoffs

example : ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
    ∀ {delta eta : ℝ} (hdelta : 0 < delta)
      (M : RegularRelativeMesh.Mesh delta eta),
      ∀ᶠ n : ℕ in atTop,
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
          (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          (∃ (hWne : B.sampleData.W ≠ 0)
            (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
            B.partition = Mesh.canonicalPartition
              M hdelta B.n_gt_one hWne S) →
          B.w = delta + eta →
          ∀ i : Fin (M.cellCount + 1),
            |B.referenceSlowRow i| ≤
              (CF + 7 * Cprod) * B.w * B.bandCenter i := by
  exact exists_global_cutoff_eventually_canonical_referenceSlowRow_le

end

end Erdos390.Full.PaperBridgeFit.BridgeData

#print Erdos390.Full.PaperBridgeFit.BridgeData.exists_global_cutoff_eventually_canonical_referenceSlowRow_le
