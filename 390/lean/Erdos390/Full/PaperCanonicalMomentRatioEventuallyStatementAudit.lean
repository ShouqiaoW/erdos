import Erdos390.Full.PaperCanonicalMomentRatioEventually

/-!
# Expanded statement audit: canonical moment ratio

The complete public type is repeated literally so that Lean independently
checks the global parameter order, paper-scale fineness, canonical-partition
identification, and absence of caller-supplied moment estimates.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel RegularRelativeMesh
open MovingLowGaugeTransfer
open RegularMeshPrimeCutoffs

noncomputable section

theorem expanded_exists_paperFineMesh_cutoff_eventually_canonical_momentRatio :
    ∃ Rproj : ℝ, 0 < Rproj ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + eta ≤ meshTol →
      ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head],
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          (∃ hWne : B.sampleData.W ≠ 0,
            ∃ S : ScaleSeparation M B.sampleData.n B.sampleData.W,
              B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
          (∑ j : Fin (M.cellCount + 1),
              B.harmonicMass j * B.bandCenter j) ≤
            Rproj * sharpWeightTotal B.harmonicMass B.bandCenter :=
  exists_paperFineMesh_cutoff_eventually_canonical_momentRatio

end

end BridgeData

end PaperBridgeFit

end Full

end Erdos390
