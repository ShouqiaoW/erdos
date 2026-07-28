import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs.Mesh

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh

noncomputable section

example {delta : ℝ} (M : Mesh delta delta) (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalActualMomentCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∀ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            (∀ p : BandPrime n W,
              |P.deviation p| ≤ delta + M.ratio) ∧
            P.totalL1 ≤ 7 * (delta + M.ratio) ∧
            (delta + M.ratio) ^ 2 / 16 ≤ P.variance ∧
            P.variance ≤ 4 * (delta + M.ratio) ^ 2 ∧
            P.totalL1 / (delta + M.ratio) ≤ 7 ∧
            (delta + M.ratio) ^ 2 / P.variance ≤ 16 ∧
            P.variance / (delta + M.ratio) ^ 2 ≤ 4 :=
  canonicalActualMomentCutoff_eventually M hdelta

end
end Erdos390.Full.RegularMeshPrimeCutoffs.Mesh
