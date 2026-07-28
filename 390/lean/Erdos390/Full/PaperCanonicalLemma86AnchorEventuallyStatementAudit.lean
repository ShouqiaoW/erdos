import Erdos390.Full.PaperCanonicalLemma86AnchorEventually

/-! Expanded statement audit for the assumption-free canonical anchor. -/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open FiniteAnchoredDirichletQuadratic PrimeSquarefreeDirichletGeometry

namespace Mesh

example :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ (1 : ℝ) / 16 →
        ∀ᶠ n : ℕ in atTop,
          ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
            ∀ S : ScaleSeparation M n W,
              let P := canonicalPartition M hdelta hn hWne S;
              let anchor := canonicalPrimeAnchorSet M P M.interiorAnchors;
                (∀ p ∈ anchor,
                  tPrime n p.1 ∈
                    Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8)) ∧
                (1 : ℝ) / 8 ≤ anchorMass (primeWeight n) anchor :=
  canonicalPaperInteriorAnchorCutoff_eventually

end Mesh

end


end Erdos390.Full.RegularMeshPrimeCutoffs
