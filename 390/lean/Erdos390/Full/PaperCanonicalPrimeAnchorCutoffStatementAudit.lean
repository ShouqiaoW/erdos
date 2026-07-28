import Erdos390.Full.PaperCanonicalPrimeAnchorEventually

open Filter Set
open scoped BigOperators

namespace Erdos390.Full.RegularMeshPrimeCutoffs.Mesh

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic

noncomputable section

example {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {epsilon : ℝ}
        (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
        (∀ k ∈ anchors, epsilon < M.lower k) →
        (∀ k ∈ anchors, M.upper k ≤ 1 - epsilon) →
        ((1 : ℝ) / 8 ≤ (∑ k ∈ anchors, M.width k) / 2) →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n, ∀ S : ScaleSeparation M n W,
          let P := canonicalPartition M hdelta hn hWne S
          let anchor := canonicalPrimeAnchorSet M P anchors
          (∀ p ∈ anchor, tPrime n p.1 ∈ Icc epsilon (1 - epsilon)) ∧
            (1 : ℝ) / 8 ≤ anchorMass (primeWeight n) anchor :=
  canonicalPrimeAnchorCutoff_eventually M hdelta

end
end Erdos390.Full.RegularMeshPrimeCutoffs.Mesh
