import Erdos390.Full.PaperCanonicalPrimeAnchorEventually
import Erdos390.Full.RegularRelativeMeshInteriorAnchors

/-!
# Assumption-free canonical interior anchor for Lemma 8.6

The paper-scale variance argument uses an interior set of prime coordinates
with a fixed positive reciprocal-logarithmic mass.  This file combines the
deterministic interior block of every sufficiently fine relative mesh with
the canonical prime-anchor quadrature.  The prime cutoff is selected before
the two mesh parameters; only the ambient threshold may depend on the fixed
mesh.
-/

open scoped BigOperators
open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open FiniteAnchoredDirichletQuadratic PrimeSquarefreeDirichletGeometry

namespace Mesh

/-- A canonical literal prime anchor, with no anchor set at the call site. -/
theorem canonicalPaperInteriorAnchorCutoff_eventually :
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
                (1 : ℝ) / 8 ≤ anchorMass (primeWeight n) anchor := by
  intro W hW delta eta M hdelta hfine
  have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
  have hdeltaSmall : delta < (1 : ℝ) / 16 := by linarith
  have hratioSmall : M.ratio < (1 : ℝ) / 16 := by
    linarith [M.ratio_le_eta]
  have hwidth : ∀ k : Fin M.cellCount,
      M.width k < (1 : ℝ) / 16 := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  have hAnchors : M.interiorAnchors.Nonempty :=
    M.interiorAnchors_nonempty hdelta hdeltaSmall hwidth
  have hIdealLower : ∀ k ∈ M.interiorAnchors,
      (1 / 8 : ℝ) < M.lower k := by
    intro k hk
    exact M.interiorAnchors_idealLower hdelta hk
  have hIdealUpper : ∀ k ∈ M.interiorAnchors,
      M.upper k ≤ 1 - (1 / 8 : ℝ) := by
    intro k hk
    exact M.interiorAnchors_idealUpper hdelta hdeltaSmall hwidth hk
  have hIdealMass : (1 / 8 : ℝ) ≤
      (∑ k ∈ M.interiorAnchors, M.width k) / 2 :=
    M.interiorAnchors_mass_lower hdelta hdeltaSmall hwidth
  have hPrime := canonicalPrimeAnchorCutoff_eventually M hdelta W hW
    (epsilon := (1 / 8 : ℝ)) M.interiorAnchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  filter_upwards [hPrime] with n hPrimeAt
  obtain ⟨hWne, hn, hAll⟩ := hPrimeAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hn hWne S
  let anchor := canonicalPrimeAnchorSet M P M.interiorAnchors
  simpa only [P, anchor] using hAll S

end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs
