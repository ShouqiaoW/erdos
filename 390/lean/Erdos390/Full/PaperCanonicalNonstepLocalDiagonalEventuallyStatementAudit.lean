import Erdos390.Full.PaperCanonicalNonstepLocalDiagonalEventually

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs.Mesh

open ArithmeticBandGeometry RegularRelativeMesh

noncomputable section

/- Expanded quantifier-order audit.  In particular `W₀,W` precede the
independent request `eta`, the mesh, and the relative tolerance; the bound
uses `delta + M.ratio`, not `delta + eta`. -/
example {delta : ℝ} (hdelta : 0 < delta) :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {eta : ℝ} (M : Mesh delta eta), ∀ r : ℝ, 0 < r →
        ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
          (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
          let P := canonicalPartition M hdelta hn hWne S
          (1 / P.mass i) *
              ∑ p ∈ P.data.fiber i,
                |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2 ≤
            r * (delta + M.ratio) * P.center i := by
  simpa only [ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare] using
    exists_cutoff_eventually_canonical_nonstepLocalDiagonal
      (delta := delta) hdelta

/- The terminal wrapper used later in the paper has the genuinely global
order: `W₀,W` precede `delta`, `eta`, the mesh, and the accuracy. -/
example :
    ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta), ∀ (hdelta : 0 < delta),
        ∀ r : ℝ, 0 < r →
          ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
            (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
            let P := canonicalPartition M hdelta hn hWne S
            (1 / P.mass i) *
                ∑ p ∈ P.data.fiber i,
                  |P.deviation p| * (1 / (p.1 : ℝ)) ^ 2 ≤
              r * (delta + M.ratio) * P.center i := by
  simpa only [ArithmeticBandGeometry.Partition.normalizedDeviationReciprocalSquare] using
    exists_global_cutoff_eventually_canonical_nonstepLocalDiagonal

end

end Erdos390.Full.RegularMeshPrimeCutoffs.Mesh
