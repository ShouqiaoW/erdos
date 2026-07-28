import Erdos390.Full.CanonicalEndpointCenterEnvelopeEventually

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs.Mesh

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh

noncomputable section

/- Expanded audit: the relative-centre cutoff is quantified before the mesh;
the mesh appears only in the eventual conclusion. -/
example {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalRelativeCenterCutoff ≤ W →
      ∀ e : ℝ, 0 < e →
        ∀ᶠ n : ℕ in atTop, ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∃ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            let E := canonicalCertificate M hdelta hn hWne S
            ∀ j : Fin (M.cellCount + 1),
              |P.center j / E.continuumCenter j - 1| ≤ e :=
  canonicalRelativeCenterCutoff_eventually M hdelta

/- Expanded audit of the sharp moving-low reciprocal scale. -/
example {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalCenterEnvelopeCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
        1 / (canonicalPartition M hdelta hn hWne S).center i ≤
          canonicalCenterEnvelopeConstant delta * Real.log (Scale.L n) :=
  canonicalCenterEnvelopeCutoff_eventually_inverse M hdelta

/- Expanded audit of the equivalent lower-centre form, with exactly the same
global cutoff and constant. -/
example {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta) :
    ∀ W : ℕ, canonicalCenterEnvelopeCutoff ≤ W →
      ∀ᶠ n : ℕ in atTop, ∀ (hn : 1 < n) (hWne : W ≠ 0)
        (S : ScaleSeparation M n W) (i : Fin (M.cellCount + 1)),
        (1 / canonicalCenterEnvelopeConstant delta) /
            Real.log (Scale.L n) ≤
          (canonicalPartition M hdelta hn hWne S).center i :=
  canonicalCenterEnvelopeCutoff_eventually_lower M hdelta

end
end Erdos390.Full.RegularMeshPrimeCutoffs.Mesh
