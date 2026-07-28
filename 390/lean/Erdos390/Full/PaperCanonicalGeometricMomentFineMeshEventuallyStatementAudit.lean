import Erdos390.Full.PaperCanonicalGeometricMomentFineMeshEventually

/-!
Expanded statement audit for the final paper-scale geometric package.

In particular this spells out the fixed cutoff, keeps `delta` and `eta`
independent, and records the two-sided permitted-mesh hypothesis.  It prevents
the public theorem from silently acquiring a diagonal-mesh or profile-level
assumption.
-/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs.Mesh

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PaperPermittedRegularMesh

example (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∀ W : ℕ,
      max canonicalActualMomentCutoff canonicalPrimeAnchorCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ (1 : ℝ) / 16 →
        ∀ᶠ n : ℕ in atTop,
          ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
            ∀ S : ScaleSeparation M n W,
              let P := canonicalPartition M hdelta hn hWne S
              (∀ p : BandPrime n W,
                |P.deviation p| ≤ delta + eta) ∧
              P.totalL1 ≤ 7 * (delta + eta) ∧
              (delta + eta) ^ 2 ≤
                (456 / cMesh ^ 2) * P.variance ∧
              P.variance ≤ 4 * (delta + eta) ^ 2 ∧
              P.variance ≤ P.centerEnergy := by
  simpa only [canonicalPaperGeometricCutoff,
    canonicalPaperGeometricMeshTolerance] using
      canonicalPaperGeometricCutoff_eventually cMesh hcMesh

end Erdos390.Full.RegularMeshPrimeCutoffs.Mesh
