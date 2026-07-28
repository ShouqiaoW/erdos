import Erdos390.Full.PaperCanonicalLemma86CoefficientPackageEventually

/-!
Expanded statement audit for the canonical Lemma 8.6 coefficient package.

The audit spells out the global cutoff and mesh tolerance and repeats the
full public interface.  In particular there is no diagonal-mesh comparison,
moment hypothesis, profile hypothesis, or caller-supplied anchor.
-/

open Filter Metric Set

namespace Erdos390.Full.PaperBridgeFit.BridgeData

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

example
    (cMesh : ℝ) (hcMesh : 0 < cMesh)
    (Cinv Crow : ℝ) (hCinv : 0 ≤ Cinv) (hCrow : 0 ≤ Crow) :
    ∀ W : ℕ,
      max RegularMeshPrimeCutoffs.canonicalActualMomentCutoff
          RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W →
      ∀ {delta eta : ℝ}
        (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ (1 : ℝ) / 16 →
        ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
          (a : NNReal),
          ∀ᶠ n : ℕ in atTop,
            ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
              B.sampleData.n = n →
              B.sampleData.W = W →
              (∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition =
                  RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
                    B.n_gt_one hWne S) →
              B.w = delta + eta →
              ∀ (z : B.EffectiveParamSpace),
                z ∈ closedBall
                  (0 : B.EffectiveParamSpace) (a : ℝ) →
                ∀ {gamma : ℝ} (hgamma : 0 < gamma)
                  (hgap : ∀ u, gamma * ‖u‖ ^ 2 ≤
                    inner ℝ u (B.nuisanceCovarianceOperator
                      (B.effectiveParamEquiv z) u))
                  (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge),
                  (∀ q, e q = B.actualBandSchurLinearMap
                    (B.effectiveParamEquiv z) hgamma hgap q) →
                  (∀ v,
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one) (e.symm v) ≤
                      Cinv *
                        paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one) v) →
                  (∀ j,
                    |B.normalizedBandCovarianceRow
                        (B.effectiveParamEquiv z)
                        (B.nuisanceResidualScore
                          (B.effectiveParamEquiv z) hgamma hgap
                          B.slowScore) j| ≤
                      (Crow * B.w) * B.bandCenter j) →
                  B.actualBandSchurLinearMap
                      (B.effectiveParamEquiv z) hgamma hgap
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) =
                    B.actualBandRegressionTarget
                      (B.effectiveParamEquiv z) hgamma hgap ∧
                  paperSharpNorm B.harmonicMass B.bandCenter
                      (B.partition.center_ne_zero B.n_gt_one)
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) ≤
                    (Cinv * (2 * Crow)) * (delta + eta) ∧
                  (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                    |B.actualCompensatedCoefficient
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) p| ≤
                      (1 + Cinv * (2 * Crow)) * (delta + eta)) ∧
                  B.partition.compensatedL1
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) ≤
                    (7 + (Cinv * (2 * Crow)) * (2 * Real.log 4)) *
                      (delta + eta) ∧
                  B.partition.compensatedL2Sq
                      (B.actualBandRegression
                        (B.effectiveParamEquiv z) hgamma hgap e) ≤
                    2 * (4 +
                      (Cinv * (2 * Crow)) ^ 2 * (2 * Real.log 4)) *
                        (delta + eta) ^ 2 := by
  simpa only [canonicalPaperLemma86CoefficientCutoff,
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff,
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance] using
      canonicalPaperLemma86CoefficientCutoff_eventually
        cMesh hcMesh Cinv Crow hCinv hCrow

end Erdos390.Full.PaperBridgeFit.BridgeData
