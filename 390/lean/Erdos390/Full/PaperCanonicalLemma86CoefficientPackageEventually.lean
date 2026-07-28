import Erdos390.Full.PaperCanonicalGeometricMomentFineMeshEventually
import Erdos390.Full.PaperActualTwoStageRegression
import Erdos390.Full.PaperEffectiveNorm

/-!
# Canonical eventual coefficient package for Lemma 8.6

This file joins the paper-scale canonical prime geometry to the literal
first-stage Schur regression.  All prime-deviation moments, the moving-low
cell, the positive-cell variance, and the prime anchor are discharged before
the public call site.  The only quantitative call-site inputs are precisely
those supplied by the preceding inverse lemma:

* an equivalence representing the same literal Schur map, together with its
  sharp inverse estimate; and
* the normalized slow right-row estimate.

The theorem is uniform over an arbitrary effective box.  Its quantifiers are
ordered as in the paper: the structural prime cutoff is fixed before the
mesh, the mesh before the effective box, and only then may the ambient
integer threshold be selected.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperWeightedInverseExport PrimeSums
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

/-- The coefficient package needs no cutoff beyond the final geometric one. -/
noncomputable def canonicalPaperLemma86CoefficientCutoff : ℕ :=
  RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff

set_option maxHeartbeats 1000000 in
/--
Uniform canonical `q^reg` and compensated-coefficient bounds at the literal
paper scale `B.w = delta + eta`.

No moment, profile, row-residual, or anchor hypothesis occurs in this
statement.  The same-map identity is retained explicitly, so the displayed
regression is certified to solve the literal actual Schur equation rather
than merely being the image of an unrelated bounded equivalence.
-/
theorem canonicalPaperLemma86CoefficientCutoff_eventually
    (cMesh : ℝ) (hcMesh : 0 < cMesh)
    (Cinv Crow : ℝ) (hCinv : 0 ≤ Cinv) (hCrow : 0 ≤ Crow) :
    ∀ W : ℕ, canonicalPaperLemma86CoefficientCutoff ≤ W →
      ∀ {delta eta : ℝ}
        (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤
            RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance →
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
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instHead _instHeadDec _instHeadNonempty a
  have hWgeom :
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff ≤ W := by
    simpa only [canonicalPaperLemma86CoefficientCutoff] using hW
  have hGeometry :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually
      cMesh hcMesh W hWgeom M hdelta hPermitted hfine
  have hBandT := eventually_bandTReciprocalSum_le W
  filter_upwards [hGeometry, hBandT] with n hGeometryAt hBandTAt
  intro B hBn hBW hpartition hscale z _hz gamma hgamma hgap e he hinv
    hrightRow
  subst n
  subst W
  obtain ⟨hWgeomNe, hnGeom, hGeometryAll⟩ := hGeometryAt
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      hnGeom hWgeomNe S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hdevSupRaw, hdevL1Raw, _hvarLowerRaw, hdevL2Raw,
      _hcenterRaw⟩ := hGeometryAll S
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ B.w := by
    intro p
    rw [hpartitionCanonical, hscale]
    exact hdevSupRaw p
  have hdevL1 : B.partition.totalL1 ≤ 7 * B.w := by
    rw [hpartitionCanonical, hscale]
    exact hdevL1Raw
  have hdevL2 : B.partition.variance ≤ 4 * B.w ^ 2 := by
    rw [hpartitionCanonical, hscale]
    exact hdevL2Raw
  have hright := B.actualBandRegressionTarget_sharpNorm_le_of_row
    (B.effectiveParamEquiv z) hgamma hgap hCrow B.w_pos.le hrightRow
  have hTwoCrow : 0 ≤ 2 * Crow := mul_nonneg (by norm_num) hCrow
  have hsharpRaw := B.actualBandRegression_sharpNorm_le
    (B.effectiveParamEquiv z) hgamma hgap e hCinv hinv hright
  obtain ⟨hcoeffSupRaw, hcoeffL1Raw, hcoeffL2Raw⟩ :=
    B.actualBandRegression_compensatedCoefficient_three_bounds
      (B.effectiveParamEquiv z) hgamma hgap e hCinv hTwoCrow B.w_pos.le
      hinv hright hBandTAt hdevSup hdevL1 hdevL2
  have hnormal := B.actualBandRegression_normalEquation
    (B.effectiveParamEquiv z) hgamma hgap e he
  have hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one)
      (B.actualBandRegression
        (B.effectiveParamEquiv z) hgamma hgap e) ≤
        (Cinv * (2 * Crow)) * (delta + eta) := by
    simpa only [hscale] using hsharpRaw
  have hcoeffSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.actualCompensatedCoefficient
        (B.actualBandRegression
          (B.effectiveParamEquiv z) hgamma hgap e) p| ≤
          (1 + Cinv * (2 * Crow)) * (delta + eta) := by
    simpa only [hscale] using hcoeffSupRaw
  have hcoeffL1 : B.partition.compensatedL1
      (B.actualBandRegression
        (B.effectiveParamEquiv z) hgamma hgap e) ≤
      (7 + (Cinv * (2 * Crow)) * (2 * Real.log 4)) *
        (delta + eta) := by
    simpa only [hscale] using hcoeffL1Raw
  have hcoeffL2 : B.partition.compensatedL2Sq
      (B.actualBandRegression
        (B.effectiveParamEquiv z) hgamma hgap e) ≤
      2 * (4 + (Cinv * (2 * Crow)) ^ 2 * (2 * Real.log 4)) *
        (delta + eta) ^ 2 := by
    simpa only [hscale] using hcoeffL2Raw
  exact ⟨hnormal, hsharp, hcoeffSup, hcoeffL1, hcoeffL2⟩

/-- Existential interface making the paper's mesh/cutoff order explicit. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_actualBandRegression_coefficients_of_schurSplice
    (cMesh : ℝ) (hcMesh : 0 < cMesh)
    (Cinv Crow : ℝ) (hCinv : 0 ≤ Cinv) (hCrow : 0 ≤ Crow) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ {delta eta : ℝ}
          (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta)
          (_hPermitted : IsPermitted (cMesh := cMesh) M),
          delta + eta ≤ meshTol →
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
  refine ⟨RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance,
    by norm_num [RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance],
    canonicalPaperLemma86CoefficientCutoff, ?_⟩
  exact canonicalPaperLemma86CoefficientCutoff_eventually
    cMesh hcMesh Cinv Crow hCinv hCrow

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
