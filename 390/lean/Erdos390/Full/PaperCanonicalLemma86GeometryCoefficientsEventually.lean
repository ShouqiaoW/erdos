import Erdos390.Full.PaperCanonicalLemma84Eventually
import Erdos390.Full.PaperCanonicalLemma86CoefficientPackageEventually
import Erdos390.Full.PaperCanonicalNonstepSlowResidualEventually

/-!
# Closed geometric and coefficient clauses of paper Lemma 8.6

This file combines the already discharged moving-low-cell geometry, the
literal Lemma 8.4 Schur inverse, and the non-step slow right row.  The result
is the first half of the paper-order Lemma 8.6 umbrella: the same equivalence
which is exactly the actual finite nuisance-Schur map supplies the regression
and all three compensated-coefficient estimates.

No anchor, convergence assertion, analytic comparison, or row estimate is
present at the public call site.  The two mesh parameters are independent;
their only smallness condition is on `delta + eta`.  All numerical constants
and the structural cutoff are selected before `W`, the permitted mesh, the
finite head data, and the effective tilt ball.
-/

open scoped BigOperators
open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PaperGuardCensus PaperWeightedInverseExport
open RegularMeshPrimeCutoffs PaperPermittedRegularMesh

namespace BridgeData

set_option maxHeartbeats 2000000 in
/--
Assumption-free paper-order terminal for the geometric and coefficient
conclusions of Lemma 8.6.

The output retains the literal normal equation and the exact same-map
identity.  Consequently the displayed `q^reg` and compensated coefficients
are attached to the actual finite-`n` nuisance-Schur operator, not merely to
an abstract bounded equivalence.
-/
theorem exists_paperFineMesh_cutoff_eventually_canonical_lemma86_geometry_coefficients
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Csharp : ℝ, 0 < Csharp ∧
      ∃ Cordinary : ℝ, 0 < Cordinary ∧
      ∃ Crow : ℝ, 0 ≤ Crow ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta)
        (hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ meshTol →
        ∀ (Head : Type*) [Fintype Head] [DecidableEq Head] [Nonempty Head],
        ∀ (Phead : Head → HeadPattern.Pattern),
          (∀ h : Head, ∀ p : ℕ,
            p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
        ∀ (I : PhysicalIntervals) (U : ℝ) (hU : 1 ≤ U)
          (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
          (hupperU : ∀ sigma, I.upper sigma ≤ U),
        ∀ (Cprom Cbank : ℕ) (ledger : ∀ n, Ledger n Cprom Cbank),
        ∀ (a : NNReal) (marginFloor : ℝ), 0 < marginFloor →
        ∀ᶠ n : ℕ in atTop,
          ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            ∀ (hBWlarge : 1 < B.sampleData.W),
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell Phead I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              (hcanonical : B.sampleData = canonicalSampleData
                (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                  hsep hremaining) →
              (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                  (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
                B.partition = RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
              (hscale : B.w = delta + eta) →
              ∀ (T : BarycentricTarget B.sampleData)
                (hTmargin : marginFloor ≤ T.cellMassMargin)
                (hbaseline : B.baseline = T.baseline),
                (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                    |B.partition.deviation p| ≤ delta + eta) ∧
                B.partition.totalL1 ≤ 7 * (delta + eta) ∧
                (delta + eta) ^ 2 ≤
                  (456 / cMesh ^ 2) * B.partition.variance ∧
                B.partition.variance ≤ 4 * (delta + eta) ^ 2 ∧
                B.partition.variance ≤ B.partition.centerEnergy ∧
                ∃ e : ∀ (z : B.EffectiveParamSpace),
                    z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
                      B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge,
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) q,
                    e z hz q =
                      B.actualBandSchurLinearMap (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) q) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one)
                        ((e z hz).symm v) ≤
                      Csharp *
                        paperSharpNorm B.harmonicMass B.bandCenter
                          (B.partition.center_ne_zero B.n_gt_one) v) ∧
                  (∀ (z : B.EffectiveParamSpace)
                      (hz : z ∈ closedBall
                        (0 : B.EffectiveParamSpace) (a : ℝ)) v,
                    ‖(e z hz).symm v‖ ≤ Cordinary * ‖v‖) ∧
                  ∀ (z : B.EffectiveParamSpace)
                    (hz : z ∈ closedBall
                      (0 : B.EffectiveParamSpace) (a : ℝ)),
                    (∀ j,
                      |B.normalizedBandCovarianceRow
                          (B.effectiveParamEquiv z)
                          (B.nuisanceResidualScore
                            (B.effectiveParamEquiv z)
                            (B.canonicalEffectiveNuisanceGamma_pos
                              I U (3 * (a : ℝ)) T)
                            (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                              hU hlowerOne hupperU
                              (by intro sigma; rw [hcanonical]; rfl)
                              (by intro sigma; rw [hcanonical]; rfl)
                              T hbaseline hBWlarge z hz)
                            B.slowScore) j| ≤
                        (Crow * B.w) * B.bandCenter j) ∧
                    B.actualBandSchurLinearMap
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz)
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) =
                      B.actualBandRegressionTarget
                        (B.effectiveParamEquiv z)
                        (B.canonicalEffectiveNuisanceGamma_pos
                          I U (3 * (a : ℝ)) T)
                        (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                          hU hlowerOne hupperU
                          (by intro sigma; rw [hcanonical]; rfl)
                          (by intro sigma; rw [hcanonical]; rfl)
                          T hbaseline hBWlarge z hz) ∧
                    paperSharpNorm B.harmonicMass B.bandCenter
                        (B.partition.center_ne_zero B.n_gt_one)
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) ≤
                      (Csharp * (2 * Crow)) * (delta + eta) ∧
                    (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                      |B.actualCompensatedCoefficient
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) p| ≤
                        (1 + Csharp * (2 * Crow)) * (delta + eta)) ∧
                    B.partition.compensatedL1
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) ≤
                      (7 + (Csharp * (2 * Crow)) * (2 * Real.log 4)) *
                        (delta + eta) ∧
                    B.partition.compensatedL2Sq
                        (B.actualBandRegression
                          (B.effectiveParamEquiv z)
                          (B.canonicalEffectiveNuisanceGamma_pos
                            I U (3 * (a : ℝ)) T)
                          (B.canonicalEffectiveNuisanceGap_on_closedBall I a
                            hU hlowerOne hupperU
                            (by intro sigma; rw [hcanonical]; rfl)
                            (by intro sigma; rw [hcanonical]; rfl)
                            T hbaseline hBWlarge z hz)
                          (e z hz)) ≤
                      2 * (4 +
                        (Csharp * (2 * Crow)) ^ 2 * (2 * Real.log 4)) *
                          (delta + eta) ^ 2 := by
  obtain ⟨_kappa, _hkappa, inverseTol, hinverseTol,
      Csharp, hCsharp, Cordinary, hCordinary, Winverse, hInverse⟩ :=
    exists_paperFineMesh_cutoff_eventually_canonical_lemma84
  obtain ⟨CF, Cprod, hCF, hCprod, Wrow, _hWrowTwo, hRow⟩ :=
    exists_global_cutoff_eventually_canonical_nonstepSlowResidualRow_le
  let Crow : ℝ := 2 + CF + 7 * Cprod
  let meshTol : ℝ := min inverseTol
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance
  let W₀ : ℕ := max Winverse
    (max Wrow canonicalPaperLemma86CoefficientCutoff)
  have hCrow : 0 ≤ Crow := by
    dsimp only [Crow]
    positivity
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    exact lt_min hinverseTol (by
      norm_num [RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance])
  refine ⟨meshTol, hmeshTol, Csharp, hCsharp, Cordinary, hCordinary,
    Crow, hCrow, W₀, ?_⟩
  intro W hW delta eta M hdelta hPermitted hfine
    Head _instFintype _instDecidable _instNonempty Phead hPhead
    I U hU hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hWinverse : Winverse ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWrow : Wrow ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hWcoefficient : canonicalPaperLemma86CoefficientCutoff ≤ W := by
    dsimp only [W₀] at hW
    omega
  have hInverseFine : delta + eta ≤ inverseTol :=
    hfine.trans (min_le_left inverseTol
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance)
  have hGeometryFine : delta + eta ≤
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance :=
    hfine.trans (min_le_right inverseTol
      RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricMeshTolerance)
  have hInverseN := hInverse W hWinverse M hdelta hInverseFine
    Head Phead hPhead I U hU hlowerOne hupperU
      Cprom Cbank ledger a marginFloor hmargin
  have hRowN := hRow W hWrow hdelta M Phead hPhead I U hU
    hlowerOne hupperU Cprom Cbank ledger a marginFloor hmargin
  have hGeometryN :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPaperGeometricCutoff_eventually
      cMesh hcMesh W hWcoefficient M hdelta hPermitted hGeometryFine
  have hCoefficientN := canonicalPaperLemma86CoefficientCutoff_eventually
    cMesh hcMesh Csharp Crow hCsharp.le hCrow W hWcoefficient
      M hdelta hPermitted hGeometryFine (Head := Head) a
  filter_upwards [hInverseN, hRowN, hGeometryN, hCoefficientN] with
      n hInverseAt hRowAt hGeometryAt hCoefficientAt
  intro B hBn hBW hBWlarge hsep hremaining hcanonical hpartition
    hscale T hTmargin hbaseline
  subst n
  subst W
  obtain ⟨e, _hGap, he, hsharp, hordinary⟩ :=
    hInverseAt B rfl rfl hBWlarge hsep hremaining hcanonical
      hpartition T hTmargin hbaseline
  obtain ⟨hWgeomNe, hnGeom, hGeometryAll⟩ := hGeometryAt
  have hpartitionCall := hpartition
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  have hSgeom : ScaleSeparation M B.sampleData.n B.sampleData.W := S
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      hnGeom hWgeomNe hSgeom
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by dsimp only [Pcanonical])
  obtain ⟨hdevRaw, hL1Raw, hvarLowerRaw, hvarUpperRaw, hcenterRaw⟩ :=
    hGeometryAll hSgeom
  have hdev : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ delta + eta := by
    intro p
    rw [hpartitionCanonical]
    exact hdevRaw p
  have hL1 : B.partition.totalL1 ≤ 7 * (delta + eta) := by
    rw [hpartitionCanonical]
    exact hL1Raw
  have hvarLower : (delta + eta) ^ 2 ≤
      (456 / cMesh ^ 2) * B.partition.variance := by
    rw [hpartitionCanonical]
    exact hvarLowerRaw
  have hvarUpper : B.partition.variance ≤ 4 * (delta + eta) ^ 2 := by
    rw [hpartitionCanonical]
    exact hvarUpperRaw
  have hcenter : B.partition.variance ≤ B.partition.centerEnergy := by
    rw [hpartitionCanonical]
    exact hcenterRaw
  refine ⟨hdev, hL1, hvarLower, hvarUpper, hcenter, e, he, hsharp,
    hordinary, ?_⟩
  intro z hz
  let hgamma : 0 < B.canonicalEffectiveNuisanceGamma
      I U (3 * (a : ℝ)) T :=
    B.canonicalEffectiveNuisanceGamma_pos I U (3 * (a : ℝ)) T
  let hgap : ∀ v,
      B.canonicalEffectiveNuisanceGamma I U (3 * (a : ℝ)) T * ‖v‖ ^ 2 ≤
        inner ℝ v (B.nuisanceCovarianceOperator
          (B.effectiveParamEquiv z) v) :=
    B.canonicalEffectiveNuisanceGap_on_closedBall I a hU
      hlowerOne hupperU
      (by intro sigma; rw [hcanonical]; rfl)
      (by intro sigma; rw [hcanonical]; rfl)
      T hbaseline hBWlarge z hz
  have hright : ∀ j,
      |B.normalizedBandCovarianceRow
          (B.effectiveParamEquiv z)
          (B.nuisanceResidualScore
            (B.effectiveParamEquiv z) hgamma hgap B.slowScore) j| ≤
        (Crow * B.w) * B.bandCenter j := by
    intro j
    simpa only [Crow, hgamma, hgap] using
      hRowAt B rfl rfl hsep hremaining hcanonical hpartitionCall hscale
        T hTmargin hbaseline z hz j
  have hCoefficient := hCoefficientAt B rfl rfl hpartitionCall hscale z hz
    hgamma hgap (e z hz) (he z hz) (hsharp z hz) hright
  exact ⟨by simpa only [hgamma, hgap] using hright,
    by simpa only [hgamma, hgap] using hCoefficient⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
