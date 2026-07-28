import Erdos390.Full.PaperCanonicalPositiveCellVarianceEventually
import Erdos390.Full.PaperPermittedRegularMesh
import Erdos390.Full.RegularRelativeMeshInteriorAnchors

/-!
# Paper-scale geometric moment inputs on every permitted fine mesh

This file assembles the arithmetic estimates used after the continuum-to-band
transfer.  The structural prime cutoff and the numerical mesh tolerance are
chosen before the mesh.  The two mesh parameters remain independent: the
only comparison used is the two-sided regularity condition from the paper,
namely

`cMesh * eta ≤ M.ratio ≤ eta`.

The lower variance estimate deliberately combines two different arithmetic
sources.  The moving low cell controls `delta^2`, while the positive cells
control the square of the actual relative width `M.ratio`.  Thus no hidden
hypothesis such as `M.ratio ≤ delta` or `eta ≤ delta` is present.
-/

open scoped BigOperators
open Filter

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open PaperPermittedRegularMesh

namespace Mesh

/-- A single mesh-independent cutoff for the moments and the prime anchor. -/
noncomputable def canonicalPaperGeometricCutoff : ℕ :=
  max canonicalActualMomentCutoff canonicalPrimeAnchorCutoff

/-- The fixed numerical small-mesh threshold used by the anchor argument. -/
def canonicalPaperGeometricMeshTolerance : ℝ := (1 : ℝ) / 16

/--
Uniform paper-scale geometric inputs for the literal canonical partition.

The order of the quantifiers is important.  After the fixed structural
constant `cMesh`, the cutoff `W` is selected before `delta`, `eta`, and the
mesh.  Only the eventual ambient threshold may depend on the fixed mesh.
-/
theorem canonicalPaperGeometricCutoff_eventually
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∀ W : ℕ, canonicalPaperGeometricCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta)
        (hdelta : 0 < delta)
        (_hPermitted : IsPermitted (cMesh := cMesh) M),
        delta + eta ≤ canonicalPaperGeometricMeshTolerance →
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
  intro W hW delta eta M hdelta hPermitted hfine
  have hWmoment : canonicalActualMomentCutoff ≤ W :=
    (le_max_left canonicalActualMomentCutoff
      canonicalPrimeAnchorCutoff).trans hW
  have hWanchor : canonicalPrimeAnchorCutoff ≤ W :=
    (le_max_right canonicalActualMomentCutoff
      canonicalPrimeAnchorCutoff).trans hW
  have heta : 0 < eta := IsPermitted.eta_pos M
  have hdeltaSmall : delta < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith
  have hratioSmall : M.ratio < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith [M.ratio_le_eta]
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 : ℝ) / 16 := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  have hdeltaHalf : delta ≤ (1 : ℝ) / 2 := by linarith
  have hratioOne : M.ratio ≤ 1 := by linarith
  have hActualPaper : delta + M.ratio ≤ delta + eta :=
    IsPermitted.actualScale_le_paperScale
  have hActualSmall : delta + M.ratio ≤ (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    exact hActualPaper.trans hfine
  obtain ⟨anchors, anchor, hanchor, hIdealLower, hIdealUpper, hIdealMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  have hMoment :=
    canonicalActualPreliminaryMomentCutoff_eventually M hdelta W hWmoment
  have hPositive := canonicalPositiveVarianceCutoff_eventually M hdelta
    hdeltaHalf hratioOne W hWmoment
  have hPrimeAnchor := canonicalPrimeAnchorCutoff_eventually M hdelta
    W hWanchor (epsilon := (1 / 8 : ℝ)) anchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  filter_upwards [hMoment, hPositive, hPrimeAnchor] with
      n hMomentAt hPositiveAt hAnchorAt
  obtain ⟨hWm, hnm, hMomentAll⟩ := hMomentAt
  obtain ⟨hWp, hnp, hPositiveAll⟩ := hPositiveAt
  obtain ⟨hWa, hna, hAnchorAll⟩ := hAnchorAt
  refine ⟨hWm, hnm, ?_⟩
  intro S
  let P := canonicalPartition M hdelta hnm hWm S
  obtain ⟨hSupActual, hL1Actual, hLowBand, hVarUpperActual⟩ :=
    hMomentAll S
  have hPositiveRaw := hPositiveAll S
  have hPositiveCells : M.ratio ^ 2 / 224 ≤
      ∑ k : Fin M.cellCount,
        P.bandVariance (positiveBand M k) := by
    simpa only [P, Subsingleton.elim hnp hnm,
      Subsingleton.elim hWp hWm] using hPositiveRaw
  obtain ⟨hInteriorRaw, hAnchorMassRaw⟩ := hAnchorAll S
  have hInterior : ∀ p ∈ canonicalPrimeAnchorSet M P anchors,
      tPrime n p.1 ∈
        Set.Icc ((1 : ℝ) / 8) (1 - (1 : ℝ) / 8) := by
    simpa only [P, Subsingleton.elim hna hnm,
      Subsingleton.elim hWa hWm] using hInteriorRaw
  have hAnchorMass : (1 : ℝ) / 8 ≤
      FiniteAnchoredDirichletQuadratic.anchorMass
        (PrimeSquarefreeDirichletGeometry.primeWeight n)
        (canonicalPrimeAnchorSet M P anchors) := by
    simpa only [P, Subsingleton.elim hna hnm,
      Subsingleton.elim hWa hWm] using hAnchorMassRaw
  have hBandVarNonneg (j : Fin (M.cellCount + 1)) :
      0 ≤ P.bandVariance j := by
    unfold ArithmeticBandGeometry.Partition.bandVariance
    exact Finset.sum_nonneg fun p hp ↦
      mul_nonneg (by positivity) (sq_nonneg _)
  have hVarianceSplit : P.variance =
      P.bandVariance 0 +
        ∑ k : Fin M.cellCount, P.bandVariance k.succ := by
    rw [P.variance_eq_sum_bandVariance, Fin.sum_univ_succ]
  have hPositiveCells' : M.ratio ^ 2 / 224 ≤
      ∑ k : Fin M.cellCount, P.bandVariance k.succ := by
    simpa only [positiveBand] using hPositiveCells
  have hPositiveSumNonneg : 0 ≤
      ∑ k : Fin M.cellCount, P.bandVariance k.succ :=
    Finset.sum_nonneg fun k hk ↦ hBandVarNonneg k.succ
  have hLowTotal : delta ^ 2 / 4 ≤ P.variance := by
    rw [hVarianceSplit]
    linarith
  have hPositiveTotal : M.ratio ^ 2 / 224 ≤ P.variance := by
    rw [hVarianceSplit]
    exact hPositiveCells'.trans
      (le_add_of_nonneg_left (hBandVarNonneg 0))
  have hPaperLower : (delta + eta) ^ 2 ≤
      (456 / cMesh ^ 2) * P.variance :=
    IsPermitted.paperScale_sq_le_of_low_and_positive
      hdelta.le hcMesh hPermitted hLowTotal hPositiveTotal
  have hSupPaper : ∀ p : BandPrime n W,
      |P.deviation p| ≤ delta + eta := fun p ↦
    (hSupActual p).trans hActualPaper
  have hL1Paper : P.totalL1 ≤ 7 * (delta + eta) :=
    hL1Actual.trans
      (mul_le_mul_of_nonneg_left hActualPaper (by norm_num))
  have hActualNonneg : 0 ≤ delta + M.ratio :=
    (add_pos hdelta M.ratio_pos).le
  have hPaperNonneg : 0 ≤ delta + eta :=
    (add_pos hdelta heta).le
  have hScaleSq : (delta + M.ratio) ^ 2 ≤ (delta + eta) ^ 2 :=
    (sq_le_sq₀ hActualNonneg hPaperNonneg).2 hActualPaper
  have hVarUpperPaper : P.variance ≤ 4 * (delta + eta) ^ 2 :=
    hVarUpperActual.trans
      (mul_le_mul_of_nonneg_left hScaleSq (by norm_num))
  have hCenter : P.variance ≤ P.centerEnergy :=
    variance_le_centerEnergy_of_canonical_anchor_of_actualScale M hdelta
      hActualSmall hnm hWm S anchors hInterior hAnchorMass hVarUpperActual
  exact ⟨hSupPaper, hL1Paper, hPaperLower, hVarUpperPaper, hCenter⟩

/--
The canonical centre energy has an absolute lower floor on every sufficiently
fine paper mesh.  The cutoff is chosen before `delta`, `eta`, and the mesh;
no comparison between the two mesh parameters is required.

This is the denominator estimate used when an ordinary row bound is converted
to the paper's quotient moment ratio.  Stating it separately prevents that
conversion from silently importing the regularity hypothesis needed only for
the variance lower bound.
-/
theorem canonicalPaperCenterEnergyFloorCutoff_eventually :
    ∀ W : ℕ, canonicalPrimeAnchorCutoff ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta)
        (hdelta : 0 < delta),
        delta + eta ≤ canonicalPaperGeometricMeshTolerance →
        ∀ᶠ n : ℕ in atTop,
          ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
            ∀ S : ScaleSeparation M n W,
              (1 : ℝ) / 64 ≤
                (canonicalPartition M hdelta hn hWne S).centerEnergy := by
  intro W hW delta eta M hdelta hfine
  have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
  have hdeltaSmall : delta < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith
  have hratioSmall : M.ratio < (1 : ℝ) / 16 := by
    dsimp only [canonicalPaperGeometricMeshTolerance] at hfine
    linarith [M.ratio_le_eta]
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 : ℝ) / 16 := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt hratioSmall
  obtain ⟨anchors, anchor, hanchor, hIdealLower, hIdealUpper, hIdealMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hanchor⟩
  have hPrimeAnchor := canonicalPrimeAnchorCutoff_eventually M hdelta
    W hW (epsilon := (1 / 8 : ℝ)) anchors hAnchors
      hIdealLower hIdealUpper hIdealMass
  filter_upwards [hPrimeAnchor] with n hAnchorAt
  obtain ⟨hWne, hn, hAnchorAll⟩ := hAnchorAt
  refine ⟨hWne, hn, ?_⟩
  intro S
  obtain ⟨hInterior, hAnchorMass⟩ := hAnchorAll S
  exact one_div_64_le_centerEnergy_of_canonical_anchor M hdelta
    hn hWne S anchors hInterior hAnchorMass

/-- Existential wrapper exposing both mesh-independent structural choices. -/
theorem exists_fineMesh_cutoff_eventually_canonical_paper_geometric_inputs
    (cMesh : ℝ) (hcMesh : 0 < cMesh) :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
        ∀ {delta eta : ℝ} (M : Mesh delta eta)
          (hdelta : 0 < delta)
          (_hPermitted : IsPermitted (cMesh := cMesh) M),
          delta + eta ≤ meshTol →
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
  refine ⟨canonicalPaperGeometricMeshTolerance,
    by norm_num [canonicalPaperGeometricMeshTolerance],
    canonicalPaperGeometricCutoff, ?_⟩
  exact canonicalPaperGeometricCutoff_eventually cMesh hcMesh

end Mesh

end Erdos390.Full.RegularMeshPrimeCutoffs
