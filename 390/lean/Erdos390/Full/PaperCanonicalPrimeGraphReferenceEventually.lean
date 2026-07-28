import Erdos390.Full.PaperReferenceSharpPrimeGraph
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually
import Erdos390.Full.PaperCanonicalPrimeAnchorEventually
import Erdos390.Full.PaperCanonicalPrimeRowResidualEventually

/-!
# Canonical arithmetic reference inverse with cutoff before the mesh

This is the paper-order eventual wrapper for the literal prime-graph
argument.  The mesh tolerance, inverse constant, and prime cutoff are
selected before `delta` and the regular mesh.  Only the final ambient
threshold may depend on the fixed mesh and anchor block.
-/

open scoped BigOperators
open Filter Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open PaperCanonicalSlowKappa
open PaperWeightedInverseExport
open RegularRelativeMesh

namespace BridgeData

set_option maxHeartbeats 1800000 in
/-- Exact paper-order reference terminal.  In particular, `W₀` is outside
the quantifiers for `delta` and `M`, and the inverse constant is independent
of the number of cells and of the moving low-band centre. -/
theorem exists_cutoff_before_mesh_eventually_referenceSharp_primeGraph_inverse :
    ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ Cref : ℝ, 0 < Cref ∧
      ∃ W₀ : ℕ,
      ∀ W : ℕ, W₀ ≤ W →
      ∀ (Head : Type*) [Fintype Head] [DecidableEq Head],
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
        ∀ (anchors : Finset (Fin M.cellCount)), anchors.Nonempty →
          (∀ k ∈ anchors, (1 / 8 : ℝ) < M.lower k) →
          (∀ k ∈ anchors, M.upper k ≤ 1 - (1 / 8 : ℝ)) →
          ((1 / 8 : ℝ) ≤ (∑ k ∈ anchors, M.width k) / 2) →
          ∀ᶠ n : ℕ in atTop,
            ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
              B.sampleData.n = n → B.sampleData.W = W →
              (∃ (hWne : B.sampleData.W ≠ 0)
                  (S : RegularMeshPrimeCutoffs.ScaleSeparation
                    M B.sampleData.n B.sampleData.W),
                B.partition =
                  RegularMeshPrimeCutoffs.Mesh.canonicalPartition M
                    hdelta B.n_gt_one hWne S) →
              ∃ cert : PositiveCellTransfer.IntervalCertificate B.partition,
                ∃ referenceEquiv :
                    SharpGaugeSpace B.partition.mass B.partition.center
                        ≃L[ℝ]
                      SharpGaugeSpace B.partition.mass B.partition.center,
                  (∀ q, referenceEquiv q =
                    ArithmeticGaugeStableInverse.projectedSharpCLM
                      (CompressedArithmeticOperator.arithmeticDiagonal
                        (y B.sampleData.n) cert.lower cert.upper)
                      (CompressedArithmeticOperator.arithmeticKernel
                        (y B.sampleData.n) cert.lower cert.upper)
                      B.partition.center
                      (MovingLowGaugeTransfer.sharpWeight
                        B.partition.mass B.partition.center)
                      (ne_of_gt B.actualSharpWeightTotal_pos) q) ∧
                  ∀ v, ‖referenceEquiv.symm v‖ ≤ Cref * ‖v‖ := by
  obtain ⟨CF, hCF, hF⟩ :=
    PaperActualSlowRightRowFinite.exists_F_lipschitz_unit
  obtain ⟨CKernel, hCKernel, hKernel⟩ :=
    PoissonDickmanKernelBounds.exists_covarianceKernel_abs_le_first
  let kappa : ℝ := canonicalSlowKappa
  let anchorFloor : ℝ := 1 / 8
  let A : ℝ := 2 * CF + 7 * CKernel
  let radius : ℝ := kappa * anchorFloor / 16
  let meshTol : ℝ := radius / (2 * (A + 1))
  let rowTarget : ℝ := radius - A * meshTol
  let Cref : ℝ := 8 / (kappa * anchorFloor)
  have hkappa : 0 < kappa := by
    simpa only [kappa] using canonicalSlowKappa_pos
  have hfloor : 0 < anchorFloor := by
    dsimp only [anchorFloor]
    norm_num
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hAone : 0 < A + 1 := by linarith
  have hradius : 0 < radius := by
    dsimp only [radius]
    positivity
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    positivity
  have hmeshIdentity : meshTol * (2 * (A + 1)) = radius := by
    dsimp only [meshTol]
    field_simp [ne_of_gt hAone]
  have hAmLt : A * meshTol < radius := by
    nlinarith [mul_nonneg hA hmeshTol.le]
  have hrowTarget : 0 < rowTarget := by
    dsimp only [rowTarget]
    linarith
  have hCref : 0 < Cref := by
    dsimp only [Cref]
    positivity
  obtain ⟨Wrow, hRowEvent⟩ :=
    PaperCanonicalPrimeRowResidualEventually.exists_cutoff_eventually_primeRowResidual_le
      hrowTarget
  let W₀ : ℕ := max 2
    (max RegularMeshPrimeCutoffs.canonicalActualMomentCutoff
      (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow))
  refine ⟨meshTol, hmeshTol, Cref, hCref, W₀, ?_⟩
  intro W hW Head _instFintype _instDecidable
  have hWmoment :
      RegularMeshPrimeCutoffs.canonicalActualMomentCutoff ≤ W :=
    ((le_max_left _
      (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow)).trans
        (le_max_right 2 _)).trans hW
  have hWanchor :
      RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff ≤ W :=
    ((le_max_left _ Wrow).trans
      ((le_max_right _
        (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow)).trans
          (le_max_right 2 _))).trans hW
  have hWrow : Wrow ≤ W :=
    ((le_max_right _ Wrow).trans
      ((le_max_right _
        (max RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff Wrow)).trans
          (le_max_right 2 _))).trans hW
  have hRow := hRowEvent W hWrow
  intro delta eta M hdelta hmesh anchors hAnchors
    hIdealLower hIdealUpper hIdealMass
  have hMoment :=
    RegularMeshPrimeCutoffs.Mesh.canonicalActualFirstMomentCutoff_eventually
      M hdelta W hWmoment
  have hAnchor :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorCutoff_eventually
      M hdelta W hWanchor anchors hAnchors hIdealLower hIdealUpper
        hIdealMass
  filter_upwards [hMoment, hAnchor, hRow] with
      n hMomentN hAnchorN hRowN
  intro B hBn hBW hpartition
  subst n
  subst W
  obtain ⟨_hWmoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWanchor, hnAnchor, hAnchorAll⟩ := hAnchorN
  obtain ⟨hWuser, S, hpartitionUser⟩ := hpartition
  let Pcanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPartition M hdelta
      B.n_gt_one hWuser S
  let Ecanonical :=
    RegularMeshPrimeCutoffs.Mesh.canonicalCertificate M hdelta
      B.n_gt_one hWuser S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ meshTol := by
    intro p
    have hpRaw : |Pcanonical.deviation p| ≤ delta + M.ratio := by
      simpa only [Pcanonical] using hdevSupRaw p
    change |B.partition.deviation p| ≤ meshTol
    rw [hpartitionCanonical]
    exact hpRaw.trans hmesh
  have hdevL1 : B.primeDeviationL1 ≤ 7 * meshTol := by
    have hL1Raw : Pcanonical.totalL1 ≤ 7 * (delta + M.ratio) := by
      simpa only [Pcanonical] using hdevL1Raw
    change B.partition.totalL1 ≤ 7 * meshTol
    rw [hpartitionCanonical]
    exact hL1Raw.trans
      (mul_le_mul_of_nonneg_left hmesh (by norm_num))
  obtain ⟨hInteriorRaw, hMassRaw⟩ := hAnchorAll S
  let anchor :=
    RegularMeshPrimeCutoffs.Mesh.canonicalPrimeAnchorSet
      M Pcanonical anchors
  have hInterior : ∀ p ∈ anchor,
      tPrime B.sampleData.n p.1 ∈
        Set.Icc (1 / 8 : ℝ) (1 - 1 / 8) := by
    simpa only [anchor, Pcanonical,
      Subsingleton.elim hnAnchor B.n_gt_one,
      Subsingleton.elim hWanchor hWuser] using hInteriorRaw
  have hMass : (1 / 8 : ℝ) ≤
      anchorMass (primeWeight B.sampleData.n) anchor := by
    simpa only [anchor, Pcanonical,
      Subsingleton.elim hnAnchor B.n_gt_one,
      Subsingleton.elim hWanchor hWuser] using hMassRaw
  let cert : PositiveCellTransfer.IntervalCertificate B.partition := by
    rw [hpartitionCanonical]
    exact Ecanonical
  have hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n p.1) -
          DickmanBasic.F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p| := by
    intro p
    simpa only [bandCenter, primeDeviation, abs_sub_comm] using
      hF _ (tPrime_mem_unit B.n_gt_one p) _
        (B.partition.center_mem_zero_one B.n_gt_one
          (B.partition.band p))
  have hKernelFirst : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 := by
    intro p q
    exact hKernel _ (tPrime_mem_unit B.n_gt_one p) _
      (tPrime_mem_unit B.n_gt_one q)
  let mass : ℝ := anchorMass (primeWeight B.sampleData.n) anchor
  let base : ℝ := 4 / (kappa * mass)
  let loss : ℝ := base * (2 * radius)
  have hmassFloor : anchorFloor ≤ mass := by
    simpa only [anchorFloor, mass] using hMass
  have hmass : 0 < mass := hfloor.trans_le hmassFloor
  have hlossId : loss = anchorFloor / (2 * mass) := by
    dsimp only [loss, base, radius]
    field_simp [ne_of_gt hkappa, ne_of_gt hmass]
    ring
  have hlossLe : loss ≤ 1 / 2 := by
    rw [hlossId]
    apply (div_le_iff₀ (mul_pos (by norm_num) hmass)).2
    nlinarith
  have hsmallLoss : loss < 1 := hlossLe.trans_lt (by norm_num)
  have herrorIdentity :
      rowTarget + (2 * CF + 7 * CKernel) * meshTol = radius := by
    dsimp only [rowTarget, A]
    ring
  have hsmall :
      (4 / (canonicalSlowKappa *
          anchorMass (primeWeight B.sampleData.n) anchor)) *
        (2 * (rowTarget + (2 * CF + 7 * CKernel) * meshTol)) < 1 := by
    simpa only [kappa, mass, base, loss, herrorIdentity] using hsmallLoss
  obtain ⟨referenceEquiv, hreference, hinv⟩ :=
    B.exists_referenceSharpProjectedEquiv_of_primeGraph cert anchor
      hInterior hrowTarget.le hmeshTol.le hCF.le hCKernel
      hRowN hFdiff hKernelFirst hdevSup hdevL1
      (hfloor.trans_le hmassFloor) hsmall
  have hkMass : 0 < kappa * mass := mul_pos hkappa hmass
  have hkFloor : 0 < kappa * anchorFloor := mul_pos hkappa hfloor
  have hbasePos : 0 < base := by
    dsimp only [base]
    exact div_pos (by norm_num) hkMass
  have hdenHalf : 1 / 2 ≤ 1 - loss := by linarith
  have hbaseBound : base ≤ 4 / (kappa * anchorFloor) := by
    dsimp only [base]
    apply (div_le_div_iff₀ hkMass hkFloor).2
    have hkorder := mul_le_mul_of_nonneg_left hmassFloor hkappa.le
    nlinarith
  have hconstantBound : base / (1 - loss) ≤ Cref := by
    calc
      base / (1 - loss) ≤ base / (1 / 2) :=
        div_le_div_of_nonneg_left hbasePos.le (by norm_num) hdenHalf
      _ = 2 * base := by ring
      _ ≤ 2 * (4 / (kappa * anchorFloor)) :=
        mul_le_mul_of_nonneg_left hbaseBound (by norm_num)
      _ = Cref := by
        dsimp only [Cref]
        ring
  refine ⟨cert, referenceEquiv, hreference, ?_⟩
  intro v
  exact (hinv v).trans
    (mul_le_mul_of_nonneg_right (by
      simpa only [kappa, mass, base, loss, herrorIdentity] using
        hconstantBound) (norm_nonneg v))

end BridgeData
end
end Erdos390.Full.PaperBridgeFit
