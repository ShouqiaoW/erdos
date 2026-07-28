import Erdos390.Full.CanonicalEndpointWeightedInverseEventually
import Erdos390.Full.CanonicalEndpointMultiAnchorWeightedInverse

/-!
# Eventual canonical inverse from a fixed positive-mass anchor block

The mesh tolerance is chosen from a fixed lower bound for the total anchor
mass.  It therefore no longer shrinks with the width of a single cell.
-/

open scoped BigOperators
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator MovingLowGaugeTransfer
open PaperWeightedInverseExport PoissonDickmanWeightedInverse
open PoissonDickmanKernelBounds

namespace Mesh

theorem exists_meshTolerance_cutoff_eventually_multiAnchor_projected_inverse
    {epsilon anchorFloor : ℝ} (hepsilon : 0 < epsilon)
    (hhalf : epsilon < 1 / 2) (hAnchorFloor : 0 < anchorFloor) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta)
        (anchors : Finset (Fin M.cellCount)) (hAnchors : anchors.Nonempty)
        (anchor : Fin M.cellCount) (hAnchor : anchor ∈ anchors)
        (hIdealLower : ∀ k ∈ anchors, epsilon < M.lower k)
        (hIdealUpper : ∀ k ∈ anchors, M.upper k ≤ 1 - epsilon)
        (hIdealAnchorMass : anchorFloor ≤
          (∑ k ∈ anchors, M.width k) / 2),
      ((delta < meshTol ∧ ∀ k : Fin M.cellCount, M.width k < meshTol) →
        ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
          ∀ W : ℕ, W₀ ≤ W →
            ∀ᶠ n : ℕ in atTop,
              ∃ hW : W ≠ 0, ∃ hWTwo : 2 ≤ W, ∃ hn : 1 < n,
                ∃ S : ScaleSeparation M n W,
                  ∃ hInteriorLower : ∀ k ∈ anchors, epsilon ≤
                    realLogCoordinate (y n)
                      ((canonicalCertificate M hdelta hn hW S).lower
                        (positiveBand M k) : ℝ),
                  ∃ hInteriorUpper : ∀ k ∈ anchors,
                    realLogCoordinate (y n)
                      ((canonicalCertificate M hdelta hn hW S).upper
                        (positiveBand M k) : ℝ) ≤ 1 - epsilon,
                  let P := canonicalPartition M hdelta hn hW S
                  let E := canonicalCertificate M hdelta hn hW S
                  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW
                    hWTwo S epsilon anchors hAnchors
                      hInteriorLower hInteriorUpper
                  let Cinv :=
                    (4 / (kappa * ∑ j, IM.anchor j)) /
                      (1 - (4 / (kappa * ∑ j, IM.anchor j)) *
                        (2 * (kappa * anchorFloor / 16)))
                  ∃ actualEquiv : SharpGaugeSpace P.mass P.center ≃L[ℝ]
                      SharpGaugeSpace P.mass P.center,
                    (∀ q, actualEquiv q =
                      ArithmeticGaugeStableInverse.projectedSharpCLM
                        (arithmeticDiagonal (y n) E.lower E.upper)
                        (arithmeticKernel (y n) E.lower E.upper)
                        P.center (sharpWeight P.mass P.center)
                        (by
                          change (∑ j, P.mass j * P.center j ^ 2) ≠ 0
                          apply ne_of_gt
                          apply Finset.sum_pos
                          · intro j _hj
                            exact mul_pos (P.data.mass_pos j)
                              (sq_pos_of_pos (P.center_pos hn j))
                          · exact ⟨lowBand M, Finset.mem_univ _⟩) q) ∧
                    (∀ v, ‖actualEquiv.symm v‖ ≤ Cinv * ‖v‖)) := by
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_transposeQuotient_uniform_gap hepsilon hhalf
  obtain ⟨CKernel, hCKernel, hKernelBound⟩ :=
    exists_covarianceKernelQuotient_bound
  let r := kappa * anchorFloor / 16
  have hr : 0 < r := by dsimp only [r]; positivity
  let eDiagonal := r / 8
  let eKernelTail := r / 16
  let eCenter := min (1 / 4) (r / (32 * (CKernel + 1)))
  let eResidual := r / 8
  have heDiagonal : 0 < eDiagonal := by dsimp only [eDiagonal]; positivity
  have heKernelTail : 0 < eKernelTail := by
    dsimp only [eKernelTail]; positivity
  have heCenter : 0 < eCenter := by
    dsimp only [eCenter]
    apply lt_min (by norm_num)
    exact div_pos hr (mul_pos (by norm_num) (by linarith))
  have heCenterHalf : eCenter ≤ 1 / 2 :=
    (min_le_left _ _).trans (by norm_num)
  have heCenterContribution : 4 * eCenter * CKernel ≤ r / 8 := by
    have hmin := min_le_right (1 / 4) (r / (32 * (CKernel + 1)))
    have hCplus : 0 < CKernel + 1 := by linarith
    have hmul : eCenter * CKernel ≤
        (r / (32 * (CKernel + 1))) * CKernel :=
      mul_le_mul_of_nonneg_right hmin hCKernel
    have hratio : CKernel / (CKernel + 1) ≤ 1 := by
      apply (div_le_one hCplus).2
      linarith
    calc
      4 * eCenter * CKernel = 4 * (eCenter * CKernel) := by ring
      _ ≤ 4 * ((r / (32 * (CKernel + 1))) * CKernel) := by gcongr
      _ = r / 8 * (CKernel / (CKernel + 1)) := by
        field_simp [ne_of_gt hCplus]
        ring
      _ ≤ r / 8 := by
        simpa only [mul_one] using
          mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ r / 8)
  have heResidual : 0 < eResidual := by dsimp only [eResidual]; positivity
  have hmodTarget : 0 < eResidual / 10 := div_pos heResidual (by norm_num)
  obtain ⟨meshTol, hmeshTol, hFmod, hKmod⟩ :=
    exists_uniform_cell_oscillation_modulus hmodTarget hmodTarget
  refine ⟨kappa, hkappa, meshTol, hmeshTol, ?_⟩
  intro delta eta M hdelta anchors hAnchors anchor hAnchor hIdealLower
    hIdealUpper hIdealAnchorMass
  rintro ⟨hLowFine, hPositiveFine⟩
  obtain ⟨CRow, hCRow, WKernel, hKernelRowEvent⟩ :=
    exists_cutoff_eventually_canonical_doubleKernelSharpRowError M hdelta
  obtain ⟨WDiagonal, hDiagonalEvent⟩ :=
    exists_cutoff_eventually_canonical_diagonalError M hdelta
  obtain ⟨WCenter, hCenterEvent⟩ :=
    exists_cutoff_eventually_canonical_relativeCenters M hdelta
  have hFixedTerm : Tendsto (fun W : ℕ ↦
      CRow / Real.log (W : ℝ) ^ 3) atTop (nhds 0) := by
    have hLog : Tendsto (fun W : ℕ ↦ Real.log (W : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hInv := tendsto_inv_atTop_zero.comp hLog
    have h := (tendsto_const_nhds : Tendsto (fun _W : ℕ ↦ CRow) atTop
      (nhds CRow)).mul (hInv.pow 3)
    simpa only [Function.comp_apply, mul_zero,
      zero_pow (by norm_num : 3 ≠ 0), div_eq_mul_inv, inv_pow] using h
  obtain ⟨WFixed, hWFixed⟩ := eventually_atTop.1
    (hFixedTerm.eventually (eventually_le_nhds heKernelTail))
  let W₀ := max 2 (max WKernel (max WDiagonal (max WCenter WFixed)))
  refine ⟨CRow, hCRow, W₀, ?_⟩
  intro W hW
  have hWTwo : 2 ≤ W := (le_max_left 2 _).trans hW
  have hWKernel : WKernel ≤ W :=
    ((le_max_left WKernel _).trans (le_max_right 2 _)).trans hW
  have hWDiagonal : WDiagonal ≤ W := by
    exact ((le_max_left WDiagonal (max WCenter WFixed)).trans
      (le_max_right WKernel _)).trans ((le_max_right 2 _).trans hW)
  have hWCenter : WCenter ≤ W := by
    exact ((le_max_left WCenter WFixed).trans
      (le_max_right WDiagonal _)).trans
        ((le_max_right WKernel _).trans ((le_max_right 2 _).trans hW))
  have hWFixed' : WFixed ≤ W := by
    exact ((le_max_right WCenter WFixed).trans
      (le_max_right WDiagonal _)).trans
        ((le_max_right WKernel _).trans ((le_max_right 2 _).trans hW))
  have hFixedSmall : CRow / Real.log (W : ℝ) ^ 3 ≤ eKernelTail :=
    hWFixed W hWFixed'
  have hKernelN := hKernelRowEvent W hWKernel eKernelTail heKernelTail
  have hDiagonalN := hDiagonalEvent W hWDiagonal eDiagonal heDiagonal
  have hCenterN := hCenterEvent W hWCenter eCenter heCenter
  have hAnchorN := eventually_canonical_anchorBlock_coverage M hdelta
    (by omega : W ≠ 0) hWTwo anchors hAnchors hIdealLower hIdealUpper
      hIdealAnchorMass
  have hLengthN := eventually_all_actualCoordinateLengths_lt M hdelta
    hLowFine hPositiveFine W
  let beta := eResidual / (5 * (CKernel + 1))
  have hbeta : 0 < beta := by
    dsimp only [beta]
    exact div_pos heResidual (mul_pos (by norm_num) (by linarith))
  have hTailN := eventually_canonical_twoTails_lt M W hbeta
  filter_upwards [hKernelN, hDiagonalN, hCenterN, hAnchorN, hLengthN,
    hTailN] with n hKernelAt hDiagonalAt hCenterAt hAnchorAt hLengthAt hTailAt
  obtain ⟨hWk, hnk, Sk, hKernelAt⟩ := hKernelAt
  obtain ⟨hWc, hnc, Sc, hCenterAt⟩ := hCenterAt
  obtain ⟨hna, hAnchorAt⟩ := hAnchorAt
  obtain ⟨hLowerA, hUpperA, hAnchorMassA⟩ := hAnchorAt Sk
  let hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnk hWk Sk).lower
          (positiveBand M k) : ℝ) := by
    intro k hk
    simpa only [Subsingleton.elim hna hnk,
      Subsingleton.elim hWk (by omega : W ≠ 0)] using hLowerA k hk
  let hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnk hWk Sk).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon := by
    intro k hk
    simpa only [Subsingleton.elim hna hnk,
      Subsingleton.elim hWk (by omega : W ≠ 0)] using hUpperA k hk
  let P := canonicalPartition M hdelta hnk hWk Sk
  let E := canonicalCertificate M hdelta hnk hWk Sk
  let IM := canonicalIntervalMeshOfAnchors M hdelta hnk hWk hWTwo Sk epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let T := canonicalTwoTailCertificateOfAnchors M hdelta hnk hWk hWTwo Sk
    epsilon anchors hAnchors anchor hAnchor hInteriorLower hInteriorUpper
  have hAnchorMass : anchorFloor ≤ ∑ j, IM.anchor j := by
    simpa only [IM, Subsingleton.elim hna hnk,
      Subsingleton.elim hWk (by omega : W ≠ 0),
      Subsingleton.elim hWTwo hWTwo] using hAnchorMassA
  have hKernelRows (i : Fin (M.cellCount + 1)) :
      endpointDoubleKernelSharpRowError M hdelta hnk hWk Sk i ≤ r / 8 := by
    have hraw := hKernelAt i
    have hsum : CRow / Real.log (W : ℝ) ^ 3 + eKernelTail ≤ r / 8 := by
      dsimp only [eKernelTail] at hFixedSmall ⊢
      linarith
    exact hraw.trans hsum
  have hRelative (i : Fin (M.cellCount + 1)) :
      |P.center i / IM.center i - 1| ≤ eCenter := by
    have hc := hCenterAt i
    have hc' : |P.center i / E.continuumCenter i - 1| ≤ eCenter := by
      simpa only [P, E, Subsingleton.elim hnc hnk,
        Subsingleton.elim hWc hWk, Subsingleton.elim Sc Sk] using hc
    have hy : 1 < y n := by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hnk)]
        exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hnk))
      exact (Real.log_pos_iff (Scale.y_pos (Nat.zero_lt_of_lt hnk)).le).mp hlog
    have hmono : Monotone (fullCutoff M n W) :=
      fullCutoff_monotone M hdelta hnk (W_le_first_fullCutoff M Sk)
    have hLowerTwo (j : Fin (M.cellCount + 1)) : 2 ≤ E.lower j := by
      change 2 ≤ fullCutoff M n W j.1
      exact hWTwo.trans (hmono (Nat.zero_le j.1))
    have hId := IM.center_eq_intervalCertificate_continuumCenter E hy
      hLowerTwo (fun _ ↦ rfl) (fun _ ↦ rfl) i
    rw [hId]
    exact hc'
  have hLengths (j : Fin (M.cellCount + 1)) : IM.length j < meshTol := by
    simpa only [IM, canonicalIntervalMeshOfAnchors, IntervalMesh.length,
      actualCutoffCoordinate] using hLengthAt j
  have hBase : T.base < beta := by
    simpa only [T, canonicalTwoTailCertificateOfAnchors,
      canonicalTwoTailCertificate, actualCutoffCoordinate,
      fullCutoff_zero] using hTailAt.1
  have hTop : 1 - T.upperEnd < beta := by
    simpa only [T, canonicalTwoTailCertificateOfAnchors,
      canonicalTwoTailCertificate, actualCutoffCoordinate] using hTailAt.2
  have hResidualRows (i : Fin (M.cellCount + 1)) :
      |IM.rowResidual i| ≤ eResidual := by
    exact (rowResidual_lt_of_global_modulus IM T heResidual hCKernel
      (fun s hs t ht ↦ hKernelBound t ht s hs)
      hFmod hKmod rfl hBase hTop hLengths i).le
  have hSmall : eDiagonal + r / 8 + 4 * eCenter * CKernel + eResidual ≤
      kappa * anchorFloor / 16 := by
    change r / 8 + r / 8 + 4 * eCenter * CKernel + r / 8 ≤ r
    linarith [heCenterContribution]
  obtain ⟨actualEquiv, hactual, hinv⟩ :=
    exists_multiAnchor_canonical_projected_inverse M hdelta hnk hWk hWTwo
      Sk anchors hAnchors anchor hAnchor hInteriorLower hInteriorUpper
      hkappa hAnchorFloor hAnchorMass hgap heCenter.le heCenterHalf
      hDiagonalAt hKernelRows hRelative hResidualRows
      (fun s hs t ht ↦ hKernelBound t ht s hs) hSmall
  exact ⟨hWk, hWTwo, hnk, Sk, hInteriorLower, hInteriorUpper,
    actualEquiv, hactual, hinv⟩

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
