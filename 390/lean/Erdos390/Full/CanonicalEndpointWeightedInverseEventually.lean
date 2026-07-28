import Erdos390.Full.CanonicalEndpointWeightedInverseAttachment
import Erdos390.Full.CanonicalEndpointAnchorCoverage
import Erdos390.Full.CanonicalEndpointMeshGeometryEventually

/-!
# Eventual weighted inverse for the literal canonical endpoint family

This file combines the unconditional endpoint estimates with the deterministic
attachment theorem.  The order of choices is explicit: the Dickman gap and a
mesh tolerance are selected first, the fixed cutoff is selected next, and the
ambient integer is taken sufficiently large last.
-/

open scoped BigOperators
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator PositiveCellTransfer
open MovingLowGaugeTransfer
open PaperWeightedInverseExport
open PoissonDickmanWeightedInverse PoissonDickmanKernelBounds

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- A single global modulus and the two literal endpoint tails imply the
two-tail row-residual estimate for every finite interval mesh.  The constants
do not depend on the number of cells. -/
theorem rowResidual_lt_of_global_modulus
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    {epsilon target meshTol beta C : ℝ}
    (IM : IntervalMesh epsilon Band)
    (T : IM.TwoTailPartitionCertificate)
    (htarget : 0 < target)
    (hC : 0 ≤ C)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |ConditionedPoissonLimit.covarianceKernelQuotient t s| ≤ C)
    (hFmod : ∀ x ∈ Icc (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      |x - y| < meshTol → |DickmanBasic.F x - DickmanBasic.F y| < target / 10)
    (hKmod : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        |t - u| < meshTol →
          |ConditionedPoissonLimit.covarianceKernelQuotient t s -
            ConditionedPoissonLimit.covarianceKernelQuotient u s| < target / 10)
    (hbeta : beta = target / (5 * (C + 1)))
    (hBase : T.base < beta) (hTop : 1 - T.upperEnd < beta)
    (hLength : ∀ j, IM.length j < meshTol)
    (i : Band) :
    |IM.rowResidual i| < target := by
  have hCplus : 0 < C + 1 := by linarith
  have hFosc (j : Band) (s : ℝ)
      (hs : s ∈ Icc (IM.lower j) (IM.upper j)) :
      |DickmanBasic.F s - DickmanBasic.F (IM.lower j)| ≤ target / 10 := by
    apply (hFmod s (IM.cell_mem_unit hs) (IM.lower j)
      ⟨(IM.lower_pos j).le,
        (IM.lower_lt_upper j).le.trans (IM.upper_le_one j)⟩ ?_).le
    rw [abs_of_nonneg (sub_nonneg.mpr hs.1)]
    have : s - IM.lower j ≤ IM.length j := by
      unfold IntervalMesh.length
      linarith [hs.2]
    exact this.trans_lt (hLength j)
  have hKosc (j : Band) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1)
      (t : ℝ) (ht : t ∈ Icc (IM.lower j) (IM.upper j)) :
      |ConditionedPoissonLimit.covarianceKernelQuotient t s -
        ConditionedPoissonLimit.covarianceKernelQuotient (IM.lower j) s| ≤
          target / 10 := by
    apply (hKmod s hs t (IM.cell_mem_unit ht) (IM.lower j)
      ⟨(IM.lower_pos j).le,
        (IM.lower_lt_upper j).le.trans (IM.upper_le_one j)⟩ ?_).le
    rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]
    have : t - IM.lower j ≤ IM.length j := by
      unfold IntervalMesh.length
      linarith [ht.2]
    exact this.trans_lt (hLength j)
  have hraw := IM.abs_rowResidual_le_twoTails T hFosc hKosc hKernel i
  have hmiddle : T.upperEnd - T.base ≤ 1 := by
    linarith [T.base_nonneg, T.upperEnd_le_one]
  have hkernelTerm :
      2 * (target / 10) * (T.upperEnd - T.base) ≤ target / 5 := by
    have hcoef : 0 ≤ 2 * (target / 10) := by positivity
    calc
      2 * (target / 10) * (T.upperEnd - T.base) ≤
          2 * (target / 10) * 1 :=
        mul_le_mul_of_nonneg_left hmiddle hcoef
      _ = target / 5 := by ring
  have hlow : C * T.base < target / 5 := by
    have hfirst : C * T.base ≤ (C + 1) * T.base :=
      mul_le_mul_of_nonneg_right (by linarith) T.base_nonneg
    have hsecond : (C + 1) * T.base < (C + 1) * beta :=
      mul_lt_mul_of_pos_left hBase hCplus
    have heq : (C + 1) * beta = target / 5 := by
      rw [hbeta]
      field_simp [ne_of_gt hCplus]
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  have hhigh : C * (1 - T.upperEnd) < target / 5 := by
    have hnonneg : 0 ≤ 1 - T.upperEnd := sub_nonneg.mpr T.upperEnd_le_one
    have hfirst : C * (1 - T.upperEnd) ≤
        (C + 1) * (1 - T.upperEnd) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    have hsecond : (C + 1) * (1 - T.upperEnd) < (C + 1) * beta :=
      mul_lt_mul_of_pos_left hTop hCplus
    have heq : (C + 1) * beta = target / 5 := by
      rw [hbeta]
      field_simp [ne_of_gt hCplus]
    exact hfirst.trans_lt (hsecond.trans_eq heq)
  calc
    |IM.rowResidual i| ≤
        2 * (target / 10) +
          2 * (target / 10) * (T.upperEnd - T.base) +
          C * T.base + C * (1 - T.upperEnd) := hraw
    _ < target := by
      have hdiag : 2 * (target / 10) = target / 5 := by ring
      rw [hdiag]
      linarith

/-- Unconditional eventual invertibility of the literal canonical arithmetic
matrix, for every ideal mesh finer than the selected global modulus.  The
displayed inverse constant is the one obtained from the stable graph inverse;
the deterministic attachment theorem additionally exports it to the paper's
raw gauge. -/
theorem exists_meshTolerance_cutoff_eventually_canonical_projected_inverse
    (hdelta : 0 < delta)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
    (anchorCell : Fin M.cellCount)
    (hIdealLower : epsilon < M.lower anchorCell)
    (hIdealUpper : M.upper anchorCell ≤ 1 - epsilon) :
    ∃ kappa : ℝ, 0 < kappa ∧ ∃ meshTol : ℝ, 0 < meshTol ∧
      ((delta < meshTol ∧ ∀ k : Fin M.cellCount, M.width k < meshTol) →
        ∃ CRow : ℝ, 0 < CRow ∧ ∃ W₀ : ℕ,
          ∀ W : ℕ, W₀ ≤ W →
            ∀ᶠ n : ℕ in atTop,
              ∃ hW : W ≠ 0, ∃ hWTwo : 2 ≤ W, ∃ hn : 1 < n,
                ∃ S : ScaleSeparation M n W,
                  ∃ hInteriorLower : epsilon ≤
                    realLogCoordinate (y n)
                      ((canonicalCertificate M hdelta hn hW S).lower
                        (positiveBand M anchorCell) : ℝ),
                  ∃ hInteriorUpper :
                    realLogCoordinate (y n)
                      ((canonicalCertificate M hdelta hn hW S).upper
                        (positiveBand M anchorCell) : ℝ) ≤ 1 - epsilon,
                  let P := canonicalPartition M hdelta hn hW S
                  let E := canonicalCertificate M hdelta hn hW S
                  let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S
                    epsilon anchorCell hInteriorLower hInteriorUpper
                  let Cinv :=
                    (4 / (kappa * ∑ j, IM.anchor j)) /
                      (1 - (4 / (kappa * ∑ j, IM.anchor j)) *
                        (2 * (kappa * (M.width anchorCell / 2) / 16)))
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
  let anchorFloor := M.width anchorCell / 2
  have hAnchorFloor : 0 < anchorFloor := half_pos (M.width_pos hdelta anchorCell)
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
  have heCenterHalf : eCenter ≤ 1 / 2 := by
    exact (min_le_left _ _).trans (by norm_num)
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
  have hFixedEventually := hFixedTerm.eventually
    (eventually_le_nhds heKernelTail)
  obtain ⟨WFixed, hWFixed⟩ := (eventually_atTop.1 hFixedEventually)
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
  have hAnchorN := eventually_canonical_anchor_coverage M hdelta
    (by omega : W ≠ 0) anchorCell hIdealLower hIdealUpper
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
  have hCoverage := hAnchorAt Sk
  have hInteriorLower : epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnk hWk Sk).lower
          (positiveBand M anchorCell) : ℝ) := by
    simpa only [Subsingleton.elim hna hnk, Subsingleton.elim hWk (by omega : W ≠ 0)]
      using hCoverage.1
  have hInteriorUpper :
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnk hWk Sk).upper
          (positiveBand M anchorCell) : ℝ) ≤ 1 - epsilon := by
    simpa only [Subsingleton.elim hna hnk, Subsingleton.elim hWk (by omega : W ≠ 0)]
      using hCoverage.2.1
  have hAnchorLength : M.width anchorCell / 2 ≤
      realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hnk hWk Sk).upper
            (positiveBand M anchorCell) : ℝ) -
        realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hnk hWk Sk).lower
            (positiveBand M anchorCell) : ℝ) := by
    simpa only [Subsingleton.elim hna hnk, Subsingleton.elim hWk (by omega : W ≠ 0)]
      using hCoverage.2.2
  let P := canonicalPartition M hdelta hnk hWk Sk
  let E := canonicalCertificate M hdelta hnk hWk Sk
  let IM := canonicalIntervalMesh M hdelta hnk hWk hWTwo Sk epsilon anchorCell
    hInteriorLower hInteriorUpper
  let T := canonicalTwoTailCertificate M hdelta hnk hWk hWTwo Sk epsilon
    anchorCell hInteriorLower hInteriorUpper
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
    have hId := canonicalIM_center_eq_certificate M hdelta hnk hWk hWTwo Sk
      epsilon anchorCell hInteriorLower hInteriorUpper i
    change IM.center i = E.continuumCenter i at hId
    rw [hId]
    exact hc'
  have hLengths (j : Fin (M.cellCount + 1)) : IM.length j < meshTol := by
    simpa only [IM, canonicalIntervalMesh, IntervalMesh.length,
      actualCutoffCoordinate] using hLengthAt j
  have hBase : T.base < beta := by
    simpa only [T, canonicalTwoTailCertificate, actualCutoffCoordinate,
      fullCutoff_zero] using hTailAt.1
  have hTop : 1 - T.upperEnd < beta := by
    simpa only [T, canonicalTwoTailCertificate, actualCutoffCoordinate]
      using hTailAt.2
  have hResidualRows (i : Fin (M.cellCount + 1)) :
      |IM.rowResidual i| ≤ eResidual := by
    exact (rowResidual_lt_of_global_modulus IM T heResidual hCKernel
      (fun s hs t ht ↦ hKernelBound t ht s hs)
      hFmod hKmod rfl hBase hTop hLengths i).le
  have hSmall : eDiagonal + r / 8 + 4 * eCenter * CKernel + eResidual ≤
      kappa * (M.width anchorCell / 2) / 16 := by
    change r / 8 + r / 8 + 4 * eCenter * CKernel + r / 8 ≤ r
    linarith [heCenterContribution]
  obtain ⟨actualEquiv, hactual, hinv, _hpaper⟩ :=
    exists_canonical_projected_inverse_and_paper_solutions M hdelta hnk hWk
      hWTwo Sk anchorCell hInteriorLower hInteriorUpper
      hAnchorLength hkappa hgap heCenter.le heCenterHalf hDiagonalAt
      hKernelRows hRelative hResidualRows
      (fun s hs t ht ↦ hKernelBound t ht s hs) hSmall
  refine ⟨hWk, hWTwo, hnk, Sk, hInteriorLower, hInteriorUpper, actualEquiv,
    hactual, ?_⟩
  exact hinv

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
