import Erdos390.Full.ContinuumManyLowArithmeticGaugeOrdinary
import Erdos390.Full.CanonicalEndpointPrefixGeometry
import Erdos390.Full.CanonicalEndpointRawWeightDefectEventually
import Erdos390.Full.CanonicalEndpointOrdinaryRawRowEventually
import Erdos390.Full.CanonicalEndpointMultiAnchorCoverage
import Erdos390.Full.PaperCanonicalPrimeAnchorEventually
import Erdos390.Full.PaperActualSlowRightRowFinite
import Erdos390.Full.CanonicalEndpointWeightedInverseEventually

/-!
# Mesh-uniform ordinary inverse for the canonical endpoint operator

This is the arithmetic conclusion of the moving-low-cell transfer.  All
structural constants, the mesh tolerance, and the prime cutoff are selected
before the two independent mesh parameters.  For each permitted mesh only
the eventual ambient threshold is allowed to vary.
-/

open scoped BigOperators NNReal
open Filter Topology Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open ContinuumCellGraph.ArithmeticGaugeOrdinary
open CompressedArithmeticOperator MovingLowGaugeTransfer
open PaperWeightedInverseExport PoissonDickmanWeightedInverse
open PoissonDickmanKernelBounds PrimeSums
open PaperBridgeFit.PaperActualSlowRightRowFinite

namespace Mesh

private theorem sharpWeightTotal_partition_eq_centerEnergy
    {n W : ℕ} {Band : Type*} [Fintype Band] [DecidableEq Band]
    (P : ArithmeticBandGeometry.Partition n W Band) :
    sharpWeightTotal P.mass P.center = P.centerEnergy := by
  unfold sharpWeightTotal sharpWeight
  unfold ArithmeticBandGeometry.Partition.centerEnergy
    Erdos390.Lemma84.WeightedBandData.centerEnergy
    Erdos390.Lemma84.WeightedBandData.bandNormSq
    Erdos390.Lemma84.WeightedBandData.bandInner
  simp only [pow_two, mul_assoc]

set_option maxHeartbeats 4000000 in
/-- Canonical endpoint arithmetic operator, inverted in the ordinary raw
sup norm.  The hypothesis uses the actual relative-mesh scale
`delta + M.ratio`; a paper-facing `delta + eta` wrapper follows by
`M.ratio_le_eta`. -/
theorem exists_fineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse :
    ∃ Cref : ℝ, 0 < Cref ∧
      ∃ meshTol : ℝ, 0 < meshTol ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + M.ratio ≤ meshTol →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∃ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            let E := canonicalCertificate M hdelta hn hWne S
            ∀ q : RawGaugeSpace P.mass P.center,
              ‖q‖ ≤ Cref *
                ‖projectedRawLinearMap
                  (arithmeticDiagonal (y n) E.lower E.upper)
                  (arithmeticKernel (y n) E.lower E.upper)
                  P.mass P.center
                  (by
                    rw [sharpWeightTotal_partition_eq_centerEnergy P]
                    exact (P.centerEnergy_pos hn).ne') q‖ := by
  obtain ⟨kappa, hkappa, hgap⟩ :=
    exists_transposeQuotient_uniform_gap
      (by norm_num : (0 : ℝ) < 1 / 8)
      (by norm_num : (1 : ℝ) / 8 < 1 / 2)
  obtain ⟨C, hCpos, hKernelProduct⟩ := DickmanBasic.kernel_product_bound
  obtain ⟨CF, hCFpos, hFLipschitz⟩ := exists_F_lipschitz_unit
  obtain ⟨Cquot, hCquot, hQuotient⟩ :=
    exists_covarianceKernelQuotient_bound
  let R : ℝ := 128 * Real.log 4
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let Kabs : ℝ := 144 * C / kappa + 384 * C + 192
  have hKabs : 0 < Kabs := by
    dsimp only [Kabs]
    positivity
  let tau : ℝ := min (1 / 64)
    (min (1 / (16 * (CF + 1))) (1 / (8 * (Kabs + 1))))
  have htau : 0 < tau := by
    dsimp only [tau]
    positivity
  have htauOne : tau ≤ 1 := by
    exact (min_le_left _ _).trans (by norm_num)
  have htau64 : tau ≤ 1 / 64 := min_le_left _ _
  have htauCF : tau ≤ 1 / (16 * (CF + 1)) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have htauAbs : tau ≤ 1 / (8 * (Kabs + 1)) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hKabsTau : Kabs * tau ≤ 1 / 8 := by
    have hKplus : 0 < Kabs + 1 := by linarith
    calc
      Kabs * tau ≤ Kabs * (1 / (8 * (Kabs + 1))) :=
        mul_le_mul_of_nonneg_left htauAbs hKabs.le
      _ = (1 / 8) * (Kabs / (Kabs + 1)) := by
        field_simp [ne_of_gt hKplus]
      _ ≤ (1 / 8) * 1 := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact (div_le_one hKplus).2 (by linarith)
      _ = 1 / 8 := by ring
  let gaugeRatio : ℝ := 96
  let CmainBound : ℝ := max 2
    (16 / kappa * (2 / tau + 4 * C * tau) + gaugeRatio * 2)
  have hCmainBound : 0 < CmainBound :=
    (by norm_num : (0 : ℝ) < 2) |>.trans_le (le_max_left _ _)
  have hOneR : 0 < 1 + R := by linarith
  let errorTarget : ℝ := 1 / (32 * CmainBound * (1 + R))
  have hErrorTarget : 0 < errorTarget := by
    dsimp only [errorTarget]
    positivity
  let residualTarget : ℝ := min tau errorTarget
  have hResidualTarget : 0 < residualTarget :=
    lt_min htau hErrorTarget
  have hResidualTau : residualTarget ≤ tau := min_le_left _ _
  have hResidualError : residualTarget ≤ errorTarget := min_le_right _ _
  let weightTarget : ℝ := min (1 / 256) (tau / 32)
  have hWeightTarget : 0 < weightTarget := by
    dsimp only [weightTarget]
    positivity
  have hWeight256 : weightTarget ≤ 1 / 256 := min_le_left _ _
  have hWeightTau : weightTarget ≤ tau / 32 := min_le_right _ _
  obtain ⟨continuumMeshTol, hContinuumMeshTol, hFmod, hKmod⟩ :=
    exists_uniform_cell_oscillation_modulus
      (div_pos hResidualTarget (by norm_num : (0 : ℝ) < 10))
      (div_pos hResidualTarget (by norm_num : (0 : ℝ) < 10))
  let meshTol : ℝ := min (tau / 2)
    (min (1 / 16) continuumMeshTol)
  have hmeshTol : 0 < meshTol := by
    dsimp only [meshTol]
    positivity
  obtain ⟨CRow, hCRow, Wrow, hRowEvent⟩ :=
    exists_cutoff_before_mesh_eventually_canonical_ordinaryRawRowError
  have hFixedTerm : Tendsto (fun W : ℕ ↦
      CRow / Real.log (W : ℝ) ^ 3) atTop (nhds 0) := by
    have hLog : Tendsto (fun W : ℕ ↦ Real.log (W : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hInv := tendsto_inv_atTop_zero.comp hLog
    have h := (tendsto_const_nhds : Tendsto (fun _W : ℕ ↦ CRow)
      atTop (nhds CRow)).mul (hInv.pow 3)
    simpa only [Function.comp_apply, mul_zero,
      zero_pow (by norm_num : 3 ≠ 0), div_eq_mul_inv, inv_pow] using h
  obtain ⟨Wfixed, hWfixed⟩ := eventually_atTop.1
    (hFixedTerm.eventually
      (eventually_le_nhds (half_pos hErrorTarget)))
  let W₀ : ℕ := max 2 (max Wrow (max Wfixed
    (max canonicalRawWeightDefectCutoff canonicalPrimeAnchorCutoff)))
  let Cref : ℝ := 8 * CmainBound
  have hCref : 0 < Cref := by dsimp only [Cref]; positivity
  refine ⟨Cref, hCref, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  have hWTwo : 2 ≤ W := (le_max_left 2 _).trans hW
  have hWne : W ≠ 0 := by omega
  have hWrow : Wrow ≤ W := by
    exact ((le_max_left Wrow _).trans (le_max_right 2 _)).trans hW
  have hWfixed' : Wfixed ≤ W := by
    exact ((le_max_left Wfixed _).trans (le_max_right Wrow _)).trans
      ((le_max_right 2 _).trans hW)
  have hWweight : canonicalRawWeightDefectCutoff ≤ W := by
    exact ((le_max_left canonicalRawWeightDefectCutoff
      canonicalPrimeAnchorCutoff).trans (le_max_right Wfixed _)).trans
        ((le_max_right Wrow _).trans ((le_max_right 2 _).trans hW))
  have hWanchor : canonicalPrimeAnchorCutoff ≤ W := by
    exact ((le_max_right canonicalRawWeightDefectCutoff
      canonicalPrimeAnchorCutoff).trans (le_max_right Wfixed _)).trans
        ((le_max_right Wrow _).trans ((le_max_right 2 _).trans hW))
  have hdeltaMesh : delta < meshTol := by
    linarith [M.ratio_pos]
  have hratioMesh : M.ratio < meshTol := by
    linarith [hdelta]
  have hdeltaTau : delta < tau :=
    hdeltaMesh.trans_le ((min_le_left _ _).trans (by linarith))
  have hratioTau : M.ratio ≤ tau / 2 :=
    hratioMesh.le.trans (min_le_left _ _)
  have hdeltaSmall : delta < (1 / 16 : ℝ) :=
    hdeltaMesh.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hwidthSmall : ∀ k : Fin M.cellCount,
      M.width k < (1 / 16 : ℝ) := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt
      (hratioMesh.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hLengthFineLow : delta < continuumMeshTol :=
    hdeltaMesh.trans_le
      ((min_le_right _ _).trans (min_le_right _ _))
  have hLengthFinePositive : ∀ k : Fin M.cellCount,
      M.width k < continuumMeshTol := by
    intro k
    exact (M.width_le_ratio hdelta k).trans_lt
      (hratioMesh.trans_le
        ((min_le_right _ _).trans (min_le_right _ _)))
  obtain ⟨anchors, anchor, hAnchor, hIdealLower,
      hIdealUpper, hIdealMass⟩ :=
    M.exists_interiorAnchorBlock hdelta hdeltaSmall hwidthSmall
  have hAnchors : anchors.Nonempty := ⟨anchor, hAnchor⟩
  have hIdealAboveTau : ∀ k ∈ anchors, tau < M.lower k := by
    intro k hk
    exact htau64.trans_lt (by
      have hkLower := hIdealLower k hk
      norm_num at hkLower ⊢
      linarith)
  have hTauRatioSmall : tau + M.ratio < 1 := by
    calc
      tau + M.ratio ≤ tau + tau / 2 := add_le_add le_rfl hratioTau
      _ ≤ (1 / 64 : ℝ) + 1 / 128 := by linarith
      _ < 1 := by norm_num
  letI : Nonempty (M.prefixHigh tau htauOne) :=
    M.prefixHigh_nonempty hdelta htauOne hTauRatioSmall
  have hFixedSmall : CRow / Real.log (W : ℝ) ^ 3 ≤ errorTarget / 2 :=
    hWfixed W hWfixed'
  have hRowN := hRowEvent M hdelta W hWrow
    (errorTarget / 2) (half_pos hErrorTarget)
  have hWeightN := canonicalRawWeightDefectCutoff_eventually
    W hWweight M hdelta hWeightTarget
  have hCoverageN := eventually_canonical_anchorBlock_coverage M hdelta
    hWne hWTwo anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hPrimeAnchorN := canonicalPrimeAnchorCutoff_eventually M hdelta
    W hWanchor anchors hAnchors hIdealLower hIdealUpper hIdealMass
  have hBoundaryN := eventually_canonicalPrefixBoundary_between M hdelta
    htauOne hdeltaTau hratioTau W
  have hLengthN := eventually_all_actualCoordinateLengths_lt M hdelta
    hLengthFineLow hLengthFinePositive W
  let beta : ℝ := residualTarget / (5 * (Cquot + 1))
  have hbeta : 0 < beta := by
    dsimp only [beta]
    positivity
  have hTailN := eventually_canonical_twoTails_lt M W hbeta
  have hBandTN := eventually_bandTReciprocalSum_le W
  filter_upwards [hRowN, hWeightN, hCoverageN, hPrimeAnchorN,
    hBoundaryN, hLengthN, hTailN, hBandTN] with n hRowAt hWeightAt
      hCoverageAt hPrimeAnchorAt hBoundaryAt hLengthAt hTailAt hBandTAt
  obtain ⟨hWr, hnr, S, hRows⟩ := hRowAt
  obtain ⟨hnc, hCoverageAll⟩ := hCoverageAt
  obtain ⟨hWa, hna, hPrimeAnchorAll⟩ := hPrimeAnchorAt
  obtain ⟨hInteriorLowerRaw, hInteriorUpperRaw, hAnchorMassRaw⟩ :=
    hCoverageAll S
  let hInteriorLower : ∀ k ∈ anchors, (1 / 8 : ℝ) ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnr hWr S).lower
          (positiveBand M k) : ℝ) := hInteriorLowerRaw
  let hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hnr hWr S).upper
          (positiveBand M k) : ℝ) ≤ 1 - (1 / 8 : ℝ) :=
    hInteriorUpperRaw
  let P := canonicalPartition M hdelta hnr hWr S
  let E := canonicalCertificate M hdelta hnr hWr S
  let IM := canonicalIntervalMeshOfAnchors M hdelta hnr hWr hWTwo S
    (1 / 8) anchors hAnchors hInteriorLower hInteriorUpper
  let split := M.prefixSplitEquiv tau htauOne
  let T := canonicalTwoTailCertificateOfAnchors M hdelta hnr hWr hWTwo S
    (1 / 8) anchors hAnchors anchor hAnchor hInteriorLower hInteriorUpper
  have hAnchorMass : (1 / 8 : ℝ) ≤ ∑ j, IM.anchor j := by
    simpa only [IM, Subsingleton.elim hnc hnr,
      Subsingleton.elim hWTwo hWTwo] using hAnchorMassRaw
  have hPrimeAnchor :
      let A := canonicalPrimeAnchorSet M P anchors
      (∀ p ∈ A, tPrime n p.1 ∈ Icc (1 / 8 : ℝ) (1 - 1 / 8)) ∧
        (1 / 8 : ℝ) ≤
          FiniteAnchoredDirichletQuadratic.anchorMass
            (PrimeSquarefreeDirichletGeometry.primeWeight n) A := by
    simpa only [P, Subsingleton.elim hna hnr,
      Subsingleton.elim hWa hWr] using hPrimeAnchorAll S
  have hRawDefect :
      (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - endpointContinuumMoment M n W j|) ≤
          weightTarget := by
    simpa only [P, Subsingleton.elim hWr hWne] using
      hWeightAt hnr hWr S
  have hBoundaryLower : tau / 2 ≤
      canonicalPrefixBoundary M n W tau htauOne := hBoundaryAt.1
  have hBoundaryUpper :
      canonicalPrefixBoundary M n W tau htauOne ≤ 2 * tau :=
    hBoundaryAt.2
  have hLengths (j : Fin (M.cellCount + 1)) :
      IM.length j < continuumMeshTol := by
    simpa only [IM, canonicalIntervalMeshOfAnchors, IntervalMesh.length,
      actualCutoffCoordinate] using hLengthAt j
  have hBase : T.base < beta := by
    simpa only [T, canonicalTwoTailCertificateOfAnchors,
      canonicalTwoTailCertificate, actualCutoffCoordinate,
      fullCutoff_zero] using hTailAt.1
  have hTop : 1 - T.upperEnd < beta := by
    simpa only [T, canonicalTwoTailCertificateOfAnchors,
      canonicalTwoTailCertificate, actualCutoffCoordinate] using hTailAt.2
  have hResidual (i : Fin (M.cellCount + 1)) :
      |IM.rowResidual i| ≤ residualTarget := by
    exact (rowResidual_lt_of_global_modulus IM T hResidualTarget hCquot
      (fun s hs t ht ↦ hQuotient t ht s hs) hFmod hKmod rfl
      hBase hTop hLengths i).le
  have hContinuumWeight (j : Fin (M.cellCount + 1)) :
      IM.harmonicMass j * IM.center j =
        endpointContinuumMoment M n W j := by
    rw [IM.harmonicMass_mul_center_eq_length]
    simpa only [IM, canonicalIntervalMeshOfAnchors, IntervalMesh.length]
      using (endpointContinuumMoment_eq_coordinateLength
        (W := W) M hnr j).symm
  have hRawWeightDefect :
      (∑ j : Fin (M.cellCount + 1),
        |P.mass j * P.center j - IM.harmonicMass j * IM.center j|) ≤
          weightTarget := by
    simpa only [hContinuumWeight] using hRawDefect
  have hEnergy : (1 / 64 : ℝ) ≤ P.centerEnergy := by
    let A := canonicalPrimeAnchorSet M P anchors
    have hE := epsilon_mul_anchorMass_le_centerEnergy M P hnr
      (by norm_num : (0 : ℝ) ≤ 1 / 8) anchors hPrimeAnchor.1
    calc
      (1 / 64 : ℝ) = (1 / 8 : ℝ) * (1 / 8 : ℝ) := by norm_num
      _ ≤ (1 / 8 : ℝ) *
          FiniteAnchoredDirichletQuadratic.anchorMass
            (PrimeSquarefreeDirichletGeometry.primeWeight n) A := by
        exact mul_le_mul_of_nonneg_left hPrimeAnchor.2 (by norm_num)
      _ ≤ P.centerEnergy := hE
  have hMomentRatio :
      (1 : ℝ) * (∑ i, P.mass i * P.center i) ≤
        R * sharpWeightTotal P.mass P.center := by
    have htotal : (∑ i, P.mass i * P.center i) =
        bandTReciprocalSum n W := P.sum_mass_mul_center_eq_bandTReciprocalSum
    have henergyId : sharpWeightTotal P.mass P.center = P.centerEnergy := by
      exact sharpWeightTotal_partition_eq_centerEnergy P
    rw [one_mul, htotal, henergyId]
    calc
      bandTReciprocalSum n W ≤ 2 * Real.log 4 := hBandTAt
      _ = R * (1 / 64) := by dsimp only [R]; ring
      _ ≤ R * P.centerEnergy :=
        mul_le_mul_of_nonneg_left hEnergy hR
  have hLowCenter (l : M.prefixLow tau htauOne) :
      IM.center (split (.inl l)) ≤ 2 * tau := by
    exact (canonicalPrefix_low_center_le_boundary M hdelta hnr hWr
      hWTwo S htauOne anchors hAnchors hInteriorLower hInteriorUpper l).trans
        hBoundaryUpper
  have hHighCenterLower (k : M.prefixHigh tau htauOne) :
      tau / 2 ≤ IM.center (split (.inr k)) := by
    exact hBoundaryLower.trans
      (canonicalPrefix_boundary_le_high_center M hdelta hnr hWr
        hWTwo S htauOne anchors hAnchors hInteriorLower hInteriorUpper k)
  have hHighCenterUpper (k : M.prefixHigh tau htauOne) :
      IM.center (split (.inr k)) ≤ 1 :=
    (IM.center_le_upper _).trans (IM.upper_le_one _)
  have hLowLength :
      (∑ l : M.prefixLow tau htauOne, IM.length (split (.inl l))) ≤
        2 * tau := by
    exact (sum_canonicalPrefix_low_length_le_boundary M hdelta hnr hWr
      hWTwo S htauOne anchors hAnchors hInteriorLower hInteriorUpper).trans
        hBoundaryUpper
  have hTotalLength : (∑ i, IM.length i) ≤ 1 :=
    sum_canonical_all_length_le_one M hdelta hnr hWr hWTwo S
      anchors hAnchors hInteriorLower hInteriorUpper
  have hHighAnchor : (1 / 8 : ℝ) ≤
      ∑ k : M.prefixHigh tau htauOne, IM.splitHighAnchor split k := by
    rw [sum_canonicalPrefix_high_anchor_eq_all M hdelta hnr hWr hWTwo S
      htauOne anchors hAnchors hIdealAboveTau hInteriorLower hInteriorUpper]
    exact hAnchorMass
  have hDiagonalLow (l : M.prefixLow tau htauOne) :
      |IM.normalizedDiagonalCell (split (.inl l)) - 1| ≤ 1 / 4 := by
    apply IM.abs_normalizedDiagonalCell_sub_one_le
    intro s hs
    have hsUnit := IM.cell_mem_unit hs
    have hUpperBoundary : IM.upper (split (.inl l)) ≤
        canonicalPrefixBoundary M n W tau htauOne := by
      have hmono : Monotone (fullCutoff M n W) :=
        fullCutoff_monotone M hdelta hnr (W_le_first_fullCutoff M S)
      have hidx : (split (.inl l)).1 + 1 ≤
          M.prefixIndex tau htauOne + 1 := by
        change l.1 + 1 ≤ M.prefixIndex tau htauOne + 1
        have hl : l.1 < M.prefixIndex tau htauOne + 1 := l.2
        omega
      have hcut := hmono hidx
      have hy : 1 < y n := by
        rw [← Real.log_pos_iff (Scale.y_pos
          (Nat.zero_lt_of_lt hnr)).le]
        rw [Scale.log_y (Nat.zero_lt_of_lt hnr)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hnr))
      have hlowerTwo : 2 ≤ fullCutoff M n W ((split (.inl l)).1 + 1) :=
        hWTwo.trans (hmono (Nat.zero_le _))
      have hcoord := realLogCoordinate_mono_nat hy hlowerTwo hcut
      simpa only [IM, canonicalIntervalMeshOfAnchors_upper,
        canonicalCertificate_upper, canonicalPrefixBoundary,
        actualCutoffCoordinate] using hcoord
    have hsUpper' : s ≤ 2 * tau :=
      hs.2.trans (hUpperBoundary.trans hBoundaryUpper)
    have hLip := hFLipschitz s hsUnit 0 (by norm_num)
    simp only [DickmanBasic.F_zero] at hLip
    calc
      |DickmanBasic.F s - 1| ≤ CF * |s - 0| := hLip
      _ = CF * s := by rw [sub_zero, abs_of_nonneg hsUnit.1]
      _ ≤ CF * (2 * tau) :=
        mul_le_mul_of_nonneg_left hsUpper' hCFpos.le
      _ ≤ 1 / 4 := by
        have hCFtau : CF * tau ≤ 1 / 16 := by
          have hCFplus : 0 < CF + 1 := by linarith
          calc
            CF * tau ≤ CF * (1 / (16 * (CF + 1))) :=
              mul_le_mul_of_nonneg_left htauCF hCFpos.le
            _ = (1 / 16) * (CF / (CF + 1)) := by
              field_simp [ne_of_gt hCFplus]
            _ ≤ (1 / 16) * 1 := by
              apply mul_le_mul_of_nonneg_left _ (by norm_num)
              exact (div_le_one hCFplus).2 (by linarith)
            _ = 1 / 16 := by ring
        nlinarith
  have hRowError (q : RawGaugeSpace P.mass P.center)
      (i : Fin (M.cellCount + 1)) :
      |rawOperator (arithmeticDiagonal (y n) E.lower E.upper)
          (arithmeticKernel (y n) E.lower E.upper) q.1 i -
        rawOperator IM.normalizedDiagonalCell IM.normalizedKernelCell
          q.1 i| ≤ errorTarget * ‖q‖ := by
    have hraw := hRows q.1 i
    have hDiagId (j : Fin (M.cellCount + 1)) :
        IM.normalizedDiagonalCell j =
          continuumDiagonal (y n) E.lower E.upper j := by
      exact IM.normalizedDiagonalCell_eq_endpointContinuum
        (y n) E.lower E.upper (fun _ ↦ rfl) (fun _ ↦ rfl) j
    have hKernelId (j k : Fin (M.cellCount + 1)) :
        IM.normalizedKernelCell j k =
          continuumKernel (y n) E.lower E.upper j k := by
      exact IM.normalizedKernelCell_eq_endpointContinuum
        (y n) E.lower E.upper (fun _ ↦ rfl) (fun _ ↦ rfl) j k
    have hcoeff : CRow / Real.log (W : ℝ) ^ 3 + errorTarget / 2 ≤
        errorTarget := by linarith
    have hDiagFun : IM.normalizedDiagonalCell =
        continuumDiagonal (y n) E.lower E.upper := funext hDiagId
    have hKernelFun : IM.normalizedKernelCell =
        continuumKernel (y n) E.lower E.upper := by
      funext j k
      exact hKernelId j k
    rw [hDiagFun, hKernelFun]
    simpa only [E, canonicalCertificate_lower, canonicalCertificate_upper]
      using hraw.trans
        (mul_le_mul_of_nonneg_right hcoeff (norm_nonneg q.1))
  -- The remaining inequalities are finite arithmetic consequences of the
  -- preceding literal bounds.
  have hAlphaUpper (i : Fin (M.cellCount + 1)) : P.center i ≤ 1 :=
    (P.center_mem_zero_one hnr i).2
  have hLowArithmetic :
      (∑ l : M.prefixLow tau htauOne,
        P.mass (split (.inl l)) * P.center (split (.inl l))) ≤
        3 * tau := by
    have hdefLow :
        (∑ l : M.prefixLow tau htauOne,
          |P.mass (split (.inl l)) * P.center (split (.inl l)) -
            IM.length (split (.inl l))|) ≤ weightTarget := by
      calc
        _ ≤ ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j - IM.length j| := by
          rw [← Equiv.sum_comp split]
          rw [Fintype.sum_sum_type]
          exact le_add_of_nonneg_right
            (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        _ = ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j -
              IM.harmonicMass j * IM.center j| := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [IM.harmonicMass_mul_center_eq_length]
        _ ≤ weightTarget := hRawWeightDefect
    have hsum :
        (∑ l : M.prefixLow tau htauOne,
          P.mass (split (.inl l)) * P.center (split (.inl l))) ≤
          (∑ l : M.prefixLow tau htauOne,
            IM.length (split (.inl l))) + weightTarget := by
      calc
        _ ≤ ∑ l : M.prefixLow tau htauOne,
            (IM.length (split (.inl l)) +
              |P.mass (split (.inl l)) * P.center (split (.inl l)) -
                IM.length (split (.inl l))|) := by
          apply Finset.sum_le_sum
          intro l _hl
          linarith [le_abs_self
            (P.mass (split (.inl l)) * P.center (split (.inl l)) -
              IM.length (split (.inl l)))]
        _ = (∑ l : M.prefixLow tau htauOne,
              IM.length (split (.inl l))) +
            ∑ l : M.prefixLow tau htauOne,
              |P.mass (split (.inl l)) * P.center (split (.inl l)) -
                IM.length (split (.inl l))| := Finset.sum_add_distrib
        _ ≤ (∑ l : M.prefixLow tau htauOne,
              IM.length (split (.inl l))) + weightTarget :=
          add_le_add le_rfl hdefLow
    exact hsum.trans (by linarith [hLowLength, hWeightTau, htau])
  have hHighMixed : tau / 32 ≤
      ∑ k : M.prefixHigh tau htauOne,
        P.mass (split (.inr k)) * P.center (split (.inr k)) *
          IM.center (split (.inr k)) := by
    have hContinuumHigh : tau / 16 ≤
        ∑ k : M.prefixHigh tau htauOne,
          IM.length (split (.inr k)) * IM.center (split (.inr k)) := by
      have hsharp := IM.amin_mul_highAnchor_le_highSharpWeight split
        (show 0 ≤ tau / 2 by positivity) hHighCenterLower
      calc
        tau / 16 = (tau / 2) * (1 / 8) := by ring
        _ ≤ (tau / 2) *
            (∑ k : M.prefixHigh tau htauOne,
              IM.splitHighAnchor split k) :=
          mul_le_mul_of_nonneg_left hHighAnchor (by positivity)
        _ ≤ ∑ k : M.prefixHigh tau htauOne,
            IM.harmonicMass (split (.inr k)) *
              IM.center (split (.inr k)) ^ 2 := hsharp
        _ = ∑ k : M.prefixHigh tau htauOne,
            IM.length (split (.inr k)) * IM.center (split (.inr k)) := by
          apply Finset.sum_congr rfl
          intro k _hk
          exact IM.harmonicMass_mul_center_sq_eq (split (.inr k))
    have hdefHigh :
        |(∑ k : M.prefixHigh tau htauOne,
            P.mass (split (.inr k)) * P.center (split (.inr k)) *
              IM.center (split (.inr k))) -
          ∑ k : M.prefixHigh tau htauOne,
            IM.length (split (.inr k)) * IM.center (split (.inr k))| ≤
          weightTarget := by
      rw [← Finset.sum_sub_distrib]
      calc
        |∑ k : M.prefixHigh tau htauOne,
            (P.mass (split (.inr k)) * P.center (split (.inr k)) *
                IM.center (split (.inr k)) -
              IM.length (split (.inr k)) * IM.center (split (.inr k)))| ≤
            ∑ k : M.prefixHigh tau htauOne,
              |P.mass (split (.inr k)) * P.center (split (.inr k)) -
                IM.length (split (.inr k))| := by
          calc
            _ ≤ ∑ k : M.prefixHigh tau htauOne,
                |P.mass (split (.inr k)) * P.center (split (.inr k)) -
                  IM.length (split (.inr k))| *
                    |IM.center (split (.inr k))| := by
              calc
                _ ≤ ∑ k : M.prefixHigh tau htauOne,
                    |P.mass (split (.inr k)) * P.center (split (.inr k)) *
                        IM.center (split (.inr k)) -
                      IM.length (split (.inr k)) *
                        IM.center (split (.inr k))| :=
                  Finset.abs_sum_le_sum_abs _ _
                _ = _ := by
                  apply Finset.sum_congr rfl
                  intro k _hk
                  rw [show
                    P.mass (split (.inr k)) * P.center (split (.inr k)) *
                        IM.center (split (.inr k)) -
                      IM.length (split (.inr k)) * IM.center (split (.inr k)) =
                        (P.mass (split (.inr k)) *
                          P.center (split (.inr k)) -
                          IM.length (split (.inr k))) *
                            IM.center (split (.inr k)) by ring,
                    abs_mul]
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro k _hk
              rw [abs_of_pos (IM.center_pos _)]
              simpa only [mul_one] using
                (mul_le_mul_of_nonneg_left (hHighCenterUpper k)
                  (abs_nonneg
                    (P.mass (split (.inr k)) * P.center (split (.inr k)) -
                      IM.length (split (.inr k)))))
        _ ≤ ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j - IM.length j| := by
          rw [← Equiv.sum_comp split, Fintype.sum_sum_type]
          exact le_add_of_nonneg_left
            (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)
        _ = ∑ j : Fin (M.cellCount + 1),
            |P.mass j * P.center j -
              IM.harmonicMass j * IM.center j| := by
          apply Finset.sum_congr rfl
          intro j _hj
          rw [IM.harmonicMass_mul_center_eq_length]
        _ ≤ weightTarget := hRawWeightDefect
    have hleft := neg_le_of_abs_le hdefHigh
    linarith [hContinuumHigh, hWeightTau]
  have hMixedGauge :
      (∑ l : M.prefixLow tau htauOne,
        P.mass (split (.inl l)) * P.center (split (.inl l))) ≤
        gaugeRatio *
          (∑ k : M.prefixHigh tau htauOne,
            P.mass (split (.inr k)) * P.center (split (.inr k)) *
              IM.center (split (.inr k))) := by
    dsimp only [gaugeRatio]
    nlinarith [hLowArithmetic, hHighMixed]
  have hEpsLowBound :
      (residualTarget + C * (2 * tau) * 1) / (1 - (1 / 4 : ℝ)) ≤
        (4 * C + 2) * tau := by
    have hres := hResidualTau
    have hnonneg : 0 ≤ C * tau := mul_nonneg hCpos.le htau.le
    field_simp
    nlinarith
  have hEpsSmall :
      (residualTarget + C * (2 * tau) * 1) / (1 - (1 / 4 : ℝ)) ≤
        1 / 8 := by
    have hCoeff : 4 * C + 2 ≤ Kabs := by
      dsimp only [Kabs]
      have hdiv : 0 ≤ 144 * C / kappa := by positivity
      nlinarith
    exact hEpsLowBound.trans
      ((mul_le_mul_of_nonneg_right hCoeff htau.le).trans hKabsTau)
  have hInvAnchor : 1 / (kappa * ∑ k : M.prefixHigh tau htauOne,
      IM.splitHighAnchor split k) ≤ 8 / kappa := by
    have hsumPos : 0 < ∑ k : M.prefixHigh tau htauOne,
        IM.splitHighAnchor split k := (by norm_num : (0 : ℝ) < 1 / 8)
          |>.trans_le hHighAnchor
    apply (div_le_div_iff₀ (mul_pos hkappa hsumPos) hkappa).2
    have hmul := mul_le_mul_of_nonneg_left hHighAnchor hkappa.le
    nlinarith
  have hAbsorbLow :
      let epsLow :=
        (residualTarget + C * (2 * tau) * 1) / (1 - (1 / 4 : ℝ))
      max epsLow
        (1 *
          (2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
              ((C * (2 * tau) * (2 * tau)) / (tau / 2) +
                (C * (2 * tau)) * epsLow) +
            gaugeRatio * epsLow)) ≤ 1 / 2 := by
    dsimp only
    apply max_le
    · exact hEpsSmall.trans (by norm_num)
    · have htauNe : tau ≠ 0 := ne_of_gt htau
      have hfirst : (C * (2 * tau) * (2 * tau)) / (tau / 2) =
          8 * C * tau := by field_simp [htauNe]; ring
      rw [hfirst]
      have hInsideNonneg : 0 ≤
          8 * C * tau +
            C * (2 * tau) *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ))) := by positivity
      have hInside :
          8 * C * tau + C * (2 * tau) *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ))) ≤ 9 * C * tau := by
        have hmul :
            C * (2 * tau) *
                ((residualTarget + C * (2 * tau) * 1) /
                  (1 - (1 / 4 : ℝ))) ≤
              C * (2 * tau) * (1 / 8 : ℝ) := by
          exact mul_le_mul_of_nonneg_left hEpsSmall
            (mul_nonneg hCpos.le
              (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) htau.le))
        nlinarith
      have hinvMul :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) ≤ 16 / kappa := by
        calc
          _ ≤ 2 * (8 / kappa) :=
            mul_le_mul_of_nonneg_left hInvAnchor (by norm_num)
          _ = 16 / kappa := by ring
      have hfirstTerm :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
            (8 * C * tau + C * (2 * tau) *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ)))) ≤
          (144 * C / kappa) * tau := by
        calc
          _ ≤ (16 / kappa) * (9 * C * tau) :=
            mul_le_mul hinvMul hInside hInsideNonneg
              (by positivity)
          _ = (144 * C / kappa) * tau := by ring
      have hsecondTerm : gaugeRatio *
          ((residualTarget + C * (2 * tau) * 1) /
            (1 - (1 / 4 : ℝ))) ≤
          (384 * C + 192) * tau := by
        dsimp only [gaugeRatio]
        nlinarith [hEpsLowBound]
      have htotal :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
              (8 * C * tau + C * (2 * tau) *
                ((residualTarget + C * (2 * tau) * 1) /
                  (1 - (1 / 4 : ℝ)))) +
            gaugeRatio *
              ((residualTarget + C * (2 * tau) * 1) /
                (1 - (1 / 4 : ℝ))) ≤ Kabs * tau := by
        dsimp only [Kabs]
        linarith
      norm_num only [gaugeRatio, one_mul] at htotal ⊢
      exact htotal.trans
        (hKabsTau.trans (by norm_num : (1 / 8 : ℝ) ≤ 1 / 2))
  have hClow : (1 / (1 - (1 / 4 : ℝ))) ≤ 2 := by norm_num
  have hCmainActual :
      max (1 / (1 - (1 / 4 : ℝ)))
        (1 *
          (2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
              (1 / (tau / 2) +
                (C * (2 * tau)) * (1 / (1 - (1 / 4 : ℝ)))) +
            gaugeRatio * (1 / (1 - (1 / 4 : ℝ))))) ≤
        CmainBound := by
    apply max_le
    · exact hClow.trans (le_max_left _ _)
    · have htauNe : tau ≠ 0 := ne_of_gt htau
      have hInvTau : 1 / (tau / 2) = 2 / tau := by
        field_simp [htauNe]
      rw [hInvTau]
      have hInside :
          2 / tau + C * (2 * tau) * (1 / (1 - (1 / 4 : ℝ))) ≤
            2 / tau + 4 * C * tau := by
        norm_num at hClow
        nlinarith [mul_nonneg hCpos.le htau.le]
      have hInsideNonneg : 0 ≤
          2 / tau + C * (2 * tau) * (1 / (1 - (1 / 4 : ℝ))) := by
        positivity
      have hfirst :
          2 * (1 / (kappa *
              ∑ k : M.prefixHigh tau htauOne,
                IM.splitHighAnchor split k)) *
            (2 / tau + C * (2 * tau) *
              (1 / (1 - (1 / 4 : ℝ)))) ≤
          16 / kappa * (2 / tau + 4 * C * tau) := by
        have hinvMul : 2 * (1 / (kappa *
            ∑ k : M.prefixHigh tau htauOne,
              IM.splitHighAnchor split k)) ≤ 16 / kappa := by
          calc
            _ ≤ 2 * (8 / kappa) :=
              mul_le_mul_of_nonneg_left hInvAnchor (by norm_num)
            _ = 16 / kappa := by ring
        exact mul_le_mul hinvMul hInside hInsideNonneg (by positivity)
      have hgauge : gaugeRatio * (1 / (1 - (1 / 4 : ℝ))) ≤
          gaugeRatio * 2 :=
        mul_le_mul_of_nonneg_left hClow (by dsimp only [gaugeRatio]; norm_num)
      calc
        1 *
            (2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (2 / tau + C * (2 * tau) *
                  (1 / (1 - (1 / 4 : ℝ)))) +
              gaugeRatio * (1 / (1 - (1 / 4 : ℝ)))) =
            2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (2 / tau + C * (2 * tau) *
                  (1 / (1 - (1 / 4 : ℝ)))) +
              gaugeRatio * (1 / (1 - (1 / 4 : ℝ))) := one_mul _
        _ ≤ 16 / kappa * (2 / tau + 4 * C * tau) +
            gaugeRatio * 2 := add_le_add hfirst hgauge
        _ ≤ CmainBound := by
          dsimp only [CmainBound]
          exact le_max_right _ _
  have hAbsorbArithmetic :
      let Clow := 1 / (1 - (1 / 4 : ℝ))
      let Cmain :=
        max Clow
          (1 *
            (2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (1 / (tau / 2) + (C * (2 * tau)) * Clow) +
              gaugeRatio * Clow))
      4 * Cmain * ((1 + R) * (errorTarget + residualTarget)) ≤ 1 / 2 := by
    dsimp only
    have hErrSum : errorTarget + residualTarget ≤ 2 * errorTarget := by
      linarith [hResidualError]
    have hnonneg : 0 ≤ (1 + R) * (errorTarget + residualTarget) := by
      positivity
    calc
      4 *
          max (1 / (1 - (1 / 4 : ℝ)))
            (1 *
              (2 * (1 / (kappa *
                  ∑ k : M.prefixHigh tau htauOne,
                    IM.splitHighAnchor split k)) *
                  (1 / (tau / 2) +
                    C * (2 * tau) * (1 / (1 - (1 / 4 : ℝ)))) +
                gaugeRatio * (1 / (1 - (1 / 4 : ℝ))))) *
            ((1 + R) * (errorTarget + residualTarget)) ≤
          4 * CmainBound * ((1 + R) * (2 * errorTarget)) := by
        gcongr
      _ = 1 / 4 := by
        dsimp only [errorTarget]
        field_simp [ne_of_gt hCmainBound, ne_of_gt hOneR]
        ring
      _ ≤ 1 / 2 := by norm_num
  have hRawDefectScaled :
      (1 : ℝ) *
          (∑ i, |P.mass i * P.center i -
            IM.harmonicMass i * IM.center i|) ≤
        (1 / 4 : ℝ) * sharpWeightTotal P.mass P.center := by
    rw [one_mul]
    have hweight :
        (∑ i, |P.mass i * P.center i -
          IM.harmonicMass i * IM.center i|) ≤ 1 / 256 :=
      hRawWeightDefect.trans hWeight256
    have henergyId : sharpWeightTotal P.mass P.center = P.centerEnergy := by
      exact sharpWeightTotal_partition_eq_centerEnergy P
    rw [henergyId]
    nlinarith [hEnergy]
  have hBound :=
    ContinuumCellGraph.ArithmeticGaugeOrdinary.IntervalMesh.ordinary_split_arithmetic_projected_raw_bound
    IM split
    (arithmeticDiagonal (y n) E.lower E.upper)
    (arithmeticKernel (y n) E.lower E.upper)
    P.mass P.center
    hCpos.le hKernelProduct hkappa hgap
    ((by norm_num : (0 : ℝ) < 1 / 8).trans_le hHighAnchor)
    (div_pos htau (by norm_num)) hHighCenterLower hHighCenterUpper
    (by norm_num) (by positivity) hLowCenter (by positivity) hLowLength
    (by norm_num) hTotalLength P.data.mass_pos (P.center_pos hnr)
    hAlphaUpper hMixedGauge (by norm_num : (1 / 4 : ℝ) < 1)
    hDiagonalLow hResidualTarget.le hResidual hErrorTarget.le hRowError
    hR hMomentRatio (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    hRawDefectScaled hAbsorbLow hAbsorbArithmetic
  refine ⟨hWr, hnr, S, ?_⟩
  dsimp only
  intro q
  have hq := hBound q
  have hconstant :
      8 *
        max (1 / (1 - (1 / 4 : ℝ)))
          (1 *
            (2 * (1 / (kappa *
                ∑ k : M.prefixHigh tau htauOne,
                  IM.splitHighAnchor split k)) *
                (1 / (tau / 2) +
                  (C * (2 * tau)) * (1 / (1 - (1 / 4 : ℝ)))) +
              gaugeRatio * (1 / (1 - (1 / 4 : ℝ))))) ≤ Cref := by
    dsimp only [Cref]
    exact mul_le_mul_of_nonneg_left hCmainActual (by norm_num)
  exact hq.trans (mul_le_mul_of_nonneg_right hconstant (norm_nonneg _))

/-- Paper-scale wrapper.  The displayed mesh request is `delta + eta`,
while the proof uses only the smaller actual scale `delta + M.ratio`. -/
theorem exists_paperFineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse :
    ∃ Cref : ℝ, 0 < Cref ∧
      ∃ w₀ : ℝ, 0 < w₀ ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (M : Mesh delta eta) (hdelta : 0 < delta),
      delta + eta ≤ w₀ →
      ∀ᶠ n : ℕ in atTop,
        ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
          ∃ S : ScaleSeparation M n W,
            let P := canonicalPartition M hdelta hn hWne S
            let E := canonicalCertificate M hdelta hn hWne S
            ∀ q : RawGaugeSpace P.mass P.center,
              ‖q‖ ≤ Cref *
                ‖projectedRawLinearMap
                  (arithmeticDiagonal (y n) E.lower E.upper)
                  (arithmeticKernel (y n) E.lower E.upper)
                  P.mass P.center
                  (by
                    rw [sharpWeightTotal_partition_eq_centerEnergy P]
                    exact (P.centerEnergy_pos hn).ne') q‖ := by
  obtain ⟨Cref, hCref, meshTol, hmeshTol, W₀, hmain⟩ :=
    exists_fineMesh_cutoff_eventually_canonical_ordinaryProjectedRaw_inverse
  refine ⟨Cref, hCref, meshTol, hmeshTol, W₀, ?_⟩
  intro W hW delta eta M hdelta hfine
  exact hmain W hW M hdelta (by linarith [M.ratio_le_eta])

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
