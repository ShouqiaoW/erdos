import Erdos390.Full.CanonicalEndpointWeightedInverseAttachment
import Erdos390.Full.CanonicalEndpointMultiAnchorCoverage

/-!
# Weighted inverse with a positive-mass canonical anchor block

This is the nondegenerate refinement of the singleton attachment.  The
Neumann radius and inverse constant use an external lower bound for the
*total* interior anchor mass.  Consequently they need not deteriorate as a
permitted mesh is refined.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator MovingLowGaugeTransfer
open UniformMeshArithmeticInverse
open PaperWeightedInverseExport
open PoissonDickmanWeightedInverse

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

def multiCanonicalCenterRatioError
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors : anchors.Nonempty)
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon)
    (i j : Fin (M.cellCount + 1)) : ℝ :=
  let P := canonicalPartition M hdelta hn hW S
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  |P.center j / P.center i - IM.center j / IM.center i|

theorem multiCanonical_arithmeticGraphRowBudget_le
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchors : Finset (Fin M.cellCount))
    (hAnchors : anchors.Nonempty)
    (anchor : Fin M.cellCount) (hAnchor : anchor ∈ anchors)
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon)
    {eDiagonal eKernel eCenter eResidual CKernel : ℝ}
    (heCenter : 0 ≤ eCenter) (heCenterHalf : eCenter ≤ 1 / 2)
    (hDiagonal : ∀ i : Fin (M.cellCount + 1),
      endpointDiagonalError M n W i ≤ eDiagonal)
    (hKernelRow : ∀ i : Fin (M.cellCount + 1),
      endpointDoubleKernelSharpRowError M hdelta hn hW S i ≤ eKernel)
    (hRelativeCenter : ∀ i : Fin (M.cellCount + 1),
      |(canonicalPartition M hdelta hn hW S).center i /
          (canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
            anchors hAnchors hInteriorLower hInteriorUpper).center i - 1| ≤
        eCenter)
    (hResidual : ∀ i : Fin (M.cellCount + 1),
      |(canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
        anchors hAnchors hInteriorLower hInteriorUpper).rowResidual i| ≤
          eResidual)
    (hKernelBound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |ConditionedPoissonLimit.covarianceKernelQuotient t s| ≤ CKernel)
    (i : Fin (M.cellCount + 1)) :
    let P := canonicalPartition M hdelta hn hW S
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
    IM.arithmeticGraphRowBudget
        (endpointDiagonalError M n W)
        (endpointDoubleKernelError M n W)
        (multiCanonicalCenterRatioError M hdelta hn hW hWTwo S epsilon
          anchors hAnchors hInteriorLower hInteriorUpper)
        P.center i ≤
      eDiagonal + eKernel + 4 * eCenter * CKernel + eResidual := by
  let P := canonicalPartition M hdelta hn hW S
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let T := canonicalTwoTailCertificateOfAnchors M hdelta hn hW hWTwo S
    epsilon anchors hAnchors anchor hAnchor hInteriorLower hInteriorUpper
  have hCenterRow :
      (∑ j, |IM.normalizedKernelCell i j| *
        multiCanonicalCenterRatioError M hdelta hn hW hWTwo S epsilon
          anchors hAnchors hInteriorLower hInteriorUpper i j) ≤
        4 * eCenter * CKernel := by
    exact IM.centerRatio_weightedRow_le T P.center heCenter heCenterHalf
      hRelativeCenter hKernelBound i
  change endpointDiagonalError M n W i +
      (∑ j, endpointDoubleKernelError M n W i j *
        |P.center j / P.center i|) +
      (∑ j, |IM.normalizedKernelCell i j| *
        multiCanonicalCenterRatioError M hdelta hn hW hWTwo S epsilon
          anchors hAnchors hInteriorLower hInteriorUpper i j) +
      |IM.rowResidual i| ≤
    eDiagonal + eKernel + 4 * eCenter * CKernel + eResidual
  have hKernel := hKernelRow i
  change (∑ j, endpointDoubleKernelError M n W i j *
      |P.center j / P.center i|) ≤ eKernel at hKernel
  linarith [hDiagonal i, hCenterRow, hResidual i]

/-- Deterministic canonical projected inverse whose constants use a lower
bound for the total anchor block, not the width of one cell. -/
theorem exists_multiAnchor_canonical_projected_inverse
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W) (S : ScaleSeparation M n W)
    {epsilon : ℝ} (anchors : Finset (Fin M.cellCount))
    (hAnchors : anchors.Nonempty)
    (anchor : Fin M.cellCount) (hAnchor : anchor ∈ anchors)
    (hInteriorLower : ∀ k ∈ anchors, epsilon ≤
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M k) : ℝ))
    (hInteriorUpper : ∀ k ∈ anchors,
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M k) : ℝ) ≤ 1 - epsilon)
    {kappa anchorFloor eDiagonal eKernel eCenter eResidual CKernel : ℝ}
    (hkappa : 0 < kappa) (hAnchorFloor : 0 < anchorFloor)
    (hAnchorMass : anchorFloor ≤
      ∑ j, (canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
        anchors hAnchors hInteriorLower hInteriorUpper).anchor j)
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc epsilon (1 - epsilon),
      kappa ≤ -ConditionedPoissonLimit.covarianceKernelQuotient t s)
    (heCenter : 0 ≤ eCenter) (heCenterHalf : eCenter ≤ 1 / 2)
    (hDiagonal : ∀ i : Fin (M.cellCount + 1),
      endpointDiagonalError M n W i ≤ eDiagonal)
    (hKernelRow : ∀ i : Fin (M.cellCount + 1),
      endpointDoubleKernelSharpRowError M hdelta hn hW S i ≤ eKernel)
    (hRelativeCenter : ∀ i : Fin (M.cellCount + 1),
      |(canonicalPartition M hdelta hn hW S).center i /
          (canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
            anchors hAnchors hInteriorLower hInteriorUpper).center i - 1| ≤
        eCenter)
    (hResidual : ∀ i : Fin (M.cellCount + 1),
      |(canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
        anchors hAnchors hInteriorLower hInteriorUpper).rowResidual i| ≤
          eResidual)
    (hKernelBound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |ConditionedPoissonLimit.covarianceKernelQuotient t s| ≤ CKernel)
    (hSmall : eDiagonal + eKernel + 4 * eCenter * CKernel + eResidual ≤
      kappa * anchorFloor / 16) :
    let P := canonicalPartition M hdelta hn hW S
    let E := canonicalCertificate M hdelta hn hW S
    let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper
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
      ∀ v, ‖actualEquiv.symm v‖ ≤ Cinv * ‖v‖ := by
  let P := canonicalPartition M hdelta hn hW S
  let E := canonicalCertificate M hdelta hn hW S
  let IM := canonicalIntervalMeshOfAnchors M hdelta hn hW hWTwo S epsilon
    anchors hAnchors hInteriorLower hInteriorUpper
  let r := kappa * anchorFloor / 16
  have hMassNonneg : ∀ j, 0 ≤ P.mass j := fun j ↦ (P.data.mass_pos j).le
  have hOmega : ∀ j, 0 ≤ sharpWeight P.mass P.center j :=
    sharpWeight_nonneg_of_mass_nonneg P.mass P.center hMassNonneg
  have hTotalPos : 0 < sharpWeightTotal P.mass P.center := by
    unfold sharpWeightTotal sharpWeight
    apply Finset.sum_pos
    · intro j _hj
      exact mul_pos (P.data.mass_pos j) (sq_pos_of_pos (P.center_pos hn j))
    · exact ⟨lowBand M, Finset.mem_univ _⟩
  have hDiagonalEntry (i : Fin (M.cellCount + 1)) :
      |arithmeticDiagonal (y n) E.lower E.upper i -
          IM.normalizedDiagonalCell i| ≤ endpointDiagonalError M n W i := by
    have hId := IM.normalizedDiagonalCell_eq_endpointContinuum
      (y n) E.lower E.upper (fun _ ↦ rfl) (fun _ ↦ rfl) i
    rw [hId]
    exact le_rfl
  have hKernelEntry (i j : Fin (M.cellCount + 1)) :
      |arithmeticKernel (y n) E.lower E.upper i j -
          IM.normalizedKernelCell i j| ≤ endpointDoubleKernelError M n W i j := by
    have hId := IM.normalizedKernelCell_eq_endpointContinuum
      (y n) E.lower E.upper (fun _ ↦ rfl) (fun _ ↦ rfl) i j
    rw [hId]
    exact le_rfl
  have hCenterEntry (i j : Fin (M.cellCount + 1)) :
      |P.center j / P.center i - IM.center j / IM.center i| ≤
        multiCanonicalCenterRatioError M hdelta hn hW hWTwo S epsilon
          anchors hAnchors hInteriorLower hInteriorUpper i j := le_rfl
  have hBudget (i : Fin (M.cellCount + 1)) :
      IM.arithmeticGraphRowBudget
          (endpointDiagonalError M n W)
          (endpointDoubleKernelError M n W)
          (multiCanonicalCenterRatioError M hdelta hn hW hWTwo S epsilon
            anchors hAnchors hInteriorLower hInteriorUpper)
          P.center i ≤ r := by
    have hAgg := multiCanonical_arithmeticGraphRowBudget_le M hdelta hn hW
      hWTwo S epsilon anchors hAnchors anchor hAnchor hInteriorLower
      hInteriorUpper heCenter heCenterHalf hDiagonal hKernelRow
      hRelativeCenter hResidual hKernelBound i
    exact hAgg.trans (by simpa only [r] using hSmall)
  exact exists_stable_arithmetic_inverse_of_uniform_gap hkappa hgap
    hAnchorFloor IM hAnchorMass
    (arithmeticDiagonal (y n) E.lower E.upper)
    (endpointDiagonalError M n W)
    (arithmeticKernel (y n) E.lower E.upper)
    (endpointDoubleKernelError M n W)
    (multiCanonicalCenterRatioError M hdelta hn hW hWTwo S epsilon
      anchors hAnchors hInteriorLower hInteriorUpper)
    P.center (sharpWeight P.mass P.center) hOmega hTotalPos
    hDiagonalEntry hKernelEntry hCenterEntry hBudget

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
