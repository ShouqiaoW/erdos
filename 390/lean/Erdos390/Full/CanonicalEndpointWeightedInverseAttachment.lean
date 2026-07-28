import Erdos390.Full.CanonicalEndpointDoubleKernelRowEventually
import Erdos390.Full.CanonicalEndpointTwoTailCertificate
import Erdos390.Full.MovingLowSharpRowAggregation
import Erdos390.Full.UniformMeshArithmeticInverse
import Erdos390.Full.PaperWeightedInverseExport
import Erdos390.Full.PoissonDickmanKernelBounds

/-!
# Attachment of the canonical endpoint estimates to the weighted inverse

This file is the deterministic application layer after the endpoint PNT
estimates.  It identifies the literal prime-cell matrix with the entries in
the canonical continuum mesh, aggregates diagonal, two-index, relative-centre
and two-tail errors in the actual sharp row norm, applies the stable finite
graph inverse, and exports the result in the paper's raw weighted gauge.

No inverse or coercivity statement is assumed.  The only quantitative inputs
are the four error estimates supplied by the preceding unconditional
quadrature and mesh modules.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel ArithmeticBandGeometry RegularRelativeMesh
open KernelPrimeQuadrature DoubleKernelPrimeQuadrature
open ContinuumCellGraph ContinuumCellGraph.IntervalMesh
open CompressedArithmeticOperator PositiveCellTransfer
open MovingLowGaugeTransfer
open UniformMeshArithmeticInverse PaperWeightedInverseExport
open PoissonDickmanWeightedInverse

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

section ExactIdentifications

variable {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
  (hW : W ≠ 0) (hWTwo : 2 ≤ W)
  (S : ScaleSeparation M n W)
  (epsilon : ℝ) (anchorCell : Fin M.cellCount)
  (hInteriorLower : epsilon ≤
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).lower
        (positiveBand M anchorCell) : ℝ))
  (hInteriorUpper :
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).upper
        (positiveBand M anchorCell) : ℝ) ≤ 1 - epsilon)

private abbrev CanonicalBand := Fin (M.cellCount + 1)

private def canonicalIM :
    IntervalMesh epsilon (CanonicalBand M) :=
  canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
    hInteriorLower hInteriorUpper

private def canonicalP :
    Partition n W (CanonicalBand M) :=
  canonicalPartition M hdelta hn hW S

private def canonicalE :
    IntervalCertificate (canonicalP M hdelta hn hW S) :=
  canonicalCertificate M hdelta hn hW S

theorem canonicalIM_center_eq_certificate
    (i : CanonicalBand M) :
    (canonicalIM M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper).center i =
      (canonicalE M hdelta hn hW S).continuumCenter i := by
  let IM := canonicalIM M hdelta hn hW hWTwo S epsilon anchorCell
    hInteriorLower hInteriorUpper
  let E := canonicalE M hdelta hn hW S
  have hy : 1 < y n := by
    have hlog : 0 < Real.log (y n) := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
    exact (Real.log_pos_iff (Scale.y_pos
      (Nat.zero_lt_of_lt hn)).le).mp hlog
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have hLowerTwo (j : CanonicalBand M) : 2 ≤ E.lower j := by
    change 2 ≤ fullCutoff M n W j.1
    exact hWTwo.trans (hmono (Nat.zero_le j.1))
  exact IM.center_eq_intervalCertificate_continuumCenter E hy hLowerTwo
    (fun _ ↦ rfl) (fun _ ↦ rfl) i

theorem canonicalIM_normalizedDiagonal_eq_endpoint
    (i : CanonicalBand M) :
    (canonicalIM M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper).normalizedDiagonalCell i =
      continuumDiagonal (y n)
        (canonicalE M hdelta hn hW S).lower
        (canonicalE M hdelta hn hW S).upper i := by
  let IM := canonicalIM M hdelta hn hW hWTwo S epsilon anchorCell
    hInteriorLower hInteriorUpper
  exact IM.normalizedDiagonalCell_eq_endpointContinuum (y n)
    (canonicalE M hdelta hn hW S).lower
    (canonicalE M hdelta hn hW S).upper
    (fun _ ↦ rfl) (fun _ ↦ rfl) i

theorem canonicalIM_normalizedKernel_eq_endpoint
    (i j : CanonicalBand M) :
    (canonicalIM M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper).normalizedKernelCell i j =
      continuumKernel (y n)
        (canonicalE M hdelta hn hW S).lower
        (canonicalE M hdelta hn hW S).upper i j := by
  let IM := canonicalIM M hdelta hn hW hWTwo S epsilon anchorCell
    hInteriorLower hInteriorUpper
  exact IM.normalizedKernelCell_eq_endpointContinuum (y n)
    (canonicalE M hdelta hn hW S).lower
    (canonicalE M hdelta hn hW S).upper
    (fun _ ↦ rfl) (fun _ ↦ rfl) i j

end ExactIdentifications

section RowBudget

variable {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
  (hW : W ≠ 0) (hWTwo : 2 ≤ W)
  (S : ScaleSeparation M n W)
  (epsilon : ℝ) (anchorCell : Fin M.cellCount)
  (hInteriorLower : epsilon ≤
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).lower
        (positiveBand M anchorCell) : ℝ))
  (hInteriorUpper :
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).upper
        (positiveBand M anchorCell) : ℝ) ≤ 1 - epsilon)

/-- The literal centre-ratio discrepancy used in the arithmetic graph row
budget. -/
def canonicalCenterRatioError (i j : Fin (M.cellCount + 1)) : ℝ :=
  let P := canonicalPartition M hdelta hn hW S
  let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
    hInteriorLower hInteriorUpper
  |P.center j / P.center i - IM.center j / IM.center i|

/-- The four canonical estimates aggregate with constants independent of the
number of cells.  In particular the already summed double-kernel term enters
with coefficient one, and relative centres cost only `4 eCenter CKernel`.
-/
theorem canonical_arithmeticGraphRowBudget_le
    {eDiagonal eKernel eCenter eResidual CKernel : ℝ}
    (heCenter : 0 ≤ eCenter) (heCenterHalf : eCenter ≤ 1 / 2)
    (hDiagonal : ∀ i : Fin (M.cellCount + 1),
      endpointDiagonalError M n W i ≤ eDiagonal)
    (hKernelRow : ∀ i : Fin (M.cellCount + 1),
      endpointDoubleKernelSharpRowError M hdelta hn hW S i ≤ eKernel)
    (hRelativeCenter : ∀ i : Fin (M.cellCount + 1),
      |(canonicalPartition M hdelta hn hW S).center i /
          (canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
            hInteriorLower hInteriorUpper).center i - 1| ≤ eCenter)
    (hResidual : ∀ i : Fin (M.cellCount + 1),
      |(canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
        hInteriorLower hInteriorUpper).rowResidual i| ≤ eResidual)
    (hKernelBound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |ConditionedPoissonLimit.covarianceKernelQuotient t s| ≤ CKernel)
    (i : Fin (M.cellCount + 1)) :
    let P := canonicalPartition M hdelta hn hW S
    let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper
    IM.arithmeticGraphRowBudget
        (endpointDiagonalError M n W)
        (endpointDoubleKernelError M n W)
        (canonicalCenterRatioError M hdelta hn hW hWTwo S epsilon anchorCell
          hInteriorLower hInteriorUpper)
        P.center i ≤
      eDiagonal + eKernel + 4 * eCenter * CKernel + eResidual := by
  let P := canonicalPartition M hdelta hn hW S
  let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
    hInteriorLower hInteriorUpper
  let T := canonicalTwoTailCertificate M hdelta hn hW hWTwo S epsilon
    anchorCell hInteriorLower hInteriorUpper
  have hCenterRow :
      (∑ j, |IM.normalizedKernelCell i j| *
        canonicalCenterRatioError M hdelta hn hW hWTwo S epsilon anchorCell
          hInteriorLower hInteriorUpper i j) ≤
        4 * eCenter * CKernel := by
    exact IM.centerRatio_weightedRow_le T P.center heCenter heCenterHalf
      hRelativeCenter hKernelBound i
  change endpointDiagonalError M n W i +
      (∑ j, endpointDoubleKernelError M n W i j *
        |P.center j / P.center i|) +
      (∑ j, |IM.normalizedKernelCell i j| *
        canonicalCenterRatioError M hdelta hn hW hWTwo S epsilon anchorCell
          hInteriorLower hInteriorUpper i j) +
      |IM.rowResidual i| ≤
    eDiagonal + eKernel + 4 * eCenter * CKernel + eResidual
  have hKernel := hKernelRow i
  change (∑ j, endpointDoubleKernelError M n W i j *
      |P.center j / P.center i|) ≤ eKernel at hKernel
  linarith [hDiagonal i, hCenterRow, hResidual i]

end RowBudget

section StableInverse

variable {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
  (hW : W ≠ 0) (hWTwo : 2 ≤ W)
  (S : ScaleSeparation M n W)
  {epsilon : ℝ} (hepsilon : 0 < epsilon) (hhalf : epsilon < 1 / 2)
  (anchorCell : Fin M.cellCount)
  (hInteriorLower : epsilon ≤
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).lower
        (positiveBand M anchorCell) : ℝ))
  (hInteriorUpper :
    realLogCoordinate (y n)
      ((canonicalCertificate M hdelta hn hW S).upper
        (positiveBand M anchorCell) : ℝ) ≤ 1 - epsilon)
  (hAnchorLength : M.width anchorCell / 2 ≤
    realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).upper
          (positiveBand M anchorCell) : ℝ) -
      realLogCoordinate (y n)
        ((canonicalCertificate M hdelta hn hW S).lower
          (positiveBand M anchorCell) : ℝ))

/-- Once the four already-proved endpoint estimates fit inside the explicit
graph budget, the literal projected prime-cell matrix has an actual inverse.
The second conclusion is the same inverse exported to the paper gauge; its
equation and weighted norm estimate are conclusions, not hypotheses. -/
theorem exists_canonical_projected_inverse_and_paper_solutions
    {kappa eDiagonal eKernel eCenter eResidual CKernel : ℝ}
    (hAnchorLength : M.width anchorCell / 2 ≤
      realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hn hW S).upper
            (positiveBand M anchorCell) : ℝ) -
        realLogCoordinate (y n)
          ((canonicalCertificate M hdelta hn hW S).lower
            (positiveBand M anchorCell) : ℝ))
    (hkappa : 0 < kappa)
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc epsilon (1 - epsilon),
      kappa ≤ -ConditionedPoissonLimit.covarianceKernelQuotient t s)
    (heCenter : 0 ≤ eCenter) (heCenterHalf : eCenter ≤ 1 / 2)
    (hDiagonal : ∀ i : Fin (M.cellCount + 1),
      endpointDiagonalError M n W i ≤ eDiagonal)
    (hKernelRow : ∀ i : Fin (M.cellCount + 1),
      endpointDoubleKernelSharpRowError M hdelta hn hW S i ≤ eKernel)
    (hRelativeCenter : ∀ i : Fin (M.cellCount + 1),
      |(canonicalPartition M hdelta hn hW S).center i /
          (canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
            hInteriorLower hInteriorUpper).center i - 1| ≤ eCenter)
    (hResidual : ∀ i : Fin (M.cellCount + 1),
      |(canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
        hInteriorLower hInteriorUpper).rowResidual i| ≤ eResidual)
    (hKernelBound : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |ConditionedPoissonLimit.covarianceKernelQuotient t s| ≤ CKernel)
    (hSmall : eDiagonal + eKernel + 4 * eCenter * CKernel + eResidual ≤
      kappa * (M.width anchorCell / 2) / 16) :
    let P := canonicalPartition M hdelta hn hW S
    let E := canonicalCertificate M hdelta hn hW S
    let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
      hInteriorLower hInteriorUpper
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
      (∀ v, ‖actualEquiv.symm v‖ ≤ Cinv * ‖v‖) ∧
      ∀ u : RawGaugeSpace P.mass P.center,
        ∃ b : RawGaugeSpace P.mass P.center,
          projectedRawLinearMap
              (arithmeticDiagonal (y n) E.lower E.upper)
              (arithmeticKernel (y n) E.lower E.upper)
              P.mass P.center
              (by
                change (∑ j, P.mass j * P.center j ^ 2) ≠ 0
                apply ne_of_gt
                apply Finset.sum_pos
                · intro j _hj
                  exact mul_pos (P.data.mass_pos j)
                    (sq_pos_of_pos (P.center_pos hn j))
                · exact ⟨lowBand M, Finset.mem_univ _⟩) b = u ∧
          paperSharpNorm P.mass P.center (P.center_ne_zero hn) b ≤
            Cinv * paperSharpNorm P.mass P.center (P.center_ne_zero hn) u := by
  let P := canonicalPartition M hdelta hn hW S
  let E := canonicalCertificate M hdelta hn hW S
  let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S epsilon anchorCell
    hInteriorLower hInteriorUpper
  let anchorFloor := M.width anchorCell / 2
  let r := kappa * anchorFloor / 16
  let Cinv :=
    (4 / (kappa * ∑ j, IM.anchor j)) /
      (1 - (4 / (kappa * ∑ j, IM.anchor j)) * (2 * r))
  have hAnchorMass : anchorFloor ≤ ∑ j, IM.anchor j := by
    have hsum : (∑ j, IM.anchor j) = IM.length (positiveBand M anchorCell) := by
      unfold IntervalMesh.anchor
      simp only [IM, canonicalIntervalMesh, Finset.mem_singleton,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [hsum]
    exact hAnchorLength
  have hMassNonneg : ∀ j, 0 ≤ P.mass j :=
    fun j ↦ (P.data.mass_pos j).le
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
    have hId := canonicalIM_normalizedDiagonal_eq_endpoint M hdelta hn hW
      hWTwo S epsilon anchorCell hInteriorLower hInteriorUpper i
    change IM.normalizedDiagonalCell i =
      continuumDiagonal (y n) E.lower E.upper i at hId
    rw [hId]
    exact le_rfl
  have hKernelEntry (i j : Fin (M.cellCount + 1)) :
      |arithmeticKernel (y n) E.lower E.upper i j -
          IM.normalizedKernelCell i j| ≤ endpointDoubleKernelError M n W i j := by
    have hId := canonicalIM_normalizedKernel_eq_endpoint M hdelta hn hW
      hWTwo S epsilon anchorCell hInteriorLower hInteriorUpper i j
    change IM.normalizedKernelCell i j =
      continuumKernel (y n) E.lower E.upper i j at hId
    rw [hId]
    exact le_rfl
  have hCenterEntry (i j : Fin (M.cellCount + 1)) :
      |P.center j / P.center i - IM.center j / IM.center i| ≤
        canonicalCenterRatioError M hdelta hn hW hWTwo S epsilon anchorCell
          hInteriorLower hInteriorUpper i j := le_rfl
  have hBudget (i : Fin (M.cellCount + 1)) :
      IM.arithmeticGraphRowBudget
          (endpointDiagonalError M n W)
          (endpointDoubleKernelError M n W)
          (canonicalCenterRatioError M hdelta hn hW hWTwo S epsilon anchorCell
            hInteriorLower hInteriorUpper)
          P.center i ≤ r := by
    have hAgg := canonical_arithmeticGraphRowBudget_le M hdelta hn hW hWTwo S
      epsilon anchorCell hInteriorLower hInteriorUpper heCenter heCenterHalf
      hDiagonal hKernelRow hRelativeCenter hResidual hKernelBound i
    exact hAgg.trans (by simpa only [r, anchorFloor] using hSmall)
  obtain ⟨actualEquiv, hactual, hinv⟩ :=
    exists_stable_arithmetic_inverse_of_uniform_gap hkappa hgap
      (half_pos (M.width_pos hdelta anchorCell)) IM hAnchorMass
      (arithmeticDiagonal (y n) E.lower E.upper)
      (endpointDiagonalError M n W)
      (arithmeticKernel (y n) E.lower E.upper)
      (endpointDoubleKernelError M n W)
      (canonicalCenterRatioError M hdelta hn hW hWTwo S epsilon anchorCell
        hInteriorLower hInteriorUpper)
      P.center (sharpWeight P.mass P.center) hOmega hTotalPos
      hDiagonalEntry hKernelEntry hCenterEntry hBudget
  refine ⟨actualEquiv, hactual, hinv, ?_⟩
  intro u
  exact exists_raw_solution_with_paperSharpNorm_bound
    (arithmeticDiagonal (y n) E.lower E.upper)
    (arithmeticKernel (y n) E.lower E.upper)
    P.mass P.center (P.center_ne_zero hn) hTotalPos actualEquiv hactual hinv u

end StableInverse

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
