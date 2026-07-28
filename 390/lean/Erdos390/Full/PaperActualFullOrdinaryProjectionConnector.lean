import Erdos390.Full.PaperActualFullOrdinaryRowTransfer
import Erdos390.Full.PaperExactTwoStageOrdinaryFast

/-!
# Ordinary projected transfer from the Dickman reference to the actual full row

The row estimates are first established before gauge projection.  This file
performs the exact finite projection and identifies the projected Dickman
reference with the literal endpoint arithmetic raw operator.  The only
projection loss is the displayed first-moment/centre-energy ratio; there is
no division by the moving low-band centre.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open PaperWeightedInverseExport
open PrimePowerSharpBandTransfer
open SquarefreeSharpBandTransfer
open SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PositiveCellTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual full band map is exactly the projection of its literal full
valuation row. -/
theorem actualBandFullLinearMap_eq_projectedFullBandRow
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    B.actualBandFullLinearMap xi q =
      B.projectRawBandVector (fun i ↦
        fullBandRow (B.actualValuationLaw xi) B.partition q.1 i) := by
  change B.projectRawBandVector
      (B.normalizedBandCovarianceRow xi (B.bandRegressionScore q)) = _
  congr 1
  funext i
  exact (B.fullBandRow_actualValuationLaw_eq_normalizedBandCovarianceRow
    xi q i).symm

/-- Coordinatewise ordinary full-to-reference control survives the exact
arithmetic gauge projection with only the first-moment ratio loss. -/
theorem actualBandFull_sub_projectedReference_norm_le_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {E Rproj : ℝ}
    (hE : 0 ≤ E) (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hrow : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          referenceBandRow B.partition q.1 i| ≤ ‖q‖ * E) :
    ‖B.actualBandFullLinearMap xi q -
        B.projectRawBandVector
          (fun i ↦ referenceBandRow B.partition q.1 i)‖ ≤
      (1 + Rproj) * E * ‖q‖ := by
  let full : Band → ℝ := fun i ↦
    fullBandRow (B.actualValuationLaw xi) B.partition q.1 i
  let reference : Band → ℝ := fun i ↦
    referenceBandRow B.partition q.1 i
  have hC : 0 ≤ ‖q‖ * E := mul_nonneg (norm_nonneg q) hE
  have hproject :
      ‖B.projectRawBandVector (full - reference)‖ ≤
        (1 + Rproj) * (‖q‖ * E) := by
    exact B.projectRawBandVector_norm_le_of_moment_ratio
      (full - reference) hC hRproj (by
        intro i
        simpa only [full, reference, Pi.sub_apply] using hrow i) hRatio
  rw [B.actualBandFullLinearMap_eq_projectedFullBandRow xi q]
  rw [← B.projectRawBandVector_sub]
  simpa only [full, reference, mul_assoc, mul_left_comm, mul_comm] using
    hproject

/-- Direct form using the squarefree-profile error and Lemma 7.5's weighted
full-versus-squarefree row. -/
theorem actualBandFull_sub_projectedReference_norm_le_of_rows_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {Esquare Rpow Rproj : ℝ}
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hsquare : ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow) :
    ‖B.actualBandFullLinearMap xi q -
        B.projectRawBandVector
          (fun i ↦ referenceBandRow B.partition q.1 i)‖ ≤
      (1 + Rproj) * (Rpow + Esquare) * ‖q‖ := by
  have hrow : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
          referenceBandRow B.partition q.1 i| ≤
        ‖q‖ * (Rpow + Esquare) := by
    intro i
    exact B.fullBandRow_sub_referenceBandRow_le_ordinary
      xi q hsquare hfull i
  exact B.actualBandFull_sub_projectedReference_norm_le_ordinary
    xi q (add_nonneg hRpow hEsquare) hRproj hRatio hrow

/-- The projected reference in the preceding theorems is literally the
paper's endpoint arithmetic raw linear map. -/
theorem projectRawBandVector_referenceBandRow_eq_projectedRawLinearMap
    [Nonempty Band]
    (Ecert : IntervalCertificate B.partition)
    (q : B.RawBandGauge) :
    B.projectRawBandVector
        (fun i ↦ referenceBandRow B.partition q.1 i) =
      projectedRawLinearMap
        (CompressedArithmeticOperator.arithmeticDiagonal
          (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
        (CompressedArithmeticOperator.arithmeticKernel
          (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
        B.harmonicMass B.bandCenter
        (ne_of_gt B.sharpBandWeightTotal_pos) q := by
  apply Subtype.ext
  change MovingLowGaugeTransfer.weightedGaugeProjection
      B.harmonicMass B.bandCenter
        (fun i ↦ referenceBandRow B.partition q.1 i) =
    MovingLowGaugeTransfer.weightedGaugeProjection
      B.harmonicMass B.bandCenter
        (rawOperator
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          q.1)
  congr 1
  funext i
  exact referenceBandRow_eq_rawOperator Ecert q.1 i

/-- Final finite ordinary perturbation estimate with the endpoint arithmetic
reference displayed as a linear map. -/
theorem actualBandFull_sub_projectedArithmeticRaw_norm_le_of_rows_ordinary
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Ecert : IntervalCertificate B.partition)
    (q : B.RawBandGauge)
    {Esquare Rpow Rproj : ℝ}
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hsquare : ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow) :
    ‖B.actualBandFullLinearMap xi q -
        projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          B.harmonicMass B.bandCenter
          (ne_of_gt B.sharpBandWeightTotal_pos) q‖ ≤
      (1 + Rproj) * (Rpow + Esquare) * ‖q‖ := by
  rw [← B.projectRawBandVector_referenceBandRow_eq_projectedRawLinearMap
    Ecert q]
  exact B.actualBandFull_sub_projectedReference_norm_le_of_rows_ordinary
    xi q hEsquare hRpow hRproj hRatio hsquare hfull

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
