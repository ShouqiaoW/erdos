import Erdos390.Full.PaperActualFullOrdinaryProjectionConnector
import Erdos390.Full.PaperActualSchurOrdinaryRow

/-!
# Same-map ordinary inverse from the endpoint reference

This file performs the last two deterministic perturbations in ordinary raw
norm.  The reference is the literal endpoint arithmetic operator, the first
perturbation is the actual full-valuation row, and the second is the literal
nuisance Schur correction.  The equivalence in the conclusion is the same
equivalence supplied by the sharp existence argument.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry
open PaperWeightedInverseExport
open SquarefreeReferenceOperatorIdentification
open PositiveCellTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- A reference ordinary inverse and an actual-full row perturbation give
an ordinary inverse for the literal actual-full map. -/
theorem actualBandFull_ordinary_inverse_of_endpoint_reference
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) (Ecert : IntervalCertificate B.partition)
    {Cref Esquare Rpow Rproj : ℝ}
    (hCref : 0 ≤ Cref)
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hReference : ∀ q : B.RawBandGauge,
      ‖q‖ ≤ Cref *
        ‖projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          B.harmonicMass B.bandCenter
          (ne_of_gt B.sharpBandWeightTotal_pos) q‖)
    (hsquare : ∀ q : B.RawBandGauge, ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.referenceBandRow
          B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ q : B.RawBandGauge, ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow)
    (hSmallFull :
      Cref * ((1 + Rproj) * (Rpow + Esquare)) ≤ 1 / 2) :
    ∀ q : B.RawBandGauge,
      ‖q‖ ≤ (2 * Cref) * ‖B.actualBandFullLinearMap xi q‖ := by
  let deltaFull : ℝ := (1 + Rproj) * (Rpow + Esquare)
  have herror (q : B.RawBandGauge) :
      ‖B.actualBandFullLinearMap xi q -
          projectedRawLinearMap
            (CompressedArithmeticOperator.arithmeticDiagonal
              (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
            (CompressedArithmeticOperator.arithmeticKernel
              (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
            B.harmonicMass B.bandCenter
            (ne_of_gt B.sharpBandWeightTotal_pos) q‖ ≤
        deltaFull * ‖q‖ := by
    simpa only [deltaFull] using
      B.actualBandFull_sub_projectedArithmeticRaw_norm_le_of_rows_ordinary
        xi Ecert q hEsquare hRpow hRproj hRatio
          (hsquare q) (hfull q)
  intro q
  let Aref := projectedRawLinearMap
    (CompressedArithmeticOperator.arithmeticDiagonal
      (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
    (CompressedArithmeticOperator.arithmeticKernel
      (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
    B.harmonicMass B.bandCenter
    (ne_of_gt B.sharpBandWeightTotal_pos)
  have href := hReference q
  have htri : ‖Aref q‖ ≤
      ‖B.actualBandFullLinearMap xi q‖ + deltaFull * ‖q‖ := by
    have hid : Aref q = B.actualBandFullLinearMap xi q -
        (B.actualBandFullLinearMap xi q - Aref q) := by abel
    calc
      ‖Aref q‖ = ‖B.actualBandFullLinearMap xi q -
          (B.actualBandFullLinearMap xi q - Aref q)‖ := congrArg norm hid
      _ ≤ ‖B.actualBandFullLinearMap xi q‖ +
          ‖B.actualBandFullLinearMap xi q - Aref q‖ := norm_sub_le _ _
      _ ≤ ‖B.actualBandFullLinearMap xi q‖ + deltaFull * ‖q‖ :=
        add_le_add le_rfl (by simpa only [Aref] using herror q)
  have hraw : ‖q‖ ≤ Cref * ‖B.actualBandFullLinearMap xi q‖ +
      (Cref * deltaFull) * ‖q‖ := by
    calc
      ‖q‖ ≤ Cref * ‖Aref q‖ := by simpa only [Aref] using href
      _ ≤ Cref *
          (‖B.actualBandFullLinearMap xi q‖ + deltaFull * ‖q‖) :=
        mul_le_mul_of_nonneg_left htri hCref
      _ = Cref * ‖B.actualBandFullLinearMap xi q‖ +
          (Cref * deltaFull) * ‖q‖ := by ring
  have habsorb : (Cref * deltaFull) * ‖q‖ ≤
      (1 / 2) * ‖q‖ :=
    mul_le_mul_of_nonneg_right (by
      simpa only [deltaFull] using hSmallFull) (norm_nonneg q)
  have hhalf : ‖q‖ ≤ Cref * ‖B.actualBandFullLinearMap xi q‖ +
      (1 / 2) * ‖q‖ := hraw.trans (add_le_add le_rfl habsorb)
  linarith

/-- Exact terminal: the sharp argument supplies the literal Schur
equivalence, while the endpoint and nuisance estimates give an ordinary
inverse for that same map. -/
theorem actualBandSchur_sameEquiv_ordinary_inverse_of_endpoint_reference
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (Ecert : IntervalCertificate B.partition)
    {Cref Esquare Rpow Rproj deltaSchur : ℝ}
    (hCref : 0 ≤ Cref)
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hReference : ∀ q : B.RawBandGauge,
      ‖q‖ ≤ Cref *
        ‖projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          B.harmonicMass B.bandCenter
          (ne_of_gt B.sharpBandWeightTotal_pos) q‖)
    (hsquare : ∀ q : B.RawBandGauge, ∀ i : Band,
      |SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.referenceBandRow
          B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ q : B.RawBandGauge, ∀ i : Band,
      |PrimePowerSharpBandTransfer.fullBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        SquarefreeSharpBandTransfer.squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i| ≤
          ‖q‖ * Rpow)
    (hSmallFull :
      Cref * ((1 + Rproj) * (Rpow + Esquare)) ≤ 1 / 2)
    (hSchurError : ∀ q : B.RawBandGauge,
      ‖B.actualBandSchurLinearMap xi hgamma hgap q -
          B.actualBandFullLinearMap xi q‖ ≤ deltaSchur * ‖q‖)
    (hSmallSchur : (2 * Cref) * deltaSchur ≤ 1 / 2) :
    (∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q) ∧
      ∀ v, ‖e.symm v‖ ≤ (4 * Cref) * ‖v‖ := by
  have hFullInverse :=
    B.actualBandFull_ordinary_inverse_of_endpoint_reference
      xi Ecert hCref hEsquare hRpow hRproj hRatio hReference
      hsquare hfull hSmallFull
  refine ⟨he, ?_⟩
  have hCtwo : 0 ≤ 2 * Cref := mul_nonneg (by norm_num) hCref
  have hinv := B.actualBandSchur_inverse_norm_le_of_full_ordinary
    xi hgamma hgap e he hCtwo hSmallSchur hFullInverse hSchurError
  intro v
  have hconstant : 2 * (2 * Cref) * ‖v‖ =
      (4 * Cref) * ‖v‖ := by ring
  exact (hinv v).trans_eq hconstant

end BridgeData
end
end Erdos390.Full.PaperBridgeFit
