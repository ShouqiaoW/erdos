import Erdos390.Full.PaperActualSchurOrdinaryEndpointConnector

/-!
# Transporting an endpoint reference to a literal bridge partition

The endpoint theorem naturally returns a canonical partition as a local
witness.  A bridge constructed from the same canonical endpoint family may
carry propositionally different proofs of the scale inequalities.  This
small deterministic lemma performs the proof-irrelevant transport once and
then invokes the same-equivalence ordinary Schur connector.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport
open SquarefreeReferenceOperatorIdentification PositiveCellTransfer

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Endpoint-reference connector allowing the reference partition to be
identified propositionally with the literal partition stored in `B`. -/
theorem actualBandSchur_sameEquiv_ordinary_inverse_of_partition_eq_endpoint_reference
    [Nonempty Head] [Nonempty Band]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.RawBandGauge ≃ₗ[ℝ] B.RawBandGauge)
    (he : ∀ q, e q = B.actualBandSchurLinearMap xi hgamma hgap q)
    (P : ArithmeticBandGeometry.Partition
      B.sampleData.n B.sampleData.W Band)
    (hpartition : B.partition = P)
    (Ecert : IntervalCertificate P)
    {Cref Esquare Rpow Rproj deltaSchur : ℝ}
    (hCref : 0 ≤ Cref)
    (hEsquare : 0 ≤ Esquare) (hRpow : 0 ≤ Rpow)
    (hRproj : 0 ≤ Rproj)
    (hRatio : (∑ j : Band,
        B.harmonicMass j * B.bandCenter j) ≤
      Rproj * MovingLowGaugeTransfer.sharpWeightTotal
        B.harmonicMass B.bandCenter)
    (hReference : ∀ q : RawGaugeSpace P.mass P.center,
      ‖q‖ ≤ Cref *
        ‖projectedRawLinearMap
          (CompressedArithmeticOperator.arithmeticDiagonal
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          (CompressedArithmeticOperator.arithmeticKernel
            (ArithmeticModel.y B.sampleData.n) Ecert.lower Ecert.upper)
          P.mass P.center
          (by
            unfold MovingLowGaugeTransfer.sharpWeightTotal
              MovingLowGaugeTransfer.sharpWeight
            simpa only [Erdos390.Lemma84.WeightedBandData.centerEnergy,
              Erdos390.Lemma84.WeightedBandData.bandNormSq,
              Erdos390.Lemma84.WeightedBandData.bandInner, pow_two,
              mul_assoc] using
                (P.centerEnergy_pos B.n_gt_one).ne') q‖)
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
  subst P
  exact B.actualBandSchur_sameEquiv_ordinary_inverse_of_endpoint_reference
    xi hgamma hgap e he Ecert hCref hEsquare hRpow hRproj hRatio
      hReference hsquare hfull hSmallFull hSchurError hSmallSchur

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
