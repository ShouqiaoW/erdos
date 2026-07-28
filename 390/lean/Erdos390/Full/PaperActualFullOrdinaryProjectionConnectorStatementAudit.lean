import Erdos390.Full.PaperActualFullOrdinaryProjectionConnector

/-! Expanded independent audit of the final ordinary projection connector. -/

open scoped BigOperators

namespace Erdos390.Full.PaperActualFullOrdinaryProjectionConnectorStatementAudit

noncomputable section

open PaperBridgeFit ArithmeticBandGeometry
open PaperWeightedInverseExport PrimePowerSharpBandTransfer
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open PositiveCellTransfer

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example
    [Nonempty Head] [Nonempty Band]
    (B : BridgeData Head Band)
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
      |squarefreeBandRow
          (B.actualValuationLaw xi) B.partition q.1 i -
        referenceBandRow B.partition q.1 i| ≤ ‖q‖ * Esquare)
    (hfull : ∀ i : Band,
      |fullBandRow (B.actualValuationLaw xi) B.partition q.1 i -
        squarefreeBandRow
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
  exact B.actualBandFull_sub_projectedArithmeticRaw_norm_le_of_rows_ordinary
    xi Ecert q hEsquare hRpow hRproj hRatio hsquare hfull

end

end Erdos390.Full.PaperActualFullOrdinaryProjectionConnectorStatementAudit
