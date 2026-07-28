import Erdos390.Full.PaperNonstepSlowRightLedger

/-!
Expanded statement audit for the standalone non-step slow-right ledger.
The terminal is finite and mesh-free: the actual full row, the literal
squarefree row, the Lemma 7.5 transfer hypothesis, the `L¹` hypothesis, and
the local reciprocal-square diagonal are all restated below rather than
trusted through a bare `#print`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PaperPrimePowerLemma75
open PrimePowerCovariance.BoundedValuationLaw

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Independent source-level expansion of the law-generic exact ledger. -/
example {Omega : Type*} [Fintype Omega] {Mlaw : ℕ}
    (law : BoundedValuationLaw Omega Mlaw)
    {Cpow epsilon w : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon) (hw : 0 ≤ w)
    (hW : 1 < B.sampleData.W)
    (h75 : PrimePowerTransferBounds law
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law.covVV p.1 q.1) -
        ((1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q * law.covII p.1 q.1)| ≤
      (21 * Cpow * (1 / (B.sampleData.W : ℝ))) *
          (w * B.bandCenter i) +
        (21 * epsilon * (1 / (B.sampleData.W : ℝ))) * w +
        3 * (Cpow + epsilon) *
          ((1 / B.harmonicMass i) *
            ∑ p ∈ B.partition.data.fiber i,
              |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
  simpa only [nonstepFullCoefficientRow,
    nonstepSquarefreeCoefficientRow, nonstepPrimePowerRowBudget,
    bandDeviationReciprocalSquare] using
      B.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
        law hCpow hepsilon hw hW h75 hdevL1 i

/-- Independent source-level expansion of the exact non-step terminal. -/
example [Nonempty Head]
    (xi : B.ParamSpace)
    {Cpow epsilon w : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon) (hw : 0 ≤ w)
    (hW : 1 < B.sampleData.W)
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.normalizedBandCovarianceRow xi B.slowScore i -
        B.normalizedSquarefreeBandCovarianceRow xi B.slowSquarefreeScore i| ≤
      (21 * Cpow * (1 / (B.sampleData.W : ℝ))) *
          (w * B.bandCenter i) +
        (21 * epsilon * (1 / (B.sampleData.W : ℝ))) * w +
        3 * (Cpow + epsilon) *
          ((1 / B.harmonicMass i) *
            ∑ p ∈ B.partition.data.fiber i,
              |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
  simpa only [nonstepPrimePowerRowBudget,
    bandDeviationReciprocalSquare] using
      B.abs_normalizedSlowRow_sub_squarefree_le_nonstepBudget xi
        hCpow hepsilon hw hW h75 hdevL1 i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit

#print Erdos390.Full.PaperBridgeFit.BridgeData.slowSquarefreeScore
#print Erdos390.Full.PaperBridgeFit.BridgeData.normalizedSquarefreeBandCovarianceRow
#print Erdos390.Full.PaperBridgeFit.BridgeData.bandDeviationReciprocalSquare
#print Erdos390.Full.PaperBridgeFit.BridgeData.nonstepPrimePowerRowBudget
#print Erdos390.Full.PaperBridgeFit.BridgeData.nonstepFullCoefficientRow
#print Erdos390.Full.PaperBridgeFit.BridgeData.nonstepSquarefreeCoefficientRow
#print Erdos390.Full.PaperBridgeFit.BridgeData.normalizedSlowRows_eq_fullSquarefreeCoefficientRows
#print Erdos390.Full.PaperBridgeFit.BridgeData.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
#print Erdos390.Full.PaperBridgeFit.BridgeData.abs_normalizedSlowRow_sub_squarefree_le_nonstepBudget
