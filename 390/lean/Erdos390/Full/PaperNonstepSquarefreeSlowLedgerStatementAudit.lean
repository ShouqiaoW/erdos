import Erdos390.Full.PaperNonstepSquarefreeSlowLedger

/-!
Expanded statement audit for the exact squarefree/reference comparison with
the literal non-step coefficient `g_p = alpha_{j(p)} - t_p`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/- The entrywise profile error aggregates without a least-centre divisor or
number-of-bands loss.  Both the signed coefficient and the local `p^{-2}`
term are expanded literally. -/
example [Nonempty Head]
    (xi : B.ParamSpace)
    {epsilonOff epsilonDiag Cdiag w : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hepsilonDiag : 0 ≤ epsilonDiag)
    (hentry : ∀ p q : BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 q.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 q.1| ≤
        epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
          else 0))
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.normalizedSquarefreeBandCovarianceRow xi B.slowSquarefreeScore i -
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                squarefreeReferenceEntry B.sampleData.n p.1 q.1| ≤
      7 * epsilonOff * w +
        2 * epsilonDiag * B.bandCenter i +
        Cdiag *
          ((1 / B.harmonicMass i) *
            ∑ p ∈ B.partition.data.fiber i,
              |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
  simpa only [referenceSlowRow, bandDeviationReciprocalSquare] using
    B.abs_squarefreeSlowRow_sub_referenceSlowRow_le xi
      hepsilonOff hepsilonDiag hentry hdevL1 i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
