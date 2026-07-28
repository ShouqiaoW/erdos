import Erdos390.Full.PaperProposition87CanonicalFeasibilitySlackEventually

open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example (U : ℝ) (hU : 1 ≤ U) (W : ℕ) (a : NNReal)
    (Cfixed Cactive : ℝ) (hCactive : 0 ≤ Cactive) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        Cfixed +
            Real.exp (2 *
              ((PaperStatisticNorm.valuationLogCoefficient
                    U B.sampleData.W +
                  B.nuisanceStatisticCoefficient U) * (3 * (a : ℝ)))) *
              Cactive ≤ B.L := by
  exact eventually_canonical_exponential_slack_le_L
    U hU W a Cfixed Cactive hCactive

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
