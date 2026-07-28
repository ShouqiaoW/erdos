import Erdos390.Full.PaperCanonicalBandFirstMomentEventually

open scoped BigOperators
open Filter

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

example (W : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (B : BridgeData Head Band),
        B.sampleData.n = n → B.sampleData.W = W →
        (∑ j : Band, B.harmonicMass j * B.bandCenter j) ≤
          2 * Real.log 4 := by
  exact eventually_bandFirstMoment_le_two_log_four W

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
