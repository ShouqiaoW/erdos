import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveRemainingInputsConnector

/-!
# Statement audit for the signed exceptional four/five remaining inputs
-/

namespace Erdos390.WholePaper

namespace BankPaperRealization

#check roughCanonicalSignedExceptionalFourFiveChamberInputAt_of_precursors
#check exists_roughCanonicalSignedExceptionalFourFiveRemainingInputs

/-- The exported theorem has the exact six-constant shape consumed by the
unconditional chamber closure. -/
example (W K0 : Nat) {c deltaStar : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∃ deepPlus deepHigh deepBroad
        cutoffPlus cutoffHigh cutoffBroad : Real,
      0 <= deepPlus ∧ 0 <= deepHigh ∧ 0 <= deepBroad ∧
      0 <= cutoffPlus ∧ 0 <= cutoffHigh ∧ 0 <= cutoffBroad ∧
      RoughCanonicalSignedExceptionalFourFiveRemainingInputs
        W K0 c deltaStar
        deepPlus deepHigh deepBroad
        cutoffPlus cutoffHigh cutoffBroad :=
  exists_roughCanonicalSignedExceptionalFourFiveRemainingInputs
    W K0 hc hdelta hdeltaUpper

end BankPaperRealization

end Erdos390.WholePaper
