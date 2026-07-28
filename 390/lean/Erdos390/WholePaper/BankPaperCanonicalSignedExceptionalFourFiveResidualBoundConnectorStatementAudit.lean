import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveResidualBoundConnector

/-!
# Statement audit for the unconditional signed exceptional four/five bound
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

namespace BankPaperRealization

#check exists_eventually_roughCanonicalSignedExceptionalResidualBound_fourFive

/-- The exported closure hides all six interval constants and the chamber
variation constant behind one nonnegative residual-bound coefficient. -/
example (W K0 : Nat) {c deltaStar beta : Real}
    (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    ∃ C : Real, 0 <= C ∧
      ∀ᶠ n : Nat in atTop, ∀ p : Nat,
        p.Prime -> W < p -> p <= yNat n ->
        RoughCanonicalSignedExceptionalResidualBound
          n (upperTailLength c n) (K0 + 1) deltaStar
          (roughHeadCompatibleRawWeight
            W n (upperTailLength c n) (K0 + 1)
            (roughHeadBalancedAlpha
              W n (upperTailLength c n) (K0 + 1) beta (L n))
            beta (L n))
          p (C * secondOrderScale n / ((p : Real) * L n)) :=
  exists_eventually_roughCanonicalSignedExceptionalResidualBound_fourFive
    W K0 hc hdelta hdeltaUpper

end BankPaperRealization

end Erdos390.WholePaper
