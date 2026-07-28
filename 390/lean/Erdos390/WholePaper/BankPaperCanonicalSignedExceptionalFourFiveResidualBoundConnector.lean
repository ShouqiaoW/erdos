import Erdos390.WholePaper.BankPaperCanonicalSignedExceptionalFourFiveRemainingInputsConnector

/-!
# Unconditional signed exceptional four/five residual bound

The remaining-input connector supplies the six nonnegative interval
constants required by the four/five chamber.  The chamber connector then
supplies its positive variation constant and the eventual signed exceptional
residual estimate.

This file performs only that final existential composition.  Its exported
constant absorbs the deep, cutoff, and variation constants appearing in the
conditional chamber theorem.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-- The signed exceptional four/five chamber is unconditional once its
geometry, deep-prefix, and cutoff-band precursor connectors are composed. -/
theorem
    exists_eventually_roughCanonicalSignedExceptionalResidualBound_fourFive
    (W K0 : Nat) {c deltaStar beta : Real}
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
          p (C * secondOrderScale n / ((p : Real) * L n)) := by
  obtain ⟨deepPlus, deepHigh, deepBroad,
      cutoffPlus, cutoffHigh, cutoffBroad,
      hdeepPlus, hdeepHigh, hdeepBroad,
      hcutoffPlus, hcutoffHigh, hcutoffBroad, hinputs⟩ :=
    exists_roughCanonicalSignedExceptionalFourFiveRemainingInputs
      W K0 hc hdelta hdeltaUpper
  obtain ⟨Cvariation, hCvariation, hbound⟩ :=
    exists_eventually_roughCanonicalSignedExceptionalResidualBound_of_fourFiveInputs
      (W := W) (K0 := K0) (c := c) (deltaStar := deltaStar)
      (beta := beta) hc hdelta hdeltaUpper
      hdeepPlus hdeepHigh hdeepBroad
      hcutoffPlus hcutoffHigh hcutoffBroad hinputs
  let C :=
    roughCanonicalSignedExceptionalCoreBoundConstant W c deltaStar
      (roughCanonicalFourFiveDeepCoreConstant
        W K0 c beta deepPlus deepHigh deepBroad)
      (roughCanonicalFourFiveCutoffCoreConstant
        W K0 c beta cutoffPlus cutoffHigh cutoffBroad)
      Cvariation
  refine ⟨C, ?_, ?_⟩
  · dsimp only [C]
    exact
      roughCanonicalSignedExceptionalCoreBoundConstant_nonneg
        hc.le hdelta.le
        (roughCanonicalFourFiveDeepCoreConstant_nonneg
          hc.le hdeepPlus hdeepHigh hdeepBroad)
        (roughCanonicalFourFiveCutoffCoreConstant_nonneg
          hc.le hcutoffPlus hcutoffHigh hcutoffBroad)
        hCvariation.le
  · simpa only [C] using hbound

end BankPaperRealization

end

end Erdos390.WholePaper
