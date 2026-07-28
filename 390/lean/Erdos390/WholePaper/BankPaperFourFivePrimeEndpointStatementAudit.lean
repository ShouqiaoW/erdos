import Erdos390.WholePaper.BankPaperFourFivePrimeEndpoint

/-! Expanded statement audit for the four/five prime-counting endpoint. -/

open Set

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeBandQuadrature

#check fourFiveLogIntegralIncrement
#check fourFivePrimeCountingErrorKernel
#check fourFiveLogIntegralIncrement_eq_integral_inv_log
#check fourFivePrimeCounting_sub_logIntegralIncrement_eq_thetaError
#check fourFivePrimeCounting_sub_integral_inv_log_eq_thetaError
#check abs_fourFivePrimeCounting_sub_logIntegralIncrement_le
#check abs_fourFivePrimeCounting_sub_integral_inv_log_le
#check exists_abs_fourFivePrimeCounting_sub_logIntegralIncrement_le
#check exists_abs_fourFivePrimeCounting_sub_integral_inv_log_le

example (A B : Real) :
    fourFiveLogIntegralIncrement A B =
      B / Real.log B - A / Real.log A +
        ∫ t in A..B, 1 / Real.log t ^ 2 := by
  rfl

example {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    fourFiveLogIntegralIncrement A B =
      ∫ t in A..B, 1 / Real.log t :=
  fourFiveLogIntegralIncrement_eq_integral_inv_log hA hAB

example {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    ((Nat.primeCounting ⌊B⌋₊ : Real) -
        (Nat.primeCounting ⌊A⌋₊ : Real)) -
        fourFiveLogIntegralIncrement A B =
      thetaError B / Real.log B - thetaError A / Real.log A +
        ∫ t in A..B, fourFivePrimeCountingErrorKernel t :=
  fourFivePrimeCounting_sub_logIntegralIncrement_eq_thetaError hA hAB

example {A B : Real} (hA : 2 <= A) (hAB : A <= B) :
    ((Nat.primeCounting ⌊B⌋₊ : Real) -
        (Nat.primeCounting ⌊A⌋₊ : Real)) -
        (∫ t in A..B, 1 / Real.log t) =
      thetaError B / Real.log B - thetaError A / Real.log A +
        ∫ t in A..B, fourFivePrimeCountingErrorKernel t :=
  fourFivePrimeCounting_sub_integral_inv_log_eq_thetaError hA hAB

example {A B C : Real} (hA : 3 <= A) (hAB : A <= B) (hC : 0 <= C)
    (hTheta : ∀ t ∈ Icc A B,
      |thetaError t| <= C * t / Real.log t ^ 4) :
    abs (((Nat.primeCounting ⌊B⌋₊ : Real) -
        (Nat.primeCounting ⌊A⌋₊ : Real)) -
        fourFiveLogIntegralIncrement A B) <=
      3 * C * B / Real.log A ^ 5 :=
  abs_fourFivePrimeCounting_sub_logIntegralIncrement_le hA hAB hC hTheta

example :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      forall A B : Real, X0 <= A -> A <= B ->
        abs (((Nat.primeCounting ⌊B⌋₊ : Real) -
            (Nat.primeCounting ⌊A⌋₊ : Real)) -
            fourFiveLogIntegralIncrement A B) <=
          3 * C * B / Real.log A ^ 5 :=
  exists_abs_fourFivePrimeCounting_sub_logIntegralIncrement_le

example :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      forall A B : Real, X0 <= A -> A <= B ->
        abs (((Nat.primeCounting ⌊B⌋₊ : Real) -
            (Nat.primeCounting ⌊A⌋₊ : Real)) -
            (∫ t in A..B, 1 / Real.log t)) <=
          3 * C * B / Real.log A ^ 5 :=
  exists_abs_fourFivePrimeCounting_sub_integral_inv_log_le

end Erdos390.WholePaper.BankPaperRealization
