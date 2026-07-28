import Erdos390.WholePaper.BankPaperCanonicalFourFiveKernelVariation

/-!
# Statement audit for frozen four/five kernel variation
-/

open scoped BigOperators

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.ArithmeticModel

noncomputable section

#check roughCanonicalFourFiveFrozenCoordinate
#check roughCanonicalFourFiveFrozenKernelWeight
#check abs_fourFiveContinuumMixtureKernel_sub_le_of_C1_bound
#check roughCanonicalFourFiveFrozenCoordinate_sub_succ
#check abs_roughCanonicalFourFiveFrozenCoordinate_sub_succ_le
#check roughCoreDiscreteVariation_le_two_mul_div_of_reciprocalSteps
#check roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_le
#check roughCoreDiscreteVariation_fourFiveFrozenKernelWeight_primePower_le
#check exists_roughCanonicalFourFiveFrozenKernelVariationConstant
#check exists_roughCanonicalFourFiveFrozenKernelPrimePowerVariationConstant

/-- Expanded terminal variation statement. -/
example :
    ∃ Cvariation : Real, 0 < Cvariation ∧
      ∀ n D B : Nat,
        0 < n ->
        0 < D ->
        1 <= Real.log (yNat n : Real) ->
        (∀ m ∈ Finset.Icc 1 B,
          Real.log ((2 * (n : Real)) / ((D * m : Nat) : Real)) /
              Real.log (yNat n : Real) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) ->
        roughCoreDiscreteVariation
            (fun m =>
              if D * m = 0 then 0 else
                fourFiveContinuumMixtureKernel
                  (Real.log
                    ((2 * (n : Real)) / ((D * m : Nat) : Real)) /
                      Real.log (yNat n : Real)) /
                    ((D * m : Nat) : Real)) B <=
          Cvariation / (D : Real) := by
  simpa only [roughCanonicalFourFiveFrozenCoordinate,
    roughCanonicalFourFiveFrozenKernelWeight] using
      exists_roughCanonicalFourFiveFrozenKernelVariationConstant

/-- Expanded chamber-facing prime-power statement. -/
example :
    ∃ Cvariation : Real, 0 < Cvariation ∧
      ∀ n p k B : Nat,
        0 < n ->
        p.Prime ->
        1 <= Real.log (yNat n : Real) ->
        (∀ m ∈ Finset.Icc 1 (B / p ^ k),
          Real.log
                ((2 * (n : Real)) / ((p ^ k * m : Nat) : Real)) /
              Real.log (yNat n : Real) ∈
            Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) ->
        roughCoreDiscreteVariation
            (fun m =>
              if p ^ k * m = 0 then 0 else
                fourFiveContinuumMixtureKernel
                  (Real.log
                    ((2 * (n : Real)) / ((p ^ k * m : Nat) : Real)) /
                      Real.log (yNat n : Real)) /
                    ((p ^ k * m : Nat) : Real))
            (B / p ^ k) <=
          Cvariation / ((p ^ k : Nat) : Real) := by
  simpa only [roughCanonicalFourFiveFrozenCoordinate,
    roughCanonicalFourFiveFrozenKernelWeight] using
      exists_roughCanonicalFourFiveFrozenKernelPrimePowerVariationConstant

end

end Erdos390.WholePaper.BankPaperRealization
