import Erdos1002

open Filter MeasureTheory Set
open scoped BigOperators

#check Erdos1002.erdos1002
#print axioms Erdos1002.erdos1002
#check Erdos1002.erdos1002_official
#print axioms Erdos1002.erdos1002_official

namespace Erdos1002

example : Erdos1002Conclusion := erdos1002

example :
    ∃ g : ℝ → ℝ,
      Monotone g ∧
      Tendsto g atBot (nhds 0) ∧
      Tendsto g atTop (nhds 1) ∧
      ∀ c : ℝ,
        Tendsto
          (fun n : ℕ =>
            (volume
              {α : ℝ |
                α ∈ Ioo (0 : ℝ) 1 ∧
                  (1 / Real.log (n : ℝ)) *
                      (∑ k ∈ Finset.Icc 1 n,
                        ((1 : ℝ) / 2 - Int.fract (α * (k : ℝ)))) ≤ c}).toReal)
          atTop (nhds (g c)) :=
  erdos1002_official

/-- Definitionally expanded verification that the public theorem has the
original fixed-start statement, normalization, quantifier, and Cauchy CDF. -/
example :
    ∀ c : ℝ,
      Tendsto
        (fun N : ℕ ↦
          (volume
            {α : ℝ |
              α ∈ Ioo (0 : ℝ) 1 ∧
                (∑ k ∈ Finset.Icc 1 N,
                    ((1 : ℝ) / 2 - Int.fract ((k : ℝ) * α))) /
                    Real.log (N : ℝ) ≤
                  c}).toReal)
        atTop
        (nhds
          ((1 : ℝ) / 2 +
            (1 / Real.pi) * Real.arctan (2 * Real.pi * c))) := by
  simpa only [distributionValue, normalizedRotationSum, rotationSum,
    sawtooth, cauchyLimitCDF] using erdos1002

end Erdos1002
