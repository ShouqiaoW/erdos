import Erdos390.WholePaper.NaguraChebyshevIdentity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SumIntegralComparisons

/-!
# Effective factorial bounds for Nagura's Chebyshev sum

The exact identity `naguraChebyshevSum_eq_log_factorial` reduces analytic
bounds for Nagura's `T` function to explicit estimates for `log (n!)`.  This
file records the elementary integral upper bound, complementing Mathlib's
global Stirling lower bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- Elementary global upper bound for the factorial logarithm. -/
theorem log_factorial_le_integral_upper (n : ℕ) :
    Real.log (n.factorial : ℝ) ≤
      ((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) -
        ((n + 1 : ℕ) : ℝ) + 1 := by
  have hIntegral := MonotoneOn.sum_le_integral_Ico
    (f := Real.log) (a := 1) (b := n + 1) (by omega) (by
      intro x hx y _ hxy
      exact Real.log_le_log (lt_of_lt_of_le (by norm_num) hx.1) hxy)
  have hSum :
      (∑ k ∈ Finset.Ico 1 (n + 1), Real.log k) =
        Real.log (n.factorial : ℝ) := by
    rw [Finset.Ico_add_one_right_eq_Icc]
    exact (naguraDivisorLogSum_eq_sum_log n).symm.trans
      (naguraDivisorLogSum_eq_log_factorial n)
  rw [hSum, integral_log] at hIntegral
  simpa using hIntegral

/-- The corresponding explicit upper bound for Nagura's finite `T` sum. -/
theorem naguraChebyshevSum_le_integral_upper (n : ℕ) :
    naguraChebyshevSum n ≤
      ((n + 1 : ℕ) : ℝ) * Real.log ((n + 1 : ℕ) : ℝ) -
        ((n + 1 : ℕ) : ℝ) + 1 := by
  rw [naguraChebyshevSum_eq_log_factorial]
  exact log_factorial_le_integral_upper n

/-- The same elementary estimate, written in the form used in Nagura's
linear combination of factorial logarithms. -/
theorem log_factorial_le_stirling_elementary {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
        Real.log (n : ℝ) + 1 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  have h := log_factorial_le_integral_upper m
  rw [Nat.factorial_succ, Nat.cast_mul,
    Real.log_mul (by positivity) (by positivity)]
  linarith

/-- Elementary upper bound for Nagura's finite `T` sum in the form that
matches the Stirling lower bound term-by-term. -/
theorem naguraChebyshevSum_le_stirling_elementary {n : ℕ} (hn : n ≠ 0) :
    naguraChebyshevSum n ≤
      (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
        Real.log (n : ℝ) + 1 := by
  rw [naguraChebyshevSum_eq_log_factorial]
  exact log_factorial_le_stirling_elementary hn

end Erdos390.WholePaper
