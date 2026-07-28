import Erdos390.WholePaper.NaguraFactorialBounds
import Mathlib.Analysis.SpecialFunctions.Stirling

/-!
# Nagura's explicit Stirling combination

Nagura uses the reciprocal identity

`1 / 2 + 1 / 3 + 1 / 7 + 1 / 43 + 1 / 1806 = 1`

to combine six values of his finite Chebyshev sum.  This file records the
analytic half of that argument: the positive term is bounded by the elementary
factorial estimate, and the five subtracted terms are bounded with Mathlib's
proved Stirling lower bound.
-/

namespace Erdos390.WholePaper

/-- The elementary upper model for `log (n!)`. -/
noncomputable def naguraFactorialLogUpper (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) + Real.log (n : ℝ) + 1

/-- The proved Stirling lower model for `log (n!)`. -/
noncomputable def naguraFactorialLogLower (n : ℕ) : ℝ :=
  (n : ℝ) * Real.log (n : ℝ) - (n : ℝ) +
    Real.log (n : ℝ) / 2 + Real.log (2 * Real.pi) / 2

/-- The coefficient of the main linear term after Nagura's reciprocal
identity cancels the `k * log k` terms. -/
noncomputable def naguraMainCoefficient : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 7 / 7 +
    Real.log 43 / 43 + Real.log 1806 / 1806

/-- Nagura's six-term combination of finite Chebyshev sums, at the common
denominator `1806 = 2 * 3 * 7 * 43`. -/
noncomputable def naguraChebyshevCombination (k : ℕ) : ℝ :=
  naguraChebyshevSum (1806 * k) - naguraChebyshevSum (903 * k) -
    naguraChebyshevSum (602 * k) - naguraChebyshevSum (258 * k) -
      naguraChebyshevSum (42 * k) - naguraChebyshevSum k

/-- The completely explicit Stirling majorant for Nagura's six-term
Chebyshev combination. -/
noncomputable def naguraStirlingMajorant (k : ℕ) : ℝ :=
  naguraFactorialLogUpper (1806 * k) -
    naguraFactorialLogLower (903 * k) -
      naguraFactorialLogLower (602 * k) -
        naguraFactorialLogLower (258 * k) -
          naguraFactorialLogLower (42 * k) -
            naguraFactorialLogLower k

/-- The lower-order part left after extracting Nagura's main linear
coefficient from the Stirling majorant. -/
noncomputable def naguraStirlingRemainder (k : ℕ) : ℝ :=
  Real.log ((1806 * k : ℕ) : ℝ) + 1 -
    Real.log ((903 * k : ℕ) : ℝ) / 2 -
      Real.log ((602 * k : ℕ) : ℝ) / 2 -
        Real.log ((258 * k : ℕ) : ℝ) / 2 -
          Real.log ((42 * k : ℕ) : ℝ) / 2 -
            Real.log (k : ℝ) / 2 -
              5 * Real.log (2 * Real.pi) / 2

/-- The Egyptian-fraction identity responsible for cancellation of all
`k * log k` and linear terms in Nagura's combination. -/
theorem nagura_reciprocal_numerators :
    903 + 602 + 258 + 42 + 1 = 1806 := by
  norm_num

/-- Mathlib's Stirling theorem supplies the lower model for every positive
factorial argument. -/
theorem naguraFactorialLogLower_le_log_factorial {n : ℕ} (hn : n ≠ 0) :
    naguraFactorialLogLower n ≤ Real.log (n.factorial : ℝ) := by
  exact Stirling.le_log_factorial_stirling hn

/-- The elementary integral estimate supplies the upper model. -/
theorem log_factorial_le_naguraFactorialLogUpper {n : ℕ} (hn : n ≠ 0) :
    Real.log (n.factorial : ℝ) ≤ naguraFactorialLogUpper n := by
  exact log_factorial_le_stirling_elementary hn

/-- Exact simplification of the explicit Stirling majorant.  In particular,
the cancellation of the `k * log k` and linear terms is checked by the
kernel, rather than used as an informal asymptotic calculation. -/
theorem naguraStirlingMajorant_eq_main_add_remainder
    {k : ℕ} (hk : 0 < k) :
    naguraStirlingMajorant k =
      (1806 : ℝ) * (k : ℝ) * naguraMainCoefficient +
        naguraStirlingRemainder k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have h903 : Real.log (903 : ℝ) = Real.log 1806 - Real.log 2 := by
    calc
      Real.log (903 : ℝ) = Real.log ((1806 : ℝ) / 2) := by norm_num
      _ = Real.log 1806 - Real.log 2 :=
        Real.log_div (by norm_num) (by norm_num)
  have h602 : Real.log (602 : ℝ) = Real.log 1806 - Real.log 3 := by
    calc
      Real.log (602 : ℝ) = Real.log ((1806 : ℝ) / 3) := by norm_num
      _ = Real.log 1806 - Real.log 3 :=
        Real.log_div (by norm_num) (by norm_num)
  have h258 : Real.log (258 : ℝ) = Real.log 1806 - Real.log 7 := by
    calc
      Real.log (258 : ℝ) = Real.log ((1806 : ℝ) / 7) := by norm_num
      _ = Real.log 1806 - Real.log 7 :=
        Real.log_div (by norm_num) (by norm_num)
  have h42 : Real.log (42 : ℝ) = Real.log 1806 - Real.log 43 := by
    calc
      Real.log (42 : ℝ) = Real.log ((1806 : ℝ) / 43) := by norm_num
      _ = Real.log 1806 - Real.log 43 :=
        Real.log_div (by norm_num) (by norm_num)
  simp only [naguraStirlingMajorant, naguraFactorialLogUpper,
    naguraFactorialLogLower, naguraMainCoefficient, naguraStirlingRemainder,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (1806 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (903 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (602 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (258 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (42 : ℝ) ≠ 0) hkR,
    h903, h602, h258, h42]
  ring

/-- Nagura's Chebyshev combination is bounded above by the fully explicit
Stirling expression. -/
theorem naguraChebyshevCombination_le_stirlingMajorant
    {k : ℕ} (hk : 0 < k) :
    naguraChebyshevCombination k ≤ naguraStirlingMajorant k := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have h1806 : (1806 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h903 : (903 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h602 : (602 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h258 : (258 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h42 : (42 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have hUpper := log_factorial_le_naguraFactorialLogUpper h1806
  have h903Lower := naguraFactorialLogLower_le_log_factorial h903
  have h602Lower := naguraFactorialLogLower_le_log_factorial h602
  have h258Lower := naguraFactorialLogLower_le_log_factorial h258
  have h42Lower := naguraFactorialLogLower_le_log_factorial h42
  have hkLower := naguraFactorialLogLower_le_log_factorial hk0
  simp only [naguraChebyshevCombination, naguraChebyshevSum_eq_log_factorial]
  unfold naguraStirlingMajorant
  linarith

end Erdos390.WholePaper
