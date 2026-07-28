import Erdos390.WholePaper.NaguraStirlingCombination
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Certified logarithm bounds used by Nagura

The only transcendental numerical input below is Mathlib's proved
`Real.log_two_lt_d9`.  The remaining logarithms are reduced to powers of two
and bounded by the explicit finite Taylor remainder theorem for
`log (1 - x)`.  Every residual calculation is rational and discharged by
`norm_num`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- A convenient one-sided form of Mathlib's finite Taylor remainder bound
for `log (1 - x)`. -/
theorem log_one_sub_le_neg_sum_add_remainder {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    Real.log (1 - x) ≤
      -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) +
        |x| ^ (n + 1) / (1 - |x|) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have hUpper := (abs_le.mp h).2
  linarith

theorem log_three_lt_1_099 :
    Real.log 3 < (1099 : ℝ) / 1000 := by
  have hResidual :
      Real.log (1 - (1 : ℝ) / 4) ≤ -(2873 : ℝ) / 10000 := by
    calc
      Real.log (1 - (1 : ℝ) / 4) ≤
          -(∑ i ∈ Finset.range 5,
              ((1 : ℝ) / 4) ^ (i + 1) / (i + 1)) +
            |(1 : ℝ) / 4| ^ (5 + 1) / (1 - |(1 : ℝ) / 4|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 5
      _ ≤ -(2873 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 3 = 2 * Real.log 2 + Real.log (1 - (1 : ℝ) / 4) := by
    calc
      Real.log 3 = Real.log ((2 : ℝ) ^ 2 * (1 - (1 : ℝ) / 4)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 2) + Real.log (1 - (1 : ℝ) / 4) := by
        rw [Real.log_mul] <;> norm_num
      _ = 2 * Real.log 2 + Real.log (1 - (1 : ℝ) / 4) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]

theorem log_three_lt_eleven_tenths :
    Real.log 3 < (11 : ℝ) / 10 :=
  log_three_lt_1_099.trans (by norm_num)

theorem log_seven_lt_1_949 :
    Real.log 7 < (1949 : ℝ) / 1000 := by
  have hResidual :
      Real.log (1 - (1 : ℝ) / 8) ≤ -(1305 : ℝ) / 10000 := by
    calc
      Real.log (1 - (1 : ℝ) / 8) ≤
          -(∑ i ∈ Finset.range 2,
              ((1 : ℝ) / 8) ^ (i + 1) / (i + 1)) +
            |(1 : ℝ) / 8| ^ (2 + 1) / (1 - |(1 : ℝ) / 8|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 2
      _ ≤ -(1305 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 7 = 3 * Real.log 2 + Real.log (1 - (1 : ℝ) / 8) := by
    calc
      Real.log 7 = Real.log ((2 : ℝ) ^ 3 * (1 - (1 : ℝ) / 8)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log (1 - (1 : ℝ) / 8) := by
        rw [Real.log_mul] <;> norm_num
      _ = 3 * Real.log 2 + Real.log (1 - (1 : ℝ) / 8) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]

theorem log_seven_lt_one_point_nine_five :
    Real.log 7 < (195 : ℝ) / 100 :=
  log_seven_lt_1_949.trans (by norm_num)

theorem log_forty_three_lt_3_762 :
    Real.log 43 < (1881 : ℝ) / 500 := by
  have hResidual :
      Real.log (1 - (21 : ℝ) / 64) ≤ -(3969 : ℝ) / 10000 := by
    calc
      Real.log (1 - (21 : ℝ) / 64) ≤
          -(∑ i ∈ Finset.range 6,
              ((21 : ℝ) / 64) ^ (i + 1) / (i + 1)) +
            |(21 : ℝ) / 64| ^ (6 + 1) / (1 - |(21 : ℝ) / 64|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 6
      _ ≤ -(3969 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 43 = 6 * Real.log 2 + Real.log (1 - (21 : ℝ) / 64) := by
    calc
      Real.log 43 = Real.log ((2 : ℝ) ^ 6 * (1 - (21 : ℝ) / 64)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 6) + Real.log (1 - (21 : ℝ) / 64) := by
        rw [Real.log_mul] <;> norm_num
      _ = 6 * Real.log 2 + Real.log (1 - (21 : ℝ) / 64) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]

theorem log_forty_three_lt_three_point_seven_seven :
    Real.log 43 < (377 : ℝ) / 100 :=
  log_forty_three_lt_3_762.trans (by norm_num)

theorem log_one_thousand_eight_hundred_six_lt_seven_point_five :
    Real.log 1806 < (15 : ℝ) / 2 := by
  have hResidual :
      Real.log (1 - (121 : ℝ) / 1024) ≤ -(1254 : ℝ) / 10000 := by
    calc
      Real.log (1 - (121 : ℝ) / 1024) ≤
          -(∑ i ∈ Finset.range 3,
              ((121 : ℝ) / 1024) ^ (i + 1) / (i + 1)) +
            |(121 : ℝ) / 1024| ^ (3 + 1) /
              (1 - |(121 : ℝ) / 1024|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 3
      _ ≤ -(1254 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 1806 =
        11 * Real.log 2 + Real.log (1 - (121 : ℝ) / 1024) := by
    calc
      Real.log 1806 =
          Real.log ((2 : ℝ) ^ 11 * (1 - (121 : ℝ) / 1024)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 11) +
          Real.log (1 - (121 : ℝ) / 1024) := by
        rw [Real.log_mul] <;> norm_num
      _ = 11 * Real.log 2 + Real.log (1 - (121 : ℝ) / 1024) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]

/-- Nagura's main logarithmic coefficient is strictly below `1.086`, using
only the certified rational bounds above. -/
theorem naguraMainCoefficient_lt_1_086 :
    naguraMainCoefficient < (543 : ℝ) / 500 := by
  unfold naguraMainCoefficient
  nlinarith [Real.log_two_lt_d9, log_three_lt_eleven_tenths,
    log_seven_lt_one_point_nine_five,
    log_forty_three_lt_three_point_seven_seven,
    log_one_thousand_eight_hundred_six_lt_seven_point_five]

/-- The same certified component bounds in fact give the slightly sharper
constant `1.085`, leaving room for Nagura's recursion by `1806`. -/
theorem naguraMainCoefficient_lt_1_085 :
    naguraMainCoefficient < (217 : ℝ) / 200 := by
  unfold naguraMainCoefficient
  nlinarith [Real.log_two_lt_d9, log_three_lt_eleven_tenths,
    log_seven_lt_one_point_nine_five,
    log_forty_three_lt_three_point_seven_seven,
    log_one_thousand_eight_hundred_six_lt_seven_point_five]

/-- A sharper certified coefficient, still using short rational Taylor
calculations only. -/
theorem naguraMainCoefficient_lt_1_083 :
    naguraMainCoefficient < (1083 : ℝ) / 1000 := by
  unfold naguraMainCoefficient
  nlinarith [Real.log_two_lt_d9, log_three_lt_1_099,
    log_seven_lt_1_949, log_forty_three_lt_3_762,
    log_one_thousand_eight_hundred_six_lt_seven_point_five]

/-- The lower-order Stirling remainder is already negative for every positive
`k`.  Powers of two give ample certified lower bounds for the four large
subtracted logarithms. -/
theorem naguraStirlingRemainder_lt_zero {k : ℕ} (hk : 0 < k) :
    naguraStirlingRemainder k < 0 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hkLog : 0 ≤ Real.log (k : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hk
  have h903 : 9 * Real.log 2 ≤ Real.log 903 := by
    calc
      9 * Real.log 2 = Real.log ((2 : ℝ) ^ 9) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log 903 := Real.log_le_log (by positivity) (by norm_num)
  have h602 : 9 * Real.log 2 ≤ Real.log 602 := by
    calc
      9 * Real.log 2 = Real.log ((2 : ℝ) ^ 9) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log 602 := Real.log_le_log (by positivity) (by norm_num)
  have h258 : 8 * Real.log 2 ≤ Real.log 258 := by
    calc
      8 * Real.log 2 = Real.log ((2 : ℝ) ^ 8) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log 258 := Real.log_le_log (by positivity) (by norm_num)
  have h42 : 5 * Real.log 2 ≤ Real.log 42 := by
    calc
      5 * Real.log 2 = Real.log ((2 : ℝ) ^ 5) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log 42 := Real.log_le_log (by positivity) (by norm_num)
  have hPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  simp only [naguraStirlingRemainder, Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (1806 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (903 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (602 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (258 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (42 : ℝ) ≠ 0) hkR]
  nlinarith [Real.log_two_gt_d9,
    log_one_thousand_eight_hundred_six_lt_seven_point_five]

/-- Fully certified analytic estimate for Nagura's `1806`-scale Chebyshev
combination. -/
theorem naguraChebyshevCombination_lt_1_086_mul
    {k : ℕ} (hk : 0 < k) :
    naguraChebyshevCombination k <
      (543 : ℝ) / 500 * ((1806 * k : ℕ) : ℝ) := by
  have hCombination := naguraChebyshevCombination_le_stirlingMajorant hk
  have hMajorant := naguraStirlingMajorant_eq_main_add_remainder hk
  have hCoefficient := naguraMainCoefficient_lt_1_086
  have hRemainder := naguraStirlingRemainder_lt_zero hk
  have hScale : 0 < (1806 : ℝ) * (k : ℝ) := by positivity
  have hMain := mul_lt_mul_of_pos_left hCoefficient hScale
  rw [hMajorant] at hCombination
  calc
    naguraChebyshevCombination k ≤
        (1806 : ℝ) * (k : ℝ) * naguraMainCoefficient +
          naguraStirlingRemainder k := hCombination
    _ < (1806 : ℝ) * (k : ℝ) * ((543 : ℝ) / 500) := by
      linarith
    _ = (543 : ℝ) / 500 * ((1806 * k : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      ring

/-- Sharper form of the combination estimate, used to absorb the recursive
`ψ(k)` term. -/
theorem naguraChebyshevCombination_lt_1_085_mul
    {k : ℕ} (hk : 0 < k) :
    naguraChebyshevCombination k <
      (217 : ℝ) / 200 * ((1806 * k : ℕ) : ℝ) := by
  have hCombination := naguraChebyshevCombination_le_stirlingMajorant hk
  have hMajorant := naguraStirlingMajorant_eq_main_add_remainder hk
  have hCoefficient := naguraMainCoefficient_lt_1_085
  have hRemainder := naguraStirlingRemainder_lt_zero hk
  have hScale : 0 < (1806 : ℝ) * (k : ℝ) := by positivity
  have hMain := mul_lt_mul_of_pos_left hCoefficient hScale
  rw [hMajorant] at hCombination
  calc
    naguraChebyshevCombination k ≤
        (1806 : ℝ) * (k : ℝ) * naguraMainCoefficient +
          naguraStirlingRemainder k := hCombination
    _ < (1806 : ℝ) * (k : ℝ) * ((217 : ℝ) / 200) := by
      linarith
    _ = (217 : ℝ) / 200 * ((1806 * k : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      ring

/-- The sharpened combination estimate used in the final explicit
`ψ(1806 k)` upper bound. -/
theorem naguraChebyshevCombination_lt_1_083_mul
    {k : ℕ} (hk : 0 < k) :
    naguraChebyshevCombination k <
      (1083 : ℝ) / 1000 * ((1806 * k : ℕ) : ℝ) := by
  have hCombination := naguraChebyshevCombination_le_stirlingMajorant hk
  have hMajorant := naguraStirlingMajorant_eq_main_add_remainder hk
  have hCoefficient := naguraMainCoefficient_lt_1_083
  have hRemainder := naguraStirlingRemainder_lt_zero hk
  have hScale : 0 < (1806 : ℝ) * (k : ℝ) := by positivity
  have hMain := mul_lt_mul_of_pos_left hCoefficient hScale
  rw [hMajorant] at hCombination
  calc
    naguraChebyshevCombination k ≤
        (1806 : ℝ) * (k : ℝ) * naguraMainCoefficient +
          naguraStirlingRemainder k := hCombination
    _ < (1806 : ℝ) * (k : ℝ) * ((1083 : ℝ) / 1000) := by
      linarith
    _ = (1083 : ℝ) / 1000 * ((1806 * k : ℕ) : ℝ) := by
      norm_num [Nat.cast_mul]
      ring

end Erdos390.WholePaper
