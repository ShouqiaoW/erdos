import Erdos390.WholePaper.NaguraLowerCombination

/-!
# Explicit Nagura-style bounds for `ψ` on arithmetic progressions

This file completes the safe factorial/Stirling chain for the lower
`2,3,5,30` combination.  Together with the upper `1806` combination, it gives
fully explicit, unconditional `ψ` estimates at natural endpoints divisible
by the relevant common denominator.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

/-- One-sided lower form of the finite Taylor remainder for `log (1 - x)`. -/
theorem neg_sum_sub_remainder_le_log_one_sub {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) -
        |x| ^ (n + 1) / (1 - |x|) ≤ Real.log (1 - x) := by
  have h := Real.abs_log_sub_add_sum_range_le hx n
  have hLower := (abs_le.mp h).1
  linarith

theorem log_three_gt_1_098 :
    (549 : ℝ) / 500 < Real.log 3 := by
  have hResidual :
      -(288 : ℝ) / 1000 ≤ Real.log (1 - (1 : ℝ) / 4) := by
    calc
      -(288 : ℝ) / 1000 ≤
          -(∑ i ∈ Finset.range 5,
              ((1 : ℝ) / 4) ^ (i + 1) / (i + 1)) -
            |(1 : ℝ) / 4| ^ (5 + 1) / (1 - |(1 : ℝ) / 4|) := by
        norm_num [Finset.sum_range_succ]
      _ ≤ Real.log (1 - (1 : ℝ) / 4) :=
        neg_sum_sub_remainder_le_log_one_sub (by norm_num) 5
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
  nlinarith [Real.log_two_gt_d9]

theorem log_five_gt_1_609 :
    (1609 : ℝ) / 1000 < Real.log 5 := by
  have hResidual :
      -(4703 : ℝ) / 10000 ≤ Real.log (1 - (3 : ℝ) / 8) := by
    calc
      -(4703 : ℝ) / 10000 ≤
          -(∑ i ∈ Finset.range 8,
              ((3 : ℝ) / 8) ^ (i + 1) / (i + 1)) -
            |(3 : ℝ) / 8| ^ (8 + 1) / (1 - |(3 : ℝ) / 8|) := by
        norm_num [Finset.sum_range_succ]
      _ ≤ Real.log (1 - (3 : ℝ) / 8) :=
        neg_sum_sub_remainder_le_log_one_sub (by norm_num) 8
  have hSplit :
      Real.log 5 = 3 * Real.log 2 + Real.log (1 - (3 : ℝ) / 8) := by
    calc
      Real.log 5 = Real.log ((2 : ℝ) ^ 3 * (1 - (3 : ℝ) / 8)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log (1 - (3 : ℝ) / 8) := by
        rw [Real.log_mul] <;> norm_num
      _ = 3 * Real.log 2 + Real.log (1 - (3 : ℝ) / 8) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_gt_d9]

theorem log_thirty_lt_3_402 :
    Real.log 30 < (1701 : ℝ) / 500 := by
  have hResidual :
      Real.log (1 - (1 : ℝ) / 16) ≤ -(641 : ℝ) / 10000 := by
    calc
      Real.log (1 - (1 : ℝ) / 16) ≤
          -(∑ i ∈ Finset.range 2,
              ((1 : ℝ) / 16) ^ (i + 1) / (i + 1)) +
            |(1 : ℝ) / 16| ^ (2 + 1) / (1 - |(1 : ℝ) / 16|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 2
      _ ≤ -(641 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 30 = 5 * Real.log 2 + Real.log (1 - (1 : ℝ) / 16) := by
    calc
      Real.log 30 = Real.log ((2 : ℝ) ^ 5 * (1 - (1 : ℝ) / 16)) := by norm_num
      _ = Real.log ((2 : ℝ) ^ 5) + Real.log (1 - (1 : ℝ) / 16) := by
        rw [Real.log_mul] <;> norm_num
      _ = 5 * Real.log 2 + Real.log (1 - (1 : ℝ) / 16) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]

/-- The main coefficient of Nagura's lower factorial combination. -/
noncomputable def naguraLowerMainCoefficient : ℝ :=
  Real.log 2 / 2 + Real.log 3 / 3 + Real.log 5 / 5 -
    Real.log 30 / 30

theorem naguraLowerMainCoefficient_gt_0_9209 :
    (9209 : ℝ) / 10000 < naguraLowerMainCoefficient := by
  unfold naguraLowerMainCoefficient
  nlinarith [Real.log_two_gt_d9, log_three_gt_1_098,
    log_five_gt_1_609, log_thirty_lt_3_402]

/-- The Stirling minorant for the lower `2,3,5,30` combination at `30k`. -/
noncomputable def naguraLowerStirlingMinorant (k : ℕ) : ℝ :=
  naguraFactorialLogLower (30 * k) - naguraFactorialLogUpper (15 * k) -
    naguraFactorialLogUpper (10 * k) - naguraFactorialLogUpper (6 * k) +
      naguraFactorialLogLower k

/-- Its lower-order remainder after exact cancellation of the linear and
`k log k` main terms. -/
noncomputable def naguraLowerStirlingRemainder (k : ℕ) : ℝ :=
  Real.log ((30 * k : ℕ) : ℝ) / 2 - Real.log ((15 * k : ℕ) : ℝ) -
    Real.log ((10 * k : ℕ) : ℝ) - Real.log ((6 * k : ℕ) : ℝ) +
      Real.log (k : ℝ) / 2 + Real.log (2 * Real.pi) - 3

theorem naguraLowerStirlingMinorant_eq_main_add_remainder
    {k : ℕ} (hk : 0 < k) :
    naguraLowerStirlingMinorant k =
      (30 : ℝ) * (k : ℝ) * naguraLowerMainCoefficient +
        naguraLowerStirlingRemainder k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have h15 : Real.log (15 : ℝ) = Real.log 30 - Real.log 2 := by
    calc
      Real.log (15 : ℝ) = Real.log ((30 : ℝ) / 2) := by norm_num
      _ = Real.log 30 - Real.log 2 := Real.log_div (by norm_num) (by norm_num)
  have h10 : Real.log (10 : ℝ) = Real.log 30 - Real.log 3 := by
    calc
      Real.log (10 : ℝ) = Real.log ((30 : ℝ) / 3) := by norm_num
      _ = Real.log 30 - Real.log 3 := Real.log_div (by norm_num) (by norm_num)
  have h6 : Real.log (6 : ℝ) = Real.log 30 - Real.log 5 := by
    calc
      Real.log (6 : ℝ) = Real.log ((30 : ℝ) / 5) := by norm_num
      _ = Real.log 30 - Real.log 5 := Real.log_div (by norm_num) (by norm_num)
  simp only [naguraLowerStirlingMinorant, naguraFactorialLogLower,
    naguraFactorialLogUpper, naguraLowerMainCoefficient,
    naguraLowerStirlingRemainder, Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (30 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (15 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hkR,
    h15, h10, h6]
  ring

/-- Stirling bounds sandwich the factorial combination from below. -/
theorem naguraLowerStirlingMinorant_le_combination
    {k : ℕ} (hk : 0 < k) :
    naguraLowerStirlingMinorant k ≤
      naguraLowerChebyshevCombination (30 * k) := by
  have hk0 : k ≠ 0 := Nat.ne_of_gt hk
  have h30 : (30 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h15 : (15 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h10 : (10 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h6 : (6 * k : ℕ) ≠ 0 := Nat.mul_ne_zero (by norm_num) hk0
  have h30Lower := naguraFactorialLogLower_le_log_factorial h30
  have hkLower := naguraFactorialLogLower_le_log_factorial hk0
  have h15Upper := log_factorial_le_naguraFactorialLogUpper h15
  have h10Upper := log_factorial_le_naguraFactorialLogUpper h10
  have h6Upper := log_factorial_le_naguraFactorialLogUpper h6
  simp only [naguraLowerChebyshevCombination,
    naguraChebyshevSum_eq_log_factorial]
  have h2 : 30 * k / 2 = 15 * k := by omega
  have h3 : 30 * k / 3 = 10 * k := by omega
  have h5 : 30 * k / 5 = 6 * k := by omega
  have h30div : 30 * k / 30 = k := by omega
  rw [h2, h3, h5, h30div]
  unfold naguraLowerStirlingMinorant
  linarith

/-- A deliberately simple explicit logarithm bound, sufficient to control
the lower-order Stirling remainder. -/
theorem log_nat_lt_div_one_hundred_add_four {k : ℕ} (hk : 0 < k) :
    Real.log (k : ℝ) < (k : ℝ) / 100 + 4 := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have hkPos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hSmall := Real.log_le_sub_one_of_pos
    (show 0 < (k : ℝ) / 100 by positivity)
  have hLogHundred : Real.log 100 < 5 := by
    have hMono : Real.log (100 : ℝ) < Real.log ((2 : ℝ) ^ 7) :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    rw [Real.log_pow] at hMono
    norm_num at hMono
    nlinarith [Real.log_two_lt_d9]
  have hSplit :
      Real.log (k : ℝ) = Real.log ((k : ℝ) / 100) + Real.log 100 := by
    calc
      Real.log (k : ℝ) = Real.log (((k : ℝ) / 100) * 100) := by
        congr 1
        field_simp
      _ = Real.log ((k : ℝ) / 100) + Real.log 100 :=
        Real.log_mul (div_ne_zero hkR (by norm_num)) (by norm_num)
  rw [hSplit]
  linarith

/-- A coarse but fully explicit lower estimate for the lower-order
Stirling remainder. -/
theorem neg_eleven_sub_two_log_lt_naguraLowerStirlingRemainder
    {k : ℕ} (hk : 0 < k) :
    -11 - 2 * Real.log (k : ℝ) < naguraLowerStirlingRemainder k := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have h15 : Real.log 15 < 4 * Real.log 2 := by
    calc
      Real.log 15 < Real.log ((2 : ℝ) ^ 4) :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      _ = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h10 : Real.log 10 < 4 * Real.log 2 := by
    calc
      Real.log 10 < Real.log ((2 : ℝ) ^ 4) :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      _ = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h6 : Real.log 6 < 3 * Real.log 2 := by
    calc
      Real.log 6 < Real.log ((2 : ℝ) ^ 3) :=
        Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
      _ = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h30 : 0 ≤ Real.log 30 := Real.log_nonneg (by norm_num)
  have hPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  simp only [naguraLowerStirlingRemainder, Nat.cast_mul, Nat.cast_ofNat]
  rw [Real.log_mul (by norm_num : (30 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (15 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (10 : ℝ) ≠ 0) hkR,
    Real.log_mul (by norm_num : (6 : ℝ) ≠ 0) hkR]
  nlinarith [Real.log_two_lt_d9]

/-- Explicit analytic lower bound for the factorial combination once
`30k ≥ 4500`. -/
theorem naguraLowerChebyshevCombination_gt_0_916_mul
    {k : ℕ} (hk : 150 ≤ k) :
    (229 : ℝ) / 250 * ((30 * k : ℕ) : ℝ) <
      naguraLowerChebyshevCombination (30 * k) := by
  have hkPos : 0 < k := by omega
  have hMinorant := naguraLowerStirlingMinorant_le_combination hkPos
  have hIdentity := naguraLowerStirlingMinorant_eq_main_add_remainder hkPos
  have hCoefficient := naguraLowerMainCoefficient_gt_0_9209
  have hRemainder :=
    neg_eleven_sub_two_log_lt_naguraLowerStirlingRemainder hkPos
  have hLog := log_nat_lt_div_one_hundred_add_four hkPos
  have hScale : 0 < (30 : ℝ) * (k : ℝ) := by positivity
  have hMain := mul_lt_mul_of_pos_left hCoefficient hScale
  have hkR : (150 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rw [hIdentity] at hMinorant
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hMinorant ⊢
  nlinarith

/-- Fully unconditional Nagura-style lower bound on `ψ` at positive
multiples of `30` beyond the explicit threshold `3900`. -/
theorem psi_mul_30_gt_0_916 {k : ℕ} (hk : 150 ≤ k) :
    (229 : ℝ) / 250 * ((30 * k : ℕ) : ℝ) <
      Chebyshev.psi ((30 * k : ℕ) : ℝ) := by
  exact (naguraLowerChebyshevCombination_gt_0_916_mul hk).trans_le
    (naguraLowerChebyshevCombination_le_psi (30 * k))

/-- Rounding down to a multiple of `30` gives an unconditional global lower
bound.  The additive loss `27.48 = 0.916 * 30` is exactly the cost of this
safe rounding step. -/
theorem psi_gt_0_916_mul_sub_27_48 {n : ℕ} (hn : 4500 ≤ n) :
    (229 : ℝ) / 250 * (n : ℝ) - (687 : ℝ) / 25 <
      Chebyshev.psi (n : ℝ) := by
  let k := n / 30
  have hk : 150 ≤ k := by
    dsimp only [k]
    omega
  have hLower := psi_mul_30_gt_0_916 hk
  have hMulLe : 30 * k ≤ n := by
    dsimp only [k]
    omega
  have hClose : n < 30 * k + 30 := by
    dsimp only [k]
    omega
  have hMono :
      Chebyshev.psi ((30 * k : ℕ) : ℝ) ≤ Chebyshev.psi (n : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hMulLe)
  have hCloseR : (n : ℝ) < (30 * k : ℕ) + 30 := by exact_mod_cast hClose
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hLower hMono hCloseR ⊢
  nlinarith

/-- Rounding up to a multiple of `1806` gives an unconditional global upper
bound.  This isolates the additive loss caused by restricting the fully
proved sharp estimate to that arithmetic progression. -/
theorem psi_lt_1_086_mul_add_1961_316 {n : ℕ} (hn : 0 < n) :
    Chebyshev.psi (n : ℝ) <
      (543 : ℝ) / 500 * (n : ℝ) + (490329 : ℝ) / 250 := by
  let k := (n + 1805) / 1806
  have hk : 0 < k := by
    dsimp only [k]
    omega
  have hnLe : n ≤ 1806 * k := by
    dsimp only [k]
    omega
  have hClose : 1806 * k < n + 1806 := by
    dsimp only [k]
    omega
  have hUpper := psi_mul_1806_lt_1_086 hk
  have hMono :
      Chebyshev.psi (n : ℝ) ≤ Chebyshev.psi ((1806 * k : ℕ) : ℝ) :=
    Chebyshev.psi_mono (by exact_mod_cast hnLe)
  have hCloseR : ((1806 * k : ℕ) : ℝ) < (n : ℝ) + 1806 := by
    exact_mod_cast hClose
  norm_num only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat] at hUpper hMono hCloseR ⊢
  nlinarith

end Erdos390.WholePaper
