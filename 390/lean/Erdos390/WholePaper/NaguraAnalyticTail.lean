import Erdos390.WholePaper.NaguraGeneralLowerBound
import Erdos390.WholePaper.NaguraPsiBridge

/-!
# An explicit analytic tail for Nagura's interval

The arbitrary-endpoint bounds for `ψ` leave a linear gap of size about
`0.0132 n`.  A scaled elementary logarithm estimate makes Mathlib's
`2 sqrt(x) log(x)` comparison error smaller than `x / 100` once
`x ≥ 16,000,000`.
-/

namespace Erdos390.WholePaper

/-- Beyond sixteen million, the square-root error dominates the logarithm
by the explicit factor needed below. -/
theorem log_lt_sqrt_div_two_hundred {x : ℝ} (hx : 16000000 ≤ x) :
    Real.log x < Real.sqrt x / 200 := by
  have hxPos : 0 < x := by linarith
  let t : ℝ := Real.sqrt x
  have htNonneg : 0 ≤ t := by
    dsimp only [t]
    positivity
  have htSq : t ^ 2 = x := by
    dsimp only [t]
    exact Real.sq_sqrt hxPos.le
  have htLower : 4000 ≤ t := by nlinarith
  have htPos : 0 < t := by linarith
  have hSmall := Real.log_le_sub_one_of_pos
    (show 0 < t / 1000 by positivity)
  have hLogThousand : Real.log 1000 < 7 := by
    have hMono : Real.log (1000 : ℝ) < Real.log ((2 : ℝ) ^ 10) :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    rw [Real.log_pow] at hMono
    norm_num at hMono
    linarith [Real.log_two_lt_d9]
  have hSplit :
      Real.log t = Real.log (t / 1000) + Real.log 1000 := by
    calc
      Real.log t = Real.log ((t / 1000) * 1000) := by
        congr 1
        field_simp
      _ = Real.log (t / 1000) + Real.log 1000 :=
        Real.log_mul (div_ne_zero (ne_of_gt htPos) (by norm_num))
          (by norm_num)
  have hLogT : Real.log t < t / 400 := by
    rw [hSplit]
    linarith
  have hLogX : Real.log x = 2 * Real.log t := by
    calc
      Real.log x = Real.log (t ^ 2) := by rw [htSq]
      _ = 2 * Real.log t := by rw [Real.log_pow]; norm_num
  rw [hLogX]
  linarith

theorem two_sqrt_mul_log_lt_div_one_hundred {x : ℝ}
    (hx : 16000000 ≤ x) :
    2 * Real.sqrt x * Real.log x < x / 100 := by
  have hxPos : 0 < x := by linarith
  have hLog := log_lt_sqrt_div_two_hundred hx
  have hSqrtPos : 0 < Real.sqrt x := Real.sqrt_pos.2 hxPos
  have hMul := mul_lt_mul_of_pos_left hLog
    (show 0 < 2 * Real.sqrt x by positivity)
  have hSq := Real.sq_sqrt hxPos.le
  calc
    2 * Real.sqrt x * Real.log x <
        2 * Real.sqrt x * (Real.sqrt x / 200) := by
      simpa only [mul_assoc] using hMul
    _ = (Real.sqrt x) ^ 2 / 100 := by ring
    _ = x / 100 := by rw [hSq]

/-- The fully explicit analytic tail of Nagura's theorem. -/
theorem exists_prime_nagura_analytic_tail {n : ℕ}
    (hn : 16000000 ≤ n) : HasNaguraPrime n := by
  let u := naguraStrictUpper n
  have hnUpper : 1000000 ≤ n := by omega
  have huThreshold : 16000000 ≤ u := by
    dsimp only [u, naguraStrictUpper]
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
    omega
  have huLower : 20000 ≤ u := by omega
  have hPsiUpper := psi_nat_lt_1_086_mul hnUpper
  have hPsiLower := psi_nat_gt_0_916_mul huLower
  have hError := two_sqrt_mul_log_lt_div_one_hundred
    (show (16000000 : ℝ) ≤ (u : ℝ) by exact_mod_cast huThreshold)
  have hFloorLower : 6 * n ≤ 5 * u + 5 := by
    dsimp only [u, naguraStrictUpper]
    have hDiv := Nat.lt_mul_div_succ (6 * n - 1)
      (by norm_num : 0 < 5)
    omega
  have hFloorLowerR :
      (6 : ℝ) * (n : ℝ) ≤ 5 * (u : ℝ) + 5 := by
    exact_mod_cast hFloorLower
  have hnR : (16000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hNumeric :
      (543 : ℝ) / 500 * (n : ℝ) + (u : ℝ) / 100 <
        (229 : ℝ) / 250 * (u : ℝ) := by
    linarith
  have hGap :
      Chebyshev.psi (n : ℝ) +
          2 * Real.sqrt (u : ℝ) * Real.log (u : ℝ) <
        Chebyshev.psi (u : ℝ) := by
    calc
      Chebyshev.psi (n : ℝ) +
            2 * Real.sqrt (u : ℝ) * Real.log (u : ℝ) <
          (543 : ℝ) / 500 * (n : ℝ) + (u : ℝ) / 100 :=
        add_lt_add hPsiUpper hError
      _ < (229 : ℝ) / 250 * (u : ℝ) := hNumeric
      _ < Chebyshev.psi (u : ℝ) := hPsiLower
  exact hasNaguraPrime_of_psi_gap (by omega) hGap

end Erdos390.WholePaper
