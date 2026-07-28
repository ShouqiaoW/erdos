import Erdos390.Full.FriableAsymptotic

/-!
# The elementary `p L / yNat^4` tail rate

The valuation cutoff used in the nuisance estimates is `T = yNat n ^ 4`.
For every active prime `p <= yNat n`, its omitted tail becomes negligible
on the sharp `1 / (p L)` scale because `p L / T -> 0` uniformly in `p`.
-/

open Filter Topology

namespace Erdos390.Full.PaperPrimePowerTailRate

open ArithmeticModel Scale

noncomputable section

theorem tendsto_L_div_three_fifths :
    Tendsto (fun n : ℕ ↦
      L n / (n : ℝ) ^ (3 / 5 : ℝ)) atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x / x ^ (3 / 5 : ℝ))
      atTop (𝓝 0) := by
    simpa using
      (isLittleO_log_rpow_rpow_atTop (1 : ℝ)
        (by norm_num : (0 : ℝ) < 3 / 5)).tendsto_div_nhds_zero
  simpa only [L, Real.rpow_one] using
    hreal.comp tendsto_natCast_atTop_atTop

/-- The integral smoothness cutoff is eventually at least `n^(1/5)`.
This deliberately uses only the already-proved logarithmic lower bound for
`yNat`; no informal floor comparison is hidden. -/
theorem eventually_rpow_one_fifth_le_yNat :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (1 / 5 : ℝ) ≤ (yNat n : ℝ) := by
  filter_upwards [FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
    Filter.eventually_gt_atTop 1] with n hlog hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hL : 0 < L n := L_pos hn
  have hlogYpos : 0 < Real.log (yNat n : ℝ) := by
    exact (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlog
  have hYpos : (0 : ℝ) < (yNat n : ℝ) :=
    (Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogYpos |>.trans' zero_lt_one
  calc
    (n : ℝ) ^ (1 / 5 : ℝ) =
        Real.exp ((1 / 5 : ℝ) * L n) := by
      rw [Real.rpow_def_of_pos hnpos]
      congr 1
      unfold L
      ring
    _ ≤ Real.exp (Real.log (yNat n : ℝ)) :=
      Real.exp_le_exp.mpr hlog
    _ = (yNat n : ℝ) := Real.exp_log hYpos

/-- Uniform arithmetic tail comparison in the exact form needed after the
logarithmic valuation cutoff. -/
theorem eventually_prime_mul_L_div_yNat_pow_four_le_one :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, p ≤ yNat n →
      (p : ℝ) * L n / (yNat n : ℝ) ^ 4 ≤ 1 := by
  have hratio : ∀ᶠ n : ℕ in atTop,
      L n / (n : ℝ) ^ (3 / 5 : ℝ) ≤ 1 :=
    (tendsto_L_div_three_fifths.eventually
      (Iic_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  filter_upwards [eventually_rpow_one_fifth_le_yNat, hratio,
    FriableAsymptotic.eventually_one_fifth_L_le_log_yNat,
    Filter.eventually_gt_atTop 1] with n hY hratioN hlog hn
  intro p hp
  let Y : ℝ := yNat n
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hL : 0 < L n := L_pos hn
  have hlogYpos : 0 < Real.log Y := by
    dsimp only [Y]
    exact (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlog
  have hYpos : 0 < Y :=
    (Real.log_pos_iff (by dsimp only [Y]; positivity)).mp hlogYpos |>.trans'
      zero_lt_one
  have hpY : (p : ℝ) ≤ Y := by
    dsimp only [Y]
    exact_mod_cast hp
  have hnPowPos : 0 < (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.rpow_pos_of_pos hnpos _
  have hY3 : (n : ℝ) ^ (3 / 5 : ℝ) ≤ Y ^ 3 := by
    have hmono := Real.rpow_le_rpow
      (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 5 : ℝ))
      (by simpa only [Y] using hY) (by norm_num : (0 : ℝ) ≤ 3)
    calc
      (n : ℝ) ^ (3 / 5 : ℝ) =
          ((n : ℝ) ^ (1 / 5 : ℝ)) ^ (3 : ℝ) := by
        convert Real.rpow_mul (Nat.cast_nonneg n) (1 / 5 : ℝ) (3 : ℝ)
          using 1
        all_goals norm_num
      _ ≤ Y ^ (3 : ℝ) := hmono
      _ = Y ^ 3 := by norm_num [Real.rpow_natCast]
  calc
    (p : ℝ) * L n / Y ^ 4 ≤ Y * L n / Y ^ 4 := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hpY hL.le) (by positivity)
    _ = L n / Y ^ 3 := by field_simp [hYpos.ne']
    _ ≤ L n / (n : ℝ) ^ (3 / 5 : ℝ) :=
      div_le_div_of_nonneg_left hL.le hnPowPos hY3
    _ ≤ 1 := hratioN

/-- Direct sharp-rate conversion used with the valuation-tail census. -/
theorem eventually_mul_two_div_yNat_pow_four_le_sharp :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p → p ≤ yNat n →
      ∀ G : ℝ, 0 ≤ G →
        G * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) ≤
          ((2 * G) / L n) * (1 / (p : ℝ)) := by
  filter_upwards [eventually_prime_mul_L_div_yNat_pow_four_le_one,
    Filter.eventually_gt_atTop 1,
    FriableAsymptotic.eventually_one_fifth_L_le_log_yNat] with
      n hrate hn hlog
  intro p hp hpY G hG
  have hL : 0 < L n := L_pos hn
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogYpos : 0 < Real.log (yNat n : ℝ) := by
    exact (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlog
  have hYpos : (0 : ℝ) < (yNat n : ℝ) :=
    zero_lt_one.trans ((Real.log_pos_iff (Nat.cast_nonneg _)).mp hlogYpos)
  have hcoef : 0 ≤ (2 * G) / ((p : ℝ) * L n) := by positivity
  calc
    G * (2 / ((yNat n ^ 4 : ℕ) : ℝ)) =
        ((2 * G) / ((p : ℝ) * L n)) *
          (((p : ℝ) * L n) / ((yNat n : ℝ) ^ 4)) := by
      norm_num only [Nat.cast_pow]
      field_simp [hpR.ne', hL.ne', hYpos.ne']
    _ ≤ ((2 * G) / ((p : ℝ) * L n)) * 1 :=
      mul_le_mul_of_nonneg_left (hrate p hpY) hcoef
    _ = ((2 * G) / L n) * (1 / (p : ℝ)) := by ring

end

end Erdos390.Full.PaperPrimePowerTailRate
