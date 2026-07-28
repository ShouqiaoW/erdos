import Erdos390.WholePaper.Definitions

/-!
# Elementary scale facts for the upper bound

This module isolates the exact ceiling and endpoint used on the upper-bound
side of the paper.  Every asymptotic statement is proved directly from
elementary real-logarithm limits.  No prime-counting input is used.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- The paper's integral upper-tail length at fixed positive scale `c`. -/
def upperTailLength (c : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (c * secondOrderScale n)

/-- The endpoint obtained by adjoining a tail of length `h` above `2n`. -/
def upperEndpoint (n h : ℕ) : ℕ :=
  2 * n + h

/-- The elementary logarithmic comparison `log n / n → 0`, made public
for later upper-bound estimates. -/
theorem log_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    (Real.isLittleO_log_id_atTop.comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

/-- The second-order scale `n / log n` diverges to infinity. -/
theorem secondOrderScale_tendsto_atTop :
    Tendsto secondOrderScale atTop atTop := by
  have hpos :
      ∀ᶠ n : ℕ in atTop,
        0 < Real.log (n : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    exact div_pos (Real.log_pos (by exact_mod_cast hn)) (by positivity)
  have hright :
      Tendsto
        (fun n : ℕ ↦ Real.log (n : ℝ) / (n : ℝ))
        atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr
      ⟨log_natCast_div_natCast_tendsto_zero, hpos⟩
  apply hright.inv_tendsto_nhdsGT_zero.congr'
  exact Eventually.of_forall fun n ↦ by
    change (Real.log (n : ℝ) / (n : ℝ))⁻¹ =
      secondOrderScale n
    rw [secondOrderScale, inv_div]

/-- A pointwise positivity criterion for the second-order scale. -/
theorem secondOrderScale_pos {n : ℕ} (hn : 2 ≤ n) :
    0 < secondOrderScale n := by
  rw [secondOrderScale]
  exact div_pos (by positivity)
    (Real.log_pos (by exact_mod_cast hn))

/-- Eventually the second-order scale is strictly positive. -/
theorem eventually_secondOrderScale_pos :
    ∀ᶠ n : ℕ in atTop, 0 < secondOrderScale n := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  exact secondOrderScale_pos hn

/-- The second-order scale is sublinear. -/
theorem secondOrderScale_ratio_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ secondOrderScale n / (n : ℝ))
      atTop (nhds 0) := by
  have hinvLog :
      Tendsto (fun n : ℕ ↦ 1 / Real.log (n : ℝ))
        atTop (nhds 0) := by
    simpa only [one_div] using
      (Real.tendsto_log_atTop.comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).inv_tendsto_atTop
  apply hinvLog.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  rw [secondOrderScale]
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  have hlogNe : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  field_simp

/-- For `c > 0`, the integral tail length itself diverges. -/
theorem upperTailLength_tendsto_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (upperTailLength c) atTop atTop := by
  have hscaled :
      Tendsto (fun n : ℕ ↦ c * secondOrderScale n) atTop atTop :=
    secondOrderScale_tendsto_atTop.const_mul_atTop hc
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_atTop (α := ℝ)).comp hscaled

/-- For `c > 0`, the integral tail is eventually nonempty. -/
theorem eventually_upperTailLength_pos {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, 0 < upperTailLength c n :=
  (upperTailLength_tendsto_atTop hc).eventually (eventually_gt_atTop 0)

/-- Ceiling changes `c n/log n` only by a negligible relative error. -/
theorem upperTailLength_normalized_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailLength c n : ℝ) / secondOrderScale n)
      atTop (nhds c) := by
  simpa only [upperTailLength] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) hc.le).comp
      secondOrderScale_tendsto_atTop

/-- The chosen upper tail is `o(n)`. -/
theorem upperTailLength_ratio_tendsto_zero {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦ (upperTailLength c n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hmul :=
    (upperTailLength_normalized_tendsto hc).mul
      secondOrderScale_ratio_tendsto_zero
  rw [mul_zero] at hmul
  apply hmul.congr'
  filter_upwards [eventually_secondOrderScale_pos,
      eventually_gt_atTop 1] with n hscale hn
  have hscaleNe : secondOrderScale n ≠ 0 := hscale.ne'
  have hnNe : (n : ℝ) ≠ 0 := by positivity
  field_simp

/-- Hence the chosen tail length is eventually at most `n`. -/
theorem eventually_upperTailLength_le {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, upperTailLength c n ≤ n := by
  have hsmall := (upperTailLength_ratio_tendsto_zero hc).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hratio hn
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hcast : (upperTailLength c n : ℝ) ≤ (n : ℝ) := by
    have hratioLe :
        (upperTailLength c n : ℝ) / (n : ℝ) ≤ 1 := hratio.le
    have := (div_le_iff₀ hnReal).mp hratioLe
    simpa only [one_mul] using this
  exact_mod_cast hcast

/-- Every upper endpoint lies weakly above `2n`. -/
theorem two_mul_le_upperEndpoint (n h : ℕ) :
    2 * n ≤ upperEndpoint n h := by
  simp only [upperEndpoint, Nat.le_add_right]

/-- A tail of length at most `n` gives an endpoint at most `3n`. -/
theorem upperEndpoint_le_three_mul {n h : ℕ} (hh : h ≤ n) :
    upperEndpoint n h ≤ 3 * n := by
  simp only [upperEndpoint]
  omega

/-- The natural-number excess over `2n` recovers the tail length exactly. -/
theorem upperEndpoint_sub_two_mul (n h : ℕ) :
    upperEndpoint n h - 2 * n = h := by
  simp only [upperEndpoint]
  omega

/-- The paper's scaled upper endpoint is eventually in `[2n,3n]`. -/
theorem eventually_upperScaledEndpoint_bounds {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      2 * n ≤ upperEndpoint n (upperTailLength c n) ∧
        upperEndpoint n (upperTailLength c n) ≤ 3 * n := by
  filter_upwards [eventually_upperTailLength_le hc] with n hn
  exact ⟨two_mul_le_upperEndpoint n (upperTailLength c n),
    upperEndpoint_le_three_mul hn⟩

/-- The normalized excess of the scaled endpoint has the literal limit `c`. -/
theorem upperScaledEndpoint_excess_normalized_tendsto
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        ((upperEndpoint n (upperTailLength c n) : ℝ) -
            2 * (n : ℝ)) /
          secondOrderScale n)
      atTop (nhds c) := by
  apply (upperTailLength_normalized_tendsto hc).congr'
  exact Eventually.of_forall fun n ↦ by
    simp only [upperEndpoint, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    ring

private theorem log_sq_natCast_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [Function.comp_apply, id_eq] using
    ((Real.isLittleO_pow_log_id_atTop (n := 2)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).tendsto_div_nhds_zero

private theorem log_three_mul_natCast_mul_log_div_natCast_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hconstant :
      Tendsto (fun _n : ℕ ↦ Real.log 3) atTop (nhds (Real.log 3)) :=
    tendsto_const_nhds
  have hsum :
      Tendsto
        (fun n : ℕ ↦
          Real.log 3 * (Real.log (n : ℝ) / (n : ℝ)) +
            Real.log (n : ℝ) ^ 2 / (n : ℝ))
        atTop (nhds 0) := by
    simpa only [mul_zero, add_zero] using
      (hconstant.mul log_natCast_div_natCast_tendsto_zero).add
        log_sq_natCast_div_natCast_tendsto_zero
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hnReal]
  ring

private theorem logb_two_three_mul_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        Real.logb 2 (3 * (n : ℝ)) / secondOrderScale n)
      atTop (nhds 0) := by
  have hscaled :
      Tendsto
        (fun n : ℕ ↦
          (1 / Real.log 2) *
            (Real.log (3 * (n : ℝ)) * Real.log (n : ℝ) /
              (n : ℝ)))
        atTop (nhds 0) := by
    simpa only [mul_zero] using
      log_three_mul_natCast_mul_log_div_natCast_tendsto_zero.const_mul
        (1 / Real.log 2)
  apply hscaled.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnReal : (n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt hn).ne'
  have hlogN : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos one_lt_two).ne'
  rw [Real.logb, secondOrderScale]
  field_simp

/-- The binary-logarithmic tail error is negligible on the second-order
scale. -/
theorem log2_three_mul_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (Nat.log2 (3 * n) : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    logb_two_three_mul_normalized_tendsto_zero
  · filter_upwards [eventually_ge_atTop 2] with n hn
    exact div_nonneg (by positivity) (secondOrderScale_pos hn).le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hlogBound :
        (Nat.log2 (3 * n) : ℝ) ≤ Real.logb 2 (3 * (n : ℝ)) := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        Real.log2_le_logb (3 * n)
    exact div_le_div_of_nonneg_right hlogBound
      (secondOrderScale_pos hn).le

end

end Erdos390.WholePaper
