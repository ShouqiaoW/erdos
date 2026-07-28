import Erdos390.WholePaper.ScaledPrimeCounting

/-!
# Fixed prime-interval counts

This converts the safe fixed-dilate PNT into the exact difference form used
by each stationary layer of Section 3.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

private theorem eventually_secondOrderScale_ne_zero :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) / Real.log (n : ℝ) ≠ 0 := by
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  exact div_ne_zero hnPos.ne'
    (Real.log_pos (by exact_mod_cast hn)).ne'

theorem primeCounting_const_mul_normalized_tendsto (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun n : ℕ =>
        (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds a) := by
  have hdenNe :
      ∀ᶠ n : ℕ in atTop,
        (a * (n : ℝ)) / Real.log (n : ℝ) ≠ 0 := by
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
    exact div_ne_zero (mul_ne_zero ha.ne' hnPos.ne')
      (Real.log_pos (by exact_mod_cast hn)).ne'
  have hone := (isEquivalent_iff_tendsto_one hdenNe).mp
    (primeCounting_const_mul_nat_isEquivalent a ha)
  have hmul := hone.const_mul a
  have hmul' : Tendsto
      (fun n : ℕ =>
        a * ((Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
          ((a * (n : ℝ)) / Real.log (n : ℝ))))
      atTop (nhds a) := by
    simpa only [mul_one] using hmul
  apply hmul'.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  have hnPos : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hlog : Real.log (n : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hn)).ne'
  change
    a * ((Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
        ((a * (n : ℝ)) / Real.log (n : ℝ))) =
      (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ) /
        ((n : ℝ) / Real.log (n : ℝ))
  field_simp

theorem primeCounting_interval_normalized_tendsto
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ : ℝ) -
          (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) /
            ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (b - a)) := by
  have hsub := (primeCounting_const_mul_normalized_tendsto b hb).sub
    (primeCounting_const_mul_normalized_tendsto a ha)
  apply hsub.congr'
  filter_upwards [eventually_secondOrderScale_ne_zero] with n hn
  field_simp

/-- Natural-cardinality version for the prime interval `(a n, b n]`. -/
theorem primeCounting_interval_natSub_normalized_tendsto
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ -
            Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds (b - a)) := by
  have hb : 0 < b := ha.trans_le hab
  apply (primeCounting_interval_normalized_tendsto ha hb).congr'
  exact Eventually.of_forall fun n => by
    have harg : a * (n : ℝ) ≤ b * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hab (Nat.cast_nonneg n)
    have hfloor : ⌊a * (n : ℝ)⌋₊ ≤ ⌊b * (n : ℝ)⌋₊ :=
      Nat.floor_mono harg
    have hpi := Nat.monotone_primeCounting hfloor
    change
      ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ : ℝ) -
          (Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)) =
        ((Nat.primeCounting ⌊b * (n : ℝ)⌋₊ -
          Nat.primeCounting ⌊a * (n : ℝ)⌋₊ : ℕ) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ))
    rw [Nat.cast_sub hpi]

end Erdos390.WholePaper.SafePrimeCounting
