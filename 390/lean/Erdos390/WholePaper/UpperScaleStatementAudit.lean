import Erdos390.WholePaper.UpperScale

/-!
# Literal statement audit for the upper-bound scale

The examples expose the literal real scale, natural ceiling, generic endpoint,
and every asymptotic interface without hiding a target limit in a structure.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

example (c : ℝ) (n : ℕ) :
    upperTailLength c n =
      Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))) := rfl

example (n h : ℕ) :
    upperEndpoint n h = 2 * n + h := rfl

example :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ))
      atTop atTop := by
  simpa only [secondOrderScale] using secondOrderScale_tendsto_atTop

example :
    ∀ᶠ n : ℕ in atTop,
      0 < (n : ℝ) / Real.log (n : ℝ) := by
  simpa only [secondOrderScale] using eventually_secondOrderScale_pos

example :
    Tendsto
      (fun n : ℕ ↦
        ((n : ℝ) / Real.log (n : ℝ)) / (n : ℝ))
      atTop (nhds 0) := by
  simpa only [secondOrderScale] using
    secondOrderScale_ratio_tendsto_zero

example {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds c) := by
  simpa only [upperTailLength, secondOrderScale] using
    upperTailLength_normalized_tendsto hc

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ))) ≤ n := by
  simpa only [upperTailLength, secondOrderScale] using
    eventually_upperTailLength_le hc

example {n h : ℕ} (hh : h ≤ n) :
    2 * n ≤ 2 * n + h ∧
      2 * n + h ≤ 3 * n ∧
      (2 * n + h) - 2 * n = h := by
  exact ⟨two_mul_le_upperEndpoint n h,
    upperEndpoint_le_three_mul hh,
    upperEndpoint_sub_two_mul n h⟩

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      2 * n ≤
          2 * n + Nat.ceil
            (c * ((n : ℝ) / Real.log (n : ℝ))) ∧
        2 * n + Nat.ceil
            (c * ((n : ℝ) / Real.log (n : ℝ))) ≤
          3 * n := by
  simpa only [upperEndpoint, upperTailLength, secondOrderScale] using
    eventually_upperScaledEndpoint_bounds hc

example {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (((2 * n + Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ))) : ℕ) : ℝ) -
            2 * (n : ℝ)) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds c) := by
  simpa only [upperEndpoint, upperTailLength, secondOrderScale] using
    upperScaledEndpoint_excess_normalized_tendsto hc

example :
    Tendsto
      (fun n : ℕ ↦
        (Nat.log2 (3 * n) : ℝ) /
          ((n : ℝ) / Real.log (n : ℝ)))
      atTop (nhds 0) := by
  simpa only [secondOrderScale] using
    log2_three_mul_normalized_tendsto_zero

end

end Erdos390.WholePaper
