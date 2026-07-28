import Erdos390.WholePaper.ThirteenLayerLowerBound

/-!
# Expanded statement audit for the thirteen-layer lower bound

The examples expose the fixed-prime tail estimate, its exact nine-prime
coefficient, the literal real endpoint inequality, and the unconditional
liminf terminal.  In particular, the public normalized expression subtracts
real casts and never uses `Nat.sub`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {n h ℓ : ℕ} (hℓ : ℓ.Prime) :
    (2 * n + h).factorial.factorization ℓ -
        (2 * n).factorial.factorization ℓ ≤
      h / (ℓ - 1) + Nat.log2 (2 * n + h) := by
  exact factorialValuationSub_le_div_pred_add_log2 hℓ

example {n h : ℕ} (hh : h ≤ n) :
    ((∑ ℓ ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ),
        ((2 * n + h).factorial.factorization ℓ -
          2 * n.factorial.factorization ℓ) : ℕ) : ℝ) ≤
      (h : ℝ) * ((17927 : ℝ) / 7920) +
        ((∑ ℓ ∈ ({2, 3, 5, 7, 11, 13, 17, 19, 23} : Finset ℕ),
          (Nat.choose (2 * n) n).factorization ℓ : ℕ) : ℝ) +
            9 * (Nat.log2 (3 * n) : ℝ) := by
  have h := smallPrimeFactorialValuationSum_cast_le hh
  rw [S23_eq] at h
  simpa only [smallPrimes, centralSmallPrimeValuationSum, Rat.cast_div,
    Rat.cast_natCast] using h

example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      2 * (n : ℝ) +
          (((4029639598 : ℝ) / 25970038185) - ε) *
            ((n : ℝ) / Real.log (n : ℝ)) ≤
        (f n : ℝ) := by
  simpa only [C0, secondOrderScale] using
    eventually_f_ge_two_mul_add_C0_sub_eps_mul_secondOrderScale hε

example {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((4029639598 : ℝ) / 25970038185) - ε ≤
        (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
          (n : ℝ) := by
  simpa only [C0] using
    eventually_C0_sub_eps_le_normalized_f_sub_two_mul hε

example :
    (((4029639598 : ℝ) / 25970038185 : ℝ) : EReal) ≤
      liminf
        (fun n : ℕ ↦
          ((((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
            (n : ℝ) : EReal))
        atTop := by
  simpa only [C0] using C0_le_liminf_normalized_f_sub_two_mul

end

end Erdos390.WholePaper
