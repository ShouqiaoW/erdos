import Erdos536.PrimeSums
import Erdos536.Squarefree

/-!
# Square-reciprocal tails of finite prime supports
-/

open scoped BigOperators
open Finset

namespace Erdos536

open PrimeSums

/-- A finite prime support lying above `A` has square-reciprocal mass at
most `1 / A`, uniformly in its upper endpoint. -/
theorem sum_primeSupport_inv_sq_le
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {A : ℕ} (hA : 1 ≤ A)
    (habove : ∀ p ∈ R, A < p) :
    (∑ p ∈ R, (p : ℝ)⁻¹ ^ 2) ≤ 1 / (A : ℝ) := by
  let Y := R.sup id
  have hsub : R ⊆ primesUpTo Y \ primesUpTo A := by
    intro p hp
    apply Finset.mem_sdiff.mpr
    constructor
    · have hpY : p ≤ Y :=
        Finset.le_sup (s := R) (f := id) hp
      simp [primesUpTo, hpY, hR p hp]
    · intro hpA
      have hpAleData : p ≤ A ∧ p.Prime := by
        simpa [primesUpTo] using hpA
      have hpAle : p ≤ A := hpAleData.1
      have hpAbove : A < p := habove p hp
      omega
  calc
    (∑ p ∈ R, (p : ℝ)⁻¹ ^ 2) ≤
        ∑ p ∈ primesUpTo Y \ primesUpTo A,
          (p : ℝ)⁻¹ ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsub
      intro p _hp _hpR
      positivity
    _ = reciprocalSquareSumBetween A Y := by
      simp [reciprocalSquareSumBetween, one_div]
    _ ≤ 1 / (A : ℝ) :=
      reciprocalSquareSumBetween_le A Y hA

end Erdos536
