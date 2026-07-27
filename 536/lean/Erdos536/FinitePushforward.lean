import Mathlib

/-!
# Finite pushforward and total-variation contraction
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Push forward explicit finite masses along a function. -/
def finitePushforwardMass
    {Ω V : Type*} [DecidableEq Ω] [DecidableEq V]
    (A : Finset Ω) (w : Ω → ℝ) (f : Ω → V) (v : V) : ℝ :=
  ∑ x ∈ A, if f x = v then w x else 0

private theorem finitePushforward_sub
    {Ω V : Type*} [DecidableEq Ω] [DecidableEq V]
    (A : Finset Ω) (w u : Ω → ℝ) (f : Ω → V) (v : V) :
    finitePushforwardMass A w f v -
        finitePushforwardMass A u f v =
      ∑ x ∈ A, if f x = v then w x - u x else 0 := by
  rw [finitePushforwardMass, finitePushforwardMass,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases h : f x = v <;> simp [h]

/-- Taking a finite pushforward cannot increase `L¹` distance. -/
theorem finitePushforward_l1_le
    {Ω V : Type*} [DecidableEq Ω] [DecidableEq V]
    (A : Finset Ω) (B : Finset V)
    (w u : Ω → ℝ) (f : Ω → V)
    (hf : ∀ x ∈ A, f x ∈ B) :
    (∑ v ∈ B,
        |finitePushforwardMass A w f v -
          finitePushforwardMass A u f v|) ≤
      ∑ x ∈ A, |w x - u x| := by
  calc
    (∑ v ∈ B,
        |finitePushforwardMass A w f v -
          finitePushforwardMass A u f v|) =
        ∑ v ∈ B,
          |∑ x ∈ A, if f x = v then w x - u x else 0| := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [finitePushforward_sub]
    _ ≤ ∑ v ∈ B, ∑ x ∈ A,
          |if f x = v then w x - u x else 0| := by
      apply Finset.sum_le_sum
      intro v _hv
      exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ A, |w x - u x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_eq_single (f x)]
      · simp
      · intro v _hv hv
        simp [hv.symm]
      · exact fun hnot => (hnot (hf x hx)).elim

end Erdos536
