import Mathlib

/-!
# Finite product laws on subsets

The prime-band arguments are finite.  We expose their product probabilities
as explicit finite sums, so subsequent insertion and moment calculations do
not depend on measure-theoretic conditional-probability infrastructure.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- The mass of `S` under independent Bernoulli parameters `r`, relative to
the finite ground set `P`.  Later uses always have `S ⊆ P`. -/
def subsetWeight {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (S : Finset α) : ℝ :=
  (∏ p ∈ S, r p) * ∏ p ∈ P \ S, (1 - r p)

theorem sum_subsetWeight {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) :
    ∑ S ∈ P.powerset, subsetWeight P r S = 1 := by
  simp only [subsetWeight]
  rw [← Finset.prod_add]
  simp

theorem subsetWeight_nonneg {α : Type*} [DecidableEq α]
    {P S : Finset α} {r : α → ℝ}
    (hr0 : ∀ p ∈ P, 0 ≤ r p) (hr1 : ∀ p ∈ P, r p ≤ 1)
    (hS : S ⊆ P) :
    0 ≤ subsetWeight P r S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg fun p hp => hr0 p (hS hp)
  · exact Finset.prod_nonneg fun p hp =>
      sub_nonneg.mpr (hr1 p (mem_sdiff.mp hp).1)

theorem subsetWeight_insert_mul_complement {α : Type*} [DecidableEq α]
    {P A : Finset α} {r : α → ℝ} {p : α}
    (hpP : p ∈ P) (hpA : p ∉ A) :
    subsetWeight P r (insert p A) * (1 - r p) =
      subsetWeight P r A * r p := by
  have hpDiff : p ∈ P \ A := mem_sdiff.mpr ⟨hpP, hpA⟩
  rw [subsetWeight, subsetWeight, prod_insert hpA, Finset.sdiff_insert]
  rw [← Finset.mul_prod_erase (P \ A) (fun q => 1 - r q) hpDiff]
  ring

theorem subsetWeight_insert_odds {α : Type*} [DecidableEq α]
    {P A : Finset α} {r : α → ℝ} {p : α}
    (hpP : p ∈ P) (hpA : p ∉ A)
    (hr : r p ≠ 1) :
    subsetWeight P r (insert p A) =
      subsetWeight P r A * (r p / (1 - r p)) := by
  have hcomp : 1 - r p ≠ 0 := sub_ne_zero.mpr (Ne.symm hr)
  apply (mul_right_cancel₀ hcomp)
  rw [subsetWeight_insert_mul_complement hpP hpA]
  field_simp

end Erdos536
