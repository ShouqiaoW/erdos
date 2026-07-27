import Erdos536.FiniteProbability

/-!
# Union bounds for explicitly weighted finite spaces
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Mass of a Boolean event on an explicitly weighted finite space. -/
def finiteBoolEventMass
    {Ω : Type*} [DecidableEq Ω]
    (P : Finset Ω) (w : Ω → ℝ) (E : Ω → Bool) : ℝ :=
  ∑ ω ∈ P, if E ω then w ω else 0

/-- Union of a finite family of Boolean events. -/
def finiteBoolEventUnion
    {ι Ω : Type*} [DecidableEq ι]
    (I : Finset ι) (E : ι → Ω → Bool) (ω : Ω) : Bool :=
  decide (∃ i ∈ I, E i ω)

@[simp]
theorem finiteBoolEventUnion_iff
    {ι Ω : Type*} [DecidableEq ι]
    {I : Finset ι} {E : ι → Ω → Bool} {ω : Ω} :
    finiteBoolEventUnion I E ω ↔ ∃ i ∈ I, E i ω := by
  simp [finiteBoolEventUnion]

/-- Elementary finite union bound. -/
theorem finiteBoolEventUnion_mass_le_sum
    {ι Ω : Type*} [DecidableEq ι] [DecidableEq Ω]
    (I : Finset ι) (P : Finset Ω) (w : Ω → ℝ)
    (E : ι → Ω → Bool)
    (hw : ∀ ω ∈ P, 0 ≤ w ω) :
    finiteBoolEventMass P w (finiteBoolEventUnion I E) ≤
      ∑ i ∈ I, finiteBoolEventMass P w (E i) := by
  rw [finiteBoolEventMass]
  simp_rw [finiteBoolEventMass]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro ω hω
  by_cases hUnion : finiteBoolEventUnion I E ω
  · rw [if_pos hUnion]
    obtain ⟨i, hiI, hi⟩ := finiteBoolEventUnion_iff.mp hUnion
    calc
      w ω = (if E i ω then w ω else 0) := by simp [hi]
      _ ≤ ∑ j ∈ I, if E j ω then w ω else 0 := by
        exact Finset.single_le_sum
          (s := I) (f := fun j => if E j ω then w ω else 0)
          (by
            intro j hj
            by_cases hjE : E j ω
            · simpa [hjE] using hw ω hω
            · simp [hjE])
          hiI
      _ = ∑ i ∈ I, if E i ω then w ω else 0 := rfl
  · rw [if_neg hUnion]
    apply Finset.sum_nonneg
    intro i hi
    split_ifs
    · exact hw ω hω
    · exact le_rfl

end Erdos536
