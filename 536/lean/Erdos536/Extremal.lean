import Erdos536.Definitions

/-!
# Elementary facts about the extremal function
-/

open Finset Nat

namespace Erdos536

@[simp]
theorem lcmTriangleFree_empty : LcmTriangleFree ∅ := by
  simp [LcmTriangleFree]

theorem mem_safeFamilies_iff {N : ℕ} {A : Finset ℕ} :
    A ∈ safeFamilies N ↔ A ⊆ Finset.Icc 1 N ∧ LcmTriangleFree A := by
  simp [safeFamilies]

theorem safeFamilies_nonempty (N : ℕ) : (safeFamilies N).Nonempty := by
  exact ⟨∅, mem_safeFamilies_iff.mpr ⟨empty_subset _, lcmTriangleFree_empty⟩⟩

theorem card_le_f {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.Icc 1 N)
    (hfree : LcmTriangleFree A) : A.card ≤ f N := by
  rw [f]
  exact Finset.le_sup (mem_safeFamilies_iff.mpr ⟨hA, hfree⟩)

theorem exists_extremal (N : ℕ) :
    ∃ A : Finset ℕ, A ⊆ Finset.Icc 1 N ∧ LcmTriangleFree A ∧ A.card = f N := by
  obtain ⟨A, hA, hsup⟩ :=
    Finset.exists_mem_eq_sup (safeFamilies N) (safeFamilies_nonempty N) card
  rw [mem_safeFamilies_iff] at hA
  exact ⟨A, hA.1, hA.2, hsup.symm⟩

theorem f_le_interval_card (N : ℕ) : f N ≤ (Finset.Icc 1 N).card := by
  rw [f]
  apply Finset.sup_le
  intro A hA
  exact card_le_card (mem_safeFamilies_iff.mp hA).1

theorem f_le (N : ℕ) : f N ≤ N := by
  calc
    f N ≤ (Finset.Icc 1 N).card := f_le_interval_card N
    _ ≤ N := by
      rw [Nat.card_Icc]
      omega

end Erdos536
