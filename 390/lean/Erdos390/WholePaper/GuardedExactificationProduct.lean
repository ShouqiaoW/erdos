import Erdos390.WholePaper.GuardedExactificationAlgebra

/-!
# Guarded unions and their ordinary products

Every hypothesis below names literal finite factor sets.  In particular,
the guard conclusions do not pass through a separate compatibility
contract.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The literal union used after rounding and bank-state replacement. -/
def guardedFinalFactorSet {A G : Type*} [Fintype A] [Fintype G]
    (fixed : Finset ℕ) (state : G → Bool → Finset ℕ)
    (choice : G → Bool) (value : A → ℕ) (X : A → ℝ) : Finset ℕ :=
  (fixed ∪ chosenBankFactors state choice) ∪ selectedFactorSet value X

theorem selectedFactorSet_subset_candidateUniverse
    {A : Type*} [Fintype A] (value : A → ℕ) (X : A → ℝ) :
    selectedFactorSet value X ⊆ Finset.univ.image value := by
  intro a ha
  obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩

theorem disjoint_chosenBankFactors_of_disjoint_states_left
    {G : Type*} [Fintype G] (fixed : Finset ℕ)
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (hguard : ∀ g b, Disjoint fixed (state g b)) :
    Disjoint fixed (chosenBankFactors state choice) := by
  classical
  unfold chosenBankFactors
  rw [Finset.disjoint_biUnion_right]
  intro g _hg
  exact hguard g (choice g)

theorem disjoint_chosenBankFactors_selectedFactorSet
    {A G : Type*} [Fintype A] [Fintype G]
    (state : G → Bool → Finset ℕ) (choice : G → Bool)
    (value : A → ℕ) (X : A → ℝ)
    (hguard : ∀ g b,
      Disjoint (Finset.univ.image value) (state g b)) :
    Disjoint (chosenBankFactors state choice) (selectedFactorSet value X) := by
  classical
  apply Disjoint.symm
  apply (disjoint_chosenBankFactors_of_disjoint_states_left
    (Finset.univ.image value) state choice hguard).mono
    (selectedFactorSet_subset_candidateUniverse value X)
    (Finset.Subset.rfl)

theorem guardedFinalFactorSet_prod_eq
    {A G : Type*} [Fintype A] [Fintype G]
    (fixed : Finset ℕ) (state : G → Bool → Finset ℕ)
    (choice : G → Bool) (value : A → ℕ) (X : A → ℝ)
    (hfixedBank : Disjoint fixed (chosenBankFactors state choice))
    (hfixedSelected : Disjoint fixed (selectedFactorSet value X))
    (hbankSelected :
      Disjoint (chosenBankFactors state choice) (selectedFactorSet value X)) :
    (guardedFinalFactorSet fixed state choice value X).prod id =
      (fixed.prod id * (chosenBankFactors state choice).prod id) *
        (selectedFactorSet value X).prod id := by
  unfold guardedFinalFactorSet
  rw [Finset.prod_union
      (Finset.disjoint_union_left.mpr ⟨hfixedSelected, hbankSelected⟩),
    Finset.prod_union hfixedBank]

theorem guardedFinalFactorSet_factorization
    {A G : Type*} [Fintype A] [Fintype G]
    (fixed : Finset ℕ) (state : G → Bool → Finset ℕ)
    (choice : G → Bool) (value : A → ℕ) (X : A → ℝ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hbankPositive : ∀ g b a, a ∈ state g b → 0 < a)
    (hvaluePositive : ∀ a, 0 < value a)
    (hfixedBank : Disjoint fixed (chosenBankFactors state choice))
    (hfixedSelected : Disjoint fixed (selectedFactorSet value X))
    (hbankSelected :
      Disjoint (chosenBankFactors state choice) (selectedFactorSet value X))
    (q : ℕ) :
    ((guardedFinalFactorSet fixed state choice value X).prod id).factorization q =
      (fixed.prod id).factorization q +
        ((chosenBankFactors state choice).prod id).factorization q +
          ((selectedFactorSet value X).prod id).factorization q := by
  have hfixedNe : fixed.prod id ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun a ha ↦ (hfixedPositive a ha).ne'
  have hbankNe : (chosenBankFactors state choice).prod id ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    obtain ⟨g, _hg, haState⟩ := Finset.mem_biUnion.mp ha
    exact (hbankPositive g (choice g) a haState).ne'
  have hselectedNe : (selectedFactorSet value X).prod id ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp ha
    exact (hvaluePositive i).ne'
  rw [guardedFinalFactorSet_prod_eq fixed state choice value X
      hfixedBank hfixedSelected hbankSelected,
    Nat.factorization_mul (mul_ne_zero hfixedNe hbankNe) hselectedNe,
    Nat.factorization_mul hfixedNe hbankNe]
  rfl

end

end Erdos390.WholePaper
