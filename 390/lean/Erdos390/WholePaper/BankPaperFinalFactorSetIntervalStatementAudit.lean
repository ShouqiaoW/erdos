import Erdos390.WholePaper.BankPaperFinalFactorSetInterval

/-! # Expanded statement audit for concrete final-set interval support -/

namespace Erdos390.WholePaper

noncomputable section

example {n M : ℕ} (R : BankPaperRealization n M)
    (choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool) :
    chosenBankFactors R.exactificationState choice ⊆ factorInterval n M :=
  R.chosenExactificationBank_subset_factorInterval choice

example {n M : ℕ} (R : BankPaperRealization n M) :
    baseBankFactors R.exactificationState ⊆ factorInterval n M :=
  R.baseExactificationBank_subset_factorInterval

example {A : Type*} [Fintype A] {n M : ℕ}
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n M) :
    selectedFactorSet value X ⊆ factorInterval n M :=
  selectedFactorSet_subset_factorInterval value X hvalue

example {A : Type*} [Fintype A] {n M : ℕ}
    (R : BankPaperRealization n M)
    (fixed : Finset ℕ) (hfixed : fixed ⊆ factorInterval n M)
    (choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n M) :
    guardedFinalFactorSet fixed R.exactificationState choice value X ⊆
      factorInterval n M :=
  R.guardedFinalFactorSet_subset_factorInterval
    fixed hfixed choice value X hvalue

end

end Erdos390.WholePaper
