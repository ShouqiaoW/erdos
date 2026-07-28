import Erdos390.WholePaper.BankPaperExactificationState

/-!
# Interval support of the concrete final factor set

The actual exactification bank and the selected candidate factors lie in the
paper interval `(n,M]`.  A caller-provided fixed factor set may then be joined
to them once it has the same literal interval property.  Central anchors are
external residual bookkeeping here: this file does not identify them with
the `fixed` input of guarded exactification.
-/

namespace Erdos390.WholePaper

noncomputable section

namespace BankPaperRealization

/-- Every factor in an arbitrarily toggled concrete bank is an actual factor
in `(n,M]`. -/
theorem chosenExactificationBank_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M)
    (choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool) :
    chosenBankFactors R.exactificationState choice ⊆ factorInterval n M := by
  classical
  intro factor hfactor
  rw [chosenBankFactors, Finset.mem_biUnion] at hfactor
  obtain ⟨slot, _hslot, hstate⟩ := hfactor
  exact R.exactificationState_subset_factorInterval
    slot (choice slot) hstate

/-- The precharged state-zero bank is the constant-false instance of the
arbitrary-choice interval theorem. -/
theorem baseExactificationBank_subset_factorInterval
    {n M : ℕ} (R : BankPaperRealization n M) :
    baseBankFactors R.exactificationState ⊆ factorInterval n M := by
  simpa only [baseBankFactors] using
    R.chosenExactificationBank_subset_factorInterval
      (fun _slot ↦ false)

end BankPaperRealization

/-- Selecting a subset of an interval-valued candidate family cannot leave
the interval. -/
theorem selectedFactorSet_subset_factorInterval
    {A : Type*} [Fintype A] {n M : ℕ}
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n M) :
    selectedFactorSet value X ⊆ factorInterval n M := by
  intro factor hfactor
  obtain ⟨a, _ha, rfl⟩ := Finset.mem_image.mp hfactor
  exact hvalue a

namespace BankPaperRealization

/-- Concrete final-set interval terminal.  The fixed factors remain a
separate caller-supplied set; no anchor family is silently inserted here. -/
theorem guardedFinalFactorSet_subset_factorInterval
    {A : Type*} [Fintype A] {n M : ℕ}
    (R : BankPaperRealization n M)
    (fixed : Finset ℕ) (hfixed : fixed ⊆ factorInterval n M)
    (choice : SignedBankSlot (bankRoundingBetaOnSupport n) → Bool)
    (value : A → ℕ) (X : A → ℝ)
    (hvalue : ∀ a, value a ∈ factorInterval n M) :
    guardedFinalFactorSet fixed R.exactificationState choice value X ⊆
      factorInterval n M := by
  intro factor hfactor
  rw [guardedFinalFactorSet, Finset.mem_union] at hfactor
  rcases hfactor with hfixedOrBank | hselected
  · rw [Finset.mem_union] at hfixedOrBank
    rcases hfixedOrBank with hfixedFactor | hbankFactor
    · exact hfixed hfixedFactor
    · exact R.chosenExactificationBank_subset_factorInterval
        choice hbankFactor
  · exact selectedFactorSet_subset_factorInterval value X hvalue hselected

end BankPaperRealization

end

end Erdos390.WholePaper
