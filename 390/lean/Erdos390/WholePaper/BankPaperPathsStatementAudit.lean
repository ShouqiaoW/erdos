import Erdos390.WholePaper.BankPaperPaths

/-! # Expanded statement audit for actual full bank paths -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {n : ℕ}
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    Function.Injective (bankPaperPathComponentRequest slot) :=
  bankPaperPathComponentRequest_injective slot

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateZeroValue slot component ∈
        R.pathComponentOccurrences slot component ∧
      R.pathStateOneValue slot component ∈
        R.pathComponentOccurrences slot component :=
  ⟨R.pathStateZeroValue_mem_componentOccurrences slot component,
    R.pathStateOneValue_mem_componentOccurrences slot component⟩

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    {component component' : BankPaperPathComponent slot}
    (hcomponent : component ≠ component') :
    Disjoint (R.pathComponentOccurrences slot component)
      (R.pathComponentOccurrences slot component') :=
  R.pathComponentOccurrences_disjoint slot hcomponent

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    Function.Injective (R.pathStateZeroValue slot) ∧
      Function.Injective (R.pathStateOneValue slot) :=
  ⟨R.pathStateZeroValue_injective slot,
    R.pathStateOneValue_injective slot⟩

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    (R.pathStateZero slot).card = Fintype.card (BankPaperPathComponent slot) ∧
      (R.pathStateOne slot).card = Fintype.card (BankPaperPathComponent slot) :=
  ⟨R.pathStateZero_card slot, R.pathStateOne_card slot⟩

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.pathStateZero slot ⊆ R.pathComponentCensus slot ∧
      R.pathStateOne slot ⊆ R.pathComponentCensus slot :=
  ⟨R.pathStateZero_subset_componentCensus slot,
    R.pathStateOne_subset_componentCensus slot⟩

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    {occurrence : ℕ}
    (hoccurrence : occurrence ∈ R.pathComponentCensus slot) :
    occurrence ∈ factorInterval n M :=
  R.pathComponentCensus_mem_factorInterval slot hoccurrence

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    completeRoughSignature (yNat n) (R.pathStateZeroValue slot component) =
      completeRoughSignature (yNat n) (R.pathStateOneValue slot component) :=
  R.pathComponent_completeRoughSignature_eq slot component

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (signature : ℕ →₀ ℕ) :
    completeSignatureMultiplicity (yNat n) (R.pathStateZero slot) signature =
      completeSignatureMultiplicity (yNat n) (R.pathStateOne slot) signature :=
  R.path_completeSignatureMultiplicity_eq slot signature

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.realizedFullPathChange slot =
      R.ordinary.realizedSlotChange slot +
        R.bottom.realizedSlotChange slot :=
  R.realizedFullPathChange_eq_ordinary_add_bottom slot

/-! This literal match locks the orientation signs, instead of auditing only
the name of the signed-change abbreviation. -/
example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    R.realizedFullPathChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit slot.1.1
      | .inr _copy => coordinateUnit slot.1.1 := by
  simpa only [BankPaperRealization.signedFullPathChange] using
    R.realizedFullPathChange_eq_signedUnit slot

/-! Above five, the ordinary part contributes `e₅-eₚ` downward and its
negative upward, while the bottom part contributes the complementary signed
unit at five. -/
example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hp5 : 5 ≤ slot.1.1) :
    R.ordinary.realizedSlotChange slot =
        (match slot.2 with
        | .inl _copy => coordinateUnit 5 - coordinateUnit slot.1.1
        | .inr _copy => coordinateUnit slot.1.1 - coordinateUnit 5) ∧
      R.bottom.realizedSlotChange slot =
        (match slot.2 with
        | .inl _copy => -coordinateUnit 5
        | .inr _copy => coordinateUnit 5) :=
  ⟨by
    simpa only [BankOrdinaryPaperRealization.signedPrimeToFiveChange] using
      R.ordinary.realizedSlotChange_eq_signedPrimeToFiveChange slot hp5,
    R.bottom.realizedSlotChange_eq_signedUnit_five_of_five_le slot hp5⟩

/-! The two exceptional truncated paths have the same downward/upward sign
convention as the general path. -/
example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : slot.1.1 = 3) :
    R.bottom.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 3
      | .inr _copy => coordinateUnit 3 :=
  R.bottom.realizedSlotChange_eq_signedUnit_three slot hprime

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (hprime : slot.1.1 = 2) :
    R.bottom.realizedSlotChange slot =
      match slot.2 with
      | .inl _copy => -coordinateUnit 2
      | .inr _copy => coordinateUnit 2 :=
  R.bottom.realizedSlotChange_eq_signedUnit_two slot hprime

end

end Erdos390.WholePaper
