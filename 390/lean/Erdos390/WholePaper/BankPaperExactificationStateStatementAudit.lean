import Erdos390.WholePaper.BankPaperExactificationState

/-! # Expanded statement audit for the actual two-state paper bank -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) :
    integerValuationVector ((R.exactificationState slot true).prod id) -
        integerValuationVector ((R.exactificationState slot false).prod id) =
      embeddedSignedBankSlotChange
        (fun p : ↑(bankRoundingPrimeSupport n) ↦ p.1) slot :=
  R.exactificationState_productChange slot

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (signature : ℕ →₀ ℕ) :
    completeSignatureMultiplicity (yNat n)
        (R.exactificationState slot false) signature =
      completeSignatureMultiplicity (yNat n)
        (R.exactificationState slot true) signature :=
  R.exactificationState_completeSignatureMultiplicity_eq slot signature

example {n M : ℕ} (R : BankPaperRealization n M)
    {slot slot' : SignedBankSlot (bankRoundingBetaOnSupport n)}
    (hslot : slot ≠ slot') (selected selected' : Bool) :
    Disjoint (R.exactificationState slot selected)
      (R.exactificationState slot' selected') :=
  R.exactificationState_disjoint_of_slot_ne hslot selected selected'

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) (selected : Bool) :
    R.exactificationState slot selected ⊆ factorInterval n M :=
  R.exactificationState_subset_factorInterval slot selected

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n)) (selected : Bool)
    {a : ℕ} (ha : a ∈ R.exactificationState slot selected) :
    0 < a :=
  R.exactificationState_positive slot selected ha

end

end Erdos390.WholePaper
