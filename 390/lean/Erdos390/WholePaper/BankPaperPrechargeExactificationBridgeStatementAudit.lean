import Erdos390.WholePaper.BankPaperPrechargeExactificationBridge

/-! # Expanded statement audit for the precharge/exactification bridge -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

local instance bankPaperBridgeAuditMarkerRequestDecidableEq (n : ℕ) :
    DecidableEq (BankPaperMarkerRequest n) :=
  Classical.decEq _

example {n : ℕ}
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    bankPaperIndexedPathComponentRequest ⟨slot, component⟩ =
      bankPaperPathComponentRequest slot component :=
  rfl

example {n : ℕ} :
    Function.Surjective
      (bankPaperIndexedPathComponentRequest (n := n)) :=
  bankPaperIndexedPathComponentRequest_surjective

example {n M : ℕ} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateZeroValue slot component =
      R.prechargeBaseStateValue
        (bankPaperPathComponentRequest slot component) :=
  R.pathStateZeroValue_eq_prechargeBaseStateValue slot component

example {n M : ℕ} (R : BankPaperRealization n M) :
    baseBankFactors R.exactificationState = R.prechargeBaseState :=
  R.baseExactificationBank_eq_prechargeBaseState

example {n M : ℕ} (R : BankPaperRealization n M) :
    chosenBankFactors R.exactificationState (fun _ ↦ false) =
      indexedPathState R.prechargeBaseStateValue := by
  simpa only [baseBankFactors, BankPaperRealization.prechargeBaseState] using
    R.baseExactificationBank_eq_prechargeBaseState

example {n M : ℕ} (R : BankPaperRealization n M) :
    (baseBankFactors R.exactificationState).prod id =
      R.prechargeBaseStateProduct :=
  R.baseExactificationBank_prod_eq_prechargeBaseStateProduct

example {n M : ℕ} (R : BankPaperRealization n M) :
    (baseBankFactors R.exactificationState).prod id =
      ∏ request : BankPaperMarkerRequest n,
        R.prechargeBaseStateValue request :=
  R.baseExactificationBank_prod_eq_prechargeComponentProduct

example {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ) :
    fixed.prod id * (baseBankFactors R.exactificationState).prod id =
      fixed.prod id * R.prechargeBaseStateProduct :=
  R.fixed_mul_baseExactificationBank_prod_eq_precharge fixed

end

end Erdos390.WholePaper
