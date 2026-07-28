import Erdos390.WholePaper.BankPaperCanonicalBridgeRelevantGuardLedger

/-!
# Statement audit for the bridge-relevant guard ledger

The public inventory consists of six definitions and eighteen theorems.
The expanded examples record the exact finite enumeration, both eventual
local-agreement quantifier orders, and the raw-cell deletion consequence.
The remaining declarations are checked at their public types.
-/

namespace Erdos390.WholePaper

open Filter
open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale
open Erdos390.Full.StructuredCells

noncomputable section

#check guardFinsetWithZeroEmbedding
#check ledgerOfFinsetWithZero
#check ledgerOfFinsetWithZero_guards
#check roughCanonicalBridgeRelevantGuardSet
#check roughCanonicalBridgeRelevantGuardSet_card_le
#check roughCanonicalBridgeRelevantGuardSet_subset_anchors
#check guardedCentralAnchor_mem_bridgeRelevant_of_smooth
#check roughCanonicalBridgeRelevantLedgerFamily

namespace BankPaperRealization

#check mem_roughCanonicalBridgeRelevantGuardSet_iff_mem_guardSet
#check roughCanonicalBridgeRelevantGuardSet_insert_zero_card_le_guardSlot
#check roughCanonicalBridgeRelevantLedger
#check roughCanonicalBridgeRelevantLedgerFamily_eq
#check roughCanonicalBridgeRelevantLedger_guards
#check BankPaperCanonicalBridgeGuardAgreement
#check roughCanonicalBridgeRelevantLedger_agreement
#check roughCanonicalBridgeRelevantLedgerFamily_agreement
#check eventually_roughCanonicalBridgeRelevantLedger_agreement
#check eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
#check rawCell_value_le_two_mul
#check rawCell_sdiff_roughCanonicalBridgeRelevantLedger_eq_fullGuard
#check structuredSample_value_mem_relevantLedger_iff_fullGuard
#check structuredActiveValues_sdiff_relevantLedger_eq_fullGuard
#check structuredSample_value_not_fullGuard_of_agreement
#check structuredSample_value_not_fullGuard_of_relevantLedger

example {c : Real} (depth : Nat) (deltaStar : Real) :
    ∀ᶠ n : Nat in atTop,
      forall
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        BankPaperCanonicalBridgeGuardAgreement
          (R.roughCanonicalBridgeRelevantLedger certificate)
          R certificate deltaStar :=
  eventually_roughCanonicalBridgeRelevantLedger_agreement depth deltaStar

example {c : Real} (depth : Nat) (deltaStar : Real) :
    ∀ᶠ n : Nat in atTop,
      forall
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth)),
        BankPaperCanonicalBridgeGuardAgreement
          (roughCanonicalBridgeRelevantLedgerFamily depth n)
          R certificate deltaStar :=
  eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
    depth deltaStar

example
    {n Cprom Cbank : Nat} (guards : Finset Nat)
    (hcard :
      (insert 0 guards).card <=
        Fintype.card (GuardSlot n Cprom Cbank)) :
    (ledgerOfFinsetWithZero guards hcard).guards =
      insert 0 guards :=
  ledgerOfFinsetWithZero_guards guards hcard

example
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    BankPaperCanonicalBridgeGuardAgreement
      (R.roughCanonicalBridgeRelevantLedger certificate)
      R certificate deltaStar :=
  R.roughCanonicalBridgeRelevantLedger_agreement
    certificate deltaStar hyCutoff

example
    {Head : Type*} [Fintype Head]
    (P : Head -> HeadPattern.Pattern) (I : PhysicalIntervals)
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (cell : Cell Head) :
    rawCell P I n cell \
        (R.roughCanonicalBridgeRelevantLedger certificate).guards =
      rawCell P I n cell \
        R.roughCanonicalGuardSet certificate deltaStar :=
  rawCell_sdiff_roughCanonicalBridgeRelevantLedger_eq_fullGuard
    P I R certificate deltaStar hyCutoff hupperTwo cell

end BankPaperRealization

end

end Erdos390.WholePaper
