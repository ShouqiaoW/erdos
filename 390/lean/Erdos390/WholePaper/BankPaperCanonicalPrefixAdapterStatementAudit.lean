import Erdos390.WholePaper.BankPaperCanonicalPrefixAdapter

/-! # Expanded statement audit for the canonical prefix adapter -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! The primitive prefix conclusion expands to the strict tail of the
pointwise majorant, with no separately assumed prefix estimate. -/
example
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (selector : Nat -> Real)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <= pointwiseUpper p)
    (band : Band) (cut : Nat) :
    |tangentRatioCellPrefixMass
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex band cut| <=
      ∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band ∧ cut < cellIndex p then pointwiseUpper p else 0 := by
  simpa only [tangentRatioCellTailPointwiseUpper] using
    bankPaperCanonicalTangentResidual_abs_prefixMass_le_tailPointwiseUpper
      R certificate fixed candidates bandOf cellIndex pointwiseUpper selector
      hbalance hpointwise band cut

/-! This expansion shows that the adapter consumes only the ordinary
selector state, exact band balance, pointwise control, and the analytic tail
majorization.  In particular there is no primitive `abs prefix <= ...`
hypothesis. -/
example
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (hselector : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector)
    (hprimeBandBalance :
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector)
    (hdeficitSupport :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0)
    (hpointwise : forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <= pointwiseUpper p)
    (htailMajorant : forall band : Band, forall cut : Nat,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band ∧ cut < cellIndex p then pointwiseUpper p else 0) <=
          prefixUpper band cut) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector := by
  apply bankPaperCanonicalRoundedSelectorTangentInput_of_tailPointwiseMajorant
    R certificate fixed candidates bandOf cellIndex pointwiseUpper
      prefixUpper selector hselector hrowIntegral hprimeBandBalance
      hdeficitSupport hbalance hpointwise
  intro band cut
  simpa only [tangentRatioCellTailPointwiseUpper] using
    htailMajorant band cut

#check bankPaperCanonicalRoundedSelectorTangentInput_of_balance_pointwise

end

end Erdos390.WholePaper
