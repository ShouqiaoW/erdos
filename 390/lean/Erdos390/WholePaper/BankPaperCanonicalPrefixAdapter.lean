import Erdos390.WholePaper.BankPaperCanonicalPreTangentSelector

/-!
# Prefix adapter for the canonical rounded selector

The rounded selector already supplies exact mass balance in every declared
ratio band and a pointwise bound for every prime residual.  Those two facts
determine the required prefix estimate: a prefix is the negative strict tail
of its band, so its absolute value is bounded by the sum of the pointwise
majorants in that tail.

This file keeps that elementary conversion separate from the analytic work.
In particular, the constructor below does not ask for an independently
rounded prefix estimate.  For a user-chosen `prefixUpper`, its only extra
input is the analytic comparison from the deterministic tail sum to that
majorant.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Exact band balance and the pointwise canonical residual estimate imply
the primitive ratio-cell prefix bound.  The right side is the literal strict
tail sum of the pointwise upper bounds; no prefix-rounding hypothesis occurs
in this statement. -/
theorem bankPaperCanonicalTangentResidual_abs_prefixMass_le_tailPointwiseUpper
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
      tangentRatioCellTailPointwiseUpper
        pointwiseUpper bandOf cellIndex band cut := by
  exact abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    pointwiseUpper bandOf cellIndex hbalance hpointwise band cut

/-- Constructor for the existing pre-tangent selector interface which
derives its prefix field from band balance and the pointwise residual bound.
The sole surviving prefix-side hypothesis is the analytic domination of the
literal pointwise tail sum by the requested `prefixUpper`. -/
theorem bankPaperCanonicalRoundedSelectorTangentInput_of_tailPointwiseMajorant
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
      tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex band cut <= prefixUpper band cut) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector := by
  refine ⟨hselector, hrowIntegral, hprimeBandBalance, hdeficitSupport,
    hbalance, hpointwise, ?_⟩
  intro band cut
  exact le_trans
    (bankPaperCanonicalTangentResidual_abs_prefixMass_le_tailPointwiseUpper
      R certificate fixed candidates bandOf cellIndex pointwiseUpper selector
      hbalance hpointwise band cut)
    (htailMajorant band cut)

/-- In the primitive form no analytic simplification of the tail sum is
made at all: the existing selector input is obtained with the deterministic
tail sum itself as `prefixUpper`. -/
theorem bankPaperCanonicalRoundedSelectorTangentInput_of_balance_pointwise
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
          R certificate fixed candidates selector p| <= pointwiseUpper p) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex pointwiseUpper
        (tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex) selector := by
  exact bankPaperCanonicalRoundedSelectorTangentInput_of_tailPointwiseMajorant
    R certificate fixed candidates bandOf cellIndex pointwiseUpper
      (tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex)
      selector hselector hrowIntegral hprimeBandBalance hdeficitSupport
      hbalance hpointwise (fun _band _cut => le_rfl)

end

end Erdos390.WholePaper
