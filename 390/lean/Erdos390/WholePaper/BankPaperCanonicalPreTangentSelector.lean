import Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge
import Erdos390.WholePaper.TangentDistributedFlowCensus

/-!
# Honest selector-rounding interface for the finite-band tangent

The canonical Saias theorem controls complete-rough row quota errors, while
the tangent consumes prime-valuation residuals of an actual rounded
selector.  Those are different index sets, so a row error cannot simply be
renamed as traffic.

This file records the minimal missing selector-rounding output as a
predicate on an explicit selector.  It contains no flow, request count,
density, or collision target.  The residual estimates are exactly the two
inputs used upstream of the paper earthmover:

* the pointwise prime estimate;
* signed prefix estimates on literal ratio-cell cuts.

Unlike a conclusion-bearing structure, the selector and every requested
property remain visible in the existential handoff proposition.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Actual rounded selector state and the residual estimates needed before
constructing any tangent flow.

`bandOf` is the fixed exponent-band assignment and `cellIndex` is the
consecutive multiplicative-ratio cell index inside that band.  Thus the last
line is an explicit prefix sum, rather than a target traffic estimate. -/
def BankPaperCanonicalRoundedSelectorTangentInput
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
    (selector : Nat -> Real) : Prop :=
  (∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1) ∧
    BankPaperCanonicalSelectorRowIntegral n candidates selector ∧
    BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates selector ∧
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
      R certificate fixed candidates selector ∧
    (forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0) ∧
    (forall p : BankPaperCanonicalTangentPrime n W,
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <= pointwiseUpper p) ∧
    (forall band : Band, forall cut : Nat,
      |tangentRatioCellPrefixMass
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex band cut| <= prefixUpper band cut)

/-- The honest missing implication from complete-rough row quota estimates
to an actual selector with prime-coordinate control.

The conclusion is not a traffic premise: it existentially exposes the
selector and only pointwise/prefix residual estimates. -/
def BankPaperCanonicalSelectorRoundingTangentHandoff
    {c : Real} {depth n W h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat} {alpha beta L : Real}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed : Finset Nat)
    (E : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n h K) -> Real)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real) : Prop :=
  (forall row : CanonicalCompleteRoughRow (yNat n)
      (roughRawCandidateSet n h K),
    row.1 <= n ->
      |roughCanonicalRawRowQuotaError W n h K (yNat n)
          alpha beta L row| <= 3 * E row) ->
    ∃ selector : Nat -> Real,
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed (roughRawCandidateSet n h K)
        bandOf cellIndex pointwiseUpper prefixUpper selector

/-! ## Direct projections used by downstream assembly -/

theorem bankPaperCanonicalRoundedSelectorTangentInput_selectorState
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      left right changed}
    {fixed candidates : Finset Nat}
    {Band : Type*} [DecidableEq Band]
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real}
    {prefixUpper : Band -> Nat -> Real}
    {selector : Nat -> Real}
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    (∀ a ∈ candidates,
        0 <= selector a ∧ selector a <= 1) ∧
      BankPaperCanonicalSelectorRowIntegral n candidates selector ∧
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed candidates selector ∧
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed candidates selector := by
  exact ⟨S.1, S.2.1, S.2.2.1, S.2.2.2.1⟩

theorem bankPaperCanonicalRoundedSelectorTangentInput_residualBounds
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      left right changed}
    {fixed candidates : Finset Nat}
    {Band : Type*} [DecidableEq Band]
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real}
    {prefixUpper : Band -> Nat -> Real}
    {selector : Nat -> Real}
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    (forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime n W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p
        else 0) = 0) ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| <=
          pointwiseUpper p) ∧
      (forall band : Band, forall cut : Nat,
        |tangentRatioCellPrefixMass
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex band cut| <= prefixUpper band cut) := by
  exact ⟨S.2.2.2.2.1, S.2.2.2.2.2.1, S.2.2.2.2.2.2⟩

end

end Erdos390.WholePaper
