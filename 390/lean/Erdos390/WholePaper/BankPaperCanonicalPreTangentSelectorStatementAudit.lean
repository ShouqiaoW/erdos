import Erdos390.WholePaper.BankPaperCanonicalPreTangentSelector

/-! # Expanded statement audit for the pre-tangent selector handoff -/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! This expansion makes explicit that the handoff contains no flow,
traffic, request count, density, or final collision target. -/
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
    (selector : Nat -> Real) :
    BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed candidates bandOf cellIndex
          pointwiseUpper prefixUpper selector ↔
      ((∀ a ∈ candidates,
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
              R certificate fixed candidates selector p| <=
            pointwiseUpper p) ∧
        (forall band : Band, forall cut : Nat,
          |tangentRatioCellPrefixMass
              (bankPaperCanonicalTangentResidual
                R certificate fixed candidates selector)
              bandOf cellIndex band cut| <= prefixUpper band cut)) := by
  rfl

example
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
    (prefixUpper : Band -> Nat -> Real) :
    BankPaperCanonicalSelectorRoundingTangentHandoff
        (alpha := alpha) (beta := beta) (L := L)
        R certificate fixed E bandOf cellIndex pointwiseUpper prefixUpper ↔
      ((forall row : CanonicalCompleteRoughRow (yNat n)
          (roughRawCandidateSet n h K),
        row.1 <= n ->
          |roughCanonicalRawRowQuotaError W n h K (yNat n)
              alpha beta L row| <= 3 * E row) ->
        ∃ selector : Nat -> Real,
          BankPaperCanonicalRoundedSelectorTangentInput
            R certificate fixed (roughRawCandidateSet n h K)
            bandOf cellIndex pointwiseUpper prefixUpper selector) := by
  rfl

#check bankPaperCanonicalRoundedSelectorTangentInput_selectorState
#check bankPaperCanonicalRoundedSelectorTangentInput_residualBounds

end

end Erdos390.WholePaper
