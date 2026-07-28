import Erdos390.WholePaper.BankPaperCanonicalDistributedCleanListAdapter

/-!
# Expanded statement audit for the distributed clean-list adapter

The adapter's two public theorems are checked below in source declaration
order.  The exact prime-label cancellation theorem imported from prefix
quadrature is then restated only as a supporting arithmetic example; it is
not part of this module's declaration census.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

#check BankPaperRealization.eventually_canonicalDistributedSectionNineCleanListLower_absorbed
#check bankPaperCanonicalRoundedSelector_weightedResidual_le_harmonicScale

example {n W : Nat} (scale : Real)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        bankPaperCanonicalHarmonicPointwiseUpper scale p = scale :=
  bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper scale p

example
    {c : Real} {depth n W : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W → Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
    (prefixUpper : Band → Nat → Real)
    (scale : Real) (selector : Nat → Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        prefixUpper selector) :
    ∀ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| ≤ scale := by
  intro p
  exact bankPaperCanonicalRoundedSelector_weightedResidual_le_harmonicScale
    R certificate fixed candidates bandOf cellIndex prefixUpper scale
      selector S p

namespace BankPaperRealization

/-! Expanded public shape: fixed-tail/head placement and literal ratio-cell
geometry are the only premises added when the already absorbed unordered
pair theorem is reindexed over distributed split requests. -/
example
    (W K : Nat) {c r0 deltaStar : Real}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : Nat in atTop,
      ∀ (depth : Nat) (left right : Nat → Nat)
        (changed : Finset Nat),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional : Finset Nat),
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band],
      ∀ (lastCell : Band → Nat)
        (residual : BankPaperCanonicalTangentPrime n W → Real)
        (bandOf : BankPaperCanonicalTangentPrime n W → Band)
        (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
        (L sigma : Real),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        bandOf cellIndex r0 →
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        0 < bankPaperCanonicalDistributedTangentLowerCard
          (density := tangentPaperCleanListDensity W r0) request) ∧
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        bankPaperCanonicalDistributedTangentLowerCard
            (density := tangentPaperCleanListDensity W r0) request ≤
          (tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges
              (tangentRatioCellEarthmoverFlow lastCell residual
                bandOf cellIndex))
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              tangentRatioCellEarthmoverFlow lastCell residual
                bandOf cellIndex edge.1 edge.2)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card) ∧
      ∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        ∀ side,
          tangentPaperCleanListDensity W r0 * n ≤
            (bankPaperCanonicalDistributedTangentLowerCard
              (density := tangentPaperCleanListDensity W r0)
              request : Real) *
              tangentEndpointLabel
                bankPaperCanonicalDistributedTangentRequestSource
                bankPaperCanonicalDistributedTangentRequestTarget
                side request :=
  eventually_canonicalDistributedSectionNineCleanListLower_absorbed
    W K hc hr0one hr0three hdelta hdeltaUpper hmainSmall

end BankPaperRealization

end

end Erdos390.WholePaper
