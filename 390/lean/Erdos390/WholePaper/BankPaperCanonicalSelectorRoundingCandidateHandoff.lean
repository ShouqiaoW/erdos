import Erdos390.WholePaper.BankPaperCanonicalDistributedCandidateSet

/-!
# Candidate-parametric selector-rounding handoff

`BankPaperCanonicalSelectorRoundingTangentHandoff` is the original raw-set
socket: a complete-rough row estimate is assumed to produce a selector on
`roughRawCandidateSet n h K`.  The distributed Section 9 assembly also has a
generic socket on a guarded subset of those candidates.

This file connects the two APIs without claiming that a raw selector can be
restricted to a guarded subset.  Such a restriction would change the row
sums and the prime-valuation residual.  Instead the candidate-parametric
handoff records exactly the two inputs used by the generic assembly:

* containment of the supplied candidates in the raw universe; and
* an actual selector satisfying the full candidate-indexed rounded-selector
  predicate.

The old raw handoff remains unchanged.  The adapters below merely package an
already supplied selector, or apply the old handoff to its explicit row-bound
hypothesis when the candidate set is literally the raw set.  In particular,
no analytic selector-existence statement for a proper guarded subset is
introduced here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Exact selector-rounding data on an arbitrary candidate subset of the
literal raw universe.

This is deliberately a proposition with an exposed existential selector,
matching the original handoff style.  Its second conjunct is precisely the
selector input consumed by
`exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates`.
-/
def BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
    {c : Real} {depth n W h K : Nat} {left right : Nat -> Nat}
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
    (prefixUpper : Band -> Nat -> Real) : Prop :=
  candidates ⊆ roughRawCandidateSet n h K ∧
    ∃ selector : Nat -> Real,
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed candidates bandOf cellIndex
          pointwiseUpper prefixUpper selector

/-! ## Exact constructors and projections -/

/-- Package a candidate selector already known to satisfy every exact
rounded-selector property.  Raw containment is a separate explicit premise;
no existence or restriction argument is performed. -/
theorem bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_of_selectorInput
    {c : Real} {depth n W h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    (hcandidatesRaw : candidates ⊆ roughRawCandidateSet n h K)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
      (h := h) (K := K)
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper := by
  exact ⟨hcandidatesRaw, selector, S⟩

/-- The candidate containment retained by the handoff. -/
theorem bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_subset_raw
    {c : Real} {depth n W h K : Nat} {left right : Nat -> Nat}
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
    (H : BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
      (h := h) (K := K)
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper) :
    candidates ⊆ roughRawCandidateSet n h K := by
  exact H.1

/-- Extract the actual selector and its exact candidate-indexed properties.
Together with `..._subset_raw`, this gives precisely the two selector inputs
of the generic distributed assembly. -/
theorem bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_exists_selectorInput
    {c : Real} {depth n W h K : Nat} {left right : Nat -> Nat}
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
    (H : BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
      (h := h) (K := K)
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper) :
    ∃ selector : Nat -> Real,
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed candidates bandOf cellIndex
          pointwiseUpper prefixUpper selector := by
  exact H.2

/-! ## Backward-compatible raw and guarded adapters -/

/-- On the literal raw set, an exact selector input automatically gives the
candidate-parametric handoff.  This is the non-analytic raw wrapper. -/
theorem bankPaperCanonicalSelectorRoundingTangentHandoffOnRawCandidates_of_selectorInput
    {c : Real} {depth n W h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed (roughRawCandidateSet n h K)
        bandOf cellIndex pointwiseUpper prefixUpper selector) :
    BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
      (h := h) (K := K)
      R certificate fixed (roughRawCandidateSet n h K)
        bandOf cellIndex pointwiseUpper prefixUpper := by
  constructor
  · intro a ha
    exact ha
  · exact ⟨selector, S⟩

/-- Apply the legacy raw handoff to its explicit row estimate, then expose its
result through the candidate-parametric API on the same raw set.

This theorem does not produce a selector on a proper subset. -/
theorem bankPaperCanonicalSelectorRoundingTangentHandoffOnRawCandidates_of_legacyHandoff
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
    (prefixUpper : Band -> Nat -> Real)
    (H : BankPaperCanonicalSelectorRoundingTangentHandoff
      (alpha := alpha) (beta := beta) (L := L)
      R certificate fixed E bandOf cellIndex pointwiseUpper prefixUpper)
    (hrow : forall row : CanonicalCompleteRoughRow (yNat n)
        (roughRawCandidateSet n h K),
      row.1 <= n ->
        |roughCanonicalRawRowQuotaError W n h K (yNat n)
            alpha beta L row| <= 3 * E row) :
    BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
      (h := h) (K := K)
      R certificate fixed (roughRawCandidateSet n h K)
        bandOf cellIndex pointwiseUpper prefixUpper := by
  constructor
  · intro a ha
    exact ha
  · exact H hrow

/-- The concrete guarded set-difference API needs no new selector-existence
principle: once an exact selector on that set is supplied, its raw containment
is the already-proved `sdiff` inclusion. -/
theorem bankPaperCanonicalSelectorRoundingTangentHandoffOnGuardedCandidates_of_selectorInput
    {c : Real} {depth n W h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed numericalGuards : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
        (bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards)
        bandOf cellIndex pointwiseUpper prefixUpper selector) :
    BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
      (h := h) (K := K)
      R certificate fixed
        (bankPaperCanonicalDistributedGuardedCandidates
          n h K numericalGuards)
        bandOf cellIndex pointwiseUpper prefixUpper := by
  exact
    bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_of_selectorInput
      (h := h) (K := K)
      R certificate fixed
      (bankPaperCanonicalDistributedGuardedCandidates
        n h K numericalGuards)
      (bankPaperCanonicalDistributedGuardedCandidates_subset_raw
        n h K numericalGuards)
      bandOf cellIndex pointwiseUpper prefixUpper selector S

end

end Erdos390.WholePaper
