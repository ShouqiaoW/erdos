import Erdos390.WholePaper.BankPaperCanonicalSelectorRoundingCandidateHandoff

/-! # Statement audit for the candidate-parametric selector handoff -/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

#check BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
#check bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_of_selectorInput
#check bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_subset_raw
#check bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_exists_selectorInput
#check bankPaperCanonicalSelectorRoundingTangentHandoffOnRawCandidates_of_selectorInput
#check bankPaperCanonicalSelectorRoundingTangentHandoffOnRawCandidates_of_legacyHandoff
#check bankPaperCanonicalSelectorRoundingTangentHandoffOnGuardedCandidates_of_selectorInput
#check BankPaperRealization.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates

/-! The public proposition contains only raw containment and the exact
candidate-indexed selector predicate.  In particular it contains no row-error
premise purporting to construct a guarded selector. -/
example
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
    (prefixUpper : Band -> Nat -> Real) :
    BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
        (h := h) (K := K)
        R certificate fixed candidates bandOf cellIndex
          pointwiseUpper prefixUpper ↔
      (candidates ⊆ roughRawCandidateSet n h K ∧
        ∃ selector : Nat -> Real,
          BankPaperCanonicalRoundedSelectorTangentInput
            R certificate fixed candidates bandOf cellIndex
              pointwiseUpper prefixUpper selector) := by
  rfl

/-! An exact guarded selector packages directly, while the candidate set and
all residuals stay indexed by the guarded set. -/
example
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
    bankPaperCanonicalSelectorRoundingTangentHandoffOnGuardedCandidates_of_selectorInput
      R certificate fixed numericalGuards bandOf cellIndex
        pointwiseUpper prefixUpper selector S

/-! Eliminating the handoff exposes exactly the selector argument and `S`
argument of the generic distributed assembly, together with its raw-subset
premise. -/
example
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
    candidates ⊆ roughRawCandidateSet n h K ∧
      ∃ selector : Nat -> Real,
        BankPaperCanonicalRoundedSelectorTangentInput
          R certificate fixed candidates bandOf cellIndex
            pointwiseUpper prefixUpper selector := by
  exact ⟨
    bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_subset_raw H,
    bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_exists_selectorInput H⟩

end

end Erdos390.WholePaper
