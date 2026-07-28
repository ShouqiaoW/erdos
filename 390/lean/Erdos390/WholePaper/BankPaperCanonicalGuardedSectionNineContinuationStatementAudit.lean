import Erdos390.WholePaper.BankPaperCanonicalGuardedSectionNineContinuation

/-! # Statement audit for the guarded Section 9 continuation

This restates both public definitions and all six public theorem statements
from `BankPaperCanonicalGuardedSectionNineContinuation`.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Complete public declaration census -/

#check Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet_eq_distributedGuardedCandidates
#check Erdos390.WholePaper.BankPaperRealization.roughCanonicalGuardedCandidateSet_cleanEndpoints
#check Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalGuardedSmoothFlexibleQuota
#check Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedSmoothFlexibleQuota_eq_intCast
#check Erdos390.WholePaper.BankPaperRealization.BankPaperCanonicalGuardedSectionNineContinuation
#check Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedSectionNineContinuation_capacityInputs
#check Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedSectionNineContinuation_exists_assemblyFrontEnd
#check Erdos390.WholePaper.BankPaperRealization.bankPaperCanonicalGuardedSectionNineContinuation_selectorHandoff

/-! ## Imported dependencies used by the expanded checks -/

#check RoughCanonicalExceptionalLabel
#check RoughCanonicalActiveNonexceptionalLabel
#check roughCanonical_activeNonexceptional_or_exceptional
#check exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates

example
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) :
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K =
      bankPaperCanonicalDistributedGuardedCandidates n
        (upperTailLength c n) K
        (R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar)) :=
  R.roughCanonicalGuardedCandidateSet_eq_distributedGuardedCandidates
    certificate deltaStar

example
    {c : Real} {depth n W K Phead X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real}
    (hKh : K * upperTailLength c n <= n)
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) {common : Nat}
    (hcommon : common ∈
      tangentSplitCleanMultiplierLists
        (tangentPositiveFlowEdges flow)
        (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
        (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
        L sigma
        (fun edge : BankPaperCanonicalTangentPrime n W ×
            BankPaperCanonicalTangentPrime n W =>
          flow edge.1 edge.2)
        n K (upperTailLength c n) Phead X0 (yNat n)
        R.tangentPaperDedicatedRows
        (R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar)) request) :
    bankPaperCanonicalDistributedTangentRequestSource request * common ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
      bankPaperCanonicalDistributedTangentRequestTarget request * common ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K :=
  R.roughCanonicalGuardedCandidateSet_cleanEndpoints certificate deltaStar
    hKh request hcommon

/-! Full public shape.  In particular, the postcharge `q_R` equation and
all three capacity inputs are restricted to active nonexceptional rows;
exceptional nonsmooth rows have zero selector mass, while the smooth row
has an independent existential integer quota. -/
example
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    {Band : Type*} [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (tailLower tailUpper : Band -> Nat -> Nat)
    (scale : Real) (guardBudget poolMinimum : Nat) :
    BankPaperCanonicalGuardedSectionNineContinuation
        (K := K) R certificate deltaStar lastCell bandOf cellIndex
          tailLower tailUpper scale guardBudget poolMinimum ↔
      ((∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalGuardLocalCensusBound R certificate deltaStar K
            label guardBudget) ∧
      (∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar W K
            label poolMinimum) ∧
      (∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
          RoughCanonicalPostchargeRowCapacity R certificate deltaStar K
            label) ∧
      0 <= scale ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        cellIndex p <= lastCell (bandOf p)) ∧
      (forall band cell, cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) ∧
      (forall band cut,
        Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformCutoff <=
          tailLower band cut) ∧
      (forall band cut, tailLower band cut <= tailUpper band cut) ∧
      (forall band cut (p : BankPaperCanonicalTangentPrime n W),
        bandOf p = band -> cut < cellIndex p ->
          tailLower band cut < bankPaperCanonicalTangentPrimeLabel p ∧
            bankPaperCanonicalTangentPrimeLabel p <= tailUpper band cut) ∧
      ∃ smoothFlexibleQuota : Int,
      ∃ selector : Nat -> Real,
        (∀ a ∈
            R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          0 <= selector a ∧ selector a <= 1) ∧
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            selector a) = (smoothFlexibleQuota : Real) ∧
        (∀ label ∈ completeRoughLabelSet (yNat n)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
          RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
            (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
                selector a) =
              R.roughCanonicalPostchargeRowTarget deltaStar label) ∧
        (∀ label ∈ completeRoughLabelSet (yNat n)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
          label ≠ 1 -> RoughCanonicalExceptionalLabel n deltaStar label ->
            (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
                selector a) = 0) ∧
        BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
          R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            selector ∧
        BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
          R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            selector ∧
        (forall band : Band,
          (∑ p : BankPaperCanonicalTangentPrime n W,
            if bandOf p = band then
              bankPaperCanonicalTangentResidual R certificate
                (R.paperFixedExceptionalFactors deltaStar)
                (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
                selector p
            else 0) = 0) ∧
        (forall p : BankPaperCanonicalTangentPrime n W,
          |bankPaperCanonicalTangentResidual R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              selector p| <=
            bankPaperCanonicalHarmonicPointwiseUpper scale p)) := by
  rfl

/-! The two guarded-candidate definitions agree at the actual paper guard
set, so the endpoint adapter is available with no membership premise beyond
clean-list membership. -/
example
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) :
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K =
      roughRawCandidateSet n (upperTailLength c n) K \
        R.tangentPaperNumericalGuardSet certificate
          (R.paperFixedExceptionalFactors deltaStar) := by
  rfl

/-! The public continuation is an explicit proposition.  It is not an
existence theorem for the guarded selector or for any capacity estimate. -/
#check RoughCanonicalGuardLocalCensusBound
#check RoughCanonicalGuardedBroadPoolCapacity
#check RoughCanonicalPostchargeRowCapacity

/-! The smooth label is `1` and has its own integer flexible quota.  This
statement is intentionally not the postcharge expression used for
nontrivial rough labels. -/
example
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (selector : Nat -> Real)
    (smoothFlexibleQuota : Int) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota R certificate deltaStar K
        selector smoothFlexibleQuota ↔
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          selector a) = (smoothFlexibleQuota : Real) := by
  rfl

example
    {c : Real} {depth n K : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar : Real} {selector : Nat -> Real}
    {smoothFlexibleQuota : Int}
    (H : BankPaperCanonicalGuardedSmoothFlexibleQuota R certificate
      deltaStar K selector smoothFlexibleQuota) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        selector a) = (smoothFlexibleQuota : Real) :=
  bankPaperCanonicalGuardedSmoothFlexibleQuota_eq_intCast H

example
    {c : Real} {depth n W K : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar : Real}
    {Band : Type*} [DecidableEq Band]
    {lastCell : Band -> Nat}
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {tailLower tailUpper : Band -> Nat -> Nat}
    {scale : Real} {guardBudget poolMinimum : Nat}
    (H : BankPaperCanonicalGuardedSectionNineContinuation
      (K := K)
      R certificate deltaStar lastCell bandOf cellIndex tailLower tailUpper
        scale guardBudget poolMinimum) :
    (∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalGuardLocalCensusBound R certificate deltaStar K label
          guardBudget) ∧
    (∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalGuardedBroadPoolCapacity R certificate deltaStar W K
          label poolMinimum) ∧
    (∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
        RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) :=
  bankPaperCanonicalGuardedSectionNineContinuation_capacityInputs H

/-! Its output retains the smooth integer quota and supplies the rounded
selector, raw containment, and the two occupied-cell geometry fields needed
by the candidate assembly. -/
example
    {c : Real} {depth n W K : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar : Real}
    {Band : Type*} [DecidableEq Band]
    {lastCell : Band -> Nat}
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {tailLower tailUpper : Band -> Nat -> Nat}
    {scale : Real} {guardBudget poolMinimum : Nat}
    (H : BankPaperCanonicalGuardedSectionNineContinuation
      (K := K)
      R certificate deltaStar lastCell bandOf cellIndex tailLower tailUpper
        scale guardBudget poolMinimum) :
    ∃ smoothFlexibleQuota : Int,
    ∃ selector : Nat -> Real,
      BankPaperCanonicalGuardedSmoothFlexibleQuota R certificate deltaStar K
          selector smoothFlexibleQuota ∧
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K ⊆
          roughRawCandidateSet n (upperTailLength c n) K ∧
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        bandOf cellIndex
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        (fun band cut => bankPaperCanonicalHarmonicTailMajorant scale
          (tailLower band cut) (tailUpper band cut)) selector ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        cellIndex p <= lastCell (bandOf p)) ∧
      (forall band cell, cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :=
  bankPaperCanonicalGuardedSectionNineContinuation_exists_assemblyFrontEnd
    (K := K) H

example
    {c : Real} {depth n W K : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar : Real}
    {Band : Type*} [DecidableEq Band]
    {lastCell : Band -> Nat}
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {tailLower tailUpper : Band -> Nat -> Nat}
    {scale : Real} {guardBudget poolMinimum : Nat}
    (H : BankPaperCanonicalGuardedSectionNineContinuation
      (K := K)
      R certificate deltaStar lastCell bandOf cellIndex tailLower tailUpper
        scale guardBudget poolMinimum) :
    BankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates
      (h := upperTailLength c n) (K := K)
      R certificate (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      bandOf cellIndex
      (bankPaperCanonicalHarmonicPointwiseUpper scale)
      (fun band cut => bankPaperCanonicalHarmonicTailMajorant scale
        (tailLower band cut) (tailUpper band cut)) :=
  bankPaperCanonicalGuardedSectionNineContinuation_selectorHandoff H

end BankPaperRealization

end

end Erdos390.WholePaper
