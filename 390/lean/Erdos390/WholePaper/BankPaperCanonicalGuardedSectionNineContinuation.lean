import Erdos390.WholePaper.BankPaperCanonicalSelectorRoundingCandidateHandoff
import Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger
import Erdos390.WholePaper.BankPaperCanonicalPrefixQuadrature

/-!
# Guarded canonical Section 9 continuation

The guarded candidate set, the candidate-parametric tangent assembly, and
the harmonic prefix adapter now fit together definitionally.  What is not
yet available is a theorem constructing the required selector on the
guarded rows from the local capacity estimates.  This module records that
remaining front end without turning it into an axiom or silently replacing
the guarded set by the raw set.

`BankPaperCanonicalGuardedSectionNineContinuation` is an explicit `Prop`.
It keeps three kinds of input visible:

* the local guard census, guarded broad-pool capacity, and guarded-row
  capacity for the active nonexceptional rough rows from the finite ledger;
* an actual feasible guarded selector with the exact postcharge targets on
  active nonexceptional rows, zero mass on exceptional rows, a separate
  integer flexible quota on the smooth row, and the prime-coordinate
  properties used before the tangent; and
* the occupied-cell and harmonic-tail geometry used by the distributed
  earthmover and the prefix quadrature.

The extraction theorem uses the paper's three row cases: the postcharge
integer target on active nonexceptional labels, the proved zero target on
exceptional labels, and an independent integer `q_sm^flex(d)` when the
label is `1`.  It then obtains the full rounded-selector tangent input
through the proved harmonic quadrature.  Separate finite adapters provide
raw-set containment and clean-list endpoint closure.  Thus the remaining
traffic, collision-census, slack, and selector-charge hypotheses of the
existing candidate assembly can be supplied directly, with no extra
selector or geometry conversion layer.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## The literal guarded set as a distributed candidate set -/

/-- The guard-local ledger and the candidate-parametric tangent use the
same literal set difference when the numerical guards are the actual paper
guards. -/
theorem roughCanonicalGuardedCandidateSet_eq_distributedGuardedCandidates
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
          (R.paperFixedExceptionalFactors deltaStar)) := by
  rfl

/-- Every clean common multiplier has both endpoints in the literal
guard-local candidate set.  This is the exact endpoint-closure premise of
the candidate-parametric distributed assembly. -/
theorem roughCanonicalGuardedCandidateSet_cleanEndpoints
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
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
  simpa only [
      R.roughCanonicalGuardedCandidateSet_eq_distributedGuardedCandidates
        (K := K) certificate deltaStar] using
    (bankPaperCanonicalDistributed_cleanEndpoints_mem_guardedCandidates
      (n := n) (W := W) (K := K) (h := upperTailLength c n)
      (Phead := Phead) (X0 := X0)
      (dedicatedRows := R.tangentPaperDedicatedRows)
      (numericalGuards := R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar))
      hKh request hcommon)

/-! ## Explicit remaining continuation input -/

/-- The paper's flexible smooth-row quota `q_sm^flex(d)`.  It is an
integer total for the flexible numerical coordinates in complete rough
label `1`; it is not the nontrivial-row expression `q_R` and it need not
identify any of the real protected/active summands separately. -/
def BankPaperCanonicalGuardedSmoothFlexibleQuota
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat) (selector : Nat -> Real)
    (smoothFlexibleQuota : Int) : Prop :=
  (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
      selector a) = (smoothFlexibleQuota : Real)

/-- Unfold the named smooth-row ledger without changing its integer
quota. -/
theorem bankPaperCanonicalGuardedSmoothFlexibleQuota_eq_intCast
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
  H

/-- The exact front-end obligations still separating the guard-local row
ledger from the distributed Section 9 assembly.

For an active nonexceptional label, the selector row equation is
deliberately stronger and more informative than merely postulating integer
row sums: the target is the literal postcharge target already proved
nonnegative and integral by the finite ledger.  An exceptional nonsmooth
row instead has selector mass zero, matching the proved identity `q_R = 0`.
Neither formula is applied to the smooth row.  That row carries the separate
integer `smoothFlexibleQuota` above, matching the structured smooth bridge.
Likewise the three guard-local capacity clauses are restricted to active
nonexceptional rows, exactly where the paper invokes their estimates.

The capacity clauses do not manufacture this selector; they remain visible
alongside it until guarded nonsmooth correction and smooth-row construction
theorems prove the missing implications. -/
def BankPaperCanonicalGuardedSectionNineContinuation
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
    (scale : Real) (guardBudget poolMinimum : Nat) : Prop :=
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
      RoughCanonicalPostchargeRowCapacity R certificate deltaStar K label) ∧
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
        bankPaperCanonicalHarmonicPointwiseUpper scale p)

/-! ## Projections into the existing APIs -/

/-- The three active-nonexceptional-row capacity statements remain
separately visible; none is deduced from the existence of the selector,
and none is demanded on smooth or exceptional labels. -/
theorem bankPaperCanonicalGuardedSectionNineContinuation_capacityInputs
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
  ⟨H.1, H.2.1, H.2.2.1⟩

/-- The continuation preserves the separate smooth integer quota and
produces exactly the selector input, raw containment, and occupied-cell
geometry consumed at the front of the existing candidate-parametric
distributed assembly.  Prefix control is derived from the harmonic-tail
geometry rather than assumed independently. -/
theorem bankPaperCanonicalGuardedSectionNineContinuation_exists_assemblyFrontEnd
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
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) := by
  rcases H with ⟨_hguardCensus, _hpoolCapacity, _hrowCapacity,
    hscale, hindex, hoccupied, hlowerCutoff, hendpoints, hgeometry,
    smoothFlexibleQuota, selector, hselector, hsmoothTarget,
    hactiveRoughRowTarget, hexceptionalRoughRowZero, hprimeBandBalance,
    hdeficitSupport, hbalance, hpointwise⟩
  have hrowIntegral : BankPaperCanonicalSelectorRowIntegral n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      selector := by
    intro label hlabel
    by_cases hlabelSmooth : label = 1
    · subst label
      refine ⟨smoothFlexibleQuota, ?_⟩
      simpa only [roughCanonicalGuardedRow] using hsmoothTarget
    · rcases roughCanonical_activeNonexceptional_or_exceptional
          (n := n) (deltaStar := deltaStar) hlabelSmooth with
        hactive | hexceptional
      · refine ⟨R.roughCanonicalPostchargeRowTargetInt deltaStar label, ?_⟩
        calc
          (∑ a ∈ completeRoughRowFiber (yNat n)
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              label, selector a) =
              R.roughCanonicalPostchargeRowTarget deltaStar label := by
            simpa only [roughCanonicalGuardedRow] using
              hactiveRoughRowTarget label hlabel hactive
          _ = (R.roughCanonicalPostchargeRowTargetInt deltaStar label : Real) :=
            R.roughCanonicalPostchargeRowTarget_eq_intCast deltaStar label
      · refine ⟨R.roughCanonicalPostchargeRowTargetInt deltaStar label, ?_⟩
        calc
          (∑ a ∈ completeRoughRowFiber (yNat n)
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              label, selector a) = 0 := by
            simpa only [roughCanonicalGuardedRow] using
              hexceptionalRoughRowZero label hlabel hlabelSmooth hexceptional
          _ = R.roughCanonicalPostchargeRowTarget deltaStar label :=
            (R.roughCanonicalPostchargeRowTarget_eq_zero_of_exceptional
              deltaStar label hexceptional).symm
          _ = (R.roughCanonicalPostchargeRowTargetInt deltaStar label : Real) :=
            R.roughCanonicalPostchargeRowTarget_eq_intCast deltaStar label
  have S :=
    bankPaperCanonicalRoundedSelectorTangentInput_of_harmonicTailGeometry
      R certificate (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      bandOf cellIndex tailLower tailUpper scale selector hscale hselector
      hrowIntegral hprimeBandBalance hdeficitSupport hbalance hpointwise
      hlowerCutoff hendpoints hgeometry
  have hsmoothQuota : BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K selector smoothFlexibleQuota :=
    hsmoothTarget
  exact ⟨smoothFlexibleQuota, selector, hsmoothQuota,
    R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
      certificate deltaStar K,
    S, hindex, hoccupied⟩

/-- Package the derived selector front end in the candidate-parametric
rounding handoff used immediately before the distributed assembly. -/
theorem bankPaperCanonicalGuardedSectionNineContinuation_selectorHandoff
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
        (tailLower band cut) (tailUpper band cut)) := by
  obtain ⟨_smoothFlexibleQuota, selector, _hsmoothTarget, hcandidatesRaw,
      S, _hindex, _hoccupied⟩ :=
    bankPaperCanonicalGuardedSectionNineContinuation_exists_assemblyFrontEnd
      (K := K) H
  exact
    bankPaperCanonicalSelectorRoundingTangentHandoffOnCandidates_of_selectorInput
      (h := upperTailLength c n) (K := K)
      R certificate (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      hcandidatesRaw bandOf cellIndex
      (bankPaperCanonicalHarmonicPointwiseUpper scale)
      (fun band cut => bankPaperCanonicalHarmonicTailMajorant scale
        (tailLower band cut) (tailUpper band cut)) selector S

end BankPaperRealization

end

end Erdos390.WholePaper
