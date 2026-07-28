import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourceSelectorDeficitPaperRateClosureConnector
import Erdos390.WholePaper.BankPaperCanonicalImplementationDefectRateReductionConnector
import Erdos390.WholePaper.BankPaperCanonicalMediumPrimeStructuredPlacementMomentRateConnector

/-!
# Literal implementation-rate reductions for the rounded frozen-top source

The balanced selector-deficit identity for the rounded frozen-top source
contains three implementation terms.  This file connects each of them to
the strongest already justified finite reduction, without identifying the
frozen-top source with the older no-top source.

* The source-to-guarded defect is partitioned into complete rough rows.
  Every nonsmooth row cancels for the literal frozen-top selector, leaving
  exactly one guarded smooth-row defect.
* The guarded/raw defect is source-independent, so its existing rowwise
  pool-moment and numerator-shift majorant applies literally.
* A second two-zero-cell rebalance has the existing uniform-cell valuation
  moment whenever the retained outside part of the frozen-top source agrees
  with its old tagged seed on occupied active coordinates.  That compatibility
  is stated explicitly; it is not inferred by confusing the top source with
  the legacy source.

The only quantitative inputs left by the final constructor are therefore
the smooth-row mismatch, the guarded/raw rowwise majorant, the two uniform
cell valuation means, and the absolute two-cell mass budget.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Source-parametric nonsmooth cancellation -/

/-- The row contribution to the source-to-guarded defect for an arbitrary
source, with the literal raw weight and guarded postcharge correction. -/
def roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (sourceSelector : Nat -> Real) (p label : Nat) : Real :=
  R.roughCanonicalSourceGuardedRowValuationDefectAtLabel certificate
    deltaStar K sourceSelector
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta ell)
    (fun rowLabel =>
      R.roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
        certificate deltaStar W K rowLabel alpha beta ell p)
    p label

/-- The arbitrary source-to-guarded defect is exactly the sum of the
postcharge row defects over attained raw labels. -/
theorem
    roughCanonicalSourceToGuardedCorrectionValuationDefect_eq_sum_postchargeRowDefects
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (sourceSelector : Nat -> Real) :
    roughCanonicalSourceToGuardedCorrectionValuationDefect
        (W := W) (K := K)
        R certificate deltaStar alpha beta ell sourceSelector p =
      ∑ label ∈ completeRoughLabelSet (yNat n)
          (roughRawCandidateSet n (upperTailLength c n) K),
        R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
          certificate deltaStar W K alpha beta ell
            sourceSelector p label := by
  simpa only [
    roughCanonicalSourceToGuardedCorrectionValuationDefect,
    roughCanonicalAggregateGuardedPostchargeRowCorrection,
    roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel,
    roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel] using
    (R.roughCanonicalSourceValuationCorrectionMoment_sub_guardedCorrection_eq_sum_rowDefects
      certificate deltaStar alpha beta ell sourceSelector
      (fun rowLabel =>
        R.roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
          certificate deltaStar W K rowLabel alpha beta ell p))

/-- An active nonexceptional nonsmooth row contributes zero whenever the
source is pointwise the guarded postcharge corrected weight on that row. -/
theorem
    roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel_eq_zero_of_active
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hsource : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label,
      sourceSelector a =
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta ell a) :
    R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
        certificate deltaStar W K alpha beta ell sourceSelector
          p label = 0 := by
  classical
  have hnotExceptional :
      ¬ RoughCanonicalExceptionalLabel n deltaStar label :=
    not_lt_of_ge hactive.2
  have hsourceMoment :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        sourceSelector a * (a.factorization p : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar W K label alpha beta ell a *
            (a.factorization p : Real) := by
    apply Finset.sum_congr rfl
    intro a ha
    rw [hsource a ha]
  unfold roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
  unfold roughCanonicalSourceGuardedRowValuationDefectAtLabel
  rw [
    R.completeRoughRowFiber_nonexceptionalGuarded_eq_guardedRow
      certificate deltaStar hnotExceptional,
    if_pos hactive,
    hsourceMoment,
    R.sum_guardedPostchargeRowCorrectedWeight_mul_factorization_eq
      certificate deltaStar alpha beta ell]
  unfold
    roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
  ring

/-- An exceptional nonsmooth row contributes zero whenever the source is
pointwise zero there.  The nonexceptional baseline row is then empty and no
active correction is installed. -/
theorem
    roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel_eq_zero_of_exceptional
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (_hlabel : label ≠ 1)
    (hexceptional : RoughCanonicalExceptionalLabel n deltaStar label)
    (hsource : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label,
      sourceSelector a = 0) :
    R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
        certificate deltaStar W K alpha beta ell sourceSelector
          p label = 0 := by
  classical
  have hnotActive :
      ¬ RoughCanonicalActiveNonexceptionalLabel n deltaStar label := by
    intro hactive
    exact (not_lt_of_ge hactive.2) hexceptional
  have hsourceMoment :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        sourceSelector a * (a.factorization p : Real)) = 0 := by
    apply Finset.sum_eq_zero
    intro a ha
    rw [hsource a ha, zero_mul]
  unfold roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
  unfold roughCanonicalSourceGuardedRowValuationDefectAtLabel
  rw [
    R.completeRoughRowFiber_nonexceptionalGuarded_eq_empty
      certificate deltaStar hexceptional,
    Finset.sum_empty, if_neg hnotActive, hsourceMoment]
  ring

/-- The one possible surviving row in an arbitrary source-to-guarded
defect.  The membership test handles an empty raw smooth row. -/
def roughCanonicalSmoothSourceToGuardedValuationDefect
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (sourceSelector : Nat -> Real) (p : Nat) : Real :=
  if 1 ∈ completeRoughLabelSet (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) K) then
    R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
      certificate deltaStar W K alpha beta ell sourceSelector p 1
  else
    0

/-- If a source is the corrected weight on every active nonsmooth row and
zero on every exceptional nonsmooth row, its full source-to-guarded defect
is exactly its smooth-row defect. -/
theorem
    roughCanonicalSourceToGuardedCorrectionValuationDefect_eq_smooth_of_nonsmooth
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (sourceSelector : Nat -> Real)
    (hactiveSource : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        sourceSelector a =
          R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
            deltaStar W K label alpha beta ell a)
    (hexceptionalSource : ∀ label,
      label ≠ 1 ->
      RoughCanonicalExceptionalLabel n deltaStar label ->
      ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        sourceSelector a = 0) :
    roughCanonicalSourceToGuardedCorrectionValuationDefect
        (W := W) (K := K)
        R certificate deltaStar alpha beta ell sourceSelector p =
      R.roughCanonicalSmoothSourceToGuardedValuationDefect
        certificate deltaStar W K alpha beta ell sourceSelector p := by
  classical
  rw [
    R.roughCanonicalSourceToGuardedCorrectionValuationDefect_eq_sum_postchargeRowDefects
      certificate deltaStar alpha beta ell sourceSelector]
  unfold roughCanonicalSmoothSourceToGuardedValuationDefect
  let labels :=
    completeRoughLabelSet (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) K)
  have hnonsmooth :
      ∀ label ∈ labels, label ≠ 1 ->
        R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel
          certificate deltaStar W K alpha beta ell sourceSelector
            p label = 0 := by
    intro label _hlabel hlabel
    rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := n) (deltaStar := deltaStar) hlabel with
      hactive | hexceptional
    · exact
        R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel_eq_zero_of_active
          certificate deltaStar alpha beta ell sourceSelector hactive
            (hactiveSource label hactive)
    · exact
        R.roughCanonicalPostchargeSourceGuardedRowValuationDefectAtLabel_eq_zero_of_exceptional
          certificate deltaStar alpha beta ell sourceSelector
            hlabel hexceptional
              (hexceptionalSource label hlabel hexceptional)
  by_cases hsmooth : 1 ∈ labels
  · rw [if_pos (by simpa only [labels] using hsmooth)]
    exact Finset.sum_eq_single 1
      (fun label hlabel hlabelNe =>
        hnonsmooth label hlabel hlabelNe)
      (fun hsmoothNotMem => (hsmoothNotMem hsmooth).elim)
  · rw [if_neg (by simpa only [labels] using hsmooth)]
    apply Finset.sum_eq_zero
    intro label hlabel
    exact hnonsmooth label hlabel (fun hlabelOne => by
      subst label
      exact hsmooth hlabel)

/-! ## Literal rounded frozen-top source reduction -/

/-- The surviving smooth-row mismatch for the literal rounded frozen-top
source at balanced depth `K0 + 1`. -/
def roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat) : Real :=
  R.roughCanonicalSmoothSourceToGuardedValuationDefect certificate
    deltaStar B.sampleData.W (K0 + 1)
    (bankPaperCanonicalPostHfitBalancedAlpha
      B c K0 betaProt betaAct)
    (betaProt + betaAct) B.L
    (bankPaperCanonicalTopFrozenRoundedSourceSelector
      (K := K0 + 1) B R certificate T deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde)
    p

/-- Exact frozen-top reduction: all nonsmooth rows cancel for the literal
selector, and no equality with the legacy selector is used. -/
theorem
    roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_eq_smooth
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat) :
    roughCanonicalSourceToGuardedCorrectionValuationDefect
        (W := B.sampleData.W) (K := K0 + 1)
        R certificate deltaStar
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L
          (bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde) p =
      roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p := by
  unfold roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
  apply
    R.roughCanonicalSourceToGuardedCorrectionValuationDefect_eq_smooth_of_nonsmooth
      certificate deltaStar
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L
        (bankPaperCanonicalTopFrozenRoundedSourceSelector
          (K := K0 + 1) B R certificate T deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct) qTilde)
  · intro label hactive a ha
    simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
        (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct)
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
            B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct) qTilde)
          hactive ha)
  · intro label hlabel hexceptional a ha
    simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_exceptionalNonsmoothRow
        (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct)
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
            B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct) qTilde)
          hlabel hexceptional ha)

/-- The smallest quantitative source input left after nonsmooth
cancellation: a bound for the literal rounded frozen-top smooth row. -/
def RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat) (bound : Real) : Prop :=
  abs
      (roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect
        B K0 R certificate T deltaStar betaProt betaAct qTilde p) <=
    bound

/-- A bound for the surviving smooth row is a bound for the literal
frozen-top source-to-guarded defect. -/
theorem
    abs_roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_le_of_smooth
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat) (bound : Real)
    (hsmooth :
      RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
        B K0 R certificate T deltaStar betaProt betaAct qTilde p bound) :
    abs
      (roughCanonicalSourceToGuardedCorrectionValuationDefect
        (W := B.sampleData.W) (K := K0 + 1)
        R certificate deltaStar
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L
          (bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde) p) <=
      bound := by
  rw [
    roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_eq_smooth
      B K0 R certificate T deltaStar betaProt betaAct qTilde p]
  exact hsmooth

/-! ## The two literal non-placement defect inputs -/

/-- The frozen-top source defect after exact smooth reduction, together
with the already source-independent guarded/raw rowwise majorant. -/
def BankPaperCanonicalTopFrozenRoundedTwoImplementationDefectRateInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (p : Nat) (scale Csource CguardedRaw : Real) : Prop :=
  RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
      B K0 R certificate T deltaStar betaProt betaAct qTilde p
        (Csource * scale) ∧
    RoughCanonicalGuardedRawCorrectionValuationRowwiseBound
      R certificate deltaStar B.sampleData.W (K0 + 1)
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L p
      (CguardedRaw * scale)

/-- The two reduced inputs and any literal placement-moment bound construct
the three-conjunct frozen-top implementation package. -/
theorem
    bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_defectReductions
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat) (scale Csource CguardedRaw Cplacement : Real)
    (hdefects :
      BankPaperCanonicalTopFrozenRoundedTwoImplementationDefectRateInputs
        B K0 R certificate T deltaStar betaProt betaAct qTilde
          p scale Csource CguardedRaw)
    (hplacement :
      abs
        (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde)
          placementSeed p) <=
        Cplacement * scale) :
    BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
      B K0 R certificate T deltaStar betaProt betaAct qTilde
        placementSeed p scale Csource CguardedRaw Cplacement := by
  rcases hdefects with ⟨hsource, hguardedRaw⟩
  refine ⟨?_, ?_, hplacement⟩
  · exact
      abs_roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_le_of_smooth
        B K0 R certificate T deltaStar betaProt betaAct qTilde
          p (Csource * scale) hsource
  · exact
      R.abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_of_rowwise
        certificate deltaStar
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L
        (CguardedRaw * scale) hguardedRaw

/-- Direct aggregate variant of the implementation-input constructor.
This is the appropriate interface when the guarded/raw defect has been
estimated after summing the rows, without imposing the stronger rowwise
majorant used by
`bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_defectReductions`. -/
theorem
    bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_smooth_aggregateGuardedRaw_and_placement
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (p : Nat) (scale Csource CguardedRaw Cplacement : Real)
    (hsmooth :
      RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
        B K0 R certificate T deltaStar betaProt betaAct qTilde p
          (Csource * scale))
    (hguardedRaw :
      abs
        (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W (K0 + 1)
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L p) <=
        CguardedRaw * scale)
    (hplacement :
      abs
        (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde)
          placementSeed p) <=
        Cplacement * scale) :
    BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
      B K0 R certificate T deltaStar betaProt betaAct qTilde
        placementSeed p scale Csource CguardedRaw Cplacement := by
  refine ⟨?_, hguardedRaw, hplacement⟩
  exact
    abs_roughCanonicalTopFrozenRoundedSourceToGuardedCorrectionValuationDefect_le_of_smooth
      B K0 R certificate T deltaStar betaProt betaAct qTilde
        p (Csource * scale) hsmooth

/-! ## Source-parametric two-zero placement moment -/

/-- Exact uniform-cell valuation expectation for a structured placement
starting from an arbitrary two-zero-head-cell source.  The retained outside
selector only needs to agree with the old tagged seed on occupied active
coordinates outside the protected pool. -/
theorem
    bankPaperCanonicalTwoZeroHeadCellSourceStructuredPlacementValuationMoment_eq
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (outsideSelector : Nat -> Real)
    (minusMass plusMass : Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 ->
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p =
      minusMass *
          (B.guardedCellProbability (none, .minus)).expect
            (fun m ↦ valuation p (m : Nat)) +
        plusMass *
          (B.guardedCellProbability (none, .plus)).expect
            (fun m ↦ valuation p (m : Nat)) := by
  classical
  have hdiff (a : Nat) :
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source_of_active
      (K := K) B R certificate deltaStar betaProt oldSeed
        outsideSelector houtsideActive minusMass plusMass a
  have hvalues (m : B.sampleData.Sample) :
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  unfold
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a) *
          (a.factorization p : Real)) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a) * valuation p a := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [hdiff a]
        rfl
    _ =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
                (bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass) a *
              valuation p a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a * valuation p a := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
    _ =
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass m *
              valuation p (B.sampleData.value m)) -
          ∑ m : B.sampleData.Sample,
            oldSeed m * valuation p (B.sampleData.value m) := by
        rw [
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass)
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues p,
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData oldSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues p]
    _ =
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalUniformCellIncrement
                B.sampleData (none, .minus) minusMass m *
              valuation p (B.sampleData.value m)) +
          ∑ m : B.sampleData.Sample,
            bankPaperCanonicalUniformCellIncrement
                B.sampleData (none, .plus) plusMass m *
              valuation p (B.sampleData.value m) := by
        rw [show
          (∑ m : B.sampleData.Sample,
              bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass m *
                valuation p (B.sampleData.value m)) =
            (∑ m : B.sampleData.Sample,
                oldSeed m * valuation p (B.sampleData.value m)) +
              (∑ m : B.sampleData.Sample,
                bankPaperCanonicalUniformCellIncrement
                    B.sampleData (none, .minus) minusMass m *
                  valuation p (B.sampleData.value m)) +
              ∑ m : B.sampleData.Sample,
                bankPaperCanonicalUniformCellIncrement
                    B.sampleData (none, .plus) plusMass m *
                  valuation p (B.sampleData.value m) by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro m _hm
            unfold bankPaperCanonicalTwoZeroHeadCellRebalance
            ring]
        ring
    _ =
      minusMass *
          (B.guardedCellProbability (none, .minus)).expect
            (fun m ↦ valuation p (m : Nat)) +
        plusMass *
          (B.guardedCellProbability (none, .plus)).expect
            (fun m ↦ valuation p (m : Nat)) := by
        rw [
          sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
            B (none, .minus) minusMass p,
          sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
            B (none, .plus) plusMass p]

/-- Reciprocal uniform-cell valuation means and an absolute two-cell mass
budget give the paper-rate bound for the source-parametric placement. -/
theorem
    abs_bankPaperCanonicalTwoZeroHeadCellSourceStructuredPlacementValuationMoment_le_paperRate
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (outsideSelector : Nat -> Real)
    (minusMass plusMass Aval Cmass : Real) (p : Nat)
    (hp : p.Prime)
    (hAval : 0 <= Aval) (_hCmass : 0 <= Cmass)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 ->
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hmean : ∀ sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) <= Aval / (p : Real))
    (hmass :
      |minusMass| + |plusMass| <=
        Cmass * secondOrderScale B.sampleData.n / B.L) :
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p) <=
      Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := by
  let meanMinus : Real :=
    (B.guardedCellProbability (none, .minus)).expect
      (fun m ↦ valuation p (m : Nat))
  let meanPlus : Real :=
    (B.guardedCellProbability (none, .plus)).expect
      (fun m ↦ valuation p (m : Nat))
  have hmeanMinusNonneg : 0 <= meanMinus :=
    (B.guardedCellProbability (none, .minus)).expect_nonneg _
      (fun m ↦ valuation_nonneg p (m : Nat))
  have hmeanPlusNonneg : 0 <= meanPlus :=
    (B.guardedCellProbability (none, .plus)).expect_nonneg _
      (fun m ↦ valuation_nonneg p (m : Nat))
  have hmeanMinus : meanMinus <= Aval / (p : Real) := hmean .minus
  have hmeanPlus : meanPlus <= Aval / (p : Real) := hmean .plus
  have hpReal : 0 < (p : Real) := by
    exact_mod_cast hp.pos
  have hrateNonneg : 0 <= Aval / (p : Real) :=
    div_nonneg hAval hpReal.le
  rw [
    bankPaperCanonicalTwoZeroHeadCellSourceStructuredPlacementValuationMoment_eq
      B R certificate deltaStar betaProt oldSeed outsideSelector
        minusMass plusMass houtsideActive hactiveSmooth p]
  change abs (minusMass * meanMinus + plusMass * meanPlus) <= _
  calc
    abs (minusMass * meanMinus + plusMass * meanPlus) <=
        abs (minusMass * meanMinus) + abs (plusMass * meanPlus) :=
      abs_add_le _ _
    _ = |minusMass| * meanMinus + |plusMass| * meanPlus := by
      rw [abs_mul, abs_mul, abs_of_nonneg hmeanMinusNonneg,
        abs_of_nonneg hmeanPlusNonneg]
    _ <= |minusMass| * (Aval / (p : Real)) +
        |plusMass| * (Aval / (p : Real)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmeanMinus (abs_nonneg minusMass))
        (mul_le_mul_of_nonneg_left hmeanPlus (abs_nonneg plusMass))
    _ = (|minusMass| + |plusMass|) * (Aval / (p : Real)) := by
      ring
    _ <= (Cmass * secondOrderScale B.sampleData.n / B.L) *
        (Aval / (p : Real)) :=
      mul_le_mul_of_nonneg_right hmass hrateNonneg
    _ = Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := by
      field_simp [hpReal.ne', B.L_pos.ne']

/-! ## Literal frozen-top placement specialization -/

/-- The exact compatibility needed to reuse the two-zero-cell placement
formula for the rounded frozen-top source.  It only concerns occupied
structured active coordinates outside the protected broad pool. -/
def BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real) : Prop :=
  ∀ a,
    a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
    a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ->
    bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
        B R certificate deltaStar alpha beta
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde) a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) a

/-- A concrete sufficient form of outside compatibility: the restored
top weight vanishes on the relevant structured active coordinates. -/
def BankPaperCanonicalTopFrozenSmoothTopInvisibleOnStructuredActive
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha : Real) : Prop :=
  ∀ a,
    a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
    a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ->
    bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
      (upperTailLength c B.sampleData.n) K alpha B.L a = 0

/-- Vanishing of the restored top weight supplies the exact outside
compatibility, by unfolding the label-one branch on the guarded smooth row. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_topInvisible
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htop :
      BankPaperCanonicalTopFrozenSmoothTopInvisibleOnStructuredActive
        (K := K) B R certificate deltaStar alpha) :
    BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
      (K := K) B R certificate T deltaStar betaProt alpha beta qTilde := by
  intro a haActive haNotPool
  have haRow := hactiveSmooth haActive
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRow).2
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop
  rw [if_pos haLabel, htop a haActive haNotPool]
  ring

/-- Exact placement moment for the literal rounded frozen-top source and a
second two-zero-cell rebalance of its rounded active seed. -/
theorem
    bankPaperCanonicalTopFrozenRoundedStructuredPlacementValuationMoment_twoZeroHeadCells_eq
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (minusMass plusMass : Real)
    (hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate T deltaStar betaProt alpha beta qTilde)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          minusMass plusMass) p =
      minusMass *
          (B.guardedCellProbability (none, .minus)).expect
            (fun m ↦ valuation p (m : Nat)) +
        plusMass *
          (B.guardedCellProbability (none, .plus)).expect
            (fun m ↦ valuation p (m : Nat)) := by
  simpa only [
    bankPaperCanonicalTopFrozenRoundedSourceSelector,
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using
    (bankPaperCanonicalTwoZeroHeadCellSourceStructuredPlacementValuationMoment_eq
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde))
        minusMass plusMass hcompat hactiveSmooth p)

/-- Paper-rate form of the preceding exact frozen-top placement identity. -/
theorem
    abs_bankPaperCanonicalTopFrozenRoundedStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real)
    (minusMass plusMass Aval Cmass : Real) (p : Nat)
    (hp : p.Prime)
    (hAval : 0 <= Aval) (hCmass : 0 <= Cmass)
    (hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate T deltaStar betaProt alpha beta qTilde)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hmean : ∀ sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) <= Aval / (p : Real))
    (hmass :
      |minusMass| + |plusMass| <=
        Cmass * secondOrderScale B.sampleData.n / B.L) :
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate T deltaStar betaProt alpha qTilde)
          minusMass plusMass) p) <=
      Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := by
  simpa only [
    bankPaperCanonicalTopFrozenRoundedSourceSelector,
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using
    (abs_bankPaperCanonicalTwoZeroHeadCellSourceStructuredPlacementValuationMoment_le_paperRate
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde))
        minusMass plusMass Aval Cmass p hp hAval hCmass
        hcompat hactiveSmooth hmean hmass)

/-! ## Complete three-input constructor -/

/-- The exact reductions above fill all three literal implementation
conjuncts for a two-zero-cell Post-Hfit placement.  The remaining premises
are precisely the honest quantitative smooth-row, guarded/raw, uniform-cell
mean, and two-cell mass estimates. -/
theorem
    bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_defectReductions_and_twoZeroHeadCellMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt betaAct qTilde : Real)
    (minusMass plusMass Aval Cmass Csource CguardedRaw : Real)
    (p : Nat)
    (hp : p.Prime)
    (hAval : 0 <= Aval) (hCmass : 0 <= Cmass)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K0 + 1) B R certificate T deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) qTilde)
    (hmean : ∀ sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) <= Aval / (p : Real))
    (hmass :
      |minusMass| + |plusMass| <=
        Cmass * secondOrderScale B.sampleData.n / B.L)
    (hdefects :
      BankPaperCanonicalTopFrozenRoundedTwoImplementationDefectRateInputs
        B K0 R certificate T deltaStar betaProt betaAct qTilde p
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L))
        Csource CguardedRaw) :
    BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
      B K0 R certificate T deltaStar betaProt betaAct qTilde
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
          B R certificate T deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct) qTilde)
        minusMass plusMass)
      p (secondOrderScale B.sampleData.n / ((p : Real) * B.L))
      Csource CguardedRaw (Cmass * Aval) := by
  apply
    bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_defectReductions
      B K0 R certificate T deltaStar betaProt betaAct qTilde
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
            B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct) qTilde)
          minusMass plusMass)
        p (secondOrderScale B.sampleData.n / ((p : Real) * B.L))
        Csource CguardedRaw (Cmass * Aval) hdefects
  have hplacement :=
    abs_bankPaperCanonicalTopFrozenRoundedStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
      (K := K0 + 1) B R certificate T deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde minusMass plusMass Aval Cmass p
        hp hAval hCmass hcompat hactiveSmooth hmean hmass
  calc
    abs
        (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde)
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
              B R certificate T deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct) qTilde)
            minusMass plusMass) p) <=
      Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := hplacement
    _ = (Cmass * Aval) *
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L)) := by
      ring

end BankPaperRealization

end

end Erdos390.WholePaper
