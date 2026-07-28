import Erdos390.WholePaper.BankPaperCanonicalSignedResidualSelectorIdentification

/-!
# Exact guarded-versus-raw correction-moment defect

The implemented nonsmooth selector spreads each postcharge discrepancy over
the guarded broad pool.  The quantitative signed residual instead uses the
older correction on the raw broad pool.  These corrections have the same
outer row index, but guarding changes both

* the correction numerator, through fixed/base charges and deleted raw mass;
* the normalized `p`-valuation moment of the correction pool.

Consequently, equality of the two aggregate correction moments is not a
set-theoretic reindex.  This file records the unconditional rowwise defect
and its exact aggregate sum.  Division is the totalized real division used by
the underlying correction densities, so none of the identities below needs a
pool-nonemptiness hypothesis.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

/-! ## Normalized pool moments and the postcharge numerator shift -/

/-- The raw broad pool's totalized normalized `p`-valuation moment. -/
def roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
    (W n h K label p : Nat) : Real :=
  (∑ a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) label,
      (a.factorization p : Real)) /
    ((roughCanonicalBroadCorrectionPool W n h K
      (yNat n) label).card : Real)

/-- The guarded broad pool's totalized normalized `p`-valuation moment. -/
def roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label p : Nat) : Real :=
  (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K label,
      (a.factorization p : Real)) /
    ((R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label).card : Real)

/-- The change in the guarded postcharge numerator relative to the raw row
discrepancy.  It contains the two charged multiplicities and restores raw
mass on every coordinate deleted from the row. -/
def roughCanonicalGuardedPostchargeRawNumeratorShift
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K label : Nat) (rawWeight : Nat -> Real) : Real :=
  -(completeLabelMultiplicity (yNat n)
      (R.paperFixedExceptionalFactors deltaStar) label : Real) -
    (completeLabelMultiplicity (yNat n)
      R.prechargeBaseState label : Real) +
    ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar K label,
      rawWeight a

/-- On an active nonexceptional row the fixed-exceptional multiplicity in the
numerator shift vanishes. -/
theorem roughCanonicalGuardedPostchargeRawNumeratorShift_eq_of_active
    {c : Real} {depth n K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (rawWeight : Nat -> Real)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
        deltaStar K label rawWeight =
      -(completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : Real) +
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar K label,
          rawWeight a := by
  unfold roughCanonicalGuardedPostchargeRawNumeratorShift
  rw [
    R.paperFixedExceptionalFactors_completeLabelMultiplicity_eq_zero_of_active
      deltaStar label hactive]
  ring

/-! ## Density and row-moment identities -/

/-- The raw correction density is definitionally the raw discrepancy divided
by the raw broad-pool cardinality. -/
theorem roughCanonicalRawCorrectionDensityAtLabel_eq_rawDiscrepancy_div
    (W n h K label : Nat) (alpha beta ell : Real) :
    roughCanonicalRawCorrectionDensityAtLabel
        W n h K alpha beta ell label =
      roughCanonicalRawRowDiscrepancy n h K label
          (roughHeadCompatibleRawWeight W n h K alpha beta ell) /
        ((roughCanonicalBroadCorrectionPool W n h K
          (yNat n) label).card : Real) := by
  rfl

/-- The guarded density is the raw discrepancy plus the explicit postcharge
numerator shift, divided by the guarded broad-pool cardinality. -/
theorem roughCanonicalGuardedPostchargeCorrectionDensity_eq_rawDiscrepancy_add_shift_div
    {c : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W K label alpha beta ell =
      (roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) +
        R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
          deltaStar K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell)) /
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card : Real) := by
  rw [
    R.roughCanonicalGuardedPostchargeCorrectionDensity_eq_rawLedger
      certificate deltaStar alpha beta ell]
  unfold roughCanonicalGuardedPostchargeRawNumeratorShift
  ring

/-- The raw correction contribution of one complete-rough label. -/
def roughCanonicalRawRowCorrectionValuationMomentAtLabel
    (W n h K label : Nat) (alpha beta ell : Real) (p : Nat) : Real :=
  roughCanonicalRawCorrectionDensityAtLabel
      W n h K alpha beta ell label *
    ∑ a ∈ roughCanonicalBroadCorrectionPool W n h K (yNat n) label,
      (a.factorization p : Real)

/-- The implemented guarded postcharge correction contribution of one
complete-rough label. -/
def roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
      deltaStar W K label alpha beta ell *
    ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K label,
      (a.factorization p : Real)

/-- The literal guarded-minus-raw correction-moment defect in one row. -/
def roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  R.roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
      certificate deltaStar W K label alpha beta ell p -
    roughCanonicalRawRowCorrectionValuationMomentAtLabel
      W n (upperTailLength c n) K label alpha beta ell p

/-- Exact unconditional row defect.  Its first term measures the change in
the normalized pool valuation moment, and its second term measures the
postcharge numerator shift against the guarded normalized moment. -/
theorem roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
        certificate deltaStar W K label alpha beta ell p =
      roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) *
        (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
            certificate deltaStar W K label p -
          roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
            W n (upperTailLength c n) K label p) +
      R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
          deltaStar K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) *
        R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
          certificate deltaStar W K label p := by
  unfold roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
  unfold roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
  unfold roughCanonicalRawRowCorrectionValuationMomentAtLabel
  rw [
    R.roughCanonicalGuardedPostchargeCorrectionDensity_eq_rawDiscrepancy_add_shift_div
      certificate deltaStar alpha beta ell,
    roughCanonicalRawCorrectionDensityAtLabel_eq_rawDiscrepancy_div]
  unfold
    roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
  unfold roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
  ring

/-- Active-row specialization of the explicit defect: the only numerator
shift left is deleted raw mass minus the base multiplicity. -/
theorem roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit_of_active
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
        certificate deltaStar W K label alpha beta ell p =
      roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) *
        (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
            certificate deltaStar W K label p -
          roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
            W n (upperTailLength c n) K label p) +
      (-(completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : Real) +
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar K label,
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell a) *
        R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
          certificate deltaStar W K label p := by
  rw [
    R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit
      certificate deltaStar alpha beta ell,
    R.roughCanonicalGuardedPostchargeRawNumeratorShift_eq_of_active
      certificate deltaStar
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell) hactive]

/-! ## Aggregate defect -/

/-- The literal difference between the implemented guarded aggregate
correction moment and the older raw aggregate correction moment. -/
def roughCanonicalAggregateGuardedRawCorrectionValuationDefect
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
      deltaStar W K alpha beta ell p -
    roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) K deltaStar alpha beta ell p

/-- The global guarded-minus-raw defect is exactly the sum of the literal
row defects over the common active-label set. -/
theorem roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_rowDefects
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar W K alpha beta ell p =
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
          certificate deltaStar W K label alpha beta ell p := by
  unfold roughCanonicalAggregateGuardedRawCorrectionValuationDefect
  rw [
    roughCanonicalAggregateRawRowCorrection_eq_density_mul_valuationSum]
  unfold roughCanonicalAggregateGuardedPostchargeRowCorrection
  unfold roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
  unfold roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
  unfold roughCanonicalRawRowCorrectionValuationMomentAtLabel
  rw [Finset.sum_sub_distrib]

/-- Fully explicit aggregate defect, without any moment-preservation
assumption. -/
theorem roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_explicit
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar W K alpha beta ell p =
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        (roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
            (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell) *
          (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
              certificate deltaStar W K label p -
            roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
              W n (upperTailLength c n) K label p) +
        R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
            deltaStar K label
            (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell) *
          R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
            certificate deltaStar W K label p) := by
  rw [
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_rowDefects
      certificate deltaStar alpha beta ell]
  exact Finset.sum_congr
    (s₁ := roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar)
    (s₂ := roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar)
    rfl (fun label _hlabel =>
    R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit
      (W := W) (K := K) (label := label) (p := p)
      certificate deltaStar alpha beta ell)

/-- Active-label form of the aggregate defect.  The displayed two summands
are precisely the pool-average change and the remaining base/deletion
numerator change. -/
theorem roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_explicit_active
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar W K alpha beta ell p =
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        (roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
            (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell) *
          (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
              certificate deltaStar W K label p -
            roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
              W n (upperTailLength c n) K label p) +
        (-(completeLabelMultiplicity (yNat n)
            R.prechargeBaseState label : Real) +
          ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar K label,
            roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell a) *
          R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
            certificate deltaStar W K label p) := by
  rw [
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_rowDefects
      certificate deltaStar alpha beta ell]
  exact Finset.sum_congr
    (s₁ := roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar)
    (s₂ := roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar)
    rfl (fun label hlabel =>
    R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit_of_active
      (W := W) (K := K) (label := label) (p := p)
      certificate deltaStar alpha beta ell
      (mem_roughCanonicalActiveRawCorrectionLabels.mp hlabel).2)

/-- The disputed guarded-to-raw reindex is exactly the assertion that the
explicit aggregate defect vanishes. -/
theorem roughCanonicalAggregateGuardedPostchargeRowCorrection_eq_raw_iff_defect_eq_zero
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
        deltaStar W K alpha beta ell p =
        roughCanonicalAggregateRawRowCorrection W n
          (upperTailLength c n) K deltaStar alpha beta ell p ↔
      R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar W K alpha beta ell p = 0 := by
  unfold roughCanonicalAggregateGuardedRawCorrectionValuationDefect
  constructor
  · intro h
    rw [h, sub_self]
  · intro h
    linarith

/-- Specialization of the preceding equivalence to the named Post-Hfit
guarded-to-raw reindex request. -/
theorem bankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex_iff_guardedRawDefect_eq_zero
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
    (deltaStar betaProt betaAct : Real) (p : Nat) :
    BankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex
        B K0 R certificate deltaStar betaProt betaAct p ↔
      R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar B.sampleData.W (K0 + 1)
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L p = 0 := by
  unfold BankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex
  exact
    R.roughCanonicalAggregateGuardedPostchargeRowCorrection_eq_raw_iff_defect_eq_zero
      certificate deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L

/-- Rowwise vanishing of the explicit defects is a sufficient, transparent
condition for the global defect to vanish. -/
theorem roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_zero_of_rowwise
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (hrow :
      ∀ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
          certificate deltaStar W K label alpha beta ell p = 0) :
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect certificate
        deltaStar W K alpha beta ell p = 0 := by
  rw [
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_rowDefects
      certificate deltaStar alpha beta ell]
  apply Finset.sum_eq_zero
  intro label hlabel
  exact hrow label hlabel

end BankPaperRealization

end

end Erdos390.WholePaper
