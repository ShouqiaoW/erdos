import Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitPaperRateClosureConnector
import Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure

/-!
# Quantitative reduction of the two selector implementation defects

The selector-deficit closure leaves two implementation terms:

* the actual Post-Hfit source moment minus the correction installed on the
  guarded nonsmooth pools;
* that guarded correction minus the older correction on raw pools.

This file reduces both terms without identifying either pair of moments by
fiat.  The first defect is partitioned by complete rough rows.  The already
proved pointwise formula for the global source kills every nonsmooth row,
so only the literal smooth-row defect remains.  The second defect is bounded
by the exact two rowwise quantities from the guarded/raw defect formula:
the normalized pool-moment shift and the postcharge numerator shift.

The finite guard census is used once more to bound the latter numerator
shift by `1 + 3 M` whenever the raw row coordinates have absolute value at
most `M`.  Thus any later analytic estimate sees the precise pool-moment
input that is still required rather than an unjustified reindex.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

/-! ## Row partition of the source-to-guarded defect -/

/-- The contribution of one raw complete-rough label to the difference
between an actual source correction moment and a supplied family of guarded
row-correction moments.  The second sum uses the literal nonexceptional
guarded set, so the definition remains valid without deciding whether the
smooth label itself is exceptional. -/
def roughCanonicalSourceGuardedRowValuationDefectAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat)
    (selector rawWeight : Nat -> Real)
    (guardedCorrection : Nat -> Real) (p label : Nat) : Real :=
  by
    classical
    exact
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          selector a * (a.factorization p : Real)) -
        (∑ a ∈ completeRoughRowFiber (yNat n)
            (R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
              deltaStar K) label,
          rawWeight a * (a.factorization p : Real)) -
        if RoughCanonicalActiveNonexceptionalLabel n deltaStar label then
          guardedCorrection label
        else
          0

/-- The nonexceptional filter does nothing inside a row whose label is
nonexceptional. -/
theorem completeRoughRowFiber_nonexceptionalGuarded_eq_guardedRow
    {c : Real} {depth n K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hlabel :
      ¬ RoughCanonicalExceptionalLabel n deltaStar label) :
    completeRoughRowFiber (yNat n)
        (R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
          deltaStar K) label =
      R.roughCanonicalGuardedRow certificate deltaStar K label := by
  classical
  ext a
  constructor
  · intro ha
    have haData := mem_completeRoughRowFiber.mp ha
    have haNonexceptional :=
      (R.mem_roughCanonicalNonexceptionalGuardedCandidateSet
        certificate deltaStar).1 haData.1
    exact mem_completeRoughRowFiber.mpr
      ⟨haNonexceptional.1, haData.2⟩
  · intro ha
    have haData := mem_completeRoughRowFiber.mp ha
    apply mem_completeRoughRowFiber.mpr
    refine ⟨(R.mem_roughCanonicalNonexceptionalGuardedCandidateSet
      certificate deltaStar).2 ⟨haData.1, ?_⟩, haData.2⟩
    simpa only [haData.2] using hlabel

/-- The nonexceptional filtered row is empty at an exceptional label. -/
theorem completeRoughRowFiber_nonexceptionalGuarded_eq_empty
    {c : Real} {depth n K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hlabel : RoughCanonicalExceptionalLabel n deltaStar label) :
    completeRoughRowFiber (yNat n)
        (R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
          deltaStar K) label = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro a ha
  have haData := mem_completeRoughRowFiber.mp ha
  have haNonexceptional :=
    (R.mem_roughCanonicalNonexceptionalGuardedCandidateSet
      certificate deltaStar).1 haData.1
  exact haNonexceptional.2 (by simpa only [haData.2] using hlabel)

/-- Pure finite algebra: source minus a correction summed over active raw
labels is the sum of the displayed row defects over every attained raw
label. -/
theorem roughCanonicalSourceValuationCorrectionMoment_sub_guardedCorrection_eq_sum_rowDefects
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (guardedCorrection : Nat -> Real) :
    roughCanonicalSourceValuationCorrectionMoment
        (W := W) (K := K)
        R certificate deltaStar alpha beta ell selector p -
      (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        guardedCorrection label) =
      ∑ label ∈ completeRoughLabelSet (yNat n)
          (roughRawCandidateSet n (upperTailLength c n) K),
        R.roughCanonicalSourceGuardedRowValuationDefectAtLabel
          certificate deltaStar K selector
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell)
          guardedCorrection p label := by
  classical
  let labels :=
    completeRoughLabelSet (yNat n)
      (roughRawCandidateSet n (upperTailLength c n) K)
  have hguardedLabels :
      completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K) ⊆
        labels := by
    intro label hlabel
    obtain ⟨a, ha, halabel⟩ := mem_completeRoughLabelSet.mp hlabel
    exact mem_completeRoughLabelSet.mpr
      ⟨a,
        R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
          certificate deltaStar K ha,
        halabel⟩
  have hnonexceptionalLabels :
      completeRoughLabelSet (yNat n)
          (R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
            deltaStar K) ⊆ labels := by
    intro label hlabel
    obtain ⟨a, ha, halabel⟩ := mem_completeRoughLabelSet.mp hlabel
    have haGuarded :=
      ((R.mem_roughCanonicalNonexceptionalGuardedCandidateSet
        certificate deltaStar).1 ha).1
    exact mem_completeRoughLabelSet.mpr
      ⟨a,
        R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
          certificate deltaStar K haGuarded,
        halabel⟩
  unfold roughCanonicalSourceValuationCorrectionMoment
  rw [sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
      (yNat n)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      labels
      (fun a => selector a * (a.factorization p : Real))
      hguardedLabels,
    sum_eq_sum_completeRoughRowFibers_of_labelSet_subset
      (yNat n)
      (R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
        deltaStar K)
      labels
      (fun a =>
        roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell a * (a.factorization p : Real))
      hnonexceptionalLabels]
  unfold roughCanonicalActiveRawCorrectionLabels
  rw [Finset.sum_filter]
  simp only [labels, roughCanonicalGuardedRow,
    roughCanonicalSourceGuardedRowValuationDefectAtLabel,
    Finset.sum_sub_distrib]

/-! ## Post-Hfit specialization and nonsmooth cancellation -/

/-- The Post-Hfit specialization of the preceding row defect. -/
def roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real) (p label : Nat) : Real :=
  R.roughCanonicalSourceGuardedRowValuationDefectAtLabel certificate
    deltaStar (K0 + 1)
    (bankPaperCanonicalPostHfitGlobalSourceSelector
      B K0 R certificate deltaStar betaProt betaAct oldSeed)
    (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
      (upperTailLength c B.sampleData.n) (K0 + 1)
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L)
    (fun rowLabel =>
      R.roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
        certificate deltaStar B.sampleData.W (K0 + 1) rowLabel
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L p)
    p label

/-- The source-to-guarded defect is exactly the sum of its literal row
defects over the raw attained labels. -/
theorem roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_eq_sum_rowDefects
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) :
    roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
        B K0 R certificate deltaStar betaProt betaAct oldSeed p =
      ∑ label ∈ completeRoughLabelSet (yNat B.sampleData.n)
          (roughRawCandidateSet B.sampleData.n
            (upperTailLength c B.sampleData.n) (K0 + 1)),
        roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
          B K0 R certificate deltaStar betaProt betaAct oldSeed p label := by
  simpa only [
    roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect,
    roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment,
    roughCanonicalAggregateGuardedPostchargeRowCorrection,
    roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel,
    roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel] using
    (R.roughCanonicalSourceValuationCorrectionMoment_sub_guardedCorrection_eq_sum_rowDefects
      certificate deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      (fun rowLabel =>
        R.roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
          certificate deltaStar B.sampleData.W (K0 + 1) rowLabel
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L p))

/-- Every active nonsmooth Post-Hfit row has zero source-to-guarded row
defect: the actual source is the guarded corrected weight on the whole row,
and the existing row-moment identity extracts exactly the installed
correction. -/
theorem roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel_eq_zero_of_active
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 label p : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label) :
    roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
        B K0 R certificate deltaStar betaProt betaAct oldSeed p label = 0 := by
  classical
  let alpha :=
    bankPaperCanonicalPostHfitBalancedAlpha
      B c K0 betaProt betaAct
  let beta := betaProt + betaAct
  have hnotExceptional :
      ¬ RoughCanonicalExceptionalLabel
        B.sampleData.n deltaStar label :=
    not_lt_of_ge hactive.2
  have hsource :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar
          (K0 + 1) label,
        bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed a *
          (a.factorization p : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar
            (K0 + 1) label,
          R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W (K0 + 1) label
              alpha beta B.L a *
            (a.factorization p : Real) := by
    unfold bankPaperCanonicalPostHfitGlobalSourceSelector
    apply Finset.sum_congr rfl
    intro a ha
    rw [bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_nonsmoothRow
      B R certificate deltaStar betaProt alpha beta oldSeed hactive ha]
  unfold roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
  unfold roughCanonicalSourceGuardedRowValuationDefectAtLabel
  rw [
    R.completeRoughRowFiber_nonexceptionalGuarded_eq_guardedRow
      certificate deltaStar hnotExceptional,
    if_pos hactive,
    hsource,
    R.sum_guardedPostchargeRowCorrectedWeight_mul_factorization_eq
      certificate deltaStar alpha beta B.L]
  unfold
    roughCanonicalGuardedPostchargeRowCorrectionValuationMomentAtLabel
  ring

/-- Every exceptional nonsmooth Post-Hfit row also has zero row defect:
the source vanishes there, the nonexceptional baseline row is empty, and
the row is not in the active correction family. -/
theorem roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel_eq_zero_of_exceptional
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 label p : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (hlabel : label ≠ 1)
    (hexceptional :
      RoughCanonicalExceptionalLabel B.sampleData.n deltaStar label) :
    roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
        B K0 R certificate deltaStar betaProt betaAct oldSeed p label = 0 := by
  classical
  let alpha :=
    bankPaperCanonicalPostHfitBalancedAlpha
      B c K0 betaProt betaAct
  let beta := betaProt + betaAct
  have hnotActive :
      ¬ RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label := by
    intro hactive
    exact (not_lt_of_ge hactive.2) hexceptional
  have hsource :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar
          (K0 + 1) label,
        bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed a *
          (a.factorization p : Real)) = 0 := by
    unfold bankPaperCanonicalPostHfitGlobalSourceSelector
    apply Finset.sum_eq_zero
    intro a ha
    rw [
      bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_exceptionalNonsmoothRow
        B R certificate deltaStar betaProt alpha beta oldSeed
          hlabel hexceptional ha,
      zero_mul]
  unfold roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
  unfold roughCanonicalSourceGuardedRowValuationDefectAtLabel
  rw [
    R.completeRoughRowFiber_nonexceptionalGuarded_eq_empty
      certificate deltaStar hexceptional,
    Finset.sum_empty, if_neg hnotActive, hsource]
  ring

/-- The only row that can survive in the source-to-guarded defect.  The
membership guard makes the definition valid even when the raw smooth row
is empty. -/
def roughCanonicalPostHfitSmoothSourceToGuardedValuationDefect
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) : Real :=
  if 1 ∈ completeRoughLabelSet (yNat B.sampleData.n)
      (roughRawCandidateSet B.sampleData.n
        (upperTailLength c B.sampleData.n) (K0 + 1)) then
    roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
      B K0 R certificate deltaStar betaProt betaAct oldSeed p 1
  else
    0

/-- Exact source reduction: all nonsmooth rows cancel, leaving only the
guarded smooth-row valuation mismatch. -/
theorem roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_eq_smooth
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) :
    roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
        B K0 R certificate deltaStar betaProt betaAct oldSeed p =
      roughCanonicalPostHfitSmoothSourceToGuardedValuationDefect
        B K0 R certificate deltaStar betaProt betaAct oldSeed p := by
  classical
  rw [
    roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_eq_sum_rowDefects
      B K0 R certificate deltaStar betaProt betaAct oldSeed p]
  unfold roughCanonicalPostHfitSmoothSourceToGuardedValuationDefect
  let labels :=
    completeRoughLabelSet (yNat B.sampleData.n)
      (roughRawCandidateSet B.sampleData.n
        (upperTailLength c B.sampleData.n) (K0 + 1))
  have hnonsmooth :
      ∀ label ∈ labels, label ≠ 1 ->
        roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel
          B K0 R certificate deltaStar betaProt betaAct oldSeed p label = 0 := by
    intro label _hlabel hlabel
    rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := B.sampleData.n) (deltaStar := deltaStar) hlabel with
      hactive | hexceptional
    · exact
        roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel_eq_zero_of_active
          B R certificate deltaStar betaProt betaAct oldSeed hactive
    · exact
        roughCanonicalPostHfitSourceGuardedRowValuationDefectAtLabel_eq_zero_of_exceptional
          B R certificate deltaStar betaProt betaAct oldSeed
            hlabel hexceptional
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

/-- Public pointwise source estimate after the exact smooth-row reduction. -/
def RoughCanonicalPostHfitSmoothSourceToGuardedValuationDefectBound
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (p : Nat) (bound : Real) : Prop :=
  abs (roughCanonicalPostHfitSmoothSourceToGuardedValuationDefect
    B K0 R certificate deltaStar betaProt betaAct oldSeed p) <= bound

/-- A bound for the one surviving smooth row is exactly a bound for the
global source-to-guarded defect. -/
theorem abs_roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_le_of_smooth
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (p : Nat) (bound : Real)
    (hsmooth :
      RoughCanonicalPostHfitSmoothSourceToGuardedValuationDefectBound
        B K0 R certificate deltaStar betaProt betaAct oldSeed p bound) :
    abs
      (roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
        B K0 R certificate deltaStar betaProt betaAct oldSeed p) <=
      bound := by
  rw [
    roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_eq_smooth
      B K0 R certificate deltaStar betaProt betaAct oldSeed p]
  exact hsmooth

/-! ## Rowwise guarded/raw rate majorant -/

/-- The part of one raw broad pool removed by the numerical guard.  It is
the exact support of the normalized pool-moment change. -/
def roughCanonicalBroadCorrectionPoolGuardDeleted
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) : Finset Nat :=
  roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
      (yNat n) label ∩
    R.roughCanonicalGuardSet certificate deltaStar

/-- The deleted part of an active broad correction pool contains at most
three coordinates. -/
theorem roughCanonicalBroadCorrectionPoolGuardDeleted_card_le_three
    {c : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    (R.roughCanonicalBroadCorrectionPoolGuardDeleted certificate
      deltaStar W K label).card <= 3 := by
  have hsubset :
      R.roughCanonicalBroadCorrectionPoolGuardDeleted certificate
          deltaStar W K label ⊆
        R.roughCanonicalGuardDeletedRow certificate deltaStar K label := by
    intro a ha
    have haData : a ∈
        roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
            (yNat n) label ∩
          R.roughCanonicalGuardSet certificate deltaStar := by
      simpa only [roughCanonicalBroadCorrectionPoolGuardDeleted] using ha
    exact Finset.mem_inter.mpr
      ⟨roughCanonicalBroadCorrectionPool_subset_rawRow
        W n (upperTailLength c n) K (yNat n) label
          (Finset.mem_inter.mp haData).1,
        (Finset.mem_inter.mp haData).2⟩
  have hcensus :=
    R.roughCanonicalGuardLocalCensusBound_three_of_active certificate
      deltaStar K label hnCutoff hyCutoff hactive
  exact (Finset.card_le_card hsubset).trans
    (by
      simpa only [RoughCanonicalGuardLocalCensusBound] using hcensus)

/-- Cross-multiplied numerator of the change between the guarded and raw
normalized valuation moments. -/
def roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label p : Nat) : Real :=
  (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K label,
      (a.factorization p : Real)) *
      ((roughCanonicalBroadCorrectionPool W n
        (upperTailLength c n) K (yNat n) label).card : Real) -
    (∑ a ∈ roughCanonicalBroadCorrectionPool W n
        (upperTailLength c n) K (yNat n) label,
      (a.factorization p : Real)) *
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K label).card : Real)

/-- The cross numerator is supported exactly on the deleted part of the
pool.  This identity is often more convenient than comparing two quotients
directly. -/
theorem roughCanonicalGuardedRawPoolValuationMomentCrossNumerator_eq_deleted
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) :
    R.roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
        certificate deltaStar W K label p =
      (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K label,
        (a.factorization p : Real)) *
        ((R.roughCanonicalBroadCorrectionPoolGuardDeleted certificate
          deltaStar W K label).card : Real) -
      (∑ a ∈ R.roughCanonicalBroadCorrectionPoolGuardDeleted certificate
          deltaStar W K label,
        (a.factorization p : Real)) *
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K label).card : Real) := by
  classical
  let rawPool :=
    roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
      (yNat n) label
  let guard := R.roughCanonicalGuardSet certificate deltaStar
  let guardedPool := rawPool \ guard
  let deletedPool := rawPool ∩ guard
  have hdisjoint : Disjoint guardedPool deletedPool := by
    rw [Finset.disjoint_left]
    intro a haGuarded haDeleted
    exact (Finset.mem_sdiff.mp haGuarded).2
      (Finset.mem_inter.mp haDeleted).2
  have hunion : guardedPool ∪ deletedPool = rawPool := by
    ext a
    simp only [guardedPool, deletedPool, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hsum :
      (∑ a ∈ rawPool, (a.factorization p : Real)) =
        (∑ a ∈ guardedPool, (a.factorization p : Real)) +
          ∑ a ∈ deletedPool, (a.factorization p : Real) := by
    rw [← hunion, Finset.sum_union hdisjoint]
  have hcardNat :
      rawPool.card = guardedPool.card + deletedPool.card := by
    rw [← hunion, Finset.card_union_of_disjoint hdisjoint]
  have hcard :
      (rawPool.card : Real) =
        (guardedPool.card : Real) + (deletedPool.card : Real) := by
    exact_mod_cast hcardNat
  unfold
    roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
    roughCanonicalBroadCorrectionPoolGuardDeleted
    roughCanonicalGuardedBroadCorrectionPool
  change
    (∑ a ∈ guardedPool, (a.factorization p : Real)) *
          (rawPool.card : Real) -
        (∑ a ∈ rawPool, (a.factorization p : Real)) *
          (guardedPool.card : Real) =
      (∑ a ∈ guardedPool, (a.factorization p : Real)) *
          (deletedPool.card : Real) -
        (∑ a ∈ deletedPool, (a.factorization p : Real)) *
          (guardedPool.card : Real)
  rw [hsum, hcard]
  ring

/-- With nonempty raw and guarded pools, the normalized moment difference
is the cross numerator divided by the product of the two cardinalities. -/
theorem roughCanonicalGuardedNormalizedValuationMoment_sub_raw_eq_crossNumerator_div
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hraw :
      (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
        (yNat n) label).card ≠ 0)
    (hguarded :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card ≠ 0) :
    R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
          certificate deltaStar W K label p -
        roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
          W n (upperTailLength c n) K label p =
      R.roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
          certificate deltaStar W K label p /
        (((R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K label).card : Real) *
          ((roughCanonicalBroadCorrectionPool W n
            (upperTailLength c n) K (yNat n) label).card : Real)) := by
  unfold
    roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
    roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
    roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
  field_simp [Nat.cast_ne_zero.mpr hraw, Nat.cast_ne_zero.mpr hguarded]

/-- The existing raw linear lower bound and the `3`-point guard census make
both denominators in the cross-numerator formula nonzero as soon as the raw
linear mass is at least six. -/
theorem roughCanonicalRaw_and_guardedBroadCorrectionPool_card_ne_zero_of_linear_lower
    {c deltaStar d : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hraw :
      d * ((n / label : Nat) : Real) <=
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card)
    (hsix : 6 <= d * ((n / label : Nat) : Real)) :
    (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
        (yNat n) label).card ≠ 0 ∧
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card ≠ 0 := by
  have hrawPositive :
      (0 : Real) <
        ((roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card : Real) :=
    (by linarith : 0 < d * ((n / label : Nat) : Real)).trans_le hraw
  have hguardedLower :=
    R.roughCanonicalGuardedBroadCorrectionPool_linear_half_lower
      certificate hnCutoff hyCutoff hactive hraw hsix
  have hlinearPositive :
      0 < d / 2 * ((n / label : Nat) : Real) := by
    nlinarith
  have hguardedPositive :
      (0 : Real) <
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          W K label).card : Real) :=
    hlinearPositive.trans_le hguardedLower
  constructor
  · exact (show 0 <
        (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
          (yNat n) label).card by
      exact_mod_cast hrawPositive).ne'
  · exact (show 0 <
        (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
          W K label).card by
      exact_mod_cast hguardedPositive).ne'

/-- The two-term triangle majorant dictated by the exact guarded/raw row
defect: raw discrepancy times normalized pool-moment change, plus the
postcharge numerator shift times the guarded normalized moment. -/
def roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  abs (roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell)) *
    abs
      (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
          certificate deltaStar W K label p -
        roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
          W n (upperTailLength c n) K label p) +
  abs
      (R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
        deltaStar K label
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell)) *
    abs
      (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
        certificate deltaStar W K label p)

/-- When the two pools are nonempty, the row majorant exposes the literal
cross-moment numerator and both pool cardinalities. -/
theorem roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel_eq_crossNumerator
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (hraw :
      (roughCanonicalBroadCorrectionPool W n (upperTailLength c n) K
        (yNat n) label).card ≠ 0)
    (hguarded :
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card ≠ 0) :
    R.roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
        certificate deltaStar W K label alpha beta ell p =
      abs (roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell)) *
        (abs
          (R.roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
            certificate deltaStar W K label p) /
          (((R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar W K label).card : Real) *
            ((roughCanonicalBroadCorrectionPool W n
              (upperTailLength c n) K (yNat n) label).card : Real))) +
      abs
          (R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
            deltaStar K label
            (roughHeadCompatibleRawWeight W n
              (upperTailLength c n) K alpha beta ell)) *
        abs
          (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
            certificate deltaStar W K label p) := by
  have hdenNonneg :
      0 <=
        ((R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
            W K label).card : Real) *
          ((roughCanonicalBroadCorrectionPool W n
            (upperTailLength c n) K (yNat n) label).card : Real) :=
    mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have habsCross :
      abs
          (R.roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
              certificate deltaStar W K label p /
            (((R.roughCanonicalGuardedBroadCorrectionPool certificate
                deltaStar W K label).card : Real) *
              ((roughCanonicalBroadCorrectionPool W n
                (upperTailLength c n) K (yNat n) label).card : Real))) =
        abs
            (R.roughCanonicalGuardedRawPoolValuationMomentCrossNumerator
              certificate deltaStar W K label p) /
          (((R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar W K label).card : Real) *
            ((roughCanonicalBroadCorrectionPool W n
              (upperTailLength c n) K (yNat n) label).card : Real)) := by
    rw [abs_div, abs_of_nonneg hdenNonneg]
  unfold
    roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
  rw [
    R.roughCanonicalGuardedNormalizedValuationMoment_sub_raw_eq_crossNumerator_div
      certificate deltaStar hraw hguarded,
    habsCross]

/-- The exact row defect is bounded by its two literal implementation
components. -/
theorem abs_roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_le_majorant
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    abs
      (R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
        certificate deltaStar W K label alpha beta ell p) <=
      R.roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
        certificate deltaStar W K label alpha beta ell p := by
  rw [
    R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_eq_explicit
      certificate deltaStar alpha beta ell]
  unfold
    roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
  calc
    abs (_ + _) <= abs _ + abs _ := abs_add_le _ _
    _ = _ := by rw [abs_mul, abs_mul]

/-- Aggregate guarded/raw defect bound with no uniformity loss beyond the
outer triangle inequality. -/
theorem abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_rowwiseMajorant
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    abs
      (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
        certificate deltaStar W K alpha beta ell p) <=
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        R.roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
          certificate deltaStar W K label alpha beta ell p := by
  rw [
    R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect_eq_sum_rowDefects
      certificate deltaStar alpha beta ell]
  calc
    abs
        (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
            (upperTailLength c n) K deltaStar,
          R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
            certificate deltaStar W K label alpha beta ell p) <=
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        abs
          (R.roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel
            certificate deltaStar W K label alpha beta ell p) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <=
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        R.roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
          certificate deltaStar W K label alpha beta ell p := by
      apply Finset.sum_le_sum
      intro label _hlabel
      exact
        R.abs_roughCanonicalGuardedRawRowCorrectionValuationDefectAtLabel_le_majorant
          certificate deltaStar alpha beta ell

/-- Public rowwise pool-moment/numerator-shift input for a guarded/raw
aggregate bound. -/
def RoughCanonicalGuardedRawCorrectionValuationRowwiseBound
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (p : Nat) (bound : Real) : Prop :=
  (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar,
    R.roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
      certificate deltaStar W K label alpha beta ell p) <= bound

/-- Aggregate input for only the normalized pool-moment-change part of the
guarded/raw defect. -/
def RoughCanonicalGuardedRawPoolMomentChangeContributionBound
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (p : Nat) (bound : Real) : Prop :=
  (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar,
    abs (roughCanonicalRawRowDiscrepancy n (upperTailLength c n) K label
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell)) *
      abs
        (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
            certificate deltaStar W K label p -
          roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
            W n (upperTailLength c n) K label p)) <= bound

/-- Aggregate input for only the postcharge numerator-shift part of the
guarded/raw defect. -/
def RoughCanonicalGuardedRawNumeratorShiftContributionBound
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (p : Nat) (bound : Real) : Prop :=
  (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar,
    abs
        (R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
          deltaStar K label
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell)) *
      abs
        (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
          certificate deltaStar W K label p)) <= bound

/-- Separate pool-moment and numerator-shift contribution estimates imply
the aggregate guarded/raw bound with the sum of their constants. -/
theorem abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_of_splitContributions
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell poolBound shiftBound : Real)
    (hpool :
      RoughCanonicalGuardedRawPoolMomentChangeContributionBound
        R certificate deltaStar W K alpha beta ell p poolBound)
    (hshift :
      RoughCanonicalGuardedRawNumeratorShiftContributionBound
        R certificate deltaStar W K alpha beta ell p shiftBound) :
    abs
      (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
        certificate deltaStar W K alpha beta ell p) <=
      poolBound + shiftBound := by
  calc
    abs
        (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar W K alpha beta ell p) <=
      ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        R.roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel
          certificate deltaStar W K label alpha beta ell p :=
      R.abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_rowwiseMajorant
        certificate deltaStar alpha beta ell
    _ =
      (∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
          (upperTailLength c n) K deltaStar,
        abs (roughCanonicalRawRowDiscrepancy n
            (upperTailLength c n) K label
            (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell)) *
          abs
            (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
                certificate deltaStar W K label p -
              roughCanonicalRawBroadCorrectionPoolNormalizedValuationMoment
                W n (upperTailLength c n) K label p)) +
        ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
            (upperTailLength c n) K deltaStar,
          abs
              (R.roughCanonicalGuardedPostchargeRawNumeratorShift
                certificate deltaStar K label
                (roughHeadCompatibleRawWeight W n
                  (upperTailLength c n) K alpha beta ell)) *
            abs
              (R.roughCanonicalGuardedBroadCorrectionPoolNormalizedValuationMoment
                certificate deltaStar W K label p) := by
      simp only [
        roughCanonicalGuardedRawRowCorrectionValuationMajorantAtLabel,
        Finset.sum_add_distrib]
    _ <= poolBound + shiftBound := add_le_add hpool hshift

/-- The named rowwise input implies the aggregate guarded/raw defect bound. -/
theorem abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_of_rowwise
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell bound : Real)
    (hrow :
      RoughCanonicalGuardedRawCorrectionValuationRowwiseBound
        R certificate deltaStar W K alpha beta ell p bound) :
    abs
      (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
        certificate deltaStar W K alpha beta ell p) <= bound :=
  (R.abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_rowwiseMajorant
    certificate deltaStar alpha beta ell).trans hrow

/-! ## The finite numerator-shift estimate already available from guards -/

/-- The postcharge numerator shift costs at most `1 + 3M` on every active
row.  This is exactly the existing base/deleted-row census estimate,
rewritten in the numerator-shift language used by the guarded/raw defect. -/
theorem abs_roughCanonicalGuardedPostchargeRawNumeratorShift_le_fixed
    {c : Real} {depth n W K label : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell M : Real)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n)
    (hactive : RoughCanonicalActiveNonexceptionalLabel n deltaStar label)
    (hM : 0 <= M)
    (hweight :
      ∀ a ∈ completeRoughRowFiber (yNat n)
          (roughRawCandidateSet n (upperTailLength c n) K) label,
        abs
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell a) <= M) :
    abs
      (R.roughCanonicalGuardedPostchargeRawNumeratorShift certificate
        deltaStar K label
        (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell)) <=
      1 + 3 * M := by
  let rawWeight :=
    roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta ell
  have hfinite :=
    R.roughCanonicalGuardLocalDiscrepancyIncrement_abs_le_fixed
      certificate deltaStar M rawWeight hnCutoff hyCutoff hactive hM
      (by simpa only [rawWeight] using hweight)
  have hledger :=
    R.roughCanonicalGuardLocalDiscrepancyLedger certificate deltaStar
      K label rawWeight
  rw [hledger] at hfinite
  simpa only [
    roughCanonicalGuardedPostchargeRawNumeratorShift, rawWeight] using
      hfinite

/-! ## Direct connector to the existing implementation-rate package -/

/-- The two defect inputs after their exact reductions.  The placement
moment is deliberately not included. -/
def BankPaperCanonicalPostHfitTwoImplementationDefectRateInputs
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (p : Nat) (scale Csource CguardedRaw : Real) : Prop :=
  RoughCanonicalPostHfitSmoothSourceToGuardedValuationDefectBound
      B K0 R certificate deltaStar betaProt betaAct oldSeed p
        (Csource * scale) ∧
    RoughCanonicalGuardedRawCorrectionValuationRowwiseBound
      R certificate deltaStar B.sampleData.W (K0 + 1)
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L p
      (CguardedRaw * scale)

/-- A smooth-row source estimate and the explicit guarded/raw rowwise
majorant fill the two corresponding conjuncts of the existing medium-prime
implementation package. -/
theorem bankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs_of_defectReductions
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (p : Nat)
    (scale Csource CguardedRaw Cplacement : Real)
    (hdefects :
      BankPaperCanonicalPostHfitTwoImplementationDefectRateInputs
        B K0 R certificate deltaStar betaProt betaAct oldSeed p
          scale Csource CguardedRaw)
    (hplacement :
      abs
        (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p) <=
        Cplacement * scale) :
    BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p scale
        Csource CguardedRaw Cplacement := by
  rcases hdefects with ⟨hsource, hguardedRaw⟩
  refine ⟨?_, ?_, hplacement⟩
  · exact
      abs_roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect_le_of_smooth
        B K0 R certificate deltaStar betaProt betaAct oldSeed p
          (Csource * scale) hsource
  · exact
      R.abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_of_rowwise
        certificate deltaStar
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L (CguardedRaw * scale) hguardedRaw

/-- Eventual form of the preceding connector for a varying prime and
scale.  It is intentionally a transport theorem: all substantive content
is in the smooth-row and rowwise pool-moment hypotheses. -/
theorem eventually_bankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs_of_defectReductions
    {ι : Type*} {l : Filter ι}
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
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real)
    (p : ι -> Nat) (scale : ι -> Real)
    (Csource CguardedRaw Cplacement : Real)
    (hdefects : ∀ᶠ i in l,
      BankPaperCanonicalPostHfitTwoImplementationDefectRateInputs
        B K0 R certificate deltaStar betaProt betaAct oldSeed (p i)
          (scale i) Csource CguardedRaw)
    (hplacement : ∀ᶠ i in l,
      abs
        (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) (p i)) <=
        Cplacement * scale i) :
    ∀ᶠ i in l,
      BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
        B K0 R certificate deltaStar betaProt betaAct oldSeed
          minusMass plusMass (p i) (scale i)
          Csource CguardedRaw Cplacement := by
  filter_upwards [hdefects, hplacement] with i hdefectsI hplacementI
  exact
    bankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs_of_defectReductions
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass (p i) (scale i)
        Csource CguardedRaw Cplacement hdefectsI hplacementI

end BankPaperRealization

end

end Erdos390.WholePaper
