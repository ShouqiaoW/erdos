import Erdos390.WholePaper.BankPaperCanonicalPostHfitSlackConnector
import Erdos390.WholePaper.BankPaperCanonicalSignedGuardResidual

/-!
# Exact selector identification for the four-term signed rough residual

The quantitative signed-residual file defines the four scalar terms and
proves their bounds, while the selector handoff defines the literal
target-minus-selector valuation deficit.  This file isolates the finite
identity still needed to connect them.

There are two independent finite ledgers:

* the target ledger expands the charged selector target as the raw upper
  valuation, less fixed exceptional factors and the bank base, with
  exceptional donors restored;
* the selector ledger expands the concrete guarded source as the raw lower
  valuation, less exceptional and nonexceptional deleted coordinates, plus
  the aggregate row correction.

The target ledger is proved below in the medium-prime range from the existing
charge divisibility.  The selector ledger remains a named source-level input:
the current implementation uses guarded postcharge corrections, whereas the
available aggregate correction scalar is defined using raw rows and raw
broad pools, and no global valuation reindexing theorem identifies them.

Once the two ledgers are available, the exact four signs follow by ring
algebra.  A final transport theorem records the additional, already-defined
valuation moment introduced by structured smooth placement.  Thus the
remaining gap is localized without assuming the desired final equality.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit

noncomputable section

namespace BankPaperRealization

/-! ## Concrete raw and source ledgers -/

/-- The raw primewise residual before exceptional deletion, row correction,
and numerical guards. -/
def roughCanonicalRawSignedValuationResidual
    (n h K : Nat) (rawWeight : Nat -> Real) (p : Nat) : Real :=
  (∑ a ∈ roughUpperBlock n h, (a.factorization p : Real)) -
    ∑ a ∈ roughRawCandidateSet n h K,
      rawWeight a * (a.factorization p : Real)

/-- Exact charged-target expansion required by the paper's sign ledger. -/
def BankPaperCanonicalSignedResidualTargetLedger
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (p : Nat) : Prop :=
  ((certificate.selectorTailTarget R
      (R.paperFixedExceptionalFactors deltaStar)).factorization p : Real) =
    (∑ a ∈ roughUpperBlock n (upperTailLength c n),
      (a.factorization p : Real)) -
    (∑ a ∈ paperExceptionalUpperFactors n (upperTailLength c n) deltaStar,
      (a.factorization p : Real)) +
    (∑ a ∈ R.roughCanonicalExceptionalDonorSet deltaStar,
      (a.factorization p : Real)) -
    ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)

/-- Exact guarded-source expansion required by the paper's sign ledger.

This is the one genuinely missing finite reindexing.  Its right-hand side
uses the already-defined raw lower family, signed exceptional lower family,
nonexceptional guard-deletion family, and aggregate *raw* row correction. -/
def BankPaperCanonicalSignedResidualSelectorLedger
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat) : Prop :=
  (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      selector a * (a.factorization p : Real)) =
    (∑ a ∈ roughRawCandidateSet n (upperTailLength c n) K,
      roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell a * (a.factorization p : Real)) -
    (∑ a ∈ roughCanonicalExceptionalRawLowerSet n
        (upperTailLength c n) K deltaStar,
      roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell a * (a.factorization p : Real)) -
    (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
        deltaStar K,
      roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell a * (a.factorization p : Real)) +
    roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) K deltaStar alpha beta ell p

/-! ## Exact reduction of the source ledger -/

/-- The guarded candidates whose complete rough row is not exceptional. -/
def roughCanonicalNonexceptionalGuardedCandidateSet
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (K : Nat) : Finset Nat := by
  classical
  exact
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K).filter
      fun a =>
        ¬ RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a)

@[simp]
theorem mem_roughCanonicalNonexceptionalGuardedCandidateSet
    {c : Real} {depth n h K a : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) :
    a ∈ R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
        deltaStar K ↔
      a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
        ¬ RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) := by
  classical
  simp only [roughCanonicalNonexceptionalGuardedCandidateSet,
    Finset.mem_filter]

/-- After exceptional raw rows and nonexceptional guard deletions are
removed, the remaining raw mass is exactly the mass on surviving
nonexceptional guarded candidates.  This is the complete set-theoretic
reindex behind the first three source-ledger terms. -/
theorem sum_raw_sub_exceptional_sub_nonexceptionalDeleted_eq_guardedNonexceptional
    {c : Real} {depth n h K : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (weight : Nat -> Real) :
    (∑ a ∈ roughRawCandidateSet n h K, weight a) -
        (∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
          weight a) -
        (∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
          deltaStar K, weight a) =
      ∑ a ∈ R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
        deltaStar K, weight a := by
  classical
  let nonexceptionalRaw :=
    (roughRawCandidateSet n h K).filter fun a =>
      ¬ RoughCanonicalExceptionalLabel n deltaStar
        (completeRoughLabel (yNat n) a)
  have hexceptionalDisjoint :
      Disjoint
        (roughCanonicalExceptionalRawLowerSet n h K deltaStar)
        nonexceptionalRaw := by
    rw [Finset.disjoint_left]
    intro a haExceptional haNonexceptional
    have haExceptional' :=
      (mem_roughCanonicalExceptionalRawLowerSet.mp haExceptional).2
    have haNonexceptional' := (Finset.mem_filter.mp haNonexceptional).2
    exact haNonexceptional' haExceptional'
  have hexceptionalUnion :
      roughCanonicalExceptionalRawLowerSet n h K deltaStar ∪
          nonexceptionalRaw =
        roughRawCandidateSet n h K := by
    ext a
    simp only [roughCanonicalExceptionalRawLowerSet, nonexceptionalRaw,
      Finset.mem_union, Finset.mem_filter]
    by_cases hlabel :
        RoughCanonicalExceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) a) <;>
      simp_all
  have hguardedDeletedDisjoint :
      Disjoint
        (R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
          deltaStar K)
        (R.roughCanonicalNonexceptionalGuardDeletedSet certificate
          deltaStar K) := by
    rw [Finset.disjoint_left]
    intro a haGuarded haDeleted
    have haGuarded' :=
      (R.mem_roughCanonicalNonexceptionalGuardedCandidateSet
        certificate deltaStar).1 haGuarded
    have haDeleted' :=
      (R.mem_roughCanonicalNonexceptionalGuardDeletedSet
        certificate deltaStar).1 haDeleted
    exact
      (Finset.disjoint_left.mp
        (R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
          certificate deltaStar K))
        haGuarded'.1 haDeleted'.2.1
  have hguardedDeletedUnion :
      R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
            deltaStar K ∪
          R.roughCanonicalNonexceptionalGuardDeletedSet certificate
            deltaStar K =
        nonexceptionalRaw := by
    ext a
    simp only [roughCanonicalNonexceptionalGuardedCandidateSet,
      roughCanonicalGuardedCandidateSet,
      roughCanonicalNonexceptionalGuardDeletedSet, nonexceptionalRaw,
      Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff,
      Finset.mem_inter]
    by_cases hguard :
        a ∈ R.roughCanonicalGuardSet certificate deltaStar <;>
      simp_all
  have hrawSum :
      (∑ a ∈ roughRawCandidateSet n h K, weight a) =
        (∑ a ∈ roughCanonicalExceptionalRawLowerSet n h K deltaStar,
          weight a) +
        ∑ a ∈ nonexceptionalRaw, weight a := by
    rw [← Finset.sum_union hexceptionalDisjoint, hexceptionalUnion]
  have hnonexceptionalSum :
      (∑ a ∈ nonexceptionalRaw, weight a) =
        (∑ a ∈ R.roughCanonicalNonexceptionalGuardedCandidateSet
          certificate deltaStar K, weight a) +
        ∑ a ∈ R.roughCanonicalNonexceptionalGuardDeletedSet certificate
          deltaStar K, weight a := by
    rw [← Finset.sum_union hguardedDeletedDisjoint,
      hguardedDeletedUnion]
  rw [hrawSum, hnonexceptionalSum]
  ring

/-- The actual source contribution beyond surviving nonexceptional raw
weight.  It includes the smooth structured source, exceptional rows, and
the correction installed on every nonsmooth guarded row. -/
def roughCanonicalSourceValuationCorrectionMoment
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat) : Real :=
  (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      selector a * (a.factorization p : Real)) -
    ∑ a ∈ R.roughCanonicalNonexceptionalGuardedCandidateSet certificate
        deltaStar K,
      roughHeadCompatibleRawWeight W n (upperTailLength c n) K
          alpha beta ell a * (a.factorization p : Real)

/-- The exact error made by replacing the correction moment of a supplied
source with the existing aggregate raw-pool correction. -/
def roughCanonicalSourceRawCorrectionValuationDefect
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat) : Real :=
  roughCanonicalSourceValuationCorrectionMoment
      (W := W) (K := K)
      R certificate deltaStar alpha beta ell selector p -
    roughCanonicalAggregateRawRowCorrection W n
      (upperTailLength c n) K deltaStar alpha beta ell p

/-- The opaque-looking source ledger is equivalent to one exact and fully
visible finite equality: the source's correction moment must equal the
aggregate *raw-pool* correction moment. -/
theorem bankPaperCanonicalSignedResidualSelectorLedger_iff_correctionMoment_eq_raw
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat) :
    BankPaperCanonicalSignedResidualSelectorLedger
        (W := W) (K := K)
        R certificate deltaStar alpha beta ell selector p ↔
      roughCanonicalSourceValuationCorrectionMoment
          (W := W) (K := K)
          R certificate deltaStar alpha beta ell selector p =
        roughCanonicalAggregateRawRowCorrection W n
          (upperTailLength c n) K deltaStar alpha beta ell p := by
  have hbase :=
    sum_raw_sub_exceptional_sub_nonexceptionalDeleted_eq_guardedNonexceptional
      (n := n) (h := upperTailLength c n) (K := K)
      R certificate deltaStar
        (fun a =>
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell a * (a.factorization p : Real))
  unfold BankPaperCanonicalSignedResidualSelectorLedger
  unfold roughCanonicalSourceValuationCorrectionMoment
  rw [hbase]
  constructor <;> intro h <;> linarith

/-- Equivalently, the complete source ledger says exactly that the explicit
guarded-to-raw correction defect vanishes. -/
theorem bankPaperCanonicalSignedResidualSelectorLedger_iff_sourceRawCorrectionDefect_eq_zero
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat) :
    BankPaperCanonicalSignedResidualSelectorLedger
        (W := W) (K := K)
        R certificate deltaStar alpha beta ell selector p ↔
      roughCanonicalSourceRawCorrectionValuationDefect
          (W := W) (K := K)
          R certificate deltaStar alpha beta ell selector p = 0 := by
  rw [
    bankPaperCanonicalSignedResidualSelectorLedger_iff_correctionMoment_eq_raw]
  unfold roughCanonicalSourceRawCorrectionValuationDefect
  constructor <;> intro h <;> linarith

/-! ## What the guarded postcharge correction actually contributes -/

/-- A constant-pool correction against an arbitrary scalar weight contributes
the original weighted sum plus the correction density times the pool's
weighted sum.  Unlike the unweighted target theorem, this needs no
nonemptiness assumption. -/
theorem sum_bankPaperConstantPoolCorrection_mul_eq
    (row pool : Finset Nat) (x : Nat -> Real) (target : Real)
    (weight : Nat -> Real) (hpool : pool ⊆ row) :
    (∑ a ∈ row,
        bankPaperConstantPoolCorrection row pool x target a * weight a) =
      (∑ a ∈ row, x a * weight a) +
        bankPaperConstantPoolCorrectionDensity row pool x target *
          ∑ a ∈ pool, weight a := by
  classical
  have hfilter :
      row.filter (fun a => a ∈ pool) = pool := by
    ext a
    simp only [Finset.mem_filter]
    constructor
    · exact fun ha => ha.2
    · exact fun ha => ⟨hpool ha, ha⟩
  calc
    (∑ a ∈ row,
        bankPaperConstantPoolCorrection row pool x target a * weight a) =
        ∑ a ∈ row,
          (x a * weight a +
            if a ∈ pool then
              bankPaperConstantPoolCorrectionDensity row pool x target *
                weight a
            else 0) := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases haPool : a ∈ pool
      · simp [bankPaperConstantPoolCorrection, haPool, add_mul]
      · simp [bankPaperConstantPoolCorrection, haPool]
    _ = (∑ a ∈ row, x a * weight a) +
        ∑ a ∈ row,
          if a ∈ pool then
            bankPaperConstantPoolCorrectionDensity row pool x target *
              weight a
          else 0 := by
      rw [Finset.sum_add_distrib]
    _ = (∑ a ∈ row, x a * weight a) +
        ∑ a ∈ pool,
          bankPaperConstantPoolCorrectionDensity row pool x target *
            weight a := by
      apply congrArg
        (fun z : Real => (∑ a ∈ row, x a * weight a) + z)
      rw [← Finset.sum_filter, hfilter]
    _ = (∑ a ∈ row, x a * weight a) +
        bankPaperConstantPoolCorrectionDensity row pool x target *
          ∑ a ∈ pool, weight a := by
      rw [Finset.mul_sum]

/-- Exact numerator of the guarded postcharge density.  The local finite
ledger shows why it is not definitionally the raw density: fixed/base
charges and raw weights on guard-deleted coordinates alter the numerator,
while deleting guards can also alter the denominator. -/
theorem roughCanonicalGuardedPostchargeCorrectionDensity_eq_rawLedger
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
            alpha beta ell) -
        (completeLabelMultiplicity (yNat n)
          (R.paperFixedExceptionalFactors deltaStar) label : Real) -
        (completeLabelMultiplicity (yNat n)
          R.prechargeBaseState label : Real) +
        ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
            K label,
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell a) /
      ((R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label).card : Real) := by
  let rawWeight :=
    roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta ell
  have hledger :=
    R.roughCanonicalGuardLocalDiscrepancyLedger certificate deltaStar
      K label rawWeight
  have hpost :
      R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
          K label rawWeight =
        roughCanonicalRawRowDiscrepancy n (upperTailLength c n)
            K label rawWeight -
          (completeLabelMultiplicity (yNat n)
            (R.paperFixedExceptionalFactors deltaStar) label : Real) -
          (completeLabelMultiplicity (yNat n)
            R.prechargeBaseState label : Real) +
          ∑ a ∈ R.roughCanonicalGuardDeletedRow certificate deltaStar
              K label,
            rawWeight a := by
    linarith only [hledger]
  unfold roughCanonicalGuardedPostchargeCorrectionDensity
  unfold bankPaperConstantPoolCorrectionDensity
  change
    R.roughCanonicalPostchargeRowDiscrepancy certificate deltaStar
        K label rawWeight /
          ((R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K label).card : Real) =
      _
  rw [hpost]

/-- The valuation contribution of one actual guarded corrected row. -/
theorem sum_guardedPostchargeRowCorrectedWeight_mul_factorization_eq
    {c : Real} {depth n W K label p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta ell a *
        (a.factorization p : Real)) =
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell a * (a.factorization p : Real)) +
      R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
          deltaStar W K label alpha beta ell *
        ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K label,
          (a.factorization p : Real) := by
  simpa only [roughCanonicalGuardedPostchargeRowCorrectedWeight,
    roughCanonicalGuardedPostchargeCorrectionDensity] using
    (sum_bankPaperConstantPoolCorrection_mul_eq
      (R.roughCanonicalGuardedRow certificate deltaStar K label)
      (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label)
      (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
        alpha beta ell)
      (R.roughCanonicalPostchargeRowTarget deltaStar label)
      (fun a => (a.factorization p : Real))
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar W K label))

/-- The correction moment installed by the implemented postcharge selector
on active nonsmooth rows.  Its guarded pools and guarded densities are
deliberately visible; this is not the raw correction used by the existing
quantitative residual bound. -/
def roughCanonicalAggregateGuardedPostchargeRowCorrection
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta ell : Real)
    (p : Nat) : Real :=
  ∑ label ∈ roughCanonicalActiveRawCorrectionLabels n
      (upperTailLength c n) K deltaStar,
    R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
        deltaStar W K label alpha beta ell *
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar W K label,
        (a.factorization p : Real)

/-- On an entire active nonexceptional guarded row—not only its broad
correction pool—the implemented global source is exactly the guarded
postcharge corrected weight. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_nonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha beta B.L a := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hactive.1 (haLabel.symm.trans haSmoothLabel)
  have haNotOne :
      completeRoughLabel (yNat B.sampleData.n) a ≠ 1 := by
    intro haOne
    exact hactive.1 (haLabel.symm.trans haOne)
  have hnonexceptional :
      ¬ RoughCanonicalExceptionalLabel
        B.sampleData.n deltaStar label :=
    not_lt_of_ge hactive.2
  unfold bankPaperCanonicalGlobalCorrectedSourceSelector
  unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
  rw [if_neg hnotSmoothPool]
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelector
  rw [if_neg haNotOne, haLabel, if_neg hnonexceptional]

/-- On an exceptional nonsmooth guarded row, the implemented global source
is pointwise zero. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_exceptionalNonsmoothRow
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K label : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hlabel : label ≠ 1)
    (hexceptional :
      RoughCanonicalExceptionalLabel B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a = 0 := by
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp ha).2
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    have haSmoothRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth
    have haSmoothLabel :
        completeRoughLabel (yNat B.sampleData.n) a = 1 :=
      (mem_completeRoughRowFiber.mp haSmoothRow).2
    exact hlabel (haLabel.symm.trans haSmoothLabel)
  have haNotOne :
      completeRoughLabel (yNat B.sampleData.n) a ≠ 1 := by
    intro haOne
    exact hlabel (haLabel.symm.trans haOne)
  unfold bankPaperCanonicalGlobalCorrectedSourceSelector
  unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
  rw [if_neg hnotSmoothPool]
  unfold bankPaperCanonicalGlobalCorrectedOutsideSelector
  rw [if_neg haNotOne, haLabel, if_pos hexceptional]

/-! ## The charged target ledger is already derivable -/

/-- The literal exceptional upper set is the disjoint union of the retained
fixed exceptional factors and the exceptional designated donors. -/
theorem paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
    {n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (deltaStar : Real) :
    paperExceptionalUpperFactors n h deltaStar =
      R.paperFixedExceptionalFactors deltaStar ∪
        R.roughCanonicalExceptionalDonorSet deltaStar := by
  ext a
  constructor
  · intro ha
    by_cases hdonor : a ∈ R.prechargeDonorSet
    · apply Finset.mem_union_right
      exact (R.mem_roughCanonicalExceptionalDonorSet).2
        ⟨hdonor, (mem_paperExceptionalUpperFactors.mp ha).2⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨ha, hdonor⟩
  · intro ha
    rcases Finset.mem_union.mp ha with hfixed | hdonor
    · exact (Finset.mem_sdiff.mp hfixed).1
    · have hdonorData :=
        (R.mem_roughCanonicalExceptionalDonorSet).1 hdonor
      have htail := R.prechargeDonorSet_subset_tail hdonorData.1
      apply mem_paperExceptionalUpperFactors.mpr
      constructor
      · simpa only [roughUpperBlock, upperEndpoint] using htail
      · exact hdonorData.2

/-- At a medium prime the central anchor divisor has zero valuation, and
the two quotient charges expand to the exact target ledger. -/
theorem bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
    {c : Real} {depth n W p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hprefix : 2 * depth + 1 <= W)
    (hp : p.Prime) (hWp : W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget) :
    BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p := by
  let h := upperTailLength c n
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let exceptional := paperExceptionalUpperFactors n h deltaStar
  let exceptionalDonors :=
    R.roughCanonicalExceptionalDonorSet deltaStar
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  let charge := R.selectorTailCharge fixed
  let target := certificate.selectorTailTarget R fixed
  have hchargeDvd' :
      charge ∣ certificate.prechargedTailTarget := by
    simpa only [charge, fixed] using hchargeDvd
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have htail := R.paperFixedExceptionalFactors_subset_tail deltaStar ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  have hbasePositive : 0 < R.prechargeBaseStateProduct := by
    unfold prechargeBaseStateProduct
    apply Finset.prod_pos
    intro a ha
    have hinterval := R.prechargeBaseState_subset_factorInterval ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hfixedProdPositive : 0 < fixed.prod id := by
    apply Finset.prod_pos
    intro a ha
    simpa only [id_eq] using hfixedPositive a ha
  have hchargePositive : 0 < charge := by
    dsimp only [charge]
    exact R.selectorTailCharge_pos fixed hfixedPositive
  have htargetPositive : 0 < target := by
    dsimp only [target]
    exact certificate.selectorTailTarget_pos
      R fixed hfixedPositive hchargeDvd'
  have hdivisorPositive : 0 < divisor := by
    dsimp only [divisor]
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have hprechargedPositive : 0 < certificate.prechargedTailTarget :=
    certificate.prechargedTailTarget_pos
  have hdivisorZero : divisor.factorization p = 0 := by
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpDvd
    have hpSupport := certificate.divisor_prime_support p hp
      (by simpa only [divisor] using hpDvd)
    have hpLe : p <= 2 * depth + 1 :=
      (mem_primesUpTo.mp hpSupport).2
    omega
  have hprechargedFactorization :
      certificate.prechargedTailTarget.factorization p =
        (centralTailProduct n h).factorization p := by
    have hproduct := congrArg (fun z : Nat => z.factorization p)
      certificate.prechargedTailTarget_mul_centralAnchorDivisor
    change
      (certificate.prechargedTailTarget * divisor).factorization p =
        (centralTailProduct n h).factorization p at hproduct
    rw [Nat.factorization_mul hprechargedPositive.ne'
      hdivisorPositive.ne', Finsupp.add_apply, hdivisorZero,
      add_zero] at hproduct
    exact hproduct
  have htargetFactorization :
      target.factorization p + charge.factorization p =
        certificate.prechargedTailTarget.factorization p := by
    have hproduct := congrArg (fun z : Nat => z.factorization p)
      (certificate.selectorTailTarget_mul_selectorTailCharge
        R fixed hchargeDvd')
    change
      (target * charge).factorization p =
        certificate.prechargedTailTarget.factorization p at hproduct
    simpa only [Nat.factorization_mul htargetPositive.ne'
      hchargePositive.ne', Finsupp.add_apply] using hproduct
  have hchargeFactorization :
      charge.factorization p =
        (fixed.prod id).factorization p +
          R.prechargeBaseStateProduct.factorization p := by
    dsimp only [charge]
    rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct,
      Nat.factorization_mul hfixedProdPositive.ne'
        hbasePositive.ne', Finsupp.add_apply]
  have htailFactorization :
      ((centralTailProduct n h).factorization p : Real) =
        ∑ a ∈ roughUpperBlock n h, (a.factorization p : Real) := by
    have hnat :
        (centralTailProduct n h).factorization p =
          ∑ a ∈ roughUpperBlock n h, a.factorization p := by
      unfold centralTailProduct roughUpperBlock factorInterval
      rw [Nat.factorization_prod_apply]
      · simp only [id_eq]
      · intro a ha
        exact (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp ha).1).ne'
    exact_mod_cast hnat
  have hfixedFactorization :
      ((fixed.prod id).factorization p : Real) =
        ∑ a ∈ fixed, (a.factorization p : Real) := by
    have hnat :
        (fixed.prod id).factorization p =
          ∑ a ∈ fixed, a.factorization p :=
      Nat.factorization_prod_apply
        (fun a ha => (hfixedPositive a ha).ne')
    exact_mod_cast hnat
  have hbaseFactorization :
      (R.prechargeBaseStateProduct.factorization p : Real) =
        ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real) := by
    have hnat :
        R.prechargeBaseStateProduct.factorization p =
          ∑ a ∈ R.prechargeBaseState, a.factorization p := by
      unfold prechargeBaseStateProduct
      rw [Nat.factorization_prod_apply]
      · simp only [id_eq]
      · intro a ha
        have hinterval := R.prechargeBaseState_subset_factorInterval ha
        exact (Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1).ne'
    exact_mod_cast hnat
  have hfixedExceptionalDisjoint :
      Disjoint fixed exceptionalDonors := by
    rw [Finset.disjoint_left]
    intro a hfixedA hexceptionalDonor
    have hdonorA :=
      ((R.mem_roughCanonicalExceptionalDonorSet).1
        hexceptionalDonor).1
    exact (Finset.disjoint_left.mp
      (R.paperFixedExceptionalFactors_disjoint_prechargeDonorSet
        deltaStar)) hfixedA hdonorA
  have hexceptionalPartition :
      exceptional = fixed ∪ exceptionalDonors := by
    dsimp only [exceptional, fixed, exceptionalDonors]
    exact
      paperExceptionalUpperFactors_eq_fixed_union_exceptionalDonors
        R deltaStar
  have hexceptionalSum :
      (∑ a ∈ exceptional, (a.factorization p : Real)) =
        (∑ a ∈ fixed, (a.factorization p : Real)) +
          ∑ a ∈ exceptionalDonors, (a.factorization p : Real) := by
    rw [hexceptionalPartition,
      Finset.sum_union hfixedExceptionalDisjoint]
  unfold BankPaperCanonicalSignedResidualTargetLedger
  change
    (target.factorization p : Real) =
      (∑ a ∈ roughUpperBlock n h, (a.factorization p : Real)) -
      (∑ a ∈ exceptional, (a.factorization p : Real)) +
      (∑ a ∈ exceptionalDonors, (a.factorization p : Real)) -
      ∑ a ∈ R.prechargeBaseState, (a.factorization p : Real)
  have htargetFactorizationReal :
      (target.factorization p : Real) +
          (charge.factorization p : Real) =
        (certificate.prechargedTailTarget.factorization p : Real) := by
    exact_mod_cast htargetFactorization
  have hchargeFactorizationReal :
      (charge.factorization p : Real) =
        ((fixed.prod id).factorization p : Real) +
          (R.prechargeBaseStateProduct.factorization p : Real) := by
    exact_mod_cast hchargeFactorization
  rw [hprechargedFactorization] at htargetFactorizationReal
  rw [htailFactorization, hchargeFactorizationReal,
    hfixedFactorization, hbaseFactorization] at htargetFactorizationReal
  rw [hexceptionalSum]
  linarith only [htargetFactorizationReal]

/-! ## Four-term identification and structured transport -/

/-- The two explicit finite ledgers imply the paper's exact four-term
signed-residual identity for the literal canonical selector deficit. -/
theorem bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hselector : BankPaperCanonicalSignedResidualSelectorLedger
      (W := W) (K := K) R certificate deltaStar alpha beta ell selector p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector p =
      roughCanonicalCompleteSignedResidual
        (roughCanonicalRawSignedValuationResidual n
          (upperTailLength c n) K
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) p)
        (roughCanonicalSignedExceptionalResidual n
          (upperTailLength c n) K deltaStar
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) p)
        (roughCanonicalAggregateRawRowCorrection W n
          (upperTailLength c n) K deltaStar alpha beta ell p)
        (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) p) := by
  unfold BankPaperCanonicalSignedResidualTargetLedger at htarget
  unfold BankPaperCanonicalSignedResidualSelectorLedger at hselector
  unfold bankPaperCanonicalSelectorValuationDeficit
  unfold roughCanonicalCompleteSignedResidual
  unfold roughCanonicalRawSignedValuationResidual
  unfold roughCanonicalSignedExceptionalResidual
  unfold roughCanonicalAggregateGuardResidual
  rw [htarget, hselector]
  ring

/-- Without assuming the disputed guarded-to-raw reindex, the literal
selector deficit is the four-term paper residual minus one explicit finite
source-correction defect.  This is the unconditional exact replacement for
the preceding conditional identity. -/
theorem bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual_sub_sourceDefect
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real) (p : Nat)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector p =
      roughCanonicalCompleteSignedResidual
          (roughCanonicalRawSignedValuationResidual n
            (upperTailLength c n) K
            (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell) p)
          (roughCanonicalSignedExceptionalResidual n
            (upperTailLength c n) K deltaStar
            (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell) p)
          (roughCanonicalAggregateRawRowCorrection W n
            (upperTailLength c n) K deltaStar alpha beta ell p)
          (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
            (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell) p) -
        roughCanonicalSourceRawCorrectionValuationDefect
          (W := W) (K := K)
          R certificate deltaStar alpha beta ell selector p := by
  have hbase :=
    sum_raw_sub_exceptional_sub_nonexceptionalDeleted_eq_guardedNonexceptional
      (n := n) (h := upperTailLength c n) (K := K)
      R certificate deltaStar
        (fun a =>
          roughHeadCompatibleRawWeight W n (upperTailLength c n) K
              alpha beta ell a * (a.factorization p : Real))
  unfold BankPaperCanonicalSignedResidualTargetLedger at htarget
  unfold bankPaperCanonicalSelectorValuationDeficit
  unfold roughCanonicalCompleteSignedResidual
  unfold roughCanonicalRawSignedValuationResidual
  unfold roughCanonicalSignedExceptionalResidual
  unfold roughCanonicalAggregateGuardResidual
  unfold roughCanonicalSourceRawCorrectionValuationDefect
  unfold roughCanonicalSourceValuationCorrectionMoment
  rw [htarget]
  linarith only [hbase]

/-- In the medium-prime range, charge divisibility discharges the target
ledger automatically.  Thus the guarded-source ledger is the only new
finite identity required for the literal selector deficit. -/
theorem bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual_of_chargeDvd
    {c : Real} {depth n W K p : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta ell : Real)
    (selector : Nat -> Real)
    (hprefix : 2 * depth + 1 <= W)
    (hp : p.Prime) (hWp : W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hselector : BankPaperCanonicalSignedResidualSelectorLedger
      (W := W) (K := K) R certificate deltaStar alpha beta ell selector p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector p =
      roughCanonicalCompleteSignedResidual
        (roughCanonicalRawSignedValuationResidual n
          (upperTailLength c n) K
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) p)
        (roughCanonicalSignedExceptionalResidual n
          (upperTailLength c n) K deltaStar
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) p)
        (roughCanonicalAggregateRawRowCorrection W n
          (upperTailLength c n) K deltaStar alpha beta ell p)
        (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
          (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
            alpha beta ell) p) := by
  exact bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual
    (W := W) (K := K)
      R certificate deltaStar alpha beta ell selector p
      (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
        (W := W) R certificate deltaStar hprefix hp hWp hchargeDvd)
      hselector

/-- Structured smooth placement changes the signed-residual identity by
exactly its already-defined valuation moment. -/
theorem bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hselector : BankPaperCanonicalSignedResidualSelectorLedger
      (W := B.sampleData.W) (K := K)
        R certificate deltaStar alpha beta ell baseSelector p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
          (K := K) B R certificate deltaStar betaProt
            baseSelector activeSeed) p =
      roughCanonicalCompleteSignedResidual
          (roughCanonicalRawSignedValuationResidual B.sampleData.n
            (upperTailLength c B.sampleData.n) K
            (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha beta ell) p)
          (roughCanonicalSignedExceptionalResidual B.sampleData.n
            (upperTailLength c B.sampleData.n) K deltaStar
            (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha beta ell) p)
          (roughCanonicalAggregateRawRowCorrection B.sampleData.W
            B.sampleData.n (upperTailLength c B.sampleData.n) K
              deltaStar alpha beta ell p)
          (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
            (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha beta ell) p) -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K) B R certificate deltaStar betaProt
            baseSelector activeSeed p := by
  rw [
    bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        baseSelector activeSeed hactiveSmooth p,
    bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual
      (W := B.sampleData.W) (K := K)
        R certificate deltaStar alpha beta ell baseSelector p
        htarget hselector]

/-- Unconditional structured-placement transport with the exact source
defect kept visible. -/
theorem bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
          (K := K) B R certificate deltaStar betaProt
            baseSelector activeSeed) p =
      roughCanonicalCompleteSignedResidual
          (roughCanonicalRawSignedValuationResidual B.sampleData.n
            (upperTailLength c B.sampleData.n) K
            (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha beta ell) p)
          (roughCanonicalSignedExceptionalResidual B.sampleData.n
            (upperTailLength c B.sampleData.n) K deltaStar
            (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha beta ell) p)
          (roughCanonicalAggregateRawRowCorrection B.sampleData.W
            B.sampleData.n (upperTailLength c B.sampleData.n) K
              deltaStar alpha beta ell p)
          (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
            (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
              (upperTailLength c B.sampleData.n) K alpha beta ell) p) -
        roughCanonicalSourceRawCorrectionValuationDefect
          (W := B.sampleData.W) (K := K)
          R certificate deltaStar alpha beta ell baseSelector p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K) B R certificate deltaStar betaProt
            baseSelector activeSeed p := by
  rw [
    bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        baseSelector activeSeed hactiveSmooth p,
    bankPaperCanonicalSelectorValuationDeficit_eq_completeSignedResidual_sub_sourceDefect
      (W := B.sampleData.W) (K := K)
      R certificate deltaStar alpha beta ell baseSelector p htarget]

/-- If the structured placement has zero moment at a coordinate, the
pre-selector deficit is literally the four-term complete residual there. -/
theorem bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_of_moment_eq_zero
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta ell : Real)
    (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (p : Nat)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hselector : BankPaperCanonicalSignedResidualSelectorLedger
      (W := B.sampleData.W) (K := K)
        R certificate deltaStar alpha beta ell baseSelector p)
    (hmoment :
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
          baseSelector activeSeed p = 0) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
          (K := K) B R certificate deltaStar betaProt
            baseSelector activeSeed) p =
      roughCanonicalCompleteSignedResidual
        (roughCanonicalRawSignedValuationResidual B.sampleData.n
          (upperTailLength c B.sampleData.n) K
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha beta ell) p)
        (roughCanonicalSignedExceptionalResidual B.sampleData.n
          (upperTailLength c B.sampleData.n) K deltaStar
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha beta ell) p)
        (roughCanonicalAggregateRawRowCorrection B.sampleData.W
          B.sampleData.n (upperTailLength c B.sampleData.n) K
            deltaStar alpha beta ell p)
        (R.roughCanonicalAggregateGuardResidual certificate deltaStar K
          (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
            (upperTailLength c B.sampleData.n) K alpha beta ell) p) := by
  rw [
    bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
      (K := K) B R certificate deltaStar betaProt alpha beta ell
        baseSelector activeSeed p hactiveSmooth htarget hselector,
    hmoment, sub_zero]

/-! ## The literal Post-Hfit pre-selector -/

/-- The four concrete signed terms at the balanced Post-Hfit parameters. -/
def roughCanonicalPostHfitCompleteSignedResidual
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
    (deltaStar betaProt betaAct : Real) (p : Nat) : Real :=
  roughCanonicalCompleteSignedResidual
    (roughCanonicalRawSignedValuationResidual B.sampleData.n
      (upperTailLength c B.sampleData.n) (K0 + 1)
      (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) (K0 + 1)
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L) p)
    (roughCanonicalSignedExceptionalResidual B.sampleData.n
      (upperTailLength c B.sampleData.n) (K0 + 1) deltaStar
      (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) (K0 + 1)
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L) p)
    (roughCanonicalAggregateRawRowCorrection B.sampleData.W
      B.sampleData.n (upperTailLength c B.sampleData.n) (K0 + 1)
      deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L p)
    (R.roughCanonicalAggregateGuardResidual certificate deltaStar
      (K0 + 1)
      (roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) (K0 + 1)
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L) p)

/-- The correction moment of the actual balanced Post-Hfit global source,
measured relative to surviving nonexceptional raw weight. -/
def roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment
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
  roughCanonicalSourceValuationCorrectionMoment
    (W := B.sampleData.W) (K := K0 + 1)
    R certificate deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      p

/-- The literal finite defect between the implemented Post-Hfit source
correction moment and the raw-pool correction used in the paper residual. -/
def roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect
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
  roughCanonicalSourceRawCorrectionValuationDefect
    (W := B.sampleData.W) (K := K0 + 1)
    R certificate deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      p

/-- The first exact reindex needed by the implementation: all smooth and
exceptional source contributions, together with the nonsmooth corrected
rows, must reduce to the correction moment actually installed on guarded
postcharge pools.  This is not a consequence of row-sum integrality. -/
def BankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex
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
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) : Prop :=
  roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment
      B K0 R certificate deltaStar betaProt betaAct oldSeed p =
    R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
      deltaStar B.sampleData.W (K0 + 1)
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L p

/-- The second exact reindex needed by the current quantitative bound:
the correction moment on guarded postcharge pools must equal the older
pre-guard correction moment on raw pools.  The displayed density formula
above shows the finite numerator and denominator changes that must be
accounted for in any proof of this equality. -/
def BankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex
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
    (deltaStar betaProt betaAct : Real) (p : Nat) : Prop :=
  R.roughCanonicalAggregateGuardedPostchargeRowCorrection certificate
      deltaStar B.sampleData.W (K0 + 1)
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L p =
    roughCanonicalAggregateRawRowCorrection B.sampleData.W
      B.sampleData.n (upperTailLength c B.sampleData.n) (K0 + 1)
      deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L p

/-- The complete global source reindexing, specialized to the actual
balanced Post-Hfit source selector.  The preceding two propositions expose
its two independent finite components. -/
def BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
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
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat) : Prop :=
  BankPaperCanonicalSignedResidualSelectorLedger
    (W := B.sampleData.W) (K := K0 + 1)
    R certificate deltaStar
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) B.L
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      p

/-- Exact characterization of the remaining Post-Hfit source ledger as a
single finite correction-moment equality. -/
theorem bankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger_iff_correctionMoment_eq_raw
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
    BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
        B K0 R certificate deltaStar betaProt betaAct oldSeed p ↔
      roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment
          B K0 R certificate deltaStar betaProt betaAct oldSeed p =
        roughCanonicalAggregateRawRowCorrection B.sampleData.W
          B.sampleData.n (upperTailLength c B.sampleData.n) (K0 + 1)
          deltaStar
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L p := by
  unfold
    BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
  unfold roughCanonicalPostHfitGlobalSourceValuationCorrectionMoment
  exact
    bankPaperCanonicalSignedResidualSelectorLedger_iff_correctionMoment_eq_raw
      (W := B.sampleData.W) (K := K0 + 1)
      R certificate deltaStar
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        p

/-- The two independently visible finite reindexes imply the complete
Post-Hfit source ledger. -/
theorem bankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger_of_reindexes
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
    (oldSeed : B.sampleData.Sample -> Real) (p : Nat)
    (hsource :
      BankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex
        B K0 R certificate deltaStar betaProt betaAct oldSeed p)
    (hcorrection :
      BankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex
        B K0 R certificate deltaStar betaProt betaAct p) :
    BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
      B K0 R certificate deltaStar betaProt betaAct oldSeed p := by
  apply
    (bankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger_iff_correctionMoment_eq_raw
      B K0 R certificate deltaStar betaProt betaAct oldSeed p).2
  unfold
    BankPaperCanonicalPostHfitSourceToGuardedCorrectionValuationReindex
    at hsource
  unfold
    BankPaperCanonicalPostHfitGuardedToRawCorrectionValuationReindex
    at hcorrection
  exact hsource.trans hcorrection

/-- Unconditional exact expansion of the literal Post-Hfit structured
pre-selector.  The additional source defect is the precise price of using
the implemented guarded postcharge source with the existing raw-pool
correction bound. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
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
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p =
      roughCanonicalPostHfitCompleteSignedResidual
          B K0 R certificate deltaStar betaProt betaAct p -
        roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect
          B K0 R certificate deltaStar betaProt betaAct oldSeed p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p := by
  simpa only [bankPaperCanonicalPostHfitStructuredPreSelector,
    roughCanonicalPostHfitCompleteSignedResidual,
    roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect] using
    (bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
      (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass)
        p hactiveSmooth htarget)

/-- Medium-prime charge divisibility supplies the target side of the
unconditional defect formula. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment_of_chargeDvd
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
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hp : p.Prime) (hWp : B.sampleData.W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p =
      roughCanonicalPostHfitCompleteSignedResidual
          B K0 R certificate deltaStar betaProt betaAct p -
        roughCanonicalPostHfitGlobalSourceRawCorrectionValuationDefect
          B K0 R certificate deltaStar betaProt betaAct oldSeed p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p := by
  exact
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_sourceDefect_sub_moment
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p hactiveSmooth
        (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
          (W := B.sampleData.W) R certificate deltaStar
            hprefix hp hWp hchargeDvd)

/-- Exact expansion of the literal Post-Hfit structured pre-selector.  Its
source input is precisely the two-part finite reindex above; the target
ledger is independently derivable from charge divisibility. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
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
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hselector :
      BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
        B K0 R certificate deltaStar betaProt betaAct oldSeed p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p =
      roughCanonicalPostHfitCompleteSignedResidual
          B K0 R certificate deltaStar betaProt betaAct p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p := by
  unfold
    BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
    at hselector
  simpa only [bankPaperCanonicalPostHfitStructuredPreSelector,
    roughCanonicalPostHfitCompleteSignedResidual] using
    (bankPaperCanonicalStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
      (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass)
        p hactiveSmooth htarget hselector)

/-- In the actual medium-prime range, the same Post-Hfit expansion requires
only charge divisibility and the named global source reindexing: the charged
target ledger is supplied by the preceding finite product argument. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment_of_chargeDvd
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
    (hprefix : 2 * depth + 1 <= B.sampleData.W)
    (hp : p.Prime) (hWp : B.sampleData.W < p)
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hselector :
      BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
        B K0 R certificate deltaStar betaProt betaAct oldSeed p) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p =
      roughCanonicalPostHfitCompleteSignedResidual
          B K0 R certificate deltaStar betaProt betaAct p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p := by
  exact
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p hactiveSmooth
        (bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
          (W := B.sampleData.W) R certificate deltaStar
            hprefix hp hWp hchargeDvd)
        hselector

/-- If the known structured placement moment vanishes at `p`, the literal
Post-Hfit pre-selector deficit is the four-term signed residual itself. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_of_moment_eq_zero
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
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (htarget : BankPaperCanonicalSignedResidualTargetLedger
      R certificate deltaStar p)
    (hselector :
      BankPaperCanonicalPostHfitGlobalSourceSignedResidualSelectorLedger
        B K0 R certificate deltaStar betaProt betaAct oldSeed p)
    (hmoment :
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p = 0) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1))
        (bankPaperCanonicalPostHfitStructuredPreSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed
            minusMass plusMass) p =
      roughCanonicalPostHfitCompleteSignedResidual
        B K0 R certificate deltaStar betaProt betaAct p := by
  rw [
    bankPaperCanonicalPostHfitStructuredPreSelector_deficit_eq_completeSignedResidual_sub_moment
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p hactiveSmooth htarget hselector,
    hmoment, sub_zero]

end BankPaperRealization

end

end Erdos390.WholePaper
