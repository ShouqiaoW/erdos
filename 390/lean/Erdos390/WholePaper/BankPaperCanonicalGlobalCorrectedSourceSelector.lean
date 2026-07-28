import Erdos390.WholePaper.BankPaperCanonicalStructuredPrebridgeLedgerConnector
import Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration

/-!
# Global corrected source selector

The original two-zero-cell source selector uses the protected-plus-active
weight on the smooth guarded broad pool and the old active ambient weight
everywhere else.  That is the right source for the Section 8 moment ledger,
but it is not the selector required by the Section 9 endpoint theorem on a
nonsmooth active row.

This file makes a rowwise compatible global replacement.  Off the smooth
broad pool it keeps the old ambient weight on complete-rough label `1`, and
uses the already constructed postcharge corrected row weight on active
nonexceptional labels, while exceptional labels are zero.  Consequently:

* once structured active values are known to lie in the complete smooth
  row, the source still agrees with the old ambient weight at every such
  coordinate outside the smooth broad pool, so the existing two-zero-cell
  prebridge ledger applies unchanged;
* every active nonsmooth guarded broad coordinate is exactly the explicit
  postcharge corrected row weight; and
* after structured placement, the two exact `hpreNonsmooth` and
  `hpreUpper` interfaces consumed by the endpoint-slack theorem are exposed.

The exact corrected-weight identity uses the literal active-nonexceptional
classification; preservation by structured placement additionally uses
smooth-row support of the structured active values.  The smooth upper theorem
honestly retains the pointwise `O(1 / L)` upper bound for the placement seed.
Existing two-zero-cell capacity only bounds the resulting selector by `1`;
it does not imply this sharper estimate.

On an active nonexceptional complete label, the outside selector intentionally
uses the full corrected-row weight, including its raw-weight branch outside
the guarded broad correction pool.  This is the rowwise selector whose total
is controlled by the postcharge construction, rather than a pointwise-only
patch of the old ambient source.  A rounded-selector input for this global
source remains explicit below; it is not manufactured from local slack.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Arbitrary-seed push-forward -/

/-- Numerical head-pattern separation makes the structured value map
injective, so the ambient push-forward of an arbitrary seed at an occupied
coordinate is exactly the corresponding tagged weight.  This elementary
form is kept below the Section 8 one-shot layer so that the latter can reuse
the global source connector without an import cycle. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (hsep : D.HeadPatternsSeparated) (m : D.Sample) :
    bankPaperCanonicalActiveSeedAmbientWeight D seed (D.value m) =
      seed m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _hk hkm
    rw [if_neg]
    intro hvalue
    exact hkm (D.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

/-! ## The global outside selector -/

/-- Off the smooth correction pool, retain the old ambient active weight on
the complete smooth row, vanish on exceptional nonsmooth rows, and use the
explicit corrected weight on active nonexceptional rows. -/
def bankPaperCanonicalGlobalCorrectedOutsideSelector
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
    (deltaStar alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) (a : Nat) : Real := by
  classical
  exact
    if completeRoughLabel (yNat B.sampleData.n) a = 1 then
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a
    else
      if RoughCanonicalExceptionalLabel B.sampleData.n deltaStar
          (completeRoughLabel (yNat B.sampleData.n) a) then
        0
      else
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar B.sampleData.W K
            (completeRoughLabel (yNat B.sampleData.n) a)
              alpha beta B.L a

/-- On the complete smooth row, the global outside selector is exactly the
old active ambient weight. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_ambient_of_mem_smoothRow
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
    {deltaStar alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
        B R certificate deltaStar alpha beta oldSeed a =
      bankPaperCanonicalActiveSeedAmbientWeight
        B.sampleData oldSeed a := by
  have hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1 :=
    (mem_completeRoughRowFiber.mp ha).2
  simp [bankPaperCanonicalGlobalCorrectedOutsideSelector, hlabel]

/-- A guarded broad coordinate in a nonsmooth row cannot also lie in the
complete smooth row. -/
theorem roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
    {c deltaStar : Real} {depth n W K label a : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  intro haSmooth
  have haLabel : a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar W K label ha
  have hsmoothEq := (mem_completeRoughRowFiber.mp haSmooth).2
  have hlabelEq := (mem_completeRoughRowFiber.mp haLabel).2
  exact hlabel (hlabelEq.symm.trans hsmoothEq)

/-- On an active nonexceptional guarded broad pool, the global outside
selector is the explicit postcharge corrected weight for that literal row
label. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_corrected_of_mem_nonsmoothPool
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
    {deltaStar alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
        B R certificate deltaStar alpha beta oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha beta B.L a := by
  have haRow : a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K label ha
  have haLabel :
      completeRoughLabel (yNat B.sampleData.n) a = label :=
    (mem_completeRoughRowFiber.mp haRow).2
  have hnonexceptional :
      ¬ RoughCanonicalExceptionalLabel
        B.sampleData.n deltaStar label :=
    not_lt_of_ge hactive.2
  simp [bankPaperCanonicalGlobalCorrectedOutsideSelector, haLabel,
    hactive.1, hnonexceptional]

/-! ## The global source and its exact rowwise values -/

/-- The protected smooth source joined to the explicit nonsmooth postcharge
correction, while retaining the old ambient source on the remainder of the
complete smooth row. -/
def bankPaperCanonicalGlobalCorrectedSourceSelector
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
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
    B R certificate deltaStar betaProt oldSeed
      (bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
        B R certificate deltaStar alpha beta oldSeed)

/-- On the guarded smooth broad pool, the global source retains the exact
protected-plus-old-active formula used by the Section 8 ledger. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_smoothPool
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
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a =
      betaProt / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  simp [bankPaperCanonicalGlobalCorrectedSourceSelector,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, ha]

/-- On every active nonexceptional guarded broad pool, the global source is
exactly the explicit corrected row selector. -/
@[simp] theorem bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_nonsmoothPool
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
    {deltaStar betaProt alpha beta : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (hactive :
      RoughCanonicalActiveNonexceptionalLabel
        B.sampleData.n deltaStar label)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed a =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha beta B.L a := by
  have hnotSmoothRow :
      a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
      certificate hactive.1 ha
  have hnotSmoothPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro haSmooth
    exact hnotSmoothRow
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 haSmooth)
  rw [bankPaperCanonicalGlobalCorrectedSourceSelector,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, if_neg hnotSmoothPool]
  exact
    bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_corrected_of_mem_nonsmoothPool
      B R certificate oldSeed hactive ha

/-! ## Compatibility with the Section 8 prebridge ledger -/

/-- The global corrected source preserves the complete two-zero-cell
prebridge moment ledger.  Only its values on the complete smooth row enter
that proof, and those values agree with the old ambient source. -/
theorem bankPaperCanonicalGlobalCorrectedSourceSelector_prebridgeMomentLedger_twoZeroHeadCells
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
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hmass : minusMass + plusMass = (rowChange : Real)) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger (K := K)
      B R certificate deltaStar betaProt
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) := by
  have houtsideActive : forall a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 ->
      bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
          B R certificate deltaStar alpha beta oldSeed a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
    intro a haActive _haPool
    exact
      bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_ambient_of_mem_smoothRow
        B R certificate oldSeed (hactiveSmooth haActive)
  simpa only [bankPaperCanonicalGlobalCorrectedSourceSelector] using
    (bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_of_active
      (K := K) B R certificate deltaStar betaProt oldSeed
        (bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
          B R certificate deltaStar alpha beta oldSeed)
        minusMass plusMass rowChange hactiveSmooth houtsideActive
          hminus hplus hmass)

/-! ## Full Section 8 placement with the global source -/

/-- A feasible global corrected source remains feasible after the
two-zero-cell rebalance once the two changed tagged cells satisfy their
literal capacities.  Values outside the structured image are unchanged by
the generic ambient-difference identity; unchanged structured cells use the
same identity together with value-map injectivity. -/
theorem
    bankPaperCanonicalGlobalCorrectedStructuredPlacementSelector_twoZeroHeadCells_feasible_of_source
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
    (deltaStar betaProt alpha beta : Real)
    (hbetaProt : 0 <= betaProt)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hsource : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hplusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <=
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a ∧
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a <= 1 := by
  have houtsideActive : forall a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 ->
      bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
          B R certificate deltaStar alpha beta oldSeed a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
    intro a haActive _haPool
    exact
      bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_ambient_of_mem_smoothRow
        B R certificate oldSeed (hactiveSmooth haActive)
  intro a haCandidate
  have hdiff :
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
            B R certificate deltaStar betaProt alpha beta oldSeed a =
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a := by
    simpa only [bankPaperCanonicalGlobalCorrectedSourceSelector] using
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source_of_active
        (K := K) B R certificate deltaStar betaProt oldSeed
          (bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
            B R certificate deltaStar alpha beta oldSeed)
          houtsideActive minusMass plusMass a)
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp hactive
    have hnewAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass)
            (B.sampleData.value m) =
          bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass)
          hsep m
    have holdAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed
            (B.sampleData.value m) =
          oldSeed m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData oldSeed hsep m
    by_cases hmMinus :
        B.sampleData.cellOf m = (none, .minus)
    · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
          (K := K) B R certificate
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass)
            (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
        hnewAmbient,
        bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate (hminus m hmMinus)]
      have hcap := hminusCapacity m hmMinus
      exact
        ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
          hcap.2⟩
    · by_cases hmPlus :
          B.sampleData.cellOf m = (none, .plus)
      · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
            (K := K) B R certificate
              (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                B R certificate deltaStar betaProt alpha beta oldSeed)
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass)
              (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
          hnewAmbient,
          bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
            B R certificate (hplus m hmPlus)]
        have hcap := hplusCapacity m hmPlus
        exact
          ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
            hcap.2⟩
      · have hsame :
          bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m =
            oldSeed m := by
          simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
            bankPaperCanonicalUniformCellIncrement, hmMinus, hmPlus]
        rw [hnewAmbient, holdAmbient, hsame] at hdiff
        have hplacedEq :
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                B R certificate deltaStar betaProt
                (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                  B R certificate deltaStar betaProt alpha beta oldSeed)
                (bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass)
                (B.sampleData.value m) =
              bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                B R certificate deltaStar betaProt alpha beta oldSeed
                  (B.sampleData.value m) := by
          linarith
        rw [hplacedEq]
        exact hsource (B.sampleData.value m) haCandidate
  · have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    rw [hnewZero, holdZero] at hdiff
    have hplacedEq :
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a =
          bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
            B R certificate deltaStar betaProt alpha beta oldSeed a := by
      linarith
    rw [hplacedEq]
    exact hsource a haCandidate

/-- A minimal global corrected source state, the ordinary two changed-cell
capacities, and the signed mass identity produce the full structured
additive placement.  This is the primary non-hardwired Section 8 entry point
needed before the Section 9 endpoint construction. -/
theorem
    bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_sourceState
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
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta : Real)
    (hbetaProt : 0 <= betaProt)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed))
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hplusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hmass : minusMass + plusMass = (rowChange : Real)) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt
      (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed)
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
        minusMass plusMass) := by
  have hfeasible :=
    bankPaperCanonicalGlobalCorrectedStructuredPlacementSelector_twoZeroHeadCells_feasible_of_source
      (K := K) B R certificate deltaStar betaProt alpha beta hbetaProt
        oldSeed minusMass plusMass hsep hactiveSmooth Ssource.feasible
          hminus hplus hminusCapacity hplusCapacity
  have hledger :=
    bankPaperCanonicalGlobalCorrectedSourceSelector_prebridgeMomentLedger_twoZeroHeadCells
      (K := K) B R certificate deltaStar betaProt alpha beta oldSeed
        minusMass plusMass rowChange hactiveSmooth hminus hplus hmass
  exact
    bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
      B R certificate fixed
      (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed)
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
        minusMass plusMass)
      hfeasible Ssource.rowIntegral
        Ssource.deficitSupportedOnPrimeBand hledger

/-- A rounded global corrected source, the ordinary two changed-cell
capacities, and the signed mass identity produce the full structured
additive placement.  This is the non-hardwired Section 8 entry point needed
before the Section 9 endpoint construction. -/
theorem
    bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_roundedSource
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
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta : Real)
    (hbetaProt : 0 <= betaProt)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (Ssource : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      B.partition.band cellIndex pointwiseUpper prefixUpper
      (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed))
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hplusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hmass : minusMass + plusMass = (rowChange : Real)) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt
      (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed)
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
        minusMass plusMass) := by
  have Sstate :=
    bankPaperCanonicalSelectorSourceState_of_roundedSelectorTangentInput
      R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      B.partition.band cellIndex pointwiseUpper prefixUpper
      (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed)
      Ssource
  exact
    bankPaperCanonicalGlobalCorrectedStructuredAdditivePlacement_twoZeroHeadCells_of_sourceState
      (K := K) B R certificate fixed deltaStar betaProt alpha beta
        hbetaProt oldSeed minusMass plusMass rowChange Sstate hsep
          hactiveSmooth hminus hplus hminusCapacity hplusCapacity hmass

/-! ## Exact endpoint-slack inputs after structured placement -/

/-- Head-pattern separation transports an arbitrary pointwise seed upper
bound to its ambient push-forward.  Unlike the older bridge-baseline lemma,
this form applies directly to a rebalanced placement seed. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_le_of_pointwise
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (seed : B.sampleData.Sample -> Real)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hseedUpper : forall m : B.sampleData.Sample,
      seed m <= Cactive / B.L) :
    forall a : Nat,
      bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData seed a <= Cactive / B.L := by
  intro a
  by_cases ha : exists m : B.sampleData.Sample,
      B.sampleData.value m = a
  · obtain ⟨m, rfl⟩ := ha
    calc
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData seed
          (B.sampleData.value m) =
        seed m :=
          bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
            B.sampleData seed hsep m
      _ <= Cactive / B.L := hseedUpper m
  · rw [bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      B.sampleData seed a (fun m hm => ha ⟨m, hm⟩)]
    exact div_nonneg hCactive B.L_pos.le

/-- The structured placement built from the global source supplies exactly
the `hpreNonsmooth` identity required by the actual endpoint-slack theorem. -/
theorem bankPaperCanonicalGlobalCorrectedStructuredPlacement_hpreNonsmooth
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
    (deltaStar betaProt alpha beta : Real)
    (oldSeed placementSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                B R certificate deltaStar betaProt
                (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                  B R certificate deltaStar betaProt alpha beta oldSeed)
                placementSeed a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a := by
  intro label hlabel a ha
  have hnotSmoothRow :
      a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
      certificate hlabel.1 ha
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
    B R certificate
      (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
        B R certificate deltaStar betaProt alpha beta oldSeed)
      placementSeed hactiveSmooth hnotSmoothRow]
  exact
    bankPaperCanonicalGlobalCorrectedSourceSelector_apply_of_mem_nonsmoothPool
      B R certificate oldSeed hlabel ha

/-- The structured placement has the smooth `hpreUpper` estimate from a
pointwise `O(1 / L)` placement-seed bound and the literal constant
comparison `betaProt + Cactive <= Cfixed`. -/
theorem bankPaperCanonicalGlobalCorrectedStructuredPlacement_hpreUpper
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
    (deltaStar betaProt alpha beta : Real)
    (oldSeed placementSeed : B.sampleData.Sample -> Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cactive / B.L)
    (Cfixed : Real) (hfixed : betaProt + Cactive <= Cfixed) :
    ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            placementSeed a <=
        Cfixed / B.L := by
  intro a ha
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
      B R certificate
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed)
        placementSeed ha,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed)
        placementSeed ha]
  have hambient :=
    bankPaperCanonicalActiveSeedAmbientWeight_le_of_pointwise
      B hsep placementSeed Cactive hCactive hplacementSeedUpper a
  calc
    betaProt / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData placementSeed a <=
        betaProt / B.L + Cactive / B.L :=
      add_le_add le_rfl hambient
    _ = (betaProt + Cactive) / B.L := by ring
    _ <= Cfixed / B.L :=
      div_le_div_of_nonneg_right hfixed B.L_pos.le

/-- The pair of hypotheses consumed verbatim as `hpreUpper` and
`hpreNonsmooth` by
`bankPaperCanonicalActualP87EndpointSelector_guardedSlackConstruction_of_reserve`.
The sharper smooth seed upper remains visible and is not hidden behind a
selector existence claim. -/
theorem bankPaperCanonicalGlobalCorrectedStructuredPlacement_slackInputs
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
    (deltaStar betaProt alpha beta : Real)
    (oldSeed placementSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cactive / B.L)
    (Cfixed : Real) (hfixed : betaProt + Cactive <= Cfixed) :
    (∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                B R certificate deltaStar betaProt alpha beta oldSeed)
              placementSeed a <=
          Cfixed / B.L) ∧
      (forall label,
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K label,
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                  B R certificate deltaStar betaProt
                  (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                    B R certificate deltaStar betaProt alpha beta oldSeed)
                  placementSeed a =
              R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha beta B.L a) := by
  exact
    ⟨bankPaperCanonicalGlobalCorrectedStructuredPlacement_hpreUpper
        B R certificate deltaStar betaProt alpha beta oldSeed placementSeed
          hsep Cactive hCactive hplacementSeedUpper Cfixed hfixed,
      bankPaperCanonicalGlobalCorrectedStructuredPlacement_hpreNonsmooth
        B R certificate deltaStar betaProt alpha beta oldSeed placementSeed
          hactiveSmooth⟩

end BankPaperRealization

end

end Erdos390.WholePaper
