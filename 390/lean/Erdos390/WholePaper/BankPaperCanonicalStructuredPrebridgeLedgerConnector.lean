import Erdos390.WholePaper.BankPaperCanonicalSmoothAdditivePlacement

/-!
# Two-zero-cell producer for the structured prebridge ledger

The complete structured placement differs from the older head-free-pool
refinement at every structured head coordinate.  There is nevertheless a
canonical source for which the whole-row signed change is elementary: use
the protected-plus-old-active selector on the correction pool and the old
ambient active seed everywhere else.  Replacing the old seed by the paper's
two-zero-head-cell rebalance then changes that source pointwise by exactly
the ambient push-forward of the tagged rebalance.

The existing support and head-free-pool theorems consequently prove all
three fields of
`BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger`:

* structured values lie in the guarded smooth row;
* the smooth-row mass change is the prescribed integer; and
* every prime at most `W` has zero signed valuation change.

No head-target, medium-prime, capacity, or asymptotic hypothesis is used.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- The canonical source for a structured two-zero-cell rebalance.  It is
the protected-plus-old-active selector on the head-free correction pool and
the old ambient active seed off that pool. -/
def bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector
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
    (oldSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K) B R certificate
    deltaStar betaProt oldSeed
      (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed)

@[simp] theorem bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_mem
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
    {deltaStar betaProt : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
      B R certificate
        deltaStar betaProt oldSeed a =
      betaProt / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a := by
  simp [bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, ha]

@[simp] theorem bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_not_mem
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
    {deltaStar betaProt : Real}
    (oldSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
      B R certificate
        deltaStar betaProt oldSeed a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed a := by
  simp [bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector,
    bankPaperCanonicalTwoZeroHeadCellSourceSelector, ha]

/-- The ambient signed change of a two-zero-cell rebalance vanishes outside
any finite support containing both changed cell images. -/
theorem bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub_eq_zero_of_not_mem
    {P : Finset Nat}
    (D : StructuredSampleData (PaperHeadSimplex.Tag P))
    (seed : D.Sample -> Real) (minusMass plusMass : Real)
    (support : Finset Nat)
    (hminus : forall m : D.Sample,
      D.cellOf m = (none, .minus) -> D.value m ∈ support)
    (hplus : forall m : D.Sample,
      D.cellOf m = (none, .plus) -> D.value m ∈ support)
    {a : Nat} (ha : a ∉ support) :
    bankPaperCanonicalActiveSeedAmbientWeight D
          (bankPaperCanonicalTwoZeroHeadCellRebalance D seed
            minusMass plusMass) a -
        bankPaperCanonicalActiveSeedAmbientWeight D seed a = 0 := by
  rw [bankPaperCanonicalActiveSeedAmbientWeight_sub]
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  by_cases hchange :
      bankPaperCanonicalTwoZeroHeadCellRebalance D seed
          minusMass plusMass m - seed m = 0
  · simp [hchange]
  · have hmSupport : D.value m ∈ support :=
      bankPaperCanonicalTwoZeroHeadCellRebalance_changeSupport
        D seed minusMass plusMass support hminus hplus m hchange
    have hmValue : D.value m ≠ a := by
      intro hma
      apply ha
      simpa only [hma] using hmSupport
    simp [hmValue]

/-- If an outside selector agrees with a scaled seed on every structured
sample tag, numerical head-pattern separation identifies it with the
ambient push-forward at every occupied value. -/
theorem bankPaperCanonicalOutsideSelector_eq_scaledActiveSeedAmbientWeight_of_mem
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (outsideSelector : Nat -> Real)
    (houtside : forall m : D.Sample,
      outsideSelector (D.value m) =
        bankPaperCanonicalScaledActiveSeed T q m)
    {a : Nat}
    (ha : a ∈ bankPaperCanonicalStructuredActiveValues D) :
    outsideSelector a =
      bankPaperCanonicalActiveSeedAmbientWeight D
        (bankPaperCanonicalScaledActiveSeed T q) a := by
  obtain ⟨m, rfl⟩ := mem_bankPaperCanonicalStructuredActiveValues.mp ha
  rw [houtside m,
    bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      D T q hsep m]

/-- General pointwise identity.  The outside selector may retain arbitrary
frozen coordinates; it only has to agree with the old ambient seed on
structured active values outside the correction pool. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source_of_active
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
    (houtsideActive : forall a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 ->
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (minusMass plusMass : Real) (a : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
            minusMass plusMass) a -
        bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
            minusMass plusMass) a -
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) hactive]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos hpool]
      ring
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
          B R certificate hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_neg hpool, houtsideActive a hactive hpool]
      ring
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) hactive]
    have hnew :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
              minusMass plusMass) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hold :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
              minusMass plusMass) hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos hpool, hnew, hold]
      ring
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
              minusMass plusMass) hpool,
        hnew, hold]
      ring

/-- For the canonical ambient source, the corrected structured placement
changes every ambient coordinate by exactly the pushed-forward tagged
two-zero-cell change. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source
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
    (minusMass plusMass : Real) (a : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
            minusMass plusMass) a -
        bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
            minusMass plusMass) a -
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) hactive]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate hpool,
        bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_mem
          B R certificate oldSeed hpool]
      ring
    · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
          B R certificate hpool,
        bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_not_mem
          B R certificate oldSeed hpool]
      ring
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) hactive]
    have hnew :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
              minusMass plusMass) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hold :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
              minusMass plusMass) hpool,
        bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_mem
          B R certificate oldSeed hpool,
        hnew, hold]
      ring
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
              minusMass plusMass) hpool,
        hnew, hold]
      ring

/-- The complete structured prebridge ledger for an arbitrary outside
selector.  Only its values on occupied structured coordinates outside the
head-free pool are constrained; all other frozen coordinates are retained. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_of_active
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
    (minusMass plusMass : Real) (rowChange : Int)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (houtsideActive : forall a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 ->
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
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
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) := by
  refine ⟨hactiveSmooth, ⟨rowChange, ?_⟩, ?_⟩
  · calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
                (bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass) a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source_of_active
              (K := K) B R certificate deltaStar betaProt oldSeed outsideSelector
                houtsideActive minusMass plusMass a
      _ = minusMass + plusMass := by
        apply sum_bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub
        · intro m hm
          exact
            R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K 1 (hminus m hm)
        · intro m hm
          exact
            R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K 1 (hplus m hm)
      _ = (rowChange : Real) := hmass
  · intro q hqPrime hqW
    unfold
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
    apply Finset.sum_eq_zero
    intro a _ha
    rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source_of_active
      (K := K) B R certificate deltaStar betaProt oldSeed outsideSelector
        houtsideActive minusMass plusMass a]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime
          B R certificate hqPrime hqW hpool]
      ring
    · rw [bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub_eq_zero_of_not_mem
          B.sampleData oldSeed minusMass plusMass
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hminus hplus hpool]
      ring

/-- Scaled structured seeds need only literal agreement of the outside
selector with the tagged seed.  Head-pattern separation turns that sample
agreement into the ambient active-coordinate agreement used above. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_scaled
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
    (T : BarycentricTarget B.sampleData) (q : Real)
    (outsideSelector : Nat -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (houtside : forall m : B.sampleData.Sample,
      outsideSelector (B.sampleData.value m) =
        bankPaperCanonicalScaledActiveSeed T q m)
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
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate
          deltaStar betaProt (bankPaperCanonicalScaledActiveSeed T q)
            outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q) minusMass plusMass) := by
  apply
    bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_of_active
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalScaledActiveSeed T q) outsideSelector
        minusMass plusMass rowChange hactiveSmooth
  · intro a haActive _haPool
    exact
      bankPaperCanonicalOutsideSelector_eq_scaledActiveSeedAmbientWeight_of_mem
        B.sampleData T q hsep outsideSelector houtside haActive
  · exact hminus
  · exact hplus
  · exact hmass

/-- Physical interval endpoints and pointwise exclusion from the rough
canonical guard discharge the structured-support premise in the scaled-seed
producer. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_scaled_of_physicalIntervals
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
    (T : BarycentricTarget B.sampleData) (q : Real)
    (outsideSelector : Nat -> Real)
    (minusMass plusMass : Real) (rowChange : Int)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (houtside : forall m : B.sampleData.Sample,
      outsideSelector (B.sampleData.value m) =
        bankPaperCanonicalScaledActiveSeed T q m)
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
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate
          deltaStar betaProt (bankPaperCanonicalScaledActiveSeed T q)
            outsideSelector)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q) minusMass plusMass) := by
  apply
    bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_scaled
      (K := K) B R certificate deltaStar betaProt T q outsideSelector
        minusMass plusMass rowChange hsep
  · exact
      bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
        B R certificate deltaStar I hlowerOne hupperTwo hlo hhi hKh hnotGuard
  · exact houtside
  · exact hminus
  · exact hplus
  · exact hmass

/-- The two literal zero-head cell changes construct the complete signed
whole-smooth-row prebridge ledger for the canonical ambient source. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells
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
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) := by
  refine ⟨hactiveSmooth, ⟨rowChange, ?_⟩, ?_⟩
  · calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed)
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed a)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
                (bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass) a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source
              (K := K) B R certificate deltaStar betaProt oldSeed
                minusMass plusMass a
      _ = minusMass + plusMass := by
        apply sum_bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub
        · intro m hm
          exact
            R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K 1 (hminus m hm)
        · intro m hm
          exact
            R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K 1 (hplus m hm)
      _ = (rowChange : Real) := hmass
  · intro q hqPrime hqW
    unfold
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
    apply Finset.sum_eq_zero
    intro a _ha
    rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source
      (K := K) B R certificate deltaStar betaProt oldSeed minusMass plusMass a]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [factorization_eq_zero_of_mem_guardedBroadCorrectionPool_of_headPrime
          B R certificate hqPrime hqW hpool]
      ring
    · rw [bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub_eq_zero_of_not_mem
          B.sampleData oldSeed minusMass plusMass
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) hminus hplus hpool]
      ring

/-- Physical partition endpoints and pointwise exclusion from the rough
canonical guard discharge the support field of the preceding two-zero-cell
ledger producer. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_of_physicalIntervals
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
    (minusMass plusMass : Real) (rowChange : Int)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
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
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          minusMass plusMass) := by
  apply
    bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells
      (K := K) B R certificate deltaStar betaProt oldSeed
        minusMass plusMass rowChange
  · exact
      bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
        B R certificate deltaStar I hlowerOne hupperTwo hlo hhi hKh hnotGuard
  · exact hminus
  · exact hplus
  · exact hmass

end BankPaperRealization

end

end Erdos390.WholePaper
