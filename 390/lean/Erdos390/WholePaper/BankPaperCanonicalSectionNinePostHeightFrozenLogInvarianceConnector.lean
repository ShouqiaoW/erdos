import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourcePrebridgeConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector

/-!
# Frozen-log invariance under the post-height active-seed replacement

The rounded frozen-top source and the final post-height placement use
different active seeds.  The structured placement changes the selector by
exactly the corresponding change of ambient active weight.  Therefore,
after subtracting the active weight in
`bankPaperCanonicalActualFrozenWeight`, the tagged frozen remainder is
unchanged.

This file records that cancellation first for an arbitrary replacement
seed, and then for the literal rounded source and post-height barycentric
seed.  Summing the pointwise identity gives equality of the finite
candidate-log contribution and hence of
`bankPaperCanonicalActualFrozenLogMass`.  The proof is purely finite and
introduces no compatibility or redistribution contract: the specialized
result obtains the already existing outside compatibility from broad
support.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

namespace BankPaperRealization

/-! ## Arbitrary-seed frozen remainder -/

/-- Replacing the active seed in a structured placement leaves every
tagged frozen candidate weight unchanged.

The pointwise signed placement identity says that the selector changes by
the difference of the new and old ambient active weights.  Subtracting the
new ambient active weight therefore recovers the old frozen remainder. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_eq_source_of_arbitrarySeedReplacement
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
    (candidates : Finset Nat)
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (a : BankPaperCanonicalActualFrozenIndex candidates) :
    bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
          (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          newSeed)
        newSeed a =
      bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        oldSeed a := by
  have hchange :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
      (K := K) B R certificate deltaStar betaProt
        oldSeed newSeed outsideSelector houtsideActive a.1
  unfold bankPaperCanonicalActualFrozenWeight
  linarith only [hchange]

/-- The pointwise cancellation remains exact after applying the ambient
push-forward used by Proposition 8.7. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacement_frozenAmbientWeight_eq_source_of_arbitrarySeedReplacement
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
    (candidates : Finset Nat)
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (a : Nat) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
            (K := K) B R certificate deltaStar betaProt
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            newSeed)
          newSeed) a =
      BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          oldSeed) a := by
  classical
  unfold BridgeData.frozenAmbientWeight
  apply Finset.sum_congr rfl
  intro b _hb
  by_cases hvalue :
      bankPaperCanonicalActualFrozenValue b = a
  · rw [if_pos hvalue, if_pos hvalue]
    exact
      bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_eq_source_of_arbitrarySeedReplacement
        (K := K) B R certificate candidates deltaStar betaProt
          oldSeed newSeed outsideSelector houtsideActive b
  · rw [if_neg hvalue, if_neg hvalue]

/-- The logarithmically weighted finite frozen-candidate sum is invariant
under the same arbitrary active-seed replacement. -/
theorem
    sum_bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_mul_log_eq_source_of_arbitrarySeedReplacement
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
    (candidates : Finset Nat)
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a) :
    (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
        bankPaperCanonicalActualFrozenWeight B.sampleData candidates
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed)
            newSeed a *
          Real.log (bankPaperCanonicalActualFrozenValue a : Real)) =
      ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
        bankPaperCanonicalActualFrozenWeight B.sampleData candidates
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            oldSeed a *
          Real.log (bankPaperCanonicalActualFrozenValue a : Real) := by
  classical
  apply Finset.sum_congr rfl
  intro a _ha
  rw [
    bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_eq_source_of_arbitrarySeedReplacement
      (K := K) B R certificate candidates deltaStar betaProt
        oldSeed newSeed outsideSelector houtsideActive a]

/-- Fixed factors and the state-zero bank do not depend on the active seed,
so the complete finite frozen logarithmic mass is invariant as well. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenLogMass_eq_source_of_arbitrarySeedReplacement
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
    (fixed bankBase candidates : Finset Nat)
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a) :
    bankPaperCanonicalActualFrozenLogMass B.sampleData
        fixed bankBase candidates
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
          (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          newSeed)
        newSeed =
      bankPaperCanonicalActualFrozenLogMass B.sampleData
        fixed bankBase candidates
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        oldSeed := by
  unfold bankPaperCanonicalActualFrozenLogMass
  rw [
    sum_bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_mul_log_eq_source_of_arbitrarySeedReplacement
      (K := K) B R certificate candidates deltaStar betaProt
        oldSeed newSeed outsideSelector houtsideActive]

/-! ## Literal rounded-source to post-height specialization -/

/-- Pointwise tagged frozen-weight invariance from the rounded frozen-top
source to the literal post-height placed selector.

The only geometric inputs are the smooth-row and broad-lower-block support
facts already used by the post-height prebridge.  They construct the
outside compatibility through
`bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport`;
no compatibility proposition is assumed. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_eq_roundedSource
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (a : BankPaperCanonicalActualFrozenIndex
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)) :
    bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) a =
      bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha qTilde) a := by
  have hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate Tsource deltaStar betaProt
          alpha beta qTilde :=
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde hactiveSmooth hactiveBroad
  simpa only [
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalTopFrozenRoundedSourceSelector,
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using
    (bankPaperCanonicalGuardedStructuredAdditivePlacement_actualFrozenWeight_eq_source_of_arbitrarySeedReplacement
      (K := K) B R certificate
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate Tsource deltaStar betaProt alpha qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H)
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt alpha qTilde))
        hcompat a)

/-- The candidate part of the frozen logarithmic mass is unchanged by the
literal rounded-source to post-height replacement. -/
theorem
    sum_bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_mul_log_eq_roundedSource
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
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K) :
    (∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector
              (K := K) B R certificate Tsource I hlo hhi H
                deltaStar betaProt alpha beta qTilde)
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H) a *
          Real.log (bankPaperCanonicalActualFrozenValue a : Real)) =
      ∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha beta qTilde)
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde) a *
          Real.log (bankPaperCanonicalActualFrozenValue a : Real) := by
  classical
  apply Finset.sum_congr rfl
  intro a _ha
  rw [
    bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_eq_roundedSource
      (K := K) B R certificate Tsource I hlo hhi H
        deltaStar betaProt alpha beta qTilde
        hactiveSmooth hactiveBroad a]

/-- The complete finite frozen logarithmic mass, including fixed factors
and the state-zero bank, is the same before and after the post-height
active-seed replacement. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenLogMass_eq_roundedSource
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
    (fixed bankBase : Finset Nat)
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K) :
    bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) =
      bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha qTilde) := by
  unfold bankPaperCanonicalActualFrozenLogMass
  rw [
    sum_bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_mul_log_eq_roundedSource
      (K := K) B R certificate Tsource I hlo hhi H
        deltaStar betaProt alpha beta qTilde
        hactiveSmooth hactiveBroad]

end BankPaperRealization

end

end Erdos390.WholePaper
