import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacedMeasureConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenSmoothFeasibilityConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenSelectorTailSupportReductionConnector

/-!
# The literal frozen-top source-to-post-height prebridge

The frozen-top rounded source contains its own nearest-integer active seed,
whereas the final baseline uses the fresh post-height barycentric seed of
mass `q0-d`.  These seeds are not equal.  What the structured prebridge
needs is instead their exact *signed difference* on the complete smooth
row:

* its total mass is the integer `-d`;
* its valuation moment at every head prime is zero.

This file proves that ledger.  The old head moment is recovered from the
literal source state's zero deficit outside the medium-prime band and the
paper's selector-tail target.  The new head moment is the exact
`activeHeadTarget` realized by the post-height target.  Thus no equality of
the old and new seeds is assumed.

The final theorem combines this ledger with the geometric feasibility
theorem from the post-height placed-measure connector, yielding the actual
measure and the full row-integral structured placement.
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

/-! ## The geometric outside compatibility -/

/-- Broad-lower-block support makes the restored smooth top invisible at
every occupied structured coordinate outside the protected pool.  Hence
the literal rounded frozen-top source has the exact outside compatibility
needed for active-seed replacement.

This discharges the earlier compatibility predicate from concrete support
geometry rather than retaining it as an abstract contract. -/
theorem
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
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
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K) :
    BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde := by
  apply
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_topInvisible
      (K := K) B R certificate Tsource deltaStar betaProt alpha beta qTilde
        hactiveSmooth
  intro a haActive haNotPool
  obtain ⟨m, rfl⟩ :=
    mem_bankPaperCanonicalStructuredActiveValues.mp haActive
  have hmActive :
      B.sampleData.value m ∈
        bankPaperCanonicalStructuredActiveValues B.sampleData :=
    mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩
  have hmSmooth := hactiveSmooth hmActive
  calc
    bankPaperCanonicalSmoothTopWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha B.L
          (B.sampleData.value m) =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L
          (B.sampleData.value m) :=
      bankPaperCanonicalSmoothTopWeight_eq_rawWeight_of_mem_guardedSmoothRow_of_not_mem_broadPool
        B R certificate hmSmooth haNotPool
    _ =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate deltaStar betaProt
          (B.sampleData.value m) :=
      (bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem_smoothBroadRow
        B R certificate hmSmooth (hactiveBroad m)).symm
    _ = 0 :=
      bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
        B R certificate haNotPool

/-! ## Arbitrary replacement of a two-zero-cell source seed -/

/-- Pointwise signed identity for replacing the active seed of an arbitrary
two-zero-cell source by a fresh structured seed.

The outside selector may retain any frozen data.  It is constrained only
at occupied active coordinates outside the protected broad pool, exactly
as in the existing two-zero-cell placement theorem. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
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
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector)
          newSeed a -
        bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector a =
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData newSeed a -
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed hactive]
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
        newSeed hactive]
    have hnew :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData newSeed a = 0 := by
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
            newSeed hpool]
      unfold bankPaperCanonicalTwoZeroHeadCellSourceSelector
      rw [if_pos hpool, hnew, hold]
      ring
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed outsideSelector)
            newSeed hpool,
        hnew, hold]
      ring

/-- Exact prebridge ledger for an arbitrary fresh replacement seed.

This theorem distills the mathematical content of a seed replacement:
support on the complete smooth row, an integral signed mass change, and
equality of all head-prime moments. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_of_arbitrarySeedReplacement
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
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (rowChange : Int)
    (hmass :
      bankPaperCanonicalLiteralActiveMass B.sampleData newSeed -
          bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed =
        (rowChange : Real))
    (hhead : ∀ q : Nat, q.Prime → q ≤ B.sampleData.W →
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation q (B.sampleData.value m)) =
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation q (B.sampleData.value m)) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    exact hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  refine ⟨hactiveSmooth, ⟨rowChange, ?_⟩, ?_⟩
  · calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
              (K := K) B R certificate deltaStar betaProt
                oldSeed newSeed outsideSelector houtsideActive a
      _ =
          (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData newSeed a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a := by
        rw [Finset.sum_sub_distrib]
      _ =
          bankPaperCanonicalLiteralActiveMass B.sampleData newSeed -
            bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed := by
        rw [
          sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
            B.sampleData newSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues,
          sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
            B.sampleData oldSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues]
      _ = (rowChange : Real) := hmass
  · intro q hqPrime hqW
    unfold
      bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a) *
          (a.factorization q : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) * valuation q a := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
              (K := K) B R certificate deltaStar betaProt
                oldSeed newSeed outsideSelector houtsideActive a]
          rfl
      _ =
          (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a * valuation q a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData oldSeed a * valuation q a := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
      _ =
          (∑ m : B.sampleData.Sample,
            newSeed m * valuation q (B.sampleData.value m)) -
          ∑ m : B.sampleData.Sample,
            oldSeed m * valuation q (B.sampleData.value m) := by
        rw [
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData newSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues q,
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData oldSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues q]
      _ = 0 := sub_eq_zero.mpr (hhead q hqPrime hqW)

/-! ## Recovering the old head moment from the literal source state -/

/-- The source-state support equation at head primes and the exact
post-height target moment identify the old rounded seed moment with the
fresh post-height seed moment.

The only target compatibility is the paper's literal one:
`activeHeadTarget` is the factorization of the selector-tail target at the
corresponding head prime. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_headMoments_eq_roundedSource_of_sourceState
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
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (htarget : ∀ p : {p : Nat // p ∈ P},
      p.1 ≤ B.sampleData.W →
        activeHeadTarget p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde)) :
    ∀ q : Nat, q.Prime → q ≤ B.sampleData.W →
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H m *
            valuation q (B.sampleData.value m)) =
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m) := by
  intro q hqPrime hqW
  have hqHead : q ∈ primesUpTo B.sampleData.W :=
    mem_primesUpTo.mpr ⟨hqPrime, hqW⟩
  let p : {p : Nat // p ∈ P} := ⟨q, hhead hqHead⟩
  have hqNotBand : q ∉ primeBand B.sampleData.n B.sampleData.W := by
    intro hqBand
    exact (not_lt_of_ge hqW) (mem_primeBand.mp hqBand).2.1
  have hdeficit :=
    Ssource.deficitSupportedOnPrimeBand q hqPrime hqNotBand
  have hsourceMoment :
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde a *
          (a.factorization q : Real)) =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := by
    unfold bankPaperCanonicalSelectorValuationDeficit at hdeficit
    linarith
  have hsourceAmbient :
      (∑ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde a *
          (a.factorization q : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate Tsource deltaStar betaProt
                  alpha qTilde) a *
            (a.factorization q : Real) := by
    apply Finset.sum_congr rfl
    intro a ha
    simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_mul_factorization_eq_ambient_of_headPrime
        (K := K) B R certificate deltaStar betaProt alpha beta
          (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
            B R certificate Tsource deltaStar betaProt alpha qTilde)
          hactiveSmooth hqPrime hqW ha)
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact
      (mem_completeRoughRowFiber.mp
        (hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr
            ⟨m, rfl⟩))).1
  have hold :
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m)) =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := by
    calc
      (∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m)) =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                B R certificate Tsource deltaStar betaProt
                  alpha qTilde) a *
            valuation q a := by
          symm
          exact
            sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
              B.sampleData
                (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
                  B R certificate Tsource deltaStar betaProt
                    alpha qTilde)
                (R.roughCanonicalGuardedCandidateSet
                  certificate deltaStar K)
                hvalues q
      _ =
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha beta qTilde a *
            (a.factorization q : Real) := by
          simpa only [valuation] using hsourceAmbient.symm
      _ =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := hsourceMoment
  have hnew :=
    bankPaperCanonicalSectionNinePostHeight_activeSeed_headMoment
      B I hlo hhi H hprime hpattern p
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          valuation q (B.sampleData.value m)) =
      activeHeadTarget p := by
        simpa only [p] using hnew
    _ =
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization q :
            Real) := by
      simpa only [p] using htarget p hqW
    _ =
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate Tsource deltaStar betaProt
                alpha qTilde m *
            valuation q (B.sampleData.value m) :=
      hold.symm

/-! ## The paper's `q0-d` prebridge ledger -/

/-- The literal rounded frozen-top source and the fresh post-height target
have the exact signed prebridge ledger.  The post-height input is
specialized to the literal rounded mass, so the total replacement mass is
definitionally `-d`. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridgeMomentLedger_of_sourceState
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
    (deltaStar betaProt alpha beta qTilde : Real)
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (hq0 : q0 =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (htarget : ∀ p : {p : Nat // p ∈ P},
      p.1 ≤ B.sampleData.W →
        activeHeadTarget p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde)) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) := by
  let oldSeed :=
    bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
      B R certificate Tsource deltaStar betaProt alpha qTilde
  let newSeed :=
    bankPaperCanonicalSectionNinePostHeightActiveSeed
      B I hlo hhi H
  have hmass :
      bankPaperCanonicalLiteralActiveMass B.sampleData newSeed -
          bankPaperCanonicalLiteralActiveMass B.sampleData oldSeed =
        ((-d : Int) : Real) := by
    dsimp only [newSeed, oldSeed]
    rw [
      bankPaperCanonicalSectionNinePostHeight_literalActiveMass_activeSeed,
      bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed]
    simp only [bankPaperCanonicalSectionNinePostHeightActiveMass_eq,
      Int.cast_neg]
    rw [hq0]
    ring
  have hmoments : ∀ q : Nat, q.Prime → q ≤ B.sampleData.W →
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation q (B.sampleData.value m)) =
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation q (B.sampleData.value m) := by
    simpa only [newSeed, oldSeed] using
      (bankPaperCanonicalSectionNinePostHeight_headMoments_eq_roundedSource_of_sourceState
        (K := K) B R certificate Tsource I hlo hhi H
          deltaStar betaProt alpha beta qTilde hprime hpattern
          hactiveSmooth hhead htarget Ssource)
  have hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate Tsource deltaStar betaProt
          alpha beta qTilde :=
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde hactiveSmooth hactiveBroad
  simpa only [
    oldSeed, newSeed,
    bankPaperCanonicalTopFrozenRoundedSourceSelector,
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using
    (bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_of_arbitrarySeedReplacement
      (K := K) B R certificate deltaStar betaProt oldSeed newSeed
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta oldSeed)
        hcompat hactiveSmooth (-d) hmass hmoments)

/-! ## Row quota and full placement -/

/-- The new prebridge ledger transports every complete-row integer quota
from the literal rounded source to the post-height placed preselector. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector_rowIntegral_of_sourceState
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
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde))
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H)) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
        B R certificate Tsource I hlo hhi H
          deltaStar betaProt alpha beta qTilde) := by
  simpa only [
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
    (bankPaperCanonicalSelectorRowIntegral_structuredAdditivePlacement_of_prebridgeMomentLedger
      B R certificate
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H)
        Ssource.rowIntegral hledger)

/-- Source feasibility, source row/support state, and the exact new
prebridge ledger give the complete guarded structured placement. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_structuredPlacement_of_sourceState
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
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde))
    (hplacedFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 ≤
          bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
            B R certificate Tsource I hlo hhi H
              deltaStar betaProt alpha beta qTilde a ∧
        bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
            B R certificate Tsource I hlo hhi H
              deltaStar betaProt alpha beta qTilde a ≤ 1)
    (hledger :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H)) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) := by
  apply
    bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H)
  · simpa only [
      bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
      bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
      hplacedFeasible
  · exact Ssource.rowIntegral
  · exact Ssource.deficitSupportedOnPrimeBand
  · exact hledger

/-! ## One-shot geometric source-to-post-height construction -/

/-- The literal finite source-to-post-height handoff in one theorem.

Physical interval and guard geometry supply smooth/broad support.  The
source state and selector-tail target supply the old row quotas and head
moments.  The post-height target supplies the new mass and head moments.
Finally, mass/cardinality geometry supplies `[0,1]` feasibility.

The output contains:

1. the signed source-to-`Tpost` prebridge ledger;
2. the actual active measure of exact mass `q0-d`;
3. the full structured placement, including all complete-row integer
   quotas and deficit support outside the tangent prime band.
-/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridge_actualMeasure_and_placement_of_sourceState
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
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperTwo : ∀ sigma, I.upper sigma ≤ 2)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hupperBroad : ∀ sigma,
      physicalBound (I.upper sigma) B.sampleData.n ≤
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (deltaStar betaProt alpha beta qTilde : Real)
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (hq0 : q0 =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
        B R certificate deltaStar betaProt alpha qTilde)
    (hqn : 1 ≤
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime exponent)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (htarget : ∀ p : {p : Nat // p ∈ P},
      p.1 ≤ B.sampleData.W →
        activeHeadTarget p =
          ((certificate.selectorTailTarget R
            (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
              Real))
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n ≤ B.sampleData.n)
    (hnotGuard : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde))
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density ≤ B.L) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H) ∧
      BankPaperCanonicalActualActiveMeasureConstructor B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) ∧
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
        B R certificate (R.paperFixedExceptionalFactors deltaStar)
          deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H) := by
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
      B R certificate deltaStar I hlowerOne hupperTwo hlo hhi
        hKh hnotGuard
  have hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K :=
    bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
      B I (upperTailLength c B.sampleData.n) K
        hlowerOne hupperTwo hlo hhi hupperBroad
  have hledger :=
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridgeMomentLedger_of_sourceState
      (K := K) B R certificate Tsource I hlo hhi
        deltaStar betaProt alpha beta qTilde H hq0 hprime hpattern
        hactiveSmooth hactiveBroad hhead htarget Ssource
  have hmeasureFeasible :=
    bankPaperCanonicalSectionNinePostHeightPlaced_actualMeasure_and_feasible_of_massAndCellDensity
      (K := K) B R certificate Tsource I hlowerOne hupperTwo hlo hhi H
        deltaStar betaProt alpha beta qTilde hqn hsep hKh hnotGuard
        hbetaProt
        (fun a ha => Ssource.feasible a ha)
        Cmass density hCmass hdensity hmass hcard hlarge
  have hplacement :=
    bankPaperCanonicalSectionNinePostHeightPlaced_structuredPlacement_of_sourceState
      (K := K) B R certificate Tsource I hlo hhi H
        deltaStar betaProt alpha beta qTilde Ssource
        (fun a ha => hmeasureFeasible.2 a ha)
        hledger
  exact ⟨hledger, hmeasureFeasible.1, hplacement⟩

end BankPaperRealization

end

end Erdos390.WholePaper
