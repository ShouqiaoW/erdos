import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstFiniteAssembly
import Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateEventualConnector

/-!
# Source-first actual-data identities

This module supplies the two finite facts needed to build the exact Section 8
ledger before the post-height bridge.

* The pre-rounding global corrected source selector, paired with the genuine
  barycentric scaled seed, satisfies the actual active-measure constructor.
* Floating rounding changes the selector and its ambient seed by exactly the
  same pointwise amount.  Hence their frozen remainder, and therefore its
  literal logarithmic mass, is unchanged.

These are exact finite statements.  They contain no asymptotic estimate or
ledger hypothesis.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## The pre-rounding actual active measure -/

/-- The source-first corrected selector paired with the literal scaled
barycentric seed is an honest actual active-measure constructor. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_actualActiveMeasureConstructor
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
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hqTilde : 1 ≤ qTilde)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (halpha : 0 ≤ alpha ∧ alpha ≤ 1)
    (hbetaProtBox :
      0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1)
    (hselectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 ≤
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde) a) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))
      (bankPaperCanonicalScaledActiveSeed T qTilde) := by
  apply bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
    B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
        B R certificate deltaStar betaProt alpha betaTotal
          (bankPaperCanonicalScaledActiveSeed T qTilde))
      qTilde hqTilde hsep
  · intro m
    exact
      (mem_completeRoughRowFiber.mp
        (hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr
            ⟨m, rfl⟩))).1
  · exact hselectorNonneg
  · unfold BankPaperCanonicalActualCoordinateFit
    intro m
    have hmSmooth :
        B.sampleData.value m ∈
          R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
      hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr
          ⟨m, rfl⟩)
    rw [
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_smoothRow
        (K := K) B R certificate
          (bankPaperCanonicalScaledActiveSeed T qTilde) hmSmooth,
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value_of_headPatternsSeparated
        B.sampleData (bankPaperCanonicalScaledActiveSeed T qTilde)
          hsep m]
    exact le_add_of_nonneg_left
      (roughHeadCompatibleRawWeight_mem_unitInterval
        (W := B.sampleData.W) (n := B.sampleData.n)
        (h := upperTailLength c B.sampleData.n) (K := K)
        (α := alpha) (β := betaProt) (L := B.L)
        halpha hbetaProtBox (B.sampleData.value m)).1

/-! ## Exact frozen-log invariance under floating rounding -/

/-- The rounded source pair and the pre-rounding scaled source pair have
exactly the same literal frozen logarithmic mass. -/
theorem
    bankPaperCanonicalTopFrozenRounded_actualFrozenLogMass_eq_qTildeSource
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
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha betaTotal qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde) =
      bankPaperCanonicalActualFrozenLogMass B.sampleData fixed bankBase
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha betaTotal
            (bankPaperCanonicalScaledActiveSeed T qTilde))
        (bankPaperCanonicalScaledActiveSeed T qTilde) := by
  classical
  have hcandidate :
      (∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde)
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a *
          Real.log
            (bankPaperCanonicalActualFrozenValue a : Real)) =
        ∑ a : BankPaperCanonicalActualFrozenIndex
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K),
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
              (K := K) B R certificate deltaStar betaProt alpha
                betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde))
            (bankPaperCanonicalScaledActiveSeed T qTilde) a *
          Real.log
            (bankPaperCanonicalActualFrozenValue a : Real) := by
    apply Finset.sum_congr rfl
    intro a _ha
    have hdiff :=
      bankPaperCanonicalTopFrozenRoundedSourceSelector_sub_qTildeSource_eq_ambient_sub
        (K := K) B R certificate T deltaStar betaProt alpha
          betaTotal qTilde hactiveSmooth a.2
    have hweight :
        bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
              B R certificate T deltaStar betaProt alpha betaTotal
                qTilde)
            (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
              B R certificate T deltaStar betaProt alpha qTilde) a =
          bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K)
            (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
              (K := K) B R certificate deltaStar betaProt alpha
                betaTotal
                (bankPaperCanonicalScaledActiveSeed T qTilde))
            (bankPaperCanonicalScaledActiveSeed T qTilde) a := by
      unfold bankPaperCanonicalActualFrozenWeight
      linarith only [hdiff]
    rw [hweight]
  unfold bankPaperCanonicalActualFrozenLogMass
  rw [hcandidate]

end BankPaperRealization

end

end Erdos390.WholePaper
