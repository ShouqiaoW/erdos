import Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector
import Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration

/-!
# Feasibility reduction for the frozen-top sources

Exceptional nonsmooth rows of the frozen-top source are now pointwise zero.
Thus feasibility on the whole guarded candidate set reduces exactly to two
genuine inputs:

* feasibility on the guarded smooth row; and
* feasibility of the explicit corrected weight on active nonexceptional
  nonsmooth rows.

The first pair of finite theorems records this reduction for the general
frozen-top source and for its nearest-integer rounded specialization.  The
last pair discharges the active-row premise from the existing two-sided
slack theorem: on the guarded broad correction pool that theorem supplies
the box bounds, while off the pool the corrected weight is the feasible raw
weight.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Feasibility of one active corrected row -/

/-- Two-sided slack on the guarded broad correction pool, together with
the raw parameter box, proves `[0,1]` feasibility on the entire guarded
active row.  Outside the correction pool the corrected weight is literally
the raw head-compatible weight. -/
theorem
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mem_unitInterval_of_twoSidedSlack
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real}
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbeta : 0 <= beta / L ∧ beta / L <= 1)
    (hsigma : 0 <= sigma / L)
    (hfloor :
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| <=
        beta / L)
    (hceiling :
      beta / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| <=
        1 - sigma / L)
    {a : Nat}
    (_ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    0 <=
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ∧
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a <= 1 := by
  by_cases haPool :
      a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K label
  · have hslack :=
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
        hfloor hceiling haPool
    exact
      ⟨hsigma.trans hslack.1,
        hslack.2.trans (sub_le_self 1 hsigma)⟩
  · rw [roughCanonicalGuardedPostchargeRowCorrectedWeight,
      bankPaperConstantPoolCorrection_apply_of_not_mem haPool]
    exact roughHeadCompatibleRawWeight_mem_unitInterval halpha hbeta a

/-! ## Classification reduction on the guarded candidate set -/

/-- The general frozen-top source is feasible on the full guarded candidate
set once its smooth row and its explicit active nonexceptional corrected
rows are feasible.  Exceptional nonsmooth rows require no premise because
the source is pointwise zero there. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_active
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
    (hsmooth : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1)
    (hactive : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          0 <=
              R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha beta B.L a ∧
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha beta B.L a <= 1) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1 := by
  intro a ha
  by_cases hlabel :
      completeRoughLabel (yNat B.sampleData.n) a = 1
  · have haSmooth :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, hlabel⟩)
    exact hsmooth a haSmooth
  · have haRow :
        a ∈ R.roughCanonicalGuardedRow certificate deltaStar K
          (completeRoughLabel (yNat B.sampleData.n) a) := by
      simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
        (mem_completeRoughRowFiber.mpr ⟨ha, rfl⟩)
    rcases roughCanonical_activeNonexceptional_or_exceptional
        (n := B.sampleData.n) (deltaStar := deltaStar) hlabel with
      hactiveLabel | hexceptional
    · rw [
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
          (K := K) B R certificate deltaStar betaProt alpha beta oldSeed
            hactiveLabel haRow]
      exact hactive _ hactiveLabel a haRow
    · rw [
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_exceptionalNonsmoothRow
          (K := K) B R certificate deltaStar betaProt alpha beta oldSeed
            hlabel hexceptional haRow]
      exact ⟨le_rfl, zero_le_one⟩

/-- The same classification reduction for the nearest-integer rounded
frozen-top selector.  Its nonsmooth rows are independent of the rounded
active seed, so the active premise is the identical corrected-row premise
used by the unrounded source. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_smooth_of_active
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
    (hsmooth : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1)
    (hactive : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          0 <=
              R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha betaTotal B.L a ∧
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
                deltaStar B.sampleData.W K label alpha betaTotal B.L a <= 1) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1 := by
  simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
    (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_active
      (K := K) B R certificate deltaStar betaProt alpha betaTotal
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        (by
          intro a ha
          simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
            hsmooth a ha)
        hactive)

/-! ## Closing the active premise by two-sided slack -/

/-- The raw parameter box and the existing two-sided correction-pool slack
close the active-row premise in the general frozen-top feasibility
reduction. -/
theorem
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_twoSidedSlack
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
    (deltaStar betaProt alpha beta sigma : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbeta : 0 <= beta / B.L ∧ beta / B.L <= 1)
    (hsigma : 0 <= sigma / B.L)
    (hsmooth : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1)
    (hfloor : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L)
    (hceiling : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a ∧
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed a <= 1 := by
  apply
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_smooth_of_active
      (K := K) B R certificate deltaStar betaProt alpha beta oldSeed hsmooth
  intro label hactiveLabel a ha
  exact
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mem_unitInterval_of_twoSidedSlack
      (R := R) (certificate := certificate) halpha hbeta hsigma
        (hfloor label hactiveLabel) (hceiling label hactiveLabel) ha

/-- The nearest-integer rounded selector is globally feasible under its
smooth-row feasibility and the same raw-box/two-sided-slack data on active
nonsmooth rows. -/
theorem
    bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_smooth_of_twoSidedSlack
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
    (deltaStar betaProt alpha betaTotal qTilde sigma : Real)
    (halpha : 0 <= alpha ∧ alpha <= 1)
    (hbeta : 0 <= betaTotal / B.L ∧ betaTotal / B.L <= 1)
    (hsigma : 0 <= sigma / B.L)
    (hsmooth : ∀ a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1)
    (hfloor : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha betaTotal B.L| <=
          betaTotal / B.L)
    (hceiling : ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        betaTotal / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha betaTotal B.L| <=
          1 - sigma / B.L) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a ∧
        bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate T deltaStar betaProt alpha betaTotal qTilde a <= 1 := by
  apply
    bankPaperCanonicalTopFrozenRoundedSourceSelector_feasible_of_smooth_of_active
      (K := K) B R certificate T deltaStar betaProt alpha betaTotal qTilde
        hsmooth
  intro label hactiveLabel a ha
  exact
    roughCanonicalGuardedPostchargeRowCorrectedWeight_mem_unitInterval_of_twoSidedSlack
      (R := R) (certificate := certificate) halpha hbeta hsigma
        (hfloor label hactiveLabel) (hceiling label hactiveLabel) ha

end BankPaperRealization

end

end Erdos390.WholePaper
