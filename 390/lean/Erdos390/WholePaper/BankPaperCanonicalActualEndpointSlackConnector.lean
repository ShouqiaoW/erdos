import Erdos390.WholePaper.BankPaperProposition87ActualDataConnector
import Erdos390.WholePaper.BankPaperCanonicalProposition87EndpointSlack

/-!
# Actual paper-data connector for guarded P87 endpoint slack

This file joins the literal Proposition 8.7 data realization to the guarded
smooth-row slack theorem.  The actual frozen tag at a guarded candidate has
weight

`preSelector a - activeSeedAmbient a`.

Guarded broad-pool containment and nonnegativity of the active seed are
already consequences of the existing finite ledger and active-measure
constructor, so they disappear here.  The only quantitative smooth-row
inputs left visible are exactly the paper estimates

* `sigma / L + activeSeedAmbient a <= preSelector a`, the protected reserve;
* `preSelector a <= Cfixed / L`, the raw broad upper bound.

The second theorem then identifies the generic frozen-plus-active endpoint
with `bankPaperCanonicalActualP87EndpointSelector` definitionally and
supplies its two-sided smooth tangent slack.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The literal protected window -/

/-- The actual frozen remainder has the required protected window once the
two literal broad-selector estimates are known.  Pool containment and
active-seed nonnegativity are derived, not repeated as premises. -/
theorem bankPaperCanonicalActualSmoothProtectedWindow_of_reserve
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
    (sigma Cfixed : Real)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        preSelector x)
    (hpreUpper : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      preSelector x <= Cfixed / B.L) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      sigma Cfixed := by
  have hpool :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 ⊆
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro x hx
    exact (mem_completeRoughRowFiber.mp
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 hx)).1
  have hactiveNonneg : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= bankPaperCanonicalActiveSeedAmbientWeight
        B.sampleData activeSeed x := by
    intro x _hx
    exact bankPaperCanonicalActiveSeedAmbientWeight_nonneg Hmeasure x
  simpa only [bankPaperCanonicalActualFrozenValue,
      bankPaperCanonicalActualFrozenWeight] using
    (bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeRemainder
      B R certificate deltaStar
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      preSelector
      (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed)
      sigma Cfixed hpool hactiveNonneg hprotectedReserve hpreUpper)

/-! ## Smooth slack for the actual endpoint -/

/-- The actual P87 endpoint has the protected lower floor and strict upper
reserve on every guarded smooth broad coordinate.  The active upper bound is
derived from the P87 effective box.  The only selector-specific quantitative
premises are the protected reserve and raw broad upper bound displayed in the
preceding theorem. -/
theorem exists_bankPaperCanonicalActualP87EndpointSelector_smoothSlackLayers
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        preSelector x)
    (hpreUpper : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      preSelector x <= Cfixed / B.L)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L) :
    ∃ protectedPart active : Nat -> Real,
      ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        bankPaperCanonicalActualP87EndpointSelector B
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              preSelector activeSeed path x =
            protectedPart x + active x ∧
          sigma / B.L <= protectedPart x ∧
          0 <= active x ∧
          protectedPart x + active x <= 1 - sigma / B.L := by
  have hprotected :=
    bankPaperCanonicalActualSmoothProtectedWindow_of_reserve
      B R certificate deltaStar preSelector activeSeed Hmeasure
        sigma Cfixed hprotectedReserve hpreUpper
  have hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L := by
    intro m
    rw [hseed m]
    exact hactiveSeed m
  simpa only [bankPaperCanonicalActualP87EndpointSelector] using
    (exists_bankPaperProposition87EndpointSelector_smoothSlackLayers
      B R certificate deltaStar Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      quota path Hpath C sigma Cfixed Cactive hC hW hhi hsep hCactive
      hactive hprotected hlarge)

/-! ## Actual endpoint plus nonsmooth correction -/

/-- Join the actual smooth P87 endpoint to the existing nonsmooth
constant-pool correction.  On a nonsmooth row the structured active seed
vanishes by complete-rough-label separation, so the actual frozen remainder
is just `preSelector`; consequently the nonsmooth identification premise is
stated directly for that selector rather than for an opaque frozen layer. -/
theorem bankPaperCanonicalActualP87EndpointSelector_guardedSlackConstruction_of_reserve
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        preSelector x)
    (hpreUpper : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      preSelector x <= Cfixed / B.L)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L)
    (hpreNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          preSelector x =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L x) :
    R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar B.sampleData.W K alpha beta B.L sigma
      (bankPaperCanonicalActualP87EndpointSelector B
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed path) := by
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  have hprotected :=
    bankPaperCanonicalActualSmoothProtectedWindow_of_reserve
      B R certificate deltaStar preSelector activeSeed Hmeasure
        sigma Cfixed hprotectedReserve hpreUpper
  have hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L := by
    intro m
    rw [hseed m]
    exact hactiveSeed m
  have hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates := by
    intro m
    exact bankPaperCanonicalActiveSeed_value_mem_candidates Hmeasure m
  have hactiveSmooth : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    have hm := bankPaperCanonicalActualActiveValues_subset_smoothRow
      B candidates hvalues
        (mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩)
    simpa only [candidates, roughCanonicalGuardedRow] using hm
  have hfrozenNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          BridgeData.frozenAmbientWeight
              (bankPaperCanonicalActualFrozenValue
                (candidates := candidates))
              (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
                preSelector activeSeed) x =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L x := by
    intro label hlabel x hx
    rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
    have hxCandidate : x ∈ candidates := by
      exact (mem_completeRoughRowFiber.mp
        (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
          certificate deltaStar B.sampleData.W K label hx)).1
    rw [if_pos hxCandidate]
    have hseedZero :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hmx
      have hxSmooth : x ∈
          R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
        simpa only [hmx] using hactiveSmooth m
      have hxLabel : x ∈
          R.roughCanonicalGuardedRow certificate deltaStar K label :=
        R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
          certificate deltaStar B.sampleData.W K label hx
      have hsmoothEq := (mem_completeRoughRowFiber.mp hxSmooth).2
      have hlabelEq := (mem_completeRoughRowFiber.mp hxLabel).2
      exact hlabel.1 (hlabelEq.symm.trans hsmoothEq)
    rw [hseedZero, sub_zero]
    exact hpreNonsmooth label hlabel x hx
  simpa only [bankPaperCanonicalActualP87EndpointSelector, candidates] using
    (guardedEndpointSlackConstruction_of_proposition87EndpointSelector
      B R certificate deltaStar alpha beta Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
      quota path Hpath C sigma Cfixed Cactive hC hW hhi hsep hCactive
      hactive hprotected hlarge hactiveSmooth hnonsmoothBounds
      hfrozenNonsmooth)

end BankPaperRealization

end

end Erdos390.WholePaper
