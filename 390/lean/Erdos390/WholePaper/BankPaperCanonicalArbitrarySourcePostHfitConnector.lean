import Erdos390.WholePaper.BankPaperCanonicalPostHfitSlackConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateConnector

/-!
# Post-Hfit production from an arbitrary verified source

The original Post-Hfit connector fixes
`bankPaperCanonicalPostHfitGlobalSourceSelector` in both its placement and
its output package.  This file separates the part of that construction which
only needs a verified selector source state from the identities special to
that old source.

For an arbitrary `sourceSelector`, the exact additional inputs are:

* the signed whole-smooth-row prebridge ledger for `placementSeed`;
* pointwise feasibility of the resulting structured placement; and
* the nonsmooth-row identification of the source.

The source state supplies row integrality and exact agreement outside the
medium-prime band.  The prebridge theorem transports those two fields to the
structured placement.  Everything after that point--Proposition 8.7, the
split-seed endpoint, the rounded tangent input, and endpoint slack--is
source-agnostic.

The final section specializes this producer to the frozen-top
nearest-integer selector.  Its nonsmooth-row identification is proved here,
so the specialization does not route through the older no-top global source.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Source-parameterized preselector and package -/

/-- The structured Post-Hfit preselector built from an arbitrary base
selector and an independently supplied placement seed. -/
def bankPaperCanonicalPostHfitStructuredPreSelectorOfSource
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
    (deltaStar betaProt : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
    B R certificate deltaStar betaProt sourceSelector placementSeed

/-- The complete finite Post-Hfit output for an arbitrary verified source.

Unlike `BankPaperCanonicalPostHfitGuardedSlackPackage`, this package does
not hide a particular source definition or a particular two-cell placement
seed.  It records those two objects as parameters. -/
def BankPaperCanonicalPostHfitGuardedSlackPackageOfSource
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
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta sigma : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (radius : NNReal) (Cpost : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (quota : Int) (path : Real -> B.ParamSpace)
    (endpoint : Nat -> Real) : Prop :=
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let preSelector :=
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
      B R certificate deltaStar betaProt sourceSelector placementSeed
  let markedTarget :=
    bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
      candidates preSelector activeSeed
  let Delta := fun j => B.markedBandResidual markedTarget 0 j
  BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt
        sourceSelector placementSeed ∧
    B.HasPaperProposition87Conclusion
      Delta radius markedTarget B.q Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        preSelector activeSeed)
      quota ∧
    B.IsPaperProposition87Path
      Delta radius markedTarget B.q Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight B.sampleData candidates
        preSelector activeSeed)
      quota path ∧
    endpoint =
      bankPaperCanonicalActualP87EndpointSelector B candidates
        preSelector activeSeed path ∧
    BankPaperCanonicalRoundedSelectorTangentInput R certificate fixed
      candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
      (tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        B.partition.band cellIndex)
      endpoint ∧
    R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar B.sampleData.W K alpha beta B.L sigma endpoint

/-! ## Generic slack inputs -/

/-- On the smooth correction pool, the structured placement has the same
`O(1/L)` upper bound for every base selector.  The base selector is
overwritten on that pool, so no source-specific identity is used. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreUpper
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
    (deltaStar betaProt : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cplacement / B.L)
    (Cfixed : Real) (hfixed : betaProt + Cplacement <= Cfixed) :
    ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt sourceSelector placementSeed a <=
        Cfixed / B.L := by
  intro a ha
  rw [bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
      B R certificate sourceSelector placementSeed ha,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate sourceSelector placementSeed ha]
  have hambient :=
    bankPaperCanonicalActiveSeedAmbientWeight_le_of_pointwise
      B hsep placementSeed Cplacement hCplacement hplacementSeedUpper a
  calc
    betaProt / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData placementSeed a <=
        betaProt / B.L + Cplacement / B.L :=
      add_le_add le_rfl hambient
    _ = (betaProt + Cplacement) / B.L := by ring
    _ <= Cfixed / B.L :=
      div_le_div_of_nonneg_right hfixed B.L_pos.le

/-- A source identity on nonsmooth active rows passes unchanged through the
structured placement, provided the structured active image is contained in
the smooth row. -/
theorem bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreNonsmooth
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
    (deltaStar betaProt alpha beta : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hsourceNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          sourceSelector a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a) :
    forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
                B R certificate deltaStar betaProt
                  sourceSelector placementSeed a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a := by
  intro label hlabel a ha
  have hnotSmoothRow :
      a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_not_mem_smoothRow_of_ne_one
      certificate hlabel.1 ha
  rw [bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
      B R certificate sourceSelector placementSeed hactiveSmooth
        hnotSmoothRow]
  exact hsourceNonsmooth label hlabel a ha

/-! ## Arbitrary-source producer -/

/-- Produce the exact Post-Hfit endpoint and slack package from any verified
selector source state.

The source state is used, rather than merely carried: its row-integrality
and outside-band support fields are transported across the supplied signed
prebridge ledger. -/
theorem
    exists_bankPaperCanonicalPostHfitGuardedSlackPackageOfSource_of_sourceState
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
    (fixed : Finset Nat)
    (deltaStar betaProt alpha beta sigma : Real)
    (sourceSelector : Nat -> Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      sourceSelector)
    (hplacedFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed a ∧
        bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed a <= 1)
    (hprebridge :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          sourceSelector placementSeed)
    (hsourceNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          sourceSelector a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
        B R certificate deltaStar betaProt sourceSelector placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
            B R certificate deltaStar betaProt
              sourceSelector placementSeed)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
            B R certificate deltaStar betaProt
              sourceSelector placementSeed) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
              B R certificate deltaStar betaProt
                sourceSelector placementSeed)
            activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cplacement / B.L)
    (hfixed : betaProt + Cplacement <= Cfixed)
    (C : Real) (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hCactive : 0 <= Cactive)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt
            sourceSelector placementSeed x)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
      BankPaperCanonicalPostHfitGuardedSlackPackageOfSource (K := K)
        B R certificate fixed deltaStar betaProt alpha beta sigma
          sourceSelector placementSeed activeSeed radius Cpost cellIndex
          quota path endpoint := by
  have Hplacement :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
        B R certificate fixed deltaStar betaProt
          sourceSelector placementSeed := by
    exact
      bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
        B R certificate fixed sourceSelector placementSeed
          hplacedFeasible Ssource.rowIntegral
            Ssource.deficitSupportedOnPrimeBand hprebridge
  have hpreUpper :=
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreUpper
      (K := K) B R certificate deltaStar betaProt sourceSelector
        placementSeed hsep Cplacement hCplacement hplacementSeedUpper
        Cfixed hfixed
  have hpreNonsmooth :=
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource_hpreNonsmooth
      (K := K) B R certificate deltaStar betaProt alpha beta
        sourceSelector placementSeed hprebridge.1 hsourceNonsmooth
  obtain ⟨quota, path, endpoint, Hfit, Hpath, hendpoint, Sendpoint⟩ :=
    exists_bankPaperCanonicalActualP87EndpointSelector_of_localCanonical_structuredAdditivePlacement_splitSeed
      (K := K) B R certificate fixed deltaStar betaProt
        sourceSelector placementSeed activeSeed Hmeasure hseed
        Hplacement hsep Ctarget Cinitial Cfixed Cactive henv hdeficit
        hfrozenLedger hactiveLedger radius Cpost hP87 cellIndex
  have hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L := by
    intro m
    rw [← hseed m]
    exact hactiveLedger m
  have HslackActual :=
    bankPaperCanonicalActualP87EndpointSelector_guardedSlackConstruction_of_reserve
      (K := K) B R certificate deltaStar alpha beta
      (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
        B R certificate deltaStar betaProt sourceSelector placementSeed)
      activeSeed Hmeasure hseed
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
            B R certificate deltaStar betaProt
              sourceSelector placementSeed)
          activeSeed) 0 j)
      radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
          B R certificate deltaStar betaProt sourceSelector placementSeed)
        activeSeed)
      B.q Cpost quota path Hpath C sigma Cfixed Cactive
      hC hW hhi hsep hCactive hactiveSeed hprotectedReserve hpreUpper
      hlarge hnonsmoothBounds hpreNonsmooth
  have Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W K alpha beta B.L sigma endpoint := by
    rw [hendpoint]
    exact HslackActual
  refine ⟨quota, path, endpoint, ?_⟩
  unfold BankPaperCanonicalPostHfitGuardedSlackPackageOfSource
  exact ⟨Hplacement, Hfit, Hpath, hendpoint, Sendpoint, Hslack⟩

/-! ## Frozen-top rounded specialization -/

/-- The source-parameterized preselector specialized to the exact
nearest-integer frozen-top source. -/
def bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
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
    (deltaStar betaProt alpha beta qTilde : Real)
    (placementSeed : B.sampleData.Sample -> Real) : Nat -> Real :=
  bankPaperCanonicalPostHfitStructuredPreSelectorOfSource (K := K)
    B R certificate deltaStar betaProt
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha beta qTilde)
      placementSeed

/-- Frozen-top specialization of the arbitrary-source output package. -/
def BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
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
    (T : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde sigma : Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (radius : NNReal) (Cpost : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (quota : Int) (path : Real -> B.ParamSpace)
    (endpoint : Nat -> Real) : Prop :=
  BankPaperCanonicalPostHfitGuardedSlackPackageOfSource (K := K)
    B R certificate fixed deltaStar betaProt alpha beta sigma
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate T deltaStar betaProt alpha beta qTilde)
      placementSeed activeSeed radius Cpost cellIndex quota path endpoint

/-- The nearest-integer frozen-top source has the exact nonsmooth identity
required by the source-parameterized Post-Hfit producer. -/
theorem bankPaperCanonicalTopFrozenRoundedSourceSelector_hsourceNonsmooth
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
    (deltaStar betaProt alpha beta qTilde : Real) :
    forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
                B R certificate T deltaStar betaProt alpha beta qTilde a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L a := by
  intro label hlabel a ha
  have haRow :
      a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K label ha
  simpa only [bankPaperCanonicalTopFrozenRoundedSourceSelector] using
    (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_apply_of_mem_nonsmoothRow
      (K := K) B R certificate deltaStar betaProt alpha beta
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
          B R certificate T deltaStar betaProt alpha qTilde)
        hlabel haRow)

/-- Run Post-Hfit directly from the verified nearest-integer frozen-top
source state.  No equality with
`bankPaperCanonicalPostHfitGlobalSourceSelector` is assumed. -/
theorem
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_sourceState
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
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde sigma : Real)
    (placementSeed activeSeed : B.sampleData.Sample -> Real)
    (Ssource : BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt alpha beta qTilde))
    (hplacedFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <=
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed a ∧
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed a <= 1)
    (hprebridge :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K) B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt alpha beta qTilde)
          placementSeed)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K) B R certificate Tsource deltaStar betaProt alpha beta
          qTilde placementSeed)
      activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed)
          activeSeed) 0 j))
    (hdeficit : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K) B R certificate Tsource deltaStar betaProt alpha beta
              qTilde placementSeed) p) <=
        Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K) B R certificate Tsource deltaStar betaProt alpha beta
                qTilde placementSeed)
            activeSeed)
          (B.sampleData.value m) <= Cfixed / B.L)
    (hactiveLedger : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (radius : NNReal) (Cpost : Real)
    (hP87 :
      forall (Delta : Band -> Real),
        B.HasTargetEnvelopes Ctarget Delta ->
        forall (markedTarget : Nat -> Real) (N : Real),
          0 <= N ->
          B.q <= (1 : Real) * N ->
          (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
            abs (markedTarget p -
              B.paperMoment (B.markedValuation p) 0) <=
                Cinitial * N / ((p : Real) * B.L)) ->
          (forall j,
            Delta j = B.markedBandResidual markedTarget 0 j) ->
          forall {Fixed : Type} [Fintype Fixed]
            (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q ->
            B.sampleData.HeadPatternsSeparated ->
            (forall x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) ->
            (forall m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                (B.sampleData.value m) <= Cfixed / B.L) ->
            (forall m : B.sampleData.Sample,
              B.baseline.baseWeight m <= Cactive / B.L) ->
            B.HasPaperProposition87Conclusion Delta radius
              markedTarget N Cpost fixedValue fixedWeight quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (Cplacement : Real) (hCplacement : 0 <= Cplacement)
    (hplacementSeedUpper : forall m : B.sampleData.Sample,
      placementSeed m <= Cplacement / B.L)
    (hfixed : betaProt + Cplacement <= Cfixed)
    (C : Real) (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hCactive : 0 <= Cactive)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed x <=
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K) B R certificate Tsource deltaStar betaProt alpha beta
            qTilde placementSeed x)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L) :
    ∃ quota : Int, ∃ path : Real -> B.ParamSpace,
    ∃ endpoint : Nat -> Real,
      BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
        (K := K) B R certificate fixed Tsource deltaStar betaProt alpha
          beta qTilde sigma placementSeed activeSeed radius Cpost cellIndex
          quota path endpoint := by
  simpa only [
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage] using
    (exists_bankPaperCanonicalPostHfitGuardedSlackPackageOfSource_of_sourceState
      (K := K) B R certificate fixed deltaStar betaProt alpha beta sigma
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt alpha beta qTilde)
        placementSeed activeSeed Ssource hplacedFeasible hprebridge
        (bankPaperCanonicalTopFrozenRoundedSourceSelector_hsourceNonsmooth
          (K := K) B R certificate Tsource deltaStar betaProt alpha beta
            qTilde)
        Hmeasure hseed hsep Ctarget Cinitial Cfixed Cactive henv hdeficit
        hfrozenLedger hactiveLedger radius Cpost hP87 cellIndex
        Cplacement hCplacement hplacementSeedUpper hfixed C hC hW hhi
        hCactive hprotectedReserve hlarge hnonsmoothBounds)

end BankPaperRealization

end

end Erdos390.WholePaper
