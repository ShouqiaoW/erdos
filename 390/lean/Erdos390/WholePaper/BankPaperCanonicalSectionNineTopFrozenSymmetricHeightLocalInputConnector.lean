import Erdos390.WholePaper.BankPaperCanonicalSectionNineSymmetricHeightLocalInputConnector
import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector

/-!
# Finite Section 9 inputs for the frozen-top symmetric-height source

The older symmetric-height finite interface fixes
`bankPaperCanonicalPostHfitGlobalSourceSelector`.  The literal frozen-top
construction instead starts from
`bankPaperCanonicalTopFrozenRoundedSourceSelector`, and these two selectors
are not identified here.

This file records a selector-correct first finite layer.  It reuses
`BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt` for the common
geometry and scalar data, but states every premise consumed by the
arbitrary-source Post-hfit producer for the actual frozen-top selector.
In particular, the placement seed and active seed are explicit, and their
compatibility with the active measure and bridge baseline is carried by
fields rather than a hidden definitional equality.

The output is exactly the frozen-top rounded Post-hfit guarded-slack
package.  No Section 9 distributed geometry or asymptotic conclusion is
asserted.
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

/-! ## Selector-correct finite inputs -/

/-- The selector and measure data for the literal frozen-top source.

`Tsource` and `qTilde` belong to the source selector.  They are deliberately
independent of the target and normalization data stored in `core`.  The
actual Post-hfit placement and active seeds are also explicit.  The last
four fields are precisely the source-state, feasibility, prebridge, and
active-measure premises of the arbitrary-source producer. -/
structure BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar : Real) where
  core : BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
    B R certificate K0 deltaStar
  Tsource : BarycentricTarget B.sampleData
  alpha : Real
  beta : Real
  qTilde : Real
  placementSeed : B.sampleData.Sample → Real
  activeSeed : B.sampleData.Sample → Real
  sourceState :
    BankPaperCanonicalSelectorSourceState
      (W := B.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
        B R certificate Tsource deltaStar core.betaProt alpha beta qTilde)
  placedFeasible :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1),
      0 ≤
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate Tsource deltaStar
              core.betaProt alpha beta qTilde placementSeed a ∧
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate Tsource deltaStar
              core.betaProt alpha beta qTilde placementSeed a ≤ 1
  prebridge :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
      (K := K0 + 1) B R certificate deltaStar core.betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
          B R certificate Tsource deltaStar core.betaProt alpha beta qTilde)
        placementSeed
  activeMeasure :
    BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData core.T
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K0 + 1) B R certificate Tsource deltaStar
          core.betaProt alpha beta qTilde placementSeed)
      activeSeed
  baseline_seed :
    ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m

/-- The analytic and numerical tail for a frozen-top source.

The fields follow the quantifier order of
`exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_sourceState`.
Every target, deficit, ledger, and reserve assertion names the same literal
frozen-top preselector stored in `S`; no compatibility with the legacy
global source selector is postulated. -/
structure
    BankPaperCanonicalSectionNineTopFrozenSymmetricHeightDependentInputsAt
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (S :
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
        B R certificate K0 deltaStar) where
  Ctarget : Real
  Cinitial : Real
  Cfixed : Real
  Cactive : Real
  radius : NNReal
  targetEnvelopes :
    B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate S.Tsource deltaStar
              S.core.betaProt S.alpha S.beta S.qTilde S.placementSeed)
          S.activeSeed) 0 j)
  selectorDeficit :
    ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate S.Tsource deltaStar
              S.core.betaProt S.alpha S.beta S.qTilde S.placementSeed) p) ≤
        Cinitial * B.q / ((p : Real) * B.L)
  frozenLedger :
    ∀ m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1)))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) B R certificate S.Tsource deltaStar
                S.core.betaProt S.alpha S.beta S.qTilde S.placementSeed)
            S.activeSeed)
          (B.sampleData.value m) ≤ Cfixed / B.L
  activeLedger :
    ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L
  localP87 :
    ∀ (Delta : Band → Real),
      B.HasTargetEnvelopes Ctarget Delta →
      ∀ (markedTarget : Nat → Real) (N : Real),
        0 ≤ N →
        B.q ≤ (1 : Real) * N →
        (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
          abs (markedTarget p -
            B.paperMoment (B.markedValuation p) 0) ≤
              Cinitial * N / ((p : Real) * B.L)) →
        (∀ j, Delta j = B.markedBandResidual markedTarget 0 j) →
        ∀ {Fixed : Type} [Fintype Fixed],
          ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) + B.q →
            B.sampleData.HeadPatternsSeparated →
            (∀ x,
              BridgeData.frozenAmbientWeight
                fixedValue fixedWeight x ∈ Icc (0 : Real) 1) →
            (∀ m : B.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤
                Cfixed / B.L) →
            (∀ m : B.sampleData.Sample,
              B.baseline.baseWeight m ≤ Cactive / B.L) →
            B.HasPaperProposition87Conclusion
              Delta radius markedTarget N Cpost
                fixedValue fixedWeight quota
  cellIndex : BankPaperCanonicalTangentPrime
    B.sampleData.n B.sampleData.W → Nat
  Cplacement : Real
  Cplacement_nonneg : 0 ≤ Cplacement
  placementSeedUpper :
    ∀ m : B.sampleData.Sample,
      S.placementSeed m ≤ Cplacement / B.L
  fixedRoom :
    S.core.betaProt + Cplacement ≤ Cfixed
  C : Real
  C_one_le : 1 ≤ C
  W_large : 1 < B.sampleData.W
  physicalUpper :
    ∀ sign, B.sampleData.hi sign ≤ physicalBound C B.sampleData.n
  Cactive_nonneg : 0 ≤ Cactive
  protectedReserve :
    ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W (K0 + 1) 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData S.activeSeed x ≤
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
          (K := K0 + 1) B R certificate S.Tsource deltaStar
            S.core.betaProt S.alpha S.beta S.qTilde S.placementSeed x
  largeL :
    Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) *
          Cactive + sigma ≤
      B.L
  nonsmooth :
    ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          B.sampleData.n deltaStar label →
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W (K0 + 1) label
                S.alpha S.beta B.L| ≤
          S.beta / B.L ∧
        S.beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W (K0 + 1) label
                S.alpha S.beta B.L| ≤
          1 - sigma / B.L

/-! ## Finite package producer -/

/-- Produce the frozen-top rounded Post-hfit package from the exact
selector-correct source and dependent fields.

This theorem is a direct finite specialization of the audited
arbitrary-source producer.  In particular, it never rewrites the frozen-top
selector to `bankPaperCanonicalPostHfitGlobalSourceSelector`. -/
theorem
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_symmetricHeightInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma Cpost : Real)
    (S :
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
        B R certificate K0 deltaStar)
    (A :
      BankPaperCanonicalSectionNineTopFrozenSymmetricHeightDependentInputsAt
        B R certificate K0 deltaStar sigma Cpost S) :
    ∃ quota : Int, ∃ path : Real → B.ParamSpace,
      ∃ endpoint : Nat → Real,
        BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
          (K := K0 + 1) B R certificate
          (R.paperFixedExceptionalFactors deltaStar) S.Tsource
          deltaStar S.core.betaProt S.alpha S.beta S.qTilde sigma
          S.placementSeed S.activeSeed A.radius Cpost A.cellIndex
          quota path endpoint := by
  exact
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_sourceState
      (K := K0 + 1) (T := S.core.T) B R certificate
      (R.paperFixedExceptionalFactors deltaStar) S.Tsource
      deltaStar S.core.betaProt S.alpha S.beta S.qTilde sigma
      S.placementSeed S.activeSeed S.sourceState S.placedFeasible
      S.prebridge S.activeMeasure S.baseline_seed S.core.headSeparated
      A.Ctarget A.Cinitial A.Cfixed A.Cactive A.targetEnvelopes
      A.selectorDeficit A.frozenLedger A.activeLedger A.radius Cpost
      A.localP87 A.cellIndex A.Cplacement A.Cplacement_nonneg
      A.placementSeedUpper A.fixedRoom A.C A.C_one_le A.W_large
      A.physicalUpper A.Cactive_nonneg A.protectedReserve A.largeL
      A.nonsmooth

end BankPaperRealization

end

end Erdos390.WholePaper
