import Erdos390.WholePaper.BankPaperCanonicalSectionNineFinalPayloadConnector
import Erdos390.WholePaper.BankPaperCanonicalPostHfitSlackConnector
import Erdos390.WholePaper.BankPaperCombinedChargeDepthFirstTerminal

/-!
# Same-witness producer for the synchronized Post-Hfit input

The final-payload connector deliberately leaves one compatibility statement:
the capacity bank and guarded anchor certificate must be the same bank and
certificate used by the Section 8/Post-Hfit construction.

This file closes the formal quantifier handoff.  The fixed-depth combined
charge terminal first supplies one capacity bank and certificate.  A local
analytic supplier is then applied to that very pair, and the existing
Post-Hfit slack connector constructs the endpoint package for the same
bridge data.

`BankPaperCanonicalSectionNinePostHfitLocalInputsAt` lists the genuinely
remaining finite analytic inputs.  It contains no Post-Hfit slack package,
Section 9 output, final payload, budget closure, or collision conclusion.
The canonical mesh partition is also kept outside it, so the eventual
producer visibly uses the same scale-separation witness which determines the
ratio-cell index in the synchronized output.
-/

open Filter Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Exact local analytic input -/

/-- The finite hypotheses which remain before the audited Post-Hfit slack
connector can be run at one already fixed `B`, `R`, and `certificate`.

The rounded source state, actual-measure compatibility, Proposition 8.7
estimates, pointwise placement bound, reserve inequality, large-`L`
inequality, and balanced nonsmooth bounds remain explicit.  Everything
which follows from those hypotheses (structured placement, P87 path,
endpoint identity, rounded endpoint state, and endpoint slack) is omitted
from this input and is constructed below. -/
def BankPaperCanonicalSectionNinePostHfitLocalInputsAt
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
    (deltaStar sigma Cpost : Real) : Prop :=
  ∃ betaProt betaAct : Real,
    ∃ oldSeed activeSeed : B.sampleData.Sample → Real,
      ∃ minusMass plusMass : Real,
        ∃ rowChange : Int,
          ∃ sourceCellIndex : BankPaperCanonicalTangentPrime
              B.sampleData.n B.sampleData.W → Nat,
            ∃ sourcePointwiseUpper : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W → Real,
              ∃ sourcePrefixUpper : Band → Nat → Real,
                ∃ T : BarycentricTarget B.sampleData,
                  ∃ Ctarget Cinitial Cfixed Cactive : Real,
                    ∃ radius : NNReal,
                      ∃ Cplacement C : Real,
                        0 ≤ betaProt ∧
                        BankPaperCanonicalRoundedSelectorTangentInput
                          R certificate
                          (R.paperFixedExceptionalFactors deltaStar)
                          (R.roughCanonicalGuardedCandidateSet certificate
                            deltaStar (K0 + 1))
                          B.partition.band sourceCellIndex
                          sourcePointwiseUpper sourcePrefixUpper
                          (bankPaperCanonicalPostHfitGlobalSourceSelector
                            B K0 R certificate deltaStar betaProt betaAct
                              oldSeed) ∧
                        B.sampleData.HeadPatternsSeparated ∧
                        bankPaperCanonicalStructuredActiveValues
                              B.sampleData ⊆
                            R.roughCanonicalGuardedRow certificate deltaStar
                              (K0 + 1) 1 ∧
                        (∀ m : B.sampleData.Sample,
                          B.sampleData.cellOf m = (none, .minus) →
                            B.sampleData.value m ∈
                              R.roughCanonicalGuardedBroadCorrectionPool
                                certificate deltaStar B.sampleData.W
                                  (K0 + 1) 1) ∧
                        (∀ m : B.sampleData.Sample,
                          B.sampleData.cellOf m = (none, .plus) →
                            B.sampleData.value m ∈
                              R.roughCanonicalGuardedBroadCorrectionPool
                                certificate deltaStar B.sampleData.W
                                  (K0 + 1) 1) ∧
                        (∀ m : B.sampleData.Sample,
                          B.sampleData.cellOf m = (none, .minus) →
                            0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
                                B.sampleData oldSeed minusMass plusMass m ∧
                              betaProt / B.L +
                                  bankPaperCanonicalTwoZeroHeadCellRebalance
                                    B.sampleData oldSeed minusMass plusMass m ≤
                                1) ∧
                        (∀ m : B.sampleData.Sample,
                          B.sampleData.cellOf m = (none, .plus) →
                            0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
                                B.sampleData oldSeed minusMass plusMass m ∧
                              betaProt / B.L +
                                  bankPaperCanonicalTwoZeroHeadCellRebalance
                                    B.sampleData oldSeed minusMass plusMass m ≤
                                1) ∧
                        minusMass + plusMass = (rowChange : Real) ∧
                        BankPaperCanonicalActualActiveMeasureConstructor
                          B.sampleData T
                          (R.roughCanonicalGuardedCandidateSet certificate
                            deltaStar (K0 + 1))
                          (bankPaperCanonicalPostHfitStructuredPreSelector
                            B K0 R certificate deltaStar betaProt betaAct
                              oldSeed minusMass plusMass)
                          activeSeed ∧
                        (∀ m, B.baseline.baseWeight m = activeSeed m) ∧
                        B.HasTargetEnvelopes Ctarget
                          (fun j => B.markedBandResidual
                            (bankPaperCanonicalActualActiveMarkedTarget
                              B R certificate
                              (R.paperFixedExceptionalFactors deltaStar)
                              (R.roughCanonicalGuardedCandidateSet certificate
                                deltaStar (K0 + 1))
                              (bankPaperCanonicalPostHfitStructuredPreSelector
                                B K0 R certificate deltaStar betaProt betaAct
                                  oldSeed minusMass plusMass)
                              activeSeed) 0 j) ∧
                        (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                          abs (bankPaperCanonicalSelectorValuationDeficit
                            R certificate
                              (R.paperFixedExceptionalFactors deltaStar)
                              (R.roughCanonicalGuardedCandidateSet certificate
                                deltaStar (K0 + 1))
                              (bankPaperCanonicalPostHfitStructuredPreSelector
                                B K0 R certificate deltaStar betaProt betaAct
                                  oldSeed minusMass plusMass) p) ≤
                            Cinitial * B.q / ((p : Real) * B.L)) ∧
                        (∀ m : B.sampleData.Sample,
                          BridgeData.frozenAmbientWeight
                              (bankPaperCanonicalActualFrozenValue
                                (candidates :=
                                  R.roughCanonicalGuardedCandidateSet
                                    certificate deltaStar (K0 + 1)))
                              (bankPaperCanonicalActualFrozenWeight B.sampleData
                                (R.roughCanonicalGuardedCandidateSet
                                  certificate deltaStar (K0 + 1))
                                (bankPaperCanonicalPostHfitStructuredPreSelector
                                  B K0 R certificate deltaStar betaProt
                                    betaAct oldSeed minusMass plusMass)
                                activeSeed)
                              (B.sampleData.value m) ≤
                            Cfixed / B.L) ∧
                        (∀ m : B.sampleData.Sample,
                          B.baseline.baseWeight m ≤ Cactive / B.L) ∧
                        (∀ (Delta : Band → Real),
                          B.HasTargetEnvelopes Ctarget Delta →
                          ∀ (markedTarget : Nat → Real) (N : Real),
                            0 ≤ N →
                            B.q ≤ (1 : Real) * N →
                            (∀ p ∈ primeBand
                                B.sampleData.n B.sampleData.W,
                              abs (markedTarget p -
                                B.paperMoment
                                  (B.markedValuation p) 0) ≤
                                Cinitial * N / ((p : Real) * B.L)) →
                            (∀ j,
                              Delta j =
                                B.markedBandResidual markedTarget 0 j) →
                            ∀ {Fixed : Type} [Fintype Fixed],
                              ∀ (fixedValue : Fixed → Nat)
                                (fixedWeight : Fixed → Real) (quota : Int),
                                (quota : Real) =
                                    (∑ f, fixedWeight f) + B.q →
                                B.sampleData.HeadPatternsSeparated →
                                (∀ x,
                                  BridgeData.frozenAmbientWeight
                                    fixedValue fixedWeight x ∈
                                      Icc (0 : Real) 1) →
                                (∀ m : B.sampleData.Sample,
                                  BridgeData.frozenAmbientWeight
                                      fixedValue fixedWeight
                                        (B.sampleData.value m) ≤
                                    Cfixed / B.L) →
                                (∀ m : B.sampleData.Sample,
                                  B.baseline.baseWeight m ≤ Cactive / B.L) →
                                B.HasPaperProposition87Conclusion
                                  Delta radius markedTarget N Cpost
                                    fixedValue fixedWeight quota) ∧
                        0 ≤ Cplacement ∧
                        (∀ m : B.sampleData.Sample,
                          bankPaperCanonicalTwoZeroHeadCellRebalance
                              B.sampleData oldSeed minusMass plusMass m ≤
                            Cplacement / B.L) ∧
                        betaProt + Cplacement ≤ Cfixed ∧
                        1 ≤ C ∧
                        1 < B.sampleData.W ∧
                        (∀ sign,
                          B.sampleData.hi sign ≤
                            physicalBound C B.sampleData.n) ∧
                        0 ≤ Cactive ∧
                        (∀ x ∈
                          R.roughCanonicalGuardedBroadCorrectionPool
                            certificate deltaStar B.sampleData.W
                              (K0 + 1) 1,
                          sigma / B.L +
                              bankPaperCanonicalActiveSeedAmbientWeight
                                B.sampleData activeSeed x ≤
                            bankPaperCanonicalPostHfitStructuredPreSelector
                              B K0 R certificate deltaStar betaProt betaAct
                                oldSeed minusMass plusMass x) ∧
                        Cfixed +
                            Real.exp (2 *
                              ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                                    C B.sampleData.W +
                                B.nuisanceStatisticCoefficient C) *
                                  (3 * (radius : Real)))) *
                              Cactive + sigma ≤
                          B.L ∧
                        RoughCanonicalBalancedNonsmoothBounds
                          R certificate deltaStar B.sampleData.W K0
                            betaProt betaAct sigma

/-- The same finite Post-Hfit input with only the selector information
consumed before Proposition 8.7.  In contrast to
`BankPaperCanonicalSectionNinePostHfitLocalInputsAt`, this interface has no
source cell-index, pointwise-bound, or prefix-bound witnesses and assumes no
source prime-band balance or tangent residual bounds. -/
def BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
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
    (deltaStar sigma Cpost : Real) : Prop :=
  ∃ betaProt betaAct : Real,
    ∃ oldSeed activeSeed : B.sampleData.Sample → Real,
      ∃ minusMass plusMass : Real,
        ∃ rowChange : Int,
          ∃ T : BarycentricTarget B.sampleData,
            ∃ Ctarget Cinitial Cfixed Cactive : Real,
              ∃ radius : NNReal,
                ∃ Cplacement C : Real,
                  0 ≤ betaProt ∧
                  BankPaperCanonicalSelectorSourceState
                    (W := B.sampleData.W) R certificate
                    (R.paperFixedExceptionalFactors deltaStar)
                    (R.roughCanonicalGuardedCandidateSet certificate
                      deltaStar (K0 + 1))
                    (bankPaperCanonicalPostHfitGlobalSourceSelector
                      B K0 R certificate deltaStar betaProt betaAct
                        oldSeed) ∧
                  B.sampleData.HeadPatternsSeparated ∧
                  bankPaperCanonicalStructuredActiveValues
                        B.sampleData ⊆
                      R.roughCanonicalGuardedRow certificate deltaStar
                        (K0 + 1) 1 ∧
                  (∀ m : B.sampleData.Sample,
                    B.sampleData.cellOf m = (none, .minus) →
                      B.sampleData.value m ∈
                        R.roughCanonicalGuardedBroadCorrectionPool
                          certificate deltaStar B.sampleData.W
                            (K0 + 1) 1) ∧
                  (∀ m : B.sampleData.Sample,
                    B.sampleData.cellOf m = (none, .plus) →
                      B.sampleData.value m ∈
                        R.roughCanonicalGuardedBroadCorrectionPool
                          certificate deltaStar B.sampleData.W
                            (K0 + 1) 1) ∧
                  (∀ m : B.sampleData.Sample,
                    B.sampleData.cellOf m = (none, .minus) →
                      0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
                          B.sampleData oldSeed minusMass plusMass m ∧
                        betaProt / B.L +
                            bankPaperCanonicalTwoZeroHeadCellRebalance
                              B.sampleData oldSeed minusMass plusMass m ≤
                          1) ∧
                  (∀ m : B.sampleData.Sample,
                    B.sampleData.cellOf m = (none, .plus) →
                      0 ≤ bankPaperCanonicalTwoZeroHeadCellRebalance
                          B.sampleData oldSeed minusMass plusMass m ∧
                        betaProt / B.L +
                            bankPaperCanonicalTwoZeroHeadCellRebalance
                              B.sampleData oldSeed minusMass plusMass m ≤
                          1) ∧
                  minusMass + plusMass = (rowChange : Real) ∧
                  BankPaperCanonicalActualActiveMeasureConstructor
                    B.sampleData T
                    (R.roughCanonicalGuardedCandidateSet certificate
                      deltaStar (K0 + 1))
                    (bankPaperCanonicalPostHfitStructuredPreSelector
                      B K0 R certificate deltaStar betaProt betaAct
                        oldSeed minusMass plusMass)
                    activeSeed ∧
                  (∀ m, B.baseline.baseWeight m = activeSeed m) ∧
                  B.HasTargetEnvelopes Ctarget
                    (fun j => B.markedBandResidual
                      (bankPaperCanonicalActualActiveMarkedTarget
                        B R certificate
                        (R.paperFixedExceptionalFactors deltaStar)
                        (R.roughCanonicalGuardedCandidateSet certificate
                          deltaStar (K0 + 1))
                        (bankPaperCanonicalPostHfitStructuredPreSelector
                          B K0 R certificate deltaStar betaProt betaAct
                            oldSeed minusMass plusMass)
                        activeSeed) 0 j) ∧
                  (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                    abs (bankPaperCanonicalSelectorValuationDeficit
                      R certificate
                        (R.paperFixedExceptionalFactors deltaStar)
                        (R.roughCanonicalGuardedCandidateSet certificate
                          deltaStar (K0 + 1))
                        (bankPaperCanonicalPostHfitStructuredPreSelector
                          B K0 R certificate deltaStar betaProt betaAct
                            oldSeed minusMass plusMass) p) ≤
                      Cinitial * B.q / ((p : Real) * B.L)) ∧
                  (∀ m : B.sampleData.Sample,
                    BridgeData.frozenAmbientWeight
                        (bankPaperCanonicalActualFrozenValue
                          (candidates :=
                            R.roughCanonicalGuardedCandidateSet
                              certificate deltaStar (K0 + 1)))
                        (bankPaperCanonicalActualFrozenWeight B.sampleData
                          (R.roughCanonicalGuardedCandidateSet
                            certificate deltaStar (K0 + 1))
                          (bankPaperCanonicalPostHfitStructuredPreSelector
                            B K0 R certificate deltaStar betaProt
                              betaAct oldSeed minusMass plusMass)
                          activeSeed)
                        (B.sampleData.value m) ≤
                      Cfixed / B.L) ∧
                  (∀ m : B.sampleData.Sample,
                    B.baseline.baseWeight m ≤ Cactive / B.L) ∧
                  (∀ (Delta : Band → Real),
                    B.HasTargetEnvelopes Ctarget Delta →
                    ∀ (markedTarget : Nat → Real) (N : Real),
                      0 ≤ N →
                      B.q ≤ (1 : Real) * N →
                      (∀ p ∈ primeBand
                          B.sampleData.n B.sampleData.W,
                        abs (markedTarget p -
                          B.paperMoment
                            (B.markedValuation p) 0) ≤
                          Cinitial * N / ((p : Real) * B.L)) →
                      (∀ j,
                        Delta j =
                          B.markedBandResidual markedTarget 0 j) →
                      ∀ {Fixed : Type} [Fintype Fixed],
                        ∀ (fixedValue : Fixed → Nat)
                          (fixedWeight : Fixed → Real) (quota : Int),
                          (quota : Real) =
                              (∑ f, fixedWeight f) + B.q →
                          B.sampleData.HeadPatternsSeparated →
                          (∀ x,
                            BridgeData.frozenAmbientWeight
                              fixedValue fixedWeight x ∈
                                Icc (0 : Real) 1) →
                          (∀ m : B.sampleData.Sample,
                            BridgeData.frozenAmbientWeight
                                fixedValue fixedWeight
                                  (B.sampleData.value m) ≤
                              Cfixed / B.L) →
                          (∀ m : B.sampleData.Sample,
                            B.baseline.baseWeight m ≤ Cactive / B.L) →
                          B.HasPaperProposition87Conclusion
                            Delta radius markedTarget N Cpost
                              fixedValue fixedWeight quota) ∧
                  0 ≤ Cplacement ∧
                  (∀ m : B.sampleData.Sample,
                    bankPaperCanonicalTwoZeroHeadCellRebalance
                        B.sampleData oldSeed minusMass plusMass m ≤
                      Cplacement / B.L) ∧
                  betaProt + Cplacement ≤ Cfixed ∧
                  1 ≤ C ∧
                  1 < B.sampleData.W ∧
                  (∀ sign,
                    B.sampleData.hi sign ≤
                      physicalBound C B.sampleData.n) ∧
                  0 ≤ Cactive ∧
                  (∀ x ∈
                    R.roughCanonicalGuardedBroadCorrectionPool
                      certificate deltaStar B.sampleData.W
                        (K0 + 1) 1,
                    sigma / B.L +
                        bankPaperCanonicalActiveSeedAmbientWeight
                          B.sampleData activeSeed x ≤
                      bankPaperCanonicalPostHfitStructuredPreSelector
                        B K0 R certificate deltaStar betaProt betaAct
                          oldSeed minusMass plusMass x) ∧
                  Cfixed +
                      Real.exp (2 *
                        ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                              C B.sampleData.W +
                          B.nuisanceStatisticCoefficient C) *
                            (3 * (radius : Real)))) *
                        Cactive + sigma ≤
                    B.L ∧
                  RoughCanonicalBalancedNonsmoothBounds
                    R certificate deltaStar B.sampleData.W K0
                      betaProt betaAct sigma

/-! ## Legacy rounded-source adapter -/

/-- Forget the source-only tangent witnesses from the legacy local input,
retaining exactly the selector state consumed by the weak Post-Hfit
constructor. -/
theorem
    bankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt_of_localInputs
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
    (Hlocal : BankPaperCanonicalSectionNinePostHfitLocalInputsAt
      (K0 := K0) B R certificate deltaStar sigma Cpost) :
    BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
      (K0 := K0) B R certificate deltaStar sigma Cpost := by
  unfold BankPaperCanonicalSectionNinePostHfitLocalInputsAt at Hlocal
  obtain
      ⟨betaProt, betaAct, oldSeed, activeSeed, minusMass, plusMass,
        rowChange, sourceCellIndex, sourcePointwiseUpper,
        sourcePrefixUpper, T, Ctarget, Cinitial, Cfixed, Cactive,
        radius, Cplacement, C, hbetaProt, Ssource, hsep,
        hactiveSmooth, hminus, hplus, hminusCapacity, hplusCapacity,
        hmass, Hmeasure, hseed, henv, hdeficit, hfrozenLedger,
        hactiveLedger, hP87, hCplacement, hplacementSeedUpper,
        hfixed, hC, hWlarge, hhi, hCactive, hprotectedReserve,
        hlarge, Hnonsmooth⟩ := Hlocal
  have SsourceState :=
    bankPaperCanonicalSelectorSourceState_of_roundedSelectorTangentInput
      R certificate (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
      B.partition.band sourceCellIndex sourcePointwiseUpper sourcePrefixUpper
      (bankPaperCanonicalPostHfitGlobalSourceSelector
        B K0 R certificate deltaStar betaProt betaAct oldSeed)
      Ssource
  unfold BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
  exact
    ⟨betaProt, betaAct, oldSeed, activeSeed, minusMass, plusMass,
      rowChange, T, Ctarget, Cinitial, Cfixed, Cactive, radius,
      Cplacement, C, hbetaProt, SsourceState, hsep, hactiveSmooth,
      hminus, hplus, hminusCapacity, hplusCapacity, hmass, Hmeasure,
      hseed, henv, hdeficit, hfrozenLedger, hactiveLedger, hP87,
      hCplacement, hplacementSeedUpper, hfixed, hC, hWlarge, hhi,
      hCactive, hprotectedReserve, hlarge, Hnonsmooth⟩

/-! ## Eventual local supplier -/

/-- A canonical-partition witness together with local analytic inputs for
whichever capacity bank and certificate are selected at that index.

The four implications expose exactly which facts may be reused from the
combined-charge terminal. -/
def BankPaperCanonicalSectionNinePostHfitLocalSupplier
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∃ hW : (B n).sampleData.W ≠ 0,
      ∃ S : ScaleSeparation M
          (B n).sampleData.n (B n).sampleData.W,
        (B n).partition =
            RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta (B n).n_gt_one hW S ∧
          ∀ (R : BankPaperRealization (B n).sampleData.n
                (upperEndpoint (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              (B n).sampleData.n R.anchorGuardLeftCore
              R.anchorGuardRightCore
              (R.centralChangedMarkers depth)),
            centralAnchorDivisor (B n).sampleData.n
                  (centralAnchorCutoff depth (B n).sampleData.n)
                  certificate.q * R.prechargeBaseStateProduct ∣
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            (baseBankFactors R.exactificationState).prod id ∣
                certificate.prechargedTailTarget →
            R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) ∣
                certificate.prechargedTailTarget →
            certificate.prechargedTailTarget *
                  centralAnchorDivisor (B n).sampleData.n
                    (centralAnchorCutoff depth (B n).sampleData.n)
                    certificate.q =
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            BankPaperCanonicalSectionNinePostHfitLocalInputsAt
              (K0 := K0) (B n) R certificate deltaStar sigma Cpost

/-- Eventual canonical-partition witnesses carrying only the weak
source-state local analytic input for each selected capacity bank and
certificate. -/
def BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    ∃ hW : (B n).sampleData.W ≠ 0,
      ∃ S : ScaleSeparation M
          (B n).sampleData.n (B n).sampleData.W,
        (B n).partition =
            RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta (B n).n_gt_one hW S ∧
          ∀ (R : BankPaperRealization (B n).sampleData.n
                (upperEndpoint (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              (B n).sampleData.n R.anchorGuardLeftCore
              R.anchorGuardRightCore
              (R.centralChangedMarkers depth)),
            centralAnchorDivisor (B n).sampleData.n
                  (centralAnchorCutoff depth (B n).sampleData.n)
                  certificate.q * R.prechargeBaseStateProduct ∣
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            (baseBankFactors R.exactificationState).prod id ∣
                certificate.prechargedTailTarget →
            R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) ∣
                certificate.prechargedTailTarget →
            certificate.prechargedTailTarget *
                  centralAnchorDivisor (B n).sampleData.n
                    (centralAnchorCutoff depth (B n).sampleData.n)
                    certificate.q =
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) →
            BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
              (K0 := K0) (B n) R certificate deltaStar sigma Cpost

/-! ## Same-witness finite assembly -/

/-- Construct the synchronized Post-Hfit input from one capacity witness and
the weak source-state local analytic inputs for exactly that witness. -/
theorem
    bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_sourceStateLocalInputs
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hcombined :
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hbaseDvd :
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget)
    (hchargeDvd :
      R.selectorTailCharge
            (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (htargetTail :
      certificate.prechargedTailTarget *
            centralAnchorDivisor B.sampleData.n
              (centralAnchorCutoff depth B.sampleData.n)
              certificate.q =
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hW : B.sampleData.W ≠ 0)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition :
      B.partition =
        RegularMeshPrimeCutoffs.Mesh.canonicalPartition
          M hdelta B.n_gt_one hW S)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
        (K0 := K0) B R certificate deltaStar sigma Cpost) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
      M B c depth K0 deltaStar rho sigma Cpost hdelta := by
  unfold BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt at Hlocal
  obtain
      ⟨betaProt, betaAct, oldSeed, activeSeed, minusMass, plusMass,
        rowChange, T, Ctarget, Cinitial, Cfixed, Cactive,
        radius, Cplacement, C, hbetaProt, SsourceState, hsep,
        hactiveSmooth, hminus, hplus, hminusCapacity, hplusCapacity,
        hmass, Hmeasure, hseed, henv, hdeficit, hfrozenLedger,
        hactiveLedger, hP87, hCplacement, hplacementSeedUpper,
        hfixed, hC, hWlarge, hhi, hCactive, hprotectedReserve,
        hlarge, Hnonsmooth⟩ := Hlocal
  obtain ⟨quota, path, endpoint, Hpost⟩ :=
    exists_bankPaperCanonicalPostHfitGuardedSlackPackage_of_sourceState
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        deltaStar betaProt betaAct sigma hbetaProt oldSeed activeSeed
        minusMass plusMass rowChange SsourceState hsep hactiveSmooth hminus hplus
        hminusCapacity hplusCapacity hmass Hmeasure hseed Ctarget
        Cinitial Cfixed Cactive henv hdeficit hfrozenLedger hactiveLedger
        radius Cpost hP87
        (bankPaperCanonicalRatioCellIndex
          M hdelta B.n_gt_one hW S rho)
        Cplacement hCplacement hplacementSeedUpper hfixed C hC
        hWlarge hhi hCactive hprotectedReserve hlarge Hnonsmooth
  unfold BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
  exact
    ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd, htargetTail,
      hW, S, hpartition, betaProt, betaAct, oldSeed, activeSeed,
      minusMass, plusMass, radius, quota, path, endpoint, Hpost⟩

/-- Compatibility producer for the legacy rounded-source local input. -/
theorem bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_localInputs
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hcombined :
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hbaseDvd :
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget)
    (hchargeDvd :
      R.selectorTailCharge
            (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (htargetTail :
      certificate.prechargedTailTarget *
            centralAnchorDivisor B.sampleData.n
              (centralAnchorCutoff depth B.sampleData.n)
              certificate.q =
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hW : B.sampleData.W ≠ 0)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition :
      B.partition =
        RegularMeshPrimeCutoffs.Mesh.canonicalPartition
          M hdelta B.n_gt_one hW S)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitLocalInputsAt
        (K0 := K0) B R certificate deltaStar sigma Cpost) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
      M B c depth K0 deltaStar rho sigma Cpost hdelta := by
  exact
    bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_sourceStateLocalInputs
      (K0 := K0) M B R certificate deltaStar rho sigma Cpost hdelta
        hcombined hbaseDvd hchargeDvd htargetTail hW S hpartition
        (bankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt_of_localInputs
          (K0 := K0) B R certificate deltaStar sigma Cpost Hlocal)

/-! ## Eventual capacity-to-Post-Hfit handoff -/

/-- A local supplier applied to every capacity witness closes the exact
compatibility gap in the synchronized input.

The quantifier order is intentional: the combined-charge terminal selects
`R` and `certificate` first; the supplier then receives those selected
objects together with their four capacity facts. -/
theorem
    bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n)
    (Hcapacity :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma Cpost hdelta := by
  simp only [BankPaperCombinedChargeTerminalAtDepth] at Hcapacity
  simp only [BankPaperCanonicalSectionNinePostHfitLocalSupplier] at Hlocal
  simp only [BankPaperCanonicalSectionNineSynchronizedPostHfitInput]
  filter_upwards [Hcapacity, hBn, Hlocal] with
    n HcapacityN hBnN HlocalN
  have HcapacityN' :
      ∃ R : BankPaperRealization (B n).sampleData.n
          (upperEndpoint (B n).sampleData.n
            (upperTailLength c (B n).sampleData.n)),
        ∃ certificate : GuardedCentralAnchorCertificate c depth
            (B n).sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth),
          centralAnchorDivisor (B n).sampleData.n
                (centralAnchorCutoff depth (B n).sampleData.n)
                certificate.q * R.prechargeBaseStateProduct ∣
              centralTailProduct (B n).sampleData.n
                (upperTailLength c (B n).sampleData.n) ∧
            (baseBankFactors R.exactificationState).prod id ∣
              certificate.prechargedTailTarget ∧
            R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) ∣
              certificate.prechargedTailTarget ∧
            (∀ p ∈ primesUpTo (2 * depth + 1),
              (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                    secondOrderScale (B n).sampleData.n +
                  (R.selectorTailCharge
                    (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
                certificate.prechargedTailTarget.factorization p) ∧
            certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors deltaStar) *
                R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) =
              certificate.prechargedTailTarget ∧
            certificate.prechargedTailTarget *
                  centralAnchorDivisor (B n).sampleData.n
                    (centralAnchorCutoff depth (B n).sampleData.n)
                    certificate.q =
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) := by
    rw [hBnN]
    exact HcapacityN
  obtain
      ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd,
        _hretained, _hselectorIdentity, htargetTail⟩ := HcapacityN'
  obtain ⟨hW, S, hpartition, Hsupplier⟩ := HlocalN
  exact
    bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_localInputs
      M (B n) R certificate deltaStar rho sigma Cpost hdelta
        hcombined hbaseDvd hchargeDvd htargetTail hW S hpartition
        (Hsupplier R certificate hcombined hbaseDvd hchargeDvd htargetTail)

/-- The eventual same-witness producer with the weak source-state supplier.
At each selected capacity witness it invokes the source-state finite
producer directly. -/
theorem
    bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal_sourceStateLocalSupplier
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n)
    (Hcapacity :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma Cpost hdelta := by
  simp only [BankPaperCombinedChargeTerminalAtDepth] at Hcapacity
  simp only [BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier]
    at Hlocal
  simp only [BankPaperCanonicalSectionNineSynchronizedPostHfitInput]
  filter_upwards [Hcapacity, hBn, Hlocal] with
    n HcapacityN hBnN HlocalN
  have HcapacityN' :
      ∃ R : BankPaperRealization (B n).sampleData.n
          (upperEndpoint (B n).sampleData.n
            (upperTailLength c (B n).sampleData.n)),
        ∃ certificate : GuardedCentralAnchorCertificate c depth
            (B n).sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth),
          centralAnchorDivisor (B n).sampleData.n
                (centralAnchorCutoff depth (B n).sampleData.n)
                certificate.q * R.prechargeBaseStateProduct ∣
              centralTailProduct (B n).sampleData.n
                (upperTailLength c (B n).sampleData.n) ∧
            (baseBankFactors R.exactificationState).prod id ∣
              certificate.prechargedTailTarget ∧
            R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) ∣
              certificate.prechargedTailTarget ∧
            (∀ p ∈ primesUpTo (2 * depth + 1),
              (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                    secondOrderScale (B n).sampleData.n +
                  (R.selectorTailCharge
                    (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
                certificate.prechargedTailTarget.factorization p) ∧
            certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors deltaStar) *
                R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar) =
              certificate.prechargedTailTarget ∧
            certificate.prechargedTailTarget *
                  centralAnchorDivisor (B n).sampleData.n
                    (centralAnchorCutoff depth (B n).sampleData.n)
                    certificate.q =
                centralTailProduct (B n).sampleData.n
                  (upperTailLength c (B n).sampleData.n) := by
    rw [hBnN]
    exact HcapacityN
  obtain
      ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd,
        _hretained, _hselectorIdentity, htargetTail⟩ := HcapacityN'
  obtain ⟨hW, S, hpartition, Hsupplier⟩ := HlocalN
  exact
    bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_sourceStateLocalInputs
      M (B n) R certificate deltaStar rho sigma Cpost hdelta
        hcombined hbaseDvd hchargeDvd htargetTail hW S hpartition
        (Hsupplier R certificate hcombined hbaseDvd hchargeDvd htargetTail)

end BankPaperRealization

end

end Erdos390.WholePaper
