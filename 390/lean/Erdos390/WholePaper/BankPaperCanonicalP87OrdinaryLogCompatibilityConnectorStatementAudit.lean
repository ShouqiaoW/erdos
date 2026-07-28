import Erdos390.WholePaper.BankPaperCanonicalP87OrdinaryLogCompatibilityConnector

/-!
# Statement audit for exact P87 ordinary-log propagation

The examples expose the two key claims: `primeLogScore` is the finite
`tPrime`-weighted marked moment, and the actual P87 endpoint preserves the
weighted literal selector deficit.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

#check bankPaperCanonicalPaperMoment_primeLogScore_eq_sum_markedValuation
#check bankPaperCanonicalWeightedActiveResidual_eq_target_sub_primeLogMoment
#check bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq
#check bankPaperCanonicalActualInitialSelector_weightedResidual_eq
#check bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq_initial
#check bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatible
#check bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatible_of_path

/-- Expanded exact prime-log moment identity. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (xi : B.ParamSpace) :
    B.paperMoment B.primeLogScore xi =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          B.paperMoment (B.markedValuation p.1) xi :=
  bankPaperCanonicalPaperMoment_primeLogScore_eq_sum_markedValuation B xi

/-- Expanded exact propagation statement. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hprimeLog :
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalTangentResidual R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p) =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 *
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates preSelector p :=
  bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq_initial
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed path hprimeLog

/-- Expanded conditional endpoint-compatibility statement. -/
example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hprimeLog :
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0)
    (hinitial : BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W)
      R certificate fixed candidates preSelector) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W) R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) :=
  bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatible
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed path hprimeLog hinitial

end

end Erdos390.WholePaper
