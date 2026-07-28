import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellHfitConnector

/-!
# Statement audit for the two-zero-cell Hfit connector

The first expanded check records the corrected frozen constant
`betaProt + gamma`: the actual bridge uses the original seed, not the
rebalanced placement seed.  The second check records that the eventual
specialization quantifies the realization and certificate pointwise after
the asymptotic index.  The third exposes the exact local canonical-P87 tail
and shows which analytic inputs remain visible.
-/

open Filter Topology Asymptotics Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- Expanded finite frozen-ledger statement. -/
example
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
    (deltaStar betaProt : Real) (hbetaProt : 0 <= betaProt)
    (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalScaledActiveSeed T q))
    (gamma : Real)
    (hgamma : 0 <= gamma)
    (hcellUpper : forall sigma : PhysicalSign,
      bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (gamma / B.L)) :
    forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K))
          (bankPaperCanonicalActualFrozenWeight B.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt baseSelector
              (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                (bankPaperCanonicalScaledActiveSeed T q)
                (bankPaperCanonicalSymmetricHeightCellMass d)
                (bankPaperCanonicalSymmetricHeightCellMass d)))
            (bankPaperCanonicalScaledActiveSeed T q))
          (B.sampleData.value m) <=
        (betaProt + gamma) / B.L :=
  bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
    B R certificate deltaStar betaProt hbetaProt baseSelector T q d hsep
      Hmeasure gamma hgamma hcellUpper

/-- Expanded eventual frozen-ledger specialization.  The realization and
certificate are local data after `n` and the canonical sample, rather than
a family required before the eventual quantifier. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu betaProt deltaStar : Real}
    (hmu : 0 < mu) (hbetaProt : 0 <= betaProt)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate :
              GuardedCentralAnchorCertificate c depth B.sampleData.n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth))
            (T : BarycentricTarget B.sampleData)
            (baseSelector : Nat -> Real),
            let q :=
              bankPaperCanonicalSmoothQ0Family mFrozen qTilde n
            let d :=
              bankPaperCanonicalSmoothDIntFamily
                mu logY Lambda0 mFrozen qTilde n
            BankPaperCanonicalActualActiveMeasureConstructor
                B.sampleData T
                (R.roughCanonicalGuardedCandidateSet
                  certificate deltaStar K)
                (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                  B R certificate
                  deltaStar betaProt baseSelector
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T q)
                    (bankPaperCanonicalSymmetricHeightCellMass d)
                    (bankPaperCanonicalSymmetricHeightCellMass d)))
                (bankPaperCanonicalScaledActiveSeed T q) ->
              B.sampleData.HeadPatternsSeparated ->
              forall m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight
                    (bankPaperCanonicalActualFrozenValue
                      (candidates :=
                        R.roughCanonicalGuardedCandidateSet
                          certificate deltaStar K))
                    (bankPaperCanonicalActualFrozenWeight B.sampleData
                      (R.roughCanonicalGuardedCandidateSet
                        certificate deltaStar K)
                      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                        B R certificate
                        deltaStar betaProt baseSelector
                        (bankPaperCanonicalTwoZeroHeadCellRebalance
                          B.sampleData
                          (bankPaperCanonicalScaledActiveSeed T q)
                          (bankPaperCanonicalSymmetricHeightCellMass d)
                          (bankPaperCanonicalSymmetricHeightCellMass d)))
                      (bankPaperCanonicalScaledActiveSeed T q))
                    (B.sampleData.value m) <=
                  (betaProt + 1) / B.L :=
  eventually_bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
    (Band := Band) (betaProt := betaProt) (deltaStar := deltaStar)
    Phead I Cprom Cbank ledger depth W K hmu hbetaProt
      logY Lambda0 mFrozen qTilde Hledger

/-- Expanded terminal adapter.  It fixes `N = B.q` and `Cmass = 1`, while
leaving the target, initial selector-residual, frozen, and active ledgers
in their literal existing forms. -/
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
    (hselector : ∀ a ∈ candidates,
      0 <= preSelector a ∧ preSelector a <= 1)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector)
    (hhead : B.sampleData.HeadPatternsSeparated)
    (Ctarget Cinitial Cfixed Cactive : Real)
    (henv : B.HasTargetEnvelopes Ctarget
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed) 0 j))
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L))
    (hfrozenLedger : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates := candidates))
          (bankPaperCanonicalActualFrozenWeight
            B.sampleData candidates preSelector activeSeed)
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
              markedTarget N Cpost fixedValue fixedWeight quota) :
    ∃ quota : Int,
      B.HasPaperProposition87Conclusion
        (fun j => B.markedBandResidual
          (bankPaperCanonicalActualActiveMarkedTarget
            B R certificate fixed candidates preSelector activeSeed) 0 j)
        radius
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed)
        B.q Cpost
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        quota :=
  exists_bankPaperCanonicalActualP87Conclusion_of_localCanonical
    B R certificate fixed candidates preSelector activeSeed
      Hmeasure hseed hselector hrow hhead
      Ctarget Cinitial Cfixed Cactive henv hdeficit
      hfrozenLedger hactiveLedger radius Cpost hP87

/-! ## Complete public declaration census -/

#check eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_upperAbsorption
#check bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
#check eventually_bankPaperCanonicalActualFrozenWeight_symmetricHeight_le
#check bankPaperCanonicalActualInitialMarkedRate_of_selectorDeficit
#check exists_bankPaperCanonicalActualP87Conclusion_of_localCanonical

end BankPaperRealization

end

end Erdos390.WholePaper
