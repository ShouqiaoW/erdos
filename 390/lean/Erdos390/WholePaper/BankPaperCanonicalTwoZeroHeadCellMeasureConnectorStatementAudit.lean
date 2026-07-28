import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellMeasureConnector

/-!
# Statement audit for the two-zero-cell actual-measure connector

The expanded terminal below shows that `Hmeasure` is constructed for the
original scaled barycentric seed.  Its only new finite inequality is the
literal protected absorption bound in the two zero-head cells; the
asymptotic terminal in the implementation derives that inequality from the
existing Section 8 ledger.
The fixed relevant-ledger specialization is checked at its public type; it
aligns the canonical-sample hypotheses with the fixed-family one-shot
terminal.
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

/-! ## Protected reserve retained by the final selector -/

/-- Expanded finite endpoint reserve.  The ambient term is the original
scaled seed retained by the actual bridge, while the selector uses the
two-zero-cell rebalanced seed. -/
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
    (deltaStar betaProt sigma : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hgap : 0 < betaProt - sigma)
    (hloss : forall sign : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sign)) : Real) *
          ((betaProt - sigma) / B.L)) :
    ∀ a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q) a <=
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q)
            (bankPaperCanonicalSymmetricHeightCellMass d)
            (bankPaperCanonicalSymmetricHeightCellMass d)) a :=
  bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
    (K := K) B R certificate deltaStar betaProt sigma baseSelector T q d
      hsep hgap hloss

/-- Expanded eventual endpoint reserve.  Realizations and certificates are
pointwise data after the asymptotic index; no global realization family is
assumed. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu betaProt deltaStar sigma : Real}
    (hmu : 0 < mu) (hgap : 0 < betaProt - sigma)
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
          (hphysical : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hphysical hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate :
              GuardedCentralAnchorCertificate c depth B.sampleData.n
                R.anchorGuardLeftCore R.anchorGuardRightCore
                (R.centralChangedMarkers depth))
            (T : BarycentricTarget B.sampleData),
            B.sampleData.HeadPatternsSeparated ->
            ∀ (baseSelector : Nat -> Real) (a : Nat),
              a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
                deltaStar B.sampleData.W K 1 ->
              sigma / B.L +
                  bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n)) a <=
                bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                  B R certificate deltaStar betaProt baseSelector
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) a :=
  eventually_bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
    (Band := Band) (betaProt := betaProt)
      (deltaStar := deltaStar) (sigma := sigma)
      Phead I Cprom Cbank ledger depth W K hmu hgap
      logY Lambda0 mFrozen qTilde Hledger

/-- Expanded `Hmeasure` terminal.  The structured placement supplies final
selector nonnegativity, smooth-row support supplies candidate support, and
protected absorption supplies coordinate fit at the only changed cells. -/
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
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (d : Int)
    (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hbetaProt : 0 <= betaProt)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hloss : forall sigma : PhysicalSign,
      -bankPaperCanonicalSymmetricHeightCellMass d <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L))
    (Hplacement : BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt baseSelector
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalScaledActiveSeed T q)
        (bankPaperCanonicalSymmetricHeightCellMass d)
        (bankPaperCanonicalSymmetricHeightCellMass d))) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalScaledActiveSeed T q) :=
  bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight
    (K := K) B R certificate fixed deltaStar betaProt baseSelector T q d hq hsep
      hactiveSmooth hbetaProt hminus hplus hloss Hplacement

/-! ## Eventual paper-facing composition -/

/-- The analytic Section 8 ledger supplies both `q0 >= 1` and protected
absorption, so a one-shot structured placement with its already proved
support facts produces `Hmeasure` without a new measure premise.
Realizations and certificates are quantified pointwise after the
asymptotic index. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu betaProt deltaStar : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct)
    (hmu : 0 < mu) (hbetaProt : 0 < betaProt)
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
            (T : BarycentricTarget B.sampleData),
            B.sampleData.HeadPatternsSeparated ->
            forall (fixed : Finset Nat) (baseSelector : Nat -> Real),
              bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
                  R.roughCanonicalGuardedRow
                    certificate deltaStar K 1 ->
              (forall m : B.sampleData.Sample,
                B.sampleData.cellOf m = (none, .minus) ->
                  B.sampleData.value m ∈
                    R.roughCanonicalGuardedBroadCorrectionPool
                      certificate deltaStar
                      B.sampleData.W K 1) ->
              (forall m : B.sampleData.Sample,
                B.sampleData.cellOf m = (none, .plus) ->
                  B.sampleData.value m ∈
                    R.roughCanonicalGuardedBroadCorrectionPool
                      certificate deltaStar
                      B.sampleData.W K 1) ->
              BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
                  B R certificate
                  fixed deltaStar betaProt baseSelector
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) ->
                BankPaperCanonicalActualActiveMeasureConstructor
                  B.sampleData T
                  (R.roughCanonicalGuardedCandidateSet
                    certificate deltaStar K)
                  (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                    B R certificate
                    deltaStar betaProt baseSelector
                    (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                      (bankPaperCanonicalScaledActiveSeed T
                        (bankPaperCanonicalSmoothQ0Family
                          mFrozen qTilde n))
                      (bankPaperCanonicalSymmetricHeightCellMass
                        (bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n))
                      (bankPaperCanonicalSymmetricHeightCellMass
                        (bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n))))
                  (bankPaperCanonicalScaledActiveSeed T
                    (bankPaperCanonicalSmoothQ0Family
                      mFrozen qTilde n)) :=
  eventually_bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_placement
    (Band := Band) (deltaStar := deltaStar)
      Phead I Cprom Cbank ledger depth W K
      hc hbeta hmu hbetaProt logY Lambda0 mFrozen qTilde Hledger

/-! ## Complete public declaration census -/

#check eventually_bankPaperCanonicalTwoZeroHeadCell_protectedAbsorption_of_littleO
#check eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_protectedAbsorption
#check bankPaperCanonicalScaledActiveSeed_le_protected_add_symmetricHeightRebalance
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
#check eventually_bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_protectedReserve_symmetricHeight
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit_symmetricHeight
#check bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight
#check bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_canonicalGeometry
#check bankPaperCanonicalActiveMassBridgeData_baseWeight_scaledSeed
#check eventually_bankPaperCanonicalSymmetricHeight_actualMeasureInputs
#check eventually_bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_placement
#check eventually_bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight_of_placement_relevantLedgerFamily

end BankPaperRealization

end

end Erdos390.WholePaper
