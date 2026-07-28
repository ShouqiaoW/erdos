import Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector

/-!
# Statement audit for the Section 8 two-zero-cell one-shot connector

The expanded terminal below records every family identification that
remains in the theorem statement.  In particular, the canonical P87 sample
equality and cell-mass margin are local arguments, while the ledger and rough
guard are required to agree only on the positive smooth bridge universe.
The fixed relevant-ledger corollary is checked separately; it chooses the
ledger before the asymptotic index and discharges that local agreement
eventually.
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

/-- Expanded paper-level terminal: analytic height control, canonical sample
geometry, a rounded source selector, and local guard agreement give the full
structured placement and exact quota transport. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperStrict : forall sigma, I.upper sigma < 2)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu marginFloor deltaStar betaProt : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (hmarginFloor : 0 < marginFloor)
    (hbetaProt : 0 <= betaProt)
    (hhead : primesUpTo W ⊆ P)
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
        B.sampleData.W = W ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell (PaperHeadSimplex.pattern P hprime E) I
                B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                (PaperHeadSimplex.pattern P hprime E) I
                (ledger B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
              (R.centralChangedMarkers depth))
            (_hguardAgreement : BankPaperCanonicalBridgeGuardAgreement
              (ledger B.sampleData.n) R certificate deltaStar),
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall (fixed : Finset Nat)
              (cellIndex : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W -> Nat)
              (pointwiseUpper : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W -> Real)
              (prefixUpper : Band -> Nat -> Real),
              BankPaperCanonicalRoundedSelectorTangentInput
                R certificate fixed
                (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
                B.partition.band cellIndex pointwiseUpper prefixUpper
                (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                  B R certificate
                    deltaStar betaProt
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))) ->
              BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
                  B R certificate
                  fixed deltaStar betaProt
                  (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                    B R certificate
                      deltaStar betaProt
                      (bankPaperCanonicalScaledActiveSeed T
                        (bankPaperCanonicalSmoothQ0Family
                          mFrozen qTilde n)))
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) ∧
                forall baseQuota : Int,
                  BankPaperCanonicalGuardedSmoothFlexibleQuota
                      R certificate
                      deltaStar K
                      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                        B R certificate
                          deltaStar betaProt
                          (bankPaperCanonicalScaledActiveSeed T
                            (bankPaperCanonicalSmoothQ0Family
                              mFrozen qTilde n)))
                      baseQuota ->
                    BankPaperCanonicalGuardedSmoothFlexibleQuota
                      R certificate
                      deltaStar K
                      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                        B R certificate
                          deltaStar betaProt
                          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                            B R certificate
                              deltaStar betaProt
                              (bankPaperCanonicalScaledActiveSeed T
                                (bankPaperCanonicalSmoothQ0Family
                                  mFrozen qTilde n)))
                          (bankPaperCanonicalTwoZeroHeadCellRebalance
                            B.sampleData
                            (bankPaperCanonicalScaledActiveSeed T
                              (bankPaperCanonicalSmoothQ0Family
                                mFrozen qTilde n))
                            (bankPaperCanonicalSymmetricHeightCellMass
                              (bankPaperCanonicalSmoothDIntFamily
                                mu logY Lambda0 mFrozen qTilde n))
                            (bankPaperCanonicalSymmetricHeightCellMass
                              (bankPaperCanonicalSmoothDIntFamily
                                mu logY Lambda0 mFrozen qTilde n))))
                      (baseQuota -
                        bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n) :=
  eventually_bankPaperCanonicalSectionEight_twoZeroHeadCell_oneShot
    hprime E hE I hlowerOne hupperStrict Cprom Cbank ledger depth W K
    hc hbeta hmu hmarginFloor hbetaProt hhead
    logY Lambda0 mFrozen qTilde Hledger

/-! ## Exact literal smooth quota -/

/-- The rounded source's existing row-integrality field determines its
literal initialized smooth quota, and the symmetric two-cell placement
then transports that quota to the displayed integer height.  No separate
source-quota premise remains in this specialization. -/
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
    (fixed : Finset Nat) (deltaStar betaProt qTilde : Real)
    (oldSeed : B.sampleData.Sample -> Real) (d : Int)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (Ssource : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      B.partition.band cellIndex pointwiseUpper prefixUpper
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt oldSeed))
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalSmoothFlexibleQuotaAt
        (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
          certificate deltaStar
          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed)
          qTilde)
        qTilde
        (Int.ofNat
          (completeLabelMultiplicity (yNat B.sampleData.n)
              (R.paperFixedExceptionalFactors deltaStar) 1 +
            completeLabelMultiplicity (yNat B.sampleData.n)
              R.prechargeBaseState 1))
        d) :=
  bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_roundedSource
    B R certificate fixed deltaStar betaProt qTilde oldSeed d
      cellIndex pointwiseUpper prefixUpper Ssource hminus hplus

/-! ## Complete public declaration census -/

#check eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
#check bankPaperCanonicalSymmetricHeightCellMassFamily
#check bankPaperCanonicalSymmetricHeightCellMassFamily_isLittleO
#check eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_scalarCapacity
#check eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_rebalance_capacity
#check bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_feasible_of_source
#check bankPaperCanonicalGuardedStructuredAdditivePlacement_symmetricHeight_of_roundedSource
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_source
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_initialSource_of_rowIntegral
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_ambientSource_initial
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_initialQuota
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_roundedSource
#check eventually_mul_upperTailLength_le_self
#check bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
#check eventually_bankPaperCanonicalSectionEight_twoZeroHeadCell_oneShot
#check eventually_bankPaperCanonicalSectionEight_twoZeroHeadCell_oneShot_relevantLedgerFamily

/-! The actual-data ledger constructor and the actual P87 rounded-endpoint
consumer are the two existing adjacent APIs composed with this terminal. -/

#check bankPaperCanonicalSectionEightAnalyticLedger_of_constructedSmoothQuota_intervalGeometry
#check exists_bankPaperCanonicalActualP87EndpointSelector_of_structuredAdditivePlacement

end BankPaperRealization

end

end Erdos390.WholePaper
