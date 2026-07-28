import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellOuterCapacityConnector

/-! # Statement audit for the outer two-zero-head-cell capacity connector -/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-- Expanded terminal audit: the existing Section 8 ledger, the canonical
P87 sample identification, and the uniform P87 cell-mass margin imply both
literal scalar capacity inequalities in each physical sign. -/
example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct mu marginFloor : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (hmarginFloor : 0 < marginFloor)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde))
    (betaProt : Real) :
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
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall sigma : PhysicalSign,
              0 <= qTilde n * T.baseline.cellMass (none, sigma) +
                bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
                  mu logY Lambda0 mFrozen qTilde n ∧
              qTilde n * T.baseline.cellMass (none, sigma) +
                  bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
                    mu logY Lambda0 mFrozen qTilde n <=
                (Fintype.card
                    (B.sampleData.SampleAt (none, sigma)) : Real) *
                  (1 - betaProt / B.L) :=
  eventually_bankPaperCanonicalSymmetricInitialAndHeight_twoZeroHeadCell_scalarCapacity
    (P := P) (Band := Band)
    Phead I Cprom Cbank ledger W K hc hbeta hmu hmarginFloor
      logY Lambda0 mFrozen qTilde Hledger betaProt

/-! ## Complete public declaration census -/

#check secondOrderScale_isLittleO_natCast
#check bankPaperCanonical_marginFloor_le_baseline_cellMass
#check bankPaperCanonical_baseline_cellMass_le_one
#check bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
#check bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily_isLittleO
#check bankPaperCanonicalZeroHeadCellDensityFloor
#check bankPaperCanonicalZeroHeadCellDensityFloor_pos
#check bankPaperCanonicalZeroHeadCellDensityFloor_le
#check eventually_bankPaperCanonicalSymmetricInitialAndHeight_twoZeroHeadCell_scalarCapacity
#check eventually_bankPaperCanonicalSymmetricInitialAndHeight_twoZeroHeadCell_rebalance_capacity

end BankPaperRealization

end

end Erdos390.WholePaper
