import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerFamilies

/-!
# Statement audit for total source-first ledger families
-/

open Filter Topology Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : 0 < c)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaStarUpper : deltaStar < 1)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (source :
      ∀ n, N ≤ n →
        Σ B : BridgeData (PaperHeadSimplex.Tag P) Band,
          BankPaperCanonicalGuardedTailFiber
              c depth B.sampleData.n ×
            BarycentricTarget B.sampleData)
    (Hsource :
      ∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let X := source n hn
          let B := X.1
          let R := X.2.1.1
          let certificate := X.2.1.2
          let T := X.2.2
          let alpha :=
            bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct
          let qTilde :=
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n
          B.sampleData.n = n ∧
            B.sampleData.W = W ∧
            qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass
                R certificate deltaStar B.sampleData.W
                  (K0 + 1) betaAct ∧
            1 ≤ qTilde ∧
            B.sampleData.HeadPatternsSeparated ∧
            bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
              R.roughCanonicalGuardedRow
                certificate deltaStar (K0 + 1) 1 ∧
            (0 ≤ alpha ∧ alpha ≤ 1) ∧
            (0 ≤ betaProt / B.L ∧ betaProt / B.L ≤ 1) ∧
            BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
              (K := K0 + 1) B R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              T deltaStar betaProt alpha
                (betaProt + betaAct) qTilde ∧
            certificate.prechargedTailTarget =
              (F.certificate n hn).prechargedTailTarget) :
    ∃ logY Lambda0 mFrozen : Nat → Real,
      logY = F.extendedPrechargedTailLogTarget ∧
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar)) ∧
      ∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let X := source n hn
          let B := X.1
          let R := X.2.1.1
          let certificate := X.2.1.2
          let T := X.2.2
          let alpha :=
            bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct
          let qTilde :=
            F.extendedGuardedSmoothBaseMass
              W (K0 + 1) betaAct deltaStar n
          mFrozen n =
              bankPaperCanonicalTopFrozenSmoothFrozenMass
                (K := K0 + 1) B R certificate
                  deltaStar betaProt alpha ∧
            logY n =
              bankPaperCanonicalSectionNinePostHeightLogY
                B R certificate ∧
            Lambda0 n =
              bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                (K0 + 1) B R certificate T
                  deltaStar betaProt alpha
                    (betaProt + betaAct) qTilde :=
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies
    hc hdeltaStar hdeltaStarUpper F source Hsource

#check
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies

end

end Erdos390.WholePaper
