import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstRichSourceProducer

/-!
# Statement audit for the rich source-first producer

This audit freezes the full expanded producer interface: the literal
combined-charge tail hypotheses, preledger constants, dependent rich source,
thin projection, exact ledger-family source clause, post-ledger readiness,
and canonical guard geometry.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

set_option maxHeartbeats 2400000 in
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hdeltaStar : IsPaperCombinedChargeDeltaStar c deltaStar)
    (hW : 0 < W)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 ≤ W)
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hterminal :
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n)) :
    ∃ cSource cUpper : Real, ∃ E : Nat, ∃ sourceCellMargin : Real,
      0 < cSource ∧
        0 < cUpper ∧
        0 < E ∧
        0 < sourceCellMargin ∧
        2 *
              (∑ p : {p : Nat // p ∈ primesUpTo W},
                bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                  c p.1) ≤
            (E : Real) * (cSource / 4) ∧
        (∀ᶠ n : Nat in atTop,
          cSource * secondOrderScale n ≤
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n ∧
            F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n ≤
              cUpper * secondOrderScale n) ∧
        let P := primesUpTo W
        let I :=
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
        let Patterns :=
          PaperHeadSimplex.pattern P
            (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W) E
        let G : ∀ n, Ledger n 2 0 :=
          roughCanonicalBridgeRelevantLedgerFamily depth
        let hw : 0 < delta + eta :=
          add_pos hdelta (M.ratio_pos.trans_le M.ratio_le_eta)
        let RichFiber : Type :=
          Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
          Σ' _hnTail : N ≤ D.n,
          Σ' _hnD : 1 < D.n,
          Σ' _hWD : D.W ≠ 0,
          Σ' _S : ScaleSeparation M D.n D.W,
          Σ' _hlo : (∀ sigma, D.lo sigma =
              physicalBound (I.lower sigma) D.n),
          Σ' _hhi : (∀ sigma, D.hi sigma =
              physicalBound (I.upper sigma) D.n),
            HeadSimplexReserve P
        let ThinFiber : Type :=
          Σ B : BridgeData (PaperHeadSimplex.Tag P)
              (BankPaperCanonicalExponentBand M),
            BankPaperCanonicalGuardedTailFiber
                c depth B.sampleData.n ×
              BarycentricTarget B.sampleData
        let thinOfRich : RichFiber → ThinFiber := fun Z => by
          change
            (Σ' D : StructuredSampleData (PaperHeadSimplex.Tag P),
              Σ' _hnTail : N ≤ D.n,
              Σ' _hnD : 1 < D.n,
              Σ' _hWD : D.W ≠ 0,
              Σ' _S : ScaleSeparation M D.n D.W,
              Σ' _hlo : (∀ sigma, D.lo sigma =
                  physicalBound (I.lower sigma) D.n),
              Σ' _hhi : (∀ sigma, D.hi sigma =
                  physicalBound (I.upper sigma) D.n),
                HeadSimplexReserve P) at Z
          rcases Z with
            ⟨D, hnTail, hnD, hWD, S, hlo, hhi, Rhead⟩
          let Kphysical :=
            bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
          let Tsource :=
            bankPaperCanonicalSectionNineCoherentSourceTarget
              M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
          let Bsource :=
            bankPaperCanonicalSectionNineCoherentSourceBridge
              M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
          refine ⟨Bsource, ?_⟩
          change
            BankPaperCanonicalGuardedTailFiber c depth D.n ×
              BarycentricTarget D
          exact
            ⟨⟨F.realization D.n hnTail, F.certificate D.n hnTail⟩,
              Tsource⟩
        ∃ sourceGeom : ∀ n, N ≤ n → RichFiber,
        ∃ source : ∀ n, N ≤ n → ThinFiber,
          (∀ n hn, source n hn = thinOfRich (sourceGeom n hn)) ∧
          (∀ᶠ n : Nat in atTop,
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
                  (F.certificate n hn).prechargedTailTarget) ∧
          (∀ᶠ n : Nat in atTop,
            ∀ hn : N ≤ n,
              let X := source n hn
              let B := X.1
              let R := X.2.1.1
              let certificate := X.2.1.2
              let T := X.2.2
              let target :
                  {p : Nat // p ∈ primesUpTo W} → Real :=
                fun p =>
                  ((certificate.selectorTailTarget R
                    (R.paperFixedExceptionalFactors
                      deltaStar)).factorization p.1 : Real)
              B.sampleData.n = n ∧
                (∀ p : {p : Nat // p ∈ primesUpTo W},
                  bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
                          c W *
                        secondOrderScale n ≤
                      target p ∧
                    target p ≤
                      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                          c p.1 *
                        secondOrderScale n) ∧
                ∃ _hWB : B.sampleData.W ≠ 0,
                ∃ _S : ScaleSeparation
                    M B.sampleData.n B.sampleData.W,
                ∃ hlo : ∀ sigma, B.sampleData.lo sigma =
                    physicalBound (I.lower sigma) B.sampleData.n,
                ∃ hhi : ∀ sigma, B.sampleData.hi sigma =
                    physicalBound (I.upper sigma) B.sampleData.n,
                ∃ Rhead : HeadSimplexReserve (primesUpTo W),
                ∃ Kphysical : PhysicalInterpolationTarget I,
                  Rhead.exponent = E ∧
                    (∀ p : {p : Nat // p ∈ primesUpTo W},
                      Rhead.target p = target p) ∧
                    F.extendedGuardedSmoothBaseMass
                        W (K0 + 1) betaAct deltaStar n =
                      Rhead.activeMass ∧
                    sourceCellMargin ≤ T.cellMassMargin ∧
                    T =
                      B.barycentricTargetOfPaperData
                        I hlo hhi Rhead Kphysical) ∧
          ∀ᶠ n : Nat in atTop,
            ∀ hn : N ≤ n,
              let X := source n hn
              let B := X.1
              let R := X.2.1.1
              let certificate := X.2.1.2
              ∃ hsep :
                  physicalBound (I.upper .minus) n <
                    physicalBound (I.lower .plus) n,
              ∃ hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
                  (rawCell Patterns I n cell \ (G n).guards).Nonempty,
                B.sampleData =
                    canonicalSampleData
                      (W := W) Patterns I (G n) hsep hremaining ∧
                  BankPaperCanonicalBridgeGuardAgreement
                    (G B.sampleData.n) R certificate deltaStar :=
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceFamilies
    M hc hdeltaStar hW hbetaProt hbetaAct hbetaUpper hKlarge hprefix
      hdelta F hterminal

#check
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceFamilies

end

end Erdos390.WholePaper
