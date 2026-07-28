import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPostLedgerConnector

/-!
# Statement audit for source-first post-ledger bridge assembly

This audit freezes the full source-first interface, including the dependent
source synchronization, the retained pre-ledger geometry, and all twelve
pointwise output equalities.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale
open BankPaperRealization

noncomputable section

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hW : 0 < W)
    (hbetaAct : 0 < betaAct)
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (source :
      ∀ n, N ≤ n →
        Σ B : BridgeData
            (PaperHeadSimplex.Tag (primesUpTo W))
            (BankPaperCanonicalExponentBand M),
          BankPaperCanonicalGuardedTailFiber
              c depth B.sampleData.n ×
            BarycentricTarget B.sampleData)
    (cSource : Real)
    (E : Nat)
    (sourceCellMargin : Real)
    (hcSource : 0 < cSource)
    (hE : 0 < E)
    (hElarge :
      2 *
            (∑ p : {p : Nat // p ∈ primesUpTo W},
              bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                c p.1) ≤
          (E : Real) * (cSource / 4))
    (hsourceLower :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤
          F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar n)
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar)))
    (Hsync :
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
                      (betaProt + betaAct) qTilde)
    (Hready :
      ∀ᶠ n : Nat in atTop,
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
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W *
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
                physicalBound
                  (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                    sigma)
                  B.sampleData.n,
            ∃ hhi : ∀ sigma, B.sampleData.hi sigma =
                physicalBound
                  (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                    sigma)
                  B.sampleData.n,
            ∃ Rhead : HeadSimplexReserve (primesUpTo W),
            ∃ Kphysical : PhysicalInterpolationTarget
                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals,
              Rhead.exponent = E ∧
                (∀ p, Rhead.target p = target p) ∧
                F.extendedGuardedSmoothBaseMass
                    W (K0 + 1) betaAct deltaStar n =
                  Rhead.activeMass ∧
                sourceCellMargin ≤ T.cellMassMargin ∧
                T =
                  B.barycentricTargetOfPaperData
                    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                    hlo hhi Rhead Kphysical) :
    ∃ Cpost postMargin : Real,
      0 < Cpost ∧
        postMargin =
          bankPaperCanonicalSectionNinePostHeightHeadMargin
            E
            (fun _ : {p : Nat // p ∈ primesUpTo W} =>
              bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
            Cpost ∧
        0 < postMargin ∧
        ∀ᶠ n : Nat in atTop,
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
            ∃ Rhead : HeadSimplexReserve (primesUpTo W),
            ∃ Kphysical : PhysicalInterpolationTarget
                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals,
            ∃ J :
                BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                  (K0 := K0) M B R certificate
                    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                    deltaStar hdelta,
              J.Tsource = T ∧
                sourceCellMargin ≤ J.Tsource.cellMassMargin ∧
                Rhead.exponent = E ∧
                (∀ p, Rhead.target p = target p) ∧
                J.Tsource =
                    J.postHeightBridge.barycentricTargetOfPaperData
                      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                      J.postHeightHlo J.postHeightHhi Rhead Kphysical ∧
                J.qTilde = Rhead.activeMass ∧
                J.qTilde =
                  F.extendedGuardedSmoothBaseMass
                    W (K0 + 1) betaAct deltaStar n ∧
                J.exponent = E ∧
                J.d =
                  bankPaperCanonicalSmoothDIntFamily
                    bankPaperCanonicalSectionNinePostHeightPhysicalMu
                    logY Lambda0 mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n ∧
                J.betaProt = betaProt ∧
                J.betaAct = betaAct ∧
                J.q0 =
                  bankPaperCanonicalSmoothQ0Family
                    mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n ∧
                J.A0 =
                  bankPaperCanonicalSmoothA0Family
                    logY Lambda0 mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n ∧
                J.qn =
                  bankPaperCanonicalSmoothFinalActiveMassFamily
                    bankPaperCanonicalSectionNinePostHeightPhysicalMu
                    logY Lambda0 mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n ∧
                J.targetInputs.headMargin = postMargin ∧
                J.targetInputs.physicalEta =
                  bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 := by
  exact
    BankPaperRealization.exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceFirstPostLedgerBridgeInputs
      M hc hW hbetaAct hdelta F source cSource E sourceCellMargin
        hcSource hE hElarge hsourceLower logY Lambda0 mFrozen Hledger
        Hsync Hready

#check
  BankPaperRealization.exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceFirstPostLedgerBridgeInputs

end

end Erdos390.WholePaper
