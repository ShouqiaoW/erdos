import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPostLedgerConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstMassAlgebra
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceResidualConnector
import Erdos390.WholePaper.BankPaperCanonicalBridgeRelevantGuardLedger
import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightTwoZeroOneShotConnector
import Erdos390.Full.RegularMeshPrimeCutoffsEventually

/-!
# A rich source-first producer before the Section 8 ledger

This file constructs the genuine canonical source geometry before choosing
the logarithmic and frozen-mass families.  Its thin projection is stated in
exactly the form consumed by the source-first ledger theorem, while the
separate readiness clause contains exactly the geometry later consumed by
the post-ledger theorem.

The dependent source is totalized by reusing one complete genuine fiber on
the finite prefix.  The rich fiber itself deliberately contains no equality
with the callback index; all such synchronization is eventual.
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

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000 in
/-- Construct the canonical rich source family, its literal thin projection,
the exact source-first ledger input, and the exact post-ledger readiness
input, using only the guarded-tail family and numerical hypotheses.

No analytic ledger, frozen family, post-height bridge, or named source
contract is assumed. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstRichSourceFamilies
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
                    (G B.sampleData.n) R certificate deltaStar := by
  have hC0Pos : (0 : Real) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hdeltaStarPos : 0 < deltaStar := hdeltaStar.1
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  obtain
      ⟨cSource, cUpper, E, hcSource, hcUpper, hE, hElarge, Hmass⟩ :=
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_preledgerSourceMassExponent
      depth W (K0 + 1) hcPos hbetaAct deltaStar F
  let sourceCellMargin : Real :=
    bankPaperCanonicalSectionNinePostHeightHeadMargin E
        (fun _ : {p : Nat // p ∈ primesUpTo W} =>
          bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
        cUpper *
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau
  have hsourceCellMarginPos : 0 < sourceCellMargin := by
    apply mul_pos
    · exact
        bankPaperCanonicalSectionNinePostHeightHeadMargin_pos E _ cUpper hE
          (fun _ =>
            bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos hc hW)
          hcUpper
    · exact
        bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget.tau_pos
  refine
    ⟨cSource, cUpper, E, sourceCellMargin, hcSource, hcUpper, hE,
      hsourceCellMarginPos, hElarge, Hmass, ?_⟩
  let P := primesUpTo W
  have hprime : ∀ p ∈ P, p.Prime := by
    simpa only [P] using
      bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  let Patterns : PaperHeadSimplex.Tag P → Pattern :=
    PaperHeadSimplex.pattern P hprime E
  let G : ∀ n, Ledger n 2 0 :=
    roughCanonicalBridgeRelevantLedgerFamily depth
  have hetaPos : 0 < eta :=
    M.ratio_pos.trans_le M.ratio_le_eta
  have hw : 0 < delta + eta := add_pos hdelta hetaPos
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
  change
    ∃ sourceGeom : ∀ n, N ≤ n → RichFiber,
    ∃ source : ∀ n, N ≤ n → ThinFiber,
      (∀ n hn, source n hn = thinOfRich (sourceGeom n hn)) ∧
      _ ∧ _ ∧ _
  let a : {p : Nat // p ∈ P} → Real :=
    fun _ =>
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W
  let b : {p : Nat // p ∈ P} → Real :=
    fun p =>
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p.1
  have ha : ∀ p, 0 < a p := by
    intro p
    simpa only [a] using
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos hc hW
  have hb : ∀ p, 0 ≤ b p := by
    intro p
    have hpPrime : p.1.Prime := hprime p.1 p.2
    have hpredNat : 0 < p.1 - 1 :=
      Nat.sub_pos_of_lt hpPrime.one_lt
    have hpredReal :
        (0 : Real) < ((p.1 - 1 : Nat) : Real) := by
      exact_mod_cast hpredNat
    dsimp only [b,
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient]
    exact
      (add_pos (div_pos hcPos hpredReal) (by norm_num)).le
  have hfiberHead :
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n) := by
    intro n hn
    dsimp only
    have h := hterminal n hn
    dsimp only at h
    exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.2⟩
  have Hhead :=
    eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds
      (W := W) hc hdeltaStar hW P hprime
        (by
          intro p hp
          exact (mem_primesUpTo.mp hp).2)
        F hfiberHead
  have Hsep := eventually_physicalBound_separated I
  have Hremaining :=
    eventually_guarded_rawCell_nonempty Patterns I G
  have Hmesh :=
    Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.eventually_scaleSeparation
      M hdelta W
  have HmassPaper :
      BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
    simpa only [qTilde] using
      bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
        depth W (K0 + 1) hcPos hbetaAct deltaStar F
  have Hone :=
    eventually_one_le_bankPaperCanonicalActiveMass_of_paperScaleLower
      qTilde HmassPaper
  have hupperStrict :
      ∀ sigma, I.upper sigma < 2 := by
    intro sigma
    cases sigma <;>
      norm_num [I,
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals]
  have HupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I (K0 + 1) hcPos hupperStrict
  have HroughDepth :=
    eventually_mul_upperTailLength_le_self (K0 + 1) hcPos
  have Hagreement :=
    eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
      (c := c) depth deltaStar
  have hbetaNonneg : 0 ≤ betaProt + betaAct :=
    add_nonneg hbetaProt hbetaAct.le
  have Halpha :=
    eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
      (Head := PaperHeadSimplex.Tag P)
      (Band := BankPaperCanonicalExponentBand M)
      W K0 hcPos hbetaNonneg hbetaUpper hKlarge
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have HbetaProtRoom : ∀ᶠ n : Nat in atTop, betaProt ≤ L n :=
    hLTop.eventually (eventually_ge_atTop betaProt)
  have Hresidual :=
    eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget
      (Band := BankPaperCanonicalExponentBand M)
      Patterns I 2 0 G depth W K0
      hcPos hdeltaStarPos hbetaProt hbetaAct
      (by norm_num : (0 : Real) ≤ 0) hbetaProt
      hbetaUpper hKlarge hprefix
  have Hgood :
      ∀ᶠ n : Nat in atTop,
        ∃ Z : RichFiber,
          (∀ hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let alpha :=
              bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct
            let qSource :=
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n
            B.sampleData.n = n ∧
              B.sampleData.W = W ∧
              qSource =
                bankPaperCanonicalGuardedSmoothBaseMass
                  R certificate deltaStar B.sampleData.W
                    (K0 + 1) betaAct ∧
              1 ≤ qSource ∧
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
                  (betaProt + betaAct) qSource ∧
              certificate.prechargedTailTarget =
                (F.certificate n hn).prechargedTailTarget) ∧
          (∀ _hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let target : {p : Nat // p ∈ primesUpTo W} → Real :=
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
          ∀ _hn : N ≤ n,
            let X := thinOfRich Z
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
                  (G B.sampleData.n) R certificate deltaStar := by
    filter_upwards [
        Hmass, Hhead, Hsep, Hremaining, Hmesh, Hone,
        HupperBroad, HroughDepth, Hagreement, Halpha,
        HbetaProtRoom, Hresidual, eventually_secondOrderScale_pos,
        eventually_ge_atTop N, eventually_ge_atTop 2]
      with n hmassN hheadN hsepN hremainingN hmeshN honeN
        hupperBroadN hroughDepthN hagreementN halphaN
        hbetaProtRoomN hresidualN hscaleN hnTail hnTwo
    let D : StructuredSampleData (PaperHeadSimplex.Tag P) :=
      canonicalSampleData
        (W := W) Patterns I (G n) hsepN hremainingN
    have hnD : 1 < D.n := by
      simpa only [D, canonicalSampleData_n] using hnTwo
    have hWD : D.W ≠ 0 := by
      simpa only [D, canonicalSampleData_W] using Nat.ne_of_gt hW
    have S : ScaleSeparation M D.n D.W := by
      simpa only [D, canonicalSampleData_n, canonicalSampleData_W] using
        hmeshN
    have hlo :
        ∀ sigma, D.lo sigma =
          physicalBound (I.lower sigma) D.n := by
      intro sigma
      rfl
    have hhi :
        ∀ sigma, D.hi sigma =
          physicalBound (I.upper sigma) D.n := by
      intro sigma
      rfl
    let R := F.realization n hnTail
    let certificate := F.certificate n hnTail
    let qSource :=
      F.extendedGuardedSmoothBaseMass
        W (K0 + 1) betaAct deltaStar n
    let target : {p : Nat // p ∈ P} → Real :=
      fun p =>
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
            Real)
    have hqLower :
        cSource * secondOrderScale n ≤ qSource := by
      simpa only [qSource] using hmassN.1
    have hqUpper :
        qSource ≤ cUpper * secondOrderScale n := by
      simpa only [qSource] using hmassN.2
    have hquarterLe : cSource / 4 ≤ cSource := by
      nlinarith
    have hqLowerQuarter :
        (cSource / 4) * secondOrderScale n ≤ qSource :=
      (mul_le_mul_of_nonneg_right hquarterLe hscaleN.le).trans hqLower
    have hqPos : 0 < qSource :=
      (mul_pos hcSource hscaleN).trans_le hqLower
    have htargetLower :
        ∀ p, a p * secondOrderScale n ≤ target p := by
      intro p
      simpa only [a, target, P, R, certificate] using
        (hheadN hnTail p).1
    have htargetUpper :
        ∀ p, target p ≤ b p * secondOrderScale n := by
      intro p
      simpa only [b, target, P, R, certificate] using
        (hheadN hnTail p).2
    have hElarge' :
        2 * (∑ p : {p : Nat // p ∈ P}, b p) ≤
          (E : Real) * (cSource / 4) := by
      simpa only [P, b] using hElarge
    let margin :=
      bankPaperCanonicalSectionNinePostHeightHeadMargin E a cUpper
    have hmargins :=
      bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
        E hE a b (cSource / 4) cUpper
        (secondOrderScale n) qSource target
        ha hb (by positivity) hcUpper hscaleN hqPos
        htargetLower htargetUpper hqLowerQuarter hqUpper hElarge'
    have hmarginPos : 0 < margin := by
      simpa only [margin] using hmargins.1
    have hvertex :
        ∀ p, margin ≤ target p / ((E : Real) * qSource) := by
      simpa only [margin] using hmargins.2.1
    have hzero :
        margin ≤
          1 - ∑ p : {p : Nat // p ∈ P},
            target p / ((E : Real) * qSource) := by
      simpa only [margin] using hmargins.2.2
    let Rhead : HeadSimplexReserve P :=
      bankPaperCanonicalSectionNineCoherentSourceHeadReserve
        E qSource target margin hE hqPos hmarginPos hvertex hzero
    let Kphysical :=
      bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
    let Tsource :=
      bankPaperCanonicalSectionNineCoherentSourceTarget
        M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    let Bsource :=
      bankPaperCanonicalSectionNineCoherentSourceBridge
        M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    let Z : RichFiber :=
      ⟨D, hnTail, hnD, hWD, S, hlo, hhi, Rhead⟩
    have hthin :
        thinOfRich Z =
          ⟨Bsource,
            ⟨⟨F.realization n hnTail, F.certificate n hnTail⟩,
              Tsource⟩⟩ := by
      rfl
    have hqActual :
        qSource =
          bankPaperCanonicalGuardedSmoothBaseMass
            R certificate deltaStar Bsource.sampleData.W
              (K0 + 1) betaAct := by
      simp only [
        qSource,
        BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
        dif_pos hnTail, R, certificate, Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_W]
    have hpattern :
        Bsource.sampleData.pattern =
          PaperHeadSimplex.pattern P hprime Rhead.exponent := by
      simp only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_pattern, Patterns, Rhead,
        bankPaperCanonicalSectionNineCoherentSourceHeadReserve_exponent]
    have hheadSeparated :
        Bsource.sampleData.HeadPatternsSeparated := by
      apply
        Erdos390.Full.PaperBridgeFit.StructuredSampleData.headPatternsSeparated_of_paperHeadSimplex
          P hprime E hE
      simp only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_pattern, Patterns]
    have hbounds :=
      bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
        Bsource I
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
                sigma)
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
                sigma)
          hlo hhi
    have hguardAgreement :
        BankPaperCanonicalBridgeGuardAgreement
          (G n) R certificate deltaStar := by
      simpa only [G, R, certificate] using
        hagreementN R certificate
    have hnotGuard :
        ∀ m : Bsource.sampleData.Sample,
          Bsource.sampleData.value m ∉
            R.roughCanonicalGuardSet certificate deltaStar := by
      intro m
      exact
        structuredSample_value_not_fullGuard_of_agreement
          Bsource.sampleData (G n) R certificate deltaStar
          hguardAgreement hbounds.2 (by rfl) m
    have hactiveSmooth :
        bankPaperCanonicalStructuredActiveValues Bsource.sampleData ⊆
          R.roughCanonicalGuardedRow
            certificate deltaStar (K0 + 1) 1 :=
      bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
        Bsource R certificate deltaStar I
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
                sigma)
          (by
            intro sigma
            simpa only [I] using
              bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
                sigma)
          hlo hhi (by
            simpa only [
              Bsource,
              bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
              D, canonicalSampleData_n] using hroughDepthN)
          hnotGuard
    have halpha :
        bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct ∈ Set.Icc (0 : Real) 1 := by
      exact halphaN Bsource (by rfl) (by rfl)
    have hbetaBox :
        0 ≤ betaProt / Bsource.L ∧
          betaProt / Bsource.L ≤ 1 := by
      constructor
      · exact div_nonneg hbetaProt Bsource.L_pos.le
      · apply (div_le_iff₀ Bsource.L_pos).2
        simpa only [
          BridgeData.L, Bsource,
          bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
          D, canonicalSampleData_n, one_mul] using hbetaProtRoomN
    have hTsource :
        Tsource =
          Bsource.barycentricTargetOfPaperData
            I hlo hhi Rhead Kphysical := by
      exact
        bankPaperCanonicalSectionNineCoherentSourceTarget_eq_bridgeTarget
          M D I hlo hhi Rhead Kphysical hdelta hnD hWD S hw
    have hsourceCellMargin :
        sourceCellMargin ≤ Tsource.cellMassMargin := by
      rw [hTsource,
        Bsource.barycentricTargetOfPaperData_cellMassMargin]
      exact le_rfl
    have hqRhead : qSource = Rhead.activeMass := by
      rfl
    have hheadSubset :
        primesUpTo Bsource.sampleData.W ⊆ P := by
      intro p hp
      simpa only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_W, P] using hp
    have htargetCompatibility :
        ∀ p : {p : Nat // p ∈ P},
          p.1 ≤ Bsource.sampleData.W →
            Rhead.target p =
              ((certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar)).factorization
                  p.1 : Real) := by
      intro p _hp
      rfl
    have hchargeDvd :
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget := by
      have h := hterminal n hnTail
      simpa only [R, certificate] using h.2.2.1
    have hresidual :
        BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
          (K := K0 + 1) Bsource R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          Tsource deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              Bsource c K0 betaProt betaAct)
            (betaProt + betaAct) qSource := by
      apply
        hresidualN Bsource (by rfl) (by rfl)
          hsepN hremainingN (by rfl)
          R certificate Tsource qSource hqActual
          hprime Rhead Kphysical hlo hhi hTsource hqRhead
          hpattern hheadSubset hheadSeparated
      · intro sigma
        simpa only [I] using
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one
            sigma
      · intro sigma
        simpa only [I] using
          bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_upper_two
            sigma
      · simpa only [
          Bsource,
          bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
          D, canonicalSampleData_n] using hupperBroadN
      · simpa only [
          Bsource,
          bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
          D, canonicalSampleData_n] using hroughDepthN
      · exact hnotGuard
      · exact htargetCompatibility
      · exact hchargeDvd
    refine ⟨Z, ?_, ?_, ?_⟩
    · intro hn
      have hproof : hn = hnTail := Subsingleton.elim _ _
      subst hn
      rw [hthin]
      dsimp only
      refine
        ⟨rfl, rfl, ?_, ?_, hheadSeparated, hactiveSmooth,
          halpha, hbetaBox, hresidual, rfl⟩
      · simpa only [R, certificate] using hqActual
      · simpa only [qSource, qTilde] using honeN
    · intro _hn
      rw [hthin]
      dsimp only
      refine ⟨rfl, ?_, hWD, S, hlo, hhi, Rhead, Kphysical,
        rfl, ?_, rfl, hsourceCellMargin, hTsource⟩
      intro p
      simpa only [target, P, R, certificate] using hheadN hnTail p
      intro p
      rfl
    · intro _hn
      rw [hthin]
      dsimp only
      refine ⟨hsepN, hremainingN, rfl, ?_⟩
      simpa only [
        Bsource,
        bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData,
        D, canonicalSampleData_n] using hguardAgreement
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp Hgood
  let Nsource := max N N₀
  have hgoodFrom :
      ∀ n, Nsource ≤ n →
        ∃ Z : RichFiber,
          (∀ hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let alpha :=
              bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct
            let qSource :=
              F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar n
            B.sampleData.n = n ∧
              B.sampleData.W = W ∧
              qSource =
                bankPaperCanonicalGuardedSmoothBaseMass
                  R certificate deltaStar B.sampleData.W
                    (K0 + 1) betaAct ∧
              1 ≤ qSource ∧
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
                  (betaProt + betaAct) qSource ∧
              certificate.prechargedTailTarget =
                (F.certificate n hn).prechargedTailTarget) ∧
          (∀ _hn : N ≤ n,
            let X := thinOfRich Z
            let B := X.1
            let R := X.2.1.1
            let certificate := X.2.1.2
            let T := X.2.2
            let target : {p : Nat // p ∈ primesUpTo W} → Real :=
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
          ∀ _hn : N ≤ n,
            let X := thinOfRich Z
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
                  (G B.sampleData.n) R certificate deltaStar := by
    intro n hn
    exact hN₀ n ((le_max_right N N₀).trans hn)
  choose genuine hgenuine using hgoodFrom
  let fallback : RichFiber :=
    genuine Nsource le_rfl
  let sourceGeom : ∀ n, N ≤ n → RichFiber := fun n _hn =>
    if h : Nsource ≤ n then genuine n h else fallback
  let source : ∀ n, N ≤ n → ThinFiber := fun n hn =>
    thinOfRich (sourceGeom n hn)
  refine ⟨sourceGeom, source, ?_, ?_, ?_, ?_⟩
  · intro n hn
    rfl
  · filter_upwards [eventually_ge_atTop Nsource] with n hnLarge
    intro hn
    have hz : sourceGeom n hn = genuine n hnLarge := by
      simp only [sourceGeom, dif_pos hnLarge]
    have hs :
        source n hn = thinOfRich (genuine n hnLarge) := by
      simp only [source, hz]
    rw [hs]
    exact (hgenuine n hnLarge).1 hn
  · filter_upwards [eventually_ge_atTop Nsource] with n hnLarge
    intro hn
    have hz : sourceGeom n hn = genuine n hnLarge := by
      simp only [sourceGeom, dif_pos hnLarge]
    have hs :
        source n hn = thinOfRich (genuine n hnLarge) := by
      simp only [source, hz]
    rw [hs]
    exact (hgenuine n hnLarge).2.1 hn
  · filter_upwards [eventually_ge_atTop Nsource] with n hnLarge
    intro hn
    have hz : sourceGeom n hn = genuine n hnLarge := by
      simp only [sourceGeom, dif_pos hnLarge]
    have hs :
        source n hn = thinOfRich (genuine n hnLarge) := by
      simp only [source, hz]
    rw [hs]
    exact (hgenuine n hnLarge).2.2 hn

end BankPaperRealization

end

end Erdos390.WholePaper
