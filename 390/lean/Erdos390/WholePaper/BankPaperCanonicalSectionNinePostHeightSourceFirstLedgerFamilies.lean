import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceResidualConnector
import Erdos390.WholePaper.BankPaperPrechargeExactificationBridge

/-!
# Total source-first ledger families

The Section 8 ledger is a statement about whole natural-indexed families,
whereas the genuine bank, sample, and source target exist only on a tail.
This module performs the required dependent totalization honestly.

One complete dependent source fiber is reused on the finite prefix.  On the
tail, the supplied genuine fiber is used definitionally.  Every analytic
input is eventual, so the finite fallback has no mathematical effect.
The theorem then proves the actual-measure constructor, interval geometry,
and balanced initial realization from the literal source callback and feeds
them to the exact source-first ledger connector.
-/

open Filter Topology Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 800000 in
/-- A tail family of genuine source bridges yields total logarithmic and
frozen-mass families, the exact precharged Section 8 ledger, and pointwise
synchronization with the literal rounded source on the same tail.

The callback contains only finite source data and exact equalities.  It does
not contain an analytic ledger, a post-height bridge, or a final-mass
estimate. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies
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
                    (betaProt + betaAct) qTilde := by
  let X :
      Nat →
        Σ B : BridgeData (PaperHeadSimplex.Tag P) Band,
          BankPaperCanonicalGuardedTailFiber
              c depth B.sampleData.n ×
            BarycentricTarget B.sampleData :=
    fun n =>
      if hn : N ≤ n then
        source n hn
      else
        source N le_rfl
  have hX (n : Nat) (hn : N ≤ n) :
      X n = source n hn := by
    simp only [X, dif_pos hn]
  let B := fun n => (X n).1
  let R := fun n => (X n).2.1.1
  let certificate := fun n => (X n).2.1.2
  let D : Nat → StructuredSampleData (PaperHeadSimplex.Tag P) :=
    fun n => (B n).sampleData
  let T : ∀ n, BarycentricTarget (D n) :=
    fun n => (X n).2.2
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let alpha : Nat → Real := fun n =>
    bankPaperCanonicalPostHfitBalancedAlpha
      (B n) c K0 betaProt betaAct
  let fixed : Nat → Finset Nat := fun n =>
    (R n).paperFixedExceptionalFactors deltaStar
  let bankBase : Nat → Finset Nat := fun n =>
    (R n).prechargeBaseState
  let candidates : Nat → Finset Nat := fun n =>
    (R n).roughCanonicalGuardedCandidateSet
      (certificate n) deltaStar (K0 + 1)
  let preSelector : Nat → Nat → Real := fun n =>
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
      (K := K0 + 1) (B n) (R n) (certificate n)
      deltaStar betaProt (alpha n) (betaProt + betaAct)
        (bankPaperCanonicalScaledActiveSeed (T n) (qTilde n))
  let activeSeed : ∀ n, (D n).Sample → Real := fun n =>
    bankPaperCanonicalScaledActiveSeed (T n) (qTilde n)
  let mFrozen : Nat → Real := fun n =>
    bankPaperCanonicalTopFrozenSmoothFrozenMass
      (K := K0 + 1) (B n) (R n) (certificate n)
        deltaStar betaProt (alpha n)
  let Lambda0 : Nat → Real :=
    bankPaperCanonicalActualFrozenLogMassFamily
      D fixed bankBase candidates preSelector activeSeed
  let logY : Nat → Real :=
    F.extendedPrechargedTailLogTarget
  have Hconstructor :
      ∀ᶠ n : Nat in atTop,
        BankPaperCanonicalActualActiveMeasureConstructor
          (D n) (T n) (candidates n) (preSelector n)
            (activeSeed n) := by
    filter_upwards [eventually_ge_atTop N, Hsource] with
        n hn hsourceN
    have hs := hsourceN hn
    dsimp only at hs
    rcases hs with
      ⟨hBn, hBW, hq, hqOne, hsep, hactiveSmooth,
        halpha, hbetaBox, Hresidual, _hprecharged⟩
    have hfinite :=
      bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_actualActiveMeasureConstructor
        (K := K0 + 1)
        (source n hn).1
        (source n hn).2.1.1
        (source n hn).2.1.2
        (source n hn).2.2
        deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          (source n hn).1 c K0 betaProt betaAct)
        (betaProt + betaAct) (qTilde n)
        hqOne hsep hactiveSmooth halpha hbetaBox
        (fun a ha => (Hresidual.1 a ha).1)
    dsimp only [D, T, B, R, certificate, candidates,
      preSelector, activeSeed, alpha]
    rw [hX n hn]
    exact hfinite
  have Hbalanced :
      ∀ᶠ n : Nat in atTop,
        BankPaperCanonicalTopFrozenBalancedInitialRealization
          depth W K0 n c deltaStar (betaProt + betaAct)
            (fixed n) (bankBase n) (candidates n)
            (preSelector n) := by
    filter_upwards [eventually_ge_atTop N, Hsource] with
        n hn hsourceN
    have hs := hsourceN hn
    dsimp only at hs
    rcases hs with
      ⟨hBn, hBW, hq, _hqOne, _hsep, hactiveSmooth,
        _halpha, _hbetaBox, Hresidual, _hprecharged⟩
    have hvalues :
        ∀ m : (source n hn).1.sampleData.Sample,
          (source n hn).1.sampleData.value m ∈
            (source n hn).2.1.1.roughCanonicalGuardedRow
              (source n hn).2.1.2 deltaStar (K0 + 1) 1 := by
      intro m
      exact hactiveSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr
          ⟨m, rfl⟩)
    have hfinite :=
      bankPaperCanonicalTopFrozenBalancedInitialRealization_of_scaledSeed
        (K0 := K0)
        (source n hn).1
        (source n hn).2.1.1
        (source n hn).2.1.2
        (source n hn).2.2
        deltaStar betaProt betaAct (qTilde n)
        hvalues hq Hresidual.2.1
    dsimp only [fixed, bankBase, candidates, preSelector,
      alpha, B, R, certificate, T]
    rw [hX n hn]
    simpa only [bankPaperCanonicalPostHfitBalancedAlpha,
      hBn, hBW] using hfinite
  have Hgeometry :
      BankPaperCanonicalActualFrozenIntervalGeometry
        (c := c) fixed bankBase candidates := by
    unfold BankPaperCanonicalActualFrozenIntervalGeometry
    filter_upwards [
      eventually_ge_atTop N,
      Hsource,
      eventually_mul_upperTailLength_le_self (K0 + 1) hc]
        with n hn hsourceN hKh
    have hs := hsourceN hn
    dsimp only at hs
    rcases hs with
      ⟨hBn, _hBW, _hq, _hqOne, _hsep, _hactiveSmooth,
        _halpha, _hbetaBox, _Hresidual, _hprecharged⟩
    dsimp only [fixed, bankBase, candidates, R, certificate]
    rw [hX n hn]
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      have ht :=
        (source n hn).2.1.1.paperFixedExceptionalFactors_subset_tail
          deltaStar ha
      rw [hBn] at ht
      simp only [factorInterval, Finset.mem_Ioc] at ht ⊢
      omega
    · intro a ha
      have hb :=
        (source n hn).2.1.1.prechargeBaseState_subset_factorInterval ha
      simpa only [hBn] using hb
    · intro a ha
      have hKhB :
          (K0 + 1) *
                upperTailLength c (source n hn).1.sampleData.n ≤
              (source n hn).1.sampleData.n := by
        simpa only [hBn] using hKh
      have hraw :=
        (source n hn).2.1.1
          |>.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
            (source n hn).2.1.2 deltaStar (K0 + 1) ha
      rw [roughRawCandidateSet_eq_Ioc hKhB] at hraw
      simp only [factorInterval, Finset.mem_Ioc] at hraw ⊢
      unfold upperEndpoint
      omega
  have Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde, logY, Lambda0, activeSeed] using
      (bankPaperCanonicalSectionNinePostHeight_sourceFirstAnalyticLedger_of_actualData
        (betaAct := betaAct)
        (betaTotal := betaProt + betaAct)
        hc hdeltaStar hdeltaStarUpper
        depth W K0 1
        F D T fixed bankBase candidates preSelector mFrozen
        Hconstructor Hgeometry Hbalanced)
  refine ⟨logY, Lambda0, mFrozen, rfl, Hledger, ?_⟩
  filter_upwards [Hsource] with n hsourceN
  intro hn
  have hs := hsourceN hn
  dsimp only at hs
  rcases hs with
    ⟨_hBn, _hBW, _hq, _hqOne, _hsep, hactiveSmooth,
      _halpha, _hbetaBox, _Hresidual, hprecharged⟩
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [mFrozen, alpha, B, R, certificate]
    rw [hX n hn]
  · rw [show logY n = F.extendedPrechargedTailLogTarget n by rfl,
      F.extendedPrechargedTailLogTarget_eq hn,
      ← hprecharged]
    rfl
  · have hround :=
      bankPaperCanonicalTopFrozenRounded_actualFrozenLogMass_eq_qTildeSource
        (K := K0 + 1)
        (source n hn).1
        (source n hn).2.1.1
        (source n hn).2.1.2
        ((source n hn).2.1.1.paperFixedExceptionalFactors deltaStar)
        (source n hn).2.1.1.prechargeBaseState
        (source n hn).2.2
        deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          (source n hn).1 c K0 betaProt betaAct)
        (betaProt + betaAct) (qTilde n) hactiveSmooth
    calc
      Lambda0 n =
          bankPaperCanonicalActualFrozenLogMass
            (source n hn).1.sampleData
            ((source n hn).2.1.1.paperFixedExceptionalFactors deltaStar)
            (source n hn).2.1.1.prechargeBaseState
            ((source n hn).2.1.1.roughCanonicalGuardedCandidateSet
              (source n hn).2.1.2 deltaStar (K0 + 1))
            (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
              (K := K0 + 1)
              (source n hn).1
              (source n hn).2.1.1
              (source n hn).2.1.2
              deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                (source n hn).1 c K0 betaProt betaAct)
              (betaProt + betaAct)
              (bankPaperCanonicalScaledActiveSeed
                (source n hn).2.2 (qTilde n)))
            (bankPaperCanonicalScaledActiveSeed
              (source n hn).2.2 (qTilde n)) := by
        dsimp only [Lambda0,
          bankPaperCanonicalActualFrozenLogMassFamily,
          D, fixed, bankBase, candidates, preSelector, activeSeed,
          T, alpha, B, R, certificate]
        rw [hX n hn]
      _ =
          bankPaperCanonicalActualFrozenLogMass
            (source n hn).1.sampleData
            ((source n hn).2.1.1.paperFixedExceptionalFactors deltaStar)
            (source n hn).2.1.1.prechargeBaseState
            ((source n hn).2.1.1.roughCanonicalGuardedCandidateSet
              (source n hn).2.1.2 deltaStar (K0 + 1))
            (bankPaperCanonicalTopFrozenRoundedSourceSelector
              (K := K0 + 1)
              (source n hn).1
              (source n hn).2.1.1
              (source n hn).2.1.2
              (source n hn).2.2
              deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                (source n hn).1 c K0 betaProt betaAct)
              (betaProt + betaAct) (qTilde n))
            (bankPaperCanonicalTopFrozenRoundedActiveSeed
              (K := K0 + 1)
              (source n hn).1
              (source n hn).2.1.1
              (source n hn).2.1.2
              (source n hn).2.2
              deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                (source n hn).1 c K0 betaProt betaAct)
              (qTilde n)) :=
        hround.symm
      _ =
          bankPaperCanonicalSectionNinePostHeightRoundedLambda0
            (K0 + 1)
            (source n hn).1
            (source n hn).2.1.1
            (source n hn).2.1.2
            (source n hn).2.2
            deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              (source n hn).1 c K0 betaProt betaAct)
            (betaProt + betaAct) (qTilde n) := by
        unfold bankPaperCanonicalSectionNinePostHeightRoundedLambda0
        rw [(source n hn).2.1.1.baseExactificationBank_eq_prechargeBaseState]

end BankPaperRealization

end

end Erdos390.WholePaper
