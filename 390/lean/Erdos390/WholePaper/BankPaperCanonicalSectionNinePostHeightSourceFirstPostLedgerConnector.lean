import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstLedgerFamilies
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstFiniteAssembly

/-!
# Source-first post-ledger bridge assembly

The source reserve and source bridge have already been constructed when the
exact Section 8 ledger is obtained.  This module performs only the remaining
post-ledger work:

* retain the explicit quarter of the preledger source-mass coefficient;
* choose an upper coefficient for the final active mass;
* choose a fresh positive post-height head margin;
* transport the exact local rounded source scalars to the Section 8 families;
* and invoke the finite preconstructed-source assembler.

The positive source margin is retained explicitly and transported to the
preconstructed source target.  The new `postMargin` is chosen separately
from the final-mass upper coefficient supplied by the analytic ledger.
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

noncomputable section

namespace BankPaperRealization

/-- Assemble the eventual post-height bridge after the exact source-first
Section 8 ledger has been constructed.

`Hsync` is exactly the pointwise synchronization returned by
`exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstLedgerFamilies`.
`Hready` contains only the source data which the analytic ledger intentionally
does not remember: the mesh geometry, the preconstructed head/physical
reserve, its exponent, active mass, and exact selector target, together with
the already proved selector-target linear bounds. -/
theorem
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceFirstPostLedgerBridgeInputs
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
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let a : {p : Nat // p ∈ primesUpTo W} → Real :=
    fun _ =>
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W
  let b : {p : Nat // p ∈ primesUpTo W} → Real :=
    fun p =>
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p.1
  have hC0Pos : (0 : Real) < C0 := by
    norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have ha : ∀ p, 0 < a p := by
    intro p
    simpa only [a] using
      bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos hc hW
  have hb : ∀ p, 0 ≤ b p := by
    intro p
    have hpPrime : p.1.Prime :=
      bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
        W p.1 p.2
    have hpredNat : 0 < p.1 - 1 :=
      Nat.sub_pos_of_lt hpPrime.one_lt
    have hpredReal :
        (0 : Real) < ((p.1 - 1 : Nat) : Real) := by
      exact_mod_cast hpredNat
    dsimp only [b,
      bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient]
    exact
      (add_pos (div_pos hcPos hpredReal) (by norm_num)).le
  have Hledger' :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde] using Hledger
  have hsourceLower' :
      ∀ᶠ n : Nat in atTop,
        cSource * secondOrderScale n ≤ qTilde n := by
    simpa only [qTilde] using hsourceLower
  have hfinalLower :=
    eventually_bankPaperCanonicalSectionNinePostHeight_finalActiveMass_ge_quarter_sourceCoefficient
      (c := c) (betaAct := betaAct)
      (mu := bankPaperCanonicalSectionNinePostHeightPhysicalMu)
      W (K0 + 1)
      bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      hcSource qTilde hsourceLower' logY Lambda0 mFrozen Hledger'
  have hfinalUpperBigO :=
    bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
      W (K0 + 1) c betaAct
      bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
      logY Lambda0 mFrozen qTilde Hledger'
  obtain ⟨Cpost, hCpost, hfinalUpper⟩ :=
    hfinalUpperBigO.exists_pos
  let postMargin : Real :=
    bankPaperCanonicalSectionNinePostHeightHeadMargin E a Cpost
  have hpostMarginPos : 0 < postMargin := by
    simpa only [postMargin] using
      bankPaperCanonicalSectionNinePostHeightHeadMargin_pos
        E a Cpost hE ha hCpost
  have hphysical :=
    eventually_bankPaperCanonicalSectionNinePostHeight_smoothPhysicalMean_has_fixed_margin_of_analyticLedger
      W (K0 + 1) hcPos hbetaAct
      logY Lambda0 mFrozen qTilde Hledger'
  refine ⟨Cpost, postMargin, hCpost, ?_, hpostMarginPos, ?_⟩
  · rfl
  · filter_upwards [
      eventually_ge_atTop N,
      Hsync,
      Hready,
      hfinalLower,
      hfinalUpper.bound,
      hphysical,
      eventually_secondOrderScale_pos] with
        n _hn hsyncN hreadyN hfinalLowerN hfinalUpperN
          hphysicalN hscale
    intro hn
    have hs := hsyncN hn
    have hr := hreadyN hn
    dsimp only at hs hr ⊢
    rcases hs with
      ⟨hmFrozenSync, hlogYSync, hLambda0Sync⟩
    rcases hr with
      ⟨hBn, htargetBounds, hWB, S, hlo, hhi,
        Rhead, Kphysical, hRheadExponent, hRheadTarget,
        hqRhead, hsourceCellMargin, hTsource⟩
    let B := (source n hn).1
    let R := (source n hn).2.1.1
    let certificate := (source n hn).2.1.2
    let Tsource := (source n hn).2.2
    have hBnB : B.sampleData.n = n := by
      simpa only [B] using hBn
    let alpha :=
      bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct
    let target :
        {p : Nat // p ∈ primesUpTo W} → Real :=
      fun p =>
        ((certificate.selectorTailTarget R
          (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 :
            Real)
    let q0 :=
      bankPaperCanonicalSectionNinePostHeightRoundedQ0
        (K0 + 1) B R certificate deltaStar betaProt alpha
          (qTilde n)
    let A0 :=
      bankPaperCanonicalSectionNinePostHeightA0
        (K0 + 1) B R certificate Tsource deltaStar betaProt
          alpha (betaProt + betaAct) (qTilde n)
    let d :=
      bankPaperCanonicalSmoothDIntFamily
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        logY Lambda0 mFrozen qTilde n
    let qn :=
      bankPaperCanonicalSmoothFinalActiveMassFamily
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        logY Lambda0 mFrozen qTilde n
    have htargetLower :
        ∀ p, a p * secondOrderScale n ≤ target p := by
      intro p
      simpa only [a, target, B, R, certificate] using
        (htargetBounds p).1
    have htargetUpper :
        ∀ p, target p ≤ b p * secondOrderScale n := by
      intro p
      simpa only [b, target, B, R, certificate] using
        (htargetBounds p).2
    have hqnLower :
        (cSource / 4) * secondOrderScale n ≤ qn := by
      simpa only [qn] using hfinalLowerN
    have hqnUpper :
        qn ≤ Cpost * secondOrderScale n := by
      calc
        qn ≤ |qn| := le_abs_self _
        _ = ‖qn‖ := (Real.norm_eq_abs _).symm
        _ ≤ Cpost * ‖secondOrderScale n‖ := by
          simpa only [qn] using hfinalUpperN
        _ = Cpost * secondOrderScale n := by
          rw [Real.norm_eq_abs, abs_of_pos hscale]
    have hqnPos : 0 < qn :=
      (mul_pos (by positivity) hscale).trans_le hqnLower
    have hpost :=
      bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
        (P := primesUpTo W)
        E hE a b (cSource / 4) Cpost
        (secondOrderScale n) qn target
        ha hb (by positivity) hCpost hscale hqnPos
        htargetLower htargetUpper hqnLower hqnUpper
        (by simpa only [b] using hElarge)
    dsimp only at hpost
    have hpostVertex :
        ∀ p : {p : Nat // p ∈ primesUpTo W},
          postMargin ≤
            target p / ((Rhead.exponent : Real) * qn) := by
      intro p
      simpa only [postMargin, hRheadExponent] using hpost.2.1 p
    have hpostZero :
        postMargin ≤
          1 - ∑ p : {p : Nat // p ∈ primesUpTo W},
            target p / ((Rhead.exponent : Real) * qn) := by
      simpa only [postMargin, hRheadExponent] using hpost.2.2
    have hqRhead' :
        qTilde n = Rhead.activeMass := by
      simpa only [qTilde] using hqRhead
    have hTsource' :
        Tsource =
          B.barycentricTargetOfPaperData
            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
            hlo hhi Rhead Kphysical := by
      simpa only [Tsource, B] using hTsource
    have hq0Family :
        q0 =
          bankPaperCanonicalSmoothQ0Family
            mFrozen qTilde n := by
      dsimp only [q0]
      unfold bankPaperCanonicalSectionNinePostHeightRoundedQ0
        bankPaperCanonicalTopFrozenRoundedActiveMass
        bankPaperCanonicalSmoothQ0Family
      rw [hmFrozenSync]
    have hBL : B.L = L n := by
      change Real.log (B.sampleData.n : Real) =
        Real.log (n : Real)
      rw [hBn]
    have hA0Family :
        A0 =
          bankPaperCanonicalSmoothA0Family
            logY Lambda0 mFrozen qTilde n := by
      dsimp only [A0]
      unfold bankPaperCanonicalSectionNinePostHeightA0
        bankPaperCanonicalSmoothA0Family
        bankPaperCanonicalSmoothFrozenHeightDefect
      rw [hlogYSync, hLambda0Sync, ← hq0Family, hBL]
    have hqnEq :
        qn = q0 - (d : Real) := by
      dsimp only [qn, d]
      unfold bankPaperCanonicalSmoothFinalActiveMassFamily
        bankPaperCanonicalSmoothDRealFamily
      rw [← hq0Family]
    have hq0FamilyB :
        q0 =
          bankPaperCanonicalSmoothQ0Family
            mFrozen qTilde B.sampleData.n := by
      rw [hBnB]
      exact hq0Family
    have hA0FamilyB :
        A0 =
          bankPaperCanonicalSmoothA0Family
            logY Lambda0 mFrozen qTilde B.sampleData.n := by
      rw [hBnB]
      exact hA0Family
    have hdFamilyB :
        d =
          bankPaperCanonicalSmoothDIntFamily
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            logY Lambda0 mFrozen qTilde B.sampleData.n := by
      rw [hBnB]
    have hmean :=
      bankPaperCanonicalSectionNinePostHeightPhysicalMean_eq_smoothFamilyRatio
        B logY Lambda0 mFrozen qTilde q0 A0 d
          hq0FamilyB hA0FamilyB hdFamilyB
    have hlocalRatio :
        (A0 + (d : Real) * L B.sampleData.n) / qn =
          bankPaperCanonicalSmoothFinalActiveHeightFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n /
            bankPaperCanonicalSmoothFinalActiveMassFamily
                bankPaperCanonicalSectionNinePostHeightPhysicalMu
                logY Lambda0 mFrozen qTilde n := by
      calc
        (A0 + (d : Real) * L B.sampleData.n) / qn =
            bankPaperCanonicalSectionNinePostHeightPhysicalMean
              B q0 A0 d := by
          unfold bankPaperCanonicalSectionNinePostHeightPhysicalMean
            bankPaperCanonicalSectionNinePostHeightPhysicalLogMean
            bankPaperCanonicalSectionNinePostHeightActiveHeight
            bankPaperCanonicalSectionNinePostHeightActiveMass
          rw [hqnEq]
          rfl
        _ =
            bankPaperCanonicalSmoothFinalActiveHeightFamily
                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                  logY Lambda0 mFrozen qTilde B.sampleData.n /
              bankPaperCanonicalSmoothFinalActiveMassFamily
                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                  logY Lambda0 mFrozen qTilde B.sampleData.n :=
          hmean
        _ =
            bankPaperCanonicalSmoothFinalActiveHeightFamily
                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                  logY Lambda0 mFrozen qTilde n /
              bankPaperCanonicalSmoothFinalActiveMassFamily
                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                  logY Lambda0 mFrozen qTilde n := by
          rw [hBnB]
    have hphysicalLocal :
        Real.log
              (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                .minus) ≤
            (A0 + (d : Real) * L B.sampleData.n) / qn -
              bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
          (A0 + (d : Real) * L B.sampleData.n) / qn +
                bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
            Real.log
              (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                .plus) := by
      simpa only [hlocalRatio] using hphysicalN
    have hfinite :=
      exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_preconstructedSource_and_postMargin
        (K0 := K0) M B R certificate
        hdelta hWB S hlo hhi Rhead Kphysical Tsource hTsource'
        deltaStar betaProt betaAct (qTilde n) q0 A0 qn d postMargin
        hqRhead' hqnPos hpostMarginPos
        (by
          intro p
          simpa only [target] using hpostVertex p)
        (by simpa only [target] using hpostZero)
        hqnEq hphysicalLocal (by rfl) (by rfl)
    rcases hfinite with
      ⟨J, hJTsource, hJqRhead, hJexponent, hJd,
        hJbetaProt, hJbetaAct, hJq0, hJA0, hJqn,
        hJmargin, hJeta⟩
    have hJTsourceActual : J.Tsource = Tsource :=
      hJTsource.trans hTsource'.symm
    have hJsourceCellMargin :
        sourceCellMargin ≤ J.Tsource.cellMassMargin := by
      rw [hJTsourceActual]
      simpa only [Tsource] using hsourceCellMargin
    refine
      ⟨Rhead, Kphysical, J, ?_, hJsourceCellMargin, hRheadExponent, ?_,
        hJTsource, hJqRhead, ?_, ?_, ?_,
        hJbetaProt, hJbetaAct, ?_, ?_, ?_, hJmargin, hJeta⟩
    · simpa only [Tsource] using hJTsourceActual
    · intro p
      simpa only [target, B, R, certificate] using hRheadTarget p
    · exact hJqRhead.trans hqRhead'.symm
    · exact hJexponent.trans hRheadExponent
    · simpa only [d] using hJd
    · exact hJq0.trans hq0Family
    · exact hJA0.trans hA0Family
    · simpa only [qn] using hJqn

end BankPaperRealization

end

end Erdos390.WholePaper
