import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCrossMeshScalarTransport
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPostLedgerConnector

/-!
# Fixed-mesh post-ledger bridge with preselected numerical data

The common scalar ledger, final-active-mass upper coefficient, and positive
post-height margin are chosen before the final regular mesh.  This module is
the fixed-mesh consumption kernel for those choices.

Unlike the earlier post-ledger constructor, the theorem below does not choose
a fresh `Cpost` or `postMargin`.  It consumes the literal eventual analytic
bounds exported by the pre-mesh theorem, synchronizes them with a
fixed-numerical rich source, and returns the same finite bridge tuple.
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

/-- Construct the eventual post-ledger bridge on a fixed final mesh while
using the final-mass coefficient and head margin already selected before
that mesh.

`Hpost` is the literal mesh-free analytic event: the quarter-source lower
bound, the norm upper bound with coefficient `CfinalUpper`, and the fixed
physical-mean margin.  No analytic constant is chosen in this theorem. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostLedgerBridgeInputs
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c deltaStar betaProt betaAct : Real}
    {depth N W K0 : Nat}
    (hc : C0 < c)
    (hW : 0 < W)
    (hdelta : 0 < delta)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (cSource : Real)
    (hcSource : 0 < cSource)
    (E : Nat)
    (sourceCellMargin : Real)
    (hE : 0 < E)
    (hElarge :
      2 *
            (∑ p : {p : Nat // p ∈ primesUpTo W},
              bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                c p.1) ≤
          (E : Real) * (cSource / 4))
    (logY Lambda0 mFrozen : Nat → Real)
    (CfinalUpper postMargin : Real)
    (hCfinalUpper : 0 < CfinalUpper)
    (hpostMargin :
      postMargin =
        bankPaperCanonicalSectionNinePostHeightHeadMargin
          E
          (fun _ : {p : Nat // p ∈ primesUpTo W} =>
            bankPaperCanonicalSectionNinePostHeightHeadLinearFloor c W)
          CfinalUpper)
    (hpostMarginPos : 0 < postMargin)
    (X :
      BankPaperCanonicalSectionNinePostHeightFixedRichSourceWitness
        M (c := c) (deltaStar := deltaStar)
          (betaProt := betaProt) (betaAct := betaAct)
          (sourceCellMargin := sourceCellMargin)
          (depth := depth) (N := N) (W := W)
          (K0 := K0) (E := E) hdelta F)
    (Hsync :
      ∀ᶠ n : Nat in atTop,
        ∀ hn : N ≤ n,
          let Y := X.source n hn
          let B := Y.1
          let R := Y.2.1.1
          let certificate := Y.2.1.2
          let T := Y.2.2
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
    (Hpost :
      ∀ᶠ n : Nat in atTop,
        (cSource / 4) * secondOrderScale n ≤
            bankPaperCanonicalSmoothFinalActiveMassFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen
              (F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar) n ∧
          ‖bankPaperCanonicalSmoothFinalActiveMassFamily
              bankPaperCanonicalSectionNinePostHeightPhysicalMu
              logY Lambda0 mFrozen
              (F.extendedGuardedSmoothBaseMass
                W (K0 + 1) betaAct deltaStar) n‖ ≤
            CfinalUpper * ‖secondOrderScale n‖ ∧
          Real.log
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                  .minus) ≤
              bankPaperCanonicalSmoothFinalActiveHeightFamily
                    bankPaperCanonicalSectionNinePostHeightPhysicalMu
                    logY Lambda0 mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n /
                  bankPaperCanonicalSmoothFinalActiveMassFamily
                    bankPaperCanonicalSectionNinePostHeightPhysicalMu
                    logY Lambda0 mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n -
                bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
            bankPaperCanonicalSmoothFinalActiveHeightFamily
                    bankPaperCanonicalSectionNinePostHeightPhysicalMu
                    logY Lambda0 mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n /
                  bankPaperCanonicalSmoothFinalActiveMassFamily
                    bankPaperCanonicalSectionNinePostHeightPhysicalMu
                    logY Lambda0 mFrozen
                    (F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar) n +
                bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ≤
              Real.log
                (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                  .plus)) :
    ∀ᶠ n : Nat in atTop,
      ∀ hn : N ≤ n,
        let Y := X.source n hn
        let B := Y.1
        let R := Y.2.1.1
        let certificate := Y.2.1.2
        let T := Y.2.2
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
  filter_upwards [
      eventually_ge_atTop N,
      Hsync,
      X.ready_event,
      Hpost,
      eventually_secondOrderScale_pos] with
        n _hn hsyncN hreadyN hpostN hscale
  intro hn
  have hs := hsyncN hn
  have hr := hreadyN hn
  have hfinalLowerN := hpostN.1
  have hfinalUpperN := hpostN.2.1
  have hphysicalN := hpostN.2.2
  dsimp only at hs hr ⊢
  rcases hs with
    ⟨hmFrozenSync, hlogYSync, hLambda0Sync⟩
  rcases hr with
    ⟨hBn, htargetBounds, hWB, S, hlo, hhi,
      Rhead, Kphysical, hRheadExponent, hRheadTarget,
      hqRhead, hsourceCellMargin, hTsource⟩
  let B := (X.source n hn).1
  let R := (X.source n hn).2.1.1
  let certificate := (X.source n hn).2.1.2
  let Tsource := (X.source n hn).2.2
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
    simpa only [qn, qTilde] using hfinalLowerN
  have hqnUpper :
      qn ≤ CfinalUpper * secondOrderScale n := by
    calc
      qn ≤ |qn| := le_abs_self _
      _ = ‖qn‖ := (Real.norm_eq_abs _).symm
      _ ≤ CfinalUpper * ‖secondOrderScale n‖ := by
        simpa only [qn, qTilde] using hfinalUpperN
      _ = CfinalUpper * secondOrderScale n := by
        rw [Real.norm_eq_abs, abs_of_pos hscale]
  have hqnPos : 0 < qn :=
    (mul_pos (div_pos hcSource (by norm_num)) hscale).trans_le hqnLower
  have hpost :=
    bankPaperCanonicalSectionNinePostHeight_headMargins_of_linearBounds
      (P := primesUpTo W)
      E hE a b (cSource / 4) CfinalUpper
      (secondOrderScale n) qn target
      ha hb (by positivity) hCfinalUpper hscale hqnPos
      htargetLower htargetUpper hqnLower hqnUpper
      (by simpa only [b] using hElarge)
  dsimp only at hpost
  have hpostVertex :
      ∀ p : {p : Nat // p ∈ primesUpTo W},
        postMargin ≤
          target p / ((Rhead.exponent : Real) * qn) := by
    intro p
    simpa only [hpostMargin, a, hRheadExponent] using hpost.2.1 p
  have hpostZero :
      postMargin ≤
        1 - ∑ p : {p : Nat // p ∈ primesUpTo W},
          target p / ((Rhead.exponent : Real) * qn) := by
    simpa only [hpostMargin, a, hRheadExponent] using hpost.2.2
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
    simpa only [hlocalRatio, qTilde] using hphysicalN
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
