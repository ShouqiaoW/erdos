import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourceSelectorDeficitPaperRateClosureConnector
import Erdos390.WholePaper.BankPaperCanonicalBalancedRawSignedValuationResidualBoundConnector
import Erdos390.WholePaper.BankPaperCanonicalDirectOrdinaryLogRateConnector

/-!
# Eventual ordinary-log rate for the rounded frozen-top source

This file composes the three honest reductions already available:

* the elementary balanced raw signed-residual bound;
* the exceptional, raw-row, and guard closure of the balanced complete
  residual;
* the arbitrary-source seven-term selector identity and the direct
  `tPrime / p` summation argument.

The rounded frozen-top selector is kept literally throughout.  In
particular, it is never identified with the legacy no-top Post-Hfit source.
The only remaining source-specific inputs are the three implementation
rates displayed by
`BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs`:
the frozen-top source-to-guarded defect, the guarded/raw defect, and the
structured-placement moment.

The complete-residual estimates naturally use `secondOrderScale`.  A
pointwise lower comparison with the actual bridge mass converts that scale
to the `B.q` normalization consumed by the P87 ordinary-log interface.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-- The generic balanced residual and the three literal frozen-top
implementation rates eventually imply quantitative ordinary-log
compatibility for the actual rounded frozen-top Post-Hfit preselector.

The returned constant multiplies `B.q / B.L`.  It is fixed before `n`, the
bridge data, the realization, the source target, and the placement seed.
-/
theorem
    exists_eventually_bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_implementationRates
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (W K0 depth : Nat)
    {c deltaStar betaProt betaAct epsilon cMass
      Csource CguardedRaw Cplacement : Real}
    (hc : 0 < c)
    (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hepsilon : 0 < epsilon)
    (hcMass : 0 < cMass)
    (hCsource : 0 <= Csource)
    (hCguardedRaw : 0 <= CguardedRaw)
    (hCplacement : 0 <= Cplacement)
    (hTwoW : 2 <= W)
    (hprefix : 2 * depth + 1 <= W) :
    ∃ Clog : Real, 0 <= Clog ∧
      ∀ᶠ n : Nat in atTop,
        ∀ (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        ∀
          (R : BankPaperRealization B.sampleData.n
            (upperEndpoint B.sampleData.n
              (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth))
          (T : BarycentricTarget B.sampleData)
          (qTilde : Real)
          (placementSeed : B.sampleData.Sample -> Real),
        cMass * secondOrderScale n <= B.q ->
        (0 <=
            bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct ∧
          bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct <= 1) ->
        (0 <= (betaProt + betaAct) / B.L ∧
          (betaProt + betaAct) / B.L <= 1) ->
        bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
          R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1 ->
        R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
          certificate.prechargedTailTarget ->
        (∀ p : Nat, p.Prime -> W < p -> p <= yNat n ->
          BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
            B K0 R certificate T deltaStar betaProt betaAct qTilde
              placementSeed p
              (secondOrderScale n / ((p : Real) * L n))
              Csource CguardedRaw Cplacement) ->
        BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
          (W := B.sampleData.W) R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde placementSeed)
          ((B.q / B.L) * Clog) := by
  let Craw : Real :=
    roughCanonicalBalancedRawSignedValuationConstant
      W K0 c (betaProt + betaAct)
  let Crow : Real :=
    roughCanonicalUniformRawRowCorrectionDensityConstant
      W K0 c (betaProt + betaAct)
  have hCraw : 0 <= Craw := by
    exact
      roughCanonicalBalancedRawSignedValuationConstant_nonneg
        W K0 hc
  have hCrow : 0 <= Crow := by
    exact
      roughCanonicalUniformRawRowCorrectionDensityConstant_nonneg
        W K0 hc
  have hraw :=
    eventually_roughCanonicalBalancedRawSignedValuationResidualBound
      W K0 (beta := betaProt + betaAct) hc
  obtain ⟨Cexceptional, hCexceptional, hcomplete⟩ :=
    exists_eventually_roughCanonicalBalancedCompleteSignedResidualBound_of_raw
      W K0 depth
      (c := c) (deltaStar := deltaStar)
      (beta := betaProt + betaAct) (Craw := Craw)
      (epsilon := epsilon)
      hc hdelta hdeltaUpper hepsilon hTwoW hprefix
  let Ccomplete : Real := Craw + Cexceptional + Crow + epsilon
  let Ctotal : Real :=
    Ccomplete + Csource + CguardedRaw + Cplacement
  let Cselector : Real := Ctotal / cMass
  let Klog : Real := 2 * Real.log 4
  let Clog : Real := Cselector * Klog
  have hCcomplete : 0 <= Ccomplete := by
    dsimp only [Ccomplete]
    exact
      add_nonneg
        (add_nonneg (add_nonneg hCraw hCexceptional) hCrow)
        hepsilon.le
  have hCtotal : 0 <= Ctotal := by
    dsimp only [Ctotal]
    exact
      add_nonneg
        (add_nonneg
          (add_nonneg hCcomplete hCsource)
          hCguardedRaw)
        hCplacement
  have hCselector : 0 <= Cselector :=
    div_nonneg hCtotal hcMass.le
  have hKlog : 0 <= Klog := by
    dsimp only [Klog]
    exact mul_nonneg (by norm_num) (Real.log_nonneg (by norm_num))
  have hClog : 0 <= Clog :=
    mul_nonneg hCselector hKlog
  have hbandT :=
    Erdos390.Full.PrimeSums.eventually_bandTReciprocalSum_le W
  refine ⟨Clog, hClog, ?_⟩
  filter_upwards [hraw, hcomplete, hbandT]
      with n hrawN hcompleteN hbandTN
  intro B hBn hBW R certificate T qTilde placementSeed
    hmassLower halpha hbeta hactiveSmooth hchargeDvd himplementation
  subst n
  subst W
  have hpointwise :
      ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
        abs (bankPaperCanonicalSelectorValuationDeficit
          R certificate (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde placementSeed) p) <=
          Cselector * B.q / ((p : Real) * B.L) := by
    intro p hpBand
    have hp : p.Prime := prime_of_mem_primeBand hpBand
    have hWp : B.sampleData.W < p :=
      cutoff_lt_of_mem_primeBand hpBand
    have hpY : p <= yNat B.sampleData.n :=
      le_yNat_of_mem_primeBand hpBand
    have hrawP := hrawN p hp hWp hpY
    have hcompleteP :=
      hcompleteN R R.anchorGuardLeftCore R.anchorGuardRightCore
        (R.centralChangedMarkers depth) certificate p
        halpha hbeta hp hWp hpY hrawP
    have hcompleteScale :
        abs (R.roughCanonicalBalancedCompleteSignedResidual
          B.sampleData.W K0 certificate deltaStar
            (betaProt + betaAct) p) <=
          Ccomplete *
            (secondOrderScale B.sampleData.n /
              ((p : Real) * L B.sampleData.n)) := by
      simpa only [Ccomplete, Craw, Crow, mul_div_assoc] using
        hcompleteP
    have htarget :
        BankPaperCanonicalSignedResidualTargetLedger
          R certificate deltaStar p :=
      bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
        (W := B.sampleData.W) R certificate deltaStar
          hprefix hp hWp hchargeDvd
    have himplementationP :=
      himplementation p hp hWp hpY
    have hselector :=
      abs_bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector_deficit_le_scale_of_balancedComplete_and_implementation
        B K0 R certificate T deltaStar betaProt betaAct qTilde
          placementSeed p
          (secondOrderScale B.sampleData.n /
            ((p : Real) * L B.sampleData.n))
          Ccomplete Csource CguardedRaw Cplacement
          hactiveSmooth htarget hcompleteScale himplementationP
    have hselectorScale :
        abs (bankPaperCanonicalSelectorValuationDeficit
          R certificate (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet
            certificate deltaStar (K0 + 1))
          (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate T deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct) qTilde placementSeed) p) <=
          Ctotal *
            (secondOrderScale B.sampleData.n /
              ((p : Real) * L B.sampleData.n)) := by
      simpa only [Ctotal] using hselector
    have hsecond :
        secondOrderScale B.sampleData.n <= B.q / cMass := by
      apply (le_div_iff₀ hcMass).2
      simpa only [mul_comm] using hmassLower
    have hnum :
        Ctotal * secondOrderScale B.sampleData.n <=
          Cselector * B.q := by
      calc
        Ctotal * secondOrderScale B.sampleData.n <=
            Ctotal * (B.q / cMass) :=
          mul_le_mul_of_nonneg_left hsecond hCtotal
        _ = Cselector * B.q := by
          dsimp only [Cselector]
          ring
    have hpReal : (0 : Real) < p := by
      exact_mod_cast hp.pos
    have hdenom :
        0 <= (p : Real) * L B.sampleData.n :=
      mul_nonneg hpReal.le (L_pos B.n_gt_one).le
    have hscaleToMass :
        Ctotal *
            (secondOrderScale B.sampleData.n /
              ((p : Real) * L B.sampleData.n)) <=
          Cselector * B.q / ((p : Real) * B.L) := by
      have hL :
          L B.sampleData.n = B.L := by
        rfl
      rw [← hL]
      calc
        Ctotal *
            (secondOrderScale B.sampleData.n /
              ((p : Real) * L B.sampleData.n)) =
            (Ctotal * secondOrderScale B.sampleData.n) /
              ((p : Real) * L B.sampleData.n) := by ring
        _ <= (Cselector * B.q) /
              ((p : Real) * L B.sampleData.n) :=
          div_le_div_of_nonneg_right hnum hdenom
    exact hselectorScale.trans hscaleToMass
  have hordinary :=
    bankPaperCanonicalTopFrozenRoundedPostHfitInitialSelector_ordinaryLogCompatibleUpTo_of_pointwisePaperRate
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        T deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde placementSeed
        Cselector Klog hCselector hpointwise hbandTN
  simpa only [Clog] using hordinary

end BankPaperRealization

end

end Erdos390.WholePaper
