import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightLocalInputConnector
import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourceSelectorDeficitPaperRateClosureConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenEventualOrdinaryLogRateConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenImplementationRateReductionConnector
import Erdos390.WholePaper.BankPaperCanonicalGuardedPostchargeCorrectionRateClosure

/-!
# Uniform paper rate for the placed post-height selector deficit

The eventual ordinary-log connector proves the required pointwise
`B.q / (p * B.L)` estimate only as a local intermediate assertion.  This
file exports that intermediate conclusion for the literal fresh post-height
bridge and its literal placed selector.

No implementation-rate package is assumed.  Its three entries are
constructed from:

* the uniform rounded smooth source-to-guarded valuation defect;
* the eventual aggregate guarded-minus-raw correction defect;
* the uniform Section 9 post-height placement valuation moment.

The balanced complete residual is closed by the same raw, exceptional,
raw-row, and guard chain as in the ordinary-log connector.  Finally the
lower comparison

`cMass * secondOrderScale n <= J.postHeightBridge.q`

converts the natural second-order scale to the exact normalization required
by
`BankPaperCanonicalSectionNinePostHeightDependentInputsAt.selectorDeficit`.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-- The literal placed selector on the fresh post-height bridge eventually
has the exact pointwise deficit rate consumed by
`BankPaperCanonicalSectionNinePostHeightDependentInputsAt`.

The constant is fixed before `n`, the mesh, the bridge, the realization,
the certificate, and the medium prime.  The hypotheses left explicit are
the primitive canonical-family synchronizations and analytic estimates
which are not fields of the finite `J`/`S` packages.  In particular, no
three-term implementation package is an input. -/
theorem
    exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K0 depth : Nat)
    (hTwoW : 2 ≤ W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c deltaStar betaProt betaAct epsilon cMass Azero Cd : Real}
    (hc : 0 < c)
    (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18)
    (hepsilon : 0 < epsilon)
    (hcMass : 0 < cMass)
    (hAzero : 0 ≤ Azero)
    (hCd : 0 ≤ Cd)
    (hprefix : 2 * depth + 1 ≤ W) :
    ∃ Cinitial : Real, 0 ≤ Cinitial ∧
      ∀ᶠ n : Nat in atTop,
        ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta)
          (hmesh : 0 < delta)
          (Bsource : BridgeData (PaperHeadSimplex.Tag Phead)
            (BankPaperCanonicalExponentBand M)),
        Bsource.sampleData.n = n →
        Bsource.sampleData.W = W →
        ∀
          (R : BankPaperRealization Bsource.sampleData.n
            (upperEndpoint Bsource.sampleData.n
              (upperTailLength c Bsource.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            Bsource.sampleData.n R.anchorGuardLeftCore
            R.anchorGuardRightCore (R.centralChangedMarkers depth))
          (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
            (K0 := K0) M Bsource R certificate I deltaStar hmesh)
          (_S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
            M Bsource R certificate I deltaStar hmesh J),
        J.betaProt = betaProt →
        J.betaAct = betaAct →
        ∀
          (hsep :
            physicalBound (I.upper .minus)
                J.postHeightBridge.sampleData.n <
              physicalBound (I.lower .plus)
                J.postHeightBridge.sampleData.n)
          (hremaining :
            ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
              (rawCell Patterns I J.postHeightBridge.sampleData.n cell \
                (G J.postHeightBridge.sampleData.n).guards).Nonempty),
        J.postHeightBridge.sampleData =
            canonicalSampleData
              (W := J.postHeightBridge.sampleData.W)
              Patterns I (G J.postHeightBridge.sampleData.n)
                hsep hremaining →
        J.qTilde =
            bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar J.postHeightBridge.sampleData.W
                (K0 + 1) J.betaAct →
        (0 ≤ J.alpha ∧ J.alpha ≤ 1) →
        (0 ≤ J.beta / J.postHeightBridge.L ∧
          J.beta / J.postHeightBridge.L ≤ 1) →
        (R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar J.postHeightBridge.sampleData.W
            (K0 + 1) 1).Nonempty →
        |(J.d : Real)| ≤
          Cd *
            (secondOrderScale J.postHeightBridge.sampleData.n /
              J.postHeightBridge.L) →
        cMass * secondOrderScale J.postHeightBridge.sampleData.n ≤
          J.postHeightBridge.q →
        (∀ p : BandPrime J.postHeightBridge.sampleData.n
              J.postHeightBridge.sampleData.W,
          ∀ sigma : PhysicalSign,
            (J.postHeightBridge.guardedCellProbability
                (none, sigma)).expect
                (fun m ↦ valuation p.1 (m : Nat)) ≤
              Azero / (p.1 : Real)) →
        ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
            J.postHeightBridge.sampleData.W,
          abs
              (bankPaperCanonicalSelectorValuationDeficit
                R certificate
                (R.paperFixedExceptionalFactors deltaStar)
                (R.roughCanonicalGuardedCandidateSet certificate
                  deltaStar (K0 + 1))
                J.placedPreSelector p) ≤
            Cinitial * J.postHeightBridge.q /
              ((p : Real) * J.postHeightBridge.L) := by
  have hW : 1 < W := by omega
  have hdeltaOne : deltaStar ≤ 1 := by
    exact hdeltaUpper.le.trans (by norm_num)
  obtain ⟨Csource, hCsource, Nsource, hsource⟩ :=
    exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate
      Phead Patterns I Cprom Cbank G W K0 depth hW hHeadLe hc
        betaAct Azero hAzero
  obtain ⟨Cplacement, hCplacement, Nplacement, hplacement⟩ :=
    exists_uniform_sectionNinePostHeightPlacementValuationMoment_paperRate
      Phead Patterns I Cprom Cbank G W K0 depth hW hHeadLe hc
        betaAct Azero Cd hAzero hCd
  let Craw : Real :=
    roughCanonicalBalancedRawSignedValuationConstant
      W K0 c (betaProt + betaAct)
  let Crow : Real :=
    roughCanonicalUniformRawRowCorrectionDensityConstant
      W K0 c (betaProt + betaAct)
  let CguardedRaw : Real :=
    roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant
        W K0 c (betaProt + betaAct) +
      Crow
  have hCraw : 0 ≤ Craw := by
    exact
      roughCanonicalBalancedRawSignedValuationConstant_nonneg
        W K0 hc
  have hCrow : 0 ≤ Crow := by
    exact
      roughCanonicalUniformRawRowCorrectionDensityConstant_nonneg
        W K0 hc
  have hCguardedRaw : 0 ≤ CguardedRaw := by
    dsimp only [CguardedRaw]
    exact
      add_nonneg
        (roughCanonicalUniformGuardedPostchargeCorrectionDensityConstant_pos
          W K0 (beta := betaProt + betaAct) hc).le
        hCrow
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
  have hguardedRaw :=
    eventually_abs_roughCanonicalAggregateGuardedRawCorrectionValuationDefect_le_strictScale
      W K0 (c := c) (beta := betaProt + betaAct)
        (deltaStar := deltaStar) hc hdelta
  have hyCutoff :=
    eventually_yNat_lt_centralAnchorCutoff depth
  let Ccomplete : Real := Craw + Cexceptional + Crow + epsilon
  let Ctotal : Real :=
    Ccomplete + Csource + CguardedRaw + Cplacement
  let Cinitial : Real := Ctotal / cMass
  have hCcomplete : 0 ≤ Ccomplete := by
    dsimp only [Ccomplete]
    exact
      add_nonneg
        (add_nonneg (add_nonneg hCraw hCexceptional) hCrow)
        hepsilon.le
  have hCtotal : 0 ≤ Ctotal := by
    dsimp only [Ctotal]
    exact
      add_nonneg
        (add_nonneg
          (add_nonneg hCcomplete hCsource.le)
          hCguardedRaw)
        hCplacement.le
  have hCinitial : 0 ≤ Cinitial :=
    div_nonneg hCtotal hcMass.le
  refine ⟨Cinitial, hCinitial, ?_⟩
  filter_upwards [
      eventually_ge_atTop Nsource,
      eventually_ge_atTop Nplacement,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      hyCutoff, hguardedRaw, hraw, hcomplete]
      with n hNsource hNplacement hnCutoff hyCutoffN
        hguardedRawN hrawN hcompleteN
  intro delta eta M hmesh Bsource hBn hBW R certificate J _S
    hbetaProt hbetaAct hsep hremaining hcanonical hmassSync
    halpha hbeta hpool hd hmassLower hzeroMean p hpBand
  subst n
  subst W
  cases hbetaProt
  cases hbetaAct
  have hp : p.Prime := prime_of_mem_primeBand hpBand
  have hWp : Bsource.sampleData.W < p :=
    cutoff_lt_of_mem_primeBand hpBand
  have hpY : p ≤ yNat Bsource.sampleData.n :=
    le_yNat_of_mem_primeBand hpBand
  let pBand :
      BandPrime J.postHeightBridge.sampleData.n
        J.postHeightBridge.sampleData.W :=
    ⟨p, hpBand⟩
  let scale : Real :=
    secondOrderScale J.postHeightBridge.sampleData.n /
      ((p : Real) * J.postHeightBridge.L)
  have hvalues :
      ∀ m : J.postHeightBridge.sampleData.Sample,
        J.postHeightBridge.sampleData.value m ∈
          R.roughCanonicalGuardedRow certificate deltaStar
            (K0 + 1) 1 := by
    intro m
    exact
      _S.activeSmooth
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  have hsourceP :=
    hsource J.postHeightBridge R certificate J.Tsource
      deltaStar J.betaProt J.qTilde hNsource rfl
      hsep hremaining hcanonical hmassSync hdeltaOne
      hvalues hpool pBand (hzeroMean pBand)
  have hplacementP :=
    hplacement J.postHeightBridge R certificate J.Tsource
      J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
      deltaStar J.betaProt J.qTilde hNplacement rfl
      hsep hremaining hcanonical hmassSync hdeltaOne
      hvalues _S.activeBroad hpool J.roundedQ0_eq_postHeightBridge
      hd pBand (hzeroMean pBand)
  have hguardedRawP :
      abs
          (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
            certificate deltaStar J.postHeightBridge.sampleData.W
              (K0 + 1)
              (bankPaperCanonicalPostHfitBalancedAlpha
                J.postHeightBridge c K0 J.betaProt J.betaAct)
              (J.betaProt + J.betaAct)
              J.postHeightBridge.L p) ≤
        CguardedRaw * scale := by
    have hbound :=
      hguardedRawN depth R certificate hnCutoff hyCutoffN p hp
    simpa only [
      CguardedRaw, Crow, scale,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      bankPaperCanonicalPostHfitBalancedAlpha,
      BridgeData.L, mul_div_assoc] using hbound
  have himplementation :
      BankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs
        J.postHeightBridge K0 R certificate J.Tsource deltaStar
          J.betaProt J.betaAct J.qTilde J.postHeightActiveSeed
          p scale Csource CguardedRaw Cplacement :=
    bankPaperCanonicalTopFrozenRoundedMediumPrimeImplementationRateInputs_of_smooth_aggregateGuardedRaw_and_placement
      J.postHeightBridge K0 R certificate J.Tsource deltaStar
        J.betaProt J.betaAct J.qTilde J.postHeightActiveSeed
        p scale Csource CguardedRaw Cplacement
        hsourceP hguardedRawP hplacementP
  have hrawP := hrawN p hp hWp hpY
  have hcompleteP :=
    hcompleteN R R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth) certificate p
      (by
        simpa only [
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
          bankPaperCanonicalPostHfitBalancedAlpha,
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
          BridgeData.L] using halpha)
      (by
        simpa only [
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
          BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
          BridgeData.L] using hbeta)
      hp hWp hpY hrawP
  have hcompleteScale :
      abs
          (R.roughCanonicalBalancedCompleteSignedResidual
            J.postHeightBridge.sampleData.W K0 certificate
              deltaStar (J.betaProt + J.betaAct) p) ≤
        Ccomplete * scale := by
    simpa only [
      Ccomplete, Craw, Crow, scale,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      BridgeData.L, mul_div_assoc] using hcompleteP
  have htarget :
      BankPaperCanonicalSignedResidualTargetLedger
        R certificate deltaStar p :=
    bankPaperCanonicalSignedResidualTargetLedger_of_chargeDvd
      (W := J.postHeightBridge.sampleData.W)
      R certificate deltaStar hprefix hp hWp _S.charge_dvd
  have hselector :=
    abs_bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector_deficit_le_scale_of_balancedComplete_and_implementation
      J.postHeightBridge K0 R certificate J.Tsource deltaStar
        J.betaProt J.betaAct J.qTilde J.postHeightActiveSeed
        p scale Ccomplete Csource CguardedRaw Cplacement
        _S.activeSmooth htarget hcompleteScale himplementation
  have hselectorScale :
      abs
          (bankPaperCanonicalSelectorValuationDeficit
            R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            J.placedPreSelector p) ≤
        Ctotal * scale := by
    simpa only [
      Ctotal,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.alpha,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.beta,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightActiveSeed,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
      bankPaperCanonicalPostHfitBalancedAlpha,
      BridgeData.L] using
      hselector
  have hsecond :
      secondOrderScale J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.q / cMass := by
    apply (le_div_iff₀ hcMass).2
    simpa only [mul_comm] using hmassLower
  have hnum :
      Ctotal * secondOrderScale J.postHeightBridge.sampleData.n ≤
        Cinitial * J.postHeightBridge.q := by
    calc
      Ctotal * secondOrderScale J.postHeightBridge.sampleData.n ≤
          Ctotal * (J.postHeightBridge.q / cMass) :=
        mul_le_mul_of_nonneg_left hsecond hCtotal
      _ = Cinitial * J.postHeightBridge.q := by
        dsimp only [Cinitial]
        ring
  have hpReal : (0 : Real) < p := by
    exact_mod_cast hp.pos
  have hdenom :
      0 ≤ (p : Real) * J.postHeightBridge.L :=
    mul_nonneg hpReal.le J.postHeightBridge.L_pos.le
  have hscaleToMass :
      Ctotal * scale ≤
        Cinitial * J.postHeightBridge.q /
          ((p : Real) * J.postHeightBridge.L) := by
    dsimp only [scale]
    calc
      Ctotal *
          (secondOrderScale J.postHeightBridge.sampleData.n /
            ((p : Real) * J.postHeightBridge.L)) =
          (Ctotal *
            secondOrderScale J.postHeightBridge.sampleData.n) /
              ((p : Real) * J.postHeightBridge.L) := by ring
      _ ≤
          (Cinitial * J.postHeightBridge.q) /
            ((p : Real) * J.postHeightBridge.L) :=
        div_le_div_of_nonneg_right hnum hdenom
  exact hselectorScale.trans hscaleToMass

end BankPaperRealization

end

end Erdos390.WholePaper
