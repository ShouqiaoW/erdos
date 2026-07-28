import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourcePrebridgeConnector
import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpRoundedValuationRateConnector

/-!
# Paper-rate valuation cost of the fresh post-height baseline

The rounded frozen-top source and the final post-height baseline are not the
same structured seed.  This file controls the valuation cost of replacing
the former by the latter.

There are three exact pieces.

* The structured placement moment is the tagged valuation moment of the new
  seed minus that of the old rounded seed.
* The old rounded moment is the synchronized scaled moment plus its literal
  nearest-integer correction.
* The new seed is the scaled post-height target at mass `q0-d`.

At a medium prime, both synchronized scaled moments are compared with the
same guarded smooth-base moment by the sharp common-profile theorem.  The
remaining mass change is bounded by `|q0-qTilde| + |d|`; nearest-integer
rounding gives the first term, and the Section 8 height ledger supplies the
second on the `secondOrderScale / L` scale.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.DickmanBasic
open Erdos390.Full.Scale
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPrimePowerChamberError
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.FiniteProbability
open Erdos390.Full.PaperRawTiltedValuationMeanRows

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Exact arbitrary-seed replacement moment -/

/-- On the complete smooth row, replacing an arbitrary two-zero-cell source
seed by an arbitrary fresh seed changes every valuation moment by the
difference of the two tagged seed moments. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_arbitrarySeedReplacement_eq
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed newSeed : B.sampleData.Sample → Real)
    (outsideSelector : Nat → Real)
    (houtsideActive : ∀ a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData →
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 →
      outsideSelector a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed outsideSelector)
        newSeed p =
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation p (B.sampleData.value m)) -
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation p (B.sampleData.value m) := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    intro m
    exact hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  unfold
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
              (K := K) B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed outsideSelector)
              newSeed a -
          bankPaperCanonicalTwoZeroHeadCellSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed outsideSelector a) *
          (a.factorization p : Real)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData newSeed a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) * valuation p a := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_arbitrarySeed_sub_twoZeroSource_of_active
          (K := K) B R certificate deltaStar betaProt oldSeed newSeed
            outsideSelector houtsideActive a]
      rfl
    _ =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData newSeed a *
            valuation p a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a * valuation p a := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ =
        (∑ m : B.sampleData.Sample,
          newSeed m * valuation p (B.sampleData.value m)) -
          ∑ m : B.sampleData.Sample,
            oldSeed m * valuation p (B.sampleData.value m) := by
      rw [
        sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
          B.sampleData newSeed
            (R.roughCanonicalGuardedRow certificate deltaStar K 1)
            hvalues p,
        sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
          B.sampleData oldSeed
            (R.roughCanonicalGuardedRow certificate deltaStar K 1)
            hvalues p]

/-- For the literal rounded frozen-top source and the paper-faithful
post-height target, the placement moment is the post-height scaled moment
minus the synchronized scaled source moment and its nearest-integer term. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacementValuationMoment_eq
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hactiveBroad : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        roughBroadLowerBlock B.sampleData.n
          (upperTailLength c B.sampleData.n) K)
    (p : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) p =
      bankPaperCanonicalScaledActiveValuationMoment
          (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
          (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
            B R certificate deltaStar betaProt alpha qTilde p) := by
  let oldSeed :=
    bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
      B R certificate Tsource deltaStar betaProt alpha qTilde
  let newSeed :=
    bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H
  have hcompat :
      BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility
        (K := K) B R certificate Tsource deltaStar betaProt
          alpha beta qTilde :=
    bankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility_of_broadSupport
      (K := K) B R certificate Tsource deltaStar betaProt
        alpha beta qTilde hactiveSmooth hactiveBroad
  have hexact :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment_arbitrarySeedReplacement_eq
      (K := K) B R certificate deltaStar betaProt oldSeed newSeed
        (bankPaperCanonicalGlobalCorrectedOutsideSelectorWithTop (K := K)
          B R certificate deltaStar alpha beta oldSeed)
        hcompat hactiveSmooth p
  have hold :=
    sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_valuation_eq_scaled_add_nearestInteger
      (K := K) B R certificate Tsource deltaStar betaProt alpha qTilde p
  calc
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) p =
      (∑ m : B.sampleData.Sample,
          newSeed m * valuation p (B.sampleData.value m)) -
        ∑ m : B.sampleData.Sample,
          oldSeed m * valuation p (B.sampleData.value m) := by
      simpa only [
        oldSeed, newSeed,
        bankPaperCanonicalTopFrozenRoundedSourceSelector,
        bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop] using hexact
    _ =
      bankPaperCanonicalScaledActiveValuationMoment
          (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
          (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment (K := K)
            B R certificate deltaStar betaProt alpha qTilde p) := by
      rw [show
        (∑ m : B.sampleData.Sample,
            newSeed m * valuation p (B.sampleData.value m)) =
          bankPaperCanonicalScaledActiveValuationMoment
            (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
            (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p by
          rfl]
      simpa only [oldSeed] using congrArg
        (fun x : Real =>
          bankPaperCanonicalScaledActiveValuationMoment
              (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
              (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) p -
            x)
        hold

/-! ## A finite mass-shift estimate -/

/-- Changing only the scalar mass of one barycentric target costs its mass
change times the convexly averaged cell valuation mean. -/
theorem
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_of_massChange
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (T : BarycentricTarget B.sampleData)
    (qNew qOld Aval Cmass : Real) (p : Nat)
    (hp : p.Prime)
    (hmean : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      (B.guardedCellProbability cell).expect
          (fun m ↦ valuation p (m : Nat)) ≤ Aval / (p : Real))
    (hmass :
      |qNew - qOld| ≤
        Cmass * (secondOrderScale B.sampleData.n / B.L)) :
    |bankPaperCanonicalScaledActiveValuationMoment T qNew p -
        bankPaperCanonicalScaledActiveValuationMoment T qOld p| ≤
      (Cmass * Aval) *
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L)) := by
  let mean : Real :=
    ∑ cell : Cell (PaperHeadSimplex.Tag P),
      T.cellProbability cell *
        (B.guardedCellProbability cell).expect
          (fun m ↦ valuation p (m : Nat))
  have hpR : 0 < (p : Real) := by exact_mod_cast hp.pos
  have hL : 0 < B.L := B.L_pos
  have hmassRhs0 :
      0 ≤ Cmass * (secondOrderScale B.sampleData.n / B.L) :=
    (abs_nonneg (qNew - qOld)).trans hmass
  have hmean0 : 0 ≤ mean := by
    dsimp only [mean]
    exact Finset.sum_nonneg fun cell _hcell =>
      mul_nonneg (T.cellProbability_pos cell).le
        ((B.guardedCellProbability cell).expect_nonneg _
          (fun m ↦ valuation_nonneg p (m : Nat)))
  have hmeanUpper : mean ≤ Aval / (p : Real) := by
    dsimp only [mean]
    calc
      (∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell *
            (B.guardedCellProbability cell).expect
              (fun m ↦ valuation p (m : Nat))) ≤
        ∑ cell : Cell (PaperHeadSimplex.Tag P),
          T.cellProbability cell * (Aval / (p : Real)) := by
            apply Finset.sum_le_sum
            intro cell _hcell
            exact mul_le_mul_of_nonneg_left
              (hmean cell) (T.cellProbability_pos cell).le
      _ = Aval / (p : Real) := by
        rw [← Finset.sum_mul, T.sum_cellProbability, one_mul]
  rw [
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans,
    bankPaperCanonicalScaledActiveValuationMoment_eq_q_mul_cellMeans]
  change |qNew * mean - qOld * mean| ≤ _
  rw [← sub_mul, abs_mul, abs_of_nonneg hmean0]
  calc
    |qNew - qOld| * mean ≤
        (Cmass * (secondOrderScale B.sampleData.n / B.L)) *
          (Aval / (p : Real)) := by
      exact mul_le_mul hmass hmeanUpper hmean0
        hmassRhs0
    _ = (Cmass * Aval) *
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L)) := by
      field_simp [hpR.ne', hL.ne']

/-! ## Uniform sharp post-height placement rate -/

/-- The arbitrary post-height seed replacement has the medium-prime paper
rate.  The only height input is the literal pointwise consequence of the
Section 8 ledger, `|d| = O(secondOrderScale / L)`; all valuation estimates
are discharged here by the existing canonical common-profile chain.

The constant is uniform in the bridge, bank, certificate, source target,
post-height target data, and medium prime. -/
theorem
    exists_uniform_sectionNinePostHeightPlacementValuationMoment_paperRate
    (Phead : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag Phead → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W K0 depth : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    {c : Real} (hc : 0 < c)
    (betaAct Azero Cd : Real)
    (hAzero : 0 ≤ Azero) (hCd : 0 ≤ Cd) :
    ∃ Cplacement : Real, 0 < Cplacement ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag Phead) Band)
        (R : BankPaperRealization B.sampleData.n
          (upperEndpoint B.sampleData.n
            (upperTailLength c B.sampleData.n)))
        (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (Tsource : BarycentricTarget B.sampleData)
        (hlo : ∀ sigma, B.sampleData.lo sigma =
          physicalBound (I.lower sigma) B.sampleData.n)
        (hhi : ∀ sigma, B.sampleData.hi sigma =
          physicalBound (I.upper sigma) B.sampleData.n)
        {q0 A0 : Real} {d : Int} {exponent : Nat}
        {activeHeadTarget : {p : Nat // p ∈ Phead} → Real}
        (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
          B I q0 A0 d exponent activeHeadTarget)
        (deltaStar betaProt qTilde : Real),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Patterns I (G B.sampleData.n)
                hsep hremaining →
          qTilde = bankPaperCanonicalGuardedSmoothBaseMass R certificate
              deltaStar B.sampleData.W (K0 + 1) betaAct →
          deltaStar ≤ 1 →
          (∀ m : B.sampleData.Sample,
            B.sampleData.value m ∈
              R.roughCanonicalGuardedRow certificate deltaStar
                (K0 + 1) 1) →
          (∀ m : B.sampleData.Sample,
            B.sampleData.value m ∈
              roughBroadLowerBlock B.sampleData.n
                (upperTailLength c B.sampleData.n) (K0 + 1)) →
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W (K0 + 1) 1).Nonempty →
          q0 =
            bankPaperCanonicalTopFrozenRoundedActiveMass (K := K0 + 1)
              B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde →
          |(d : Real)| ≤
            Cd * (secondOrderScale B.sampleData.n / B.L) →
          ∀ p : BandPrime B.sampleData.n B.sampleData.W,
            (∀ sigma : PhysicalSign,
              (B.guardedCellProbability (none, sigma)).expect
                  (fun m ↦ valuation p.1 (m : Nat)) ≤
                Azero / (p.1 : Real)) →
            |bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalTopFrozenRoundedSourceSelector
                  (K := K0 + 1) B R certificate Tsource deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    (betaProt + betaAct) qTilde)
                (bankPaperCanonicalSectionNinePostHeightActiveSeed
                  B I hlo hhi H) p.1| ≤
              Cplacement *
                (secondOrderScale B.sampleData.n /
                  ((p.1 : Real) * B.L)) := by
  obtain ⟨Csource, hCsource, Nsource, hsource⟩ :=
    exists_uniform_topFrozenRoundedSmoothSourceToGuardedValuationDefectBound_paperRate
      Phead Patterns I Cprom Cbank G W K0 depth hW hHeadLe hc
        betaAct Azero hAzero
  obtain ⟨Csharp, hCsharp, Nsharp, hsharp⟩ :=
    exists_uniform_scaledActive_sub_guardedSmoothBase_valuationMoment_paperRate
      Phead Patterns I Cprom Cbank G W (K0 + 1) depth hW hHeadLe hc
  obtain ⟨Ccell, hCcell, Ncell, hcellProfile⟩ :=
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
      Patterns I Cprom Cbank G W hW hHeadLe
  let Amain : Real := 6 / rho DickmanBasic.U
  let Aval : Real := Amain + Ccell
  let Cmass : Real := Cd + 1
  let Cplacement : Real :=
    Csource + |betaAct| * Csharp + Cmass * Aval + 1
  have hAmain : 0 < Amain := by
    dsimp only [Amain]
    exact div_pos (by norm_num) DickmanBasic.rho_U_pos
  have hAval : 0 < Aval := by
    dsimp only [Aval]
    exact add_pos hAmain hCcell
  have hCmass : 0 ≤ Cmass := by
    dsimp only [Cmass]
    linarith
  have hbetaTerm : 0 ≤ |betaAct| * Csharp :=
    mul_nonneg (abs_nonneg betaAct) hCsharp.le
  have hmassTerm : 0 ≤ Cmass * Aval :=
    mul_nonneg hCmass hAval.le
  have hCplacement : 0 < Cplacement := by
    dsimp only [Cplacement]
    nlinarith
  have hscaleEvent : ∀ᶠ n : Nat in atTop,
      1 ≤ secondOrderScale n / L n :=
    secondOrderScale_div_L_tendsto_atTop.eventually
      (eventually_ge_atTop 1)
  have hLtendsto : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogEvent : ∀ᶠ n : Nat in atTop, 1 ≤ L n :=
    hLtendsto.eventually (eventually_ge_atTop 1)
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscaleEvent
  obtain ⟨Nlog, hNlog⟩ := Filter.eventually_atTop.mp hlogEvent
  refine
    ⟨Cplacement, hCplacement,
      max 2 (max Nsource (max Nsharp (max Ncell (max Nscale Nlog)))),
      ?_⟩
  intro Band _instBand _instBandDec B R certificate Tsource hlo hhi
    q0 A0 d exponent activeHeadTarget H deltaStar betaProt qTilde
    hN hBW hsep hremaining hcanonical hmassSync hdeltaUpper
    hvalues hactiveBroad hpool hq0 hd p hzeroMean
  have hn : 1 < B.sampleData.n := by omega
  have hNsource : Nsource ≤ B.sampleData.n := by omega
  have hNsharp : Nsharp ≤ B.sampleData.n := by omega
  have hNcell : Ncell ≤ B.sampleData.n := by omega
  have hNscaleBound : Nscale ≤ B.sampleData.n := by omega
  have hNlogBound : Nlog ≤ B.sampleData.n := by omega
  have hp := prime_of_mem_primeBand p.2
  have hpR : 0 < (p.1 : Real) := by exact_mod_cast hp.pos
  have hL : 0 < B.L := B.L_pos
  have hLone : 1 ≤ B.L := by
    simpa only [BridgeData.L] using hNlog B.sampleData.n hNlogBound
  have hscaleHeightOne :
      1 ≤ secondOrderScale B.sampleData.n / B.L := by
    simpa only [BridgeData.L] using
      hNscale B.sampleData.n hNscaleBound
  let scale : Real :=
    secondOrderScale B.sampleData.n / ((p.1 : Real) * B.L)
  have hscale0 : 0 ≤ scale := by
    dsimp only [scale]
    exact div_nonneg (secondOrderScale_pos (by omega)).le
      (mul_nonneg hpR.le hL.le)
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  let qn :=
    bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  have hqBound :
      |qTilde| ≤ |betaAct| * secondOrderScale B.sampleData.n := by
    rw [hmassSync]
    exact
      abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
        R certificate deltaStar B.sampleData.W (K0 + 1) betaAct hn
  have hprincipalRaw :=
    hsharp B R certificate Tpost deltaStar betaAct qTilde
      hNsharp hBW hsep hremaining hcanonical hmassSync hpool p
  have hprincipal :
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        (|betaAct| * Csharp) * scale := by
    calc
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1| ≤
        |qTilde| * (Csharp / ((p.1 : Real) * B.L)) :=
          hprincipalRaw
      _ ≤ (|betaAct| * secondOrderScale B.sampleData.n) *
          (Csharp / ((p.1 : Real) * B.L)) := by
        exact mul_le_mul_of_nonneg_right hqBound
          (div_nonneg hCsharp.le (mul_nonneg hpR.le hL.le))
      _ = (|betaAct| * Csharp) * scale := by
        dsimp only [scale]
        ring
  have hsourceRaw :=
    hsource B R certificate Tsource deltaStar betaProt qTilde
      hNsource hBW hsep hremaining hcanonical hmassSync hdeltaUpper
        hvalues hpool p hzeroMean
  have hsourceBound :
      |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment (K := K0 + 1)
            B R certificate deltaStar betaAct p.1 +
        bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            qTilde p.1| ≤
        Csource * scale := by
    unfold
      RoughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefectBound
      at hsourceRaw
    rw [
      roughCanonicalTopFrozenRoundedSmoothSourceToGuardedValuationDefect_eq_scaled_sub_guardedBase_add_nearestInteger
        B K0 R certificate Tsource deltaStar betaProt betaAct qTilde p.1
          (by omega) hdeltaUpper hvalues] at hsourceRaw
    simpa only [scale] using hsourceRaw
  have hcellRaw :=
    hcellProfile B hNcell hBW hsep hremaining hcanonical p
  let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
  let mainSum := ∑ k ∈ positiveExponents Kcut,
    paperDivisibilityMain B.sampleData.n (p.1 ^ k)
  have hpY : p.1 ≤ yNat B.sampleData.n :=
    le_yNat_of_mem_primeBand p.2
  have hY4pos : 0 < yNat B.sampleData.n ^ 4 :=
    pow_pos (hp.pos.trans_le hpY) 4
  have hpK : p.1 ^ Kcut ≤ yNat B.sampleData.n ^ 4 := by
    dsimp only [Kcut]
    exact Nat.pow_log_le_self p.1 hY4pos.ne'
  have hmainTerm (k : Nat) (hk : k ∈ positiveExponents Kcut) :
      0 ≤ paperDivisibilityMain B.sampleData.n (p.1 ^ k) ∧
        paperDivisibilityMain B.sampleData.n (p.1 ^ k) ≤
          (1 / rho DickmanBasic.U) * singleWeight p.1 k := by
    have hkLe : k ≤ Kcut := (mem_positiveExponents.mp hk).2
    have hpk :
        p.1 ^ k ≤ yNat B.sampleData.n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hkLe).trans hpK
    have hraw :=
      paperDivisibilityMain_nonneg_le hn (pow_pos hp.pos k) hpk
    refine ⟨hraw.1, ?_⟩
    have habs :=
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp hpk
    simpa only [abs_of_nonneg hraw.1] using habs
  have hweight :
      (∑ k ∈ positiveExponents Kcut, singleWeight p.1 k) ≤
        6 / (p.1 : Real) :=
    sum_singleWeight_positiveExponents_le hp.two_le
  have hmainUpper : mainSum ≤ Amain / (p.1 : Real) := by
    calc
      mainSum ≤
          ∑ k ∈ positiveExponents Kcut,
            (1 / rho DickmanBasic.U) * singleWeight p.1 k := by
        dsimp only [mainSum]
        exact Finset.sum_le_sum fun k hk => (hmainTerm k hk).2
      _ = (1 / rho DickmanBasic.U) *
          ∑ k ∈ positiveExponents Kcut, singleWeight p.1 k := by
        rw [Finset.mul_sum]
      _ ≤ (1 / rho DickmanBasic.U) * (6 / (p.1 : Real)) := by
        exact mul_le_mul_of_nonneg_left hweight
          (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
      _ = Amain / (p.1 : Real) := by
        dsimp only [Amain]
        field_simp [hpR.ne', DickmanBasic.rho_U_pos.ne']
  have hcellMean :
      ∀ cell : Cell (PaperHeadSimplex.Tag Phead),
        (B.guardedCellProbability cell).expect
            (fun m ↦ valuation p.1 (m : Nat)) ≤
          Aval / (p.1 : Real) := by
    intro cell
    let mean :=
      (B.guardedCellProbability cell).expect
        (fun m ↦ valuation p.1 (m : Nat))
    have hprofile :
        |mean - mainSum| ≤ Ccell / ((p.1 : Real) * B.L) := by
      simpa only [mean, Kcut, mainSum] using hcellRaw cell
    have herror :
        Ccell / ((p.1 : Real) * B.L) ≤
          Ccell / (p.1 : Real) := by
      apply div_le_div_of_nonneg_left hCcell.le hpR
      calc
        (p.1 : Real) = (p.1 : Real) * 1 := by ring
        _ ≤ (p.1 : Real) * B.L :=
          mul_le_mul_of_nonneg_left hLone hpR.le
    have hmeanLe : mean ≤ mainSum +
        Ccell / ((p.1 : Real) * B.L) := by
      have hself : mean - mainSum ≤ |mean - mainSum| :=
        le_abs_self _
      linarith
    calc
      mean ≤ mainSum + Ccell / ((p.1 : Real) * B.L) := hmeanLe
      _ ≤ Amain / (p.1 : Real) + Ccell / (p.1 : Real) :=
        add_le_add hmainUpper herror
      _ = Aval / (p.1 : Real) := by
        dsimp only [Aval]
        ring
  have hround :
      |q0 - qTilde| ≤ (1 : Real) / 2 := by
    rw [hq0]
    unfold bankPaperCanonicalTopFrozenRoundedActiveMass
    exact bankPaperCanonicalSmoothInitialActiveMass_abs_sub_actual_le _ _
  have hmassChange :
      |qn - qTilde| ≤
        Cmass * (secondOrderScale B.sampleData.n / B.L) := by
    have htriangle :
        |qn - qTilde| ≤ |q0 - qTilde| + |(d : Real)| := by
      calc
        |qn - qTilde| = |(q0 - qTilde) - (d : Real)| := by
          congr 1
          dsimp only [qn]
          unfold bankPaperCanonicalSectionNinePostHeightActiveMass
          ring
        _ ≤ |q0 - qTilde| + |(d : Real)| :=
          abs_sub _ _
    calc
      |qn - qTilde| ≤ |q0 - qTilde| + |(d : Real)| :=
        htriangle
      _ ≤ (1 : Real) / 2 +
          Cd * (secondOrderScale B.sampleData.n / B.L) :=
        add_le_add hround hd
      _ ≤ Cmass * (secondOrderScale B.sampleData.n / B.L) := by
        dsimp only [Cmass]
        nlinarith
  have hmassMoment :=
    abs_bankPaperCanonicalScaledActiveValuationMoment_sub_of_massChange
      B Tpost qn qTilde Aval Cmass p.1 hp hcellMean hmassChange
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1 := by
    intro a ha
    obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp ha
    exact hvalues m
  have hexact :=
    bankPaperCanonicalSectionNinePostHeightPlacementValuationMoment_eq
      (K := K0 + 1) B R certificate Tsource I hlo hhi H
        deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde hactiveSmooth hactiveBroad p.1
  rw [hexact]
  have htriangle :
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
          (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1)| ≤
        |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
            bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1| := by
    have htri1 := abs_add_le
      (bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
        bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1)
      (bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              qTilde p.1))
    have htri2 :
        |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
              bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  qTilde p.1)| ≤
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1| := by
      have h := abs_add_le
        (bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaAct p.1)
        (bankPaperCanonicalGuardedSmoothBaseValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
          (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                qTilde p.1))
      calc
        _ =
            |(bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
                bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1) +
              (bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
                (bankPaperCanonicalScaledActiveValuationMoment
                    Tsource qTilde p.1 +
                  bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                    (K := K0 + 1) B R certificate deltaStar betaProt
                      (bankPaperCanonicalPostHfitBalancedAlpha
                        B c K0 betaProt betaAct)
                      qTilde p.1))| := by
              congr 1
              ring
        _ ≤
            |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
            |bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
              (bankPaperCanonicalScaledActiveValuationMoment
                  Tsource qTilde p.1 +
                bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    qTilde p.1)| := h
        _ = _ := by
          congr 1
          rw [show
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1 -
                (bankPaperCanonicalScaledActiveValuationMoment
                    Tsource qTilde p.1 +
                  bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                    (K := K0 + 1) B R certificate deltaStar betaProt
                      (bankPaperCanonicalPostHfitBalancedAlpha
                        B c K0 betaProt betaAct)
                      qTilde p.1) =
              -(bankPaperCanonicalScaledActiveValuationMoment
                    Tsource qTilde p.1 -
                  bankPaperCanonicalGuardedSmoothBaseValuationMoment
                    (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
                bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaProt
                    (bankPaperCanonicalPostHfitBalancedAlpha
                      B c K0 betaProt betaAct)
                    qTilde p.1) by ring,
            abs_neg]
    calc
      _ ≤
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
            bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
            (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
              bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  qTilde p.1)| := by
            simpa only [sub_add_sub_cancel] using htri1
      _ ≤
          |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
            bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
          (|bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
              bankPaperCanonicalGuardedSmoothBaseValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
            |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
                bankPaperCanonicalGuardedSmoothBaseValuationMoment
                  (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
              bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
                (K := K0 + 1) B R certificate deltaStar betaProt
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  qTilde p.1|) := by
            exact add_le_add (le_refl _) htri2
      _ = _ := by ring
  calc
    |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
        (bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              qTilde p.1)| ≤
      |bankPaperCanonicalScaledActiveValuationMoment Tpost qn p.1 -
          bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1| +
        |bankPaperCanonicalScaledActiveValuationMoment Tpost qTilde p.1 -
          bankPaperCanonicalGuardedSmoothBaseValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaAct p.1| +
        |bankPaperCanonicalScaledActiveValuationMoment Tsource qTilde p.1 -
            bankPaperCanonicalGuardedSmoothBaseValuationMoment
              (K := K0 + 1) B R certificate deltaStar betaAct p.1 +
          bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              qTilde p.1| := htriangle
    _ ≤ (Cmass * Aval) * scale +
        (|betaAct| * Csharp) * scale +
        Csource * scale :=
      add_le_add (add_le_add hmassMoment hprincipal) hsourceBound
    _ = (Csource + |betaAct| * Csharp + Cmass * Aval) * scale := by
      ring
    _ ≤ Cplacement * scale := by
      exact mul_le_mul_of_nonneg_right
        (by dsimp only [Cplacement]; linarith) hscale0
    _ = Cplacement *
        (secondOrderScale B.sampleData.n / ((p.1 : Real) * B.L)) := by
      rfl

end BankPaperRealization

end

end Erdos390.WholePaper
