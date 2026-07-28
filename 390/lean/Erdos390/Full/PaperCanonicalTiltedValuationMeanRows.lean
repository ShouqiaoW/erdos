import Erdos390.Full.PaperRawTiltedValuationMeanRows
import Erdos390.Full.PaperCanonicalTiltedPrefixRows
import Erdos390.Full.PaperBridgePhysicalValuationRow

/-!
# Canonical full-valuation component means

This file transports the raw full-valuation comparison through the literal
guard deletion.  It also records a uniform reciprocal first-moment bound for
the resulting medium laws.  Both conclusions are uniform on an arbitrary
fixed prime-coefficient box selected after `W`; no inequality comparing that
box with `log W` is assumed.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperCanonicalTiltedValuationMeanRows

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability ValuationScoreDomination ValuationTiltCell
open PaperGuardCensus GuardedUniformCell GuardDeletionSquarefreeProfiles
open GuardSquarefreeErrorRate PaperPrimePowerTailRate
open PaperRawTiltedValuationMeanRows PaperCanonicalTiltedPrefixRows

noncomputable section

set_option maxHeartbeats 2400000

namespace PaperBridgeFit.BridgeData

open PaperBridgeFit

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- Canonical medium-cell valuation means have a uniform reciprocal first
moment and agree pairwise at an `o(1 / log L)/p` rate.  The first-moment
constant is fixed before `n` and is uniform in the later arithmetic bridge
data and coefficient vector. -/
theorem exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted
    [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ p ∈ (P h).primes, p ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ Aval : ℝ, 0 ≤ Aval ∧
      ∃ epsilon : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon n) ∧
        Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ,
          ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
            (B : BridgeData Head Band) (xi : B.ParamSpace),
            N₀ ≤ B.sampleData.n → B.sampleData.W = W →
            (∀ p : BandPrime B.sampleData.n B.sampleData.W,
              |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
            (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n) →
            (hremaining : ∀ c : Cell Head,
              (rawCell P I B.sampleData.n c \
                (G B.sampleData.n).guards).Nonempty) →
            B.sampleData = canonicalSampleData
              (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
            ∀ p : BandPrime B.sampleData.n B.sampleData.W,
              (∀ c : Cell Head,
                (B.cellMediumLaw xi c).expect
                    (fun m ↦ valuation p.1 (m : ℕ)) ≤
                  Aval / (p.1 : ℝ)) ∧
              (∀ c c' : Cell Head,
                |(B.cellMediumLaw xi c).expect
                      (fun m ↦ valuation p.1 (m : ℕ)) -
                  (B.cellMediumLaw xi c').expect
                      (fun m ↦ valuation p.1 (m : ℕ))| ≤
                    epsilon B.sampleData.n / (p.1 : ℝ)) := by
  let H : Cell Head → Pattern := fun c ↦ P c.1
  let Alower : Cell Head → ℝ := fun c ↦ I.lower c.2
  let Cupper : Cell Head → ℝ := fun c ↦ I.upper c.2
  let Cmax : ℝ := ∑ c : Cell Head, Cupper c
  have hCupper0 (c : Cell Head) : 0 ≤ Cupper c := by
    dsimp only [Cupper]
    exact ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)).le
  have hCupperLe (c : Cell Head) : Cupper c ≤ Cmax := by
    dsimp only [Cmax]
    exact Finset.single_le_sum
      (fun d hd ↦ hCupper0 d) (Finset.mem_univ c)
  obtain ⟨epsilonRaw, hepsilonRaw0, hepsilonRawRate, Nraw, hraw⟩ :=
    exists_uniform_fixedFinite_rawCell_tilted_valuation_mean_agreement_rate
      H Alower Cupper Cmax
      (fun c ↦ I.lower_pos c.2)
      (fun c ↦ I.lower_lt_upper c.2)
      (fun c ↦ (I.lower_pos c.2).trans (I.lower_lt_upper c.2))
      hCupperLe W hW (fun c ↦ hHeadLe c.1) Acoef hAcoef
  let Kscore : ℝ := (2 * Acoef) / Real.log (W : ℝ)
  let rhoCell : Cell Head → ℝ := fun c ↦
    PaperScaleMarkedCell.paperCellDensity (P c.1)
      (I.lower c.2) (I.upper c.2) / (4 * I.upper c.2)
  let Gcell : Cell Head → ℝ := fun c ↦
    2 * (Real.exp (2 * Kscore) / rhoCell c)
  let Aval : ℝ := ∑ c : Cell Head, Gcell c
  have hrho0 (c : Cell Head) : 0 < rhoCell c := by
    dsimp only [rhoCell]
    exact div_pos
      (PaperScaleMarkedCell.paperCellDensity_pos
        (P c.1) (I.lower_lt_upper c.2))
      (mul_pos (by norm_num)
        ((I.lower_pos c.2).trans (I.lower_lt_upper c.2)))
  have hGcell0 (c : Cell Head) : 0 ≤ Gcell c := by
    dsimp only [Gcell]
    exact mul_nonneg (by norm_num)
      (div_nonneg (Real.exp_pos _).le (hrho0 c).le)
  have hAval0 : 0 ≤ Aval := by
    dsimp only [Aval]
    exact Finset.sum_nonneg fun c hc ↦ hGcell0 c
  have hGcellLe (c : Cell Head) : Gcell c ≤ Aval := by
    dsimp only [Aval]
    exact Finset.single_le_sum
      (fun d hd ↦ hGcell0 d) (Finset.mem_univ c)
  let epsilonGuard : ℕ → ℝ := fun n ↦
    4 * canonicalGuardSquarefreeError P I G Kscore n
  let epsilon : ℕ → ℝ := fun n ↦
    epsilonRaw n + epsilonGuard n
  have hepsilonGuard0 : ∀ n, 0 ≤ epsilonGuard n := by
    intro n
    dsimp only [epsilonGuard]
    exact mul_nonneg (by norm_num)
      (canonicalGuardSquarefreeError_nonneg P I G Kscore n)
  have hepsilon0 : ∀ n, 0 ≤ epsilon n := by
    intro n
    exact add_nonneg (hepsilonRaw0 n) (hepsilonGuard0 n)
  have hepsilonGuardRate : Tendsto (fun n : ℕ ↦
      epsilonGuard n * Real.log (L n)) atTop (nhds 0) := by
    have hfour : Tendsto (fun _n : ℕ ↦ (4 : ℝ)) atTop (nhds 4) :=
      tendsto_const_nhds
    have hmul := hfour.mul
      (tendsto_canonicalGuardSquarefreeError_mul_logL_zero P I G Kscore)
    simpa only [epsilonGuard, mul_zero, mul_assoc] using hmul
  have hepsilonRate : Tendsto (fun n : ℕ ↦
      epsilon n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := hepsilonRawRate.add hepsilonGuardRate
    simpa only [epsilon, add_mul, zero_add] using hsum
  have hsmallEvent :=
    eventually_exp_two_mul_guardRatio_rawCell_le_half
      P I Cprom Cbank G Kscore
  have henvEvent :=
    eventually_valuationEnvelope_bounds (Head := Head) I W hW
  have hrowEnvEvent :=
    eventually_bandPrime_mul_valuationEnvelope_le_yNat_sq
      (Head := Head) I W hW
  have hdensityEvent :=
    eventually_guarded_rawCell_endpoint_density P I Cprom Cbank G
  have hAll : ∀ᶠ n : ℕ in atTop,
      (∀ c : Cell Head,
        Real.exp (2 * Kscore) * ((G n).guards.card : ℝ) /
          ((rawCell P I n c).card : ℝ) ≤ (1 : ℝ) / 2) ∧
      (∀ c : Cell Head, 0 ≤ valuationEnvelope I n W c ∧
        valuationEnvelope I n W c ≤
          (2 / Real.log (W : ℝ)) * L n) ∧
      (∀ (c : Cell Head) (p : BandPrime n W),
        (p.1 : ℝ) * valuationEnvelope I n W c ≤
          (yNat n : ℝ) ^ 2) ∧
      (∀ c : Cell Head,
        0 < rhoCell c ∧
          rhoCell c * (physicalBound (I.upper c.2) n : ℝ) ≤
            ((rawCell P I n c \ (G n).guards).card : ℝ)) ∧
      1 < n := by
    filter_upwards [hsmallEvent, henvEvent, hrowEnvEvent, hdensityEvent,
      Filter.eventually_gt_atTop 1] with n hsmallN henvN hrowEnvN
        hdensityN hn
    exact ⟨hsmallN, henvN, hrowEnvN,
      (by simpa only [rhoCell] using hdensityN), hn⟩
  obtain ⟨Nevent, hNevent⟩ := Filter.eventually_atTop.mp hAll
  refine ⟨Aval, hAval0, epsilon, hepsilon0, hepsilonRate,
    max Nraw Nevent, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW heta hsep hremaining
    hcanonical
  subst W
  have hNraw : Nraw ≤ B.sampleData.n := by omega
  have hNeventBound : Nevent ≤ B.sampleData.n := by omega
  obtain ⟨hsmallN, henvN, hrowEnvN, hdensityN, hn⟩ :=
    hNevent B.sampleData.n hNeventBound
  have hetaNat : ∀ q ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.effectiveNatCoefficient xi q| ≤ Acoef := by
    intro q hq
    rw [B.effectiveNatCoefficient_of_mem xi hq]
    exact heta ⟨q, hq⟩
  have hpW : 1 < B.sampleData.W := hW
  have hL : 0 < B.L := B.L_pos
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hpW)
  have hscore (c : Cell Head) : ∀ m : rawCell P I B.sampleData.n c,
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore := by
    intro m
    have hmpos : 0 < (m : ℕ) :=
      pos_of_mem_smoothInterval (mem_structuredCell.mp m.property).1
    have hmM : (m : ℕ) ≤
        physicalBound (I.upper c.2) B.sampleData.n :=
      (mem_smoothInterval.mp (mem_structuredCell.mp m.property).1).2.1
    have hprimeW : ∀ q ∈ primeBand B.sampleData.n B.sampleData.W,
        B.sampleData.W ≤ q := by
      intro q hq
      exact (cutoff_lt_of_mem_primeBand hq).le
    have hscoreRaw := abs_valuationScore_le_log_ratio
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) hmpos hmM hpW hprimeW
      hAcoef hL hetaNat
    have henvUpper : valuationEnvelope I B.sampleData.n
        B.sampleData.W c ≤
          (2 / Real.log (B.sampleData.W : ℝ)) * B.L := by
      simpa only [BridgeData.L, Scale.L] using (henvN c).2
    have hcoef : 0 ≤ Acoef / B.L := div_nonneg hAcoef hL.le
    calc
      |valuationScore (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤
        (Acoef / B.L) * valuationEnvelope I B.sampleData.n
          B.sampleData.W c := by
        simpa only [valuationEnvelope] using hscoreRaw
      _ ≤ (Acoef / B.L) *
          ((2 / Real.log (B.sampleData.W : ℝ)) * B.L) :=
        mul_le_mul_of_nonneg_left henvUpper hcoef
      _ = Kscore := by
        dsimp only [Kscore]
        field_simp [hL.ne', hlogW.ne']
  have hrawPair (p : BandPrime B.sampleData.n B.sampleData.W)
      (c c' : Cell Head) :
      |((uniformOnFinset (rawCell P I B.sampleData.n c)
            ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
            (fun m ↦ valuation p.1 (m : ℕ)) -
        ((uniformOnFinset (rawCell P I B.sampleData.n c')
            ((hremaining c').mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
            (fun m ↦ valuation p.1 (m : ℕ))| ≤
          epsilonRaw B.sampleData.n / (p.1 : ℝ) := by
    have hrawN := hraw (n := B.sampleData.n) (p := p.1)
      (B.effectiveNatCoefficient xi) hNraw p.2 hetaNat
      (fun d ↦ (hremaining d).mono Finset.sdiff_subset) c c'
    simpa only [H, Alower, Cupper, rawCell, BridgeData.L, Scale.L]
      using hrawN
  have hdelete (p : BandPrime B.sampleData.n B.sampleData.W)
      (c : Cell Head) :
      |(B.cellMediumLaw xi c).expect
            (fun m ↦ valuation p.1 (m : ℕ)) -
        ((uniformOnFinset (rawCell P I B.sampleData.n c)
            ((hremaining c).mono Finset.sdiff_subset)).exponentialTilt
          (fun m ↦ valuationScore
            (primeBand B.sampleData.n B.sampleData.W)
            (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
            (fun m ↦ valuation p.1 (m : ℕ))| ≤
          4 * valuationEnvelope I B.sampleData.n B.sampleData.W c *
            (Real.exp (2 * Kscore) *
              ((G B.sampleData.n).guards.card : ℝ) /
                ((rawCell P I B.sampleData.n c).card : ℝ)) := by
    let S := rawCell P I B.sampleData.n c
    let hS : S.Nonempty := (hremaining c).mono Finset.sdiff_subset
    let score : S → ℝ := fun m ↦ valuationScore
      (primeBand B.sampleData.n B.sampleData.W)
      (B.effectiveNatCoefficient xi) B.L (m : ℕ)
    let KA := valuationEnvelope I B.sampleData.n B.sampleData.W c
    have hKA : 0 ≤ KA := by
      exact (henvN c).1
    have hvaluation : ∀ m : S, |(valuation p.1 (m : ℕ) : ℝ)| ≤ KA := by
      intro m
      rw [abs_of_nonneg (valuation_nonneg p.1 (m : ℕ))]
      exact (rawCell_valuation_le_total P I p c m).trans
        (by simpa only [KA] using
          rawCell_totalBandValuation_le P I hpW c m)
    obtain ⟨hsmall, hdiff⟩ :=
      GuardedUniformCell.exists_deleteGuards_expect_bound
        S (G B.sampleData.n).guards hS score Kscore
        (by simpa only [S, score] using hscore c)
        (fun m ↦ (valuation p.1 (m : ℕ) : ℝ)) (KF := KA) hKA hvaluation
        (by simpa only [S] using hsmallN c)
    have hreindex := B.raw_deleteGuards_expect_eq_cellMediumLaw
      P I (G B.sampleData.n) hsep hremaining hcanonical xi c hsmall
        (fun m ↦ (valuation p.1 m : ℝ))
    rw [hreindex] at hdiff
    simpa only [S, hS, score, KA, abs_sub_comm] using hdiff
  intro p
  have hp := prime_of_mem_primeBand p.2
  have hpR : (0 : ℝ) < p.1 := by exact_mod_cast hp.pos
  have hmean (c : Cell Head) :
      (B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p.1 (m : ℕ)) ≤ Aval / (p.1 : ℝ) := by
    let rho := rhoCell c
    have hrho : 0 < rho := by simpa only [rho] using (hdensityN c).1
    have hhi : B.sampleData.hi c.2 =
        physicalBound (I.upper c.2) B.sampleData.n := by
      rw [hcanonical]
      rfl
    have hcell : B.sampleData.cellFinset c =
        rawCell P I B.sampleData.n c \ (G B.sampleData.n).guards := by
      rw [hcanonical]
      rfl
    have hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
        ((B.sampleData.cellFinset c).card : ℝ) := by
      rw [hhi, hcell]
      simpa only [rho] using (hdensityN c).2
    have hrawMean := B.cellMediumLaw_expect_valuation_le
      xi c hp hAcoef hpW hrho hcard heta
    let exponent : ℝ := (Acoef / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ))
    have hexponent : exponent ≤ Kscore := by
      have henvUpper : valuationEnvelope I B.sampleData.n
          B.sampleData.W c ≤
            (2 / Real.log (B.sampleData.W : ℝ)) * B.L := by
        simpa only [BridgeData.L, Scale.L] using (henvN c).2
      have hcoef : 0 ≤ Acoef / B.L := div_nonneg hAcoef B.L_pos.le
      calc
        exponent = (Acoef / B.L) *
            valuationEnvelope I B.sampleData.n B.sampleData.W c := by
          dsimp only [exponent, valuationEnvelope]
          rw [hhi]
        _ ≤ (Acoef / B.L) *
            ((2 / Real.log (B.sampleData.W : ℝ)) * B.L) :=
          mul_le_mul_of_nonneg_left henvUpper hcoef
        _ = Kscore := by
          dsimp only [Kscore]
          field_simp [B.L_pos.ne', hlogW.ne']
    have hlocal : 2 * (Real.exp (2 * exponent) / rho) ≤ Gcell c := by
      dsimp only [Gcell]
      exact mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left hexponent (by norm_num))) hrho.le)
        (by norm_num)
    have hcoefAval : 2 * (Real.exp (2 * exponent) / rho) ≤ Aval :=
      hlocal.trans (hGcellLe c)
    dsimp only at hrawMean
    calc
      (B.cellMediumLaw xi c).expect
          (fun m ↦ valuation p.1 (m : ℕ)) ≤
          2 * (Real.exp (2 * exponent) / rho) *
            (1 / (p.1 : ℝ)) := by
        simpa only [exponent, rho] using hrawMean
      _ ≤ Aval * (1 / (p.1 : ℝ)) :=
        mul_le_mul_of_nonneg_right hcoefAval (one_div_nonneg.mpr hpR.le)
      _ = Aval / (p.1 : ℝ) := by ring
  refine ⟨hmean, ?_⟩
  intro c c'
  let delta : Cell Head → ℝ := fun d ↦
    Real.exp (2 * Kscore) * ((G B.sampleData.n).guards.card : ℝ) /
      ((rawCell P I B.sampleData.n d).card : ℝ)
  have hdelta0 (d : Cell Head) : 0 ≤ delta d := by
    dsimp only [delta]
    have hguardCard :
        (0 : ℝ) ≤ ((G B.sampleData.n).guards.card : ℝ) := by
      exact_mod_cast Nat.zero_le (G B.sampleData.n).guards.card
    have hrawCard :
        (0 : ℝ) ≤ ((rawCell P I B.sampleData.n d).card : ℝ) := by
      exact_mod_cast Nat.zero_le (rawCell P I B.sampleData.n d).card
    exact div_nonneg
      (mul_nonneg (Real.exp_pos _).le hguardCard) hrawCard
  have hguardRow (d : Cell Head) :
      4 * valuationEnvelope I B.sampleData.n B.sampleData.W d * delta d ≤
        (2 * canonicalGuardSquarefreeError P I G Kscore B.sampleData.n) /
          (p.1 : ℝ) := by
    have hrowEnv : (p.1 : ℝ) *
        valuationEnvelope I B.sampleData.n B.sampleData.W d ≤
          (yNat B.sampleData.n : ℝ) ^ 2 := hrowEnvN d p
    have hcellToSum : guardSquarefreeError
        (rawCell P I B.sampleData.n d) (G B.sampleData.n).guards
          Kscore B.sampleData.n ≤
        canonicalGuardSquarefreeError P I G Kscore B.sampleData.n := by
      unfold canonicalGuardSquarefreeError
      exact Finset.single_le_sum
        (fun e he ↦ guardSquarefreeError_nonneg
          (rawCell P I B.sampleData.n e) (G B.sampleData.n).guards
            Kscore B.sampleData.n)
        (Finset.mem_univ d)
    apply (le_div_iff₀ hpR).2
    calc
      4 * valuationEnvelope I B.sampleData.n B.sampleData.W d * delta d *
          (p.1 : ℝ) =
        4 * ((p.1 : ℝ) *
          valuationEnvelope I B.sampleData.n B.sampleData.W d) * delta d := by
            ring
      _ ≤ 4 * (yNat B.sampleData.n : ℝ) ^ 2 * delta d := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hrowEnv (by norm_num)) (hdelta0 d)
      _ = 2 * guardSquarefreeError
          (rawCell P I B.sampleData.n d) (G B.sampleData.n).guards
            Kscore B.sampleData.n := by
        unfold guardSquarefreeError
        dsimp only [delta]
        ring
      _ ≤ 2 * canonicalGuardSquarefreeError P I G Kscore
          B.sampleData.n := mul_le_mul_of_nonneg_left hcellToSum (by norm_num)
  let rawMean : Cell Head → ℝ := fun d ↦
    ((uniformOnFinset (rawCell P I B.sampleData.n d)
        ((hremaining d).mono Finset.sdiff_subset)).exponentialTilt
      (fun m ↦ valuationScore
        (primeBand B.sampleData.n B.sampleData.W)
        (B.effectiveNatCoefficient xi) B.L (m : ℕ))).expect
        (fun m ↦ valuation p.1 (m : ℕ))
  let mediumMean : Cell Head → ℝ := fun d ↦
    (B.cellMediumLaw xi d).expect (fun m ↦ valuation p.1 (m : ℕ))
  have hc : |mediumMean c - rawMean c| ≤
      (2 * canonicalGuardSquarefreeError P I G Kscore B.sampleData.n) /
        (p.1 : ℝ) := by
    have hbase : |mediumMean c - rawMean c| ≤
        4 * valuationEnvelope I B.sampleData.n B.sampleData.W c * delta c := by
      simpa only [mediumMean, rawMean, delta] using hdelete p c
    exact hbase.trans (hguardRow c)
  have hc' : |rawMean c' - mediumMean c'| ≤
      (2 * canonicalGuardSquarefreeError P I G Kscore B.sampleData.n) /
        (p.1 : ℝ) := by
    have hbase : |mediumMean c' - rawMean c'| ≤
        4 * valuationEnvelope I B.sampleData.n B.sampleData.W c' * delta c' := by
      simpa only [mediumMean, rawMean, delta] using hdelete p c'
    rw [abs_sub_comm]
    exact hbase.trans (hguardRow c')
  have hrawPair' : |rawMean c - rawMean c'| ≤
      epsilonRaw B.sampleData.n / (p.1 : ℝ) := by
    simpa only [rawMean] using hrawPair p c c'
  change |mediumMean c - mediumMean c'| ≤ _
  calc
    |mediumMean c - mediumMean c'| =
        |(mediumMean c - rawMean c) + (rawMean c - rawMean c') +
          (rawMean c' - mediumMean c')| := by
      congr 1
      ring
    _ ≤ |mediumMean c - rawMean c| + |rawMean c - rawMean c'| +
        |rawMean c' - mediumMean c'| := by
      exact (abs_add_le _ _).trans
        (add_le_add (abs_add_le _ _) (le_refl _))
    _ ≤ (2 * canonicalGuardSquarefreeError P I G Kscore
          B.sampleData.n) / (p.1 : ℝ) +
        epsilonRaw B.sampleData.n / (p.1 : ℝ) +
        (2 * canonicalGuardSquarefreeError P I G Kscore
          B.sampleData.n) / (p.1 : ℝ) :=
      add_le_add (add_le_add hc hrawPair') hc'
    _ = epsilon B.sampleData.n / (p.1 : ℝ) := by
      dsimp only [epsilon, epsilonGuard]
      ring

end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalTiltedValuationMeanRows
