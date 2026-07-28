import Erdos390.Full.FixedFiniteMixtureLemma75
import Erdos390.Full.FullTiltPairHarmonicRate
import Erdos390.Full.FullTiltPrimePowerFallback
import Erdos390.Full.PaperPrimePowerAuxiliaryPrime
import Erdos390.Full.PaperPrimePowerRemainderRate

/-!
# Full uniform Lemma 7.5 for a fixed finite family of actual cells

This file specializes the marked-cell and full-tilt asymptotics on every
member of a fixed finite family, takes finite common majorants, and applies
the exact tagged-mixture theorem.  No desired covariance or tail estimate
is assumed by the final export.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureFullUniform

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate FullTiltPrimePowerFallback
open DickmanFourMarkProductKernel PaperScaleMarkedCell
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixtureLemma75 PaperValuationCutoff ValuationCutoff
open PrimeSums

noncomputable section

/-- Monotonicity of the integral physical endpoint. -/
theorem physicalBound_mono {C D : ℝ} (hCD : C ≤ D) (n : ℕ) :
    physicalBound C n ≤ physicalBound D n := by
  unfold physicalBound
  apply Nat.floor_mono
  exact mul_le_mul_of_nonneg_right hCD (by positivity)

@[simp] theorem coefficientScale_zero (W n : ℕ) :
    coefficientScale 0 W n = 0 := by
  unfold coefficientScale
  ring

theorem pairProbabilityScale_le_primePowerChamberRemainder
    {epsilon G k : ℝ} (hepsilon : 0 ≤ epsilon)
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    pairProbabilityScale epsilon G k ≤
      primePowerChamberRemainder epsilon G k := by
  unfold primePowerChamberRemainder aggregateChamberScale
  have hE := pairProbabilityScale_nonneg hepsilon hG hk
  have hcov := pairCovarianceScale_nonneg hE
  linarith

@[simp] theorem pairProbabilityScale_half_zero (x : ℝ) :
    pairProbabilityScale (x / 2) 0 0 = x := by
  unfold pairProbabilityScale localRestorationScale
  ring

variable {Cell : Type*} [Fintype Cell]

/-- The single prime-power constant used for every finite head family and
every later tilt box.  Its definition contains only the fixed Dickman
four-mark kernel witness. -/
noncomputable def boxIndependentPrimePowerConstant : ℝ :=
  paperPrimePowerConstant boxIndependentFourMarkKernelConstant

theorem boxIndependentPrimePowerConstant_pos :
    0 < boxIndependentPrimePowerConstant :=
  paperPrimePowerConstant_pos boxIndependentFourMarkKernelConstant_pos

/-- **Full fixed-finite-mixture export of paper Lemma 7.5.**

`H`, `A`, and `C` describe the fixed component cells.  `Cmax` is any fixed
common physical upper endpoint.  The constant is chosen before the tilt
box.  The one common remainder is nonnegative and tends to zero, and all
mixture weights are allowed (including the partition-function-reweighted
weights produced by a global exponential tilt). -/
theorem exists_boxIndependent_fixedFiniteMixture_primePower_transfer
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hCmax : 0 < Cmax)
    (hC_le : ∀ c, C c ≤ Cmax) :
    0 < boxIndependentPrimePowerConstant ∧
      ∀ W : ℕ, 1 < W →
        (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
      ∀ B : ℝ, 0 ≤ B →
      ∃ epsilon_BW : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon_BW n) ∧
        Tendsto epsilon_BW atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon_BW n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            ∀ weight : FiniteProbability Cell,
              let law := fun c ↦ widen
                (valuationTilt (H c) (physicalBound (A c) n)
                  (physicalBound (C c) n) (yNat n) (hS c)
                  (primeBand n W) eta (L n))
                (physicalBound_mono (hC_le c) n)
              PrimePowerTransferBounds (sigmaMixture weight law) n W
                boxIndependentPrimePowerConstant (epsilon_BW n) := by
  let C_K : ℝ := boxIndependentFourMarkKernelConstant
  let C_pow : ℝ := boxIndependentPrimePowerConstant
  have hCK : 0 < C_K := by
    simpa only [C_K] using boxIndependentFourMarkKernelConstant_pos
  have hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |DickmanBasic.F (x + z) - DickmanBasic.F x * DickmanBasic.F z| ≤
        C_K * x * z := by
    intro x z hx hz hxz
    simpa only [C_K, fourMarkProfile_eq_F] using
      boxIndependentFourMarkKernelConstant_bound x z hx hz hxz
  refine ⟨boxIndependentPrimePowerConstant_pos, ?_⟩
  intro W hW hHW B hB
  have hpairExists : ∀ c, ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto epsilon atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2)
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p →
        pairPower p q r s ≤ yNat n ^ 4 →
        Nat.Coprime p (H c).modulus → Nat.Coprime q (H c).modulus →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := structuredCell (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
              (fun m : S ↦ valuationScore (primeBand n W) eta (L n) m)).expect
              (fun m : S ↦ divInd (pairPower p q r s) m) -
            paperDivisibilityMain n (pairPower p q r s)| ≤
          fullPairChamberError (H c) (A c) (C c) B W n p q r s
            eta epsilon := by
    intro c
    exact exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate
      (H c) (hA c) (hAC c) (hC c) B W hB hW
  choose epsilon hepsilonData using hpairExists
  have hepsilon0 (c : Cell) : ∀ n, 0 ≤ epsilon c n :=
    (hepsilonData c).1
  have hepsilonT (c : Cell) : Tendsto (epsilon c) atTop (nhds 0) :=
    (hepsilonData c).2.1
  have hepsilonRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ epsilon c n * Real.log (L n)) atTop (nhds 0) :=
    (hepsilonData c).2.2.1
  have hepsilonRateSq (c : Cell) : Tendsto
      (fun n : ℕ ↦ epsilon c n * Real.log (L n) ^ 2) atTop (nhds 0) :=
    (hepsilonData c).2.2.2.1
  choose Npair hpairRaw using fun c ↦ (hepsilonData c).2.2.2.2
  have hfallbackExists : ∀ c, ∃ Gf : ℝ, 0 < Gf ∧ ∃ N₀ : ℕ,
      ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := structuredCell (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (valuationTilt (H c) (physicalBound (A c) n)
          (physicalBound (C c) n) (yNat n) hS
          (primeBand n W) eta (L n)).probability.expect
            (fun m ↦ divInd D (m : ℕ)) ≤ Gf / (D : ℝ) := by
    intro c
    exact exists_uniform_fullTilt_primePower_fallback
      (H c) (hA c) (hAC c) (hC c) B W hB hW
  choose Gcell hGcellData using hfallbackExists
  have hGcell (c : Cell) : 0 < Gcell c := (hGcellData c).1
  choose Nfallback hfallbackRaw using fun c ↦ (hGcellData c).2
  let cden : Cell → ℝ := fun c ↦ pairFallbackDensity (H c) (A c) (C c)
  let G₀ : Cell → ℝ := fun c ↦ paperPairFallbackCeiling B (cden c) W
  let cellRemainder : Cell → ℕ → ℝ := fun c n ↦
    primePowerChamberRemainder (epsilon c n) (G₀ c)
      (coefficientScale B W n)
  let profile : ℕ → ℝ := fun n ↦ ∑ c, |cellRemainder c n|
  let halfProfile : ℕ → ℝ := fun n ↦ profile n / 2
  let Gf : ℝ := ∑ c, Gcell c
  have hGf : 0 ≤ Gf := by
    dsimp only [Gf]
    exact Finset.sum_nonneg fun c hc ↦ (hGcell c).le
  have hcellRemainderT (c : Cell) :
      Tendsto (cellRemainder c) atTop (nhds 0) := by
    simpa only [cellRemainder] using
      (tendsto_primePowerChamberRemainder_zero_and_rate
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRate c)).1
  have hcellRemainderRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ cellRemainder c n * Real.log (L n))
        atTop (nhds 0) := by
    simpa only [cellRemainder] using
      (tendsto_primePowerChamberRemainder_zero_and_rate
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRate c)).2
  have hcellRemainderRateSq (c : Cell) : Tendsto
      (fun n : ℕ ↦ cellRemainder c n * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    simpa only [cellRemainder] using
      tendsto_primePowerChamberRemainder_mul_logL_sq_zero
        (epsilon c) (G₀ c) B W (hepsilonT c) (hepsilonRateSq c)
  have hprofileT : Tendsto profile atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ (hcellRemainderT c).abs)
    simpa only [profile, abs_zero, Finset.sum_const_zero] using hsum
  have hlogLNonneg : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.log (L n) := by
    have hLTop : Tendsto L atTop atTop := by
      simpa only [L] using
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hLge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ L n :=
      hLTop.eventually (eventually_ge_atTop 1)
    filter_upwards [hLge] with n hn
    exact Real.log_nonneg hn
  have hcellAbsRate (c : Cell) : Tendsto
      (fun n : ℕ ↦ |cellRemainder c n| * Real.log (L n))
        atTop (nhds 0) := by
    have habs := (hcellRemainderRate c).abs
    have habs0 : Tendsto
        (fun n : ℕ ↦ |cellRemainder c n * Real.log (L n)|)
          atTop (nhds 0) := by simpa only [abs_zero] using habs
    apply habs0.congr'
    filter_upwards [hlogLNonneg] with n hlog
    rw [abs_mul, abs_of_nonneg hlog]
  have hprofileRate : Tendsto
      (fun n : ℕ ↦ profile n * Real.log (L n)) atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hcellAbsRate c)
    have hsum0 : Tendsto
        (fun n : ℕ ↦ ∑ c, |cellRemainder c n| * Real.log (L n))
          atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [profile]
    rw [Finset.sum_mul]
  have hcellAbsRateSq (c : Cell) : Tendsto
      (fun n : ℕ ↦ |cellRemainder c n| * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    have habs := (hcellRemainderRateSq c).abs
    have habs0 : Tendsto
        (fun n : ℕ ↦ |cellRemainder c n * Real.log (L n) ^ 2|)
          atTop (nhds 0) := by simpa only [abs_zero] using habs
    apply habs0.congr'
    filter_upwards with n
    have hsq : |Real.log (L n) ^ 2| = Real.log (L n) ^ 2 :=
      abs_of_nonneg (sq_nonneg _)
    rw [abs_mul, hsq]
  have hprofileRateSq : Tendsto
      (fun n : ℕ ↦ profile n * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hcellAbsRateSq c)
    have hsum0 : Tendsto
        (fun n : ℕ ↦ ∑ c, |cellRemainder c n| * Real.log (L n) ^ 2)
          atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [profile]
    rw [Finset.sum_mul]
  have hhalf0 : ∀ n, 0 ≤ halfProfile n := by
    intro n
    dsimp only [halfProfile, profile]
    positivity
  have hhalfT : Tendsto halfProfile atTop (nhds 0) := by
    have htwo : Tendsto (fun _n : ℕ ↦ (2 : ℝ)) atTop (nhds 2) :=
      tendsto_const_nhds
    simpa only [halfProfile, zero_div] using hprofileT.div_const 2
  have hhalfRate : Tendsto
      (fun n : ℕ ↦ halfProfile n * Real.log (L n)) atTop (nhds 0) := by
    have h := hprofileRate.div_const 2
    have h0 : Tendsto
        (fun n : ℕ ↦ profile n * Real.log (L n) / 2)
          atTop (nhds 0) := by simpa only [zero_div] using h
    apply h0.congr'
    filter_upwards with n
    dsimp only [halfProfile]
    ring
  have hhalfRateSq : Tendsto
      (fun n : ℕ ↦ halfProfile n * Real.log (L n) ^ 2)
        atTop (nhds 0) := by
    have h := hprofileRateSq.div_const 2
    have h0 : Tendsto
        (fun n : ℕ ↦ profile n * Real.log (L n) ^ 2 / 2)
          atTop (nhds 0) := by simpa only [zero_div] using h
    apply h0.congr'
    filter_upwards with n
    dsimp only [halfProfile]
    ring
  let Eagg : ℕ → ℝ := fun n ↦
    primePowerChamberRemainder (halfProfile n) 0 0
  have hEaggT : Tendsto Eagg atTop (nhds 0) := by
    have hraw := (tendsto_primePowerChamberRemainder_zero_and_rate
      halfProfile 0 0 W hhalfT hhalfRate).1
    simpa only [Eagg, coefficientScale_zero] using hraw
  have hEaggRate : Tendsto
      (fun n : ℕ ↦ Eagg n * Real.log (L n)) atTop (nhds 0) := by
    have hraw := (tendsto_primePowerChamberRemainder_zero_and_rate
      halfProfile 0 0 W hhalfT hhalfRate).2
    simpa only [Eagg, coefficientScale_zero] using hraw
  let tail : ℕ → ℝ := tailRowMajorant Gf W
  have htailT : Tendsto tail atTop (nhds 0) := by
    simpa only [tail] using tendsto_tailRowMajorant_zero Gf W hGf hW
  have htailRate : Tendsto
      (fun n : ℕ ↦ tail n * Real.log (L n)) atTop (nhds 0) := by
    simpa only [tail] using
      tendsto_tailRowMajorant_mul_logL_zero Gf W hGf hW
  have hrowRemainderT := tendsto_primePowerRowRemainder_zero
    halfProfile 0 0 Gf W hhalfT hhalfRate hhalf0 (by norm_num)
      (by norm_num) hGf hW
  have hrowRemainderRate := tendsto_primePowerRowRemainder_mul_logL_zero
    halfProfile 0 0 Gf W hhalfT hhalfRate hhalfRateSq hhalf0
      (by norm_num) (by norm_num) hGf hW
  let rawRemainder : ℕ → ℝ := fun n ↦
    genericAggregationRemainder (Eagg n) (tail n) (tail n) (tail n)
      (tail n) n W
  have hrawRemainderT : Tendsto rawRemainder atTop (nhds 0) := by
    have hscaled : Tendsto (fun n : ℕ ↦ pairAggregationConstant * Eagg n)
        atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ pairAggregationConstant) atTop
          (nhds pairAggregationConstant) := tendsto_const_nhds
      simpa only [mul_zero] using hc.mul hEaggT
    have hthree : Tendsto (fun n : ℕ ↦ 3 * tail n) atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ (3 : ℝ)) atTop (nhds 3) :=
        tendsto_const_nhds
      simpa only [mul_zero] using hc.mul htailT
    have hsum := (hscaled.add hthree).add hrowRemainderT
    have hsum0 : Tendsto
        (fun n : ℕ ↦ pairAggregationConstant * Eagg n + 3 * tail n +
          primePowerRowRemainder halfProfile 0 0 Gf W n)
          atTop (nhds 0) := by simpa only [add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold rawRemainder genericAggregationRemainder
    unfold primePowerRowRemainder
    dsimp only [tail, Eagg]
    rw [coefficientScale_zero]
    ring
  have hrawRemainderRate : Tendsto
      (fun n : ℕ ↦ rawRemainder n * Real.log (L n))
        atTop (nhds 0) := by
    have hscaled : Tendsto
        (fun n : ℕ ↦
          pairAggregationConstant * (Eagg n * Real.log (L n)))
        atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ pairAggregationConstant) atTop
          (nhds pairAggregationConstant) := tendsto_const_nhds
      simpa only [mul_zero] using hc.mul hEaggRate
    have hthree : Tendsto
        (fun n : ℕ ↦ 3 * (tail n * Real.log (L n)))
        atTop (nhds 0) := by
      have hc : Tendsto (fun _n : ℕ ↦ (3 : ℝ)) atTop (nhds 3) :=
        tendsto_const_nhds
      simpa only [mul_zero] using hc.mul htailRate
    have hsum := (hscaled.add hthree).add hrowRemainderRate
    have hsum0 : Tendsto
        (fun n : ℕ ↦
          pairAggregationConstant * (Eagg n * Real.log (L n)) +
            3 * (tail n * Real.log (L n)) +
              primePowerRowRemainder halfProfile 0 0 Gf W n *
                Real.log (L n)) atTop (nhds 0) := by
      simpa only [add_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    unfold rawRemainder genericAggregationRemainder
    unfold primePowerRowRemainder
    dsimp only [tail, Eagg]
    rw [coefficientScale_zero]
    ring
  let epsilon_BW : ℕ → ℝ := fun n ↦ |rawRemainder n|
  have hepsilon_BW0 : ∀ n, 0 ≤ epsilon_BW n := fun n ↦ abs_nonneg _
  have hepsilon_BWT : Tendsto epsilon_BW atTop (nhds 0) := by
    simpa only [epsilon_BW, abs_zero] using hrawRemainderT.abs
  have hepsilon_BWRate : Tendsto
      (fun n : ℕ ↦ epsilon_BW n * Real.log (L n))
        atTop (nhds 0) := by
    have habs := hrawRemainderRate.abs
    have habs0 : Tendsto
        (fun n : ℕ ↦ |rawRemainder n * Real.log (L n)|)
          atTop (nhds 0) := by simpa only [abs_zero] using habs
    apply habs0.congr'
    filter_upwards [hlogLNonneg] with n hlog
    dsimp only [epsilon_BW]
    rw [abs_mul, abs_of_nonneg hlog]
  obtain ⟨q₀, q₁, aux, _, _, _, hq₀q₁, _, hauxEvent⟩ :=
    exists_eventually_auxiliaryPrime W
  have hcden (c : Cell) : 0 < cden c := by
    dsimp only [cden]
    exact pairFallbackDensity_pos_of_pos (H c) (hAC c) (hC c)
  have hG₀ (c : Cell) : 0 < G₀ c := by
    dsimp only [G₀]
    exact paperPairFallbackCeiling_pos B (cden c) W (hcden c)
  have hNpairEvent : ∀ᶠ n : ℕ in atTop, ∀ c, Npair c ≤ n := by
    rw [Filter.eventually_all]
    intro c
    exact eventually_ge_atTop (Npair c)
  have hNfallbackEvent : ∀ᶠ n : ℕ in atTop,
      ∀ c, Nfallback c ≤ n := by
    rw [Filter.eventually_all]
    intro c
    exact eventually_ge_atTop (Nfallback c)
  have hGEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      paperPairFallbackConstant B (C c) (cden c) W n ≤ G₀ c := by
    rw [Filter.eventually_all]
    intro c
    simpa only [G₀] using eventually_paperPairFallbackConstant_le
      B (C c) (cden c) W hB (hC c) (hcden c) hW
  have hcoefEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      ∀ p ∈ primeBand n W, ∀ eta₀ : ℝ, |eta₀| ≤ B → ∀ r : ℕ,
      coefficientTail p (valuationCutoff p (physicalBound (C c) n))
          r eta₀ (L n) ≤ coefficientScale B W n *
            (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
    rw [Filter.eventually_all]
    intro c
    simpa only [coefficientScale] using
      eventually_coefficientTail_le_of_pos B (C c) W hB (hC c) hW
  have htailJIEvent := eventually_sum_eJI_le Gf Cmax W hGf hCmax hW
  have htailIJEvent := eventually_sum_eIJ_le Gf Cmax W hGf hCmax hW
  have htailJJEvent := eventually_sum_eJJ_le Gf Cmax W hGf hCmax hW
  have htailDEvent := eventually_sum_weighted_eD_le
    Gf Cmax W hGf hCmax hW
  have htailRowEvent := eventually_tail_row_le Gf Cmax W hGf hCmax hW
  have hbandTEvent := eventually_bandTReciprocalSum_le W
  have hfinal : ∀ᶠ n : ℕ in atTop, ∀ eta : ℕ → ℝ,
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := fun c ↦ structuredCell (H c)
        (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
      (∀ c, (S c).Nonempty) ∧
        ∀ hS : ∀ c, (S c).Nonempty,
        ∀ weight : FiniteProbability Cell,
          let law := fun c ↦ widen
            (valuationTilt (H c) (physicalBound (A c) n)
              (physicalBound (C c) n) (yNat n) (hS c)
              (primeBand n W) eta (L n))
            (physicalBound_mono (hC_le c) n)
          PrimePowerTransferBounds (sigmaMixture weight law) n W
            C_pow (epsilon_BW n) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hNpairEvent,
      hNfallbackEvent, hGEvent, hcoefEvent, htailJIEvent,
      htailIJEvent, htailJJEvent, htailDEvent, htailRowEvent,
      hbandTEvent, hauxEvent]
      with n hn hNpairn hNfallbackn hGn hcoefn htailJIn htailIJn
        htailJJn htailDn htailRown hbandTn hauxn
    intro eta heta
    obtain ⟨hq₀Band, hq₁Band, hauxn⟩ := hauxn
    have hq₁Erase : q₁ ∈ (primeBand n W).erase q₀ :=
      Finset.mem_erase.mpr ⟨hq₀q₁.ne', hq₁Band⟩
    let S := fun c ↦ structuredCell (H c)
      (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
    have hSnonempty : ∀ c, (S c).Nonempty := by
      intro c
      have hq₀Head := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hq₀Band
      have hq₁Head := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hq₁Band
      have hyPos : 0 < yNat n :=
        (prime_of_mem_primeBand hq₀Band).pos.trans_le
          (le_yNat_of_mem_primeBand hq₀Band)
      have hzero : pairPower q₀ q₁ 0 0 ≤ yNat n ^ 4 := by
        simpa only [pairPower, pow_zero, mul_one] using
          (one_le_pow₀ (show 1 ≤ yNat n from hyPos))
      have hseed := hpairRaw c eta (hNpairn c) hq₀Band hq₁Erase
        hzero hq₀Head hq₁Head heta
      simpa only [S] using hseed.1
    refine ⟨hSnonempty, ?_⟩
    intro hS weight
    let baseLaw := fun c ↦
      valuationTilt (H c) (physicalBound (A c) n)
        (physicalBound (C c) n) (yNat n) (hS c)
        (primeBand n W) eta (L n)
    let law := fun c ↦ widen (baseLaw c)
      (physicalBound_mono (hC_le c) n)
    have hk : 0 ≤ coefficientScale B W n := by
      unfold coefficientScale
      exact mul_nonneg
        (div_nonneg (mul_nonneg (by norm_num) hB) (L_pos hn).le)
        (Real.exp_pos _).le
    have hprofileCell : ∀ c p, p ∈ primeBand n W →
        ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
        pairPower p q r s ≤ yNat n ^ 4 →
        |(law c).probability.expect
            (fun omega ↦ divInd (pairPower p q r s)
              ((law c).value omega)) -
          paperDivisibilityMain n (pairPower p q r s)| ≤
          profile n * pairWeight p q r s := by
      intro c p hpBand q hqErase r s hD4
      have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
      have hpHead := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hpBand
      have hqHead := coprime_modulus_of_mem_primeBand_of_headSupport
        (H c) (hHW c) hqBand
      have hraw := (hpairRaw c eta (hNpairn c) hpBand hqErase hD4
        hpHead hqHead heta).2 (hS c)
      have herr := fullPairChamberError_le_pairWeight
        (H c) eta (epsilon c) hn hpBand hqBand hD4
        (hepsilon0 c n)
        (show 0 ≤ pairFallbackDensity (H c) (A c) (C c) by
          exact (hcden c).le)
        (by simpa only [cden, G₀] using hGn c) (hG₀ c).le hk
        (fun z hz u ↦ hcoefn c z hz (eta z) (heta z hz) u)
      have hprobToCell :
          pairProbabilityScale (epsilon c n) (G₀ c)
              (coefficientScale B W n) ≤ cellRemainder c n := by
        exact pairProbabilityScale_le_primePowerChamberRemainder
          (hepsilon0 c n) (hG₀ c).le hk
      have hcellToProfile : cellRemainder c n ≤ profile n := by
        calc
          cellRemainder c n ≤ |cellRemainder c n| := le_abs_self _
          _ ≤ ∑ d, |cellRemainder d n| := by
            exact Finset.single_le_sum
              (fun d hd ↦ abs_nonneg (cellRemainder d n))
              (Finset.mem_univ c)
          _ = profile n := rfl
      have hscale := mul_le_mul_of_nonneg_right
        (hprobToCell.trans hcellToProfile) (pairWeight_nonneg p q r s)
      have hbound := hraw.trans (herr.trans hscale)
      simpa only [law, baseLaw, widen_probability, widen_value,
        valuationTilt_probability, valuationTilt_value] using hbound
    have hpairProfile : ∀ c p, p ∈ primeBand n W →
        ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
        pairPower p q r s ≤ yNat n ^ 4 →
        |(law c).probability.expect
            (fun omega ↦ divInd (pairPower p q r s)
              ((law c).value omega)) -
          paperDivisibilityMain n (pairPower p q r s)| ≤
          pairProbabilityScale (halfProfile n) 0 0 *
            pairWeight p q r s := by
      simpa only [halfProfile, pairProbabilityScale_half_zero] using
        hprofileCell
    have hsingleProfile : ∀ c p, p ∈ primeBand n W → ∀ r,
        p ^ r ≤ yNat n ^ 4 →
        |(law c).probability.expect
            (fun omega ↦ divInd (p ^ r) ((law c).value omega)) -
          paperDivisibilityMain n (p ^ r)| ≤
          pairProbabilityScale (halfProfile n) 0 0 * singleWeight p r := by
      intro c p hpBand r hD4
      let q := aux p
      have hqErase : q ∈ (primeBand n W).erase p := hauxn p hpBand
      have hpair := hpairProfile c p hpBand q hqErase r 0
        (by simpa only [pairPower, pow_zero, mul_one] using hD4)
      simpa only [pairPower, pow_zero, mul_one, pairWeight_eq_single_mul,
        singleWeight, Nat.cast_zero, zero_add, div_one, mul_one] using hpair
    have hfallback : ∀ c D, 0 < D →
        (law c).probability.expect
          (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ) := by
      intro c D hD
      have hraw := hfallbackRaw c eta (hNfallbackn c) heta (hS c) D hD
      have hcellLe : Gcell c ≤ Gf := by
        dsimp only [Gf]
        exact Finset.single_le_sum
          (fun d hd ↦ (hGcell d).le) (Finset.mem_univ c)
      have hdiv := div_le_div_of_nonneg_right hcellLe (by positivity :
        0 ≤ (D : ℝ))
      have hbound := hraw.trans hdiv
      simpa only [law, baseLaw, widen_probability, widen_value,
        valuationTilt_probability, valuationTilt_value] using hbound
    let T : ℝ := Gf + Gf ^ 2
    let K : ℝ := cutoffScale W * L n
    let Y : ℝ := yNat n
    have hT : 0 ≤ T := by
      dsimp only [T]
      nlinarith [sq_nonneg Gf]
    have hK : 0 ≤ K := by
      dsimp only [K]
      exact mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
    have hY : 0 < Y := by
      dsimp only [Y]
      exact_mod_cast (prime_of_mem_primeBand hq₀Band).pos.trans_le
        (le_yNat_of_mem_primeBand hq₀Band)
    have hband0 : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    have hTailLinear : T * (K / Y) ≤ tail n := by
      dsimp only [tail]
      unfold tailRowMajorant
      dsimp only [T, K, Y]
      have hKY : 0 ≤ K / Y := div_nonneg hK hY.le
      have hfirst : T * (K / Y) ≤
          T * ((K / Y) * (bandReciprocalSum n W + 1)) := by
        apply mul_le_mul_of_nonneg_left _ hT
        nlinarith [mul_nonneg hKY hband0]
      have hsecond : 0 ≤ T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by
        positivity
      have hthird : 0 ≤ 6 * Gf * (K ^ 2 / Y ^ 2) := by positivity
      linarith
    have hTailQuadratic : T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) ≤ tail n := by
      dsimp only [tail]
      unfold tailRowMajorant
      dsimp only [T, K, Y]
      have hfirst : 0 ≤
          T * ((K / Y) * (bandReciprocalSum n W + 1)) := by positivity
      have hthird : 0 ≤ 6 * Gf * (K ^ 2 / Y ^ 2) := by positivity
      linarith
    have hTailDiagonal : 2 * Gf * (K ^ 2 / Y ^ 2) ≤ tail n := by
      dsimp only [tail]
      unfold tailRowMajorant
      dsimp only [T, K, Y]
      have hfirst : 0 ≤
          T * ((K / Y) * (bandReciprocalSum n W + 1)) := by positivity
      have hsecond : 0 ≤ T * (K ^ 2 / Y ^ (2 / 3 : ℝ)) := by positivity
      have hthird : 2 * Gf * (K ^ 2 / Y ^ 2) ≤
          6 * Gf * (K ^ 2 / Y ^ 2) := by
        have hx : 0 ≤ Gf * (K ^ 2 / Y ^ 2) := by positivity
        nlinarith
      linarith
    have htailJI : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound Cmax n)),
          eJI Gf n p q r) ≤
          tail n * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by
      intro p hp q hq
      calc
        _ ≤ (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
            ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))) := by
          simpa only [actualExponentCutoff] using htailJIn p hp q hq
        _ = (T * (K / Y)) * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) := by dsimp only [T, K, Y]; ring
        _ ≤ _ := by gcongr
    have htailIJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
        (∑ s ∈ highExponents (valuationCutoff q (physicalBound Cmax n)),
          eIJ Gf n p q s) ≤
          tail n * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by
      intro p hp q hq
      calc
        _ ≤ (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
            ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))) := by
          simpa only [actualExponentCutoff] using htailIJn p hp q hq
        _ = (T * (K / Y)) * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 := by dsimp only [T, K, Y]; ring
        _ ≤ _ := by gcongr
    have htailJJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound Cmax n)),
          ∑ s ∈ highExponents (valuationCutoff q (physicalBound Cmax n)),
            eJJ Gf n p q r s) ≤
          tail n * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
      intro p hp q hq
      calc
        _ ≤ (Gf + Gf ^ 2) * (((cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
              (yNat n : ℝ) ^ (2 / 3 : ℝ))) := by
          simpa only [actualExponentCutoff] using htailJJn p hp q hq
        _ = (T * (K ^ 2 / Y ^ (2 / 3 : ℝ))) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
          dsimp only [T, K, Y]; ring
        _ ≤ _ := by gcongr
    have htailD : ∀ p ∈ primeBand n W,
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound Cmax n)),
          (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r)) ≤
          tail n * (1 / (p : ℝ)) ^ 2 := by
      intro p hp
      calc
        _ ≤ Gf * ((2 * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := by
          simpa only [actualExponentCutoff] using htailDn p hp
        _ = (2 * Gf * (K ^ 2 / Y ^ 2)) *
            (1 / (p : ℝ)) ^ 2 := by dsimp only [K, Y]; ring
        _ ≤ _ := by gcongr
    have htailRow : ∀ p ∈ primeBand n W,
        (p : ℝ) *
          ((∑ q ∈ (primeBand n W).erase p,
              (((∑ r ∈ highExponents
                    (valuationCutoff p (physicalBound Cmax n)),
                    eJI Gf n p q r)) +
                (∑ s ∈ highExponents
                    (valuationCutoff q (physicalBound Cmax n)),
                    eIJ Gf n p q s) +
                (∑ r ∈ highExponents
                    (valuationCutoff p (physicalBound Cmax n)),
                  ∑ s ∈ highExponents
                    (valuationCutoff q (physicalBound Cmax n)),
                    eJJ Gf n p q r s))) +
            3 * (∑ r ∈ highExponents
                (valuationCutoff p (physicalBound Cmax n)),
              (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r))) ≤ tail n := by
      intro p hp
      simpa only [actualExponentCutoff, tail] using htailRown p hp
    have htail0 : 0 ≤ tail n := by
      dsimp only [tail]
      exact tailRowMajorant_nonneg hGf hW hn
    have hmix := sigmaMixture_primePowerTransferBounds_of_common_profiles
      hkernel hCK.le (hhalf0 n) (by norm_num) (by norm_num) hGf
      htail0 htail0 htail0 htail0 weight law hn hW
      hpairProfile hsingleProfile hfallback htailJI htailIJ htailJJ
      htailD htailRow hbandTn
    have hmono := hmix.mono_epsilon (le_abs_self (rawRemainder n))
    simpa only [C_pow, rawRemainder, Eagg, tail, law, baseLaw,
      epsilon_BW] using hmono
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨epsilon_BW, hepsilon_BW0, hepsilon_BWT, hepsilon_BWRate, N₀, ?_⟩
  intro n eta hn heta
  exact hN₀ n hn eta heta

end

end Erdos390.Full.FixedFiniteMixtureFullUniform
