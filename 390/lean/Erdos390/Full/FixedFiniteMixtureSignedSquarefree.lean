import Erdos390.Full.FixedFiniteMixtureFullUniform
import Erdos390.Full.SquarefreeReferenceOperatorIdentification

/-!
# Signed squarefree profiles for a fixed finite family of cells

The prime-power conclusion of paper Lemma 7.5 is an absolute tail estimate.
The arithmetic inverse in Lemma 8.4 instead needs the signed one- and
two-divisor profiles before covariance is formed.  The proof of the former
already constructs a common finite-family profile with one harmonic loss to
spare.  This file exports that stronger intermediate conclusion explicitly,
without taking it as a hypothesis.
-/

open Filter Topology

namespace Erdos390.Full.FixedFiniteMixtureSignedSquarefree

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw ValuationScoreDomination
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPairHarmonicRate
open PaperTwoLocalRestorationBound LocalFugacityBounds
open PaperPrimePowerChamberError PaperPrimePowerFourDisplays
open PaperPrimePowerRemainderRate PaperScaleMarkedCell
open PaperValuationCutoff PaperPrimePowerAuxiliaryPrime
open FixedFiniteMixtureFullUniform

noncomputable section

variable {Cell : Type*} [Fintype Cell]

/-- A single signed marked-profile error works for every cell in a fixed
finite family, every pair of moving primes and every four-mark exponent
pair.  It tends to zero even after multiplication by `log (L n)`, which is
the precise margin required by the moving-low sharp row.

The coefficient box is selected only after `W`; all dependence on that box
is confined to `signedError` and the eventual threshold.

This positive-endpoint core only assumes strict positivity of `C`; the
paper-facing wrapper below retains its earlier normalization `1 ≤ C`. -/
theorem exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hC_le : ∀ c, C c ≤ Cmax) :
    ∀ W : ℕ, 1 < W →
      (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
    ∀ B : ℝ, 0 ≤ B →
      ∃ signedError : ℕ → ℝ,
        (∀ n, 0 ≤ signedError n) ∧
        Tendsto signedError atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ signedError n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            let law := fun c ↦ widen
              (valuationTilt (H c) (physicalBound (A c) n)
                (physicalBound (C c) n) (yNat n) (hS c)
                (primeBand n W) eta (L n))
              (physicalBound_mono (hC_le c) n)
            (∀ c p, p ∈ primeBand n W →
              ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
              pairPower p q r s ≤ yNat n ^ 4 →
              |(law c).probability.expect
                  (fun omega ↦ divInd (pairPower p q r s)
                    ((law c).value omega)) -
                paperDivisibilityMain n (pairPower p q r s)| ≤
                  signedError n * pairWeight p q r s) ∧
            (∀ c p, p ∈ primeBand n W →
              |(law c).probability.expect
                  (fun omega ↦ divInd p ((law c).value omega)) -
                paperDivisibilityMain n p| ≤
                  signedError n * singleWeight p 1) := by
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
  let cden : Cell → ℝ := fun c ↦ pairFallbackDensity (H c) (A c) (C c)
  let G₀ : Cell → ℝ := fun c ↦ paperPairFallbackCeiling B (cden c) W
  let cellRemainder : Cell → ℕ → ℝ := fun c n ↦
    primePowerChamberRemainder (epsilon c n) (G₀ c)
      (coefficientScale B W n)
  let signedError : ℕ → ℝ := fun n ↦ ∑ c, |cellRemainder c n|
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
  have hsignedErrorT : Tendsto signedError atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ (hcellRemainderT c).abs)
    simpa only [signedError, abs_zero, Finset.sum_const_zero] using hsum
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
  have hsignedErrorRate : Tendsto
      (fun n : ℕ ↦ signedError n * Real.log (L n))
        atTop (nhds 0) := by
    have hsum := tendsto_finset_sum (Finset.univ : Finset Cell)
      (fun c hc ↦ hcellAbsRate c)
    have hsum0 : Tendsto
        (fun n : ℕ ↦ ∑ c, |cellRemainder c n| * Real.log (L n))
          atTop (nhds 0) := by
      simpa only [Finset.sum_const_zero] using hsum
    apply hsum0.congr'
    filter_upwards with n
    dsimp only [signedError]
    rw [Finset.sum_mul]
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
  have hGEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      paperPairFallbackConstant B (C c) (cden c) W n ≤ G₀ c := by
    rw [Filter.eventually_all]
    intro c
    simpa only [G₀] using eventually_paperPairFallbackConstant_le
      B (C c) (cden c) W hB (hC c) (hcden c) hW
  have hcoefEvent : ∀ᶠ n : ℕ in atTop, ∀ c,
      ∀ p ∈ primeBand n W, ∀ eta₀ : ℝ, |eta₀| ≤ B → ∀ r : ℕ,
      coefficientTail p (ValuationCutoff.valuationCutoff p
          (physicalBound (C c) n)) r eta₀ (L n) ≤
        coefficientScale B W n * (((r : ℝ) + 1) / (p : ℝ) ^ r) := by
    rw [Filter.eventually_all]
    intro c
    simpa only [coefficientScale] using
      eventually_coefficientTail_le_of_pos B (C c) W hB (hC c) hW
  obtain ⟨q₀, q₁, aux, _, _, _, hq₀q₁, _, hauxEvent⟩ :=
    PaperPrimePowerAuxiliaryPrime.exists_eventually_auxiliaryPrime W
  have hfinal : ∀ᶠ n : ℕ in atTop, ∀ eta : ℕ → ℝ,
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := fun c ↦ structuredCell (H c)
        (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
      (∀ c, (S c).Nonempty) ∧
        ∀ hS : ∀ c, (S c).Nonempty,
        let law := fun c ↦ widen
          (valuationTilt (H c) (physicalBound (A c) n)
            (physicalBound (C c) n) (yNat n) (hS c)
            (primeBand n W) eta (L n))
          (physicalBound_mono (hC_le c) n)
        (∀ c p, p ∈ primeBand n W →
          ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
          pairPower p q r s ≤ yNat n ^ 4 →
          |(law c).probability.expect
              (fun omega ↦ divInd (pairPower p q r s)
                ((law c).value omega)) -
            paperDivisibilityMain n (pairPower p q r s)| ≤
              signedError n * pairWeight p q r s) ∧
        (∀ c p, p ∈ primeBand n W →
          |(law c).probability.expect
              (fun omega ↦ divInd p ((law c).value omega)) -
            paperDivisibilityMain n p| ≤
              signedError n * singleWeight p 1) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hNpairEvent,
      hGEvent, hcoefEvent, hauxEvent]
      with n hn hNpairn hGn hcoefn hauxn
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
    intro hS
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
          signedError n * pairWeight p q r s := by
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
              (coefficientScale B W n) ≤ cellRemainder c n :=
        pairProbabilityScale_le_primePowerChamberRemainder
          (hepsilon0 c n) (hG₀ c).le hk
      have hcellToProfile : cellRemainder c n ≤ signedError n := by
        calc
          cellRemainder c n ≤ |cellRemainder c n| := le_abs_self _
          _ ≤ ∑ d, |cellRemainder d n| := by
            exact Finset.single_le_sum
              (fun d hd ↦ abs_nonneg (cellRemainder d n))
              (Finset.mem_univ c)
          _ = signedError n := rfl
      have hscale := mul_le_mul_of_nonneg_right
        (hprobToCell.trans hcellToProfile) (pairWeight_nonneg p q r s)
      have hbound := hraw.trans (herr.trans hscale)
      simpa only [law, baseLaw, widen_probability, widen_value,
        valuationTilt_probability, valuationTilt_value] using hbound
    have hsingleProfile : ∀ c p, p ∈ primeBand n W →
        |(law c).probability.expect
            (fun omega ↦ divInd p ((law c).value omega)) -
          paperDivisibilityMain n p| ≤
          signedError n * singleWeight p 1 := by
      intro c p hpBand
      let q := aux p
      have hqErase : q ∈ (primeBand n W).erase p := hauxn p hpBand
      have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
      have hyPos : 0 < yNat n :=
        (prime_of_mem_primeBand hpBand).pos.trans_le hpY
      have hD4 : p ≤ yNat n ^ 4 := by
        calc
          p ≤ yNat n := hpY
          _ ≤ yNat n ^ 4 := by
            nlinarith [sq_nonneg ((yNat n : ℤ) ^ 2 - 1)]
      have hpair := hprofileCell c p hpBand q hqErase 1 0
        (by simpa only [pairPower, pow_one, pow_zero, mul_one] using hD4)
      simpa only [pairPower, pow_one, pow_zero, mul_one,
        pairWeight_eq_single_mul, singleWeight, Nat.cast_zero,
        zero_add, div_one, mul_one] using hpair
    exact ⟨hprofileCell, hsingleProfile⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨signedError, fun n ↦ Finset.sum_nonneg
    (fun c hc ↦ abs_nonneg (cellRemainder c n)),
    hsignedErrorT, hsignedErrorRate, N₀, ?_⟩
  intro n eta hn heta
  exact hN₀ n hn eta heta

/-- Backwards-compatible paper normalization of the positive-endpoint
core. -/
theorem exists_boxIndependent_fixedFiniteMixture_signed_profiles
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 1 ≤ C c) (hC_le : ∀ c, C c ≤ Cmax) :
    ∀ W : ℕ, 1 < W →
      (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
    ∀ B : ℝ, 0 ≤ B →
      ∃ signedError : ℕ → ℝ,
        (∀ n, 0 ≤ signedError n) ∧
        Tendsto signedError atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ signedError n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            let law := fun c ↦ widen
              (valuationTilt (H c) (physicalBound (A c) n)
                (physicalBound (C c) n) (yNat n) (hS c)
                (primeBand n W) eta (L n))
              (physicalBound_mono (hC_le c) n)
            (∀ c p, p ∈ primeBand n W →
              ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
              pairPower p q r s ≤ yNat n ^ 4 →
              |(law c).probability.expect
                  (fun omega ↦ divInd (pairPower p q r s)
                    ((law c).value omega)) -
                paperDivisibilityMain n (pairPower p q r s)| ≤
                  signedError n * pairWeight p q r s) ∧
            (∀ c p, p ∈ primeBand n W →
              |(law c).probability.expect
                  (fun omega ↦ divInd p ((law c).value omega)) -
                paperDivisibilityMain n p| ≤
                  signedError n * singleWeight p 1) := by
  exact exists_boxIndependent_fixedFiniteMixture_signed_profiles_of_pos
    H A C Cmax hA hAC
      (fun c ↦ lt_of_lt_of_le zero_lt_one (hC c)) hC_le

end

end Erdos390.Full.FixedFiniteMixtureSignedSquarefree
