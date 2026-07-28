import Erdos390.Full.FullTiltPrimePowerActualChamber

/-!
# Arbitrary-power fallback for the genuine full valuation tilt

The sharp Dickman estimate is used only inside the literal four-mark
chamber.  Outside it we need a box-uniform reciprocal bound.  This file
proves that bound directly on the actual structured cell, with the full
prime band present in the score, and derives the corresponding covariance
bound for two distinct primes.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPrimePowerFallback

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open ValuationScoreDomination OmittedTiltFallback
open OmittedTiltPairChamber FullTiltPairChamber
open PaperTwoLocalRestorationBound StructuredCellValuationLaw
open FullTiltPrimePowerCovariance

noncomputable section

/-- An indicator covariance is controlled by the joint event and the
product of the two marginal events. -/
theorem abs_primePower_covariance_le_joint_add_marginals
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    |mu.covariance
        (fun omega ↦ divInd (p ^ r) (value omega))
        (fun omega ↦ divInd (q ^ s) (value omega))| ≤
      mu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)) +
        mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
          mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) := by
  have hcov := covariance_primePowers_eq_pairProbability_sub
    mu value hpq hp hq (r := r) (s := s)
  rw [hcov]
  have hjoint0 : 0 ≤ mu.expect
      (fun omega ↦ divInd (pairPower p q r s) (value omega)) :=
    mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hp0 : 0 ≤ mu.expect
      (fun omega ↦ divInd (p ^ r) (value omega)) :=
    mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hq0 : 0 ≤ mu.expect
      (fun omega ↦ divInd (q ^ s) (value omega)) :=
    mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  simpa only [abs_of_nonneg hjoint0, abs_of_nonneg (mul_nonneg hp0 hq0)] using
    (abs_sub
      (mu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)))
      (mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
        mu.expect (fun omega ↦ divInd (q ^ s) (value omega))))

/-- Reciprocal event bounds imply the matching reciprocal covariance
bound.  This is the finite algebra used beyond four marks. -/
theorem abs_primePower_covariance_le_reciprocal
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ} {G : ℝ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) (hG : 0 ≤ G)
    (hjoint : mu.expect (fun omega ↦
        divInd (pairPower p q r s) (value omega)) ≤
      G / ((p : ℝ) ^ r * (q : ℝ) ^ s))
    (hpr : mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) ≤
      G / (p : ℝ) ^ r)
    (hqs : mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) ≤
      G / (q : ℝ) ^ s) :
    |mu.covariance
        (fun omega ↦ divInd (p ^ r) (value omega))
        (fun omega ↦ divInd (q ^ s) (value omega))| ≤
      (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  have hbase := abs_primePower_covariance_le_joint_add_marginals
    mu value hpq hp hq (r := r) (s := s)
  have hpden0 : 0 ≤ (p : ℝ) ^ r := by positivity
  have hqden0 : 0 ≤ (q : ℝ) ^ s := by positivity
  calc
    _ ≤ mu.expect (fun omega ↦
          divInd (pairPower p q r s) (value omega)) +
        mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
          mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) := hbase
    _ ≤ G / ((p : ℝ) ^ r * (q : ℝ) ^ s) +
        (G / (p : ℝ) ^ r) * (G / (q : ℝ) ^ s) := by
      apply add_le_add hjoint
      exact mul_le_mul hpr hqs
        (mu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _)
        (div_nonneg hG hpden0)
    _ = (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s) := by ring

/-- **Uniform arbitrary-power fallback for the actual full tilt.**

The ceiling `G₀` depends on the fixed box and cutoff, but not on `n`, the
moving primes, or the exponents.  No four-mark assumption occurs. -/
theorem exists_uniform_fullTilt_primePower_fallback
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ G₀ : ℝ, 0 < G₀ ∧ ∃ N₀ : ℕ,
      ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) eta (L n)).probability.expect
            (fun m ↦ divInd D (m : ℕ)) ≤ G₀ / (D : ℝ) := by
  let c := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  let G₀ := paperPairFallbackCeiling B c W
  have hG₀ : 0 < G₀ := paperPairFallbackCeiling_pos B c W hc
  obtain ⟨Ndensity, hdensity⟩ :=
    PaperScaleMarkedCell.exists_structuredCell_density_lower_bound H hA hAC
  obtain ⟨NG, hG⟩ := Filter.eventually_atTop.mp
    (eventually_paperPairFallbackConstant_le B C c W hB hC hc hW)
  have hcastTop : Tendsto (fun n : ℕ ↦ (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hphysEvent : ∀ᶠ n : ℕ in atTop, 1 ≤ physicalBound C n := by
    filter_upwards [hcastTop.eventually (eventually_ge_atTop (1 / C))]
      with n hInvCn
    unfold physicalBound
    apply Nat.le_floor
    have hOne : (1 : ℝ) ≤ C * (n : ℝ) := by
      have := (div_le_iff₀ hC).mp hInvCn
      simpa [mul_comm] using this
    exact_mod_cast hOne
  obtain ⟨Nphys, hphys⟩ := Filter.eventually_atTop.mp hphysEvent
  let N₀ := max Ndensity (max NG (max Nphys 2))
  refine ⟨G₀, hG₀, N₀, ?_⟩
  intro n eta hN heta
  have hNdensity : Ndensity ≤ n := by dsimp only [N₀] at hN; omega
  have hNG : NG ≤ n := by dsimp only [N₀] at hN; omega
  have hNphys : Nphys ≤ n := by dsimp only [N₀] at hN; omega
  have hn : 1 < n := by dsimp only [N₀] at hN; omega
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  change ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
    (valuationTilt H (physicalBound A n) (physicalBound C n)
      (yNat n) hS (primeBand n W) eta (L n)).probability.expect
        (fun m ↦ divInd D (m : ℕ)) ≤ G₀ / (D : ℝ)
  intro hS D hD
  have hcellDensity := hdensity hNdensity
  have hCpos : 0 < C := hC
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hMpos : 0 < physicalBound C n :=
    lt_of_lt_of_le Nat.zero_lt_one (hphys n hNphys)
  have hMcast : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hcard : c * (physicalBound C n : ℝ) ≤ (S.card : ℝ) := by
    calc
      c * (physicalBound C n : ℝ) ≤ c * (C * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hMcast hc.le
      _ = PaperScaleMarkedCell.paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hCpos.ne']
      _ ≤ (S.card : ℝ) := by simpa only [S] using hcellDensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  have hpW : ∀ z ∈ primeBand n W, W ≤ z := by
    intro z hz
    exact (cutoff_lt_of_mem_primeBand hz).le
  have hraw := omittedValuationTilt_divInd_le S (primeBand n W) hS eta
    hD hMpos hB (L_pos hn) hW hc hcard hSpos hSle hpW heta
  have hGn : paperPairFallbackConstant B C c W n ≤ G₀ := hG n hNG
  have hden0 : 0 ≤ (D : ℝ) := by positivity
  calc
    (valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd D (m : ℕ)) ≤
      paperPairFallbackConstant B C c W n / (D : ℝ) := by
        simpa only [StructuredCellValuationLaw.valuationTilt_probability,
          paperPairFallbackConstant, S, div_div] using hraw
    _ ≤ G₀ / (D : ℝ) :=
      div_le_div_of_nonneg_right hGn hden0

/-- Uniform reciprocal covariance fallback for every exponent pair. -/
theorem exists_uniform_fullTilt_primePower_covariance_fallback
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ G₀ : ℝ, 0 < G₀ ∧ ∃ N₀ : ℕ,
      ∀ {n p q r s : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
      p ∈ primeBand n W → q ∈ (primeBand n W).erase p →
      (∀ z ∈ primeBand n W, |eta z| ≤ B) →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        let law := valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) eta (L n)
        |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
          (G₀ + G₀ ^ 2) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  obtain ⟨G₀, hG₀, N₀, hprob⟩ :=
    exists_uniform_fullTilt_primePower_fallback
      H hA hAC (zero_lt_one.trans_le hC) B W hB hW
  refine ⟨G₀, hG₀, N₀, ?_⟩
  intro n p q r s eta hN hpBand hqErase heta
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  change ∀ hS : S.Nonempty,
    let law := valuationTilt H (physicalBound A n) (physicalBound C n)
      (yNat n) hS (primeBand n W) eta (L n)
    |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
      (G₀ + G₀ ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)
  intro hS
  let law := valuationTilt H (physicalBound A n) (physicalBound C n)
    (yNat n) hS (primeBand n W) eta (L n)
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hprobAll := hprob eta hN heta hS
  have hjoint := hprobAll (pairPower p q r s) (pairPower_pos hp hq)
  have hpr := hprobAll (p ^ r) (Nat.pow_pos hp.pos)
  have hqs := hprobAll (q ^ s) (Nat.pow_pos hq.pos)
  apply abs_primePower_covariance_le_reciprocal law.probability law.value
    hpq hp hq hG₀.le
  · simpa only [law, StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value, pairPower,
      Nat.cast_mul, Nat.cast_pow] using hjoint
  · simpa only [law, StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value, Nat.cast_pow] using hpr
  · simpa only [law, StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value, Nat.cast_pow] using hqs

end

end Erdos390.Full.FullTiltPrimePowerFallback
