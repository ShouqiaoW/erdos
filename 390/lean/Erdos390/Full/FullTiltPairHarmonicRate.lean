import Erdos390.Full.FullTiltPairChamber
import Erdos390.Full.OmittedTiltHarmonicRate

/-!
# Harmonic-rate full-tilt pair chamber

This module propagates the definitional omitted-score remainder with
`epsilon n * log (L n) -> 0` through the exact two-local restoration.  The
cutoff is the literal arithmetic chamber `pairPower <= yNat n ^ 4`.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPairHarmonicRate

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination ValuationCutoff
open PaperScaleMarkedCell OmittedTiltPairChamber OmittedTiltFallback
open OmittedTiltHarmonicRate
open TwoLocalRestoration TwoLocalPairRestoration
open TwoLocalRestorationBound PaperTwoLocalRestorationBound
open FullTiltPairChamber

noncomputable section

/-- Actual full-valuation two-prime chamber with a remainder that remains
vanishing after two complete harmonic-row losses. -/
theorem exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto epsilon atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n) ^ 2)
        atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p →
        pairPower p q r s ≤ yNat n ^ 4 →
        Nat.Coprime p H.modulus → Nat.Coprime q H.modulus →
        (∀ z ∈ primeBand n W, |eta z| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦ valuationScore (primeBand n W) eta (L n) m)).expect
                (fun m : S ↦ divInd (pairPower p q r s) m) -
              paperDivisibilityMain n (pairPower p q r s)| ≤
            fullPairChamberError H A C B W n p q r s eta epsilon := by
  obtain ⟨K, cOmit, epsilon, hK, hcOmit, hepsilonDef,
      hepsilon0, hepsilonT, hepsilonRate, hepsilonRateSq, Nomit, homit⟩ :=
    exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate
      H hA hAC hC B W hB hW
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let c := pairFallbackDensity H A C
  have hc : 0 < c := pairFallbackDensity_pos_of_pos H hAC hC
  have hhalfEvent := eventually_pairRestorationError_zero_le_half
    B C c W hB hC hc hW
  obtain ⟨Nhalf, hhalf⟩ := Filter.eventually_atTop.mp hhalfEvent
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
  let N₀ := max Nomit (max Ndensity (max Nhalf (max Nphys 2)))
  refine ⟨epsilon, hepsilon0, hepsilonT, hepsilonRate, hepsilonRateSq,
    N₀, ?_⟩
  intro n p q r s eta hN hpBand hqErase hD4 hpHead hqHead heta
  have hNomit : Nomit ≤ n := by dsimp only [N₀] at hN; omega
  have hNdensity : Ndensity ≤ n := by dsimp only [N₀] at hN; omega
  have hNhalf : Nhalf ≤ n := by dsimp only [N₀] at hN; omega
  have hNphys : Nphys ≤ n := by dsimp only [N₀] at hN; omega
  have hn : 1 < n := by dsimp only [N₀] at hN; omega
  have hqData := Finset.mem_erase.mp hqErase
  have hpq : p ≠ q := hqData.1.symm
  have hqBand : q ∈ primeBand n W := hqData.2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hDsmooth : pairPower p q r s ∈
      Nat.smoothNumbers (yNat n + 1) :=
    pairPower_mem_smoothNumbers hpBand hqBand
  have hDhead : Nat.Coprime (pairPower p q r s) H.modulus := by
    unfold pairPower
    exact (hpHead.pow_left r).mul_left (hqHead.pow_left s)
  let P := erasePair (primeBand n W) p q
  have hPsub : P ⊆ primeBand n W :=
    erasePair_subset (primeBand n W) p q
  have hDcop : ∀ u ∈ P, Nat.Coprime (pairPower p q r s) u := by
    intro u hu
    exact pairPower_coprime_erasePair hpBand hqBand hu
  have hetaP : ∀ u ∈ P, |eta u| ≤ B := by
    intro u hu
    exact heta u (hPsub hu)
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  have hpairData := homit (P := P) eta hNomit hDpos hD4 hDsmooth
    hDhead hPsub hDcop hetaP
  change S.Nonempty ∧ ∀ hS : S.Nonempty,
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta (L n) m)).expect
          (fun m : S ↦ divInd (pairPower p q r s) m) -
        paperDivisibilityMain n (pairPower p q r s)| ≤
      epsilon n / (pairPower p q r s : ℝ) at hpairData
  obtain ⟨hSnonempty, hmainAll⟩ := hpairData
  refine ⟨hSnonempty, ?_⟩
  intro hS
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
      _ = paperCellDensity H A C * (n : ℝ) / 2 := by
        dsimp only [c, pairFallbackDensity]
        field_simp [hCpos.ne']
      _ ≤ (S.card : ℝ) := by
        simpa only [S] using hcellDensity
  have hSpos : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact pos_of_mem_smoothInterval (mem_structuredCell.mp hm).1
  have hSle : ∀ m ∈ S, m ≤ physicalBound C n := by
    intro m hm
    exact (mem_smoothInterval.mp (mem_structuredCell.mp hm).1).2.1
  let omitted := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore P eta (L n) m)
  let G := paperPairFallbackConstant B C c W n
  have hpW : ∀ z ∈ P, W ≤ z := by
    intro z hz
    exact (cutoff_lt_of_mem_primeBand (hPsub hz)).le
  have hprob : ∀ u v : ℕ,
      omitted.expect (fun m : S ↦ divInd (pairPower p q u v) m) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v) := by
    intro u v
    have hPairPos : 0 < pairPower p q u v := pairPower_pos hp hq
    have hraw := omittedValuationTilt_divInd_le S P hS eta hPairPos hMpos
      hB (L_pos hn) hW hc hcard hSpos hSle hpW hetaP
    simpa only [omitted, G, paperPairFallbackConstant, P, pairPower,
      Nat.cast_mul, Nat.cast_pow, div_div] using hraw
  have hG : 0 ≤ G := paperPairFallbackConstant_nonneg B C c W n hc.le
  have hnormalizer := hhalf n hNhalf p hpBand q hqBand (eta p) (eta q)
    (heta p hpBand) (heta q hqBand)
  have hmain := hmainAll hS
  have hquot := abs_pairRestoredQuotient_sub_main_le
    (nu := omitted) (value := fun m : S ↦ (m : ℕ))
    (p := p) (q := q)
    (Ap := valuationCutoff p (physicalBound C n))
    (Aq := valuationCutoff q (physicalBound C n))
    (r := r) (s := s) (etaP := eta p) (etaQ := eta q)
    (L := L n) (G := G)
    (main := paperDivisibilityMain n (pairPower p q r s))
    (epsilon := epsilon n / (pairPower p q r s : ℝ))
    hprob hG hmain (div_nonneg (hepsilon0 n) (by positivity)) hnormalizer
  have hexact := fullTilt_pairPower_eq_maxExponent_ratio hS
    (primeBand n W) eta hpBand hqBand hpq hp hq hSpos hSle
    (L := L n) (M := physicalBound C n) (r := r) (s := s)
  have hexact' :
      ((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore (primeBand n W) eta (L n) m)).expect
          (fun m : S ↦ divInd (pairPower p q r s) m) =
        pairRestoredNumerator omitted (fun m : S ↦ (m : ℕ)) p q
            (valuationCutoff p (physicalBound C n))
            (valuationCutoff q (physicalBound C n))
            (eta p) (eta q) (L n) r s /
          pairRestoredNumerator omitted (fun m : S ↦ (m : ℕ)) p q
            (valuationCutoff p (physicalBound C n))
            (valuationCutoff q (physicalBound C n))
            (eta p) (eta q) (L n) 0 0 := by
    simpa only [pairRestoredNumerator, omitted, P] using hexact
  rw [hexact']
  simpa only [fullPairChamberError, c, G] using hquot

end

end Erdos390.Full.FullTiltPairHarmonicRate
