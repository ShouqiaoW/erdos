import Erdos390.Full.PaperTwoLocalRestorationBound

/-!
# Full valuation tilt in the two-prime four-mark chamber

This is the paper-facing closure of the two-local restoration.  It combines

* the actual structured-cell omitted-score four-mark estimate,
* the exact `N_{r,s}/N_{0,0}` restoration identity,
* the arbitrary-modulus reciprocal fallback for every restoration term, and
* the uniform lower bound for the exact normalizer.

The conclusion concerns the genuine full valuation tilt over the genuine
structured cell.  No covariance estimate or analytic transfer is assumed.
-/

open Filter Topology

namespace Erdos390.Full.FullTiltPairChamber

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability ValuationScoreDomination ValuationCutoff
open PaperScaleMarkedCell OmittedTiltPairChamber OmittedTiltFallback
open TwoLocalRestoration TwoLocalPairRestoration
open TwoLocalRestorationBound PaperTwoLocalRestorationBound

noncomputable section

/-- The fixed cell-density constant used by the arbitrary-modulus fallback. -/
def pairFallbackDensity (H : Pattern) (A C : ℝ) : ℝ :=
  paperCellDensity H A C / (2 * C)

theorem pairFallbackDensity_pos (H : Pattern) {A C : ℝ}
    (hAC : A < C) (hC : 1 ≤ C) :
    0 < pairFallbackDensity H A C := by
  unfold pairFallbackDensity
  exact div_pos (paperCellDensity_pos H hAC)
    (mul_pos (by norm_num) (zero_lt_one.trans_le hC))

/-- The fallback density is positive for every positive physical upper
endpoint; the normalization `1 ≤ C` used by older wrappers is unnecessary. -/
theorem pairFallbackDensity_pos_of_pos (H : Pattern) {A C : ℝ}
    (hAC : A < C) (hC : 0 < C) :
    0 < pairFallbackDensity H A C := by
  unfold pairFallbackDensity
  exact div_pos (paperCellDensity_pos H hAC) (mul_pos (by norm_num) hC)

/-- The explicit full-tilt error ledger.  The first and third terms are the
two-local restoration errors; the middle term is the sharp omitted-score
four-mark error. -/
def fullPairChamberError (H : Pattern) (A C B : ℝ) (W n p q r s : ℕ)
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) : ℝ :=
  let c := pairFallbackDensity H A C
  let G := paperPairFallbackConstant B C c W n
  let Ap := valuationCutoff p (physicalBound C n)
  let Aq := valuationCutoff q (physicalBound C n)
  2 * (pairRestorationError p q Ap Aq r s (eta p) (eta q) (L n) G +
    epsilon n / (pairPower p q r s : ℝ) +
    |paperDivisibilityMain n (pairPower p q r s)| *
      pairRestorationError p q Ap Aq 0 0 (eta p) (eta q) (L n) G)

theorem fullPairChamberError_nonneg
    (H : Pattern) (A C B : ℝ) (W n p q r s : ℕ)
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hepsilon : 0 ≤ epsilon n) :
    0 ≤ fullPairChamberError H A C B W n p q r s eta epsilon := by
  let c := pairFallbackDensity H A C
  let G := paperPairFallbackConstant B C c W n
  have hG : 0 ≤ G := paperPairFallbackConstant_nonneg B C c W n hc
  have hD : 0 ≤ (pairPower p q r s : ℝ) := by positivity
  have hDinv : 0 ≤ epsilon n / (pairPower p q r s : ℝ) :=
    div_nonneg hepsilon hD
  unfold fullPairChamberError
  dsimp only
  have hrs := pairRestorationError_nonneg p q
    (valuationCutoff p (physicalBound C n))
    (valuationCutoff q (physicalBound C n)) r s (eta p) (eta q) (L n) G hG
  have hzero := pairRestorationError_nonneg p q
    (valuationCutoff p (physicalBound C n))
    (valuationCutoff q (physicalBound C n)) 0 0 (eta p) (eta q) (L n) G hG
  positivity

/-- **Actual full-tilt two-prime four-mark estimate.**

One nonnegative omitted-score remainder tending to zero works uniformly for
every pair of distinct moving band primes, every exponent pair with at most
four marks, and every coefficient vector in the fixed box.  The remaining
displayed terms are explicit coefficient tails and the exact finite
normalizer correction. -/
theorem exists_uniform_fullTilt_pairPower_paper_bound_of_le
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧ Tendsto epsilon atTop (𝓝 0) ∧
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
  obtain ⟨epsilon, hepsilon0, hepsilonT, Npair, hpair⟩ :=
    exists_uniform_erasePair_pairPower_paper_bound_of_le
      H hA hAC hC B W hB hW
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound H hA hAC
  let c := pairFallbackDensity H A C
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hc : 0 < c := pairFallbackDensity_pos H hAC hC
  have hhalfEvent := eventually_pairRestorationError_zero_le_half
    B C c W hB hCpos hc hW
  obtain ⟨Nhalf, hhalf⟩ := Filter.eventually_atTop.mp hhalfEvent
  let N₀ := max Npair (max Ndensity (max Nhalf 2))
  refine ⟨epsilon, hepsilon0, hepsilonT, N₀, ?_⟩
  intro n p q r s eta hN hpBand hqErase hD4 hpHead hqHead heta
  have hNpair : Npair ≤ n := by dsimp only [N₀] at hN; omega
  have hNdensity : Ndensity ≤ n := by dsimp only [N₀] at hN; omega
  have hNhalf : Nhalf ≤ n := by dsimp only [N₀] at hN; omega
  have hn : 1 < n := by dsimp only [N₀] at hN; omega
  have hqData := Finset.mem_erase.mp hqErase
  have hpq : p ≠ q := hqData.1.symm
  have hqBand : q ∈ primeBand n W := hqData.2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  have hpairData := hpair eta hNpair hpBand hqErase hD4 hpHead hqHead heta
  change S.Nonempty ∧ ∀ hS : S.Nonempty,
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore
            (erasePair (primeBand n W) p q) eta (L n) m)).expect
          (fun m : S ↦ divInd (pairPower p q r s) m) -
        paperDivisibilityMain n (pairPower p q r s)| ≤
      epsilon n / (pairPower p q r s : ℝ) at hpairData
  obtain ⟨hSnonempty, hmainAll⟩ := hpairData
  refine ⟨hSnonempty, ?_⟩
  intro hS
  have hcellDensity := hdensity hNdensity
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hMpos : 0 < physicalBound C n := by
    have hphysical : n ≤ physicalBound C n := by
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (n : ℝ) ≤ C * (n : ℝ) by
        nlinarith [show (0 : ℝ) ≤ n by positivity])
    exact hnpos.trans_le hphysical
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
  let P := erasePair (primeBand n W) p q
  let omitted := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore P eta (L n) m)
  let G := paperPairFallbackConstant B C c W n
  have hPsub : P ⊆ primeBand n W := by
    exact erasePair_subset (primeBand n W) p q
  have hpW : ∀ z ∈ P, W ≤ z := by
    intro z hz
    exact (cutoff_lt_of_mem_primeBand (hPsub hz)).le
  have hetaP : ∀ z ∈ P, |eta z| ≤ B := by
    intro z hz
    exact heta z (hPsub hz)
  have hprob : ∀ u v : ℕ,
      omitted.expect (fun m : S ↦ divInd (pairPower p q u v) m) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v) := by
    intro u v
    have hDpos : 0 < pairPower p q u v := pairPower_pos hp hq
    have hraw := omittedValuationTilt_divInd_le S P hS eta hDpos hMpos
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

/-- The exponent-simplex version retained for callers that only require the
stronger sufficient condition `r+s ≤ 4`. -/
theorem exists_uniform_fullTilt_pairPower_paper_bound
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧ Tendsto epsilon atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p → r + s ≤ 4 →
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
  obtain ⟨epsilon, hepsilon0, hepsilonT, N₀, hbound⟩ :=
    exists_uniform_fullTilt_pairPower_paper_bound_of_le
      H hA hAC hC B W hB hW
  refine ⟨epsilon, hepsilon0, hepsilonT, N₀, ?_⟩
  intro n p q r s eta hn hpBand hqErase hrs hpHead hqHead heta
  exact hbound eta hn hpBand hqErase
    (pairPower_le_yNat_pow_four hpBand (Finset.mem_erase.mp hqErase).2 hrs)
    hpHead hqHead heta

end

end Erdos390.Full.FullTiltPairChamber
