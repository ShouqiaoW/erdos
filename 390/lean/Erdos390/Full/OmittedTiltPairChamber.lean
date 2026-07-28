import Erdos390.Full.TwoLocalRestoration

/-!
# The actual omitted-tilt two-prime four-mark chamber

This file specializes the uniform marked-divisibility theorem to the literal
moduli `p^a q^b` occurring in the two-local restoration of Lemma 7.5.  All
side conditions are discharged from membership of `p,q` in the paper prime
band, the four-mark inequality `a+b <= 4`, and coprimality with the fixed
head.  In particular, the theorem below is about the genuine structured
cell and the genuine omitted valuation score, not an abstract probability
law or a conditional analytic contract.
-/

open Filter Topology

namespace Erdos390.Full.OmittedTiltPairChamber

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability ValuationScoreDomination
open PaperScaleMarkedCell OmittedTiltMarkedProbability
open TwoLocalRestoration

noncomputable section

/-- The literal two-prime-power modulus used in the four-mark chamber. -/
def pairPower (p q a b : ℕ) : ℕ := p ^ a * q ^ b

theorem pairPower_pos {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) :
    0 < pairPower p q a b := by
  unfold pairPower
  exact Nat.mul_pos (Nat.pow_pos hp.pos) (Nat.pow_pos hq.pos)

/-- Two band primes with at most four total marks give a modulus below the
actual finite smoothness cutoff `yNat n ^ 4`. -/
theorem pairPower_le_yNat_pow_four
    {n W p q a b : ℕ} (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W) (hab : a + b ≤ 4) :
    pairPower p q a b ≤ yNat n ^ 4 := by
  have hpY : p ≤ yNat n := le_yNat_of_mem_primeBand hpBand
  have hqY : q ≤ yNat n := le_yNat_of_mem_primeBand hqBand
  have hYpos : 0 < yNat n :=
    (prime_of_mem_primeBand hpBand).pos.trans_le hpY
  calc
    pairPower p q a b = p ^ a * q ^ b := rfl
    _ ≤ yNat n ^ a * yNat n ^ b :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hpY a) (Nat.pow_le_pow_left hqY b)
    _ = yNat n ^ (a + b) := (pow_add _ _ _).symm
    _ ≤ yNat n ^ 4 := Nat.pow_le_pow_right hYpos hab

/-- Every two-prime four-mark modulus is genuinely `yNat`-friable. -/
theorem pairPower_mem_smoothNumbers
    {n W p q a b : ℕ} (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W) :
    pairPower p q a b ∈ Nat.smoothNumbers (yNat n + 1) := by
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hpSmooth : p ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hp.pos (by
      have := le_yNat_of_mem_primeBand hpBand
      omega)
  have hqSmooth : q ∈ Nat.smoothNumbers (yNat n + 1) :=
    Nat.mem_smoothNumbers_of_lt hq.pos (by
      have := le_yNat_of_mem_primeBand hqBand
      omega)
  exact Nat.mul_mem_smoothNumbers
    (pow_mem_smoothNumbers hpSmooth a) (pow_mem_smoothNumbers hqSmooth b)

/-- A two-prime-power modulus is coprime to every prime left in the score
after erasing its two local primes. -/
theorem pairPower_coprime_erasePair
    {n W p q a b r : ℕ} (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W)
    (hr : r ∈ erasePair (primeBand n W) p q) :
    Nat.Coprime (pairPower p q a b) r := by
  have hrEraseQ := Finset.mem_erase.mp hr
  have hrEraseP := Finset.mem_erase.mp hrEraseQ.2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hrPrime := prime_of_mem_primeBand hrEraseP.2
  have hpr : Nat.Coprime p r :=
    (Nat.coprime_primes hp hrPrime).mpr hrEraseP.1.symm
  have hqr : Nat.Coprime q r :=
    (Nat.coprime_primes hq hrPrime).mpr hrEraseQ.1.symm
  unfold pairPower
  exact (hpr.pow_left a).mul_left (hqr.pow_left b)

/-- **Actual two-prime four-mark probability.**

For every fixed head, physical cell, tilt box, and cutoff, one nonnegative
error tending to zero controls all band primes, all exponent pairs with at
most four total marks, and all tilt vectors in the box.  The score really is
the full band score with `p,q` erased. -/
theorem exists_uniform_erasePair_pairPower_paper_bound_of_le
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧ Tendsto epsilon atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q a b : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p →
        pairPower p q a b ≤ yNat n ^ 4 →
        Nat.Coprime p H.modulus → Nat.Coprime q H.modulus →
        (∀ r ∈ primeBand n W, |eta r| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦ valuationScore
                  (erasePair (primeBand n W) p q) eta (L n) m)).expect
                (fun m : S ↦ divInd (pairPower p q a b) m) -
              paperDivisibilityMain n (pairPower p q a b)| ≤
            epsilon n / (pairPower p q a b : ℝ) := by
  obtain ⟨epsilon, hepsilon0, hepsilonT, N₀, hbound⟩ :=
    exists_uniform_omittedTilt_divInd_paper_bound
      H hA hAC hC B W hB hW
  refine ⟨epsilon, hepsilon0, hepsilonT, N₀, ?_⟩
  intro n p q a b eta hn hpBand hqErase hD4 hpHead hqHead heta
  have hqData := Finset.mem_erase.mp hqErase
  have hpq : p ≠ q := hqData.1.symm
  have hqBand : q ∈ primeBand n W := hqData.2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hDpos : 0 < pairPower p q a b := pairPower_pos hp hq
  have hDsmooth : pairPower p q a b ∈
      Nat.smoothNumbers (yNat n + 1) :=
    pairPower_mem_smoothNumbers hpBand hqBand
  have hDhead : Nat.Coprime (pairPower p q a b) H.modulus := by
    unfold pairPower
    exact (hpHead.pow_left a).mul_left (hqHead.pow_left b)
  have hPsub : erasePair (primeBand n W) p q ⊆ primeBand n W :=
    erasePair_subset (primeBand n W) p q
  have hDcop : ∀ r ∈ erasePair (primeBand n W) p q,
      Nat.Coprime (pairPower p q a b) r := by
    intro r hr
    exact pairPower_coprime_erasePair hpBand hqBand hr
  have hetaErase : ∀ r ∈ erasePair (primeBand n W) p q, |eta r| ≤ B := by
    intro r hr
    exact heta r (hPsub hr)
  exact hbound (P := erasePair (primeBand n W) p q) eta hn hDpos hD4
    hDsmooth hDhead hPsub hDcop hetaErase

/-- The simpler exponent-simplex form is a direct corollary of the actual
finite four-mark condition. -/
theorem exists_uniform_erasePair_pairPower_paper_bound
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧ Tendsto epsilon atTop (𝓝 0) ∧
      ∃ N₀ : ℕ, ∀ {n p q a b : ℕ} (eta : ℕ → ℝ),
        N₀ ≤ n → p ∈ primeBand n W →
        q ∈ (primeBand n W).erase p → a + b ≤ 4 →
        Nat.Coprime p H.modulus → Nat.Coprime q H.modulus →
        (∀ r ∈ primeBand n W, |eta r| ≤ B) →
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        S.Nonempty ∧ ∀ hS : S.Nonempty,
          |((uniformOnFinset S hS).exponentialTilt
                (fun m : S ↦ valuationScore
                  (erasePair (primeBand n W) p q) eta (L n) m)).expect
                (fun m : S ↦ divInd (pairPower p q a b) m) -
              paperDivisibilityMain n (pairPower p q a b)| ≤
            epsilon n / (pairPower p q a b : ℝ) := by
  obtain ⟨epsilon, hepsilon0, hepsilonT, N₀, hbound⟩ :=
    exists_uniform_erasePair_pairPower_paper_bound_of_le
      H hA hAC hC B W hB hW
  refine ⟨epsilon, hepsilon0, hepsilonT, N₀, ?_⟩
  intro n p q a b eta hn hpBand hqErase hab hpHead hqHead heta
  exact hbound eta hn hpBand hqErase
    (pairPower_le_yNat_pow_four hpBand (Finset.mem_erase.mp hqErase).2 hab)
    hpHead hqHead heta

end

end Erdos390.Full.OmittedTiltPairChamber
