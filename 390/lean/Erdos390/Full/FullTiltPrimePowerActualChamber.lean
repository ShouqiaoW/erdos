import Erdos390.Full.FullTiltPrimePowerCovariance

/-!
# Genuine prime-power covariance on the actual four-mark chamber

The paper chamber is the arithmetic condition
`p ^ r * q ^ s <= yNat n ^ 4`, not the stronger exponent condition
`r + s <= 4`.  This distinction matters for small band primes.  This file
derives the exact logarithmic simplex inequality from the arithmetic chamber
and upgrades the full-tilt covariance theorem accordingly.
-/

namespace Erdos390.Full.FullTiltPrimePowerActualChamber

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PaperScaleMarkedCell OmittedTiltPairChamber
open FullTiltPairChamber DickmanFourMarkProductKernel
open StructuredCellValuationLaw FullTiltPrimePowerCovariance

noncomputable section

/-- Membership in the literal arithmetic four-mark chamber implies the
weighted logarithmic simplex condition used by the Dickman product kernel. -/
theorem pairPower_tPrime_sum_le_four
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W) (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4) :
    (r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q ≤ 4 := by
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hnpos : 0 < n := Nat.zero_lt_of_lt hn
  have hypos : 0 < y n := y_pos hnpos
  have hylog : 0 < Real.log (y n) := by
    rw [log_y hnpos]
    exact mul_pos (by norm_num) (L_pos hn)
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hDR : (0 : ℝ) < (pairPower p q r s : ℕ) := by
    exact_mod_cast hDpos
  have hyNatPos : 0 < yNat n :=
    hp.pos.trans_le (le_yNat_of_mem_primeBand hpBand)
  have hyNatRpos : (0 : ℝ) < (yNat n : ℕ) := by
    exact_mod_cast hyNatPos
  have hcast : ((pairPower p q r s : ℕ) : ℝ) =
      (p : ℝ) ^ r * (q : ℝ) ^ s := by
    simp [pairPower]
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hlogD : Real.log ((pairPower p q r s : ℕ) : ℝ) =
      (r : ℝ) * Real.log (p : ℝ) +
        (s : ℝ) * Real.log (q : ℝ) := by
    rw [hcast, Real.log_mul (pow_ne_zero r hpR) (pow_ne_zero s hqR),
      Real.log_pow, Real.log_pow]
  have hDCast : ((pairPower p q r s : ℕ) : ℝ) ≤
      (yNat n : ℝ) ^ 4 := by
    exact_mod_cast hD4
  have hlogDNat : Real.log ((pairPower p q r s : ℕ) : ℝ) ≤
      4 * Real.log (yNat n : ℝ) := by
    have h := Real.log_le_log hDR hDCast
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hyNatUpper : (yNat n : ℝ) ≤ y n := Nat.floor_le hypos.le
  have hlogNatY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatRpos hyNatUpper
  have hlogDY :
      (r : ℝ) * Real.log (p : ℝ) +
          (s : ℝ) * Real.log (q : ℝ) ≤ 4 * Real.log (y n) := by
    rw [← hlogD]
    exact hlogDNat.trans (by linarith)
  unfold tPrime
  calc
    (r : ℝ) * (Real.log (p : ℝ) / Real.log (y n)) +
        (s : ℝ) * (Real.log (q : ℝ) / Real.log (y n)) =
      ((r : ℝ) * Real.log (p : ℝ) +
        (s : ℝ) * Real.log (q : ℝ)) / Real.log (y n) := by
          field_simp [hylog.ne']
    _ ≤ 4 := (div_le_iff₀ hylog).2 (by simpa using hlogDY)

/-- The deterministic paper covariance bound on the literal arithmetic
four-mark chamber. -/
theorem abs_paperMainCovariance_le_of_le
    {C_K : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) -
          fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z)
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W) (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4) :
    |paperDivisibilityMain n (pairPower p q r s) -
        paperDivisibilityMain n (pairPower p q r 0) *
          paperDivisibilityMain n (pairPower p q 0 s)| ≤
      C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have htp0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
  have htq0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
  let x : ℝ := (r : ℝ) * tPrime n p
  let z : ℝ := (s : ℝ) * tPrime n q
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hxz4 : x + z ≤ 4 := by
    simpa only [x, z] using
      pairPower_tPrime_sum_le_four hn hpBand hqBand hD4
  rw [paperMainCovariance_eq_profileKernel hn hp hq]
  rw [abs_div]
  have hpRpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hqRpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hdenpos : 0 < (p : ℝ) ^ r * (q : ℝ) ^ s :=
    mul_pos (pow_pos hpRpos r) (pow_pos hqRpos s)
  rw [abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hkernel x z hx0 hz0 hxz4) hdenpos.le

/-- The genuine full-tilt prime-power covariance estimate throughout the
literal arithmetic four-mark chamber. -/
theorem fullTilt_primePower_covariance_le_of_le
    {C_K : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) -
          fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z)
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ)
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4)
    (hS : (structuredCell H (physicalBound A n) (physicalBound C n)
      (yNat n)).Nonempty)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hepsilon : 0 ≤ epsilon n)
    (hpair : |(valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q r s) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q r s)| ≤
      fullPairChamberError H A C B W n p q r s eta epsilon)
    (hpr : |(valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q r 0) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q r 0)| ≤
      fullPairChamberError H A C B W n p q r 0 eta epsilon)
    (hqs : |(valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q 0 s) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q 0 s)| ≤
      fullPairChamberError H A C B W n p q 0 s eta epsilon) :
    let law := valuationTilt H (physicalBound A n) (physicalBound C n)
      (yNat n) hS (primeBand n W) eta (L n)
    |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
      C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) +
        fullPrimePowerCovarianceError H A C B W n p q r s eta epsilon := by
  dsimp only
  let law := valuationTilt H (physicalBound A n) (physicalBound C n)
    (yNat n) hS (primeBand n W) eta (L n)
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  let Ers := fullPairChamberError H A C B W n p q r s eta epsilon
  let Er := fullPairChamberError H A C B W n p q r 0 eta epsilon
  let Es := fullPairChamberError H A C B W n p q 0 s eta epsilon
  have hEr : 0 ≤ Er := fullPairChamberError_nonneg
    H A C B W n p q r 0 eta epsilon hc hepsilon
  have hprob := abs_primePower_covariance_sub_mainCov_le
    law.probability law.value hpq hp hq hEr
    (Mrs := paperDivisibilityMain n (pairPower p q r s))
    (Mr := paperDivisibilityMain n (pairPower p q r 0))
    (Ms := paperDivisibilityMain n (pairPower p q 0 s))
    (by simpa only [law, StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hpair)
    (by simpa only [law, pairPower, pow_zero, mul_one,
      StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hpr)
    (by simpa only [law, pairPower, pow_zero, one_mul,
      StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hqs)
  have hmain := abs_paperMainCovariance_le_of_le hkernel hn hpBand hqBand hD4
  have htriangle :
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        |law.probability.covariance (law.Ip p r) (law.Ip q s) -
          (paperDivisibilityMain n (pairPower p q r s) -
            paperDivisibilityMain n (pairPower p q r 0) *
              paperDivisibilityMain n (pairPower p q 0 s))| +
        |paperDivisibilityMain n (pairPower p q r s) -
          paperDivisibilityMain n (pairPower p q r 0) *
            paperDivisibilityMain n (pairPower p q 0 s)| := by
    have := abs_add_le
      (law.probability.covariance (law.Ip p r) (law.Ip q s) -
        (paperDivisibilityMain n (pairPower p q r s) -
          paperDivisibilityMain n (pairPower p q r 0) *
            paperDivisibilityMain n (pairPower p q 0 s)))
      (paperDivisibilityMain n (pairPower p q r s) -
        paperDivisibilityMain n (pairPower p q r 0) *
          paperDivisibilityMain n (pairPower p q 0 s))
    simpa only [sub_add_cancel] using this
  exact htriangle.trans (by
    have := add_le_add hprob hmain
    simpa only [fullPrimePowerCovarianceError, Ers, Er, Es, law,
      add_comm, add_left_comm, add_assoc] using this)

/-- **Uniform covariance export on the actual arithmetic chamber.**

One box-independent Dickman constant and one nonnegative vanishing
omitted-score remainder work for every moving pair and every exponent pair
whose literal modulus is at most `yNat n ^ 4`. -/
theorem exists_uniform_fullTilt_primePower_covariance_bound_of_le
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ C_K : ℝ, 0 < C_K ∧
      ∃ epsilon : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon n) ∧ Filter.Tendsto epsilon Filter.atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
          N₀ ≤ n → p ∈ primeBand n W →
          q ∈ (primeBand n W).erase p →
          pairPower p q r s ≤ yNat n ^ 4 →
          Nat.Coprime p H.modulus → Nat.Coprime q H.modulus →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := structuredCell H (physicalBound A n) (physicalBound C n)
            (yNat n)
          S.Nonempty ∧ ∀ hS : S.Nonempty,
            let law := valuationTilt H (physicalBound A n)
              (physicalBound C n) (yNat n) hS (primeBand n W) eta (L n)
            |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
              C_K * ((r : ℝ) * tPrime n p) *
                  ((s : ℝ) * tPrime n q) /
                    ((p : ℝ) ^ r * (q : ℝ) ^ s) +
                fullPrimePowerCovarianceError
                  H A C B W n p q r s eta epsilon := by
  obtain ⟨C_K, hCK, hkernel⟩ :=
    exists_boxIndependent_fourMark_productKernel_bound
  obtain ⟨epsilon, hepsilon0, hepsilonT, Npair, hpair⟩ :=
    exists_uniform_fullTilt_pairPower_paper_bound_of_le
      H hA hAC hC B W hB hW
  let N₀ := max Npair 2
  refine ⟨C_K, hCK, epsilon, hepsilon0, hepsilonT, N₀, ?_⟩
  intro n p q r s eta hN hpBand hqErase hD4 hpHead hqHead heta
  have hNpair : Npair ≤ n := by dsimp only [N₀] at hN; omega
  have hn : 1 < n := by dsimp only [N₀] at hN; omega
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hdivP : pairPower p q r 0 ∣ pairPower p q r s := by
    refine ⟨q ^ s, ?_⟩
    simp only [pairPower, pow_zero, mul_one]
  have hdivQ : pairPower p q 0 s ∣ pairPower p q r s := by
    refine ⟨p ^ r, ?_⟩
    simp only [pairPower, pow_zero, one_mul]
    exact (mul_comm (q ^ s) (p ^ r)).symm
  have hD4P : pairPower p q r 0 ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivP).trans hD4
  have hD4Q : pairPower p q 0 s ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivQ).trans hD4
  have hpairData := hpair eta hNpair hpBand hqErase hD4
    hpHead hqHead heta
  have hprData := hpair (r := r) (s := 0) eta hNpair hpBand hqErase hD4P
    hpHead hqHead heta
  have hqsData := hpair (r := 0) (s := s) eta hNpair hpBand hqErase hD4Q
    hpHead hqHead heta
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  change S.Nonempty ∧ ∀ hS : S.Nonempty,
      |(valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) eta (L n)).probability.covariance
          ((valuationTilt H (physicalBound A n) (physicalBound C n)
            (yNat n) hS (primeBand n W) eta (L n)).Ip p r)
          ((valuationTilt H (physicalBound A n) (physicalBound C n)
            (yNat n) hS (primeBand n W) eta (L n)).Ip q s)| ≤
        C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s) +
          fullPrimePowerCovarianceError H A C B W n p q r s eta epsilon
  obtain ⟨hSnonempty, hpairAll⟩ := hpairData
  obtain ⟨_, hprAll⟩ := hprData
  obtain ⟨_, hqsAll⟩ := hqsData
  refine ⟨by simpa only [S] using hSnonempty, ?_⟩
  intro hS
  have hc : 0 ≤ pairFallbackDensity H A C :=
    (pairFallbackDensity_pos H hAC hC).le
  apply fullTilt_primePower_covariance_le_of_le hkernel H eta epsilon hn
    hpBand hqErase hD4 hS hc (hepsilon0 n)
  · simpa only [StructuredCellValuationLaw.valuationTilt_probability,
      S] using hpairAll hS
  · simpa only [StructuredCellValuationLaw.valuationTilt_probability,
      pairPower, pow_zero, mul_one, S] using hprAll hS
  · simpa only [StructuredCellValuationLaw.valuationTilt_probability,
      pairPower, pow_zero, one_mul, S] using hqsAll hS

end

end Erdos390.Full.FullTiltPrimePowerActualChamber
