import Erdos390.Full.PaperPrimePowerPointwise
import Erdos390.Full.FullTiltPairHarmonicRate

/-!
# Actual-law pointwise splice for Lemma 7.5

The two theorems below connect the genuine full valuation tilt to the
deterministic chamber/fallback splice.  They deliberately accept the local
probability and fallback estimates as hypotheses, so the final uniform
wrapper can choose one common remainder and one common large-`n` threshold.
-/

namespace Erdos390.Full.PaperPrimePowerActualSplice

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open OmittedTiltPairChamber FullTiltPairChamber
open FullTiltPrimePowerCovariance FullTiltPrimePowerActualChamber
open PaperPrimePowerChamberError PaperPrimePowerPointwise
open StructuredCellValuationLaw
open DickmanFourMarkProductKernel PaperScaleMarkedCell
open PaperTwoLocalRestorationBound LocalFugacityBounds

noncomputable section

/-- Actual full-tilt covariance, sharply inside the literal chamber and with
the reciprocal residual outside it. -/
theorem actual_primePower_covariance_le_chamber_add_tail
    {C_K : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) -
          fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z)
    (hCK : 0 ≤ C_K)
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) {G₀ k Gf : ℝ}
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hS : (structuredCell H (physicalBound A n) (physicalBound C n)
      (yNat n)).Nonempty)
    (hepsilon : 0 ≤ epsilon n)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hG : paperPairFallbackConstant B C (pairFallbackDensity H A C) W n ≤ G₀)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
      coefficientTail z (ValuationCutoff.valuationCutoff z (physicalBound C n))
        u (eta z) (L n) ≤
          k * (((u : ℝ) + 1) / (z : ℝ) ^ u))
    (hpair : ∀ u v : ℕ, pairPower p q u v ≤ yNat n ^ 4 →
      |(valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q u v) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q u v)| ≤
      fullPairChamberError H A C B W n p q u v eta epsilon)
    (hfallback :
      let law := valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (Gf + Gf ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)) :
    let law := valuationTilt H (physicalBound A n) (physicalBound C n)
      (yNat n) hS (primeBand n W) eta (L n)
    |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
      (C_K * tPrime n p * tPrime n q +
          pairCovarianceScale (pairProbabilityScale (epsilon n) G₀ k)) *
        pairWeight p q r s + covarianceTail Gf n p q r s := by
  dsimp only
  let law := valuationTilt H (physicalBound A n) (physicalBound C n)
    (yNat n) hS (primeBand n W) eta (L n)
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have htp := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
  have htq := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
  let E := pairProbabilityScale (epsilon n) G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  apply covariance_le_chamber_add_tail hCK hECov htp htq
  · intro hD4
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
    exact fullTilt_primePower_covariance_le_of_le hkernel H eta epsilon hn
      hpBand hqErase hD4 hS hc hepsilon (hpair r s hD4)
        (hpair r 0 hD4P) (hpair 0 s hD4Q)
  · intro hD4
    exact fullPrimePowerCovarianceError_le_pairWeight H eta epsilon hn hpBand
      hqBand hD4 hepsilon hc hG hG₀ hk hcoef
  · simpa only [law] using hfallback

/-- Actual one-prime probability obtained from the two-local restoration
with a distinct auxiliary band prime. -/
theorem actual_primePower_probability_le_chamber_add_tail
    (H : Pattern) {A C B : ℝ} {W n p q r : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) {G₀ k Gf : ℝ}
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p)
    (hS : (structuredCell H (physicalBound A n) (physicalBound C n)
      (yNat n)).Nonempty)
    (hepsilon : 0 ≤ epsilon n)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hG : paperPairFallbackConstant B C (pairFallbackDensity H A C) W n ≤ G₀)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
      coefficientTail z (ValuationCutoff.valuationCutoff z (physicalBound C n))
        u (eta z) (L n) ≤
          k * (((u : ℝ) + 1) / (z : ℝ) ^ u))
    (hpair : ∀ u : ℕ, pairPower p q u 0 ≤ yNat n ^ 4 →
      |(valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q u 0) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q u 0)| ≤
      fullPairChamberError H A C B W n p q u 0 eta epsilon)
    (hfallback :
      (valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          ((valuationTilt H (physicalBound A n) (physicalBound C n)
            (yNat n) hS (primeBand n W) eta (L n)).Ip p r) ≤
        Gf / (p : ℝ) ^ r) :
    let law := valuationTilt H (physicalBound A n) (physicalBound C n)
      (yNat n) hS (primeBand n W) eta (L n)
    law.probability.expect (law.Ip p r) ≤
      ((1 / DickmanBasic.rho DickmanBasic.U) +
          pairProbabilityScale (epsilon n) G₀ k) * singleWeight p r +
        probabilityTail Gf n p r := by
  dsimp only
  let law := valuationTilt H (physicalBound A n) (physicalBound C n)
    (yNat n) hS (primeBand n W) eta (L n)
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hp := prime_of_mem_primeBand hpBand
  let E := pairProbabilityScale (epsilon n) G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  apply probability_le_chamber_add_tail
    (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le) hE
  · intro hD4
    have hD4Pair : pairPower p q r 0 ≤ yNat n ^ 4 := by
      simpa only [pairPower, pow_zero, mul_one] using hD4
    have hprobMain := hpair r hD4Pair
    have hmain := abs_paperDivisibilityMain_pow_le_singleWeight hn hp hD4
    have htriangle : law.probability.expect (law.Ip p r) ≤
        |law.probability.expect (law.Ip p r) -
            paperDivisibilityMain n (p ^ r)| +
          |paperDivisibilityMain n (p ^ r)| := by
      have habs := abs_add_le
        (law.probability.expect (law.Ip p r) -
          paperDivisibilityMain n (p ^ r))
        (paperDivisibilityMain n (p ^ r))
      have hself := le_abs_self (law.probability.expect (law.Ip p r))
      rw [sub_add_cancel] at habs
      exact hself.trans habs
    calc
      law.probability.expect (law.Ip p r) ≤
          |law.probability.expect (law.Ip p r) -
              paperDivisibilityMain n (p ^ r)| +
            |paperDivisibilityMain n (p ^ r)| := htriangle
      _ ≤ fullPairChamberError H A C B W n p q r 0 eta epsilon +
          (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
        apply add_le_add
        · simpa only [law, pairPower, pow_zero, mul_one,
            StructuredCellValuationLaw.valuationTilt_probability,
            StructuredCellValuationLaw.valuationTilt_value] using hprobMain
        · exact hmain
      _ ≤ E * singleWeight p r +
          (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
        exact add_le_add
          (by
            have hraw := fullPairChamberError_le_pairWeight H eta epsilon hn
              hpBand hqBand hD4Pair hepsilon hc hG hG₀ hk hcoef
            simpa only [E, pairWeight_eq_single_mul, singleWeight,
              Nat.cast_zero, zero_add, pow_zero, div_one, mul_one] using hraw)
          le_rfl
      _ = (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r +
          E * singleWeight p r := by ring
  · intro _
    exact le_rfl
  · simpa only [law] using hfallback

end

end Erdos390.Full.PaperPrimePowerActualSplice
