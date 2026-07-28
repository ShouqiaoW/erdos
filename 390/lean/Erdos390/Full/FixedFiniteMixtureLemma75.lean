import Erdos390.Full.FixedFiniteMixturePrimePower
import Erdos390.Full.PaperPrimePowerGenericAggregation
import Erdos390.Full.PaperPrimePowerFourDisplays

/-!
# Lemma 7.5 for a fixed finite mixture

The hypotheses are common one- and two-divisor profiles on every component
cell, together with the common reciprocal fallback and the deterministic
tail ledgers.  The conclusion is the exact five-field statement used in
the paper.  The mixture weights are arbitrary; the proof includes the
between-cell covariance through the expectation-level mixture theorems.
-/

open scoped BigOperators

namespace Erdos390.Full.FixedFiniteMixtureLemma75

open ArithmeticModel Scale FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open OmittedTiltPairChamber DickmanFourMarkProductKernel
open PaperPrimePowerChamberError PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays PaperPrimePowerRow
open PaperPrimePowerLemma75 PaperPrimePowerGenericAggregation
open FixedFiniteMixturePrimePower PaperValuationCutoff ValuationCutoff

noncomputable section

variable {Cell : Type*} [Fintype Cell]
  {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
  {M : ℕ}

/-- Exact finite-`n` fixed-mixture form of paper Lemma 7.5. -/
theorem sigmaMixture_primePowerTransferBounds_of_common_profiles
    {C_K epsilon G₀ k Gf Tlin Tquad Tdiag Trow : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) - fourMarkProfile x * fourMarkProfile z| ≤
        C_K * x * z)
    (hCK : 0 ≤ C_K) (hε : 0 ≤ epsilon) (hG₀ : 0 ≤ G₀)
    (hk : 0 ≤ k) (hGf : 0 ≤ Gf)
    (hTlin : 0 ≤ Tlin) (hTquad : 0 ≤ Tquad)
    (hTdiag : 0 ≤ Tdiag) (hTrow : 0 ≤ Trow)
    (weight : FiniteProbability Cell)
    (law : ∀ c, BoundedValuationLaw (Omega c) M)
    {n W : ℕ} (hn : 1 < n) (hW : 1 < W)
    (hpairProfile : ∀ c p, p ∈ primeBand n W →
      ∀ q, q ∈ (primeBand n W).erase p → ∀ r s,
      pairPower p q r s ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (pairPower p q r s) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n
          (pairPower p q r s)| ≤
        pairProbabilityScale epsilon G₀ k * pairWeight p q r s)
    (hsingleProfile : ∀ c p, p ∈ primeBand n W → ∀ r,
      p ^ r ≤ yNat n ^ 4 →
      |(law c).probability.expect
          (fun omega ↦ divInd (p ^ r) ((law c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain n (p ^ r)| ≤
        pairProbabilityScale epsilon G₀ k * singleWeight p r)
    (hfallback : ∀ c D, 0 < D →
      (law c).probability.expect
        (fun omega ↦ divInd D ((law c).value omega)) ≤ Gf / (D : ℝ))
    (htailJI : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M), eJI Gf n p q r) ≤
        Tlin * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)))
    (htailIJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (valuationCutoff q M), eIJ Gf n p q s) ≤
        Tlin * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2)
    (htailJJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        ∑ s ∈ highExponents (valuationCutoff q M), eJJ Gf n p q r s) ≤
          Tquad * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2)
    (htailD : ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r)) ≤
          Tdiag * (1 / (p : ℝ)) ^ 2)
    (htailRow : ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            (((∑ r ∈ highExponents (valuationCutoff p M),
                eJI Gf n p q r)) +
              (∑ s ∈ highExponents (valuationCutoff q M),
                eIJ Gf n p q s) +
              (∑ r ∈ highExponents (valuationCutoff p M),
                ∑ s ∈ highExponents (valuationCutoff q M),
                  eJJ Gf n p q r s))) +
          3 * (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r))) ≤ Trow)
    (hbandT : PrimeSums.bandTReciprocalSum n W ≤ 2 * Real.log 4) :
    PrimePowerTransferBounds (sigmaMixture weight law) n W
      (paperPrimePowerConstant C_K)
      (genericAggregationRemainder
        (primePowerChamberRemainder epsilon G₀ k)
        Tlin Tquad Tdiag Trow n W) := by
  let mix := sigmaMixture weight law
  let Eprob := pairProbabilityScale epsilon G₀ k
  let Ecov := pairCovarianceScale Eprob
  let Eagg := primePowerChamberRemainder epsilon G₀ k
  have hEprob : 0 ≤ Eprob := pairProbabilityScale_nonneg hε hG₀ hk
  have hEagg : 0 ≤ Eagg := primePowerChamberRemainder_nonneg hε hG₀ hk
  have hgeneric : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p, ∀ r s : ℕ,
      |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q + Ecov) * pairWeight p q r s +
          covarianceTail Gf n p q r s := by
    intro p hpBand q hqErase r s
    exact sigmaMixture_primePower_covariance_le_chamber_add_tail
      hkernel hCK hEprob hGf weight law hn hpBand hqErase
      (fun c u v hD4 ↦ hpairProfile c p hpBand q hqErase u v hD4)
      hfallback
  have hdiag : ∀ p ∈ primeBand n W, ∀ r : ℕ,
      mix.probability.expect (mix.Ip p r) ≤
        ((1 / DickmanBasic.rho DickmanBasic.U) + Eprob) *
            singleWeight p r + probabilityTail Gf n p r := by
    intro p hpBand r
    exact sigmaMixture_primePower_probability_le_chamber_add_tail
      hEprob weight law hn hpBand
        (fun c hD4 ↦ hsingleProfile c p hpBand r hD4) hfallback
  have hCmain : 0 ≤ primePowerMainConstant C_K :=
    primePowerMainConstant_nonneg hCK
  have hJIpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      |mix.probability.covariance (mix.Ip p r) (mix.I q)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q + Eagg) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
            eJI Gf n p q r := by
    intro p hpBand q hqErase r hr
    exact ji_display_of_generic mix hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (by simpa only [Eprob, Ecov, Eagg] using
        hgeneric p hpBand q hqErase r 1)
  have hIJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ s ∈ highExponents (valuationCutoff q M),
      |mix.probability.covariance (mix.I p) (mix.Ip q s)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q + Eagg) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
            eIJ Gf n p q s := by
    intro p hpBand q hqErase s hs
    exact ij_display_of_generic mix hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (by simpa only [Eprob, Ecov, Eagg] using
        hgeneric p hpBand q hqErase 1 s)
  have hJJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |mix.probability.covariance (mix.Ip p r) (mix.Ip q s)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q + Eagg) *
          ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s)) + eJJ Gf n p q r s := by
    intro p hpBand q hqErase r hr s hs
    exact jj_display_of_generic mix hCK hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (by simpa only [Eprob, Ecov, Eagg] using
        hgeneric p hpBand q hqErase r s)
  have hDpoint : ∀ p ∈ primeBand n W,
      ∀ r ∈ highExponents (valuationCutoff p M),
      mix.probability.expect (mix.Ip p r) ≤
        (primePowerMainConstant C_K + Eagg) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD Gf n p r := by
    intro p hpBand r hr
    exact diagonal_display_of_generic mix hCK hε hG₀ hk
      (by simpa only [Eprob, Eagg] using hdiag p hpBand r)
  have hfinal := primePowerTransferBounds_of_pointwise mix hn hW
    hCmain hEagg hTlin hTquad hTdiag hTrow
    hJIpoint hIJpoint hJJpoint hDpoint htailJI htailIJ htailJJ htailD
    htailRow hbandT
  simpa only [paperPrimePowerConstant, mix] using hfinal

end

end Erdos390.Full.FixedFiniteMixtureLemma75
