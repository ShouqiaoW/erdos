import Erdos390.Full.PaperPrimePowerAuxiliaryPrime
import Erdos390.Full.PaperPrimePowerSumAbsAggregation

/-!
# Exact export of paper Lemma 7.5

This module joins the literal four-mark chamber, the arbitrary-power
fallback, the four prime-power orientations, and their finite row
aggregation.  The final constant is independent of the tilt box.  All box
dependence is confined to a single remainder tending to zero.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerLemma75

set_option maxHeartbeats 2400000

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open StructuredCellValuationLaw
open DickmanFourMarkProductKernel
open FullTiltPairChamber FullTiltPairHarmonicRate
open FullTiltPrimePowerFallback
open OmittedTiltPairChamber PaperScaleMarkedCell LocalFugacityBounds
open PaperTwoLocalRestorationBound PaperValuationCutoff
open PaperPrimePowerChamberError PaperPrimePowerActualSplice
open PaperPrimePowerPointwise
open PaperPrimePowerFourDisplays PaperPrimePowerPairAggregation
open PaperPrimePowerTailLedger PaperPrimePowerTailRow
open PaperPrimePowerRemainderRate PaperPrimePowerAuxiliaryPrime
open PaperPrimePowerSumAbsAggregation
open ValuationCutoff PrimeSums PaperPrimePowerRow

noncomputable section

/-- The main row constant.  Its only non-universal input is the
box-independent Dickman four-mark kernel constant. -/
def paperPrimePowerConstant (C_K : ℝ) : ℝ :=
  pairAggregationConstant * primePowerMainConstant C_K *
    (2 * Real.log 4 + 5)

theorem paperPrimePowerConstant_nonneg {C_K : ℝ} (hCK : 0 ≤ C_K) :
    0 ≤ paperPrimePowerConstant C_K := by
  unfold paperPrimePowerConstant
  exact mul_nonneg
    (mul_nonneg pairAggregationConstant_nonneg
      (primePowerMainConstant_nonneg hCK))
    (by positivity)

theorem paperPrimePowerConstant_pos {C_K : ℝ} (hCK : 0 < C_K) :
    0 < paperPrimePowerConstant C_K := by
  unfold paperPrimePowerConstant
  have hAgg : 0 < pairAggregationConstant :=
    lt_of_lt_of_le (by norm_num) sixtyFour_le_pairAggregationConstant
  have hMain : 0 < primePowerMainConstant C_K := by
    unfold primePowerMainConstant
    exact add_pos (mul_pos (by norm_num) hCK)
      (one_div_pos.mpr DickmanBasic.rho_U_pos)
  exact mul_pos (mul_pos hAgg hMain) (by positivity)

/-- The one common error used in all four product-weighted displays and in
the final row estimate. -/
def primePowerLemma75Remainder
    (epsilon : ℕ → ℝ) (G₀ B Gf : ℝ) (W n : ℕ) : ℝ :=
  pairAggregationConstant *
      primePowerChamberRemainder (epsilon n) G₀ (coefficientScale B W n) +
    primePowerRowRemainder epsilon G₀ B Gf W n

/-- The five simultaneous conclusions of paper Lemma 7.5.  In particular,
the first three fields are sums of absolute pointwise covariances, not the
weaker absolute value of an already summed covariance. -/
structure PrimePowerTransferBounds
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (n W : ℕ)
    (C_pow epsilon_BW : ℝ) : Prop where
  ji : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)|) ≤
        (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ))
  ij : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)|) ≤
        (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
          (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2
  jj : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑ r ∈ highExponents (valuationCutoff p M),
      ∑ s ∈ highExponents (valuationCutoff q M),
        |law.probability.covariance (law.Ip p r) (law.Ip q s)|) ≤
      (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2
  diagonal : ∀ p ∈ primeBand n W,
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
      (C_pow + epsilon_BW) * (1 / (p : ℝ)) ^ 2
  row : ∀ p ∈ primeBand n W,
    (p : ℝ) * ∑ q ∈ primeBand n W,
      |law.covVV p q - law.covII p q| ≤
        C_pow * (1 / (W : ℝ)) + epsilon_BW

theorem PrimePowerTransferBounds.mono_epsilon
    {Omega : Type*} [Fintype Omega] {M n W : ℕ}
    {law : BoundedValuationLaw Omega M} {C_pow epsilon₁ epsilon₂ : ℝ}
    (hε : epsilon₁ ≤ epsilon₂)
    (h : PrimePowerTransferBounds law n W C_pow epsilon₁) :
    PrimePowerTransferBounds law n W C_pow epsilon₂ := by
  refine {
    ji := ?_
    ij := ?_
    jj := ?_
    diagonal := ?_
    row := ?_ }
  · intro p hp q hq
    exact (h.ji p hp q hq).trans (by gcongr)
  · intro p hp q hq
    exact (h.ij p hp q hq).trans (by gcongr)
  · intro p hp q hq
    exact (h.jj p hp q hq).trans (by gcongr)
  · intro p hp
    exact (h.diagonal p hp).trans (by gcongr)
  · intro p hp
    exact (h.row p hp).trans (add_le_add le_rfl hε)

/-- Finite-`n` assembly.  This theorem exposes every uniform input used in
the asymptotic wrapper below and is useful for auditing the quantifier
dependencies independently of the limit arguments. -/
theorem fullTilt_lemma75_bounds_of_uniform_inputs
    {C_K G₀ Gf : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) -
          fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z)
    (hCK : 0 ≤ C_K)
    (H : Pattern) {A C B : ℝ} {W n q₀ q₁ : ℕ}
    (epsilon : ℕ → ℝ) (aux : ℕ → ℕ) (η : ℕ → ℝ)
    (hn : 1 < n) (hW : 1 < W) (hB : 0 ≤ B)
    (hε : 0 ≤ epsilon n)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hG : paperPairFallbackConstant B C
        (pairFallbackDensity H A C) W n ≤ G₀)
    (hG₀ : 0 ≤ G₀) (hGf : 0 ≤ Gf)
    (hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
      coefficientTail z (valuationCutoff z (physicalBound C n))
          u (η z) (L n) ≤
        coefficientScale B W n * (((u : ℝ) + 1) / (z : ℝ) ^ u))
    (hpair :
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
        S.Nonempty ∧ ∀ hS : S.Nonempty, ∀ u v : ℕ,
          pairPower p q u v ≤ yNat n ^ 4 →
          |(valuationTilt H (physicalBound A n) (physicalBound C n)
                (yNat n) hS (primeBand n W) η (L n)).probability.expect
                (fun m ↦ divInd (pairPower p q u v) (m : ℕ)) -
              paperDivisibilityMain n (pairPower p q u v)| ≤
            fullPairChamberError H A C B W n p q u v η epsilon)
    (hfallback :
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) η (L n)).probability.expect
            (fun m ↦ divInd D (m : ℕ)) ≤ Gf / (D : ℝ))
    (hq₀Band : q₀ ∈ primeBand n W)
    (hq₁Erase : q₁ ∈ (primeBand n W).erase q₀)
    (haux : ∀ p ∈ primeBand n W,
      aux p ∈ (primeBand n W).erase p)
    (htailJI : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
          eJI Gf n p q r) ≤
        (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))))
    (htailIJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (actualExponentCutoff C n q),
          eIJ Gf n p q s) ≤
        (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
          ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))))
    (htailJJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        ∑ s ∈ highExponents (actualExponentCutoff C n q),
          eJJ Gf n p q r s) ≤
        (Gf + Gf ^ 2) * (((cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
            (yNat n : ℝ) ^ (2 / 3 : ℝ))))
    (htailD : ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (actualExponentCutoff C n p),
        (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r)) ≤
        Gf * ((2 * (cutoffScale W * L n) ^ 2) /
          ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)))
    (htail : ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            (((∑ r ∈ highExponents (actualExponentCutoff C n p),
                eJI Gf n p q r)) +
              (∑ s ∈ highExponents (actualExponentCutoff C n q),
                eIJ Gf n p q s) +
              (∑ r ∈ highExponents (actualExponentCutoff C n p),
                ∑ s ∈ highExponents (actualExponentCutoff C n q),
                  eJJ Gf n p q r s))) +
          3 * (∑ r ∈ highExponents (actualExponentCutoff C n p),
            (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r))) ≤
        tailRowMajorant Gf W n)
    (hbandT : bandTReciprocalSum n W ≤ 2 * Real.log 4) :
    let S := structuredCell H (physicalBound A n) (physicalBound C n)
      (yNat n)
    S.Nonempty ∧ ∀ hS : S.Nonempty,
      PrimePowerTransferBounds
        (valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) η (L n)) n W
        (paperPrimePowerConstant C_K)
        (primePowerLemma75Remainder epsilon G₀ B Gf W n) := by
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  change S.Nonempty ∧ ∀ hS : S.Nonempty, PrimePowerTransferBounds _ _ _ _ _
  have hseed := hpair q₀ hq₀Band q₁ hq₁Erase
  obtain ⟨hSnonempty, _hseedAll⟩ := hseed
  refine ⟨hSnonempty, ?_⟩
  intro hS
  let law := valuationTilt H (physicalBound A n) (physicalBound C n)
    (yNat n) hS (primeBand n W) η (L n)
  have hpairLocal : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p, ∀ u v : ℕ,
      pairPower p q u v ≤ yNat n ^ 4 →
      |law.probability.expect
            (fun m ↦ divInd (pairPower p q u v) (m : ℕ)) -
          paperDivisibilityMain n (pairPower p q u v)| ≤
        fullPairChamberError H A C B W n p q u v η epsilon := by
    intro p hpBand q hqErase u v hD4
    simpa only [law] using
      (hpair p hpBand q hqErase).2 hS u v hD4
  have hfallbackLocal : ∀ D : ℕ, 0 < D →
      law.probability.expect (fun m ↦ divInd D (law.value m)) ≤
        Gf / (D : ℝ) := by
    intro D hD
    simpa only [law, valuationTilt_probability, valuationTilt_value] using
      hfallback hS D hD
  have hcovFallback : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p, ∀ r s : ℕ,
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (Gf + Gf ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
    intro p hpBand q hqErase r s
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    apply abs_primePower_covariance_le_reciprocal law.probability law.value
      hpq hp hq hGf
    · simpa only [pairPower, Nat.cast_mul, Nat.cast_pow] using
        hfallbackLocal (pairPower p q r s) (pairPower_pos hp hq)
    · simpa only [Nat.cast_pow] using
        hfallbackLocal (p ^ r) (Nat.pow_pos hp.pos)
    · simpa only [Nat.cast_pow] using
        hfallbackLocal (q ^ s) (Nat.pow_pos hq.pos)
  have hk : 0 ≤ coefficientScale B W n := by
    unfold coefficientScale
    exact mul_nonneg (div_nonneg (mul_nonneg (by norm_num) hB)
      (L_pos hn).le) (Real.exp_pos _).le
  have hgeneric : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p, ∀ r s : ℕ,
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q +
            pairCovarianceScale
              (pairProbabilityScale (epsilon n) G₀
                (coefficientScale B W n))) *
          pairWeight p q r s + covarianceTail Gf n p q r s := by
    intro p hpBand q hqErase r s
    exact actual_primePower_covariance_le_chamber_add_tail
      hkernel hCK H η epsilon hn hpBand hqErase hS hε hc hG hG₀
      hk
      hcoef
      (fun u v hD4 ↦ hpairLocal p hpBand q hqErase u v hD4)
      (hcovFallback p hpBand q hqErase r s)
  have hdiag : ∀ p ∈ primeBand n W, ∀ r : ℕ,
      law.probability.expect (law.Ip p r) ≤
        ((1 / DickmanBasic.rho DickmanBasic.U) +
            pairProbabilityScale (epsilon n) G₀
              (coefficientScale B W n)) * singleWeight p r +
          probabilityTail Gf n p r := by
    intro p hpBand r
    let q := aux p
    have hqErase : q ∈ (primeBand n W).erase p := haux p hpBand
    have hprobFallback : law.probability.expect (law.Ip p r) ≤
        Gf / (p : ℝ) ^ r := by
      simpa only [BoundedValuationLaw.Ip, Nat.cast_pow] using
        hfallbackLocal (p ^ r)
          (Nat.pow_pos (prime_of_mem_primeBand hpBand).pos)
    exact actual_primePower_probability_le_chamber_add_tail
      H η epsilon hn hpBand hqErase hS hε hc hG hG₀ hk hcoef
      (fun u hD4 ↦ hpairLocal p hpBand q hqErase u 0 hD4)
      hprobFallback
  have hmain0 : 0 ≤ primePowerMainConstant C_K :=
    primePowerMainConstant_nonneg hCK
  have hrem0 : 0 ≤
      primePowerChamberRemainder (epsilon n) G₀
        (coefficientScale B W n) :=
    primePowerChamberRemainder_nonneg hε hG₀ hk
  have hJIpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p (physicalBound C n)),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q +
            primePowerChamberRemainder (epsilon n) G₀
              (coefficientScale B W n)) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
        eJI Gf n p q r := by
    intro p hpBand q hqErase r hr
    exact ji_display_of_generic law hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (hgeneric p hpBand q hqErase r 1)
  have hIJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ s ∈ highExponents (valuationCutoff q (physicalBound C n)),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q +
            primePowerChamberRemainder (epsilon n) G₀
              (coefficientScale B W n)) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
        eIJ Gf n p q s := by
    intro p hpBand q hqErase s hs
    exact ij_display_of_generic law hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (hgeneric p hpBand q hqErase 1 s)
  have hJJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p (physicalBound C n)),
      ∀ s ∈ highExponents (valuationCutoff q (physicalBound C n)),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (primePowerMainConstant C_K * tPrime n p * tPrime n q +
            primePowerChamberRemainder (epsilon n) G₀
              (coefficientScale B W n)) *
          ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s)) +
        eJJ Gf n p q r s := by
    intro p hpBand q hqErase r hr s hs
    exact jj_display_of_generic law hCK hε hG₀ hk
      (tPrime_nonneg_of_mem_primeBand hn hpBand)
      (tPrime_nonneg_of_mem_primeBand hn
        (Finset.mem_erase.mp hqErase).2)
      (hgeneric p hpBand q hqErase r s)
  have hDpoint : ∀ p ∈ primeBand n W,
      ∀ r ∈ highExponents (valuationCutoff p (physicalBound C n)),
      law.probability.expect (law.Ip p r) ≤
        (primePowerMainConstant C_K +
            primePowerChamberRemainder (epsilon n) G₀
              (coefficientScale B W n)) *
          (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD Gf n p r := by
    intro p hpBand r hr
    exact diagonal_display_of_generic law hCK hε hG₀ hk
      (hdiag p hpBand r)
  have hrow :=
    Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.paperBand_row_le_of_cutoff_pointwise
      law hn hW
    (primePowerMainConstant C_K)
    (primePowerChamberRemainder (epsilon n) G₀
      (coefficientScale B W n))
    (tailRowMajorant Gf W n)
    (eJI Gf n) (eIJ Gf n) (eJJ Gf n) (eD Gf n)
    hmain0 hrem0 hJIpoint hIJpoint hJJpoint hDpoint
    (by simpa only [actualExponentCutoff] using htail)
  have hmainCoeff :
      0 ≤ pairAggregationConstant * primePowerMainConstant C_K :=
    mul_nonneg pairAggregationConstant_nonneg hmain0
  have hCmain :
      pairAggregationConstant * primePowerMainConstant C_K ≤
        paperPrimePowerConstant C_K := by
    unfold paperPrimePowerConstant
    have hfactor : (1 : ℝ) ≤ 2 * Real.log 4 + 5 := by
      have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
      linarith
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hfactor hmainCoeff)
  have htail0 : 0 ≤ tailRowMajorant Gf W n :=
    tailRowMajorant_nonneg hGf hW hn
  have hrowRem0 : 0 ≤ primePowerRowRemainder epsilon G₀ B Gf W n := by
    unfold primePowerRowRemainder
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    exact add_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg pairAggregationConstant_nonneg hrem0)
          (by linarith)) (by positivity)) htail0
  have htailLeRow : tailRowMajorant Gf W n ≤
      primePowerRowRemainder epsilon G₀ B Gf W n := by
    unfold primePowerRowRemainder
    have hband : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    have hleft : 0 ≤ pairAggregationConstant *
        primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) *
        (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) :=
      mul_nonneg
        (mul_nonneg
          (mul_nonneg pairAggregationConstant_nonneg hrem0)
          (by linarith)) (by positivity)
    linarith
  let T : ℝ := Gf + Gf ^ 2
  let Ktail : ℝ := cutoffScale W * L n
  let Y : ℝ := yNat n
  have hT : 0 ≤ T := by
    dsimp only [T]
    nlinarith [sq_nonneg Gf]
  have hKtail : 0 ≤ Ktail := by
    dsimp only [Ktail]
    exact mul_nonneg (cutoffScale_pos hW).le (L_pos hn).le
  have hY : 0 < Y := by
    dsimp only [Y]
    exact_mod_cast (prime_of_mem_primeBand hq₀Band).pos.trans_le
      (le_yNat_of_mem_primeBand hq₀Band)
  have hband0 : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hTailLinear : T * (Ktail / Y) ≤ tailRowMajorant Gf W n := by
    unfold tailRowMajorant
    dsimp only [T, Ktail, Y]
    have hKY : 0 ≤ Ktail / Y := div_nonneg hKtail hY.le
    have hfirst : T * (Ktail / Y) ≤
        T * ((Ktail / Y) * (bandReciprocalSum n W + 1)) := by
      apply mul_le_mul_of_nonneg_left _ hT
      nlinarith [mul_nonneg hKY hband0]
    have hsecond : 0 ≤ T *
        (Ktail ^ 2 / Y ^ (2 / 3 : ℝ)) := by positivity
    have hthird : 0 ≤ 6 * Gf * (Ktail ^ 2 / Y ^ 2) := by positivity
    linarith
  have hTailQuadratic :
      T * (Ktail ^ 2 / Y ^ (2 / 3 : ℝ)) ≤
        tailRowMajorant Gf W n := by
    unfold tailRowMajorant
    dsimp only [T, Ktail, Y]
    have hfirst : 0 ≤
        T * ((Ktail / Y) * (bandReciprocalSum n W + 1)) := by
      positivity
    have hthird : 0 ≤ 6 * Gf * (Ktail ^ 2 / Y ^ 2) := by positivity
    linarith
  have hTailDiagonal : 2 * Gf * (Ktail ^ 2 / Y ^ 2) ≤
      tailRowMajorant Gf W n := by
    unfold tailRowMajorant
    dsimp only [T, Ktail, Y]
    have hfirst : 0 ≤
        T * ((Ktail / Y) * (bandReciprocalSum n W + 1)) := by
      positivity
    have hsecond : 0 ≤ T *
        (Ktail ^ 2 / Y ^ (2 / 3 : ℝ)) := by positivity
    have hthird : 2 * Gf * (Ktail ^ 2 / Y ^ 2) ≤
        6 * Gf * (Ktail ^ 2 / Y ^ 2) := by
      have hx : 0 ≤ Gf * (Ktail ^ 2 / Y ^ 2) := by positivity
      nlinarith
    linarith
  have hErrorLinear : pairAggregationConstant *
        primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) + T * (Ktail / Y) ≤
      primePowerLemma75Remainder epsilon G₀ B Gf W n := by
    unfold primePowerLemma75Remainder
    nlinarith [hTailLinear, htailLeRow]
  have hErrorQuadratic : pairAggregationConstant *
        primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) +
        T * (Ktail ^ 2 / Y ^ (2 / 3 : ℝ)) ≤
      primePowerLemma75Remainder epsilon G₀ B Gf W n := by
    unfold primePowerLemma75Remainder
    nlinarith [hTailQuadratic, htailLeRow]
  have hErrorDiagonal : pairAggregationConstant *
        primePowerChamberRemainder (epsilon n) G₀
          (coefficientScale B W n) +
        2 * Gf * (Ktail ^ 2 / Y ^ 2) ≤
      primePowerLemma75Remainder epsilon G₀ B Gf W n := by
    unfold primePowerLemma75Remainder
    nlinarith [hTailDiagonal, htailLeRow]
  refine {
    ji := ?_
    ij := ?_
    jj := ?_
    diagonal := ?_
    row := ?_ }
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := primePowerMainConstant C_K * tPrime n p * tPrime n q +
      primePowerChamberRemainder (epsilon n) G₀
        (coefficientScale B W n)
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg hmain0 (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hrem0
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covJI_le_of_cutoff_pointwise
        law hp hq.pos hK₀
          (eJI Gf n p q) (hJIpoint p hpBand q hqErase)
    have hres :
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound C n)),
            eJI Gf n p q r) ≤
          (T * (Ktail / Y)) * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) := by
      calc
        _ ≤ (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
            ((p : ℝ) ^ 2 * (q : ℝ) * (yNat n : ℝ))) :=
          htailJI p hpBand q hqBand
        _ = _ := by dsimp only [T, Ktail, Y]; ring
    have h8 : 8 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 (by positivity)) (by positivity)) hres)
    have hmainScaled := mul_le_mul_of_nonneg_right hCmain
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + T * (Ktail / Y) ≤
        paperPrimePowerConstant C_K * tPrime n p * tPrime n q +
          primePowerLemma75Remainder epsilon G₀ B Gf W n := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hErrorLinear]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) +
          (T * (Ktail / Y)) * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) := hraw
      _ = (pairAggregationConstant * K₀ + T * (Ktail / Y)) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := primePowerMainConstant C_K * tPrime n p * tPrime n q +
      primePowerChamberRemainder (epsilon n) G₀
        (coefficientScale B W n)
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg hmain0 (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hrem0
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covIJ_le_of_cutoff_pointwise
        law hp.pos hq hK₀
          (eIJ Gf n p q) (hIJpoint p hpBand q hqErase)
    have hres :
        (∑ s ∈ highExponents (valuationCutoff q (physicalBound C n)),
            eIJ Gf n p q s) ≤
          (T * (Ktail / Y)) * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 := by
      calc
        _ ≤ (Gf + Gf ^ 2) * ((cutoffScale W * L n) /
            ((p : ℝ) * (q : ℝ) ^ 2 * (yNat n : ℝ))) :=
          htailIJ p hpBand q hqBand
        _ = _ := by dsimp only [T, Ktail, Y]; ring
    have h8 : 8 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 (by positivity)) (by positivity)) hres)
    have hmainScaled := mul_le_mul_of_nonneg_right hCmain
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + T * (Ktail / Y) ≤
        paperPrimePowerConstant C_K * tPrime n p * tPrime n q +
          primePowerLemma75Remainder epsilon G₀ B Gf W n := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hErrorLinear]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 +
          (T * (Ktail / Y)) * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ + T * (Ktail / Y)) *
          (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := primePowerMainConstant C_K * tPrime n p * tPrime n q +
      primePowerChamberRemainder (epsilon n) G₀
        (coefficientScale B W n)
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg
          (mul_nonneg hmain0 (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hrem0
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covJJ_le_of_cutoff_pointwise
        law hp hq hK₀
          (eJJ Gf n p q) (hJJpoint p hpBand q hqErase)
    have hres :
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound C n)),
          ∑ s ∈ highExponents (valuationCutoff q (physicalBound C n)),
            eJJ Gf n p q r s) ≤
          (T * (Ktail ^ 2 / Y ^ (2 / 3 : ℝ))) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
      calc
        _ ≤ (Gf + Gf ^ 2) * (((cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (q : ℝ) ^ 2 *
              (yNat n : ℝ) ^ (2 / 3 : ℝ))) :=
          htailJJ p hpBand q hqBand
        _ = _ := by dsimp only [T, Ktail, Y]; ring
    have h64 : 64 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right sixtyFour_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h64 (by positivity)) (by positivity)) hres)
    have hmainScaled := mul_le_mul_of_nonneg_right hCmain
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ +
          T * (Ktail ^ 2 / Y ^ (2 / 3 : ℝ)) ≤
        paperPrimePowerConstant C_K * tPrime n p * tPrime n q +
          primePowerLemma75Remainder epsilon G₀ B Gf W n := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hErrorQuadratic]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) ^ 2 +
          (T * (Ktail ^ 2 / Y ^ (2 / 3 : ℝ))) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ +
          T * (Ktail ^ 2 / Y ^ (2 / 3 : ℝ))) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand
    have hp := prime_of_mem_primeBand hpBand
    let K₀ := primePowerMainConstant C_K +
      primePowerChamberRemainder (epsilon n) G₀
        (coefficientScale B W n)
    have hK₀ : 0 ≤ K₀ := by dsimp only [K₀]; positivity
    have hagg :=
      Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.expect_J_sq_le_of_cutoff_pointwise
        law hp hK₀ (eD Gf n p)
          (hDpoint p hpBand)
    have hres :
        (∑ r ∈ highExponents (valuationCutoff p (physicalBound C n)),
          (((2 * r - 3 : ℕ) : ℝ) * eD Gf n p r)) ≤
        (2 * Gf * (Ktail ^ 2 / Y ^ 2)) * (1 / (p : ℝ)) ^ 2 := by
      calc
        _ ≤ Gf * ((2 * (cutoffScale W * L n) ^ 2) /
            ((p : ℝ) ^ 2 * (yNat n : ℝ) ^ 2)) := htailD p hpBand
        _ = _ := by dsimp only [Ktail, Y]; ring
    have hquad : K₀ * quadraticHalfMass ≤
        pairAggregationConstant * K₀ := by
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left
          quadraticHalfMass_le_pairAggregationConstant hK₀)
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right hquad (by positivity)) hres)
    have hcoef : pairAggregationConstant * K₀ +
          2 * Gf * (Ktail ^ 2 / Y ^ 2) ≤
        paperPrimePowerConstant C_K +
          primePowerLemma75Remainder epsilon G₀ B Gf W n := by
      dsimp only [K₀]
      nlinarith [hCmain, hErrorDiagonal]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 +
          (2 * Gf * (Ktail ^ 2 / Y ^ 2)) *
            (1 / (p : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ +
          2 * Gf * (Ktail ^ 2 / Y ^ 2)) *
            (1 / (p : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand
    have hpRow := hrow p hpBand
    have hfirst :
        (pairAggregationConstant * primePowerMainConstant C_K) *
            (bandTReciprocalSum n W + 5) * (1 / (W : ℝ)) ≤
          paperPrimePowerConstant C_K * (1 / (W : ℝ)) := by
      have hWinv : 0 ≤ 1 / (W : ℝ) := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith) hmainCoeff) hWinv
    have hsmall :
        (p : ℝ) * ∑ q ∈ primeBand n W,
            |law.covVV p q - law.covII p q| ≤
          paperPrimePowerConstant C_K * (1 / (W : ℝ)) +
            primePowerRowRemainder epsilon G₀ B Gf W n := by
      calc
        _ ≤ (pairAggregationConstant * primePowerMainConstant C_K) *
              (bandTReciprocalSum n W + 5) * (1 / (W : ℝ)) +
            pairAggregationConstant *
                primePowerChamberRemainder (epsilon n) G₀
                  (coefficientScale B W n) *
                (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) +
              tailRowMajorant Gf W n := hpRow
        _ = (pairAggregationConstant * primePowerMainConstant C_K) *
              (bandTReciprocalSum n W + 5) * (1 / (W : ℝ)) +
            primePowerRowRemainder epsilon G₀ B Gf W n := by
          unfold primePowerRowRemainder
          ring
        _ ≤ _ := add_le_add hfirst le_rfl
    exact hsmall.trans (add_le_add le_rfl (by
      unfold primePowerLemma75Remainder
      nlinarith [mul_nonneg pairAggregationConstant_nonneg hrem0]))

/-- **Paper Lemma 7.5 (full uniform export).**

For every fixed tilt box and sufficiently large prime cutoff, the genuine
full-valuation tilt satisfies all three product-weighted sum-of-absolute
covariance estimates, the diagonal square estimate, and the covariance-row
transfer.  The constant `C_pow` is built before, and independently of, every
box-dependent quantity.  The sole box-dependent term is one common function
`epsilon_BW`, which tends to zero. -/
theorem exists_boxIndependent_fullTilt_primePower_transfer
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (W : ℕ) (hW : 1 < W)
    (hHW : H.modulus ≤ W) :
    ∃ C_pow : ℝ, 0 < C_pow ∧
      ∀ B : ℝ, 0 ≤ B →
      ∃ epsilon_BW : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon_BW n) ∧
        Tendsto epsilon_BW atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (η : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |η z| ≤ B) →
          let S := structuredCell H (physicalBound A n) (physicalBound C n)
            (yNat n)
          S.Nonempty ∧ ∀ hS : S.Nonempty,
            PrimePowerTransferBounds
              (valuationTilt H (physicalBound A n) (physicalBound C n)
                (yNat n) hS (primeBand n W) η (L n)) n W
              C_pow (epsilon_BW n) := by
  obtain ⟨C_K, hCK, hkernel⟩ :=
    exists_boxIndependent_fourMark_productKernel_bound
  let C_pow := paperPrimePowerConstant C_K
  refine ⟨C_pow, paperPrimePowerConstant_pos hCK, ?_⟩
  intro B hB
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  obtain ⟨epsilon, hε0, hεT, hεRate, _hεRateSq, Npair, hpairRaw⟩ :=
    exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate
      H hA hAC hCpos B W hB hW
  obtain ⟨Gf, hGf, Nfallback, hfallbackRaw⟩ :=
    exists_uniform_fullTilt_primePower_fallback
      H hA hAC hCpos B W hB hW
  obtain ⟨q₀, q₁, aux, _, _, _, hq₀q₁, _, hauxEvent⟩ :=
    exists_eventually_auxiliaryPrime W
  let c := pairFallbackDensity H A C
  let G₀ := paperPairFallbackCeiling B c W
  have hc : 0 < c := pairFallbackDensity_pos H hAC hC
  have hG₀ : 0 < G₀ := paperPairFallbackCeiling_pos B c W hc
  let rawRemainder := primePowerLemma75Remainder epsilon G₀ B Gf W
  let epsilon_BW : ℕ → ℝ := fun n ↦ |rawRemainder n|
  have hrawT : Tendsto rawRemainder atTop (nhds 0) := by
    obtain ⟨hchamberT, _hchamberRate⟩ :=
      tendsto_primePowerChamberRemainder_zero_and_rate
        epsilon G₀ B W hεT hεRate
    have hscaled := (tendsto_const_nhds : Tendsto
      (fun _n : ℕ ↦ pairAggregationConstant) atTop
        (nhds pairAggregationConstant)).mul hchamberT
    have hscaled0 : Tendsto (fun n : ℕ ↦
        pairAggregationConstant *
          primePowerChamberRemainder (epsilon n) G₀
            (coefficientScale B W n)) atTop (nhds 0) := by
      simpa only [mul_zero] using hscaled
    have hrowT := tendsto_primePowerRowRemainder_zero
      epsilon G₀ B Gf W hεT hεRate hε0 hG₀.le hB hGf.le hW
    dsimp only [rawRemainder, primePowerLemma75Remainder]
    simpa only [add_zero] using hscaled0.add hrowT
  have hremT : Tendsto epsilon_BW atTop (nhds 0) := by
    dsimp only [epsilon_BW]
    simpa only [abs_zero] using hrawT.abs
  have hrem0 : ∀ n, 0 ≤ epsilon_BW n := by
    intro n
    dsimp only [epsilon_BW]
    exact abs_nonneg _
  have hGEvent : ∀ᶠ n : ℕ in atTop,
      paperPairFallbackConstant B C c W n ≤ G₀ := by
    simpa only [G₀] using
      eventually_paperPairFallbackConstant_le B C c W hB hCpos hc hW
  have hcoefEvent := eventually_coefficientTail_le_of_pos B C W hB hCpos hW
  have htailJIEvent := eventually_sum_eJI_le Gf C W hGf.le hCpos hW
  have htailIJEvent := eventually_sum_eIJ_le Gf C W hGf.le hCpos hW
  have htailJJEvent := eventually_sum_eJJ_le Gf C W hGf.le hCpos hW
  have htailDEvent := eventually_sum_weighted_eD_le Gf C W hGf.le hCpos hW
  have htailEvent := eventually_tail_row_le Gf C W hGf.le hCpos hW
  have hbandTEvent := eventually_bandTReciprocalSum_le W
  have hNpair : ∀ᶠ n : ℕ in atTop, Npair ≤ n :=
    eventually_ge_atTop Npair
  have hNfallback : ∀ᶠ n : ℕ in atTop, Nfallback ≤ n :=
    eventually_ge_atTop Nfallback
  have hfinal : ∀ᶠ n : ℕ in atTop, ∀ η : ℕ → ℝ,
      (∀ z ∈ primeBand n W, |η z| ≤ B) →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      S.Nonempty ∧ ∀ hS : S.Nonempty,
        PrimePowerTransferBounds
          (valuationTilt H (physicalBound A n) (physicalBound C n)
            (yNat n) hS (primeBand n W) η (L n)) n W
          C_pow (epsilon_BW n) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hNpair, hNfallback,
      hGEvent, hcoefEvent, htailJIEvent, htailIJEvent, htailJJEvent,
      htailDEvent, htailEvent, hbandTEvent, hauxEvent]
      with n hn hnpair hnfallback hGn hcoefn htailJIn htailIJn
        htailJJn htailDn htailn hbandTn hauxn
    intro η hη
    obtain ⟨hq₀Band, hq₁Band, hauxn⟩ := hauxn
    have hq₁Erase : q₁ ∈ (primeBand n W).erase q₀ :=
      Finset.mem_erase.mpr ⟨hq₀q₁.ne', hq₁Band⟩
    have hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
        coefficientTail z (valuationCutoff z (physicalBound C n))
            u (η z) (L n) ≤
          coefficientScale B W n * (((u : ℝ) + 1) / (z : ℝ) ^ u) := by
      intro z hz u
      simpa only [coefficientScale] using
        hcoefn z hz (η z) (hη z hz) u
    have hpair :
        ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
          (structuredCell H (physicalBound A n) (physicalBound C n)
              (yNat n)).Nonempty ∧
            ∀ hS : (structuredCell H (physicalBound A n)
              (physicalBound C n) (yNat n)).Nonempty, ∀ u v : ℕ,
            pairPower p q u v ≤ yNat n ^ 4 →
            |(valuationTilt H (physicalBound A n) (physicalBound C n)
                  (yNat n) hS (primeBand n W) η (L n)).probability.expect
                  (fun m ↦ divInd (pairPower p q u v) (m : ℕ)) -
                paperDivisibilityMain n (pairPower p q u v)| ≤
              fullPairChamberError H A C B W n p q u v η epsilon := by
      intro p hpBand q hqErase
      have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
      have hpHead := coprime_modulus_of_mem_primeBand H hHW hpBand
      have hqHead := coprime_modulus_of_mem_primeBand H hHW hqBand
      have hyPos : 0 < yNat n :=
        (prime_of_mem_primeBand hpBand).pos.trans_le
          (le_yNat_of_mem_primeBand hpBand)
      have hzero : pairPower p q 0 0 ≤ yNat n ^ 4 := by
        simpa only [pairPower, pow_zero, mul_one] using
          (one_le_pow₀ (show 1 ≤ yNat n from hyPos))
      have hseed := hpairRaw η hnpair hpBand hqErase hzero
        hpHead hqHead hη
      refine ⟨hseed.1, ?_⟩
      intro hS u v hD4
      exact (hpairRaw η hnpair hpBand hqErase hD4
        hpHead hqHead hη).2 hS
    have hfallback :
        let S := structuredCell H (physicalBound A n) (physicalBound C n)
          (yNat n)
        ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
          (valuationTilt H (physicalBound A n) (physicalBound C n)
            (yNat n) hS (primeBand n W) η (L n)).probability.expect
              (fun m ↦ divInd D (m : ℕ)) ≤ Gf / (D : ℝ) := by
      simpa only using hfallbackRaw η hnfallback hη
    have hassembly := fullTilt_lemma75_bounds_of_uniform_inputs
      hkernel hCK.le H epsilon aux η hn hW hB (hε0 n)
      (show 0 ≤ pairFallbackDensity H A C by simpa only [c] using hc.le)
      (by simpa only [c, G₀] using hGn) hG₀.le hGf.le hcoef hpair
      hfallback hq₀Band hq₁Erase hauxn
      (by simpa only [actualExponentCutoff] using htailJIn)
      (by simpa only [actualExponentCutoff] using htailIJn)
      (by simpa only [actualExponentCutoff] using htailJJn)
      (by simpa only [actualExponentCutoff] using htailDn)
      (by simpa only [actualExponentCutoff] using htailn) hbandTn
    obtain ⟨hSnonempty, hbounds⟩ := hassembly
    refine ⟨hSnonempty, ?_⟩
    intro hS
    have hsmall := hbounds hS
    have hmono := hsmall.mono_epsilon
      (le_abs_self (rawRemainder n))
    simpa only [C_pow, epsilon_BW, rawRemainder] using hmono
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hfinal
  refine ⟨epsilon_BW, hrem0, hremT, N₀, ?_⟩
  intro n η hn hη
  exact hN₀ n hn η hη

end

end Erdos390.Full.PaperPrimePowerLemma75
