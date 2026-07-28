import Erdos390.Full.PaperPrimePowerLemma75

/-!
# Generic finite aggregation for the five conclusions of Lemma 7.5

This module separates the finite prime-power summation from the source of
the pointwise estimates.  It can therefore be applied both to one
structured cell and to a tagged fixed finite mixture.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerGenericAggregation

open ArithmeticModel Scale
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerChamberError PaperPrimePowerPairAggregation
open PaperPrimePowerSumAbsAggregation PaperPrimePowerRow
open PaperPrimePowerLemma75 PaperValuationCutoff
open ValuationCutoff PrimeSums LocalFugacityBounds

noncomputable section

/-- A single nonnegative error large enough for all three product-weighted
sums, the diagonal square, and the row estimate. -/
def genericAggregationRemainder
    (E Tlin Tquad Tdiag Trow : ℝ) (n W : ℕ) : ℝ :=
  pairAggregationConstant * E + Tlin + Tquad + Tdiag +
    pairAggregationConstant * E *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) + Trow

theorem genericAggregationRemainder_nonneg
    {E Tlin Tquad Tdiag Trow : ℝ} {n W : ℕ}
    (hE : 0 ≤ E) (hTlin : 0 ≤ Tlin) (hTquad : 0 ≤ Tquad)
    (hTdiag : 0 ≤ Tdiag) (hTrow : 0 ≤ Trow) :
    0 ≤ genericAggregationRemainder E Tlin Tquad Tdiag Trow n W := by
  unfold genericAggregationRemainder
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hpairE : 0 ≤ pairAggregationConstant * E :=
    mul_nonneg pairAggregationConstant_nonneg hE
  have hrowTerm : 0 ≤ pairAggregationConstant * E *
      (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by
    exact mul_nonneg
      (mul_nonneg hpairE (by linarith)) (by positivity)
  linarith

/-- Finite aggregation from four pointwise bounds and their residual
majorants.  The same remainder occurs in all five conclusions. -/
theorem primePowerTransferBounds_of_pointwise
    {Omega : Type*} [Fintype Omega] {M n W : ℕ}
    (law : BoundedValuationLaw Omega M)
    {Cmain E Tlin Tquad Tdiag Trow : ℝ}
    {eJI eIJ : ℕ → ℕ → ℕ → ℝ}
    {eJJ : ℕ → ℕ → ℕ → ℕ → ℝ}
    {eD : ℕ → ℕ → ℝ}
    (hn : 1 < n) (hW : 1 < W)
    (hCmain : 0 ≤ Cmain) (hE : 0 ≤ E)
    (hTlin : 0 ≤ Tlin) (hTquad : 0 ≤ Tquad)
    (hTdiag : 0 ≤ Tdiag) (hTrow : 0 ≤ Trow)
    (hJIpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        (Cmain * tPrime n p * tPrime n q + E) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) + eJI p q r)
    (hIJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        (Cmain * tPrime n p * tPrime n q + E) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) + eIJ p q s)
    (hJJpoint : ∀ p ∈ primeBand n W,
      ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (Cmain * tPrime n p * tPrime n q + E) *
          ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s)) + eJJ p q r s)
    (hDpoint : ∀ p ∈ primeBand n W,
      ∀ r ∈ highExponents (valuationCutoff p M),
      law.probability.expect (law.Ip p r) ≤
        (Cmain + E) * (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD p r)
    (htailJI : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M), eJI p q r) ≤
        Tlin * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)))
    (htailIJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s) ≤
        Tlin * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2)
    (htailJJ : ∀ p ∈ primeBand n W, ∀ q ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        ∑ s ∈ highExponents (valuationCutoff q M), eJJ p q r s) ≤
          Tquad * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2)
    (htailD : ∀ p ∈ primeBand n W,
      (∑ r ∈ highExponents (valuationCutoff p M),
        (((2 * r - 3 : ℕ) : ℝ) * eD p r)) ≤
          Tdiag * (1 / (p : ℝ)) ^ 2)
    (htailRow : ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            (((∑ r ∈ highExponents (valuationCutoff p M), eJI p q r)) +
              (∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s) +
              (∑ r ∈ highExponents (valuationCutoff p M),
                ∑ s ∈ highExponents (valuationCutoff q M), eJJ p q r s))) +
          3 * (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * eD p r))) ≤ Trow)
    (hbandT : bandTReciprocalSum n W ≤ 2 * Real.log 4) :
    PrimePowerTransferBounds law n W
      (pairAggregationConstant * Cmain * (2 * Real.log 4 + 5))
      (genericAggregationRemainder E Tlin Tquad Tdiag Trow n W) := by
  let Cpow := pairAggregationConstant * Cmain * (2 * Real.log 4 + 5)
  let R := genericAggregationRemainder E Tlin Tquad Tdiag Trow n W
  have hpairE : 0 ≤ pairAggregationConstant * E :=
    mul_nonneg pairAggregationConstant_nonneg hE
  have hband : 0 ≤ bandReciprocalSum n W := by
    unfold bandReciprocalSum
    positivity
  have hR : 0 ≤ R := genericAggregationRemainder_nonneg hE hTlin hTquad
    hTdiag hTrow
  have hCfactor : (1 : ℝ) ≤ 2 * Real.log 4 + 5 := by
    have hlog : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    linarith
  have hCscale : pairAggregationConstant * Cmain ≤ Cpow := by
    dsimp only [Cpow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hCfactor
      (mul_nonneg pairAggregationConstant_nonneg hCmain)
  have hELinear : pairAggregationConstant * E + Tlin ≤ R := by
    dsimp only [R]
    unfold genericAggregationRemainder
    have hrowTerm : 0 ≤ pairAggregationConstant * E *
        (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by positivity
    linarith
  have hEQuad : pairAggregationConstant * E + Tquad ≤ R := by
    dsimp only [R]
    unfold genericAggregationRemainder
    have hrowTerm : 0 ≤ pairAggregationConstant * E *
        (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by positivity
    linarith
  have hEDiag : pairAggregationConstant * E + Tdiag ≤ R := by
    dsimp only [R]
    unfold genericAggregationRemainder
    have hrowTerm : 0 ≤ pairAggregationConstant * E *
        (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) := by positivity
    linarith
  have hrow :=
    Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.paperBand_row_le_of_cutoff_pointwise
      law hn hW Cmain E Trow eJI eIJ eJJ eD hCmain hE
        hJIpoint hIJpoint hJJpoint hDpoint htailRow
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
    let K₀ := Cmain * tPrime n p * tPrime n q + E
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg (mul_nonneg hCmain
          (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covJI_le_of_cutoff_pointwise
        law hp hq.pos hK₀ (eJI p q) (hJIpoint p hpBand q hqErase)
    have h8 : 8 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 (by positivity)) (by positivity))
      (htailJI p hpBand q hqBand))
    have hmainScaled := mul_le_mul_of_nonneg_right hCscale
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + Tlin ≤
        Cpow * tPrime n p * tPrime n q + R := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hELinear]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) +
          Tlin * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := hraw
      _ = (pairAggregationConstant * K₀ + Tlin) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := Cmain * tPrime n p * tPrime n q + E
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg (mul_nonneg hCmain
          (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covIJ_le_of_cutoff_pointwise
        law hp.pos hq hK₀ (eIJ p q) (hIJpoint p hpBand q hqErase)
    have h8 : 8 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 (by positivity)) (by positivity))
      (htailIJ p hpBand q hqBand))
    have hmainScaled := mul_le_mul_of_nonneg_right hCscale
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + Tlin ≤
        Cpow * tPrime n p * tPrime n q + R := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hELinear]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 +
          Tlin * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ + Tlin) *
          (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hp := prime_of_mem_primeBand hpBand
    have hq := prime_of_mem_primeBand hqBand
    let K₀ := Cmain * tPrime n p * tPrime n q + E
    have hK₀ : 0 ≤ K₀ := by
      dsimp only [K₀]
      exact add_nonneg
        (mul_nonneg (mul_nonneg hCmain
          (tPrime_nonneg_of_mem_primeBand hn hpBand))
          (tPrime_nonneg_of_mem_primeBand hn hqBand)) hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerSumAbsAggregation.BoundedValuationLaw.sum_abs_covJJ_le_of_cutoff_pointwise
        law hp hq hK₀ (eJJ p q) (hJJpoint p hpBand q hqErase)
    have h64 : 64 * K₀ ≤ pairAggregationConstant * K₀ :=
      mul_le_mul_of_nonneg_right sixtyFour_le_pairAggregationConstant hK₀
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h64 (by positivity)) (by positivity))
      (htailJJ p hpBand q hqBand))
    have hmainScaled := mul_le_mul_of_nonneg_right hCscale
      (mul_nonneg (tPrime_nonneg_of_mem_primeBand hn hpBand)
        (tPrime_nonneg_of_mem_primeBand hn hqBand))
    have hcoef : pairAggregationConstant * K₀ + Tquad ≤
        Cpow * tPrime n p * tPrime n q + R := by
      dsimp only [K₀]
      nlinarith [hmainScaled, hEQuad]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) ^ 2 +
          Tquad * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ + Tquad) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand
    have hp := prime_of_mem_primeBand hpBand
    let K₀ := Cmain + E
    have hK₀ : 0 ≤ K₀ := add_nonneg hCmain hE
    have hagg :=
      Erdos390.Full.PaperPrimePowerPairAggregation.BoundedValuationLaw.expect_J_sq_le_of_cutoff_pointwise
        law hp hK₀ (eD p) (hDpoint p hpBand)
    have hquad : K₀ * quadraticHalfMass ≤ pairAggregationConstant * K₀ := by
      simpa only [mul_comm] using
        (mul_le_mul_of_nonneg_left
          quadraticHalfMass_le_pairAggregationConstant hK₀)
    have hraw := hagg.trans (add_le_add
      (mul_le_mul_of_nonneg_right hquad (by positivity))
      (htailD p hpBand))
    have hcoef : pairAggregationConstant * K₀ + Tdiag ≤ Cpow + R := by
      dsimp only [K₀]
      nlinarith [hCscale, hEDiag]
    calc
      _ ≤ pairAggregationConstant * K₀ * (1 / (p : ℝ)) ^ 2 +
          Tdiag * (1 / (p : ℝ)) ^ 2 := hraw
      _ = (pairAggregationConstant * K₀ + Tdiag) *
          (1 / (p : ℝ)) ^ 2 := by ring
      _ ≤ _ := by gcongr
  · intro p hpBand
    have hpRow := hrow p hpBand
    have hmainCoeff : 0 ≤ pairAggregationConstant * Cmain :=
      mul_nonneg pairAggregationConstant_nonneg hCmain
    have hfirst :
        (pairAggregationConstant * Cmain) *
            (bandTReciprocalSum n W + 5) * (1 / (W : ℝ)) ≤
          Cpow * (1 / (W : ℝ)) := by
      have hWinv : 0 ≤ 1 / (W : ℝ) := by positivity
      have hfactor : bandTReciprocalSum n W + 5 ≤
          2 * Real.log 4 + 5 := by linarith
      dsimp only [Cpow]
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor hmainCoeff) hWinv
    have hrowError :
        pairAggregationConstant * E * (bandReciprocalSum n W + 5) *
              (1 / (W : ℝ)) + Trow ≤ R := by
      dsimp only [R]
      unfold genericAggregationRemainder
      linarith
    calc
      _ ≤ (pairAggregationConstant * Cmain) *
              (bandTReciprocalSum n W + 5) * (1 / (W : ℝ)) +
            pairAggregationConstant * E *
                (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) + Trow :=
        hpRow
      _ ≤ Cpow * (1 / (W : ℝ)) + R := by linarith

end

end Erdos390.Full.PaperPrimePowerGenericAggregation
