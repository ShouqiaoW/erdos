import Erdos390.Full.PrimePowerCutoffCovariance
import Erdos390.Full.PaperPrimePowerRow
import Erdos390.Full.LocalFugacityBounds

/-!
# From actual prime-power pairs to a paper prime row

This file performs the finite aggregation that follows the pointwise
two-local estimates in Lemma 7.5.  Its inputs are covariances and moments of
the genuine divisor-indicator columns of an actual `BoundedValuationLaw`.
The preceding logarithmic-cutoff module makes every exponent range literal.

The factors `8`, `64`, and `quadraticHalfMass` are obtained from the proved
geometric series, rather than hidden in an `O`-constant.  A single universal
aggregation constant then feeds the already formalized paper-band row
contraction.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerPairAggregation

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff
open PrimeSums
open PaperPrimePowerRow

noncomputable section

/-- One constant dominating all four finite geometric aggregations. -/
def pairAggregationConstant : ℝ := 64 + quadraticHalfMass

lemma pairAggregationConstant_nonneg : 0 ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  exact add_nonneg (by norm_num) quadraticHalfMass_nonneg

lemma eight_le_pairAggregationConstant : (8 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  nlinarith [quadraticHalfMass_nonneg]

lemma sixtyFour_le_pairAggregationConstant :
    (64 : ℝ) ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  linarith [quadraticHalfMass_nonneg]

lemma quadraticHalfMass_le_pairAggregationConstant :
    quadraticHalfMass ≤ pairAggregationConstant := by
  unfold pairAggregationConstant
  norm_num

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)

/-- A pointwise `JI` estimate contracts to the exact `p^{-2}q^{-1}` scale.
The residual remains a literal finite sum. -/
theorem abs_covJI_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq0 : 0 < q)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        K * (((r : ℝ) + 1) /
          ((p : ℝ) ^ r * (q : ℝ))) + e r) :
    |law.covJI p q| ≤
      8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
        ∑ r ∈ highExponents (valuationCutoff p M), e r := by
  rw [covJI_eq_valuationCutoff_sum law hp]
  calc
    |∑ r ∈ highExponents (valuationCutoff p M),
        law.probability.covariance (law.Ip p r) (law.I q)| ≤
        ∑ r ∈ highExponents (valuationCutoff p M),
          |law.probability.covariance (law.Ip p r) (law.I q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ highExponents (valuationCutoff p M),
          (K * (((r : ℝ) + 1) /
            ((p : ℝ) ^ r * (q : ℝ))) + e r) := by
      exact Finset.sum_le_sum fun r hr ↦ hpoint r hr
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            ((r : ℝ) + 1) / (p : ℝ) ^ r) * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ K * (8 / (p : ℝ) ^ 2) * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      gcongr
      exact sum_raddone_inv_pow_le hp.two_le
    _ = 8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
          ∑ r ∈ highExponents (valuationCutoff p M), e r := by
      ring

/-- The transposed one-high aggregation. -/
theorem abs_covIJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp0 : 0 < p) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        K * (((s : ℝ) + 1) /
          ((p : ℝ) * (q : ℝ) ^ s)) + e s) :
    |law.covIJ p q| ≤
      8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
        ∑ s ∈ highExponents (valuationCutoff q M), e s := by
  rw [covIJ_eq_valuationCutoff_sum law p hq]
  calc
    |∑ s ∈ highExponents (valuationCutoff q M),
        law.probability.covariance (law.I p) (law.Ip q s)| ≤
        ∑ s ∈ highExponents (valuationCutoff q M),
          |law.probability.covariance (law.I p) (law.Ip q s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s ∈ highExponents (valuationCutoff q M),
          (K * (((s : ℝ) + 1) /
            ((p : ℝ) * (q : ℝ) ^ s)) + e s) := by
      exact Finset.sum_le_sum fun s hs ↦ hpoint s hs
    _ = K * (1 / (p : ℝ)) *
          (∑ s ∈ highExponents (valuationCutoff q M),
            ((s : ℝ) + 1) / (q : ℝ) ^ s) +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ K * (1 / (p : ℝ)) * (8 / (q : ℝ) ^ 2) +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      gcongr
      exact sum_raddone_inv_pow_le hq.two_le
    _ = 8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
          ∑ s ∈ highExponents (valuationCutoff q M), e s := by
      ring

/-- The genuine double-high covariance contracts to `p^{-2}q^{-2}`. -/
theorem abs_covJJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) + e r s) :
    |law.covJJ p q| ≤
      64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
        ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
  rw [covJJ_eq_valuationCutoff_sum law hp hq]
  calc
    |∑ r ∈ highExponents (valuationCutoff p M),
        ∑ s ∈ highExponents (valuationCutoff q M),
          law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M),
            |law.probability.covariance (law.Ip p r) (law.Ip q s)| := by
      calc
        _ ≤ ∑ r ∈ highExponents (valuationCutoff p M),
            |∑ s ∈ highExponents (valuationCutoff q M),
              law.probability.covariance (law.Ip p r) (law.Ip q s)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro r hr
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M),
            (K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
              ((p : ℝ) ^ r * (q : ℝ) ^ s)) + e r s) := by
      apply Finset.sum_le_sum
      intro r hr
      exact Finset.sum_le_sum fun s hs ↦ hpoint r hr s hs
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            ((r : ℝ) + 1) / (p : ℝ) ^ r) *
          (∑ s ∈ highExponents (valuationCutoff q M),
            ((s : ℝ) + 1) / (q : ℝ) ^ s) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
      simp_rw [Finset.sum_add_distrib]
      congr 1
      calc
        (∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M),
              K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
                ((p : ℝ) ^ r * (q : ℝ) ^ s))) =
            ∑ r ∈ highExponents (valuationCutoff p M),
              (K * (((r : ℝ) + 1) / (p : ℝ) ^ r)) *
                (∑ s ∈ highExponents (valuationCutoff q M),
                  ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          ring
        _ = K *
            (∑ r ∈ highExponents (valuationCutoff p M),
              ((r : ℝ) + 1) / (p : ℝ) ^ r) *
            (∑ s ∈ highExponents (valuationCutoff q M),
              ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
      have hsumP := sum_raddone_inv_pow_le
        (R := valuationCutoff p M) hp.two_le
      have hsumQ := sum_raddone_inv_pow_le
        (R := valuationCutoff q M) hq.two_le
      have hSP0 : 0 ≤ ∑ r ∈ highExponents (valuationCutoff p M),
          ((r : ℝ) + 1) / (p : ℝ) ^ r := by positivity
      have hSQ0 : 0 ≤ ∑ s ∈ highExponents (valuationCutoff q M),
          ((s : ℝ) + 1) / (q : ℝ) ^ s := by positivity
      have hAP0 : 0 ≤ 8 / (p : ℝ) ^ 2 := by positivity
      have hmain :
          K * (∑ r ∈ highExponents (valuationCutoff p M),
              ((r : ℝ) + 1) / (p : ℝ) ^ r) *
              (∑ s ∈ highExponents (valuationCutoff q M),
                ((s : ℝ) + 1) / (q : ℝ) ^ s) ≤
            K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) := by
        calc
          _ ≤ K * (8 / (p : ℝ) ^ 2) *
              (∑ s ∈ highExponents (valuationCutoff q M),
                ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsumP hK) hSQ0
          _ ≤ K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) := by
            exact mul_le_mul_of_nonneg_left hsumQ (mul_nonneg hK hAP0)
      exact add_le_add hmain le_rfl
    _ = 64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
          ∑ r ∈ highExponents (valuationCutoff p M),
            ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
      ring

/-- The exact diagonal square ledger contracts with its literal odd weight. -/
theorem expect_J_sq_le_of_cutoff_pointwise
    {p : ℕ} (hp : p.Prime) {K : ℝ} (hK : 0 ≤ K)
    (e : ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      law.probability.expect (law.Ip p r) ≤
        K * (((r : ℝ) + 1) / (p : ℝ) ^ r) + e r) :
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
      K * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        ∑ r ∈ highExponents (valuationCutoff p M),
          (((2 * r - 3 : ℕ) : ℝ) * e r) := by
  rw [expect_J_sq_eq_valuationCutoff_weighted_sum law hp]
  calc
    (∑ r ∈ highExponents (valuationCutoff p M),
        (((2 * r - 3 : ℕ) : ℝ) *
          law.probability.expect (law.Ip p r))) ≤
        ∑ r ∈ highExponents (valuationCutoff p M),
          (((2 * r - 3 : ℕ) : ℝ) *
            (K * (((r : ℝ) + 1) / (p : ℝ) ^ r) + e r)) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hpoint r hr) (by positivity)
    _ = K *
          (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) *
              (((r : ℝ) + 1) / (p : ℝ) ^ r))) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      calc
        _ = ∑ r ∈ highExponents (valuationCutoff p M),
              (K * (((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r)) +
                (((2 * r - 3 : ℕ) : ℝ) * e r)) := by
          apply Finset.sum_congr rfl
          intro r hr
          ring
        _ = (∑ r ∈ highExponents (valuationCutoff p M),
              K * (((2 * r - 3 : ℕ) : ℝ) *
                (((r : ℝ) + 1) / (p : ℝ) ^ r))) +
              ∑ r ∈ highExponents (valuationCutoff p M),
                (((2 * r - 3 : ℕ) : ℝ) * e r) :=
          Finset.sum_add_distrib
        _ = _ := by rw [Finset.mul_sum]
    _ ≤ K * (quadraticHalfMass / (p : ℝ) ^ 2) +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      gcongr
      exact sum_diagonalWeight_raddone_inv_pow_le hp.two_le
    _ = K * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
          ∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * e r) := by
      ring

set_option maxHeartbeats 1200000 in
/-- **Actual pointwise-to-row wiring for the paper band.**

The four pointwise hypotheses concern the genuine divisor-indicator columns
of `law` and the exact logarithmic cutoffs.  After the finite geometric
aggregation, this theorem invokes the paper-band row contraction and returns
the full-valuation covariance row required by Lemma 7.5. -/
theorem paperBand_row_le_of_cutoff_pointwise
    {n W : ℕ} (hn : 1 < n) (hW : 1 < W)
    (A epsilon remRow : ℝ)
    (eJI eIJ : ℕ → ℕ → ℕ → ℝ)
    (eJJ : ℕ → ℕ → ℕ → ℕ → ℝ)
    (eD : ℕ → ℕ → ℝ)
    (hA : 0 ≤ A) (hepsilon : 0 ≤ epsilon)
    (hJI : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        (A * tPrime n p * tPrime n q + epsilon) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) + eJI p q r)
    (hIJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        (A * tPrime n p * tPrime n q + epsilon) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) + eIJ p q s)
    (hJJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (A * tPrime n p * tPrime n q + epsilon) *
          ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s)) + eJJ p q r s)
    (hD : ∀ p ∈ primeBand n W,
      ∀ r ∈ highExponents (valuationCutoff p M),
      law.probability.expect (law.Ip p r) ≤
        (A + epsilon) * (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD p r)
    (hRowRem : ∀ p ∈ primeBand n W,
      (p : ℝ) *
        ((∑ q ∈ (primeBand n W).erase p,
            ((∑ r ∈ highExponents (valuationCutoff p M), eJI p q r) +
              (∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s) +
              (∑ r ∈ highExponents (valuationCutoff p M),
                ∑ s ∈ highExponents (valuationCutoff q M),
                  eJJ p q r s))) +
          3 * (∑ r ∈ highExponents (valuationCutoff p M),
            (((2 * r - 3 : ℕ) : ℝ) * eD p r))) ≤ remRow) :
    ∀ p ∈ primeBand n W,
      (p : ℝ) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| ≤
      (pairAggregationConstant * A) * (bandTReciprocalSum n W + 5) *
          (1 / (W : ℝ)) +
        (pairAggregationConstant * epsilon) *
          (bandReciprocalSum n W + 5) * (1 / (W : ℝ)) + remRow := by
  let rJI : ℕ → ℕ → ℝ := fun p q ↦
    ∑ r ∈ highExponents (valuationCutoff p M), eJI p q r
  let rIJ : ℕ → ℕ → ℝ := fun p q ↦
    ∑ s ∈ highExponents (valuationCutoff q M), eIJ p q s
  let rJJ : ℕ → ℕ → ℝ := fun p q ↦
    ∑ r ∈ highExponents (valuationCutoff p M),
      ∑ s ∈ highExponents (valuationCutoff q M), eJJ p q r s
  let rD : ℕ → ℝ := fun p ↦
    ∑ r ∈ highExponents (valuationCutoff p M),
      (((2 * r - 3 : ℕ) : ℝ) * eD p r)
  apply PaperPrimePowerRow.BoundedValuationLaw.paperBand_covVV_sub_covII_row_le
    law hn hW (pairAggregationConstant * A)
      (pairAggregationConstant * epsilon) remRow rJI rIJ rJJ rD
      (mul_nonneg pairAggregationConstant_nonneg hA)
      (mul_nonneg pairAggregationConstant_nonneg hepsilon)
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hpPrime := prime_of_mem_primeBand hpBand
    have hqPrime := prime_of_mem_primeBand hqBand
    have htp := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
    have htq := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
    let K : ℝ := A * tPrime n p * tPrime n q + epsilon
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hagg := abs_covJI_le_of_cutoff_pointwise law hpPrime hqPrime.pos
      hK (eJI p q) (hJI p hpBand q hqErase)
    have hcoef : 8 * K ≤ pairAggregationConstant * K :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK
    calc
      |law.covJI p q| ≤
          8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) + rJI p q :=
        hagg
      _ ≤ pairAggregationConstant * K * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) + rJI p q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) le_rfl
      _ = (pairAggregationConstant * A) * tPrime n p * tPrime n q *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
          (pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) + rJI p q := by
        dsimp only [K]
        ring
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hpPrime := prime_of_mem_primeBand hpBand
    have hqPrime := prime_of_mem_primeBand hqBand
    have htp := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
    have htq := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
    let K : ℝ := A * tPrime n p * tPrime n q + epsilon
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hagg := abs_covIJ_le_of_cutoff_pointwise law hpPrime.pos hqPrime
      hK (eIJ p q) (hIJ p hpBand q hqErase)
    have hcoef : 8 * K ≤ pairAggregationConstant * K :=
      mul_le_mul_of_nonneg_right eight_le_pairAggregationConstant hK
    calc
      |law.covIJ p q| ≤
          8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 + rIJ p q :=
        hagg
      _ ≤ pairAggregationConstant * K * (1 / (p : ℝ)) *
            (1 / (q : ℝ)) ^ 2 + rIJ p q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) le_rfl
      _ = (pairAggregationConstant * A) * tPrime n p * tPrime n q *
            (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
          (pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 + rIJ p q := by
        dsimp only [K]
        ring
  · intro p hpBand q hqErase
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
    have hpPrime := prime_of_mem_primeBand hpBand
    have hqPrime := prime_of_mem_primeBand hqBand
    have htp := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
    have htq := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
    let K : ℝ := A * tPrime n p * tPrime n q + epsilon
    have hK : 0 ≤ K := by
      dsimp only [K]
      positivity
    have hagg := abs_covJJ_le_of_cutoff_pointwise law hpPrime hqPrime
      hK (eJJ p q) (hJJ p hpBand q hqErase)
    have hcoef : 64 * K ≤ pairAggregationConstant * K :=
      mul_le_mul_of_nonneg_right sixtyFour_le_pairAggregationConstant hK
    calc
      |law.covJJ p q| ≤
          64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 + rJJ p q :=
        hagg
      _ ≤ pairAggregationConstant * K * (1 / (p : ℝ)) ^ 2 *
            (1 / (q : ℝ)) ^ 2 + rJJ p q := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef (by positivity))
            (by positivity)) le_rfl
      _ = (pairAggregationConstant * A) * tPrime n p * tPrime n q *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
          (pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 + rJJ p q := by
        dsimp only [K]
        ring
  · intro p hpBand
    have hpPrime := prime_of_mem_primeBand hpBand
    have hK : 0 ≤ A + epsilon := add_nonneg hA hepsilon
    have hagg := expect_J_sq_le_of_cutoff_pointwise law hpPrime hK
      (eD p) (hD p hpBand)
    have hcoef : (A + epsilon) * quadraticHalfMass ≤
        (A + epsilon) * pairAggregationConstant :=
      mul_le_mul_of_nonneg_left quadraticHalfMass_le_pairAggregationConstant hK
    have hscale : 0 ≤ (1 / (p : ℝ)) ^ 2 := by positivity
    calc
      law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
          (A + epsilon) * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 + rD p :=
        hagg
      _ ≤ (A + epsilon) * pairAggregationConstant *
            (1 / (p : ℝ)) ^ 2 + rD p := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hcoef hscale) le_rfl
      _ = (pairAggregationConstant * A +
            pairAggregationConstant * epsilon) *
            (1 / (p : ℝ)) ^ 2 + rD p := by ring
  · intro p hpBand
    simpa only [rJI, rIJ, rJJ, rD] using hRowRem p hpBand

end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerPairAggregation
