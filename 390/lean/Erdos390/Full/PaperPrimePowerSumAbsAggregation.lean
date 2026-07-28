import Erdos390.Full.PaperPrimePowerPairAggregation

/-!
# Sum-of-absolute-values prime-power aggregation

Paper Lemma 7.5 requires sums of absolute pointwise covariances.  These are
strictly stronger than the absolute value of the already-expanded `J`
covariance, so they are exported separately here.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerSumAbsAggregation

open ArithmeticModel
open FiniteProbability PrimePowerCovariance
open PrimePowerCutoffCovariance LocalFugacityBounds
open ValuationCutoff

noncomputable section

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}
  (law : BoundedValuationLaw Omega M)

/-- One-high aggregation with the sum of absolute covariances on the left. -/
theorem sum_abs_covJI_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq0 : 0 < q)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      |law.probability.covariance (law.Ip p r) (law.I q)| ≤
        K * (((r : ℝ) + 1) /
          ((p : ℝ) ^ r * (q : ℝ))) + e r) :
    (∑ r ∈ highExponents (valuationCutoff p M),
        |law.probability.covariance (law.Ip p r) (law.I q)|) ≤
      8 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) +
        ∑ r ∈ highExponents (valuationCutoff p M), e r := by
  calc
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
    _ = _ := by ring

/-- Transposed one-high aggregation with the sum of absolute covariances. -/
theorem sum_abs_covIJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp0 : 0 < p) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℝ)
    (hpoint : ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.I p) (law.Ip q s)| ≤
        K * (((s : ℝ) + 1) /
          ((p : ℝ) * (q : ℝ) ^ s)) + e s) :
    (∑ s ∈ highExponents (valuationCutoff q M),
        |law.probability.covariance (law.I p) (law.Ip q s)|) ≤
      8 * K * (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 +
        ∑ s ∈ highExponents (valuationCutoff q M), e s := by
  calc
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
    _ = _ := by ring

/-- Double-high aggregation with the literal double sum of absolute
covariances. -/
theorem sum_abs_covJJ_le_of_cutoff_pointwise
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    {K : ℝ} (hK : 0 ≤ K) (e : ℕ → ℕ → ℝ)
    (hpoint : ∀ r ∈ highExponents (valuationCutoff p M),
      ∀ s ∈ highExponents (valuationCutoff q M),
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        K * ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) + e r s) :
    (∑ r ∈ highExponents (valuationCutoff p M),
      ∑ s ∈ highExponents (valuationCutoff q M),
        |law.probability.covariance (law.Ip p r) (law.Ip q s)|) ≤
      64 * K * (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 +
        ∑ r ∈ highExponents (valuationCutoff p M),
          ∑ s ∈ highExponents (valuationCutoff q M), e r s := by
  calc
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
        _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
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
      apply add_le_add _ le_rfl
      calc
        _ ≤ K * (8 / (p : ℝ) ^ 2) *
            (∑ s ∈ highExponents (valuationCutoff q M),
              ((s : ℝ) + 1) / (q : ℝ) ^ s) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsumP hK) hSQ0
        _ ≤ K * (8 / (p : ℝ) ^ 2) * (8 / (q : ℝ) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hsumQ (mul_nonneg hK hAP0)
    _ = _ := by ring

end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerSumAbsAggregation
