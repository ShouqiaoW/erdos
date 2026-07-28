import Erdos390.WholePaper.ExceptionalValuationSums

/-! # Statement audit for the elementary finite valuation sums -/

open scoped BigOperators

namespace Erdos390.WholePaper

example (p B : ℕ) :
    valuationPrefixReal p B =
      ∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ) := rfl

example (p : ℕ) : valuationPrefixReal p 0 = 0 :=
  valuationPrefixReal_zero p

example (p B : ℕ) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) =
      B.factorial.factorization p :=
  sum_factorization_Icc_eq_factorialFactorization p B

example {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) ≤ B / (p - 1) :=
  sum_factorization_Icc_le_div_pred hp

example {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) :=
  sum_factorization_Icc_cast_le_div_pred hp

example (p B : ℕ) :
    valuationPrefixReal p B = (B.factorial.factorization p : ℝ) :=
  valuationPrefixReal_eq_factorialFactorization p B

example {p B : ℕ} (hp : p.Prime) :
    valuationPrefixReal p B ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) :=
  valuationPrefixReal_le_div_pred hp

example (p B : ℕ) :
    (∑ b ∈ Finset.range (B + 1), (b.factorization p : ℝ)) =
      valuationPrefixReal p B :=
  sum_range_succ_factorization_cast_eq_valuationPrefixReal p B

example {p B : ℕ} (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (1 / (b : ℝ)) * (b.factorization p : ℝ)) =
      (1 / (B : ℝ)) * valuationPrefixReal p B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b :=
  weightedFactorizationSum_eq_abel hB

example {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      (1 + Real.log (B : ℝ)) / ((p - 1 : ℕ) : ℝ) :=
  weightedFactorizationSum_le_one_add_log_div_pred hp hB

example {p : ℕ} (hp : p.Prime) :
    1 / ((p - 1 : ℕ) : ℝ) ≤ 2 / (p : ℝ) :=
  one_div_prime_pred_le_two_div_prime hp

example {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      2 * (B : ℝ) / (p : ℝ) :=
  sum_factorization_Icc_cast_le_two_mul_div_prime hp

example {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      2 * (1 + Real.log (B : ℝ)) / (p : ℝ) :=
  weightedFactorizationSum_le_two_mul_one_add_log_div_prime hp hB

end Erdos390.WholePaper
