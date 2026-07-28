import Erdos390.Full.PrimePowerCovariance
import Erdos390.Full.ValuationCutoff

/-!
# Exact logarithmic cutoffs in the prime-power covariance expansion

`PrimePowerCovariance` expands the higher-valuation column using the common
physical endpoint.  The paper's local-factor analysis instead uses the exact
logarithmic cutoff `valuationCutoff p M`.  This file proves that the two finite
sums agree for every value in `(0,M]`, and consequently rewrites every actual
`JI`, `IJ`, `JJ`, and diagonal-moment expression at that logarithmic cutoff.

There is no asymptotic or probabilistic input here: the truncation follows
from the literal inequality

`factorization p m <= valuationCutoff p M`.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerCutoffCovariance

open ArithmeticModel PowerLedger ValuationCutoff
open FiniteProbability PrimePowerCovariance

noncomputable section

private theorem sum_divInd_high_eq_of_factorization_bounds
    {p m A B : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization p ≤ B) :
    (∑ k ∈ highExponents A, divInd (p ^ k) m) =
      ∑ k ∈ highExponents B, divInd (p ^ k) m := by
  simp only [highExponents, divInd,
    hp.pow_dvd_iff_le_factorization hm.ne']
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

private theorem sum_weighted_divInd_high_eq_of_factorization_bounds
    {p m A B : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization p ≤ B) :
    (∑ k ∈ highExponents A,
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m)) =
      ∑ k ∈ highExponents B,
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m) := by
  simp only [highExponents, divInd,
    hp.pow_dvd_iff_le_factorization hm.ne', mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- Exact higher-valuation expansion at the logarithmic cutoff. -/
theorem higherValuation_eq_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m =
      ∑ k ∈ highExponents (valuationCutoff p M), divInd (p ^ k) m := by
  rw [higherValuation_eq_sum_high_of_le hp hm hmM]
  exact sum_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)

/-- Exact diagonal square ledger at the logarithmic cutoff. -/
theorem higherValuation_sq_eq_weighted_sum_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m ^ 2 =
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) * divInd (p ^ k) m) := by
  rw [higherValuation_sq_eq_weighted_sum_of_le hp hm hmM]
  exact sum_weighted_divInd_high_eq_of_factorization_bounds hp hm
    ((Nat.factorization_lt p hm.ne').le.trans hmM)
    (factorization_le_valuationCutoff hp hm hmM)

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]

/-- Expectation commutes with an actual finite sum. -/
theorem expect_sum (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) :
    mu.expect (fun omega ↦ ∑ i ∈ s, F i omega) =
      ∑ i ∈ s, mu.expect (F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.expect_zero]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.expect_add, ih]

end FiniteProbability

variable {Omega : Type*} [Fintype Omega] {M : ℕ}

/-- The actual `J_p` column, cut off at `floor(log_p M)`. -/
theorem J_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    law.J p = fun omega ↦
      ∑ k ∈ highExponents (valuationCutoff p M), law.Ip p k omega := by
  funext omega
  exact higherValuation_eq_sum_valuationCutoff hp
    (law.value_pos omega) (law.value_le omega)

/-- `JI` as the literal finite sum at the exact logarithmic cutoff. -/
theorem covJI_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) (q : ℕ) :
    law.covJI p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        law.probability.covariance (law.Ip p k) (law.I q) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJI,
    J_eq_valuationCutoff_sum law hp,
    law.probability.covariance_sum_left]

/-- `IJ` as the transposed finite sum at the exact logarithmic cutoff. -/
theorem covIJ_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) (p : ℕ) {q : ℕ} (hq : q.Prime) :
    law.covIJ p q =
      ∑ k ∈ highExponents (valuationCutoff q M),
        law.probability.covariance (law.I p) (law.Ip q k) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covIJ,
    J_eq_valuationCutoff_sum law hq,
    law.probability.covariance_sum_right]

/-- `JJ` as the literal double sum at the two exact logarithmic cutoffs. -/
theorem covJJ_eq_valuationCutoff_sum
    (law : BoundedValuationLaw Omega M) {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) :
    law.covJJ p q =
      ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          law.probability.covariance (law.Ip p k) (law.Ip q l) := by
  rw [PrimePowerCovariance.BoundedValuationLaw.covJJ,
    J_eq_valuationCutoff_sum law hp,
    J_eq_valuationCutoff_sum law hq,
    law.probability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.covariance_sum_right]

/-- Pointwise diagonal square identity at the exact logarithmic cutoff. -/
theorem J_sq_eq_valuationCutoff_weighted_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    (fun omega ↦ law.J p omega ^ 2) = fun omega ↦
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) * law.Ip p k omega) := by
  funext omega
  exact higherValuation_sq_eq_weighted_sum_valuationCutoff hp
    (law.value_pos omega) (law.value_le omega)

/-- Expected diagonal square as the exact weighted prime-power sum. -/
theorem expect_J_sq_eq_valuationCutoff_weighted_sum
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) =
      ∑ k ∈ highExponents (valuationCutoff p M),
        (((2 * k - 3 : ℕ) : ℝ) *
          law.probability.expect (law.Ip p k)) := by
  rw [J_sq_eq_valuationCutoff_weighted_sum law hp,
    FiniteProbability.expect_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.expect_smul]

end

end Erdos390.Full.PrimePowerCutoffCovariance
