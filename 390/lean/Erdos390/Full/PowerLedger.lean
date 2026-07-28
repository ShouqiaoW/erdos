import Erdos390.Full.ArithmeticModel

/-!
# Exact prime-power ledgers

The aggregate prime-power argument uses the pointwise identity
`J_p^2 = ∑_{r≥2} (2r-3) 1_{p^r∣m}`.  This file proves that identity
for the actual valuation and divisibility columns, with a common finite
physical cutoff.  Thus later expectation and covariance manipulations do not
need to treat it as a stylized fact.
-/

open scoped BigOperators

namespace Erdos390.Full.PowerLedger

open ArithmeticModel

private theorem sum_odd_Icc (a : ℕ) :
    (∑ r ∈ Finset.Icc 2 a, ((2 * r - 3 : ℕ) : ℝ)) =
      (((a - 1 : ℕ) : ℝ) ^ 2) := by
  induction a with
  | zero => simp
  | succ a ih =>
      by_cases ha : 1 ≤ a
      · rw [Finset.sum_Icc_succ_top (by omega), ih]
        have hodd : 2 * (a + 1) - 3 = 2 * a - 1 := by omega
        have h2a : 1 ≤ 2 * a := by omega
        rw [hodd, Nat.cast_sub h2a]
        norm_num [Nat.succ_eq_add_one, Nat.cast_sub ha]
        ring
      · have ha0 : a = 0 := by omega
        subst a
        norm_num

private theorem higherValuation_eq_cast_pred {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ((m.factorization p - 1 : ℕ) : ℝ) := by
  by_cases hdvd : p ∣ m
  · have hfac : 1 ≤ m.factorization p :=
      (hp.dvd_iff_one_le_factorization hm.ne').mp hdvd
    rw [higherValuation, valuation, divInd]
    simp only [if_pos hdvd]
    rw [Nat.cast_sub hfac]
    norm_num
  · have hfac : m.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hdvd
    simp [higherValuation, valuation, divInd, hdvd, hfac]

/-- The exact diagonal identity used in the proof of Lemma 7.5. -/
theorem higherValuation_sq_eq_weighted_sum_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m ^ 2 =
      ∑ r ∈ highExponents M,
        ((2 * r - 3 : ℕ) : ℝ) * divInd (p ^ r) m := by
  have hfacM : m.factorization p ≤ M := by
    exact (Nat.factorization_lt p hm.ne').le.trans hmM
  rw [higherValuation_eq_cast_pred hp hm]
  simp only [highExponents, divInd, hp.pow_dvd_iff_le_factorization hm.ne']
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 2 M).filter (fun r ↦ r ≤ m.factorization p) =
        Finset.Icc 2 (m.factorization p) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, sum_odd_Icc]

theorem higherValuation_sq_eq_weighted_sum {p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m ^ 2 =
      ∑ r ∈ highExponents m,
        ((2 * r - 3 : ℕ) : ℝ) * divInd (p ^ r) m :=
  higherValuation_sq_eq_weighted_sum_of_le hp hm le_rfl

theorem higherValuation_sq_eq_weighted_sum_physical {C : ℝ}
    {n p m : ℕ} (hp : p.Prime) (hm : 0 < m)
    (hmC : m ≤ physicalBound C n) :
    higherValuation p m ^ 2 =
      ∑ r ∈ highExponents (physicalBound C n),
        ((2 * r - 3 : ℕ) : ℝ) * divInd (p ^ r) m :=
  higherValuation_sq_eq_weighted_sum_of_le hp hm hmC

end Erdos390.Full.PowerLedger
