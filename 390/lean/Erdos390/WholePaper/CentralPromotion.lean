import Erdos390.WholePaper.TailValuationCore

/-! # Promotion of residual central prime powers

This file formalizes the elementary promotion step from Section 10 of the
paper.  A positive block `B ≤ 2n` is multiplied by the least power of two
which puts it above `n`; the resulting block still lies at most `2n`.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The least exponent `k` for which `n < 2^k * B`, written using the
ceiling logarithm.  The intended use has `0 < B`. -/
def promotionExponent (n B : ℕ) : ℕ :=
  Nat.clog 2 (n / B + 1)

/-- A block promoted into the central interval by a power of two. -/
def promotedBlock (n B : ℕ) : ℕ :=
  2 ^ promotionExponent n B * B

theorem promotionExponent_spec {n B : ℕ} (hB : 0 < B) :
    n < 2 ^ promotionExponent n B * B := by
  have htarget : n / B + 1 ≤ 2 ^ promotionExponent n B := by
    simpa only [promotionExponent] using
      Nat.le_pow_clog Nat.one_lt_two (n / B + 1)
  apply (Nat.div_lt_iff_lt_mul hB).mp
  omega

theorem promotionExponent_minimal {n B k : ℕ}
    (hk : k < promotionExponent n B) :
    2 ^ k * B ≤ n := by
  have hpow : 2 ^ k < n / B + 1 := by
    exact (Nat.lt_clog_iff_pow_lt Nat.one_lt_two).mp hk
  have hpow' : 2 ^ k ≤ n / B := by omega
  exact (Nat.mul_le_mul_right B hpow').trans (Nat.div_mul_le_self n B)

theorem promotedBlock_gt {n B : ℕ} (hB : 0 < B) :
    n < promotedBlock n B := by
  exact promotionExponent_spec hB

theorem promotedBlock_le_two_mul {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ≤ 2 * n := by
  by_cases hBn : B ≤ n
  · have hdivPos : 0 < n / B := Nat.div_pos hBn hB
    have htarget : 1 < n / B + 1 := by omega
    have hkPos : 0 < promotionExponent n B := by
      simpa only [promotionExponent] using
        Nat.clog_pos Nat.one_lt_two htarget
    have hkPred : promotionExponent n B - 1 < promotionExponent n B := by
      omega
    have hprevious : 2 ^ (promotionExponent n B - 1) * B ≤ n :=
      promotionExponent_minimal hkPred
    have hkSplit : promotionExponent n B - 1 + 1 = promotionExponent n B := by
      omega
    rw [promotedBlock, ← hkSplit, pow_succ]
    calc
      (2 ^ (promotionExponent n B - 1) * 2) * B =
          2 * (2 ^ (promotionExponent n B - 1) * B) := by ac_rfl
      _ ≤ 2 * n := Nat.mul_le_mul_left 2 hprevious
  · have hnB : n < B := Nat.lt_of_not_ge hBn
    have hdiv : n / B = 0 := Nat.div_eq_of_lt hnB
    simp [promotedBlock, promotionExponent, hdiv, hBupper]

theorem promotedBlock_mem_centralInterval {n B : ℕ}
    (hB : 0 < B) (hBupper : B ≤ 2 * n) :
    promotedBlock n B ∈ Finset.Ioc n (2 * n) := by
  exact Finset.mem_Ioc.mpr
    ⟨promotedBlock_gt hB, promotedBlock_le_two_mul hB hBupper⟩

/-- The paper's pointwise promotion-cost estimate in integer-log form. -/
theorem promotionExponent_le_one_add_log2 {n B p : ℕ}
    (hp : 0 < p) (hpB : p ≤ B) :
    promotionExponent n B ≤ 1 + Nat.log2 (n / p) := by
  by_cases hkZero : promotionExponent n B = 0
  · omega
  · have hkPos : 0 < promotionExponent n B := Nat.pos_of_ne_zero hkZero
    have hkPred : promotionExponent n B - 1 < promotionExponent n B := by
      omega
    have hprevious : 2 ^ (promotionExponent n B - 1) * B ≤ n :=
      promotionExponent_minimal hkPred
    have hpPrevious : 2 ^ (promotionExponent n B - 1) * p ≤ n :=
      (Nat.mul_le_mul_left (2 ^ (promotionExponent n B - 1)) hpB).trans
        hprevious
    have hpowDiv : 2 ^ (promotionExponent n B - 1) ≤ n / p :=
      (Nat.le_div_iff_mul_le hp).2 hpPrevious
    have hlog :
        promotionExponent n B - 1 ≤ Nat.log 2 (n / p) :=
      Nat.le_log_of_pow_le Nat.one_lt_two hpowDiv
    rw [Nat.log2_eq_log_two]
    omega

/-- The full `p`-primary block in the central binomial coefficient. -/
def centralPrimeBlock (n p : ℕ) : ℕ :=
  p ^ (Nat.choose (2 * n) n).factorization p

theorem centralPrimeBlock_pos (n p : ℕ) : 0 < centralPrimeBlock n p := by
  cases p with
  | zero => simp [centralPrimeBlock]
  | succ p =>
      simpa only [centralPrimeBlock] using
        (pow_pos (Nat.succ_pos p)
          ((Nat.choose (2 * n) n).factorization (p + 1)))

theorem centralPrimeBlock_le_two_mul {n p : ℕ} (hn : 0 < n) :
    centralPrimeBlock n p ≤ 2 * n := by
  simpa only [centralPrimeBlock] using
    (Nat.pow_factorization_choose_le
      (p := p) (n := 2 * n) (k := n) (by omega))

theorem prime_le_centralPrimeBlock {n p : ℕ} (hp : p.Prime)
    (hexponent : 0 < (Nat.choose (2 * n) n).factorization p) :
    p ≤ centralPrimeBlock n p := by
  rw [centralPrimeBlock]
  calc
    p = p ^ 1 := by simp
    _ ≤ p ^ (Nat.choose (2 * n) n).factorization p :=
      Nat.pow_le_pow_right hp.pos (by omega)

theorem centralPromotionExponent_le_one_add_log2
    {n p : ℕ} (hp : p.Prime)
    (hexponent : 0 < (Nat.choose (2 * n) n).factorization p) :
    promotionExponent n (centralPrimeBlock n p) ≤
      1 + Nat.log2 (n / p) :=
  promotionExponent_le_one_add_log2 hp.pos
    (prime_le_centralPrimeBlock hp hexponent)

/-- The promoted factor `A_p = 2^{k_p} p^{e_p}` from the paper. -/
def promotedCentralFactor (n p : ℕ) : ℕ :=
  promotedBlock n (centralPrimeBlock n p)

theorem promotedCentralFactor_mem_centralInterval {n p : ℕ} (hn : 0 < n) :
    promotedCentralFactor n p ∈ Finset.Ioc n (2 * n) := by
  exact promotedBlock_mem_centralInterval
    (centralPrimeBlock_pos n p) (centralPrimeBlock_le_two_mul hn)

theorem promotedCentralFactor_gt {n p : ℕ} (hn : 0 < n) :
    n < promotedCentralFactor n p :=
  (Finset.mem_Ioc.mp (promotedCentralFactor_mem_centralInterval hn)).1

theorem promotedCentralFactor_le_two_mul {n p : ℕ} (hn : 0 < n) :
    promotedCentralFactor n p ≤ 2 * n :=
  (Finset.mem_Ioc.mp (promotedCentralFactor_mem_centralInterval hn)).2

/-- Promotion does not change the valuation at an odd base prime. -/
theorem promotedCentralFactor_factorization_odd
    {n p : ℕ} (hp : p.Prime) (hpOdd : p ≠ 2) :
    (promotedCentralFactor n p).factorization p =
      (Nat.choose (2 * n) n).factorization p := by
  have htwoPow : 2 ^ promotionExponent n (centralPrimeBlock n p) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hpPow : centralPrimeBlock n p ≠ 0 :=
    (centralPrimeBlock_pos n p).ne'
  have htwoPrime : Nat.Prime 2 := by norm_num
  have htwoFac :
      (2 ^ promotionExponent n (centralPrimeBlock n p)).factorization p = 0 := by
    rw [htwoPrime.factorization_pow]
    simp [Ne.symm hpOdd]
  rw [promotedCentralFactor, promotedBlock,
    Nat.factorization_mul htwoPow hpPow]
  simp only [Finsupp.add_apply]
  rw [htwoFac, centralPrimeBlock, Nat.factorization_pow_self hp]
  simp

/-- At an odd prime `p`, a promoted factor based at a different prime `q`
has zero `p`-valuation. -/
theorem promotedCentralFactor_factorization_cross
    {n p q : ℕ} (hq : q.Prime) (hpOdd : p ≠ 2) (hpq : p ≠ q) :
    (promotedCentralFactor n q).factorization p = 0 := by
  have htwoPow : 2 ^ promotionExponent n (centralPrimeBlock n q) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hqPow : centralPrimeBlock n q ≠ 0 :=
    (centralPrimeBlock_pos n q).ne'
  have htwoPrime : Nat.Prime 2 := by norm_num
  have htwoFac :
      (2 ^ promotionExponent n (centralPrimeBlock n q)).factorization p = 0 := by
    rw [htwoPrime.factorization_pow]
    simp [Ne.symm hpOdd]
  have hqFac : (centralPrimeBlock n q).factorization p = 0 := by
    rw [centralPrimeBlock, hq.factorization_pow]
    simp [Ne.symm hpq]
  rw [promotedCentralFactor, promotedBlock,
    Nat.factorization_mul htwoPow hqPow]
  simp only [Finsupp.add_apply]
  rw [htwoFac, hqFac, add_zero]

/-- The promoted factor belonging to the base prime `2` is itself a pure
power of two. -/
theorem promotedCentralFactor_two_eq_pow (n : ℕ) :
    promotedCentralFactor n 2 =
      2 ^ (promotionExponent n (centralPrimeBlock n 2) +
        (Nat.choose (2 * n) n).factorization 2) := by
  simp only [promotedCentralFactor, promotedBlock, centralPrimeBlock, pow_add]

/-- Promoted factors attached to distinct primes with positive central
exponent are distinct. -/
theorem promotedCentralFactor_injective_on_positive_support
    {n p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpExponent : 0 < (Nat.choose (2 * n) n).factorization p)
    (hqExponent : 0 < (Nat.choose (2 * n) n).factorization q)
    (hfactor : promotedCentralFactor n p = promotedCentralFactor n q) :
    p = q := by
  by_contra hpq
  by_cases hpTwo : p = 2
  · have hqOdd : q ≠ 2 := by
      intro hqTwo
      apply hpq
      exact hpTwo.trans hqTwo.symm
    have hcoordinate := congrArg (fun a : ℕ ↦ a.factorization q) hfactor
    change (promotedCentralFactor n p).factorization q =
      (promotedCentralFactor n q).factorization q at hcoordinate
    rw [promotedCentralFactor_factorization_cross
        (p := q) (q := p) hp hqOdd (Ne.symm hpq),
      promotedCentralFactor_factorization_odd hq hqOdd] at hcoordinate
    omega
  · have hcoordinate := congrArg (fun a : ℕ ↦ a.factorization p) hfactor
    change (promotedCentralFactor n p).factorization p =
      (promotedCentralFactor n q).factorization p at hcoordinate
    rw [promotedCentralFactor_factorization_odd hp hpTwo,
      promotedCentralFactor_factorization_cross
        (p := p) (q := q) hq hpTwo hpq] at hcoordinate
    omega

end

end Erdos390.WholePaper
