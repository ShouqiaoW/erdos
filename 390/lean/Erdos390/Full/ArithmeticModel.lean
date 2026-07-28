import Mathlib

/-!
# Arithmetic model for the full Erdős 390 formalization

This file connects the abstract covariance columns used by the earlier audit
companion to the actual arithmetic objects in the paper.  All definitions are
total, including at `n = 0`, `m = 0`, and at non-prime bases.  The valuation
identities themselves are stated with the mathematically necessary hypotheses
that the base is prime and the sampled integer is positive.
-/

open scoped BigOperators

namespace Erdos390.Full.ArithmeticModel

/-- The real smoothness threshold from the paper, `n^(2/9)`. -/
noncomputable def y (n : ℕ) : ℝ :=
  (n : ℝ) ^ (2 / 9 : ℝ)

/-- The integral cutoff used when a finite set of primes is required. -/
noncomputable def yNat (n : ℕ) : ℕ :=
  ⌊y n⌋₊

/-- The actual prime band `W < p ≤ y`. -/
noncomputable def primeBand (n W : ℕ) : Finset ℕ :=
  ((yNat n + 1).primesBelow).filter (W < ·)

/-- The logarithmic prime coordinate `log p / log y`.  The definition is
total; at the irrelevant boundary `n ≤ 1`, Lean's field conventions give a
well-defined value even though the analytic argument never uses it there. -/
noncomputable def tPrime (n p : ℕ) : ℝ :=
  Real.log (p : ℝ) / Real.log (y n)

/-- The divisibility indicator, as a real-valued random variable.  In
particular `divInd d 0 = 1`, since every natural number divides zero. -/
def divInd (d m : ℕ) : ℝ :=
  if d ∣ m then 1 else 0

/-- The actual `p`-adic valuation column.  Mathlib's factorization is zero at
`m = 0` and at non-prime bases; both conventions are recorded below. -/
def valuation (p m : ℕ) : ℝ :=
  (m.factorization p : ℝ)

/-- The higher-prime-power part `J_p = V_p - I_p`. -/
def higherValuation (p m : ℕ) : ℝ :=
  valuation p m - divInd p m

/-- A natural upper bound for the fixed physical interval `m ≤ C⋅n`. -/
noncomputable def physicalBound (C : ℝ) (n : ℕ) : ℕ :=
  ⌊C * (n : ℝ)⌋₊

/-- All positive exponents up to a common physical bound. -/
def positiveExponents (M : ℕ) : Finset ℕ :=
  Finset.Icc 1 M

/-- All exponents at least two up to a common physical bound. -/
def highExponents (M : ℕ) : Finset ℕ :=
  Finset.Icc 2 M

@[simp] theorem y_zero : y 0 = 0 := by
  simp [y]

@[simp] theorem y_one : y 1 = 1 := by
  norm_num [y]

@[simp] theorem yNat_zero : yNat 0 = 0 := by
  simp [yNat]

theorem mem_primeBand {n W p : ℕ} :
    p ∈ primeBand n W ↔ p.Prime ∧ W < p ∧ p ≤ yNat n := by
  simp only [primeBand, Finset.mem_filter, Nat.mem_primesBelow,
    Nat.lt_succ_iff]
  tauto

theorem prime_of_mem_primeBand {n W p : ℕ} (hp : p ∈ primeBand n W) :
    p.Prime :=
  (mem_primeBand.mp hp).1

theorem cutoff_lt_of_mem_primeBand {n W p : ℕ} (hp : p ∈ primeBand n W) :
    W < p :=
  (mem_primeBand.mp hp).2.1

theorem le_yNat_of_mem_primeBand {n W p : ℕ} (hp : p ∈ primeBand n W) :
    p ≤ yNat n :=
  (mem_primeBand.mp hp).2.2

@[simp] theorem zero_not_mem_primeBand (n W : ℕ) : 0 ∉ primeBand n W := by
  intro h
  exact (prime_of_mem_primeBand h).ne_zero rfl

@[simp] theorem one_not_mem_primeBand (n W : ℕ) : 1 ∉ primeBand n W := by
  intro h
  exact (prime_of_mem_primeBand h).ne_one rfl

@[simp] theorem primeBand_zero (W : ℕ) : primeBand 0 W = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro p hp
  have hle : p ≤ 0 := by
    simpa using le_yNat_of_mem_primeBand hp
  have hpos : 0 < p := (prime_of_mem_primeBand hp).pos
  omega

@[simp] theorem divInd_zero_right (d : ℕ) : divInd d 0 = 1 := by
  simp [divInd]

@[simp] theorem divInd_zero_left {m : ℕ} (hm : m ≠ 0) : divInd 0 m = 0 := by
  simp [divInd, zero_dvd_iff, hm]

theorem divInd_eq_zero_or_one (d m : ℕ) :
    divInd d m = 0 ∨ divInd d m = 1 := by
  by_cases h : d ∣ m
  · exact Or.inr (by simp [divInd, h])
  · exact Or.inl (by simp [divInd, h])

theorem divInd_nonneg (d m : ℕ) : 0 ≤ divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]

theorem divInd_le_one (d m : ℕ) : divInd d m ≤ 1 := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]

@[simp] theorem divInd_sq (d m : ℕ) : divInd d m ^ 2 = divInd d m := by
  rcases divInd_eq_zero_or_one d m with h | h <;> simp [h]

@[simp] theorem valuation_zero_right (p : ℕ) : valuation p 0 = 0 := by
  simp [valuation]

theorem valuation_eq_zero_of_not_prime {p m : ℕ} (hp : ¬p.Prime) :
    valuation p m = 0 := by
  simp [valuation, Nat.factorization_eq_zero_of_not_prime m hp]

@[simp] theorem valuation_zero_left (m : ℕ) : valuation 0 m = 0 := by
  exact valuation_eq_zero_of_not_prime Nat.not_prime_zero

@[simp] theorem valuation_one_left (m : ℕ) : valuation 1 m = 0 := by
  exact valuation_eq_zero_of_not_prime Nat.not_prime_one

theorem valuation_nonneg (p m : ℕ) : 0 ≤ valuation p m := by
  simp [valuation]

/-- At the excluded sample point `m = 0`, actual divisibility and Mathlib's
total factorization convention make `J_p = -1`.  All probabilistic cells in
the paper contain positive integers, and every positivity theorem below
therefore states that hypothesis explicitly. -/
@[simp] theorem higherValuation_zero_right (p : ℕ) :
    higherValuation p 0 = -1 := by
  simp [higherValuation]

/-- At a non-prime base, the factorization column is zero.  This records the
remaining total boundary behavior rather than silently treating a composite
base as a prime. -/
theorem higherValuation_eq_neg_divInd_of_not_prime {p m : ℕ}
    (hp : ¬p.Prime) :
    higherValuation p m = -divInd p m := by
  rw [higherValuation, valuation_eq_zero_of_not_prime hp]
  ring

@[simp] theorem mem_positiveExponents {M k : ℕ} :
    k ∈ positiveExponents M ↔ 1 ≤ k ∧ k ≤ M := by
  simp [positiveExponents]

@[simp] theorem mem_highExponents {M k : ℕ} :
    k ∈ highExponents M ↔ 2 ≤ k ∧ k ≤ M := by
  simp [highExponents]

/-- A prime valuation is the finite sum of its positive-power divisibility
indicators.  The common exponent cutoff may be any `M` above the sampled
integer, hence in particular a fixed physical upper bound for a whole cell. -/
theorem valuation_eq_sum_divInd_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    valuation p m = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
  have hMpow : m ≤ p ^ M := by
    exact hmM.trans (Nat.le_of_lt (Nat.lt_pow_self hp.one_lt))
  have hfilter := Nat.Ico_filter_pow_dvd_eq hp hm.ne' hMpow
  have hcard := Nat.factorization_eq_card_pow_dvd m hp
  calc
    valuation p m = (m.factorization p : ℝ) := rfl
    _ = (((Finset.Ico 1 m).filter fun k => p ^ k ∣ m).card : ℝ) := by
      exact_mod_cast hcard
    _ = (((Finset.Icc 1 M).filter fun k => p ^ k ∣ m).card : ℝ) := by
      rw [hfilter]
    _ = ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
      simp [positiveExponents, divInd]

theorem valuation_eq_sum_divInd {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    valuation p m = ∑ k ∈ positiveExponents m, divInd (p ^ k) m :=
  valuation_eq_sum_divInd_of_le hp hm le_rfl

theorem valuation_eq_sum_divInd_physical {C : ℝ} {n p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmC : m ≤ physicalBound C n) :
    valuation p m =
      ∑ k ∈ positiveExponents (physicalBound C n), divInd (p ^ k) m :=
  valuation_eq_sum_divInd_of_le hp hm hmC

private theorem positiveExponents_eq_insert_high {M : ℕ} (hM : 1 ≤ M) :
    positiveExponents M = insert 1 (highExponents M) := by
  ext k
  simp only [mem_positiveExponents, Finset.mem_insert, mem_highExponents]
  omega

/-- The paper's identity `J_p = sum_{k≥2} 1_{p^k ∣ m}`, with a
common finite cutoff valid throughout a physical cell. -/
theorem higherValuation_eq_sum_high_of_le {p m M : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    higherValuation p m = ∑ k ∈ highExponents M, divInd (p ^ k) m := by
  have hM : 1 ≤ M := hm.trans_le hmM
  rw [higherValuation, valuation_eq_sum_divInd_of_le hp hm hmM,
    positiveExponents_eq_insert_high hM]
  have h1not : 1 ∉ highExponents M := by simp
  rw [Finset.sum_insert h1not]
  simp [divInd]

theorem higherValuation_eq_sum_high {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m = ∑ k ∈ highExponents m, divInd (p ^ k) m :=
  higherValuation_eq_sum_high_of_le hp hm le_rfl

theorem higherValuation_eq_sum_high_physical {C : ℝ} {n p m : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmC : m ≤ physicalBound C n) :
    higherValuation p m =
      ∑ k ∈ highExponents (physicalBound C n), divInd (p ^ k) m :=
  higherValuation_eq_sum_high_of_le hp hm hmC

/-- A more precise cutoff statement: a prime power larger than the physical
integer bound cannot divide any positive sample in that interval.  Primality
is not needed for this elementary implication. -/
theorem divInd_pow_eq_zero_of_bound_lt_pow {p m M k : ℕ}
    (hm : 0 < m) (hmM : m ≤ M) (hMpow : M < p ^ k) :
    divInd (p ^ k) m = 0 := by
  have hnot : ¬p ^ k ∣ m := by
    intro hdvd
    have hpowm : p ^ k ≤ m := Nat.le_of_dvd hm hdvd
    omega
  simp [divInd, hnot]

theorem divInd_pow_eq_zero_above_physical_power {C : ℝ} {n p m k : ℕ}
    (hm : 0 < m) (hmC : m ≤ physicalBound C n)
    (hk : physicalBound C n < p ^ k) :
    divInd (p ^ k) m = 0 :=
  divInd_pow_eq_zero_of_bound_lt_pow hm hmC hk

/-- Every power whose exponent is beyond the common physical cutoff has zero
indicator on that physical interval. -/
theorem divInd_pow_eq_zero_of_bound_lt {p m M k : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) (hMk : M < k) :
    divInd (p ^ k) m = 0 := by
  have hnot : ¬p ^ k ∣ m := by
    intro hdvd
    have hpowm : p ^ k ≤ m := Nat.le_of_dvd hm hdvd
    have hkpow : k < p ^ k := Nat.lt_pow_self hp.one_lt
    omega
  simp [divInd, hnot]

theorem divInd_pow_eq_zero_above_physical {C : ℝ} {n p m k : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmC : m ≤ physicalBound C n)
    (hk : physicalBound C n < k) :
    divInd (p ^ k) m = 0 :=
  divInd_pow_eq_zero_of_bound_lt hp hm hmC hk

theorem higherValuation_nonneg {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    0 ≤ higherValuation p m := by
  rw [higherValuation_eq_sum_high hp hm]
  exact Finset.sum_nonneg fun k hk => divInd_nonneg (p ^ k) m

private theorem natCast_le_square (a : ℕ) : (a : ℝ) ≤ (a : ℝ) ^ 2 := by
  cases a with
  | zero => norm_num
  | succ a =>
      have h : (1 : ℝ) ≤ (a.succ : ℝ) := by exact_mod_cast a.succ_pos
      nlinarith

private theorem higherValuation_eq_natCast_pred {p m : ℕ}
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

/-- Since `J_p` is a nonnegative integer, `J_p ≤ J_p²`. -/
theorem higherValuation_le_sq {p m : ℕ} (hp : p.Prime) (hm : 0 < m) :
    higherValuation p m ≤ higherValuation p m ^ 2 := by
  rw [higherValuation_eq_natCast_pred hp hm]
  exact natCast_le_square _

/-- The pointwise identity `I_p J_p = J_p`.  It remains true at all total
boundary values; primality is not needed for this algebraic identity. -/
@[simp] theorem divInd_mul_higherValuation (p m : ℕ) :
    divInd p m * higherValuation p m = higherValuation p m := by
  by_cases hdvd : p ∣ m
  · simp [divInd, higherValuation, hdvd]
  · have hfac : m.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hdvd
    simp [divInd, higherValuation, valuation, hdvd, hfac]

end Erdos390.Full.ArithmeticModel
