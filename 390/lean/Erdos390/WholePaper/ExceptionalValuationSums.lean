import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Elementary finite valuation sums

This file records the two elementary estimates used when a fixed exceptional
integer contributes a factorization-coordinate charge (the `p`-adic charge
when `p` is prime).  The unweighted prefix is exactly the corresponding
factorization coordinate of a factorial.  Discrete summation by parts then
converts the same prefix estimate into a harmonic weighted bound.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The total factorization coordinate of the positive integers at most `B`
is the same coordinate of `B!`.  For prime `p`, this is the usual `p`-adic
valuation identity; primality is not needed for the factorization identity. -/
theorem sum_factorization_Icc_eq_factorialFactorization (p B : ℕ) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) =
      B.factorial.factorization p := by
  rw [← Finset.Ico_add_one_right_eq_Icc]
  rw [← Finset.prod_Ico_id_eq_factorial]
  exact (Nat.factorization_prod_apply fun b hb ↦
    (Nat.ne_of_gt (Finset.mem_Ico.mp hb).1)).symm

/-- Natural-valued Legendre bound for the total valuation of
`1, ..., B`. -/
theorem sum_factorization_Icc_le_div_pred {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, b.factorization p) ≤ B / (p - 1) := by
  rw [sum_factorization_Icc_eq_factorialFactorization]
  exact Nat.factorization_factorial_le_div_pred hp B

/-- Real version of the elementary Legendre prefix bound. -/
theorem sum_factorization_Icc_cast_le_div_pred {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  calc
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) =
        ((∑ b ∈ Finset.Icc 1 B, b.factorization p : ℕ) : ℝ) := by
      simp only [Nat.cast_sum]
    _ ≤ ((B / (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast sum_factorization_Icc_le_div_pred hp
    _ ≤ (B : ℝ) / ((p - 1 : ℕ) : ℝ) := Nat.cast_div_le

/-- Real partial valuation sum.  Naming it keeps the finite Abel identity
readable and gives later charge arguments a reusable prefix function. -/
def valuationPrefixReal (p B : ℕ) : ℝ :=
  ∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)

@[simp]
theorem valuationPrefixReal_zero (p : ℕ) : valuationPrefixReal p 0 = 0 := by
  simp [valuationPrefixReal]

theorem valuationPrefixReal_eq_factorialFactorization (p B : ℕ) :
    valuationPrefixReal p B = (B.factorial.factorization p : ℝ) := by
  unfold valuationPrefixReal
  exact_mod_cast sum_factorization_Icc_eq_factorialFactorization p B

theorem valuationPrefixReal_le_div_pred {p B : ℕ} (hp : p.Prime) :
    valuationPrefixReal p B ≤
      (B : ℝ) / ((p - 1 : ℕ) : ℝ) := by
  simpa only [valuationPrefixReal] using
    sum_factorization_Icc_cast_le_div_pred (p := p) (B := B) hp

/-- A range beginning at zero is the positive valuation prefix because the
factorization of zero is defined to be zero. -/
theorem sum_range_succ_factorization_cast_eq_valuationPrefixReal (p B : ℕ) :
    (∑ b ∈ Finset.range (B + 1), (b.factorization p : ℝ)) =
      valuationPrefixReal p B := by
  rw [Nat.range_eq_Icc_zero_sub_one _ (Nat.add_one_ne_zero B),
    Nat.add_sub_cancel_right]
  rw [Finset.Icc_eq_cons_Ioc (Nat.zero_le B), Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  simp [valuationPrefixReal]

/-- Exact finite Abel identity for the harmonically weighted valuation sum. -/
theorem weightedFactorizationSum_eq_abel {p B : ℕ} (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (1 / (b : ℝ)) * (b.factorization p : ℝ)) =
      (1 / (B : ℝ)) * valuationPrefixReal p B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := by
  have hBpos : 0 < B := by omega
  have habel := Finset.sum_Ioc_by_parts
    (f := fun b : ℕ ↦ 1 / (b : ℝ))
    (g := fun b : ℕ ↦ (b.factorization p : ℝ))
    (m := 0) (n := B) hBpos
  have hIoc : Finset.Ioc 0 B = Finset.Icc 1 B := by
    simpa only [zero_add] using
      (Finset.Icc_add_one_left_eq_Ioc 0 B).symm
  rw [hIoc] at habel
  simp_rw [sum_range_succ_factorization_cast_eq_valuationPrefixReal] at habel
  simp only [smul_eq_mul, zero_add, Nat.cast_one, div_one,
    valuationPrefixReal_zero, mul_zero, sub_zero] at habel
  have hneg :
      -(∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / ((b + 1 : ℕ) : ℝ) - 1 / (b : ℝ)) *
            valuationPrefixReal p b) =
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro b _hb
    ring
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (1 / (b : ℝ)) * (b.factorization p : ℝ)) =
        (1 / (B : ℝ)) * valuationPrefixReal p B -
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            (1 / ((b + 1 : ℕ) : ℝ) - 1 / (b : ℝ)) *
              valuationPrefixReal p b := habel
    _ = _ := by rw [sub_eq_add_neg, hneg]

private theorem one_add_sum_Ioc_succ_reciprocal_eq_harmonic
    {B : ℕ} (hB : 1 ≤ B) :
    1 + ∑ b ∈ Finset.Ioc 0 (B - 1),
        1 / ((b + 1 : ℕ) : ℝ) = (harmonic B : ℝ) := by
  have hset : Finset.Ioc 0 (B - 1) = Finset.Ico 1 B := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, Nat.sub_add_cancel hB]
    simp
  have hshift :
      (∑ b ∈ Finset.Ico 1 B, 1 / ((b + 1 : ℕ) : ℝ)) =
        ∑ k ∈ Finset.Ico 2 (B + 1), 1 / (k : ℝ) := by
    simpa only [one_add_one_eq_two] using
      (Finset.sum_Ico_add' (fun k : ℕ ↦ 1 / (k : ℝ)) 1 B 1)
  rw [hset, hshift, Finset.Ico_add_one_right_eq_Icc]
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
  rw [Finset.Icc_eq_cons_Ioc hB, Finset.sum_cons,
    ← Finset.Icc_add_one_left_eq_Ioc]
  norm_num

/-- Sharp elementary harmonic bound for the weighted valuation sum. -/
theorem weightedFactorizationSum_le_one_add_log_div_pred
    {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      (1 + Real.log (B : ℝ)) / ((p - 1 : ℕ) : ℝ) := by
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hd : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hdNat
  have hBreal : 0 < (B : ℝ) := by exact_mod_cast (show 0 < B by omega)
  have hend :
      (1 / (B : ℝ)) * valuationPrefixReal p B ≤
        1 / ((p - 1 : ℕ) : ℝ) := by
    calc
      (1 / (B : ℝ)) * valuationPrefixReal p B ≤
          (1 / (B : ℝ)) *
            ((B : ℝ) / ((p - 1 : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_left (valuationPrefixReal_le_div_pred hp)
          (one_div_nonneg.mpr hBreal.le)
      _ = 1 / ((p - 1 : ℕ) : ℝ) := by
        field_simp [ne_of_gt hBreal, ne_of_gt hd]
  have hterm (b : ℕ) (hb : b ∈ Finset.Ioc 0 (B - 1)) :
      (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          valuationPrefixReal p b ≤
        (1 / ((p - 1 : ℕ) : ℝ)) *
          (1 / ((b + 1 : ℕ) : ℝ)) := by
    have hbNat : 0 < b := (Finset.mem_Ioc.mp hb).1
    have hbReal : 0 < (b : ℝ) := by exact_mod_cast hbNat
    have hbSuccReal : 0 < ((b + 1 : ℕ) : ℝ) := by positivity
    have hdiff :
        0 ≤ 1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ) := by
      exact sub_nonneg.mpr (one_div_le_one_div_of_le hbReal (by
        exact_mod_cast Nat.le_add_right b 1))
    calc
      (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          valuationPrefixReal p b ≤
        (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
          ((b : ℝ) / ((p - 1 : ℕ) : ℝ)) :=
            mul_le_mul_of_nonneg_left (valuationPrefixReal_le_div_pred hp) hdiff
      _ = (1 / ((p - 1 : ℕ) : ℝ)) *
          (1 / ((b + 1 : ℕ) : ℝ)) := by
        push_cast
        field_simp [ne_of_gt hbReal, ne_of_gt hbSuccReal, ne_of_gt hd]
        ring
  have hinterior :
      (∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b) ≤
        (1 / ((p - 1 : ℕ) : ℝ)) *
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            1 / ((b + 1 : ℕ) : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b hb ↦ hterm b hb
  have hharm : (harmonic B : ℝ) ≤ 1 + Real.log (B : ℝ) :=
    harmonic_le_one_add_log B
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) =
        ∑ b ∈ Finset.Icc 1 B,
          (1 / (b : ℝ)) * (b.factorization p : ℝ) := by
      apply Finset.sum_congr rfl
      intro b _hb
      ring
    _ = (1 / (B : ℝ)) * valuationPrefixReal p B +
        ∑ b ∈ Finset.Ioc 0 (B - 1),
          (1 / (b : ℝ) - 1 / ((b + 1 : ℕ) : ℝ)) *
            valuationPrefixReal p b := weightedFactorizationSum_eq_abel hB
    _ ≤ 1 / ((p - 1 : ℕ) : ℝ) +
        (1 / ((p - 1 : ℕ) : ℝ)) *
          ∑ b ∈ Finset.Ioc 0 (B - 1),
            1 / ((b + 1 : ℕ) : ℝ) := add_le_add hend hinterior
    _ = (1 / ((p - 1 : ℕ) : ℝ)) * (harmonic B : ℝ) := by
      rw [← one_add_sum_Ioc_succ_reciprocal_eq_harmonic hB]
      ring
    _ ≤ (1 / ((p - 1 : ℕ) : ℝ)) *
        (1 + Real.log (B : ℝ)) :=
      mul_le_mul_of_nonneg_left hharm (one_div_nonneg.mpr hd.le)
    _ = (1 + Real.log (B : ℝ)) /
        ((p - 1 : ℕ) : ℝ) := by ring

/-- For primes, the `1/(p-1)` form costs at most a factor two compared with
`1/p`. -/
theorem one_div_prime_pred_le_two_div_prime {p : ℕ} (hp : p.Prime) :
    1 / ((p - 1 : ℕ) : ℝ) ≤ 2 / (p : ℝ) := by
  have hpReal : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hdNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hd : 0 < ((p - 1 : ℕ) : ℝ) := by exact_mod_cast hdNat
  apply (div_le_div_iff₀ hd hpReal).2
  norm_num only [one_mul]
  exact_mod_cast (show p ≤ 2 * (p - 1) by omega)

/-- Convenient `O(B/p)` version of the unweighted valuation bound. -/
theorem sum_factorization_Icc_cast_le_two_mul_div_prime
    {p B : ℕ} (hp : p.Prime) :
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
      2 * (B : ℝ) / (p : ℝ) := by
  calc
    (∑ b ∈ Finset.Icc 1 B, (b.factorization p : ℝ)) ≤
        (B : ℝ) / ((p - 1 : ℕ) : ℝ) :=
      sum_factorization_Icc_cast_le_div_pred hp
    _ = (B : ℝ) * (1 / ((p - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (B : ℝ) * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_prime_pred_le_two_div_prime hp)
        (Nat.cast_nonneg B)
    _ = 2 * (B : ℝ) / (p : ℝ) := by ring

/-- Convenient uniform `O((1 + log B)/p)` version of the weighted bound. -/
theorem weightedFactorizationSum_le_two_mul_one_add_log_div_prime
    {p B : ℕ} (hp : p.Prime) (hB : 1 ≤ B) :
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
      2 * (1 + Real.log (B : ℝ)) / (p : ℝ) := by
  have hlog : 0 ≤ 1 + Real.log (B : ℝ) := by
    have hcast : (1 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
    have hlogNonneg : 0 ≤ Real.log (B : ℝ) := Real.log_nonneg hcast
    linarith
  calc
    (∑ b ∈ Finset.Icc 1 B,
        (b.factorization p : ℝ) / (b : ℝ)) ≤
        (1 + Real.log (B : ℝ)) / ((p - 1 : ℕ) : ℝ) :=
      weightedFactorizationSum_le_one_add_log_div_pred hp hB
    _ = (1 + Real.log (B : ℝ)) *
        (1 / ((p - 1 : ℕ) : ℝ)) := by ring
    _ ≤ (1 + Real.log (B : ℝ)) * (2 / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left (one_div_prime_pred_le_two_div_prime hp) hlog
    _ = 2 * (1 + Real.log (B : ℝ)) / (p : ℝ) := by ring

end

end Erdos390.WholePaper
