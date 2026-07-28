import Erdos390.Full.OmittedScoreCell

open scoped BigOperators

namespace Erdos390.Full.ValuationScoreDomination

open ArithmeticModel DivisibilityMomentBounds

noncomputable section

/-- All prime-power moduli which can occur below the common endpoint `M`. -/
def primePowerModuli (P : Finset ℕ) (M : ℕ) : Finset ℕ :=
  (P ×ˢ positiveExponents M).image (fun pk ↦ pk.1 ^ pk.2)

theorem primePowerMap_injective {P : Finset ℕ} {M : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun pk : ℕ × ℕ ↦ pk.1 ^ pk.2)
      (↑(P ×ˢ positiveExponents M) : Set (ℕ × ℕ)) := by
  intro pk hpk ql hql heq
  have hpP := (Finset.mem_product.mp hpk).1
  have hkM := (Finset.mem_product.mp hpk).2
  have hqP := (Finset.mem_product.mp hql).1
  have hlM := (Finset.mem_product.mp hql).2
  have hk0 : pk.2 ≠ 0 := by
    rw [mem_positiveExponents] at hkM
    omega
  have hl0 : ql.2 ≠ 0 := by
    rw [mem_positiveExponents] at hlM
    omega
  have hinj := Nat.Prime.pow_inj' (hprime pk.1 hpP) (hprime ql.1 hqP)
    hk0 hl0 heq
  exact Prod.ext hinj.1 hinj.2

/-- Deduplication loses no term: distinct positive powers of primes are
distinct moduli. -/
theorem divisorScore_primePowerModuli_eq
    (P : Finset ℕ) (M m : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    divisorScore (primePowerModuli P M) m =
      ∑ p ∈ P, ∑ k ∈ positiveExponents M, divInd (p ^ k) m := by
  unfold divisorScore primePowerModuli
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · intro a ha b hb hab
    exact primePowerMap_injective hprime ha hb hab

/-- The actual valuation score appearing in a compact tilt. -/
def valuationScore (P : Finset ℕ) (eta : ℕ → ℝ)
    (L : ℝ) (m : ℕ) : ℝ :=
  ∑ p ∈ P, (eta p / L) * valuation p m

theorem valuationScore_eq_indicator_sum_of_le
    (P : Finset ℕ) (eta : ℕ → ℝ) (L : ℝ) {m M : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    valuationScore P eta L m =
      ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (eta p / L) * divInd (p ^ k) m := by
  unfold valuationScore
  apply Finset.sum_congr rfl
  intro p hp
  rw [valuation_eq_sum_divInd_of_le (hprime p hp) hm hmM,
    Finset.mul_sum]

/-- Box-uniform pointwise domination of the true valuation score by the
prime-power divisor score.  The coefficient `B/L` is independent of the
forced marked modulus. -/
theorem abs_valuationScore_le_divisorScore
    (P : Finset ℕ) (eta : ℕ → ℝ) {B L : ℝ} {m M : ℕ}
    (hprime : ∀ p ∈ P, p.Prime) (hm : 0 < m) (hmM : m ≤ M)
    (hL : 0 < L) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    |valuationScore P eta L m| ≤
      (B / L) * divisorScore (primePowerModuli P M) m := by
  rw [valuationScore_eq_indicator_sum_of_le P eta L hprime hm hmM]
  calc
    _ ≤ ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        |(eta p / L) * divInd (p ^ k) m| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun p hp ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (|eta p| / L) * divInd (p ^ k) m := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul, abs_div, abs_of_pos hL,
        abs_of_nonneg (divInd_nonneg (p ^ k) m)]
    _ ≤ ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (B / L) * divInd (p ^ k) m := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (divInd_nonneg (p ^ k) m)
    _ = (B / L) *
        (∑ p ∈ P, ∑ k ∈ positiveExponents M, divInd (p ^ k) m) := by
      simp only [Finset.mul_sum]
    _ = (B / L) * divisorScore (primePowerModuli P M) m := by
      rw [divisorScore_primePowerModuli_eq P M m hprime]

theorem pos_of_mem_primePowerModuli {P : Finset ℕ} {M a : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    (ha : a ∈ primePowerModuli P M) : 0 < a := by
  rw [primePowerModuli, Finset.mem_image] at ha
  obtain ⟨pk, hpk, rfl⟩ := ha
  exact pow_pos (hprime pk.1 (Finset.mem_product.mp hpk).1).pos _

theorem coprime_of_mem_primePowerModuli {P : Finset ℕ} {M D a : ℕ}
    (hcop : ∀ p ∈ P, Nat.Coprime D p)
    (ha : a ∈ primePowerModuli P M) : Nat.Coprime D a := by
  rw [primePowerModuli, Finset.mem_image] at ha
  obtain ⟨pk, hpk, rfl⟩ := ha
  exact (hcop pk.1 (Finset.mem_product.mp hpk).1).pow_right _

theorem sum_inv_primePowerModuli_eq
    (P : Finset ℕ) (M : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) =
      ∑ p ∈ P, ∑ k ∈ positiveExponents M, 1 / ((p ^ k : ℕ) : ℝ) := by
  unfold primePowerModuli
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
  · intro a ha b hb hab
    exact primePowerMap_injective hprime ha hb hab

private theorem sum_Icc_half_pow_pred_eq (M : ℕ) :
    (∑ k ∈ Finset.Icc 1 M, (1 / (2 : ℝ)) ^ (k - 1)) =
      ∑ i ∈ Finset.range M, (1 / (2 : ℝ)) ^ i := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]
      simp

/-- The reciprocal mass of the positive powers of one prime is bounded by
the corresponding infinite geometric series. -/
theorem sum_inv_prime_powers_le (p M : ℕ) (hp2 : 2 ≤ p) :
    (∑ k ∈ positiveExponents M, 1 / ((p ^ k : ℕ) : ℝ)) ≤
      2 / (p : ℝ) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hpPos : (0 : ℝ) < (p : ℝ) := by positivity
  calc
    _ ≤ ∑ k ∈ positiveExponents M,
        (1 / (p : ℝ)) * (1 / (2 : ℝ)) ^ (k - 1) := by
      apply Finset.sum_le_sum
      intro k hk
      rw [mem_positiveExponents] at hk
      have hpow : (2 : ℝ) ^ (k - 1) ≤ (p : ℝ) ^ (k - 1) := by gcongr
      have hpkpow : (p : ℝ) ^ k =
          (p : ℝ) * (p : ℝ) ^ (k - 1) := by
        calc
          (p : ℝ) ^ k = (p : ℝ) ^ ((k - 1) + 1) := by
            congr 1
            omega
          _ = (p : ℝ) * (p : ℝ) ^ (k - 1) := by
            rw [pow_succ']
      calc
        1 / ((p ^ k : ℕ) : ℝ) = 1 / ((p : ℝ) ^ k) := by norm_num
        _ = 1 / ((p : ℝ) * (p : ℝ) ^ (k - 1)) := by
          rw [hpkpow]
        _ ≤ 1 / ((p : ℝ) * (2 : ℝ) ^ (k - 1)) := by
          gcongr
        _ = (1 / (p : ℝ)) * (1 / (2 : ℝ)) ^ (k - 1) := by
          rw [one_div_pow]
          field_simp
    _ = (1 / (p : ℝ)) *
        (∑ k ∈ Finset.Icc 1 M, (1 / (2 : ℝ)) ^ (k - 1)) := by
      rw [Finset.mul_sum]
      rfl
    _ = (1 / (p : ℝ)) *
        (∑ i ∈ Finset.range M, (1 / (2 : ℝ)) ^ i) := by
      rw [sum_Icc_half_pow_pred_eq]
    _ ≤ (1 / (p : ℝ)) * 2 :=
      mul_le_mul_of_nonneg_left (sum_geometric_two_le M) (by positivity)
    _ = 2 / (p : ℝ) := by ring

/-- The reciprocal mass of all relevant prime powers is at most twice the
reciprocal mass of the underlying primes.  The constant is independent of
the truncation endpoint `M`. -/
theorem sum_inv_primePowerModuli_le
    (P : Finset ℕ) (M : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) ≤
      2 * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [sum_inv_primePowerModuli_eq P M hprime]
  calc
    _ ≤ ∑ p ∈ P, 2 / (p : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_inv_prime_powers_le p M (hprime p hp).two_le
    _ = 2 * ∑ p ∈ P, 1 / (p : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      ring

end

end Erdos390.Full.ValuationScoreDomination
