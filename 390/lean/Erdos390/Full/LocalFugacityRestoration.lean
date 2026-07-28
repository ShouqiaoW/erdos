import Erdos390.Full.LocalFugacity
import Erdos390.Full.FiniteExponentialFamily

/-!
# Exact restoration of omitted local fugacities

The paper omits one or two forced primes from the global score and then
restores their local fugacity by a finite divisor-indicator expansion.  This
file proves that restoration identity for the actual valuation and for an
actual finite probability law.  No approximation or independence assumption
is used here.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacityRestoration

open ArithmeticModel LocalFugacity

noncomputable section

/-- The local divisor expansion, including the exponent-zero coefficient. -/
def localFactor (p A : ℕ) (lam : ℝ) (m : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 0 A, coefficient lam a * divInd (p ^ a) m

private theorem Icc_zero_eq_insert (A : ℕ) :
    Finset.Icc 0 A = insert 0 (Finset.Icc 1 A) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

/-- The finite local factor is exactly `λ^{v_p(m)}` once the cutoff is above
the actual valuation. -/
theorem localFactor_eq_pow_valuation {p m A : ℕ} (lam : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hA : m.factorization p ≤ A) :
    localFactor p A lam m = lam ^ m.factorization p := by
  rw [localFactor, Icc_zero_eq_insert]
  have hzero : 0 ∉ Finset.Icc 1 A := by simp
  rw [Finset.sum_insert hzero]
  simp only [coefficient_zero, pow_zero, one_mul]
  have hdiv : divInd 1 m = 1 := by simp [divInd]
  rw [hdiv]
  symm
  exact pow_valuation_eq_indicator_expansion lam hp hm hA

/-- A common upper endpoint for a whole physical cell is automatically a
valid valuation cutoff at every sample point. -/
theorem localFactor_eq_pow_valuation_of_le {p m M : ℕ} (lam : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p M lam m = lam ^ m.factorization p := by
  apply localFactor_eq_pow_valuation lam hp hm
  exact (Nat.factorization_lt p hm.ne').le.trans hmM

/-- Exponential form of the same exact identity. -/
theorem localFactor_exp_eq {p m A : ℕ} (eta L : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hA : m.factorization p ≤ A) :
    localFactor p A (Real.exp (eta / L)) m =
      Real.exp (eta / L * valuation p m) := by
  rw [localFactor_eq_pow_valuation (Real.exp (eta / L)) hp hm hA]
  rw [valuation, mul_comm, Real.exp_nat_mul]

theorem localFactor_exp_eq_of_le {p m M : ℕ} (eta L : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p M (Real.exp (eta / L)) m =
      Real.exp (eta / L * valuation p m) := by
  rw [localFactor_eq_pow_valuation_of_le (Real.exp (eta / L)) hp hm hmM]
  rw [valuation, mul_comm, Real.exp_nat_mul]

/-- Exact two-prime fugacity restoration, with no coprimality shortcut: each
local factor has already been identified with the corresponding valuation. -/
theorem two_localFactor_exp_eq {p q m A B : ℕ} (eta zeta L : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hm : 0 < m)
    (hA : m.factorization p ≤ A) (hB : m.factorization q ≤ B) :
    localFactor p A (Real.exp (eta / L)) m *
        localFactor q B (Real.exp (zeta / L)) m =
      Real.exp ((eta * valuation p m + zeta * valuation q m) / L) := by
  rw [localFactor_exp_eq eta L hp hm hA,
    localFactor_exp_eq zeta L hq hm hB]
  rw [← Real.exp_add]
  congr 1
  ring

/-- Literal double-sum expansion of two restored local factors. -/
theorem localFactor_mul_eq_double_sum (p q A B : ℕ) (lam mu : ℝ) (m : ℕ) :
    localFactor p A lam m * localFactor q B mu m =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          (divInd (p ^ a) m * divInd (q ^ b) m) := by
  unfold localFactor
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- For distinct primes, the product of the two actual divisor indicators is
the indicator of the product divisor. -/
theorem divInd_primePowers_mul {p q a b m : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    divInd (p ^ a) m * divInd (q ^ b) m =
      divInd (p ^ a * q ^ b) m := by
  by_cases hpa : p ^ a ∣ m
  · by_cases hqb : q ^ b ∣ m
    · have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
        (hp.coprime_iff_not_dvd.mpr (by
          intro hdiv
          exact hpq (Nat.dvd_prime hq |>.mp hdiv |>.resolve_left hp.ne_one))).pow
          a b
      have hprod : p ^ a * q ^ b ∣ m :=
        hcop.mul_dvd_of_dvd_of_dvd hpa hqb
      simp [divInd, hpa, hqb, hprod]
    · have hnprod : ¬p ^ a * q ^ b ∣ m := by
        intro hprod
        exact hqb ((dvd_mul_left (q ^ b) (p ^ a)).trans hprod)
      simp [divInd, hpa, hqb, hnprod]
  · have hnprod : ¬p ^ a * q ^ b ∣ m := by
      intro hprod
      exact hpa ((dvd_mul_right (p ^ a) (q ^ b)).trans hprod)
    simp [divInd, hpa, hnprod]

/-- The paper's exact two-local coefficient formula for distinct primes. -/
theorem localFactor_mul_eq_product_indicator {p q A B : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    (lam mu : ℝ) (m : ℕ) :
    localFactor p A lam m * localFactor q B mu m =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          divInd (p ^ a * q ^ b) m := by
  rw [localFactor_mul_eq_double_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [divInd_primePowers_mul hpq hp hq]

section Probability

variable {Omega : Type*} [Fintype Omega]

/-- Exact numerator after restoring two omitted local fugacities and imposing
a further divisor event `D ∣ m`. -/
theorem expect_two_restored_indicator
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q A B D : ℕ} (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    (lam mu : ℝ) :
    nu.expect (fun omega ↦
        divInd D (value omega) * localFactor p A lam (value omega) *
          localFactor q B mu (value omega)) =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          nu.expect (fun omega ↦
            divInd D (value omega) *
              divInd (p ^ a * q ^ b) (value omega)) := by
  have hpoint (omega : Omega) :
      divInd D (value omega) * localFactor p A lam (value omega) *
          localFactor q B mu (value omega) =
        divInd D (value omega) *
          (∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
            coefficient lam a * coefficient mu b *
              divInd (p ^ a * q ^ b) (value omega)) := by
    rw [mul_assoc,
      localFactor_mul_eq_product_indicator hpq hp hq]
  simp_rw [hpoint]
  unfold FiniteProbability.expect
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro omega _
  ring

/-- The corresponding exact normalizing denominator. -/
theorem expect_two_restored
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q A B : ℕ} (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    (lam mu : ℝ) :
    nu.expect (fun omega ↦ localFactor p A lam (value omega) *
        localFactor q B mu (value omega)) =
      ∑ a ∈ Finset.Icc 0 A, ∑ b ∈ Finset.Icc 0 B,
        coefficient lam a * coefficient mu b *
          nu.expect (fun omega ↦
            divInd (p ^ a * q ^ b) (value omega)) := by
  simpa only [divInd, one_dvd, if_pos, one_mul] using
    expect_two_restored_indicator nu value hpq hp hq lam mu
      (A := A) (B := B) (D := 1)

end Probability

end

end Erdos390.Full.LocalFugacityRestoration
