import Erdos390.Full.ArithmeticModel
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Exact finite head patterns

The marked smooth cells impose exact valuations at finitely many fixed head
primes.  This file records their integral factor and modulus and proves the
factorization/divisibility part of the inclusion--exclusion reduction.  No
smooth-number asymptotic is used here.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos390.Full.HeadPattern

/-- A finite list of distinct head primes and their prescribed exponents. -/
structure Pattern where
  primes : Finset ℕ
  exponent : ℕ → ℕ
  prime_mem : ∀ p ∈ primes, p.Prime

namespace Pattern

variable (P : Pattern)

/-- The forced prime-power part `h_e`. -/
def factor : ℕ :=
  ∏ p ∈ P.primes, p ^ P.exponent p

/-- The squarefree head modulus `M_H`. -/
def modulus : ℕ :=
  ∏ p ∈ P.primes, p

/-- Exact agreement with the prescribed head valuations. -/
def Matches (m : ℕ) : Prop :=
  ∀ p ∈ P.primes, m.factorization p = P.exponent p

instance (m : ℕ) : Decidable (P.Matches m) := by
  unfold Matches
  infer_instance

theorem factor_ne_zero : P.factor ≠ 0 := by
  rw [factor]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem modulus_ne_zero : P.modulus ≠ 0 := by
  rw [modulus]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact (P.prime_mem p hp).ne_zero

theorem factorization_factor (q : ℕ) :
    P.factor.factorization q =
      if q ∈ P.primes then P.exponent q else 0 := by
  classical
  rw [factor, Nat.factorization_prod_apply]
  · calc
      ∑ p ∈ P.primes, (p ^ P.exponent p).factorization q =
          ∑ p ∈ P.primes, if p = q then P.exponent p else 0 := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [(P.prime_mem p hp).factorization_pow]
            simp [Finsupp.single_apply]
      _ = if q ∈ P.primes then P.exponent q else 0 := by
        simp [eq_comm]
  · intro p hp
    exact pow_ne_zero _ (P.prime_mem p hp).ne_zero

theorem factor_dvd_of_matches {m : ℕ} (hm : m ≠ 0) (hmatch : P.Matches m) :
    P.factor ∣ m := by
  rw [← Nat.factorization_le_iff_dvd P.factor_ne_zero hm]
  intro q
  rw [P.factorization_factor q]
  split_ifs with hq
  · exact (hmatch q hq).ge
  · exact Nat.zero_le _

theorem exponent_le_of_factor_dvd {m p : ℕ} (hm : m ≠ 0)
    (hfac : P.factor ∣ m) (hp : p ∈ P.primes) :
    P.exponent p ≤ m.factorization p := by
  have hle := (Nat.factorization_le_iff_dvd P.factor_ne_zero hm).mpr hfac p
  simpa [P.factorization_factor p, hp] using hle

/-- Prescribing all head valuations is exactly the condition that the forced
prime-power factor divides `m` and that the remaining quotient contains none
of the head primes.  This is the exact finite identity to which Möbius
inclusion--exclusion is later applied. -/
theorem matches_iff_factor_dvd_and_coprime {m : ℕ} (hm : m ≠ 0) :
    P.Matches m ↔
      P.factor ∣ m ∧ Nat.Coprime (m / P.factor) P.modulus := by
  constructor
  · intro hmatch
    have hfac : P.factor ∣ m := P.factor_dvd_of_matches hm hmatch
    refine ⟨hfac, ?_⟩
    rw [modulus, Nat.coprime_prod_right_iff]
    intro p hp
    apply Nat.Coprime.symm
    apply (P.prime_mem p hp).coprime_iff_not_dvd.mpr
    intro hpdvd
    have hquot_ne : m / P.factor ≠ 0 :=
      (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hfac)
        (Nat.pos_of_ne_zero P.factor_ne_zero)).ne'
    have hpos := (P.prime_mem p hp).factorization_pos_of_dvd hquot_ne hpdvd
    have hdiv : (m / P.factor).factorization p =
        m.factorization p - P.factor.factorization p := by
      simpa only [Finsupp.sub_apply] using
        congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div hfac)
    rw [P.factorization_factor p, if_pos hp, hmatch p hp] at hdiv
    have hzero : (m / P.factor).factorization p = 0 := by
      simpa using hdiv
    omega
  · rintro ⟨hfac, hcop⟩
    intro p hp
    have hhead : Nat.Coprime (m / P.factor) p := by
      rw [modulus, Nat.coprime_prod_right_iff] at hcop
      exact hcop p hp
    have hnotdvd : ¬ p ∣ m / P.factor :=
      (P.prime_mem p hp).coprime_iff_not_dvd.mp hhead.symm
    have hzero : (m / P.factor).factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnotdvd
    have hdiv : (m / P.factor).factorization p =
        m.factorization p - P.factor.factorization p := by
      simpa only [Finsupp.sub_apply] using
        congrArg (fun f : ℕ →₀ ℕ ↦ f p) (Nat.factorization_div hfac)
    rw [P.factorization_factor p, if_pos hp] at hdiv
    have hupper : m.factorization p ≤ P.exponent p := by
      apply Nat.sub_eq_zero_iff_le.mp
      exact hdiv.symm.trans hzero
    exact Nat.le_antisymm hupper (P.exponent_le_of_factor_dvd hm hfac hp)

/-- The exact Möbius weight detecting that an integer is coprime to the head
modulus.  Writing it through the gcd avoids any asymptotic or probabilistic
input. -/
def coprimeWeight (k : ℕ) : ℤ :=
  ∑ d ∈ (Nat.gcd k P.modulus).divisors, ArithmeticFunction.moebius d

theorem sum_moebius_divisors {a : ℕ} :
    (∑ d ∈ a.divisors, ArithmeticFunction.moebius d) =
      if a = 1 then 1 else 0 := by
  calc
    (∑ d ∈ a.divisors, ArithmeticFunction.moebius d) =
        (ArithmeticFunction.moebius * ArithmeticFunction.zeta :
          ArithmeticFunction ℤ) a := by
            symm
            simp only [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (1 : ArithmeticFunction ℤ) a := by
      rw [ArithmeticFunction.moebius_mul_coe_zeta]
    _ = if a = 1 then 1 else 0 := by
      rw [ArithmeticFunction.one_apply]

theorem gcd_modulus_ne_zero (k : ℕ) : Nat.gcd k P.modulus ≠ 0 := by
  intro hzero
  have := Nat.gcd_eq_zero_iff.mp hzero
  exact P.modulus_ne_zero this.2

@[simp]
theorem coprimeWeight_eq_indicator (k : ℕ) :
    P.coprimeWeight k = if Nat.Coprime k P.modulus then 1 else 0 := by
  rw [coprimeWeight, sum_moebius_divisors]

theorem divisors_gcd_eq_filter (k : ℕ) :
    (Nat.gcd k P.modulus).divisors =
      P.modulus.divisors.filter (fun d ↦ d ∣ k) := by
  ext d
  simp only [Nat.mem_divisors, Finset.mem_filter]
  constructor
  · rintro ⟨hdgcd, _⟩
    exact ⟨⟨(Nat.dvd_gcd_iff.mp hdgcd).2, P.modulus_ne_zero⟩,
      (Nat.dvd_gcd_iff.mp hdgcd).1⟩
  · rintro ⟨⟨hdmod, _⟩, hdk⟩
    exact ⟨Nat.dvd_gcd hdk hdmod, P.gcd_modulus_ne_zero k⟩

/-- The gcd form of `coprimeWeight` is exactly the usual divisor sum
`∑_{d∣M_H} μ(d) 1_{d∣k}` from the paper. -/
theorem coprimeWeight_eq_divisor_sum (k : ℕ) :
    P.coprimeWeight k =
      ∑ d ∈ P.modulus.divisors,
        if d ∣ k then ArithmeticFunction.moebius d else 0 := by
  rw [coprimeWeight, P.divisors_gcd_eq_filter k, Finset.sum_filter]

/-- The exact head-pattern inclusion--exclusion identity, in integral
indicator form. -/
theorem match_indicator_eq_inclusion_exclusion {m : ℕ} (hm : m ≠ 0) :
    (if P.Matches m then (1 : ℤ) else 0) =
      if P.factor ∣ m then
        ∑ d ∈ P.modulus.divisors,
          if d ∣ m / P.factor then ArithmeticFunction.moebius d else 0
      else 0 := by
  rw [← P.coprimeWeight_eq_divisor_sum (m / P.factor)]
  have hiff := P.matches_iff_factor_dvd_and_coprime hm
  by_cases hmatch : P.Matches m
  · obtain ⟨hfac, hcop⟩ := hiff.mp hmatch
    simp [hmatch, hfac, hcop]
  · by_cases hfac : P.factor ∣ m
    · have hnotcop : ¬ Nat.Coprime (m / P.factor) P.modulus := by
        intro hcop
        exact hmatch (hiff.mpr ⟨hfac, hcop⟩)
      simp [hmatch, hfac, hnotcop]
    · simp [hmatch, hfac]

end Pattern

end Erdos390.Full.HeadPattern
