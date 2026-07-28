import Erdos390.WholePaper.FactorizationIncidence

/-! Exact collision exclusion for the thirteen large-prime layers. -/

namespace Erdos390.WholePaper

/-- An integer below `L²` cannot contain two distinct primes at least `L`. -/
theorem not_two_distinct_large_primes_dvd
    {p q a L B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hLp : L ≤ p) (hLq : L ≤ q)
    (ha : 0 < a) (haB : a ≤ B) (hBL : B < L * L) :
    ¬(p ∣ a ∧ q ∣ a) := by
  rintro ⟨hpa, hqa⟩
  have hpqa : p * q ∣ a := hp.dvd_mul_of_dvd_ne hpq hq hpa hqa
  have hpq_le : p * q ≤ a := Nat.le_of_dvd ha hpqa
  have hLL_le : L * L ≤ p * q := Nat.mul_le_mul hLp hLq
  omega

/-- Consequently, chosen carrier factors for distinct layer primes are
distinct whenever the common physical bound lies below `L²`. -/
theorem carrier_ne_of_distinct_large_primes
    {p q bp bq L B : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hLp : L ≤ p) (hLq : L ≤ q)
    (hbp : 0 < bp) (hbpB : bp ≤ B)
    (hBL : B < L * L)
    (hpBp : p ∣ bp) (hqBq : q ∣ bq) :
    bp ≠ bq := by
  intro hEq
  subst bq
  exact not_two_distinct_large_primes_dvd hp hq hpq hLp hLq
    hbp hbpB hBL ⟨hpBp, hqBq⟩

end Erdos390.WholePaper
