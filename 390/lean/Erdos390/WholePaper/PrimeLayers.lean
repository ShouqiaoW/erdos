import Erdos390.WholePaper.Complement

/-!
# Exact prime-layer arithmetic for the lower bound

This file contains only finite identities.  Analytic estimates for the
cardinalities of the layers are kept separate.  Cross-multiplied endpoint
conditions avoid all ambiguity from natural-number division at rational
endpoints.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The moving layer in Section 3.  Its four inequalities are the exact
integer forms of
`M/(2r+2) < p ≤ M/(2r+1)` and `n/(r+1) < p ≤ n/r`. -/
def movingPrimeLayer (n M r : ℕ) : Finset ℕ :=
  (Finset.range (M + 1)).filter fun p =>
    p.Prime ∧
      M < (2 * r + 2) * p ∧
      (2 * r + 1) * p ≤ M ∧
      n < (r + 1) * p ∧
      r * p ≤ n

@[simp] theorem mem_movingPrimeLayer {n M r p : ℕ} :
    p ∈ movingPrimeLayer n M r ↔
      p ≤ M ∧ p.Prime ∧
        M < (2 * r + 2) * p ∧
        (2 * r + 1) * p ≤ M ∧
        n < (r + 1) * p ∧
        r * p ≤ n := by
  simp only [movingPrimeLayer, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff]

theorem movingPrimeLayer_prime {n M r p : ℕ}
    (hp : p ∈ movingPrimeLayer n M r) : p.Prime :=
  (mem_movingPrimeLayer.mp hp).2.1

/-- The first exact floor identity in a moving layer. -/
theorem div_eq_two_mul_add_one_of_mem_movingPrimeLayer {n M r p : ℕ}
    (hp : p ∈ movingPrimeLayer n M r) :
    M / p = 2 * r + 1 := by
  have hpPos : 0 < p := (movingPrimeLayer_prime hp).pos
  have h := mem_movingPrimeLayer.mp hp
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).mpr (by
      simpa [Nat.mul_comm] using h.2.2.1))
  · exact (Nat.le_div_iff_mul_le hpPos).mpr (by
      simpa [Nat.mul_comm] using h.2.2.2.1)

/-- The second exact floor identity in a moving layer. -/
theorem div_eq_row_of_mem_movingPrimeLayer {n M r p : ℕ}
    (hp : p ∈ movingPrimeLayer n M r) :
    n / p = r := by
  have hpPos : 0 < p := (movingPrimeLayer_prime hp).pos
  have h := mem_movingPrimeLayer.mp hp
  apply Nat.le_antisymm
  · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).mpr (by
      simpa [Nat.mul_comm] using h.2.2.2.2.1))
  · exact (Nat.le_div_iff_mul_le hpPos).mpr (by
      simpa [Nat.mul_comm] using h.2.2.2.2.2)

/-- Above the square-root cutoff, Legendre's sum has only its first term. -/
theorem factorial_factorization_eq_div_of_lt_sq {m p : ℕ}
    (hp : p.Prime) (hm : 0 < m) (hmSq : m < p ^ 2) :
    m.factorial.factorization p = m / p := by
  rw [Nat.factorization_factorial hp (Nat.log_lt_of_lt_pow hm.ne' hmSq)]
  simp

/-- A layer prime occurs exactly once in any exact complement-product
representation.  The proof uses the cross-multiplied identity and therefore
does not assume in advance that the rational quotient is a natural number. -/
theorem complementProduct_factorization_eq_one_of_mem_movingPrimeLayer
    {n M r p : ℕ} {selected : Finset ℕ}
    (hn : 0 < n) (hM : 0 < M)
    (hp : p ∈ movingPrimeLayer n M r)
    (hnSq : n < p ^ 2) (hMSq : M < p ^ 2)
    (hselectedPos : ∀ a ∈ selected, 0 < a)
    (hprod : selected.prod id * n.factorial ^ 2 = M.factorial) :
    (selected.prod id).factorization p = 1 := by
  have hpPrime : p.Prime := movingPrimeLayer_prime hp
  have hselectedNe : selected.prod id ≠ 0 :=
    (Finset.prod_pos hselectedPos).ne'
  have hfac := congrArg Nat.factorization hprod
  have hnFac : n.factorial.factorization p = r := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime hn hnSq,
      div_eq_row_of_mem_movingPrimeLayer hp]
  have hMFac : M.factorial.factorization p = 2 * r + 1 := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime hM hMSq,
      div_eq_two_mul_add_one_of_mem_movingPrimeLayer hp]
  rw [Nat.factorization_mul hselectedNe (pow_ne_zero 2 (Nat.factorial_ne_zero n)),
    Nat.factorization_pow] at hfac
  have hcoord := congrArg (fun v : ℕ →₀ ℕ => v p) hfac
  simp only [Finsupp.add_apply, Finsupp.smul_apply, nsmul_eq_mul] at hcoord
  rw [hnFac, hMFac] at hcoord
  omega

/-- The exact cofactor range forced by membership in a moving layer. -/
theorem cofactor_range_of_mem_movingPrimeLayer {n M r p q : ℕ}
    (hp : p ∈ movingPrimeLayer n M r)
    (hnpq : n < p * q) (hpqM : p * q ≤ M) :
    r + 1 ≤ q ∧ q ≤ 2 * r + 1 := by
  have hpPos : 0 < p := (movingPrimeLayer_prime hp).pos
  constructor
  · by_contra hq
    have hqr : q ≤ r := by omega
    have : p * q ≤ n := by
      calc
        p * q ≤ p * r := Nat.mul_le_mul_left p hqr
        _ = r * p := Nat.mul_comm _ _
        _ ≤ n := (mem_movingPrimeLayer.mp hp).2.2.2.2.2
    omega
  · rw [← div_eq_two_mul_add_one_of_mem_movingPrimeLayer hp]
    exact (Nat.le_div_iff_mul_le hpPos).mpr (by
      simpa [Nat.mul_comm] using hpqM)

end

end Erdos390.WholePaper
