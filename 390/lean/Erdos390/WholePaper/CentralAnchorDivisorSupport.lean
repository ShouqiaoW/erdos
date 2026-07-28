import Erdos390.WholePaper.CentralAnchorProduct

/-!
# Prime support and valuations of the central-anchor divisor

The exact anchor product introduces only the promotion power of two and the
chosen carry cofactors.  This file makes that assertion literal at every
prime, so later allocation estimates can be applied directly to the actual
integer divisor.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

theorem routedCentralCofactor_pos
    {n p q : ℕ} (hq : IsRoutedCentralCofactor n p q) : 0 < q := by
  rcases hq with hzero | ⟨r, _hrPos, _hr, _hpRow, hqLower, _hqUpper⟩
  · omega
  · omega

theorem largeCentralCofactor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q)
    {p : ℕ} (hp : p ∈ largeCentralPrimes n X) :
    0 < q p :=
  routedCentralCofactor_pos (hq p hp)

theorem largeCentralCofactorProduct_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < largeCentralCofactorProduct n X q := by
  exact Finset.prod_pos fun p hp ↦ largeCentralCofactor_pos hq hp

theorem centralAnchorDivisor_pos
    {n X : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    0 < centralAnchorDivisor n X q := by
  exact mul_pos (pow_pos (by norm_num : 0 < (2 : ℕ)) _)
    (largeCentralCofactorProduct_pos hq)

/-- Every prime divisor is either the promotion prime `2` or divides one of
the literal chosen cofactors. -/
theorem prime_dvd_centralAnchorDivisor
    {n X ℓ : ℕ} {q : ℕ → ℕ} (hℓ : ℓ.Prime)
    (hdiv : ℓ ∣ centralAnchorDivisor n X q) :
    ℓ = 2 ∨ ∃ p ∈ largeCentralPrimes n X, ℓ ∣ q p := by
  rw [centralAnchorDivisor] at hdiv
  rcases hℓ.dvd_mul.mp hdiv with htwo | hcofactor
  · left
    exact (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp
      (hℓ.dvd_of_dvd_pow htwo)
  · right
    simpa only [largeCentralCofactorProduct] using
      (hℓ.prime.dvd_finset_prod_iff q).mp hcofactor

/-- A uniform cofactor bound gives a literal finite prime support. -/
theorem prime_dvd_centralAnchorDivisor_le
    {n X B ℓ : ℕ} {q : ℕ → ℕ}
    (hqChoice : IsLargeCentralCofactorChoice n X q)
    (hqBound : ∀ p ∈ largeCentralPrimes n X, q p ≤ B)
    (hℓ : ℓ.Prime) (hdiv : ℓ ∣ centralAnchorDivisor n X q) :
    ℓ ≤ max 2 B := by
  rcases prime_dvd_centralAnchorDivisor hℓ hdiv with rfl | ⟨p, hp, hℓq⟩
  · exact le_max_left 2 B
  · have hℓLe : ℓ ≤ q p :=
      Nat.le_of_dvd (largeCentralCofactor_pos hqChoice hp) hℓq
    exact (hℓLe.trans (hqBound p hp)).trans (le_max_right 2 B)

/-- Exact valuation ledger: promotion contributes only at `2`, and every
other contribution is the sum of cofactor valuations. -/
theorem centralAnchorDivisor_factorization
    {n X ℓ : ℕ} {q : ℕ → ℕ}
    (hq : IsLargeCentralCofactorChoice n X q) :
    (centralAnchorDivisor n X q).factorization ℓ =
      (if ℓ = 2 then residualPromotionCost n X else 0) +
        ∑ p ∈ largeCentralPrimes n X, (q p).factorization ℓ := by
  have hcofactorNe : largeCentralCofactorProduct n X q ≠ 0 :=
    (largeCentralCofactorProduct_pos hq).ne'
  have hqNe : ∀ p ∈ largeCentralPrimes n X, q p ≠ 0 :=
    fun p hp ↦ (largeCentralCofactor_pos hq hp).ne'
  rw [centralAnchorDivisor,
    Nat.factorization_mul
      (pow_ne_zero _ (by norm_num : (2 : ℕ) ≠ 0)) hcofactorNe]
  simp only [Finsupp.add_apply, largeCentralCofactorProduct]
  rw [Nat.factorization_prod_apply hqNe]
  by_cases hℓTwo : ℓ = 2
  · subst ℓ
    rw [Nat.factorization_pow_self Nat.prime_two]
    simp
  · have htwoFactorization :
        (2 ^ residualPromotionCost n X).factorization ℓ = 0 := by
      rw [Nat.prime_two.factorization_pow]
      simp [hℓTwo]
    rw [htwoFactorization, if_neg hℓTwo, zero_add]

end

end Erdos390.WholePaper
