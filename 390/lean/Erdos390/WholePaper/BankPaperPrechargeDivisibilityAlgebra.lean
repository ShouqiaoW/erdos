import Erdos390.WholePaper.BankPaperPrecharge
import Erdos390.WholePaper.CentralAnchorGuardedCertificate

/-!
# Divisibility algebra for the precharged bank

The guarded central divisor has fixed prime support.  Above the moving rough
cutoff, the precharged base product has exactly the donor-product valuations,
and that donor product is a literal subset-product of the factorial tail.
Consequently the only remaining capacity obligation is the displayed finite
range of primes up to `yNat n`.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Coordinatewise divisibility with one cutoff.  The first factor vanishes
above the cutoff; below it the two valuation demands are charged together. -/
theorem mul_dvd_of_factorization_split
    {D B T cutoff : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hT : 0 < T)
    (hDhigh : ∀ p, p.Prime → cutoff < p → D.factorization p = 0)
    (hlow : ∀ p, p.Prime → p ≤ cutoff →
      D.factorization p + B.factorization p ≤ T.factorization p)
    (hhigh : ∀ p, p.Prime → cutoff < p →
      B.factorization p ≤ T.factorization p) :
    D * B ∣ T := by
  rw [← Nat.factorization_le_iff_dvd
    (mul_ne_zero hD.ne' hB.ne') hT.ne']
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul hD.ne' hB.ne', Finsupp.add_apply]
    by_cases hpCutoff : p ≤ cutoff
    · exact hlow p hp hpCutoff
    · rw [hDhigh p hp (Nat.lt_of_not_ge hpCutoff), zero_add]
      exact hhigh p hp (Nat.lt_of_not_ge hpCutoff)
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- High coordinates may be discharged by comparison with a positive donor
product which already divides the target. -/
theorem mul_dvd_of_factorization_split_with_donor
    {D B donor T cutoff : ℕ}
    (hD : 0 < D) (hB : 0 < B) (hdonor : 0 < donor) (hT : 0 < T)
    (hdonorDvd : donor ∣ T)
    (hDhigh : ∀ p, p.Prime → cutoff < p → D.factorization p = 0)
    (hbaseDonor : ∀ p, p.Prime → cutoff < p →
      B.factorization p = donor.factorization p)
    (hlow : ∀ p, p.Prime → p ≤ cutoff →
      D.factorization p + B.factorization p ≤ T.factorization p) :
    D * B ∣ T := by
  apply mul_dvd_of_factorization_split hD hB hT hDhigh hlow
  intro p hp hpCutoff
  rw [hbaseDonor p hp hpCutoff]
  exact (Nat.factorization_le_iff_dvd hdonor.ne' hT.ne').mpr
    hdonorDvd p

namespace GuardedCentralAnchorCertificate

/-- The exact paper specialization.  Once low-prime capacity is supplied,
the guarded anchor divisor times the actual precharge product divides the
literal upper-tail product. -/
theorem mul_prechargeBaseStateProduct_dvd_centralTailProduct
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hsupportCutoff : 2 * depth + 1 ≤ yNat n)
    (hlow : ∀ p, p.Prime → p ≤ yNat n →
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p +
        (R.prechargeBaseStateProduct).factorization p ≤
      (centralTailProduct n
        (upperTailLength c n)).factorization p) :
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q *
        R.prechargeBaseStateProduct ∣
      centralTailProduct n (upperTailLength c n) := by
  let D : ℕ := centralAnchorDivisor n
    (centralAnchorCutoff depth n) certificate.q
  let B : ℕ := R.prechargeBaseStateProduct
  let donor : ℕ := R.prechargeDonorSet.prod id
  let T : ℕ := centralTailProduct n (upperTailLength c n)
  have hD : 0 < D := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have hB : 0 < B := by
    dsimp [B, BankPaperRealization.prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hdonor : 0 < donor := by
    dsimp [donor]
    apply Finset.prod_pos
    intro factor hfactor
    exact Nat.zero_lt_of_lt
      (Finset.mem_Ioc.mp (R.prechargeDonorSet_subset_tail hfactor)).1
  have hT : 0 < T := by
    exact centralTailProduct_pos n (upperTailLength c n)
  have hdonorDvd : donor ∣ T := by
    exact R.prechargeDonorSet_prod_dvd_centralTailProduct
  have hDhigh : ∀ p, p.Prime → yNat n < p →
      D.factorization p = 0 := by
    intro p hp hpHigh
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpDvd
    have hpPrefix := certificate.divisor_prime_support p hp hpDvd
    have hpLe : p ≤ 2 * depth + 1 := (mem_primesUpTo.mp hpPrefix).2
    omega
  have hbaseDonor : ∀ p, p.Prime → yNat n < p →
      B.factorization p = donor.factorization p := by
    intro p _hp hpHigh
    exact R.prechargeBaseStateProduct_factorization_eq_donorSet_prod
      hpHigh
  exact mul_dvd_of_factorization_split_with_donor
    hD hB hdonor hT hdonorDvd hDhigh hbaseDonor hlow

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper
