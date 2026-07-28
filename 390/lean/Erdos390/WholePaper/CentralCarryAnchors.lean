import Erdos390.WholePaper.StationaryLayers
import Erdos390.WholePaper.TailValuationCore

/-! # Exact arithmetic of the fixed-prefix central carry anchors -/

namespace Erdos390.WholePaper

noncomputable section

/-- A stationary-layer prime has the two exact floor values displayed in
the paper. -/
theorem stationaryPrimeLayer_floor_values {n r p : ℕ}
    (hp : p ∈ stationaryPrimeLayer n r) :
    n / p = r ∧ (2 * n) / p = 2 * r + 1 := by
  have hmem := mem_stationaryPrimeLayer.mp hp
  have hpPos : 0 < p := hmem.1.pos
  have hrp : r * p ≤ n := by
    have hupper := hmem.2.2
    ring_nf at hupper ⊢
    omega
  have htwoStrict : 2 * n < (2 * r + 2) * p := by
    have hlower := hmem.2.1
    ring_nf at hlower ⊢
    omega
  constructor
  · apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).2 (by
        simpa [Nat.mul_comm] using hmem.2.1))
    · exact (Nat.le_div_iff_mul_le hpPos).2 hrp
  · apply Nat.le_antisymm
    · exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hpPos).2 (by
        simpa [Nat.mul_comm] using htwoStrict))
    · exact (Nat.le_div_iff_mul_le hpPos).2 (by
        simpa [Nat.mul_comm] using hmem.2.2)

/-- Above the square-root cutoff, a stationary-layer prime occurs exactly
once in the central binomial coefficient. -/
theorem centralChoose_factorization_eq_one_of_mem_stationaryPrimeLayer_of_sq
    {n r p : ℕ} (hn : 0 < n)
    (hp : p ∈ stationaryPrimeLayer n r) (hpSq : 2 * n < p ^ 2) :
    (Nat.choose (2 * n) n).factorization p = 1 := by
  have hpPrime : p.Prime := (mem_stationaryPrimeLayer.mp hp).1
  have hfloors := stationaryPrimeLayer_floor_values hp
  have hnSq : n < p ^ 2 := by omega
  have hnFac : n.factorial.factorization p = r := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime hn hnSq,
      hfloors.1]
  have htwoFac : (2 * n).factorial.factorization p = 2 * r + 1 := by
    rw [factorial_factorization_eq_div_of_lt_sq hpPrime (by omega) hpSq,
      hfloors.2]
  have hcentral := centralFactorialValuation_eq_choose_add
    (n := n) (p := p)
  rw [hnFac, htwoFac] at hcentral
  omega

/-- Every allowed allocation cofactor places its carry prime anchor in the
central interval. -/
theorem stationaryPrimeLayer_mul_cofactor_mem_centralInterval
    {n r p q : ℕ} (hp : p ∈ stationaryPrimeLayer n r)
    (hqLower : r + 1 ≤ q) (hqUpper : q ≤ 2 * r + 1) :
    p * q ∈ Finset.Ioc n (2 * n) := by
  have hmem := mem_stationaryPrimeLayer.mp hp
  apply Finset.mem_Ioc.mpr
  constructor
  · exact hmem.2.1.trans_le (Nat.mul_le_mul_left p hqLower)
  · exact (Nat.mul_le_mul_left p hqUpper).trans hmem.2.2

/-- A marker prime above the entire cofactor range is recovered uniquely
from its marker--cofactor product. -/
theorem prime_mul_cofactor_eq_iff_of_marker_large
    {X p p' q q' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (hpLarge : X < p) (hq'Pos : 0 < q') (hq'Upper : q' ≤ X) :
    p * q = p' * q' → p = p' ∧ q = q' := by
  intro hproduct
  have hpDvd : p ∣ p' * q' := by
    rw [← hproduct]
    exact dvd_mul_right p q
  rcases (hp.dvd_mul.mp hpDvd) with hpp' | hpq'
  · have hprimeEq : p = p' :=
      (Nat.prime_dvd_prime_iff_eq hp hp').mp hpp'
    subst p'
    exact ⟨rfl, Nat.mul_left_cancel hp.pos hproduct⟩
  · have hpLeQ : p ≤ q' := Nat.le_of_dvd hq'Pos hpq'
    omega

end

end Erdos390.WholePaper
