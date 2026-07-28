import Erdos390.Full.OmittedTiltPairChamber

/-!
# Exact max-exponent form of the two-local restoration

The numerator in the exact two-local quotient contains the product of a
forced event `p^r q^s | m` and a local-restoration event `p^a q^b | m`.
This file proves, without a squarefree shortcut, that their least common
multiple is `p^(max r a) q^(max s b)`, and rewrites the full tilted
probability in precisely the finite `N_{r,s}/N_{0,0}` form used in the
paper.
-/

open scoped BigOperators

namespace Erdos390.Full.TwoLocalPairRestoration

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds LocalFugacity LocalFugacityRestoration
open ValuationCutoff TwoLocalRestoration OmittedTiltPairChamber

noncomputable section

private theorem primePowerPair_coprime {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    Nat.Coprime (p ^ r) (q ^ s) := by
  have hpqCop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hpq
  exact hpqCop.pow r s

/-- The literal least common multiple of two products supported on the same
two distinct primes is obtained by taking the maximum in each exponent. -/
theorem lcm_pairPower_pairPower {p q r s a b : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    Nat.lcm (pairPower p q r s) (pairPower p q a b) =
      pairPower p q (max r a) (max s b) := by
  apply Nat.dvd_antisymm
  · apply Nat.lcm_dvd
    · unfold pairPower
      apply (primePowerPair_coprime hpq hp hq).mul_dvd_of_dvd_of_dvd
      · exact (Nat.pow_dvd_pow p (le_max_left r a)).trans
          (dvd_mul_right (p ^ max r a) (q ^ max s b))
      · exact (Nat.pow_dvd_pow q (le_max_left s b)).trans
          (dvd_mul_left (q ^ max s b) (p ^ max r a))
    · unfold pairPower
      apply (primePowerPair_coprime hpq hp hq).mul_dvd_of_dvd_of_dvd
      · exact (Nat.pow_dvd_pow p (le_max_right r a)).trans
          (dvd_mul_right (p ^ max r a) (q ^ max s b))
      · exact (Nat.pow_dvd_pow q (le_max_right s b)).trans
          (dvd_mul_left (q ^ max s b) (p ^ max r a))
  · unfold pairPower
    have hpMax : p ^ max r a ∣
        Nat.lcm (p ^ r * q ^ s) (p ^ a * q ^ b) := by
      rcases le_total r a with hra | har
      · rw [max_eq_right hra]
        exact (dvd_mul_right (p ^ a) (q ^ b)).trans
          (Nat.dvd_lcm_right (p ^ r * q ^ s) (p ^ a * q ^ b))
      · rw [max_eq_left har]
        exact (dvd_mul_right (p ^ r) (q ^ s)).trans
          (Nat.dvd_lcm_left (p ^ r * q ^ s) (p ^ a * q ^ b))
    have hqMax : q ^ max s b ∣
        Nat.lcm (p ^ r * q ^ s) (p ^ a * q ^ b) := by
      rcases le_total s b with hsb | hbs
      · rw [max_eq_right hsb]
        exact (dvd_mul_left (q ^ b) (p ^ a)).trans
          (Nat.dvd_lcm_right (p ^ r * q ^ s) (p ^ a * q ^ b))
      · rw [max_eq_left hbs]
        exact (dvd_mul_left (q ^ s) (p ^ r)).trans
          (Nat.dvd_lcm_left (p ^ r * q ^ s) (p ^ a * q ^ b))
    exact (primePowerPair_coprime hpq hp hq).mul_dvd_of_dvd_of_dvd
      hpMax hqMax

/-- Pointwise max-exponent identity for the actual divisor indicators. -/
theorem divInd_pairPower_mul {p q r s a b m : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    divInd (pairPower p q r s) m * divInd (pairPower p q a b) m =
      divInd (pairPower p q (max r a) (max s b)) m := by
  rw [divInd_mul_eq_lcm, lcm_pairPower_pairPower hpq hp hq]

section Cell

variable {S : Finset ℕ}

/-- The paper's exact finite `N_{r,s}/N_{0,0}` identity for an actual
structured-cell law.  All local exponent cutoffs remain literal. -/
theorem fullTilt_pairPower_eq_maxExponent_ratio
    (hS : S.Nonempty) (P : Finset ℕ) (eta : ℕ → ℝ)
    {L : ℝ} {M p q r s : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (hp : p.Prime) (hq : q.Prime)
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    let omitted := (uniformOnFinset S hS).exponentialTilt
      (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd (pairPower p q r s) m) =
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦
                divInd (pairPower p q (max r a) (max s b)) m)) /
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦ divInd (pairPower p q a b) m)) := by
  dsimp only
  let omitted := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
  rw [fullTilt_divInd_eq_twoLocal_indicator_ratio hS P eta hpP hqP hpq
    hp hq hSpos hSle]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  congr 3
  funext m
  simpa only [pairPower] using
    divInd_pairPower_mul (m := (m : ℕ)) hpq hp hq

end Cell

end

end Erdos390.Full.TwoLocalPairRestoration
