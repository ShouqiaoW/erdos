import Erdos390.Full.ValuationScoreDomination

/-!
# Actual compact valuation tilts on a finite cell

This file substitutes the genuine valuation score into the omitted-score
comparison.  Both divisor-score moments are discharged by exact
common-multiple counting; no probabilistic independence is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.ValuationTiltCell

open ArithmeticModel DivisibilityMomentBounds FiniteProbability
open OmittedScoreCell ValuationScoreDomination

noncomputable section

/-- A divisor-indicator score is bounded by the number of its moduli. -/
theorem divisorScore_le_card (R : Finset ℕ) (m : ℕ) :
    divisorScore R m ≤ (R.card : ℝ) := by
  unfold divisorScore
  calc
    (∑ a ∈ R, divInd a m) ≤ ∑ a ∈ R, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro a ha
      exact divInd_le_one a m
    _ = (R.card : ℝ) := by simp

/-- The total number of prime factors drawn from primes at least `W` is
bounded by the physical logarithm.  This is the useful compact-score bound;
it is independent of the number of primes in the band. -/
theorem sum_valuation_le_log_ratio
    (P : Finset ℕ) {m M W : ℕ}
    (hm : 0 < m) (hmM : m ≤ M)
    (hW : 1 < W) (hpW : ∀ p ∈ P, W ≤ p) :
    (∑ p ∈ P, valuation p m) ≤
      Real.log (M : ℝ) / Real.log (W : ℝ) := by
  let support : Finset ℕ := m.factorization.support
  let f : ℕ → ℝ := fun p ↦ valuation p m * Real.log (p : ℝ)
  have hsumP : (∑ p ∈ P, f p) = ∑ p ∈ P ∩ support, f p := by
    symm
    apply Finset.sum_subset Finset.inter_subset_left
    intro p hpP hpNotInter
    have hpNotSupport : p ∉ support := by
      intro hpSupport
      exact hpNotInter (Finset.mem_inter.mpr ⟨hpP, hpSupport⟩)
    have hzero : m.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp (by simpa [support] using hpNotSupport)
    simp [f, valuation, hzero]
  have hsubset : P ∩ support ⊆ support := Finset.inter_subset_right
  have hsumSupport : (∑ p ∈ P ∩ support, f p) ≤
      ∑ p ∈ support, f p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hpSupport hpNotInter
    have hpPrime : p.Prime := by
      exact Nat.prime_of_mem_primeFactors (by simpa [support] using hpSupport)
    exact mul_nonneg (valuation_nonneg p m)
      (Real.log_nonneg (by exact_mod_cast hpPrime.one_lt.le))
  have hfactorization : (∑ p ∈ support, f p) = Real.log (m : ℝ) := by
    rw [Real.log_nat_eq_sum_factorization]
    rfl
  have hweighted : Real.log (W : ℝ) * (∑ p ∈ P, valuation p m) ≤
      ∑ p ∈ P, f p := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro p hp
    have hlog : Real.log (W : ℝ) ≤ Real.log (p : ℝ) := by
      apply Real.log_le_log (by exact_mod_cast hW.le)
      exact_mod_cast hpW p hp
    simpa only [f, mul_comm] using
      mul_le_mul_of_nonneg_left hlog (valuation_nonneg p m)
  have hlogmM : Real.log (m : ℝ) ≤ Real.log (M : ℝ) := by
    apply Real.log_le_log (by exact_mod_cast hm)
    exact_mod_cast hmM
  have hlogW : 0 < Real.log (W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  apply (le_div_iff₀ hlogW).2
  calc
    (∑ p ∈ P, valuation p m) * Real.log (W : ℝ) =
        Real.log (W : ℝ) * (∑ p ∈ P, valuation p m) := by ring
    _ ≤ ∑ p ∈ P, f p := hweighted
    _ = ∑ p ∈ P ∩ support, f p := hsumP
    _ ≤ ∑ p ∈ support, f p := hsumSupport
    _ = Real.log (m : ℝ) := hfactorization
    _ ≤ Real.log (M : ℝ) := hlogmM

/-- Uniform bound for the genuine compact valuation score using the physical
logarithm rather than the (much larger) number of prime-power columns. -/
theorem abs_valuationScore_le_log_ratio
    (P : Finset ℕ) (eta : ℕ → ℝ) {m M W : ℕ} {B L : ℝ}
    (hm : 0 < m) (hmM : m ≤ M)
    (hW : 1 < W) (hpW : ∀ p ∈ P, W ≤ p)
    (hB : 0 ≤ B) (hL : 0 < L) (heta : ∀ p ∈ P, |eta p| ≤ B) :
    |valuationScore P eta L m| ≤
      (B / L) * (Real.log (M : ℝ) / Real.log (W : ℝ)) := by
  unfold valuationScore
  calc
    |∑ p ∈ P, (eta p / L) * valuation p m| ≤
        ∑ p ∈ P, |(eta p / L) * valuation p m| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ P, (|eta p| / L) * valuation p m := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [abs_mul, abs_div, abs_of_pos hL,
        abs_of_nonneg (valuation_nonneg p m)]
    _ ≤ ∑ p ∈ P, (B / L) * valuation p m := by
      apply Finset.sum_le_sum
      intro p hp
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (valuation_nonneg p m)
    _ = (B / L) * (∑ p ∈ P, valuation p m) := by
      rw [Finset.mul_sum]
    _ ≤ (B / L) *
        (Real.log (M : ℝ) / Real.log (W : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (sum_valuation_le_log_ratio P hm hmM hW hpW)
        (div_nonneg hB hL.le)

/-- Fully explicit omitted-local-prime comparison for the true compact
valuation tilt.  The only final hypothesis is the displayed smallness
inequality; in the paper it is enforced by choosing the fixed cutoff `W`
before the compact tilt box.
-/
theorem abs_valuationTilt_divInd_sub_average_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D W : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hW : 1 < W)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (hpW : ∀ p ∈ P, W ≤ p)
    (hcop : ∀ p ∈ P, Nat.Coprime D p)
    (heta : ∀ p ∈ P, |eta p| ≤ B)
    (hsmall :
      Real.exp ((B / L) *
          (Real.log (M : ℝ) / Real.log (W : ℝ))) *
          (B / L) *
          ((1 / c) * ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) -
        uniformAverage S (divInd D)| ≤
      (Real.exp ((B / L) *
          (Real.log (M : ℝ) / Real.log (W : ℝ))) *
          (B / L) *
          ((1 / (c * (D : ℝ))) *
            ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) +
        Real.exp ((B / L) *
          (Real.log (M : ℝ) / Real.log (W : ℝ))) *
          uniformAverage S (divInd D) *
          ((B / L) *
            ((1 / c) *
              ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)))) /
        (1 -
          Real.exp ((B / L) *
            (Real.log (M : ℝ) / Real.log (W : ℝ))) *
            (B / L) *
            ((1 / c) *
              ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ))) := by
  let R := primePowerModuli P M
  let beta : ℝ := B / L
  let K : ℝ := beta * (Real.log (M : ℝ) / Real.log (W : ℝ))
  let totalBound : ℝ := (1 / c) * ∑ a ∈ R, 1 / (a : ℝ)
  let markedBound : ℝ :=
    (1 / (c * (D : ℝ))) * ∑ a ∈ R, 1 / (a : ℝ)
  have hbeta : 0 ≤ beta := div_nonneg hB hL.le
  have hRpos : ∀ a ∈ R, 0 < a := by
    intro a ha
    exact pos_of_mem_primePowerModuli hprime (by simpa [R] using ha)
  have hRcop : ∀ a ∈ R, Nat.Coprime D a := by
    intro a ha
    exact coprime_of_mem_primePowerModuli hcop (by simpa [R] using ha)
  have hdom : ∀ m ∈ S,
      |valuationScore P eta L m| ≤ beta * divisorScore R m := by
    intro m hm
    simpa only [beta, R] using
      abs_valuationScore_le_divisorScore P eta hprime (hSpos m hm)
        (hSle m hm) hL heta
  have hscore : ∀ m ∈ S, |valuationScore P eta L m| ≤ K := by
    intro m hm
    simpa only [K, beta] using abs_valuationScore_le_log_ratio P eta
      (hSpos m hm) (hSle m hm) hW hpW hB hL heta
  have htotal : uniformAverage S (divisorScore R) ≤ totalBound := by
    have h := uniformAverage_marked_divisorScore_le S R
      (D := 1) (c := c) (by norm_num) hM hc hcard hSpos hSle hRpos
      (fun a ha ↦ by simp)
    simpa [divInd, totalBound] using h
  have hmarked : uniformAverage S
      (fun m ↦ divInd D m * divisorScore R m) ≤ markedBound := by
    simpa only [markedBound] using
      uniformAverage_marked_divisorScore_le S R hD hM hc hcard
        hSpos hSle hRpos hRcop
  have htotal0 : 0 ≤ totalBound := by
    dsimp only [totalBound]
    positivity
  have hmarked0 : 0 ≤ markedBound := by
    dsimp only [markedBound]
    positivity
  have hsmall' : Real.exp K * beta * totalBound < 1 := by
    simpa only [K, beta, totalBound, R] using hsmall
  simpa only [K, beta, totalBound, markedBound, R] using
    abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
      S R hS D (valuationScore P eta L) hbeta hdom hscore htotal hmarked
      htotal0 hmarked0 hsmall'

end

end Erdos390.Full.ValuationTiltCell
