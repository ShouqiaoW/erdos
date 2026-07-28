import Mathlib.NumberTheory.AbelSummation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Erdos390.Full.FiniteExponentialFamily

/-!
# Finite logarithmic Stieltjes transfer

The physical column in the marked smooth-number argument is obtained from
uniform prefix-count estimates by Abel summation.  This file isolates the
exact deterministic step.  In particular, the error is charged only once
against the total variation of `log`; it is not multiplied by the number of
integer endpoints or by an auxiliary partition size.
-/

open scoped BigOperators Interval

namespace Erdos390.Full.FiniteLogStieltjes

open Finset MeasureTheory Set

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- Centered mass carried by one integer value of a finite random
variable. -/
def centeredFiberMass (mu : FiniteProbability Omega)
    (value : Omega → ℕ) (A : Omega → ℝ) (k : ℕ) : ℝ :=
  ∑ omega, if value omega = k then
    mu.mass omega * (A omega - mu.expect A) else 0

/-- Summing the centered fiber masses over a finite set is exactly the
centered expectation of its value-preimage. -/
theorem sum_centeredFiberMass_eq
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) (s : Finset ℕ) :
    (∑ k ∈ s, centeredFiberMass mu value A k) =
      ∑ omega, if value omega ∈ s then
        mu.mass omega * (A omega - mu.expect A) else 0 := by
  unfold centeredFiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro omega homega
  by_cases hv : value omega ∈ s
  · rw [if_pos hv]
    rw [Finset.sum_eq_single (value omega)]
    · simp
    · intro k hk hne
      simp [hne.symm]
    · exact fun h ↦ (h hv).elim
  · rw [if_neg hv]
    apply Finset.sum_eq_zero
    intro k hk
    have hne : value omega ≠ k := by
      intro h
      apply hv
      simpa [h] using hk
    simp [hne]

theorem sum_centeredFiberMass_Icc_lo_eq_zero
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {lo : ℕ}
    (hlo : ∀ omega, lo < value omega) :
    ∑ k ∈ Icc 0 lo, centeredFiberMass mu value A k = 0 := by
  rw [sum_centeredFiberMass_eq]
  apply Finset.sum_eq_zero
  intro omega homega
  rw [if_neg]
  intro hmem
  exact (not_le_of_gt (hlo omega)) (Finset.mem_Icc.mp hmem).2

theorem sum_centeredFiberMass_Icc_hi_eq_zero
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {hi : ℕ}
    (hhi : ∀ omega, value omega ≤ hi) :
    ∑ k ∈ Icc 0 hi, centeredFiberMass mu value A k = 0 := by
  rw [sum_centeredFiberMass_eq]
  have hmem (omega : Omega) : value omega ∈ Finset.Icc 0 hi :=
    Finset.mem_Icc.mpr ⟨Nat.zero_le _, hhi omega⟩
  have hremove : (∑ omega, if value omega ∈ Finset.Icc 0 hi then
      mu.mass omega * (A omega - mu.expect A) else 0) =
      ∑ omega, mu.mass omega * (A omega - mu.expect A) := by
    apply Finset.sum_congr rfl
    intro omega homega
    rw [if_pos (hmem omega)]
  rw [hremove]
  unfold FiniteProbability.expect
  calc
    (∑ omega, mu.mass omega *
        (A omega - ∑ eta, mu.mass eta * A eta)) =
        ∑ omega, (mu.mass omega * A omega -
          mu.mass omega * (∑ eta, mu.mass eta * A eta)) := by
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega, mu.mass omega * A omega) -
        (∑ omega, mu.mass omega *
          (∑ eta, mu.mass eta * A eta)) := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ omega, mu.mass omega * A omega) -
        (∑ omega, mu.mass omega) *
          (∑ eta, mu.mass eta * A eta) := by
      rw [← Finset.sum_mul]
    _ = 0 := by
      rw [mu.mass_sum]
      ring

/-- The log-weighted centered fiber sum is the literal covariance with the
integer logarithm. -/
theorem sum_log_centeredFiberMass_eq_covariance
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {lo hi : ℕ}
    (hsupport : ∀ omega, lo < value omega ∧ value omega ≤ hi) :
    (∑ k ∈ Ioc lo hi,
        Real.log (k : ℝ) * centeredFiberMass mu value A k) =
      mu.covariance A (fun omega ↦ Real.log (value omega : ℝ)) := by
  unfold centeredFiberMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner (omega : Omega) :
      (∑ k ∈ Ioc lo hi,
          Real.log (k : ℝ) *
            (if value omega = k then
              mu.mass omega * (A omega - mu.expect A) else 0)) =
        Real.log (value omega : ℝ) *
          (mu.mass omega * (A omega - mu.expect A)) := by
    rw [Finset.sum_eq_single (value omega)]
    · simp
    · intro k hk hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (Finset.mem_Ioc.mpr (hsupport omega))).elim
  simp_rw [hinner]
  unfold FiniteProbability.covariance FiniteProbability.expect
  calc
    (∑ omega,
        Real.log (value omega : ℝ) *
          (mu.mass omega *
            (A omega - ∑ eta, mu.mass eta * A eta))) =
      ∑ omega,
        (mu.mass omega * (A omega * Real.log (value omega : ℝ)) -
          (∑ eta, mu.mass eta * A eta) *
            (mu.mass omega * Real.log (value omega : ℝ))) := by
      apply Finset.sum_congr rfl
      intro omega homega
      ring
    _ = (∑ omega,
        mu.mass omega * (A omega * Real.log (value omega : ℝ))) -
        (∑ omega, (∑ eta, mu.mass eta * A eta) *
          (mu.mass omega * Real.log (value omega : ℝ))) :=
      by rw [Finset.sum_sub_distrib]
    _ = (∑ omega,
        mu.mass omega * (A omega * Real.log (value omega : ℝ))) -
      (∑ eta, mu.mass eta * A eta) *
        (∑ omega, mu.mass omega * Real.log (value omega : ℝ)) := by
      rw [← Finset.mul_sum]

/-- A centered finite sequence whose every prefix is bounded by `E` has a
logarithmically weighted sum bounded by a fixed physical-interval constant.
The two endpoint hypotheses are the exact centered-mass cancellations used
in the covariance application. -/
theorem abs_sum_log_mul_le_of_prefix_bound
    (c : ℕ → ℝ) {lo hi : ℕ} {E : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hE : 0 ≤ E)
    (hprefixLo : ∑ k ∈ Icc 0 lo, c k = 0)
    (hprefixHi : ∑ k ∈ Icc 0 hi, c k = 0)
    (hprefix : ∀ t ∈ Set.Ioc (lo : ℝ) (hi : ℝ),
      |∑ k ∈ Icc 0 ⌊t⌋₊, c k| ≤ E) :
    |∑ k ∈ Ioc lo hi, Real.log (k : ℝ) * c k| ≤
      (E / (lo : ℝ)) * ((hi : ℝ) - (lo : ℝ)) := by
  have hloR : (0 : ℝ) < (lo : ℝ) := by exact_mod_cast hlo
  have hhiR : (0 : ℝ) < (hi : ℝ) := hloR.trans_le (by exact_mod_cast hlohi)
  have hdiff : ∀ t ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      DifferentiableAt ℝ Real.log t := by
    intro t ht
    exact Real.differentiableAt_log (ne_of_gt (hloR.trans_le ht.1))
  have hint : IntegrableOn (deriv Real.log)
      (Set.Icc (lo : ℝ) (hi : ℝ)) := by
    rw [Real.deriv_log']
    exact ((continuousOn_inv₀ (G₀ := ℝ)).mono fun t ht ↦
      Set.mem_compl_singleton_iff.mpr
        (ne_of_gt (hloR.trans_le ht.1))).integrableOn_Icc
  have hAbel := sum_mul_eq_sub_sub_integral_mul'
    c hlohi hdiff hint
  rw [hprefixLo, hprefixHi, mul_zero, mul_zero] at hAbel
  simp only [neg_zero, zero_sub] at hAbel
  rw [hAbel, abs_neg]
  rw [← intervalIntegral.integral_of_le (by exact_mod_cast hlohi)]
  have hbound : ∀ t ∈ Ι (lo : ℝ) (hi : ℝ),
      ‖deriv Real.log t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k‖ ≤ E / (lo : ℝ) := by
    intro t ht
    have htIoc : t ∈ Set.Ioc (lo : ℝ) (hi : ℝ) := by
      rw [Set.uIoc_of_le (by exact_mod_cast hlohi)] at ht
      exact ht
    have htpos : 0 < t := hloR.trans htIoc.1
    have hpref := hprefix t htIoc
    rw [Real.deriv_log, Real.norm_eq_abs, abs_mul, abs_inv,
      abs_of_pos htpos]
    have hinv : t⁻¹ ≤ ((lo : ℝ))⁻¹ := by
      simpa only [one_div] using
        (one_div_le_one_div_of_le hloR htIoc.1.le)
    calc
      t⁻¹ * |∑ k ∈ Icc 0 ⌊t⌋₊, c k| ≤ t⁻¹ * E :=
        mul_le_mul_of_nonneg_left hpref (inv_nonneg.mpr htpos.le)
      _ ≤ ((lo : ℝ))⁻¹ * E :=
        mul_le_mul_of_nonneg_right hinv hE
      _ = E / (lo : ℝ) := by ring
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hsub : 0 ≤ (hi : ℝ) - (lo : ℝ) :=
    sub_nonneg.mpr (by exact_mod_cast hlohi)
  simpa [abs_of_nonneg hsub] using hnorm

end

end Erdos390.Full.FiniteLogStieltjes
