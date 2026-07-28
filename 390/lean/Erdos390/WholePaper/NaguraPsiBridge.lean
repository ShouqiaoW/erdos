import Erdos390.WholePaper.Nagura

/-!
# The Chebyshev-function bridge in Nagura's argument

This file isolates the assumption-free combinatorial part of Nagura's
explicit proof.  Strict growth of `Chebyshev.theta` across a natural interval
forces a prime in that interval.  Mathlib's proved comparison between
`Chebyshev.psi` and `Chebyshev.theta` then turns a concrete `psi` gap into the
strict natural-number Nagura conclusion.

No explicit estimate for `psi` is assumed globally here.  Proving the concrete
gap in `hasNaguraPrime_of_psi_gap` uniformly is precisely the remaining
effective analytic step.
-/

namespace Erdos390.WholePaper

/-- Largest natural upper endpoint that is certainly strictly below `6n/5`. -/
def naguraStrictUpper (n : ℕ) : ℕ :=
  (6 * n - 1) / 5

theorem naguraStrictUpper_spec {n : ℕ} (hn : 25 ≤ n) :
    n < naguraStrictUpper n ∧ 5 * naguraStrictUpper n < 6 * n := by
  constructor
  · have hdiv : n + 1 ≤ (6 * n - 1) / 5 := by
      rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 5)]
      omega
    simpa only [naguraStrictUpper, Nat.lt_iff_add_one_le] using hdiv
  · have hmul : 5 * ((6 * n - 1) / 5) ≤ 6 * n - 1 := by
      rw [mul_comm]
      exact Nat.div_mul_le_self (6 * n - 1) 5
    simpa only [naguraStrictUpper] using hmul.trans_lt (by omega)

/-- A strict increase of `theta` between natural endpoints detects an actual
prime in the corresponding half-open interval. -/
theorem exists_prime_Ioc_of_theta_lt {a b : ℕ}
    (hTheta : Chebyshev.theta (a : ℝ) < Chebyshev.theta (b : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  have hab : a ≤ b := by
    by_contra hba
    have hba' : b ≤ a := Nat.le_of_not_ge hba
    have hmono :
        Chebyshev.theta (b : ℝ) ≤ Chebyshev.theta (a : ℝ) :=
      Chebyshev.theta_mono (by exact_mod_cast hba')
    exact (not_lt_of_ge hmono) hTheta
  by_contra hNoPrime
  have hNoPrime' :
      ∀ p : ℕ, p.Prime → a < p → p ≤ b → False := by
    intro p hpPrime hap hpb
    exact hNoPrime ⟨p, hpPrime, hap, hpb⟩
  have hFinset :
      (Finset.Icc 0 a).filter Nat.Prime =
        (Finset.Icc 0 b).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hpZero, hpa⟩, hpPrime⟩
      exact ⟨⟨hpZero, hpa.trans hab⟩, hpPrime⟩
    · rintro ⟨⟨hpZero, hpb⟩, hpPrime⟩
      have hpa : p ≤ a := by
        by_contra hap
        exact hNoPrime' p hpPrime (Nat.lt_of_not_ge hap) hpb
      exact ⟨⟨hpZero, hpa⟩, hpPrime⟩
  have hThetaEq :
      Chebyshev.theta (a : ℝ) = Chebyshev.theta (b : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
    simpa only [Nat.floor_natCast] using congrArg
      (fun s : Finset ℕ => ∑ p ∈ s, Real.log p) hFinset
  exact (ne_of_lt hTheta) hThetaEq

/-- A concrete Chebyshev `psi` gap implies the strict natural-number Nagura
conclusion.  The error term is the already-proved Mathlib comparison
`|psi y - theta y| ≤ 2 sqrt(y) log(y)`. -/
theorem hasNaguraPrime_of_psi_gap {n : ℕ} (hn : 25 ≤ n)
    (hPsiGap :
      Chebyshev.psi (n : ℝ) +
          2 * Real.sqrt (naguraStrictUpper n : ℝ) *
            Real.log (naguraStrictUpper n : ℝ) <
        Chebyshev.psi (naguraStrictUpper n : ℝ)) :
    HasNaguraPrime n := by
  have hUpperSpec := naguraStrictUpper_spec hn
  have hUpperOne : (1 : ℝ) ≤ naguraStrictUpper n := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (by omega))
  have hPsiTheta :=
    Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hUpperOne
  have hErrorUpper :
      Chebyshev.psi (naguraStrictUpper n : ℝ) -
          Chebyshev.theta (naguraStrictUpper n : ℝ) ≤
        2 * Real.sqrt (naguraStrictUpper n : ℝ) *
          Real.log (naguraStrictUpper n : ℝ) :=
    (le_abs_self _).trans hPsiTheta
  have hThetaPsi :
      Chebyshev.theta (n : ℝ) ≤ Chebyshev.psi (n : ℝ) :=
    Chebyshev.theta_le_psi (n : ℝ)
  have hThetaGap :
      Chebyshev.theta (n : ℝ) <
        Chebyshev.theta (naguraStrictUpper n : ℝ) := by
    linarith
  obtain ⟨p, hpPrime, hnp, hpUpper⟩ :=
    exists_prime_Ioc_of_theta_lt hThetaGap
  refine ⟨p, hpPrime, hnp, ?_⟩
  exact lt_of_le_of_lt (Nat.mul_le_mul_left 5 hpUpper) hUpperSpec.2

end Erdos390.WholePaper
