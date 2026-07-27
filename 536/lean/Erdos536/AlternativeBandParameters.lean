import Erdos536.AlternativeBandFlattening

/-!
# Elementary parameter choices for alternative bands

These lemmas remove the final Archimedean bookkeeping from the
alternative-band construction.
-/

namespace Erdos536

/-- A sufficiently large finite number of alternatives makes a uniform
second-moment bound have arbitrarily small square-root error. -/
theorem exists_alternativeCount_sqrt_div_lt
    {K ε : ℝ} (hK : 0 ≤ K) (hε : 0 < ε) :
    ∃ M : ℕ, 0 < M ∧ Real.sqrt (K / (M : ℝ)) < ε := by
  obtain ⟨M, hM⟩ := exists_nat_gt (K / ε ^ 2)
  have hquot : 0 ≤ K / ε ^ 2 := div_nonneg hK (sq_nonneg ε)
  have hMpos : 0 < M := by
    exact_mod_cast hquot.trans_lt hM
  have hMreal : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hratio : K / (M : ℝ) < ε ^ 2 := by
    rw [div_lt_iff₀ hMreal]
    have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
    have := (div_lt_iff₀ hεsq).mp hM
    nlinarith
  refine ⟨M, hMpos, ?_⟩
  exact (Real.sqrt_lt' hε).2 hratio

/-- The logarithmic tolerance whose exponential multiplicative error is
exactly `δ`. -/
theorem exists_logTolerance_exp_sub_one_eq
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ η : ℝ, 0 < η ∧ Real.exp η - 1 = δ := by
  refine ⟨Real.log (1 + δ), Real.log_pos (by linarith), ?_⟩
  rw [Real.exp_log (by linarith : (0 : ℝ) < 1 + δ)]
  ring

end Erdos536
