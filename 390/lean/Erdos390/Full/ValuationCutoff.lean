import Erdos390.Full.LocalFugacityRestoration
import Erdos390.Full.LocalFugacityBounds
import Mathlib.Data.Nat.Log

/-!
# The actual logarithmic valuation cutoff

The local fugacity expansion must be truncated at
`floor(log M / log p)`, not at the much larger physical endpoint `M`.
This module identifies Mathlib's `Nat.log p M` as a valid common cutoff for
all positive integers `m ≤ M`, proves the exact restored factor at that
cutoff, and compares it with the real logarithmic ratio used in the paper.
-/

namespace Erdos390.Full.ValuationCutoff

open ArithmeticModel LocalFugacityRestoration

noncomputable section

/-- The largest possible exponent of `p` below the physical endpoint `M`. -/
def valuationCutoff (p M : ℕ) : ℕ := Nat.log p M

/-- Every actual `p`-adic valuation in `(0,M]` is below the logarithmic
cutoff. -/
theorem factorization_le_valuationCutoff
    {p m M : ℕ} (hp : p.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    m.factorization p ≤ valuationCutoff p M := by
  have hdvd : p ^ m.factorization p ∣ m :=
    (hp.pow_dvd_iff_le_factorization hm.ne').2 le_rfl
  have hpowm : p ^ m.factorization p ≤ m := Nat.le_of_dvd hm hdvd
  exact Nat.le_log_of_pow_le hp.one_lt (hpowm.trans hmM)

/-- The finite local factor at the logarithmic cutoff is literally the
required valuation fugacity. -/
theorem localFactor_valuationCutoff_eq
    {p m M : ℕ} (lam : ℝ) (hp : p.Prime)
    (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p (valuationCutoff p M) lam m =
      lam ^ m.factorization p := by
  exact localFactor_eq_pow_valuation lam hp hm
    (factorization_le_valuationCutoff hp hm hmM)

/-- Exponential form of the exact logarithmically truncated local factor. -/
theorem localFactor_valuationCutoff_exp_eq
    {p m M : ℕ} (eta L : ℝ) (hp : p.Prime)
    (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p (valuationCutoff p M) (Real.exp (eta / L)) m =
      Real.exp (eta / L * valuation p m) := by
  rw [localFactor_valuationCutoff_eq (Real.exp (eta / L)) hp hm hmM]
  rw [valuation, mul_comm, Real.exp_nat_mul]

/-- The natural logarithmic cutoff is no larger than the corresponding real
logarithmic ratio. -/
theorem cast_valuationCutoff_le_log_ratio
    {p M : ℕ} (hp : 1 < p) (hM : 0 < M) :
    (valuationCutoff p M : ℝ) ≤
      Real.log (M : ℝ) / Real.log (p : ℝ) := by
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpR
  have hpowNat : p ^ valuationCutoff p M ≤ M := by
    exact Nat.pow_log_le_self p hM.ne'
  have hpowPos : (0 : ℝ) < ((p ^ valuationCutoff p M : ℕ) : ℝ) := by
    positivity
  have hpowCast : ((p ^ valuationCutoff p M : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hpowNat
  have hlog := Real.log_le_log hpowPos hpowCast
  norm_num only [Nat.cast_pow] at hlog
  rw [Real.log_pow] at hlog
  apply (le_div_iff₀ hlogp).2
  simpa [mul_comm] using hlog

/-- Monotonicity in the physical endpoint. -/
theorem valuationCutoff_mono_right {p M N : ℕ} (hMN : M ≤ N) :
    valuationCutoff p M ≤ valuationCutoff p N := by
  exact Nat.log_mono_right hMN

end

end Erdos390.Full.ValuationCutoff
