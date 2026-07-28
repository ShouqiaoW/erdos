import Erdos390.Full.ArithmeticModel

/-!
# Exact restoration of one local fugacity

This proves the finite telescoping identity used when an omitted prime is
restored in the tilted measure.  The coefficients are the actual
`λ^a-λ^(a-1)` coefficients and the indicators are actual divisibility
indicators.
-/

open scoped BigOperators

namespace Erdos390.Full.LocalFugacity

open ArithmeticModel

def coefficient (lam : ℝ) (a : ℕ) : ℝ :=
  if a = 0 then 1 else lam ^ a - lam ^ (a - 1)

@[simp] theorem coefficient_zero (lam : ℝ) : coefficient lam 0 = 1 := by
  simp [coefficient]

theorem coefficient_pos (lam : ℝ) {a : ℕ} (ha : 0 < a) :
    coefficient lam a = lam ^ a - lam ^ (a - 1) := by
  simp [coefficient, ha.ne']

/-- A literal coefficient bound for a compact logarithmic fugacity.  It is
stated first in terms of `x`; substituting `x=η/L` gives the paper's
`O(L⁻¹ exp(Ba/L))` estimate. -/
theorem abs_coefficient_exp_le {x : ℝ} {a : ℕ} (ha : 0 < a)
    (hx : |x| ≤ 1) :
    |coefficient (Real.exp x) a| ≤
      2 * |x| * Real.exp (|x| * (a : ℝ)) := by
  rw [coefficient_pos (Real.exp x) ha]
  have ha1 : 1 ≤ a := ha
  have hsplit : (a : ℝ) = ((a - 1 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (Nat.sub_add_cancel ha1).symm
  have hcoeff :
      Real.exp x ^ a - Real.exp x ^ (a - 1) =
        Real.exp (((a - 1 : ℕ) : ℝ) * x) * (Real.exp x - 1) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    rw [hsplit, add_mul, one_mul, Real.exp_add]
    ring
  rw [hcoeff, abs_mul, Real.abs_exp]
  calc
    Real.exp (((a - 1 : ℕ) : ℝ) * x) * |Real.exp x - 1| ≤
        Real.exp (((a - 1 : ℕ) : ℝ) * x) * (2 * |x|) :=
      mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le hx)
        (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (|x| * (a : ℝ)) * (2 * |x|) := by
      apply mul_le_mul_of_nonneg_right
      · apply Real.exp_le_exp.mpr
        have hxle : x ≤ |x| := le_abs_self x
        have hcast : (((a - 1 : ℕ) : ℝ)) ≤ (a : ℝ) := by
          exact_mod_cast Nat.sub_le a 1
        have hnonneg : 0 ≤ (((a - 1 : ℕ) : ℝ)) := by positivity
        have habs : 0 ≤ |x| := abs_nonneg x
        nlinarith
      · positivity
    _ = 2 * |x| * Real.exp (|x| * (a : ℝ)) := by ring

theorem abs_coefficient_exp_div_le {B η L : ℝ} {a : ℕ}
    (ha : 0 < a) (hL : 0 < L) (hBL : B ≤ L)
    (hη : |η| ≤ B) :
    |coefficient (Real.exp (η / L)) a| ≤
      (2 * B / L) * Real.exp (B * (a : ℝ) / L) := by
  have hx : |η / L| ≤ 1 := by
    rw [abs_div, abs_of_pos hL]
    apply (div_le_one hL).mpr
    exact hη.trans hBL
  refine (abs_coefficient_exp_le ha hx).trans ?_
  have hdiv : |η / L| ≤ B / L := by
    rw [abs_div, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hη hL.le
  have hexp :
      Real.exp (|η / L| * (a : ℝ)) ≤
        Real.exp (B * (a : ℝ) / L) := by
    apply Real.exp_le_exp.mpr
    have ha0 : 0 ≤ (a : ℝ) := by positivity
    calc
      |η / L| * (a : ℝ) ≤ (B / L) * (a : ℝ) :=
        mul_le_mul_of_nonneg_right hdiv ha0
      _ = B * (a : ℝ) / L := by ring
  have hleft : 0 ≤ 2 * |η / L| := by positivity
  have hright : 0 ≤ Real.exp (B * (a : ℝ) / L) :=
    (Real.exp_pos _).le
  calc
    2 * |η / L| * Real.exp (|η / L| * (a : ℝ)) ≤
        2 * |η / L| * Real.exp (B * (a : ℝ) / L) :=
      mul_le_mul_of_nonneg_left hexp hleft
    _ ≤ (2 * B / L) * Real.exp (B * (a : ℝ) / L) := by
      apply mul_le_mul_of_nonneg_right _ hright
      calc
        2 * |η / L| ≤ 2 * (B / L) :=
          mul_le_mul_of_nonneg_left hdiv (by norm_num)
        _ = 2 * B / L := by ring

private theorem telescoping_power (lam : ℝ) (v : ℕ) :
    1 + ∑ a ∈ Finset.Icc 1 v, (lam ^ a - lam ^ (a - 1)) = lam ^ v := by
  induction v with
  | zero => simp
  | succ v ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      calc
        1 + ((∑ a ∈ Finset.Icc 1 v, (lam ^ a - lam ^ (a - 1))) +
            (lam ^ (v + 1) - lam ^ (v + 1 - 1))) =
            (1 + ∑ a ∈ Finset.Icc 1 v, (lam ^ a - lam ^ (a - 1))) +
              (lam ^ (v + 1) - lam ^ (v + 1 - 1)) := by ring
        _ = lam ^ v + (lam ^ (v + 1) - lam ^ (v + 1 - 1)) := by rw [ih]
        _ = lam ^ (v + 1) := by
          simp only [Nat.add_sub_cancel, pow_succ]
          ring

/-- The paper's exact local-factor identity, truncated at any exponent `A`
above the actual valuation. -/
theorem pow_valuation_eq_indicator_expansion {p m A : ℕ} (lam : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hA : m.factorization p ≤ A) :
    lam ^ m.factorization p =
      1 + ∑ a ∈ Finset.Icc 1 A,
        coefficient lam a * divInd (p ^ a) m := by
  simp only [divInd, hp.pow_dvd_iff_le_factorization hm.ne']
  have hcoeff :
      (∑ a ∈ Finset.Icc 1 A,
        coefficient lam a * if a ≤ m.factorization p then 1 else 0) =
      ∑ a ∈ Finset.Icc 1 A,
        (lam ^ a - lam ^ (a - 1)) *
          if a ≤ m.factorization p then 1 else 0 := by
    apply Finset.sum_congr rfl
    intro a haMem
    have ha : 0 < a := by
      simp at haMem
      omega
    rw [coefficient_pos lam ha]
  rw [hcoeff]
  simp only [mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  have hfilter :
      (Finset.Icc 1 A).filter (fun a ↦ a ≤ m.factorization p) =
        Finset.Icc 1 (m.factorization p) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilter, telescoping_power]

/-- Rewriting the same identity directly as the exponential factor in the
bridge score. -/
theorem exp_valuation_eq_indicator_expansion {p m A : ℕ} (η L : ℝ)
    (hp : p.Prime) (hm : 0 < m) (hA : m.factorization p ≤ A) :
    Real.exp (η / L * valuation p m) =
      1 + ∑ a ∈ Finset.Icc 1 A,
        coefficient (Real.exp (η / L)) a * divInd (p ^ a) m := by
  rw [valuation]
  have hexp : Real.exp (η / L * (m.factorization p : ℝ)) =
      Real.exp (η / L) ^ m.factorization p := by
    rw [mul_comm, ← Real.exp_nat_mul]
  rw [hexp]
  exact pow_valuation_eq_indicator_expansion (Real.exp (η / L)) hp hm hA

end Erdos390.Full.LocalFugacity
