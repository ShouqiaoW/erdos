import Erdos390.WholePaper.NaguraCombinatorial

/-!
# Nagura's lower Chebyshev combination

The denominators `2, 3, 5, 30` give a second periodic weight whose prefix
sums are always zero or one.  Expanding `ψ` into the von Mangoldt function
therefore shows that the resulting factorial-log combination is at most
`ψ(n)`.
-/

open scoped BigOperators ArithmeticFunction

namespace Erdos390.WholePaper

def naguraLowerWeight (m : ℕ) : ℝ :=
  1 - (if 2 ∣ m then 1 else 0) - (if 3 ∣ m then 1 else 0) -
    (if 5 ∣ m then 1 else 0) + (if 30 ∣ m then 1 else 0)

def naguraLowerWeightPrefix (m : ℕ) : ℝ :=
  (m : ℝ) - (m / 2 : ℕ) - (m / 3 : ℕ) - (m / 5 : ℕ) + (m / 30 : ℕ)

theorem sum_naguraLowerWeight_eq_prefix (m : ℕ) :
    (∑ i ∈ Finset.range m, naguraLowerWeight (i + 1)) =
      naguraLowerWeightPrefix m := by
  simp only [naguraLowerWeight, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  rw [sum_dvd_indicator_eq_div 2,
    sum_dvd_indicator_eq_div 3,
    sum_dvd_indicator_eq_div 5,
    sum_dvd_indicator_eq_div 30]
  rfl

/-- The lower-combination prefix is exactly a zero-one valued function. -/
theorem naguraLowerWeightPrefix_mem_unitInterval (m : ℕ) :
    0 ≤ naguraLowerWeightPrefix m ∧ naguraLowerWeightPrefix m ≤ 1 := by
  let z : ℤ :=
    (m : ℤ) - ((m / 2 : ℕ) : ℤ) - ((m / 3 : ℕ) : ℤ) -
      ((m / 5 : ℕ) : ℤ) + ((m / 30 : ℕ) : ℤ)
  have hInt : 0 ≤ z ∧ z ≤ 1 := by
    dsimp only [z]
    omega
  have hLower : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast hInt.1
  have hUpper : (z : ℝ) ≤ 1 := by exact_mod_cast hInt.2
  dsimp only [z] at hLower hUpper
  push_cast at hLower hUpper
  simpa only [naguraLowerWeightPrefix] using And.intro hLower hUpper

/-- The lower weight, packaged as an arithmetic function so the finite
Dirichlet-convolution reindexing can be reused directly. -/
noncomputable def naguraLowerWeightArithmetic : ArithmeticFunction ℝ :=
  ⟨fun m ↦ if m = 0 then 0 else naguraLowerWeight m, by simp⟩

theorem naguraLowerWeightArithmetic_apply {m : ℕ} (hm : m ≠ 0) :
    naguraLowerWeightArithmetic m = naguraLowerWeight m := by
  simp [naguraLowerWeightArithmetic, hm]

/-- Swap the finite `m,q` divisor region after expanding `ψ` into the von
Mangoldt function. -/
theorem sum_lowerWeight_mul_psi_eq_sum_vonMangoldt_mul_prefix (n : ℕ) :
    (∑ m ∈ Finset.Ioc 0 n,
      naguraLowerWeight m * Chebyshev.psi ((n / m : ℕ) : ℝ)) =
      ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q * naguraLowerWeightPrefix (n / q) := by
  let w := naguraLowerWeightArithmetic
  have h₁ := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (R := ℝ) w ArithmeticFunction.vonMangoldt n
  have h₂ := ArithmeticFunction.sum_Ioc_mul_eq_sum_sum
    (R := ℝ) ArithmeticFunction.vonMangoldt w n
  have hConv :
      (∑ r ∈ Finset.Ioc 0 n, (w * ArithmeticFunction.vonMangoldt) r) =
        ∑ r ∈ Finset.Ioc 0 n, (ArithmeticFunction.vonMangoldt * w) r := by
    simp only [mul_comm]
  rw [h₁] at hConv
  rw [h₂] at hConv
  calc
    (∑ m ∈ Finset.Ioc 0 n,
        naguraLowerWeight m * Chebyshev.psi ((n / m : ℕ) : ℝ)) =
      ∑ m ∈ Finset.Ioc 0 n,
        w m *
          (∑ q ∈ Finset.Ioc 0 (n / m),
            ArithmeticFunction.vonMangoldt q) := by
      apply Finset.sum_congr rfl
      intro m hm
      have hm0 : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Ioc.mp hm).1
      rw [naguraLowerWeightArithmetic_apply hm0]
      simp [Chebyshev.psi]
    _ = ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q *
          (∑ m ∈ Finset.Ioc 0 (n / q), w m) := hConv
    _ = ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q * naguraLowerWeightPrefix (n / q) := by
      apply Finset.sum_congr rfl
      intro q _
      congr 1
      rw [sum_Ioc_zero_eq_sum_range_succ]
      calc
        (∑ i ∈ Finset.range (n / q), w (i + 1)) =
            ∑ i ∈ Finset.range (n / q), naguraLowerWeight (i + 1) := by
          apply Finset.sum_congr rfl
          intro i _
          exact naguraLowerWeightArithmetic_apply (by omega)
        _ = naguraLowerWeightPrefix (n / q) :=
          sum_naguraLowerWeight_eq_prefix (n / q)

/-- Nagura's factorial-log combination used for the lower bound on `ψ`. -/
noncomputable def naguraLowerChebyshevCombination (n : ℕ) : ℝ :=
  naguraChebyshevSum n - naguraChebyshevSum (n / 2) -
    naguraChebyshevSum (n / 3) - naguraChebyshevSum (n / 5) +
      naguraChebyshevSum (n / 30)

theorem sum_naguraLowerWeight_mul_psi_eq_combination (n : ℕ) :
    (∑ i ∈ Finset.range n,
      naguraLowerWeight (i + 1) *
        Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ)) =
      naguraLowerChebyshevCombination n := by
  simp only [naguraLowerWeight, sub_mul, add_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  simp only [ite_mul, one_mul, zero_mul]
  rw [← naguraChebyshevSum_eq_sum_range n,
    sum_dvd_indicator_psi_eq_chebyshevSum 2 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 3 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 5 n,
    sum_dvd_indicator_psi_eq_chebyshevSum 30 n]
  rfl

/-- The combinatorial lower bridge: the `2,3,5,30` factorial combination is
bounded above by `ψ(n)`. -/
theorem naguraLowerChebyshevCombination_le_psi (n : ℕ) :
    naguraLowerChebyshevCombination n ≤ Chebyshev.psi (n : ℝ) := by
  rw [← sum_naguraLowerWeight_mul_psi_eq_combination]
  calc
    (∑ i ∈ Finset.range n,
        naguraLowerWeight (i + 1) *
          Chebyshev.psi ((n / (i + 1) : ℕ) : ℝ)) =
      ∑ m ∈ Finset.Ioc 0 n,
        naguraLowerWeight m * Chebyshev.psi ((n / m : ℕ) : ℝ) := by
      exact (sum_Ioc_zero_eq_sum_range_succ
        (fun m ↦ naguraLowerWeight m *
          Chebyshev.psi ((n / m : ℕ) : ℝ)) n).symm
    _ = ∑ q ∈ Finset.Ioc 0 n,
        ArithmeticFunction.vonMangoldt q * naguraLowerWeightPrefix (n / q) :=
      sum_lowerWeight_mul_psi_eq_sum_vonMangoldt_mul_prefix n
    _ ≤ ∑ q ∈ Finset.Ioc 0 n, ArithmeticFunction.vonMangoldt q := by
      apply Finset.sum_le_sum
      intro q _
      have hΛ := ArithmeticFunction.vonMangoldt_nonneg (n := q)
      have hPrefix := (naguraLowerWeightPrefix_mem_unitInterval (n / q)).2
      nlinarith [mul_le_mul_of_nonneg_left hPrefix hΛ]
    _ = Chebyshev.psi (n : ℝ) := by
      simp [Chebyshev.psi]

end Erdos390.WholePaper
