import Erdos390.WholePaper.NaguraExplicitPsiBounds

/-!
# A floor-uniform upper model for Nagura's first combination

This is the general-integer counterpart of the exact `1806 k` calculation.
For each denominator, `floor (n / d)` is replaced by a real lower endpoint;
all rounding losses remain explicit.
-/

namespace Erdos390.WholePaper

/-- Nagura's first combination at an arbitrary natural endpoint. -/
noncomputable def naguraGeneralUpperCombination (n : ℕ) : ℝ :=
  naguraChebyshevSum n - naguraChebyshevSum (n / 2) -
    naguraChebyshevSum (n / 3) - naguraChebyshevSum (n / 7) -
      naguraChebyshevSum (n / 43) - naguraChebyshevSum (n / 1806)

/-- A real lower model for the Stirling expression at `floor (n / d)`.
The quantity `(n - d + 1) / d` is a lower bound for that floor. -/
noncomputable def naguraFloorFactorialLowerModel (n d : ℕ) : ℝ :=
  let x := (n : ℝ)
  let y := (x - (d : ℝ) + 1) / (d : ℝ)
  y * Real.log y - x / (d : ℝ) + Real.log y / 2 +
    Real.log (2 * Real.pi) / 2

/-- The real lower model lies below the proved Stirling model at the natural
floor. -/
theorem naguraFloorFactorialLowerModel_le
    {n d : ℕ} (hd : 0 < d) (hnd : 2 * d ≤ n + 1) :
    naguraFloorFactorialLowerModel n d ≤
      naguraFactorialLogLower (n / d) := by
  let x : ℝ := n
  let q : ℝ := (n / d : ℕ)
  let y : ℝ := (x - d + 1) / d
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hMulLe : n / d * d ≤ n := Nat.div_mul_le_self n d
  have hLt : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
  have hLowerNat : n + 1 ≤ d * (n / d + 1) := by omega
  have hMulLeR : q * (d : ℝ) ≤ x := by
    dsimp only [q, x]
    exact_mod_cast hMulLe
  have hLowerR : (n : ℝ) + 1 ≤ (d : ℝ) * ((n / d : ℕ) + 1) := by
    exact_mod_cast hLowerNat
  have hqy : y ≤ q := by
    dsimp only [y, q, x]
    apply (div_le_iff₀ hdR).2
    nlinarith
  have hqUpper : q ≤ x / d := by
    apply (le_div_iff₀ hdR).2
    exact hMulLeR
  have hyOne : 1 ≤ y := by
    have hndR : 2 * (d : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hnd
    dsimp only [y, x]
    apply (le_div_iff₀ hdR).2
    nlinarith
  have hyPos : 0 < y := zero_lt_one.trans_le hyOne
  have hLog : Real.log y ≤ Real.log q :=
    Real.log_le_log hyPos hqy
  have hLogNonneg : 0 ≤ Real.log y := Real.log_nonneg hyOne
  have hqNonneg : 0 ≤ q := by positivity
  have hMulLog : y * Real.log y ≤ q * Real.log q :=
    mul_le_mul hqy hLog hLogNonneg hqNonneg
  simp only [naguraFloorFactorialLowerModel, naguraFactorialLogLower]
  change
    y * Real.log y - x / d + Real.log y / 2 +
        Real.log (2 * Real.pi) / 2 ≤
      q * Real.log q - q + Real.log q / 2 +
        Real.log (2 * Real.pi) / 2
  linarith

/-- Stirling upper model for the arbitrary-endpoint combination. -/
noncomputable def naguraGeneralUpperModel (n : ℕ) : ℝ :=
  naguraFactorialLogUpper n - naguraFloorFactorialLowerModel n 2 -
    naguraFloorFactorialLowerModel n 3 - naguraFloorFactorialLowerModel n 7 -
      naguraFloorFactorialLowerModel n 43 -
        naguraFloorFactorialLowerModel n 1806

theorem naguraGeneralUpperCombination_le_model
    {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralUpperCombination n ≤ naguraGeneralUpperModel n := by
  have hn0 : n ≠ 0 := by omega
  have h2 : n / 2 ≠ 0 := by omega
  have h3 : n / 3 ≠ 0 := by omega
  have h7 : n / 7 ≠ 0 := by omega
  have h43 : n / 43 ≠ 0 := by omega
  have h1806 : n / 1806 ≠ 0 := by omega
  have hUpper := log_factorial_le_naguraFactorialLogUpper hn0
  have h2Stirling := naguraFactorialLogLower_le_log_factorial h2
  have h3Stirling := naguraFactorialLogLower_le_log_factorial h3
  have h7Stirling := naguraFactorialLogLower_le_log_factorial h7
  have h43Stirling := naguraFactorialLogLower_le_log_factorial h43
  have h1806Stirling := naguraFactorialLogLower_le_log_factorial h1806
  have h2Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 2) (by norm_num) (by omega)
  have h3Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 3) (by norm_num) (by omega)
  have h7Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 7) (by norm_num) (by omega)
  have h43Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 43) (by norm_num) (by omega)
  have h1806Floor := naguraFloorFactorialLowerModel_le
    (n := n) (d := 1806) (by norm_num) (by omega)
  simp only [naguraGeneralUpperCombination, naguraChebyshevSum_eq_log_factorial]
  unfold naguraGeneralUpperModel
  linarith

end Erdos390.WholePaper
