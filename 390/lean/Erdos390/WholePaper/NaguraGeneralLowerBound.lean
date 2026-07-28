import Erdos390.WholePaper.NaguraGeneralUpperBound

/-!
# The general-integer lower estimate in Nagura's Lemma 2

The three negatively signed factorials are evaluated at floors.  Bounding
each floor between `x / d - 1` and `x / d` costs only one additive unit in
the elementary factorial majorant.  The positively signed `n / 30` term
uses the same shifted Stirling minorant as the general upper estimate.
-/

namespace Erdos390.WholePaper

/-- A floor-uniform upper model for `log ((n / d)!)`. -/
noncomputable def naguraFactorialUpperDivCoarseModel (n d : ℕ) : ℝ :=
  let x := (n : ℝ)
  let δ := (d : ℝ)
  x / δ * (Real.log x - Real.log δ) - x / δ +
    (Real.log x - Real.log δ) + 2

theorem naguraFactorialLogUpper_div_le_coarse
    {n d : ℕ} (hd : 0 < d) (hdn : d ≤ n) :
    naguraFactorialLogUpper (n / d) ≤
      naguraFactorialUpperDivCoarseModel n d := by
  let x : ℝ := n
  let δ : ℝ := d
  let q : ℝ := (n / d : ℕ)
  let t : ℝ := x / δ
  have hdR : 0 < δ := by
    dsimp only [δ]
    exact_mod_cast hd
  have hxR : 0 < x := by
    dsimp only [x]
    exact_mod_cast (lt_of_lt_of_le hd hdn)
  have hqPosNat : 0 < n / d := Nat.div_pos hdn hd
  have hqPos : 0 < q := by
    dsimp only [q]
    exact_mod_cast hqPosNat
  have hqOneNat : 1 ≤ n / d := by omega
  have hqOne : 1 ≤ q := by
    dsimp only [q]
    exact_mod_cast hqOneNat
  have hMulLe : n / d * d ≤ n := Nat.div_mul_le_self n d
  have hMulLeR : q * δ ≤ x := by
    dsimp only [q, δ, x]
    exact_mod_cast hMulLe
  have hqt : q ≤ t := by
    dsimp only [t]
    exact (le_div_iff₀ hdR).2 hMulLeR
  have hLt : n < d * (n / d + 1) := Nat.lt_mul_div_succ n hd
  have hLtR : x < δ * (q + 1) := by
    dsimp only [x, δ, q]
    exact_mod_cast hLt
  have htq : t < q + 1 := by
    dsimp only [t]
    exact (div_lt_iff₀ hdR).2 (by nlinarith)
  have htOne : 1 ≤ t := hqOne.trans hqt
  have htPos : 0 < t := zero_lt_one.trans_le htOne
  have hLog : Real.log q ≤ Real.log t := Real.log_le_log hqPos hqt
  have hLogQNonneg : 0 ≤ Real.log q := Real.log_nonneg hqOne
  have hMulLog : q * Real.log q ≤ t * Real.log t :=
    mul_le_mul hqt hLog hLogQNonneg htPos.le
  have hLogSplit : Real.log t = Real.log x - Real.log δ := by
    dsimp only [t]
    exact Real.log_div (ne_of_gt hxR) (ne_of_gt hdR)
  simp only [naguraFactorialLogUpper,
    naguraFactorialUpperDivCoarseModel]
  change
    q * Real.log q - q + Real.log q + 1 ≤
      t * (Real.log x - Real.log δ) - t +
        (Real.log x - Real.log δ) + 2
  rw [← hLogSplit]
  linarith

/-- A lower model for the arbitrary-endpoint `2,3,5,30` combination. -/
noncomputable def naguraGeneralLowerModel (n : ℕ) : ℝ :=
  naguraFactorialLogLower n - naguraFactorialUpperDivCoarseModel n 2 -
    naguraFactorialUpperDivCoarseModel n 3 -
      naguraFactorialUpperDivCoarseModel n 5 +
        naguraFloorFactorialCoarseModel n 30

theorem naguraGeneralLowerModel_le_combination
    {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralLowerModel n ≤ naguraLowerChebyshevCombination n := by
  have hn0 : n ≠ 0 := by omega
  have h30 : n / 30 ≠ 0 := by omega
  have hLower := naguraFactorialLogLower_le_log_factorial hn0
  have h2Upper := log_factorial_le_naguraFactorialLogUpper
    (show n / 2 ≠ 0 by omega)
  have h3Upper := log_factorial_le_naguraFactorialLogUpper
    (show n / 3 ≠ 0 by omega)
  have h5Upper := log_factorial_le_naguraFactorialLogUpper
    (show n / 5 ≠ 0 by omega)
  have h30Lower := naguraFactorialLogLower_le_log_factorial h30
  have h2Coarse := naguraFactorialLogUpper_div_le_coarse
    (n := n) (d := 2) (by norm_num) (by omega)
  have h3Coarse := naguraFactorialLogUpper_div_le_coarse
    (n := n) (d := 3) (by norm_num) (by omega)
  have h5Coarse := naguraFactorialLogUpper_div_le_coarse
    (n := n) (d := 5) (by norm_num) (by omega)
  have h30Floor := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 30) (by norm_num) (by omega)
  have h30Model := naguraFloorFactorialLowerModel_le
    (n := n) (d := 30) (by norm_num) (by omega)
  simp only [naguraLowerChebyshevCombination,
    naguraChebyshevSum_eq_log_factorial]
  unfold naguraGeneralLowerModel
  linarith

/-- The sole rational loss left by the positive `n / 30` floor. -/
noncomputable def naguraLowerRoundingError (x : ℝ) : ℝ :=
  29 / (x - 30 + 1) / 2

/-- Exact expansion of the lower coarse model. -/
theorem naguraGeneralLowerModel_eq {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralLowerModel n =
      (n : ℝ) * naguraLowerMainCoefficient -
        (89 : ℝ) / 30 * Real.log (n : ℝ) +
        Real.log 2 + Real.log 3 + Real.log 5 +
        (7 : ℝ) / 15 * Real.log 30 + Real.log (2 * Real.pi) -
        (209 : ℝ) / 30 - naguraLowerRoundingError n := by
  simp only [naguraGeneralLowerModel, naguraFactorialLogLower,
    naguraFactorialUpperDivCoarseModel,
    naguraFloorFactorialCoarseModel, naguraLowerMainCoefficient,
    naguraLowerRoundingError, Nat.cast_ofNat]
  have hnR : (20000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h29 : (n : ℝ) - 30 + 1 ≠ 0 := by nlinarith
  rw [nagura_floor_coarse_algebra (by norm_num) h29]
  ring

theorem naguraLowerRoundingError_le_half
    {x : ℝ} (hx : 20000 ≤ x) :
    naguraLowerRoundingError x ≤ (1 : ℝ) / 2 := by
  have h : 29 / (x - 30 + 1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  unfold naguraLowerRoundingError
  linarith

/-- The general-integer form of Nagura's second analytic estimate. -/
theorem naguraGeneralLowerCombination_gt_0_916_mul
    {n : ℕ} (hn : 20000 ≤ n) :
    (229 : ℝ) / 250 * (n : ℝ) <
      naguraLowerChebyshevCombination n := by
  have hModel := naguraGeneralLowerModel_le_combination hn
  have hIdentity := naguraGeneralLowerModel_eq hn
  have hnPos : 0 < n := by omega
  have hnR : (20000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hCoefficient := naguraLowerMainCoefficient_gt_0_9209
  have hMain := mul_lt_mul_of_pos_left hCoefficient
    (show 0 < (n : ℝ) by exact_mod_cast hnPos)
  have hLog := log_nat_lt_div_ten_thousand_add_nine hnPos
  have hError := naguraLowerRoundingError_le_half hnR
  have hPositiveLogs :
      0 ≤ Real.log 2 + Real.log 3 + Real.log 5 +
        (7 : ℝ) / 15 * Real.log 30 + Real.log (2 * Real.pi) := by
    have hPi : 0 ≤ Real.log (2 * Real.pi) := by
      apply Real.log_nonneg
      nlinarith [Real.pi_gt_three]
    positivity
  rw [hIdentity] at hModel
  nlinarith

/-- Consequently `ψ(n) > 0.916 n` throughout the analytic tail. -/
theorem psi_nat_gt_0_916_mul {n : ℕ} (hn : 20000 ≤ n) :
    (229 : ℝ) / 250 * (n : ℝ) < Chebyshev.psi (n : ℝ) := by
  exact (naguraGeneralLowerCombination_gt_0_916_mul hn).trans_le
    (naguraLowerChebyshevCombination_le_psi n)

end Erdos390.WholePaper
