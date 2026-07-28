import Erdos390.WholePaper.NaguraGeneralUpperModel

/-!
# The general-integer upper estimate in Nagura's Lemma 2

All floor losses from the first combination are bounded uniformly.  The
threshold `20000` is intentionally conservative; the already-certified prime
chain covers the lower finite range needed by the final application.
-/

namespace Erdos390.WholePaper

/-- Elementary lower bound for the logarithm of Nagura's shifted quotient. -/
theorem log_shifted_div_lower {x d : ℝ} (hd : 1 ≤ d) (hxd : d < x) :
    Real.log ((x - d + 1) / d) ≥
      Real.log x - Real.log d - (d - 1) / (x - d + 1) := by
  have hdPos : 0 < d := zero_lt_one.trans_le hd
  have hxPos : 0 < x := hdPos.trans hxd
  have hDenomPos : 0 < x - d + 1 := by linarith
  let z : ℝ := (x - d + 1) / x
  have hz : 0 < z := by
    dsimp only [z]
    positivity
  have hResidual := Real.one_sub_inv_le_log_of_pos hz
  have hResidual' :
      -(d - 1) / (x - d + 1) ≤ Real.log z := by
    calc
      -(d - 1) / (x - d + 1) = 1 - z⁻¹ := by
        dsimp only [z]
        field_simp
        ring
      _ ≤ Real.log z := hResidual
  have hFactor : (x - d + 1) / d = (x / d) * z := by
    dsimp only [z]
    field_simp
  have hSplit :
      Real.log ((x - d + 1) / d) =
        Real.log x - Real.log d + Real.log z := by
    rw [hFactor, Real.log_mul (div_ne_zero (ne_of_gt hxPos) (ne_of_gt hdPos))
      (ne_of_gt hz), Real.log_div (ne_of_gt hxPos) (ne_of_gt hdPos)]
  rw [hSplit]
  calc
    Real.log x - Real.log d - (d - 1) / (x - d + 1) =
        (Real.log x - Real.log d) + (-(d - 1) / (x - d + 1)) := by ring
    _ ≤ (Real.log x - Real.log d) + Real.log z :=
      by linarith
    _ = Real.log x - Real.log d + Real.log z := by ring

/-- The preceding logarithm estimate inserted into the real factorial lower
model. -/
noncomputable def naguraFloorFactorialCoarseModel (n d : ℕ) : ℝ :=
  let x := (n : ℝ)
  let δ := (d : ℝ)
  let y := (x - δ + 1) / δ
  let L := Real.log x - Real.log δ - (δ - 1) / (x - δ + 1)
  y * L - x / δ + L / 2 + Real.log (2 * Real.pi) / 2

theorem naguraFloorFactorialCoarseModel_le
    {n d : ℕ} (hd : 0 < d) (hnd : 2 * d ≤ n) :
    naguraFloorFactorialCoarseModel n d ≤
      naguraFloorFactorialLowerModel n d := by
  let x : ℝ := n
  let δ : ℝ := d
  let y : ℝ := (x - δ + 1) / δ
  let L : ℝ := Real.log x - Real.log δ - (δ - 1) / (x - δ + 1)
  have hdR : 1 ≤ δ := by
    dsimp only [δ]
    exact_mod_cast hd
  have hxd : δ < x := by
    dsimp only [δ, x]
    exact_mod_cast (by omega : d < n)
  have hLog : L ≤ Real.log y := by
    exact log_shifted_div_lower hdR hxd
  have hyOne : 1 ≤ y := by
    have hdPos : 0 < δ := zero_lt_one.trans_le hdR
    have hndR : 2 * δ ≤ x := by
      dsimp only [δ, x]
      exact_mod_cast hnd
    dsimp only [y]
    apply (le_div_iff₀ hdPos).2
    linarith
  have hCoeff : 0 ≤ y + 1 / 2 := by linarith
  have hMul := mul_le_mul_of_nonneg_left hLog hCoeff
  simp only [naguraFloorFactorialCoarseModel,
    naguraFloorFactorialLowerModel]
  change
    y * L - x / δ + L / 2 + Real.log (2 * Real.pi) / 2 ≤
      y * Real.log y - x / δ + Real.log y / 2 +
        Real.log (2 * Real.pi) / 2
  nlinarith

/-- The arbitrary-endpoint model after replacing each logarithm by its
explicit rational-error lower bound. -/
noncomputable def naguraGeneralUpperCoarseModel (n : ℕ) : ℝ :=
  naguraFactorialLogUpper n - naguraFloorFactorialCoarseModel n 2 -
    naguraFloorFactorialCoarseModel n 3 -
      naguraFloorFactorialCoarseModel n 7 -
        naguraFloorFactorialCoarseModel n 43 -
          naguraFloorFactorialCoarseModel n 1806

theorem naguraGeneralUpperModel_le_coarse
    {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralUpperModel n ≤ naguraGeneralUpperCoarseModel n := by
  have h2 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 2) (by norm_num) (by omega)
  have h3 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 3) (by norm_num) (by omega)
  have h7 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 7) (by norm_num) (by omega)
  have h43 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 43) (by norm_num) (by omega)
  have h1806 := naguraFloorFactorialCoarseModel_le
    (n := n) (d := 1806) (by norm_num) (by omega)
  unfold naguraGeneralUpperModel naguraGeneralUpperCoarseModel
  linarith

/-- The residual rational loss from the five floor operations. -/
noncomputable def naguraUpperRoundingError (x : ℝ) : ℝ :=
  (1 / (x - 1) + 2 / (x - 2) + 6 / (x - 6) +
    42 / (x - 42) + 1805 / (x - 1805)) / 2

/-- A small algebra lemma, kept separate so clearing a shifted denominator
never creates the enormous common-denominator expression for all five
floors at once. -/
theorem nagura_floor_coarse_algebra
    {x δ A P : ℝ} (hδ : δ ≠ 0) (hshift : x - δ + 1 ≠ 0) :
    ((x - δ + 1) / δ) * (A - (δ - 1) / (x - δ + 1)) - x / δ +
        (A - (δ - 1) / (x - δ + 1)) / 2 + P / 2 =
      x / δ * A - (δ - 1) / δ * A - (δ - 1) / δ - x / δ +
        A / 2 - ((δ - 1) / (x - δ + 1)) / 2 + P / 2 := by
  field_simp [hδ, hshift]
  ring

/-- Exact algebraic expansion of the coarse model. -/
theorem naguraGeneralUpperCoarseModel_eq {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralUpperCoarseModel n =
      (n : ℝ) * naguraMainCoefficient + (5 : ℝ) / 2 * Real.log (n : ℝ) +
        naguraMainCoefficient -
          (Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
            Real.log 1806) / 2 +
        5 - 5 * Real.log (2 * Real.pi) / 2 +
          naguraUpperRoundingError n := by
  simp only [naguraGeneralUpperCoarseModel, naguraFactorialLogUpper,
    naguraFloorFactorialCoarseModel, naguraMainCoefficient,
    naguraUpperRoundingError, Nat.cast_ofNat]
  have hnR : (20000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (n : ℝ) - 2 + 1 ≠ 0 := by nlinarith
  have h2 : (n : ℝ) - 3 + 1 ≠ 0 := by nlinarith
  have h6 : (n : ℝ) - 7 + 1 ≠ 0 := by nlinarith
  have h42 : (n : ℝ) - 43 + 1 ≠ 0 := by nlinarith
  have h1805 : (n : ℝ) - 1806 + 1 ≠ 0 := by nlinarith
  rw [nagura_floor_coarse_algebra (by norm_num) h1,
    nagura_floor_coarse_algebra (by norm_num) h2,
    nagura_floor_coarse_algebra (by norm_num) h6,
    nagura_floor_coarse_algebra (by norm_num) h42,
    nagura_floor_coarse_algebra (by norm_num) h1805]
  ring

theorem naguraUpperRoundingError_le_two_point_five
    {x : ℝ} (hx : 20000 ≤ x) :
    naguraUpperRoundingError x ≤ (5 : ℝ) / 2 := by
  have h1 : 1 / (x - 1) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h2 : 2 / (x - 2) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h6 : 6 / (x - 6) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h42 : 42 / (x - 42) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  have h1805 : 1805 / (x - 1805) ≤ 1 := by
    apply (div_le_one (by linarith)).2
    linarith
  unfold naguraUpperRoundingError
  linarith

theorem log_nat_lt_div_ten_thousand_add_nine
    {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) < (n : ℝ) / 10000 + 9 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hSmall := Real.log_le_sub_one_of_pos
    (show 0 < (n : ℝ) / 10000 by positivity)
  have hLogTenThousand : Real.log 10000 < 10 := by
    have hMono : Real.log (10000 : ℝ) < Real.log ((2 : ℝ) ^ 14) :=
      Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
    rw [Real.log_pow] at hMono
    norm_num at hMono
    nlinarith [Real.log_two_lt_d9]
  have hSplit :
      Real.log (n : ℝ) =
        Real.log ((n : ℝ) / 10000) + Real.log 10000 := by
    calc
      Real.log (n : ℝ) = Real.log (((n : ℝ) / 10000) * 10000) := by
        congr 1
        field_simp
      _ = Real.log ((n : ℝ) / 10000) + Real.log 10000 :=
        Real.log_mul (div_ne_zero hnR (by norm_num)) (by norm_num)
  rw [hSplit]
  linarith

/-- One extra Taylor term at `7 / 8` gives enough coefficient room to
absorb the recursive `ψ(n / 1806)` term in the far tail. -/
theorem log_seven_lt_1_9465 :
    Real.log 7 < (3893 : ℝ) / 2000 := by
  have hResidual :
      Real.log (1 - (1 : ℝ) / 8) ≤ -(1331 : ℝ) / 10000 := by
    calc
      Real.log (1 - (1 : ℝ) / 8) ≤
          -(∑ i ∈ Finset.range 3,
              ((1 : ℝ) / 8) ^ (i + 1) / (i + 1)) +
            |(1 : ℝ) / 8| ^ (3 + 1) / (1 - |(1 : ℝ) / 8|) :=
        log_one_sub_le_neg_sum_add_remainder (by norm_num) 3
      _ ≤ -(1331 : ℝ) / 10000 := by
        norm_num [Finset.sum_range_succ]
  have hSplit :
      Real.log 7 = 3 * Real.log 2 + Real.log (1 - (1 : ℝ) / 8) := by
    calc
      Real.log 7 = Real.log ((2 : ℝ) ^ 3 * (1 - (1 : ℝ) / 8)) := by
        norm_num
      _ = Real.log ((2 : ℝ) ^ 3) + Real.log (1 - (1 : ℝ) / 8) := by
        rw [Real.log_mul] <;> norm_num
      _ = 3 * Real.log 2 + Real.log (1 - (1 : ℝ) / 8) := by
        rw [Real.log_pow]
        norm_num
  rw [hSplit]
  nlinarith [Real.log_two_lt_d9]

theorem naguraMainCoefficient_lt_1_0827 :
    naguraMainCoefficient < (10827 : ℝ) / 10000 := by
  unfold naguraMainCoefficient
  nlinarith [Real.log_two_lt_d9, log_three_lt_1_099,
    log_seven_lt_1_9465, log_forty_three_lt_3_762,
    log_one_thousand_eight_hundred_six_lt_seven_point_five]

/-- The general-integer form of Nagura's first analytic estimate. -/
theorem naguraGeneralUpperCombination_lt_1_0851_mul
    {n : ℕ} (hn : 20000 ≤ n) :
    naguraGeneralUpperCombination n <
      (10851 : ℝ) / 10000 * (n : ℝ) := by
  have hModel := naguraGeneralUpperCombination_le_model hn
  have hCoarse := naguraGeneralUpperModel_le_coarse hn
  have hIdentity := naguraGeneralUpperCoarseModel_eq hn
  have hnPos : 0 < n := by omega
  have hnR : (20000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hCoefficient := naguraMainCoefficient_lt_1_083
  have hMain := mul_lt_mul_of_pos_left hCoefficient
    (show 0 < (n : ℝ) by exact_mod_cast hnPos)
  have hLog := log_nat_lt_div_ten_thousand_add_nine hnPos
  have hError := naguraUpperRoundingError_le_two_point_five hnR
  have hLogSum :
      0 ≤ Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 + Real.log 1806 := by
    positivity
  have hPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  rw [hIdentity] at hCoarse
  nlinarith

/-- A sharper far-tail version of the first combination estimate. -/
theorem naguraGeneralUpperCombination_lt_1_083_mul
    {n : ℕ} (hn : 1000000 ≤ n) :
    naguraGeneralUpperCombination n <
      (1083 : ℝ) / 1000 * (n : ℝ) := by
  have hnSmall : 20000 ≤ n := by omega
  have hModel := naguraGeneralUpperCombination_le_model hnSmall
  have hCoarse := naguraGeneralUpperModel_le_coarse hnSmall
  have hIdentity := naguraGeneralUpperCoarseModel_eq hnSmall
  have hnPos : 0 < n := by omega
  have hnR : (1000000 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hCoefficient := naguraMainCoefficient_lt_1_0827
  have hMain := mul_lt_mul_of_pos_left hCoefficient
    (show 0 < (n : ℝ) by exact_mod_cast hnPos)
  have hLog := log_nat_lt_div_ten_thousand_add_nine hnPos
  have hError := naguraUpperRoundingError_le_two_point_five
    (show (20000 : ℝ) ≤ (n : ℝ) by exact_mod_cast hnSmall)
  have hLogSum :
      0 ≤ Real.log 2 + Real.log 3 + Real.log 7 + Real.log 43 +
        Real.log 1806 := by
    positivity
  have hPi : 0 ≤ Real.log (2 * Real.pi) := by
    apply Real.log_nonneg
    nlinarith [Real.pi_gt_three]
  rw [hIdentity] at hCoarse
  nlinarith

/-- General-endpoint combinatorial bridge for the first Nagura weight. -/
theorem psi_sub_psi_div_1806_le_generalUpperCombination
    {n : ℕ} (hn : 1806 ≤ n) :
    Chebyshev.psi (n : ℝ) - Chebyshev.psi ((n / 1806 : ℕ) : ℝ) ≤
      naguraGeneralUpperCombination n := by
  let a : ℕ → ℝ := fun i ↦
    Chebyshev.psi (((n / (i + 1) : ℕ) : ℝ))
  have ha : Antitone a := by
    intro i j hij
    apply Chebyshev.psi_mono
    norm_cast
    apply (Nat.le_div_iff_mul_le (by omega : 0 < i + 1)).2
    calc
      (n / (j + 1)) * (i + 1) ≤ (n / (j + 1)) * (j + 1) := by
        exact Nat.mul_le_mul_left _ (Nat.succ_le_succ hij)
      _ ≤ n := Nat.div_mul_le_self _ _
  have ha0 (i : ℕ) : 0 ≤ a i := Chebyshev.psi_nonneg _
  have h := first_sub_1806_le_nagura_weighted_sum a ha ha0 hn
  dsimp only [a] at h
  rw [sum_naguraWeight_mul_psi_eq] at h
  simpa only [Nat.zero_add, Nat.div_one, Nat.reduceAdd,
    naguraGeneralUpperCombination] using h

/-- The sharp upper bound for `ψ` at every natural endpoint in the analytic
tail. -/
theorem psi_nat_lt_1_086_mul {n : ℕ} (hn : 1000000 ≤ n) :
    Chebyshev.psi (n : ℝ) < (543 : ℝ) / 500 * (n : ℝ) := by
  have hnBridge : 1806 ≤ n := by omega
  have hBridge := psi_sub_psi_div_1806_le_generalUpperCombination hnBridge
  have hCombination := naguraGeneralUpperCombination_lt_1_083_mul hn
  have hqPosNat : 0 < n / 1806 := Nat.div_pos (by omega) (by norm_num)
  have hqPos : 0 < ((n / 1806 : ℕ) : ℝ) := by exact_mod_cast hqPosNat
  have hPsi := Chebyshev.psi_le_const_mul_self
    (x := ((n / 1806 : ℕ) : ℝ)) hqPos.le
  have hLogFour : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hCoarseConstant : Real.log 4 + 4 < (2709 : ℝ) / 500 := by
    rw [hLogFour]
    nlinarith [Real.log_two_lt_d9]
  have hCoarseTerm := mul_lt_mul_of_pos_right hCoarseConstant hqPos
  have hMulLe : (n / 1806) * 1806 ≤ n := Nat.div_mul_le_self n 1806
  have hMulLeR : ((n / 1806 : ℕ) : ℝ) * 1806 ≤ (n : ℝ) := by
    exact_mod_cast hMulLe
  nlinarith

end Erdos390.WholePaper
