import Erdos390.Full.ArithmeticModel

/-!
# Exact scale identities

This file records the elementary identities behind the fixed choice
`y = n^(2/9)` used throughout the marked and smooth bridge.  Keeping them as
equalities avoids repeatedly treating `U = 9/2` and the four-mark cofactor
margin as informal arithmetic simplifications.
-/

open Filter Topology

namespace Erdos390.Full.Scale

open ArithmeticModel

/-- The logarithmic scale `L = log n`. -/
noncomputable def L (n : ℕ) : ℝ :=
  Real.log (n : ℝ)

/-- The smooth-number parameter before it is simplified to `9/2`. -/
noncomputable def U (n : ℕ) : ℝ :=
  L n / Real.log (y n)

theorem cast_pos_of_one_lt {n : ℕ} (hn : 1 < n) : 0 < (n : ℝ) := by
  exact_mod_cast (Nat.zero_lt_of_lt hn)

theorem L_pos {n : ℕ} (hn : 1 < n) : 0 < L n := by
  exact Real.log_pos (by exact_mod_cast hn)

theorem y_pos {n : ℕ} (hn : 0 < n) : 0 < y n := by
  exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _

/-- `log y = (2/9) log n`, with no asymptotic error. -/
theorem log_y {n : ℕ} (hn : 0 < n) :
    Real.log (y n) = (2 / 9 : ℝ) * L n := by
  simpa [y, L] using
    (Real.log_rpow (by exact_mod_cast hn : (0 : ℝ) < n) (2 / 9 : ℝ))

/-- The Dickman parameter is exactly `U = 9/2` for every `n > 1`. -/
theorem U_eq_nine_halves {n : ℕ} (hn : 1 < n) :
    U n = (9 / 2 : ℝ) := by
  have hL : L n ≠ 0 := (L_pos hn).ne'
  rw [U, log_y (Nat.zero_lt_of_lt hn)]
  field_simp

/-- Four marked prime factors use precisely the exponent `8/9`. -/
theorem y_pow_four (n : ℕ) :
    y n ^ 4 = (n : ℝ) ^ (8 / 9 : ℝ) := by
  calc
    y n ^ 4 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 4 := rfl
    _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (4 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (2 / 9 : ℝ) 4).symm
    _ = (n : ℝ) ^ (8 / 9 : ℝ) := by norm_num

theorem y_pow_two (n : ℕ) :
    y n ^ 2 = (n : ℝ) ^ (4 / 9 : ℝ) := by
  calc
    y n ^ 2 = ((n : ℝ) ^ (2 / 9 : ℝ)) ^ 2 := rfl
    _ = (n : ℝ) ^ ((2 / 9 : ℝ) * (2 : ℕ)) :=
      (Real.rpow_mul_natCast (Nat.cast_nonneg n) (2 / 9 : ℝ) 2).symm
    _ = (n : ℝ) ^ (4 / 9 : ℝ) := by norm_num

/-- The smallest cofactor after four marks is exactly `n^(1/9)`. -/
theorem cofactor_four {n : ℕ} (hn : 0 < n) :
    (n : ℝ) / y n ^ 4 = (n : ℝ) ^ (1 / 9 : ℝ) := by
  rw [y_pow_four]
  calc
    (n : ℝ) / (n : ℝ) ^ (8 / 9 : ℝ) =
        (n : ℝ) ^ ((1 : ℝ) - 8 / 9) := by
          rw [Real.rpow_sub (by exact_mod_cast hn), Real.rpow_one]
    _ = (n : ℝ) ^ (1 / 9 : ℝ) := by norm_num

/-- The four-mark cofactor tends to infinity. -/
theorem tendsto_cofactor_four :
    Tendsto (fun n : ℕ => (n : ℝ) / y n ^ 4) atTop atTop := by
  have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 9 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 9)).comp
      tendsto_natCast_atTop_atTop
  apply hpow.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (cofactor_four hn).symm

/-- The accumulated two-mark endpoint scale used in the row estimates. -/
noncomputable def endpointRatio (n : ℕ) : ℝ :=
  y n ^ 2 * L n ^ 2 / (n : ℝ)

theorem endpointRatio_eq {n : ℕ} (hn : 0 < n) :
    endpointRatio n = L n ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ) := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (4 / 9 : ℝ) * (n : ℝ) ^ (5 / 9 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num
  rw [endpointRatio, y_pow_two]
  field_simp [(Real.rpow_pos_of_pos hnR (5 / 9 : ℝ)).ne', hnR.ne']
  nlinarith

/-- In particular, all `y^2 L^2 / n` endpoint errors vanish. -/
theorem tendsto_endpointRatio_zero :
    Tendsto endpointRatio atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ => Real.log x ^ (2 : ℝ) / x ^ (5 / 9 : ℝ))
      atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
      (by norm_num : (0 : ℝ) < 5 / 9)).tendsto_div_nhds_zero
  have hnat : Tendsto
      (fun n : ℕ => Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (5 / 9 : ℝ))
      atTop (𝓝 0) := by
    simpa [Real.rpow_natCast] using hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  simpa [L] using (endpointRatio_eq hn).symm

end Erdos390.Full.Scale
