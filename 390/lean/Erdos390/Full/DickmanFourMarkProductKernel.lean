import Erdos390.Full.FriableAsymptotic

/-!
# The four-mark Dickman product kernel

The four-mark chamber in the proof of Lemma 7.5 uses the normalized
Dickman profile

`F x = rho (U - x) / rho U`

on the full simplex `x, z >= 0`, `x + z <= 4`.  The local product estimate
in `DickmanBasic` covers the unit square by differentiating the actual
method-of-steps solution near the origin.  This file extends that estimate
to the whole four-mark simplex using the globally proved one-Lipschitz
bound for `rho` on `[0,5]`.  In particular, no `C^{1,1}` hypothesis and no
tilt-box parameter occurs in the statement or proof.
-/

open Set

noncomputable section

namespace Erdos390.Full.DickmanFourMarkProductKernel

open DickmanBasic FriableAsymptotic

/-- The paper's four-mark profile `h_U`, named explicitly for statement
matching.  It is definitionally the `F` constructed in `DickmanBasic`. -/
def fourMarkProfile (x : ℝ) : ℝ := rho (U - x) / rho U

@[simp] theorem fourMarkProfile_eq_F (x : ℝ) : fourMarkProfile x = F x := rfl

@[simp] theorem fourMarkProfile_zero : fourMarkProfile 0 = 1 := by
  simp [fourMarkProfile, rho_U_ne_zero]

/-- Positivity and the uniform absolute bound for the actual normalized
Dickman profile throughout the complete four-mark range. -/
lemma fourMarkProfile_pos_and_abs_le {x : ℝ} (hx0 : 0 ≤ x) (hx4 : x ≤ 4) :
    0 < fourMarkProfile x ∧ |fourMarkProfile x| ≤ 1 / rho U := by
  have harg0 : 0 ≤ U - x := by
    norm_num [U] at hx4 ⊢
    linarith
  have harg5 : U - x ≤ 5 := by
    norm_num [U] at hx0 ⊢
    linarith
  have hrpos : 0 < rho (U - x) := rho_pos_on_zero_five harg0 harg5
  have hrle : rho (U - x) ≤ 1 := rho_le_one_of_le_five harg5
  have hrU : 0 < rho U := rho_U_pos
  constructor
  · exact div_pos hrpos hrU
  · unfold fourMarkProfile
    rw [abs_of_pos (div_pos hrpos hrU)]
    exact (div_le_div_iff_of_pos_right hrU).2 hrle

/-- The normalized four-mark profile is `1 / rho U`-Lipschitz on the
ordered interval `[0,4]`.  This includes the Dickman kink crossed near the
far end of that interval; the proof uses the integral Lipschitz theorem,
not differentiability at the kink. -/
lemma fourMarkProfile_lipschitz {a b : ℝ}
    (ha0 : 0 ≤ a) (hab : a ≤ b) :
    |fourMarkProfile b - fourMarkProfile a| ≤
      (1 / rho U) * (b - a) := by
  have hargOrder : U - b ≤ U - a := by linarith
  have hargTop : U - a ≤ 5 := by
    norm_num [U] at ha0 ⊢
    linarith
  have hrho := rho_lipschitz_of_le_five hargOrder hargTop
  have hrU : 0 < rho U := rho_U_pos
  rw [fourMarkProfile, fourMarkProfile]
  rw [div_sub_div_same]
  rw [abs_div, abs_of_pos hrU]
  have hdiff : (U - a) - (U - b) = b - a := by ring
  rw [hdiff] at hrho
  calc
    |rho (U - b) - rho (U - a)| / rho U
        = |rho (U - a) - rho (U - b)| / rho U := by
            rw [abs_sub_comm]
    _ ≤ (b - a) / rho U := (div_le_div_iff_of_pos_right hrU).2 hrho
    _ = (1 / rho U) * (b - a) := by ring

/-- **Box-independent four-mark Dickman product-kernel bound.**

This is the precise analytic sublemma used in the four-mark chamber of
paper Lemma 7.5.  The constant is chosen solely from the already-constructed
Dickman profile at the fixed parameter `U`; there are no tilt radius `B`,
prime cutoff `W`, or asymptotic parameters in either the quantifiers or the
proof. -/
theorem exists_boxIndependent_fourMark_productKernel_bound :
    ∃ C_K : ℝ, 0 < C_K ∧
      ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
        |fourMarkProfile (x + z) -
            fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z := by
  obtain ⟨C₀, hC₀pos, hlocal⟩ := kernel_product_bound
  let R : ℝ := 1 / rho U
  have hRpos : 0 < R := by
    dsimp [R]
    exact one_div_pos.mpr rho_U_pos
  let C_K : ℝ := C₀ + R + R * R + 1
  have hCKpos : 0 < C_K := by
    dsimp [C_K]
    nlinarith [mul_pos hRpos hRpos]
  refine ⟨C_K, hCKpos, ?_⟩
  intro x z hx0 hz0 hxz4
  have hx4 : x ≤ 4 := by linarith
  have hz4 : z ≤ 4 := by linarith
  have hxz0 : 0 ≤ x + z := add_nonneg hx0 hz0
  have hFx := fourMarkProfile_pos_and_abs_le hx0 hx4
  have hFz := fourMarkProfile_pos_and_abs_le hz0 hz4
  have hFxz := fourMarkProfile_pos_and_abs_le hxz0 hxz4
  by_cases hx1 : x ≤ 1
  · by_cases hz1 : z ≤ 1
    · have hsmall := hlocal x ⟨hx0, hx1⟩ z ⟨hz0, hz1⟩
      rw [← fourMarkProfile_eq_F, ← fourMarkProfile_eq_F,
        ← fourMarkProfile_eq_F] at hsmall
      exact hsmall.trans (by
        have hCdom : C₀ ≤ C_K := by
          dsimp [C_K]
          nlinarith [hRpos]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hCdom hx0) hz0)
    · have hz1' : 1 < z := lt_of_not_ge hz1
      have hLipShift := fourMarkProfile_lipschitz hz0
        (show z ≤ x + z by linarith)
      have hLipZero := fourMarkProfile_lipschitz (a := 0) (b := x)
        (by norm_num) hx0
      have hdecomp :
          fourMarkProfile (x + z) - fourMarkProfile x * fourMarkProfile z =
            (fourMarkProfile (x + z) - fourMarkProfile z) +
              fourMarkProfile z * (1 - fourMarkProfile x) := by ring
      rw [hdecomp]
      calc
        |(fourMarkProfile (x + z) - fourMarkProfile z) +
            fourMarkProfile z * (1 - fourMarkProfile x)| ≤
            |fourMarkProfile (x + z) - fourMarkProfile z| +
              |fourMarkProfile z * (1 - fourMarkProfile x)| := abs_add_le _ _
        _ ≤ R * x + R * (R * x) := by
          apply add_le_add
          · simpa [R, add_sub_cancel_left] using hLipShift
          · rw [abs_mul]
            have hzeroDiff : |1 - fourMarkProfile x| ≤ R * x := by
              rw [← fourMarkProfile_zero]
              simpa [R, abs_sub_comm] using hLipZero
            exact mul_le_mul hFz.2 hzeroDiff (abs_nonneg _) hRpos.le
        _ ≤ C_K * x * z := by
          have hCoeff : R + R * R ≤ C_K := by
            dsimp [C_K]
            linarith [hC₀pos]
          calc
            R * x + R * (R * x) = (R + R * R) * x := by ring
            _ ≤ C_K * x := mul_le_mul_of_nonneg_right hCoeff hx0
            _ ≤ (C_K * x) * z := by
              have h := mul_le_mul_of_nonneg_left hz1'.le
                (mul_nonneg hCKpos.le hx0)
              simpa using h
            _ = C_K * x * z := rfl
  · have hx1' : 1 < x := lt_of_not_ge hx1
    by_cases hz1 : z ≤ 1
    · have hLipShift := fourMarkProfile_lipschitz hx0
        (show x ≤ x + z by linarith)
      have hLipZero := fourMarkProfile_lipschitz (a := 0) (b := z)
        (by norm_num) hz0
      have hdecomp :
          fourMarkProfile (x + z) - fourMarkProfile x * fourMarkProfile z =
            (fourMarkProfile (x + z) - fourMarkProfile x) +
              fourMarkProfile x * (1 - fourMarkProfile z) := by ring
      rw [hdecomp]
      calc
        |(fourMarkProfile (x + z) - fourMarkProfile x) +
            fourMarkProfile x * (1 - fourMarkProfile z)| ≤
            |fourMarkProfile (x + z) - fourMarkProfile x| +
              |fourMarkProfile x * (1 - fourMarkProfile z)| := abs_add_le _ _
        _ ≤ R * z + R * (R * z) := by
          apply add_le_add
          · simpa [R, add_sub_cancel_left] using hLipShift
          · rw [abs_mul]
            have hzeroDiff : |1 - fourMarkProfile z| ≤ R * z := by
              rw [← fourMarkProfile_zero]
              simpa [R, abs_sub_comm] using hLipZero
            exact mul_le_mul hFx.2 hzeroDiff (abs_nonneg _) hRpos.le
        _ ≤ C_K * x * z := by
          have hCoeff : R + R * R ≤ C_K := by
            dsimp [C_K]
            linarith [hC₀pos]
          calc
            R * z + R * (R * z) = (R + R * R) * z := by ring
            _ ≤ C_K * z := mul_le_mul_of_nonneg_right hCoeff hz0
            _ ≤ (C_K * x) * z := by
              apply mul_le_mul_of_nonneg_right _ hz0
              nlinarith [hCKpos]
            _ = C_K * x * z := by ring
    · have hz1' : 1 < z := lt_of_not_ge hz1
      calc
        |fourMarkProfile (x + z) -
            fourMarkProfile x * fourMarkProfile z| ≤
            |fourMarkProfile (x + z)| +
              |fourMarkProfile x * fourMarkProfile z| := abs_sub _ _
        _ ≤ R + R * R := by
          apply add_le_add hFxz.2
          rw [abs_mul]
          exact mul_le_mul hFx.2 hFz.2 (abs_nonneg _) hRpos.le
        _ ≤ C_K * x * z := by
          have hCoeff : R + R * R ≤ C_K := by
            dsimp [C_K]
            linarith [hC₀pos]
          have hxy : 1 ≤ x * z := by nlinarith
          calc
            R + R * R ≤ C_K := hCoeff
            _ ≤ C_K * (x * z) := by
              nlinarith [hCKpos]
            _ = C_K * x * z := by ring

/-- A fixed witness for the four-mark product-kernel constant.  Naming the
witness makes the dependency order formal: later prime cutoffs may depend on
this number, whereas the finite head-pattern family is selected only after
the cutoff. -/
noncomputable def boxIndependentFourMarkKernelConstant : ℝ :=
  Classical.choose exists_boxIndependent_fourMark_productKernel_bound

theorem boxIndependentFourMarkKernelConstant_pos :
    0 < boxIndependentFourMarkKernelConstant :=
  (Classical.choose_spec
    exists_boxIndependent_fourMark_productKernel_bound).1

theorem boxIndependentFourMarkKernelConstant_bound
    (x z : ℝ) (hx : 0 ≤ x) (hz : 0 ≤ z) (hxz : x + z ≤ 4) :
    |fourMarkProfile (x + z) -
        fourMarkProfile x * fourMarkProfile z| ≤
      boxIndependentFourMarkKernelConstant * x * z :=
  (Classical.choose_spec
    exists_boxIndependent_fourMark_productKernel_bound).2 x z hx hz hxz

/-- The same theorem stated directly with `DickmanBasic.F`, for downstream
modules that already use that name. -/
theorem exists_boxIndependent_F_fourMark_productKernel_bound :
    ∃ C_K : ℝ, 0 < C_K ∧
      ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
        |F (x + z) - F x * F z| ≤ C_K * x * z := by
  simpa only [fourMarkProfile_eq_F] using
    exists_boxIndependent_fourMark_productKernel_bound

end Erdos390.Full.DickmanFourMarkProductKernel
