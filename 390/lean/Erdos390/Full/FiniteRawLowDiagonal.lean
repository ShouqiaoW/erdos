import Erdos390.Full.PaperWeightedInverseExport

/-!
# Direct ordinary control of a low raw matrix row

Near the moving endpoint the continuum multiplier is close to one and the
product kernel has small row mass.  This elementary lemma records the exact
diagonal-dominance calculation in the ordinary coordinate supremum norm.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteRawLowDiagonal

open PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]

theorem abs_coordinate_le
    (diagonal : Band → ℝ) (kernel : Band → Band → ℝ)
    (b : Band → ℝ) (i : Band) {d k G : ℝ}
    (hd : |diagonal i - 1| ≤ d) (hdOne : d < 1)
    (hk : ∑ j : Band, |kernel i j| ≤ k)
    (hOutput : |rawOperator diagonal kernel b i| ≤ G) :
    |b i| ≤ (G + k * ‖b‖) / (1 - d) := by
  have hdiag : 1 - d ≤ diagonal i := by
    have := neg_le_of_abs_le hd
    linarith
  have hden : 0 < 1 - d := sub_pos.mpr hdOne
  have hdiagPos : 0 < diagonal i := hden.trans_le hdiag
  have hkernel : |∑ j : Band, kernel i j * b j| ≤ k * ‖b‖ := by
    calc
      |∑ j : Band, kernel i j * b j| ≤
          ∑ j : Band, |kernel i j * b j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band, |kernel i j| * ‖b‖ := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm b j)
          (abs_nonneg _)
      _ = (∑ j : Band, |kernel i j|) * ‖b‖ := by
        rw [← Finset.sum_mul]
      _ ≤ k * ‖b‖ :=
        mul_le_mul_of_nonneg_right hk (norm_nonneg b)
  have hscaled : (1 - d) * |b i| ≤ G + k * ‖b‖ := by
    calc
      (1 - d) * |b i| ≤ diagonal i * |b i| :=
        mul_le_mul_of_nonneg_right hdiag (abs_nonneg _)
      _ = |diagonal i * b i| := by
        rw [abs_mul, abs_of_pos hdiagPos]
      _ ≤ |rawOperator diagonal kernel b i| +
          |∑ j : Band, kernel i j * b j| := by
        have h := abs_sub (rawOperator diagonal kernel b i)
          (∑ j : Band, kernel i j * b j)
        unfold rawOperator at h
        simpa only [add_sub_cancel_right] using h
      _ ≤ G + k * ‖b‖ := add_le_add hOutput hkernel
  exact (le_div_iff₀ hden).2 (by
    simpa only [mul_comm] using hscaled)

end Erdos390.Full.FiniteRawLowDiagonal
