import Erdos390.WholePaper.SafePrimeCounting

/-!
# Quantitative safe prime-counting remainder

This exposes the `O(x / log(x)^2)` remainder available from the same audited
dependency route as `SafePrimeCounting`.  No convenience PNT import with a
tainted closure is used.
-/

open Filter Asymptotics

namespace Erdos390.WholePaper.SafePrimeCounting

/-- Quantitative real-variable PNT remainder along the audited `MediumPNT`
route. -/
theorem primeCounting_sub_main_isBigO_div_log_sq :
    (fun x : ℝ ↦
      (Nat.primeCounting ⌊x⌋₊ : ℝ) - x / Real.log x) =O[atTop]
        (fun x : ℝ ↦ x / Real.log x ^ 2) := by
  have hthetaBase :
      (Chebyshev.theta - id) =O[atTop]
        (fun x : ℝ ↦ x / Real.log x) := by
    simpa using
      Erdos390.Full.FriableAsymptotic.theta_error_isBigO_log_power 1
  have hthetaMul := hthetaBase.mul
    (isBigO_refl (fun x : ℝ ↦ (Real.log x)⁻¹) atTop)
  have htheta :
      (fun x : ℝ ↦
        Chebyshev.theta x / Real.log x - x / Real.log x) =O[atTop]
          (fun x : ℝ ↦ x / Real.log x ^ 2) := by
    apply hthetaMul.congr'
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      simp only [Pi.sub_apply, id_eq, div_eq_mul_inv]
      ring
    · filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
      rw [div_eq_mul_inv]
      field_simp
  have hadd := Chebyshev.primeCounting_sub_theta_div_log_isBigO.add htheta
  apply hadd.congr'
  · exact Eventually.of_forall fun x ↦ by ring
  · exact Eventually.of_forall fun _x ↦ rfl

end Erdos390.WholePaper.SafePrimeCounting
