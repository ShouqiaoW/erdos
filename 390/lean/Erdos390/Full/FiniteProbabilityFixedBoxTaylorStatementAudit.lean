import Erdos390.Full.FiniteProbabilityFixedBoxTaylor

/-! Independently restated signatures for the arbitrary-fixed-box layer. -/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbabilityFixedBoxTaylorStatementAudit

open Erdos390.Full.FiniteProbability

variable {Omega : Type*} [Fintype Omega]

example {K x : ℝ} (hK : 0 ≤ K) (hx : |x| ≤ K) :
    |Real.exp x - 1| ≤ fixedBoxLinearConstant K * |x| := by
  exact abs_exp_sub_one_le_fixedBox hK hx

example {K x : ℝ} (hK : 0 ≤ K) (hx : |x| ≤ K) :
    |Real.exp x - 1 - x| ≤ fixedBoxQuadraticConstant K * x ^ 2 := by
  exact abs_exp_sub_one_sub_id_le_fixedBox hK hx

example (mu : FiniteProbability Omega) (H S : Omega → ℝ)
    {K a Rone MH RH CH : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (hRone : 0 ≤ Rone)
    (hMH : 0 ≤ MH) (hRH : 0 ≤ RH) (hCH : 0 ≤ CH)
    (hscore : ∀ omega, |S omega| ≤ K)
    (hsmall : fixedBoxLinearConstant K * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hmean : |mu.expect H| ≤ MH)
    (hmarkedSq :
      mu.expect (fun omega ↦ |H omega| * S omega ^ 2) ≤ RH)
    (hcov : |mu.covariance H S| ≤ CH) :
    |(mu.exponentialTilt S).expect H -
        (mu.expect H + mu.covariance H S)| ≤
      2 * fixedBoxQuadraticConstant K *
        (RH + CH * a + (MH + CH) * Rone) := by
  exact mu.abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound_fixedBox
    H S hK ha hRone hMH hRH hCH hscore hsmall habsScore hscoreSq
      hmean hmarkedSq hcov

end Erdos390.Full.FiniteProbabilityFixedBoxTaylorStatementAudit
