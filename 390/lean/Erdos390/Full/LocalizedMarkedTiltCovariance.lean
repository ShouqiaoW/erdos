import Erdos390.Full.OmittedScoreTilt

/-!
# Localized covariance stability under a small exponential tilt

The physical/head residual in the paper is a second, small tilt of each
medium-prime cell law.  A total-variation estimate would lose the divisibility
mark.  This file instead keeps the marginal and joint-event scales visible.

Everything below is an exact statement about finite probability laws.  The
arithmetic application supplies reciprocal bounds for the three marked
events `A`, `B`, and `A * B`.
-/

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- The explicit relative expectation-loss factor for a pointwise-small
second tilt. -/
def smallTiltLoss (epsilon : ℝ) : ℝ :=
  4 * epsilon / (1 - 2 * epsilon)

theorem smallTiltLoss_nonneg {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 2 * epsilon < 1) :
    0 ≤ smallTiltLoss epsilon := by
  exact div_nonneg (mul_nonneg (by norm_num) hepsilon)
    (sub_nonneg.mpr hsmall.le)

theorem smallTiltLoss_le_eight_mul {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1) :
    smallTiltLoss epsilon ≤ 8 * epsilon := by
  have hden : 0 < 1 - 2 * epsilon := by nlinarith
  unfold smallTiltLoss
  apply (div_le_iff₀ hden).2
  nlinarith [sq_nonneg epsilon]

/-- A pointwise score of size `epsilon` changes a marked probability only
by the same relative scale.  In particular, an event of baseline probability
`O(1 / d)` changes by `O(epsilon / d)`, with no additive TV loss. -/
theorem abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    {epsilon a : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 2 * epsilon < 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      smallTiltLoss epsilon * a := by
  have hExpectAbs : mu.expect (fun omega ↦ |S omega|) ≤ epsilon := by
    calc
      mu.expect (fun omega ↦ |S omega|) ≤
          mu.expect (fun _ ↦ epsilon) := mu.expect_mono _ _ hscore
      _ = epsilon := by simp [expect, ← Finset.sum_mul, mu.mass_sum]
  have hAexpect0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have ha0 : 0 ≤ a := hAexpect0.trans hAexpect
  have hMarked :
      mu.expect (fun omega ↦ A omega * |S omega|) ≤ epsilon * a := by
    calc
      mu.expect (fun omega ↦ A omega * |S omega|) ≤
          mu.expect (fun omega ↦ A omega * epsilon) := by
        apply mu.expect_mono
        intro omega
        exact mul_le_mul_of_nonneg_left (hscore omega) (hA0 omega)
      _ = epsilon * mu.expect A := by
        rw [show (fun omega ↦ A omega * epsilon) =
            fun omega ↦ epsilon * A omega by
          funext omega
          ring]
        rw [mu.expect_smul]
      _ ≤ epsilon * a := mul_le_mul_of_nonneg_left hAexpect hepsilon
  have htotal : 2 * mu.expect (fun omega ↦ |S omega|) < 1 := by
    calc
      2 * mu.expect (fun omega ↦ |S omega|) ≤ 2 * epsilon :=
        mul_le_mul_of_nonneg_left hExpectAbs (by norm_num)
      _ < 1 := hsmall
  have hbase := mu.abs_exponentialTilt_expect_sub_expect_le_of_small_score
    A S hA0 hA1 (fun omega ↦ (hscore omega).trans (by linarith)) htotal
  have hdenActual : 0 < 1 - 2 * mu.expect (fun omega ↦ |S omega|) :=
    sub_pos.mpr htotal
  have hdenEpsilon : 0 < 1 - 2 * epsilon := sub_pos.mpr hsmall
  have hnum :
      2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|) ≤
        4 * epsilon * a := by
    have hsecond : mu.expect A * mu.expect (fun omega ↦ |S omega|) ≤
        a * epsilon :=
      mul_le_mul hAexpect hExpectAbs
        (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) ha0
    nlinarith
  refine hbase.trans ?_
  calc
    (2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|)) /
        (1 - 2 * mu.expect (fun omega ↦ |S omega|)) ≤
        (4 * epsilon * a) /
          (1 - 2 * mu.expect (fun omega ↦ |S omega|)) :=
      div_le_div_of_nonneg_right hnum hdenActual.le
    _ ≤ (4 * epsilon * a) / (1 - 2 * epsilon) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (mul_nonneg (by norm_num) hepsilon) ha0
      · exact hdenEpsilon
      · linarith
    _ = smallTiltLoss epsilon * a := by
      unfold smallTiltLoss
      field_simp

/-- Pure covariance algebra: three localized expectation perturbation bounds
give a localized covariance perturbation bound.  The product term is kept at
the product of the two marginal scales. -/
theorem abs_covariance_sub_covariance_le_of_expectation_perturbations
    (mu nu : FiniteProbability Omega) (A B : Omega → ℝ)
    {a b dA dB dAB : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (ha : mu.expect A ≤ a)
    (hb : mu.expect B ≤ b)
    (hdA0 : 0 ≤ dA)
    (hAperturb : |nu.expect A - mu.expect A| ≤ dA)
    (hBperturb : |nu.expect B - mu.expect B| ≤ dB)
    (hABperturb :
      |nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)| ≤ dAB) :
    |nu.covariance A B - mu.covariance A B| ≤
      dAB + (a + dA) * dB + b * dA := by
  have hmuA0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hmuB0 : 0 ≤ mu.expect B := mu.expect_nonneg B hB0
  have ha0 : 0 ≤ a := hmuA0.trans ha
  have hb0 : 0 ≤ b := hmuB0.trans hb
  have hnuA : nu.expect A ≤ a + dA := by
    have hle : nu.expect A - mu.expect A ≤ dA :=
      (le_abs_self _).trans hAperturb
    linarith
  have hnuA0 : 0 ≤ nu.expect A := nu.expect_nonneg A hA0
  have hproduct :
      |nu.expect A * nu.expect B - mu.expect A * mu.expect B| ≤
        (a + dA) * dB + b * dA := by
    rw [show nu.expect A * nu.expect B - mu.expect A * mu.expect B =
        nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A) by ring]
    calc
      |nu.expect A * (nu.expect B - mu.expect B) +
          mu.expect B * (nu.expect A - mu.expect A)| ≤
          |nu.expect A * (nu.expect B - mu.expect B)| +
            |mu.expect B * (nu.expect A - mu.expect A)| := abs_add_le _ _
      _ = nu.expect A * |nu.expect B - mu.expect B| +
            mu.expect B * |nu.expect A - mu.expect A| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hnuA0, abs_of_nonneg hmuB0]
      _ ≤ (a + dA) * dB + b * dA :=
        add_le_add
          (mul_le_mul hnuA hBperturb (abs_nonneg _) (add_nonneg ha0 hdA0))
          (mul_le_mul hb hAperturb (abs_nonneg _) hb0)
  unfold covariance
  rw [show
      (nu.expect (fun omega ↦ A omega * B omega) -
            nu.expect A * nu.expect B) -
          (mu.expect (fun omega ↦ A omega * B omega) -
            mu.expect A * mu.expect B) =
        (nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B) by ring]
  have habs :
      |(nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)) -
          (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| :=
    abs_sub _ _
  calc
    |(nu.expect (fun omega ↦ A omega * B omega) -
          mu.expect (fun omega ↦ A omega * B omega)) -
        (nu.expect A * nu.expect B - mu.expect A * mu.expect B)| ≤
        |nu.expect (fun omega ↦ A omega * B omega) -
            mu.expect (fun omega ↦ A omega * B omega)| +
          |nu.expect A * nu.expect B - mu.expect A * mu.expect B| := habs
    _ ≤ dAB + ((a + dA) * dB + b * dA) :=
      add_le_add hABperturb hproduct
    _ = dAB + (a + dA) * dB + b * dA := by ring

/-- Localized covariance stability for two `[0,1]`-valued marks under a
pointwise-small exponential tilt. -/
theorem abs_exponentialTilt_covariance_sub_covariance_le_smallTiltLoss
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {epsilon a b c : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 2 * epsilon < 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      let D := smallTiltLoss epsilon
      D * c + (a + D * a) * (D * b) + b * (D * a) := by
  dsimp only
  have hD0 : 0 ≤ smallTiltLoss epsilon :=
    smallTiltLoss_nonneg hepsilon hsmall
  have hAB0 : ∀ omega, 0 ≤ A omega * B omega := fun omega ↦
    mul_nonneg (hA0 omega) (hB0 omega)
  have hAB1 : ∀ omega, A omega * B omega ≤ 1 := by
    intro omega
    exact (mul_le_mul (hA1 omega) (hB1 omega) (hB0 omega) zero_le_one).trans_eq
      (mul_one 1)
  exact abs_covariance_sub_covariance_le_of_expectation_perturbations
    mu (mu.exponentialTilt S) A B hA0 hB0 hAexpect hBexpect
    (mul_nonneg hD0 ((mu.expect_nonneg A hA0).trans hAexpect))
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      A S hA0 hA1 hepsilon hsmall hscore hAexpect)
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      B S hB0 hB1 hepsilon hsmall hscore hBexpect)
    (mu.abs_exponentialTilt_expect_sub_expect_le_smallTiltLoss
      (fun omega ↦ A omega * B omega) S hAB0 hAB1 hepsilon hsmall hscore
      hABexpect)

/-- A simplified product-scale form.  Once the second score is at most
`1/8`, the normalized loss is at most `8 epsilon`, and the quadratic
normalization terms cost only the explicit factor `3 a b`. -/
theorem abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {epsilon a b c : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * epsilon ≤ 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      8 * epsilon * (c + 3 * a * b) := by
  have htwo : 2 * epsilon < 1 := by nlinarith
  have hraw :=
    mu.abs_exponentialTilt_covariance_sub_covariance_le_smallTiltLoss
      A B S hA0 hA1 hB0 hB1 hepsilon htwo hscore
      hAexpect hBexpect hABexpect
  let D := smallTiltLoss epsilon
  have hD0 : 0 ≤ D := smallTiltLoss_nonneg hepsilon htwo
  have hD8 : D ≤ 8 * epsilon := smallTiltLoss_le_eight_mul hepsilon hsmall
  have hD1 : D ≤ 1 := hD8.trans hsmall
  have ha0 : 0 ≤ a := (mu.expect_nonneg A hA0).trans hAexpect
  have hb0 : 0 ≤ b := (mu.expect_nonneg B hB0).trans hBexpect
  have hAB0 : ∀ omega, 0 ≤ A omega * B omega := fun omega ↦
    mul_nonneg (hA0 omega) (hB0 omega)
  have hc0 : 0 ≤ c := (mu.expect_nonneg _ hAB0).trans hABexpect
  have hcoef : 2 * D + D ^ 2 ≤ 3 * D := by
    nlinarith [mul_nonneg hD0 (sub_nonneg.mpr hD1)]
  have hab0 : 0 ≤ a * b := mul_nonneg ha0 hb0
  have hsum0 : 0 ≤ c + 3 * a * b := by positivity
  refine hraw.trans ?_
  dsimp only
  change
    D * c + (a + D * a) * (D * b) + b * (D * a) ≤
      8 * epsilon * (c + 3 * a * b)
  calc
    D * c + (a + D * a) * (D * b) + b * (D * a) =
        D * c + (2 * D + D ^ 2) * (a * b) := by ring
    _ ≤ D * c + (3 * D) * (a * b) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hcoef hab0)
    _ = D * (c + 3 * a * b) := by ring
    _ ≤ (8 * epsilon) * (c + 3 * a * b) :=
      mul_le_mul_of_nonneg_right hD8 hsum0

/-- The first mark may be any nonnegative bounded statistic.  Rescaling it
to `[0,1]` introduces no loss in the final expectation-scale bound: the
pointwise bound cancels exactly.  This form is used with an actual valuation
column and a normalized physical logarithm. -/
theorem abs_exponentialTilt_covariance_sub_covariance_le_eight_mul_left_bounded
    (mu : FiniteProbability Omega) (A B S : Omega → ℝ)
    {KA epsilon a b c : ℝ}
    (hKA : 0 < KA)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hAKA : ∀ omega, A omega ≤ KA)
    (hB0 : ∀ omega, 0 ≤ B omega)
    (hB1 : ∀ omega, B omega ≤ 1)
    (hepsilon : 0 ≤ epsilon)
    (hsmall : 8 * epsilon ≤ 1)
    (hscore : ∀ omega, |S omega| ≤ epsilon)
    (hAexpect : mu.expect A ≤ a)
    (hBexpect : mu.expect B ≤ b)
    (hABexpect : mu.expect (fun omega ↦ A omega * B omega) ≤ c) :
    |(mu.exponentialTilt S).covariance A B - mu.covariance A B| ≤
      8 * epsilon * (c + 3 * a * b) := by
  let A' : Omega → ℝ := fun omega ↦ A omega / KA
  have hA'0 : ∀ omega, 0 ≤ A' omega := fun omega ↦
    div_nonneg (hA0 omega) hKA.le
  have hA'1 : ∀ omega, A' omega ≤ 1 := by
    intro omega
    exact (div_le_one hKA).2 (hAKA omega)
  have hA'expect : mu.expect A' ≤ a / KA := by
    have heq : mu.expect A' = (1 / KA) * mu.expect A := by
      rw [show A' = fun omega ↦ (1 / KA) * A omega by
        funext omega
        dsimp only [A']
        ring]
      exact mu.expect_smul (1 / KA) A
    rw [heq]
    calc
      (1 / KA) * mu.expect A = mu.expect A / KA := by ring
      _ ≤ a / KA := div_le_div_of_nonneg_right hAexpect hKA.le
  have hAB'expect :
      mu.expect (fun omega ↦ A' omega * B omega) ≤ c / KA := by
    have heq :
        mu.expect (fun omega ↦ A' omega * B omega) =
          (1 / KA) * mu.expect (fun omega ↦ A omega * B omega) := by
      rw [show (fun omega ↦ A' omega * B omega) =
          fun omega ↦ (1 / KA) * (A omega * B omega) by
        funext omega
        dsimp only [A']
        ring]
      exact mu.expect_smul (1 / KA) (fun omega ↦ A omega * B omega)
    rw [heq]
    calc
      (1 / KA) * mu.expect (fun omega ↦ A omega * B omega) =
          mu.expect (fun omega ↦ A omega * B omega) / KA := by ring
      _ ≤ c / KA := div_le_div_of_nonneg_right hABexpect hKA.le
  have hraw :=
    mu.abs_exponentialTilt_covariance_sub_covariance_le_eight_mul
      A' B S hA'0 hA'1 hB0 hB1 hepsilon hsmall hscore
      hA'expect hBexpect hAB'expect
  have hcov (nu : FiniteProbability Omega) :
      nu.covariance A' B = (1 / KA) * nu.covariance A B := by
    rw [show A' = fun omega ↦ (1 / KA) * A omega by
      funext omega
      dsimp only [A']
      ring]
    exact nu.covariance_smul_left (1 / KA) A B
  rw [hcov, hcov] at hraw
  have hdiv :
      |(mu.exponentialTilt S).covariance A B - mu.covariance A B| / KA ≤
        (8 * epsilon * (c + 3 * a * b)) / KA := by
    calc
      |(mu.exponentialTilt S).covariance A B - mu.covariance A B| / KA =
          |((mu.exponentialTilt S).covariance A B -
            mu.covariance A B) / KA| := by
        rw [abs_div, abs_of_pos hKA]
      _ =
          |(1 / KA) * (mu.exponentialTilt S).covariance A B -
            (1 / KA) * mu.covariance A B| := by
        apply congrArg abs
        field_simp [ne_of_gt hKA]
      _ ≤ 8 * epsilon * (c / KA + 3 * (a / KA) * b) := hraw
      _ = (8 * epsilon * (c + 3 * a * b)) / KA := by
        field_simp [ne_of_gt hKA]
  exact (div_le_div_iff_of_pos_right hKA).mp hdiv

end FiniteProbability

end

end Erdos390.Full
