import Erdos390.WholePaper.TangentExceptionalCanonicalBounds

/-! # Statement audit for the canonical Lambda-squared analytic bounds

This restates all ten public definitions and all 44 public theorem
statements from `TangentExceptionalCanonicalBounds`.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.sigma ArithmeticFunction.zeta
open Filter

namespace Erdos390.WholePaper

noncomputable section

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

/-! ## Definition audit -/

example (n : ℕ) :
    tangentReciprocalTotientArithmeticFunction n =
      if n = 0 then 0 else 1 / (n.totient : ℝ) :=
  rfl

example :
    tangentSigmaTotientRatioArithmeticFunction =
      ArithmeticFunction.pmul
        (((ArithmeticFunction.sigma 1 : ArithmeticFunction ℕ) :
          ArithmeticFunction ℝ))
        tangentReciprocalTotientArithmeticFunction :=
  rfl

example :
    tangentSquarefreeFourOverPrimeArithmeticFunction =
      ArithmeticFunction.pmul
        (ArithmeticFunction.pmul
          (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
            ArithmeticFunction ℝ))
          (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
            ArithmeticFunction ℝ)))
        (ArithmeticFunction.prodPrimeFactors
          (fun p ↦ 4 / (p : ℝ))) :=
  rfl

example :
    tangentSquarefreeFourOverSquareArithmeticFunction =
      ArithmeticFunction.pmul
        tangentSquarefreeFourOverPrimeArithmeticFunction
        tangentReciprocalArithmeticFunction :=
  rfl

example (P : ℕ) :
    tangentSelbergFullDensitySum P =
      ∑ r ∈ P.divisors, 1 / (r.totient : ℝ) :=
  rfl

example (P : ℕ) :
    tangentSelbergFullLogMoment P =
      ∑ r ∈ P.divisors,
        Real.log (r : ℝ) / (r.totient : ℝ) :=
  rfl

example :
    tangentSelbergMertensBase =
      max Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformCutoff 2 :=
  rfl

example :
    tangentSelbergMertensLoss =
      |Erdos390.Full.PrimeSums.fullReciprocalSum
          tangentSelbergMertensBase| +
        |Real.log (Real.log (tangentSelbergMertensBase : ℝ))| +
        5 *
            Erdos390.Full.PrimeBandQuadrature.fullReciprocalSumUniformConstant /
          Real.log (tangentSelbergMertensBase : ℝ) ^ 3 :=
  rfl

example :
    tangentSelbergCanonicalMainConstant =
      10 * Real.exp tangentSelbergMertensLoss :=
  rfl

example :
    tangentSelbergCanonicalLambdaConstant =
      Real.exp 4 * tangentSelbergCanonicalMainConstant :=
  rfl

/-! ## Complete public theorem audit -/

example :
    tangentReciprocalTotientArithmeticFunction.IsMultiplicative :=
  tangentReciprocalTotientArithmeticFunction_isMultiplicative

example {n : ℕ} (hn : 0 < n) :
    tangentReciprocalTotientArithmeticFunction n =
      1 / (n.totient : ℝ) :=
  tangentReciprocalTotientArithmeticFunction_apply_of_pos hn

example {p : ℕ} (hp : p.Prime) :
    tangentReciprocalTotientArithmeticFunction p =
      1 / ((p : ℝ) - 1) :=
  tangentReciprocalTotientArithmeticFunction_apply_prime hp

example :
    tangentSigmaTotientRatioArithmeticFunction.IsMultiplicative :=
  tangentSigmaTotientRatioArithmeticFunction_isMultiplicative

example {n : ℕ} (hn : 0 < n) :
    tangentSigmaTotientRatioArithmeticFunction n =
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
        (n.totient : ℝ) :=
  tangentSigmaTotientRatioArithmeticFunction_apply_of_pos hn

example :
    tangentSquarefreeFourOverPrimeArithmeticFunction.IsMultiplicative :=
  tangentSquarefreeFourOverPrimeArithmeticFunction_isMultiplicative

example (n : ℕ) :
    0 ≤ tangentSquarefreeFourOverPrimeArithmeticFunction n :=
  tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg n

example {p : ℕ} (hp : p.Prime) :
    tangentSquarefreeFourOverPrimeArithmeticFunction p =
      4 / (p : ℝ) :=
  tangentSquarefreeFourOverPrimeArithmeticFunction_apply_prime hp

example {n : ℕ} (hn : ¬Squarefree n) :
    tangentSquarefreeFourOverPrimeArithmeticFunction n = 0 :=
  tangentSquarefreeFourOverPrimeArithmeticFunction_eq_zero_of_not_squarefree hn

example :
    tangentSquarefreeFourOverSquareArithmeticFunction.IsMultiplicative :=
  tangentSquarefreeFourOverSquareArithmeticFunction_isMultiplicative

example (n : ℕ) :
    0 ≤ tangentSquarefreeFourOverSquareArithmeticFunction n :=
  tangentSquarefreeFourOverSquareArithmeticFunction_nonneg n

example {p : ℕ} (hp : p.Prime) :
    tangentSquarefreeFourOverSquareArithmeticFunction p =
      4 / (p : ℝ) ^ 2 :=
  tangentSquarefreeFourOverSquareArithmeticFunction_apply_prime hp

example {P R : ℕ} (hP : Squarefree P) :
    tangentSelbergDensitySum P R =
      ∑ r ∈ tangentSelbergLambdaSupport P R,
        1 / (r.totient : ℝ) :=
  tangentSelbergDensitySum_eq_reciprocalTotient hP

example {s : Finset ℕ} (a b : ℕ → ℝ)
    (ha : ∀ p ∈ s, 0 ≤ a p) (hb : ∀ p ∈ s, 0 ≤ b p) :
    (∑ t ∈ s.powerset,
        (∑ p ∈ t, b p) * ∏ p ∈ t, a p) ≤
      (∏ p ∈ s, (1 + a p)) * ∑ p ∈ s, b p * a p :=
  sum_powerset_sum_mul_prod_le a b ha hb

example (y : ℕ) :
    (roughHeadModulus y).primeFactors = primesUpTo y :=
  roughHeadModulus_primeFactors y

example (y : ℕ) :
    primesUpTo y = Erdos390.Full.PrimeSums.primesUpTo y :=
  wholePaper_primesUpTo_eq_full_primesUpTo y

example (y : ℕ) :
    (∑ p ∈ (roughHeadModulus y).primeFactors,
        Real.log (p : ℝ) / ((p : ℝ) - 1)) ≤
      fullLogReciprocalSum y + fullReciprocalSum y :=
  roughHead_primeFactor_logMoment_le_fullPrimeSums y

example :
    ∀ᶠ y : ℕ in atTop,
      fullLogReciprocalSum y + fullReciprocalSum y ≤
        (9 / 5 : ℝ) * Real.log (y : ℝ) :=
  eventually_fullPrimeMoment_le_nine_fifths_log

example :
    ∀ᶠ y : ℕ in atTop,
      tangentSelbergFullLogMoment (roughHeadModulus y) ≤
        (9 / 5 : ℝ) * Real.log (y : ℝ) *
          tangentSelbergFullDensitySum (roughHeadModulus y) :=
  eventually_roughHead_fullLogMoment_le_nine_fifths

example :
    fullReciprocalSumUniformCutoff ≤ tangentSelbergMertensBase :=
  tangentSelbergMertensBase_ge_cutoff

example : 2 ≤ tangentSelbergMertensBase :=
  tangentSelbergMertensBase_ge_two

example : 0 ≤ tangentSelbergMertensLoss :=
  tangentSelbergMertensLoss_nonneg

example {y : ℕ} (hy : tangentSelbergMertensBase ≤ y) :
    Real.log (Real.log (y : ℝ)) - tangentSelbergMertensLoss ≤
      fullReciprocalSum y :=
  fullReciprocalSum_ge_logLog_sub_tangentSelbergMertensLoss hy

example (y : ℕ) :
    Real.exp (fullReciprocalSum y) ≤
      tangentSelbergFullDensitySum (roughHeadModulus y) :=
  exp_fullReciprocalSum_le_roughHeadFullDensity y

example : 0 < tangentSelbergCanonicalMainConstant :=
  tangentSelbergCanonicalMainConstant_pos

example : 0 < tangentSelbergCanonicalLambdaConstant :=
  tangentSelbergCanonicalLambdaConstant_pos

example {P : ℕ} (hP : Squarefree P) :
    tangentSelbergFullDensitySum P =
      ∏ p ∈ P.primeFactors, (1 + 1 / ((p : ℝ) - 1)) :=
  tangentSelbergFullDensitySum_eq_primeProduct hP

example {P : ℕ} (hP : Squarefree P) :
    tangentSelbergFullLogMoment P ≤
      tangentSelbergFullDensitySum P *
        (∑ p ∈ P.primeFactors,
          Real.log (p : ℝ) / ((p : ℝ) - 1)) :=
  tangentSelbergFullLogMoment_le hP

example {y : ℕ} (hy : tangentSelbergMertensBase ≤ y) :
    Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) ≤
      tangentSelbergFullDensitySum (roughHeadModulus y) :=
  roughHeadFullDensity_ge_exp_neg_loss_mul_log hy

example {P R : ℕ} (hP : Squarefree P) (hR : 1 < R) :
    tangentSelbergFullDensitySum P ≤
      tangentSelbergDensitySum P R +
        tangentSelbergFullLogMoment P / Real.log (R : ℝ) :=
  tangentSelbergFullDensitySum_le_density_add_logTail hP hR

example :
    ∀ᶠ y : ℕ in atTop,
      tangentSelbergFullDensitySum (roughHeadModulus y) / 10 ≤
        tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) :=
  eventually_roughHead_density_ge_one_tenth_fullDensity

example {r : ℕ} (hr : Squarefree r) :
    ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
        (r.totient : ℝ) ≤
      (tangentSquarefreeFourOverPrimeArithmeticFunction *
        (ζ : ArithmeticFunction ℝ)) r :=
  tangentSigmaTotientRatio_le_fourConvolution_of_squarefree hr

example (r : ℕ) :
    0 ≤ (tangentSquarefreeFourOverPrimeArithmeticFunction *
      (ζ : ArithmeticFunction ℝ)) r :=
  tangent_fourOverPrime_convolution_nonneg r

example {R : ℕ} (hR : 1 ≤ R) :
    (∏ p ∈ primesUpTo R, (1 + 4 / (p : ℝ) ^ 2)) ≤
      Real.exp 4 :=
  roughHead_fourOverSquareEulerProduct_le_exp_four hR

example {R : ℕ} (hR : 1 ≤ R) :
    (∑ q ∈ Finset.Ioc 0 R,
        tangentSquarefreeFourOverSquareArithmeticFunction q) ≤
      Real.exp 4 :=
  sum_fourOverSquare_le_exp_four hR

example {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ r ∈ tangentSelbergLambdaSupport P R,
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ)) ≤
      Real.exp 4 * (R : ℝ) :=
  tangentSelbergSigmaTotientMean_le hP hR

example {P R d : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (hd : d ∈ tangentSelbergLambdaSupport P R) :
    |tangentSelbergCanonicalLambda P R d| ≤
      (d : ℝ) / tangentSelbergDensitySum P R *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then 1 / (r.totient : ℝ) else 0 :=
  tangentSelbergCanonicalLambda_abs_le hP hR hd

example {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
      (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
            (r.totient : ℝ) :=
  tangentSelbergCanonicalLambda_l1_le_sigmaTotientMean hP hR

example {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
      Real.exp 4 * (R : ℝ) /
        tangentSelbergDensitySum P R :=
  tangentSelbergCanonicalLambda_l1_le_exp_four_mul_level_div_density
    hP hR

example :
    ∀ᶠ y : ℕ in atTop,
      1 / tangentSelbergDensitySum
          (roughHeadModulus y) (y ^ 2) ≤
          tangentSelbergCanonicalMainConstant /
            Real.log (y : ℝ) ∧
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
          tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
            Real.log (y : ℝ) :=
  eventually_tangentSelbergCanonical_coefficientBounds

example :
    ∀ᶠ y : ℕ in atTop,
      1 / tangentSelbergDensitySum
          (roughHeadModulus y) (y ^ 2) ≤
        tangentSelbergCanonicalMainConstant / Real.log (y : ℝ) :=
  eventually_tangentSelbergCanonical_invDensity_le

example :
    ∀ᶠ y : ℕ in atTop,
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
        tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
          Real.log (y : ℝ) :=
  eventually_tangentSelbergCanonical_l1_le

example :
    ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧ ∀ y : ℕ, Y₀ ≤ y →
      1 / tangentSelbergDensitySum
            (roughHeadModulus y) (y ^ 2) ≤
            tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ) ∧
        (∑ d ∈ tangentSelbergLambdaSupport
            (roughHeadModulus y) (y ^ 2),
            |tangentSelbergCanonicalLambda
              (roughHeadModulus y) (y ^ 2) d|) ≤
            tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
              Real.log (y : ℝ) :=
  exists_tangentSelbergCanonical_coefficientBounds_cutoff

example :
    ∀ᶠ y : ℕ in atTop, ∀ lo hi : ℕ,
      ((reducedResidueIoc (roughHeadModulus y) lo hi).card : ℝ) ≤
        ((hi - lo : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
            Real.log (y : ℝ) ^ 2 :=
  eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead

end

end Erdos390.WholePaper
