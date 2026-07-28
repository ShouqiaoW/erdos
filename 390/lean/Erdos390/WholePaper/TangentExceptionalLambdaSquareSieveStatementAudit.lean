import Erdos390.WholePaper.TangentExceptionalLambdaSquareSieve

/-! # Statement audit for the concrete finite Lambda-squared sieve -/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

noncomputable section

example (P R : ℕ) :
    tangentSelbergLambdaSupport P R =
      P.divisors.filter (fun d ↦ d ≤ R) :=
  rfl

example {P R d : ℕ} :
    d ∈ tangentSelbergLambdaSupport P R ↔
      (d ∣ P ∧ P ≠ 0) ∧ d ≤ R :=
  mem_tangentSelbergLambdaSupport

example {P R d : ℕ} (hd : d ∈ tangentSelbergLambdaSupport P R) :
    0 < d :=
  tangentSelbergLambdaSupport_pos hd

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    1 ∈ tangentSelbergLambdaSupport P R :=
  one_mem_tangentSelbergLambdaSupport hP hR

example (P R : ℕ) (lambda : ℕ → ℝ) (m : ℕ) :
    tangentSelbergLambdaLinearForm P R lambda m =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        if d ∣ m then lambda d else 0 :=
  rfl

example (P R : ℕ) (lambda : ℕ → ℝ) (q : ℕ) :
    tangentSelbergLambdaSquareCoefficient P R lambda q =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          if Nat.lcm d e = q then lambda d * lambda e else 0 :=
  rfl

example {P R m : ℕ} (lambda : ℕ → ℝ) (hm : 0 < m) :
    (∑ q ∈ m.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q) =
      tangentSelbergLambdaLinearForm P R lambda m ^ 2 :=
  sum_tangentSelbergLambdaSquareCoefficient_divisors lambda hm

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    BoundingSieve.IsUpperMoebius
      (tangentSelbergLambdaSquareCoefficient P R lambda) :=
  tangentSelbergLambdaSquareCoefficient_isUpperMoebius
    hP hR lambda hlambdaOne

example {P R q : ℕ} (lambda : ℕ → ℝ) (hq : R * R < q) :
    tangentSelbergLambdaSquareCoefficient P R lambda q = 0 :=
  tangentSelbergLambdaSquareCoefficient_eq_zero_of_level_sq_lt lambda hq

example {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q * F q) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e * F (Nat.lcm d e) :=
  tangentSelbergLambdaSquareCoefficient_divisorMoment hP lambda F

example {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q /
          (q : ℝ)) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) :=
  tangentSelbergLambdaSquare_mainQuadraticIdentity hP lambda

example {P R lo hi : ℕ} (hP : Squarefree P) (lambda : ℕ → ℝ) :
    (tangentIntervalReciprocalSieve P lo hi hP).mainSum
        (tangentSelbergLambdaSquareCoefficient P R lambda) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) :=
  tangentIntervalReciprocalSieve_lambdaSquare_mainSum hP lambda

example {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    1 / (Nat.lcm d e : ℝ) =
      ∑ r ∈ (Nat.gcd d e).divisors,
        (r.totient : ℝ) / ((d : ℝ) * (e : ℝ)) :=
  tangent_reciprocal_lcm_eq_totient_commonDivisorSum hd he

example {P d e : ℕ} (hP : 0 < P)
    (hd : d ∈ P.divisors) (he : e ∈ P.divisors) :
    1 / (Nat.lcm d e : ℝ) =
      ∑ r ∈ P.divisors,
        if r ∣ d ∧ r ∣ e then
          (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 :=
  tangent_reciprocal_lcm_eq_totient_modulusSum hP hd he

example (P R : ℕ) (lambda : ℕ → ℝ) (r : ℕ) :
    tangentSelbergDiagonalTransform P R lambda r =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        if r ∣ d then lambda d / (d : ℝ) else 0 :=
  rfl

example {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
      ∑ e ∈ tangentSelbergLambdaSupport P R,
        lambda d * lambda e / (Nat.lcm d e : ℝ)) =
      ∑ r ∈ P.divisors, (r.totient : ℝ) *
        tangentSelbergDiagonalTransform P R lambda r ^ 2 :=
  tangentSelbergLambdaSquare_quadraticDiagonalization hP lambda

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) :
    (∑ r ∈ tangentSelbergLambdaSupport P R,
        (ArithmeticFunction.moebius r : ℝ) *
          tangentSelbergDiagonalTransform P R lambda r) = lambda 1 :=
  tangentSelberg_moebius_diagonal_constraint hP hR lambda

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    1 / tangentSelbergDensitySum P R ≤
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) :=
  tangentSelbergDensitySum_inv_le_quadratic hP hR lambda hlambdaOne

example {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    (∑ d ∈ n.divisors,
        if a ∣ d then
          (ArithmeticFunction.moebius (n / d) : ℝ)
        else 0) = if n = a then 1 else 0 :=
  tangent_sum_moebius_quotients_over_divisors ha hn

example {P R t : ℕ} (ht : t ∈ tangentSelbergLambdaSupport P R)
    (F : ℕ → ℝ) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        if t ∣ d then
          ∑ r ∈ tangentSelbergLambdaSupport P R,
            if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) * F r
            else 0
        else 0) = F t :=
  tangentSelberg_upper_moebius_inversion ht F

example (P R : ℕ) :
    tangentSelbergDensitySum P R =
      ∑ r ∈ tangentSelbergLambdaSupport P R,
        (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) :=
  rfl

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    0 < tangentSelbergDensitySum P R :=
  tangentSelbergDensitySum_pos hP hR

example {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        |tangentSelbergLambdaSquareCoefficient P R lambda q|) ≤
      (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 :=
  tangentSelbergLambdaSquareCoefficient_l1_le hP lambda

example {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (∑ d ∈ tangentSelbergLambdaSupport P R,
            ∑ e ∈ tangentSelbergLambdaSupport P R,
              lambda d * lambda e / (Nat.lcm d e : ℝ)) +
        (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 :=
  reducedResidueIoc_card_le_lambdaSquare hP hR lambda hlambdaOne

example {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1)
    {mainBound lambdaBound : ℝ}
    (hmain :
      (∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ)) ≤ mainBound)
    (hlambda :
      (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ≤
        lambdaBound) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) * mainBound + lambdaBound ^ 2 :=
  reducedResidueIoc_card_le_lambdaSquare_of_bounds
    hP hR lambda hlambdaOne hmain hlambda

example (P R d : ℕ) :
    tangentSelbergCanonicalLambda P R d =
      if d ∈ tangentSelbergLambdaSupport P R then
        (d : ℝ) / tangentSelbergDensitySum P R *
          ∑ r ∈ tangentSelbergLambdaSupport P R,
            if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) *
                  (ArithmeticFunction.moebius r : ℝ) /
                (r.totient : ℝ)
            else 0
      else 0 :=
  rfl

example {P R d : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (hd : d ∈ tangentSelbergLambdaSupport P R) :
    tangentSelbergCanonicalLambda P R d / (d : ℝ) =
      (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
              ((ArithmeticFunction.moebius r : ℝ) / (r.totient : ℝ))
          else 0 :=
  tangentSelbergCanonicalLambda_div hP hR hd

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    tangentSelbergCanonicalLambda P R 1 = 1 :=
  tangentSelbergCanonicalLambda_one hP hR

example {P R t : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (ht : t ∈ tangentSelbergLambdaSupport P R) :
    tangentSelbergDiagonalTransform P R
        (tangentSelbergCanonicalLambda P R) t =
      (ArithmeticFunction.moebius t : ℝ) /
        ((t.totient : ℝ) * tangentSelbergDensitySum P R) :=
  tangentSelbergCanonicalLambda_diagonalTransform_of_mem hP hR ht

example {P R t : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    tangentSelbergDiagonalTransform P R
        (tangentSelbergCanonicalLambda P R) t =
      if t ∈ tangentSelbergLambdaSupport P R then
        (ArithmeticFunction.moebius t : ℝ) /
          ((t.totient : ℝ) * tangentSelbergDensitySum P R)
      else 0 :=
  tangentSelbergCanonicalLambda_diagonalTransform hP hR t

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
      ∑ e ∈ tangentSelbergLambdaSupport P R,
        tangentSelbergCanonicalLambda P R d *
            tangentSelbergCanonicalLambda P R e /
          (Nat.lcm d e : ℝ)) =
      1 / tangentSelbergDensitySum P R :=
  tangentSelbergCanonicalLambda_quadratic_eq_invDensity hP hR

example {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    BoundingSieve.IsUpperMoebius
      (tangentSelbergLambdaSquareCoefficient P R
        (tangentSelbergCanonicalLambda P R)) :=
  tangentSelbergCanonicalLambdaSquareCoefficient_isUpperMoebius hP hR

example {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (∑ d ∈ tangentSelbergLambdaSupport P R,
            ∑ e ∈ tangentSelbergLambdaSupport P R,
              tangentSelbergCanonicalLambda P R d *
                  tangentSelbergCanonicalLambda P R e /
                (Nat.lcm d e : ℝ)) +
        (∑ d ∈ tangentSelbergLambdaSupport P R,
          |tangentSelbergCanonicalLambda P R d|) ^ 2 :=
  reducedResidueIoc_card_le_canonicalLambdaSquare hP hR

example {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (1 / tangentSelbergDensitySum P R) +
        (∑ d ∈ tangentSelbergLambdaSupport P R,
          |tangentSelbergCanonicalLambda P R d|) ^ 2 :=
  reducedResidueIoc_card_le_canonicalLambdaSquare_density hP hR

example
    {P lo hi y : ℕ} (hP : Squarefree P) (hy : 1 ≤ y)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1)
    {Cmain Clambda : ℝ}
    (hmain :
      (∑ d ∈ tangentSelbergLambdaSupport P (y ^ 2),
        ∑ e ∈ tangentSelbergLambdaSupport P (y ^ 2),
          lambda d * lambda e / (Nat.lcm d e : ℝ)) ≤
        Cmain / Real.log (y : ℝ))
    (hlambda :
      (∑ d ∈ tangentSelbergLambdaSupport P (y ^ 2), |lambda d|) ≤
        Clambda * (y : ℝ) ^ 2 / Real.log (y : ℝ)) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 :=
  reducedResidueIoc_card_le_lambdaSquare_paperShape
    hP hy lambda hlambdaOne hmain hlambda

example
    {P lo hi y : ℕ} (hP : Squarefree P) (hy : 1 ≤ y)
    {Cmain Clambda : ℝ}
    (hdensity :
      1 / tangentSelbergDensitySum P (y ^ 2) ≤
        Cmain / Real.log (y : ℝ))
    (hlambda :
      (∑ d ∈ tangentSelbergLambdaSupport P (y ^ 2),
        |tangentSelbergCanonicalLambda P (y ^ 2) d|) ≤
          Clambda * (y : ℝ) ^ 2 / Real.log (y : ℝ)) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 :=
  reducedResidueIoc_card_le_canonicalLambdaSquare_paperShape
    hP hy hdensity hlambda

end

end Erdos390.WholePaper
