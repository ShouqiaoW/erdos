import Erdos390.WholePaper.TangentExceptionalSelbergReduction
import Erdos390.Full.HeadPattern
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Concrete finite Lambda-squared coefficients for the exceptional-row sieve

This file continues the Section 9 Selberg reduction past the abstract
`IsUpperMoebius` interface.  For a finite divisor support

`S(P,R) = {d : d | P, d <= R}`

and real weights `lambda_d`, it defines the literal Lambda-squared
coefficients

`muPlus(q) = sum_{d,e in S(P,R), lcm(d,e)=q} lambda_d lambda_e`.

The divisor sum of these coefficients is proved to be the square

`sum_{q|m} muPlus(q) = (sum_{d in S(P,R), d|m} lambda_d)^2`.

Consequently `lambda_1=1` gives a genuine upper-Moebius sequence.  We also
prove the exact quadratic main-term identity, the level-squared support
bound, and the sharp finite `l1` estimate obtained by partitioning pairs by
their least common multiple.  These yield a concrete interval upper sieve;
no exceptional-cardinality conclusion is assumed.

Finally, the file defines the canonical finite Selberg weights by Mobius
inversion of the diagonal target.  Their normalization `lambda_1=1`, exact
diagonal transform, and optimal quadratic value `1/G(P,R)` are proved here.
The downstream canonical-bounds layer lower-bounds the finite density sum
and upper-bounds the canonical coefficient norm.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius

namespace Erdos390.WholePaper

noncomputable section

/-! ## Finite Lambda-squared coefficients -/

/-- Divisors of `P` retained at Selberg level `R`. -/
def tangentSelbergLambdaSupport (P R : ℕ) : Finset ℕ :=
  P.divisors.filter (fun d ↦ d ≤ R)

@[simp]
theorem mem_tangentSelbergLambdaSupport {P R d : ℕ} :
    d ∈ tangentSelbergLambdaSupport P R ↔
      (d ∣ P ∧ P ≠ 0) ∧ d ≤ R := by
  simp [tangentSelbergLambdaSupport, Nat.mem_divisors]

theorem tangentSelbergLambdaSupport_pos
    {P R d : ℕ} (hd : d ∈ tangentSelbergLambdaSupport P R) :
    0 < d := by
  exact Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd).1

theorem one_mem_tangentSelbergLambdaSupport
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    1 ∈ tangentSelbergLambdaSupport P R := by
  simp [tangentSelbergLambdaSupport, hP.ne', hR]

/-- The divisor-restricted linear form whose square is the Selberg
majorant. -/
def tangentSelbergLambdaLinearForm
    (P R : ℕ) (lambda : ℕ → ℝ) (m : ℕ) : ℝ :=
  ∑ d ∈ tangentSelbergLambdaSupport P R,
    if d ∣ m then lambda d else 0

/-- Literal Lambda-squared upper-Moebius coefficient, grouped by the lcm of
the two finite divisor indices. -/
def tangentSelbergLambdaSquareCoefficient
    (P R : ℕ) (lambda : ℕ → ℝ) (q : ℕ) : ℝ :=
  ∑ d ∈ tangentSelbergLambdaSupport P R,
    ∑ e ∈ tangentSelbergLambdaSupport P R,
      if Nat.lcm d e = q then lambda d * lambda e else 0

/-- Exact square identity behind the Lambda-squared upper sieve. -/
theorem sum_tangentSelbergLambdaSquareCoefficient_divisors
    {P R m : ℕ} (lambda : ℕ → ℝ) (hm : 0 < m) :
    (∑ q ∈ m.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q) =
      tangentSelbergLambdaLinearForm P R lambda m ^ 2 := by
  classical
  let S := tangentSelbergLambdaSupport P R
  change
    (∑ q ∈ m.divisors,
      ∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) =
      (∑ d ∈ S, if d ∣ m then lambda d else 0) ^ 2
  calc
    (∑ q ∈ m.divisors,
      ∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) =
        ∑ d ∈ S, ∑ e ∈ S, ∑ q ∈ m.divisors,
          if Nat.lcm d e = q then lambda d * lambda e else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ S, ∑ e ∈ S,
        if d ∣ m ∧ e ∣ m then lambda d * lambda e else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      simp [Nat.mem_divisors, hm.ne', Nat.lcm_dvd_iff]
    _ = (∑ d ∈ S, if d ∣ m then lambda d else 0) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      by_cases hdm : d ∣ m <;> by_cases hem : e ∣ m <;>
        simp [hdm, hem]

/-- A normalized finite Lambda family gives actual upper-Moebius
coefficients, including at Mathlib's total boundary `m=0`. -/
theorem tangentSelbergLambdaSquareCoefficient_isUpperMoebius
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    BoundingSieve.IsUpperMoebius
      (tangentSelbergLambdaSquareCoefficient P R lambda) := by
  intro m
  by_cases hm0 : m = 0
  · subst m
    simp
  · rw [sum_tangentSelbergLambdaSquareCoefficient_divisors
      lambda (Nat.pos_of_ne_zero hm0)]
    by_cases hm1 : m = 1
    · subst m
      simp [tangentSelbergLambdaLinearForm,
        tangentSelbergLambdaSupport, Nat.dvd_one, hP.ne', hR,
        hlambdaOne]
    · rw [if_neg hm1]
      exact sq_nonneg _

/-! ## Level support and exact quadratic moment -/

/-- No Lambda-squared coefficient can occur beyond `R^2`, since every
contributing lcm divides the product of two indices at most `R`. -/
theorem tangentSelbergLambdaSquareCoefficient_eq_zero_of_level_sq_lt
    {P R q : ℕ} (lambda : ℕ → ℝ) (hq : R * R < q) :
    tangentSelbergLambdaSquareCoefficient P R lambda q = 0 := by
  classical
  unfold tangentSelbergLambdaSquareCoefficient
  apply Finset.sum_eq_zero
  intro d hd
  apply Finset.sum_eq_zero
  intro e he
  have hdR := (Finset.mem_filter.mp hd).2
  have heR := (Finset.mem_filter.mp he).2
  have hdPos := tangentSelbergLambdaSupport_pos hd
  have hePos := tangentSelbergLambdaSupport_pos he
  have hlcmLeProduct : Nat.lcm d e ≤ d * e :=
    Nat.le_of_dvd (mul_pos hdPos hePos) (Nat.lcm_dvd_mul d e)
  have hproductLe : d * e ≤ R * R := Nat.mul_le_mul hdR heR
  have hlcmNe : Nat.lcm d e ≠ q := by omega
  simp [hlcmNe]

/-- Summing the grouped coefficients against an arbitrary function simply
evaluates that function at each pair's lcm. -/
theorem tangentSelbergLambdaSquareCoefficient_divisorMoment
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) (F : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q * F q) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e * F (Nat.lcm d e) := by
  classical
  let S := tangentSelbergLambdaSupport P R
  change
    (∑ q ∈ P.divisors,
      (∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) * F q) =
      ∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e * F (Nat.lcm d e)
  calc
    (∑ q ∈ P.divisors,
      (∑ d ∈ S, ∑ e ∈ S,
        if Nat.lcm d e = q then lambda d * lambda e else 0) * F q) =
        ∑ q ∈ P.divisors, ∑ d ∈ S, ∑ e ∈ S,
          if Nat.lcm d e = q then
            lambda d * lambda e * F q else 0 := by
      apply Finset.sum_congr rfl
      intro q _hq
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _he
      split_ifs <;> simp_all
    _ = ∑ d ∈ S, ∑ e ∈ S, ∑ q ∈ P.divisors,
        if Nat.lcm d e = q then
          lambda d * lambda e * F q else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.sum_comm]
    _ = ∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e * F (Nat.lcm d e) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      have hdP : d ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      have heP : e ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
      have hlcmMem : Nat.lcm d e ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd hdP heP, hP.ne'⟩
      simp [hlcmMem]

/-- Exact quadratic main sum for the density `nu(q)=1/q`. -/
theorem tangentSelbergLambdaSquare_mainQuadraticIdentity
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q /
          (q : ℝ)) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) := by
  simpa only [div_eq_mul_inv, one_mul] using
    (tangentSelbergLambdaSquareCoefficient_divisorMoment
      hP lambda (fun q ↦ 1 / (q : ℝ)))

/-- The `mainSum` of the literal interval sieve is exactly the preceding
finite quadratic form. -/
theorem tangentIntervalReciprocalSieve_lambdaSquare_mainSum
    {P R lo hi : ℕ} (hP : Squarefree P) (lambda : ℕ → ℝ) :
    (tangentIntervalReciprocalSieve P lo hi hP).mainSum
        (tangentSelbergLambdaSquareCoefficient P R lambda) =
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) := by
  rw [BoundingSieve.mainSum]
  calc
    (∑ q ∈ P.divisors,
        tangentSelbergLambdaSquareCoefficient P R lambda q *
          (tangentIntervalReciprocalSieve P lo hi hP).nu q) =
        ∑ q ∈ P.divisors,
          tangentSelbergLambdaSquareCoefficient P R lambda q /
            (q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      change tangentSelbergLambdaSquareCoefficient P R lambda q *
          tangentReciprocalArithmeticFunction q = _
      rw [tangentReciprocalArithmeticFunction_apply_of_pos
        (Nat.pos_of_mem_divisors hq)]
      simp only [one_mul, div_eq_mul_inv]
    _ = _ := tangentSelbergLambdaSquare_mainQuadraticIdentity
      (Nat.pos_of_ne_zero hP.ne_zero) lambda

/-! ## Gcd--totient diagonalization -/

/-- The reciprocal lcm kernel is the totient sum over common divisors. -/
theorem tangent_reciprocal_lcm_eq_totient_commonDivisorSum
    {d e : ℕ} (hd : 0 < d) (he : 0 < e) :
    1 / (Nat.lcm d e : ℝ) =
      ∑ r ∈ (Nat.gcd d e).divisors,
        (r.totient : ℝ) / ((d : ℝ) * (e : ℝ)) := by
  have hgcdPos : 0 < Nat.gcd d e := by positivity
  have hlcmPos : 0 < Nat.lcm d e := Nat.lcm_pos hd he
  have hidentity :
      (Nat.gcd d e : ℝ) * (Nat.lcm d e : ℝ) =
        (d : ℝ) * (e : ℝ) := by
    exact_mod_cast Nat.gcd_mul_lcm d e
  have htotient :
      (∑ r ∈ (Nat.gcd d e).divisors, (r.totient : ℝ)) =
        (Nat.gcd d e : ℝ) := by
    exact_mod_cast Nat.sum_totient (Nat.gcd d e)
  calc
    1 / (Nat.lcm d e : ℝ) =
        (Nat.gcd d e : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
      have heReal : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
      have hlcmReal : (Nat.lcm d e : ℝ) ≠ 0 := by
        exact_mod_cast hlcmPos.ne'
      field_simp [hdReal, heReal, hlcmReal]
      nlinarith [hidentity]
    _ = (∑ r ∈ (Nat.gcd d e).divisors, (r.totient : ℝ)) /
          ((d : ℝ) * (e : ℝ)) := by rw [htotient]
    _ = ∑ r ∈ (Nat.gcd d e).divisors,
        (r.totient : ℝ) / ((d : ℝ) * (e : ℝ)) := by
      rw [Finset.sum_div]

/-- Common divisors of two divisors of `P` can be summed over all divisors
of `P` using a literal indicator. -/
theorem tangent_reciprocal_lcm_eq_totient_modulusSum
    {P d e : ℕ} (hP : 0 < P)
    (hd : d ∈ P.divisors) (he : e ∈ P.divisors) :
    1 / (Nat.lcm d e : ℝ) =
      ∑ r ∈ P.divisors,
        if r ∣ d ∧ r ∣ e then
          (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
        else 0 := by
  have hdPos : 0 < d := Nat.pos_of_mem_divisors hd
  have hePos : 0 < e := Nat.pos_of_mem_divisors he
  have hgcdPos : 0 < Nat.gcd d e := by positivity
  have hdP : d ∣ P := (Nat.mem_divisors.mp hd).1
  have hfilter :
      P.divisors.filter (fun r ↦ r ∣ d ∧ r ∣ e) =
        (Nat.gcd d e).divisors := by
    ext r
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨_hrP, _hP0⟩, hrd, hre⟩
      exact ⟨Nat.dvd_gcd hrd hre, hgcdPos.ne'⟩
    · rintro ⟨hrgcd, _hgcd0⟩
      have hrCommon := Nat.dvd_gcd_iff.mp hrgcd
      exact ⟨⟨hrCommon.1.trans hdP, hP.ne'⟩,
        hrCommon.1, hrCommon.2⟩
  rw [← Finset.sum_filter, hfilter]
  exact tangent_reciprocal_lcm_eq_totient_commonDivisorSum hdPos hePos

/-- Diagonal coordinate associated with one divisor `r`. -/
def tangentSelbergDiagonalTransform
    (P R : ℕ) (lambda : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ d ∈ tangentSelbergLambdaSupport P R,
    if r ∣ d then lambda d / (d : ℝ) else 0

/-- Exact diagonalization of the finite Selberg quadratic form:

`Q(lambda) = sum_{r|P} phi(r) * y_r^2`.
-/
theorem tangentSelbergLambdaSquare_quadraticDiagonalization
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
      ∑ e ∈ tangentSelbergLambdaSupport P R,
        lambda d * lambda e / (Nat.lcm d e : ℝ)) =
      ∑ r ∈ P.divisors, (r.totient : ℝ) *
        tangentSelbergDiagonalTransform P R lambda r ^ 2 := by
  classical
  let S := tangentSelbergLambdaSupport P R
  calc
    (∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e / (Nat.lcm d e : ℝ)) =
        ∑ d ∈ S, ∑ e ∈ S,
          lambda d * lambda e *
            (∑ r ∈ P.divisors,
              if r ∣ d ∧ r ∣ e then
                (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
              else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      calc
        lambda d * lambda e / (Nat.lcm d e : ℝ) =
            lambda d * lambda e *
              (1 / (Nat.lcm d e : ℝ)) := by ring
        _ = lambda d * lambda e *
            (∑ r ∈ P.divisors,
              if r ∣ d ∧ r ∣ e then
                (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
              else 0) := by
          rw [tangent_reciprocal_lcm_eq_totient_modulusSum hP
            (Finset.mem_filter.mp hd).1 (Finset.mem_filter.mp he).1]
    _ = ∑ d ∈ S, ∑ e ∈ S, ∑ r ∈ P.divisors,
        lambda d * lambda e *
          (if r ∣ d ∧ r ∣ e then
            (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
          else 0) := by
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      rw [Finset.mul_sum]
    _ = ∑ r ∈ P.divisors, ∑ d ∈ S, ∑ e ∈ S,
        lambda d * lambda e *
          (if r ∣ d ∧ r ∣ e then
            (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
          else 0) := by
      calc
        (∑ d ∈ S, ∑ e ∈ S, ∑ r ∈ P.divisors,
            lambda d * lambda e *
              (if r ∣ d ∧ r ∣ e then
                (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
              else 0)) =
            ∑ d ∈ S, ∑ r ∈ P.divisors, ∑ e ∈ S,
              lambda d * lambda e *
                (if r ∣ d ∧ r ∣ e then
                  (r.totient : ℝ) / ((d : ℝ) * (e : ℝ))
                else 0) := by
          apply Finset.sum_congr rfl
          intro d _hd
          rw [Finset.sum_comm]
        _ = _ := by rw [Finset.sum_comm]
    _ = ∑ r ∈ P.divisors, (r.totient : ℝ) *
        tangentSelbergDiagonalTransform P R lambda r ^ 2 := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [tangentSelbergDiagonalTransform, pow_two,
        Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      have hdPos := tangentSelbergLambdaSupport_pos hd
      have hePos := tangentSelbergLambdaSupport_pos he
      have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
      have heReal : (e : ℝ) ≠ 0 := by exact_mod_cast hePos.ne'
      by_cases hrd : r ∣ d <;> by_cases hre : r ∣ e
      · simp only [hrd, hre, and_self, if_true]
        field_simp [hdReal, heReal]
      · simp [hrd, hre]
      · simp [hrd, hre]
      · simp [hrd, hre]

/-- Mobius inversion at the bottom coordinate: every finite Lambda family
satisfies `sum mu(r) y_r = lambda_1`. -/
theorem tangentSelberg_moebius_diagonal_constraint
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) :
    (∑ r ∈ tangentSelbergLambdaSupport P R,
        (ArithmeticFunction.moebius r : ℝ) *
          tangentSelbergDiagonalTransform P R lambda r) = lambda 1 := by
  classical
  let S := tangentSelbergLambdaSupport P R
  have hOneMem : 1 ∈ S := one_mem_tangentSelbergLambdaSupport hP hR
  change
    (∑ r ∈ S, (ArithmeticFunction.moebius r : ℝ) *
      (∑ d ∈ S, if r ∣ d then lambda d / (d : ℝ) else 0)) = lambda 1
  calc
    (∑ r ∈ S, (ArithmeticFunction.moebius r : ℝ) *
      (∑ d ∈ S, if r ∣ d then lambda d / (d : ℝ) else 0)) =
        ∑ r ∈ S, ∑ d ∈ S,
          (ArithmeticFunction.moebius r : ℝ) *
            (if r ∣ d then lambda d / (d : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
    _ = ∑ d ∈ S, ∑ r ∈ S,
        (ArithmeticFunction.moebius r : ℝ) *
          (if r ∣ d then lambda d / (d : ℝ) else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ d ∈ S, (lambda d / (d : ℝ)) *
        (∑ r ∈ S,
          if r ∣ d then (ArithmeticFunction.moebius r : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro d _hd
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hrd : r ∣ d <;> simp [hrd, mul_comm]
    _ = ∑ d ∈ S, (lambda d / (d : ℝ)) *
        (if d = 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      congr 1
      have hdData := mem_tangentSelbergLambdaSupport.mp hd
      have hdPos := tangentSelbergLambdaSupport_pos hd
      have hfilter : S.filter (fun r ↦ r ∣ d) = d.divisors := by
        ext r
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨hrS, hrd⟩
          exact ⟨hrd, hdPos.ne'⟩
        · rintro ⟨hrd, _hd0⟩
          have hrLeD : r ≤ d := Nat.le_of_dvd hdPos hrd
          exact ⟨mem_tangentSelbergLambdaSupport.mpr
            ⟨⟨hrd.trans hdData.1.1, hdData.1.2⟩,
              hrLeD.trans hdData.2⟩, hrd⟩
      rw [← Finset.sum_filter, hfilter]
      exact_mod_cast
        (Erdos390.Full.HeadPattern.Pattern.sum_moebius_divisors (a := d))
    _ = lambda 1 := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        hOneMem, if_true, Nat.cast_one, div_one]

/-! ## Finite upper-divisibility Mobius inversion -/

/-- The Mobius sum over the divisors of `n` which are multiples of `a` is
the Kronecker delta at `n=a`.  This is the one-variable identity needed for
upper-divisibility Mobius inversion on the truncated divisor support. -/
theorem tangent_sum_moebius_quotients_over_divisors
    {a n : ℕ} (ha : 0 < a) (hn : 0 < n) :
    (∑ d ∈ n.divisors,
        if a ∣ d then
          (ArithmeticFunction.moebius (n / d) : ℝ)
        else 0) = if n = a then 1 else 0 := by
  classical
  by_cases han : a ∣ n
  · have haLeN : a ≤ n := Nat.le_of_dvd hn han
    have hquotPos : 0 < n / a := Nat.div_pos haLeN ha
    rw [← Finset.sum_filter]
    calc
      (∑ d ∈ n.divisors.filter (fun d ↦ a ∣ d),
          (ArithmeticFunction.moebius (n / d) : ℝ)) =
          ∑ k ∈ (n / a).divisors,
            (ArithmeticFunction.moebius ((n / a) / k) : ℝ) := by
        symm
        apply Finset.sum_bij (fun k _hk ↦ a * k)
        · intro k hk
          have hkData := Nat.mem_divisors.mp hk
          exact Finset.mem_filter.mpr ⟨
            Nat.mem_divisors.mpr ⟨
              (Nat.dvd_div_iff_mul_dvd han).mp hkData.1,
              hn.ne'⟩,
            Nat.dvd_mul_right a k⟩
        · intro k₁ _hk₁ k₂ _hk₂ hmul
          exact Nat.mul_left_cancel ha hmul
        · intro d hd
          have hdData := Finset.mem_filter.mp hd
          have hdDivN := (Nat.mem_divisors.mp hdData.1).1
          refine ⟨d / a, ?_, Nat.mul_div_cancel' hdData.2⟩
          apply Nat.mem_divisors.mpr
          refine ⟨?_, hquotPos.ne'⟩
          apply (Nat.dvd_div_iff_mul_dvd han).mpr
          simpa only [Nat.mul_div_cancel' hdData.2] using hdDivN
        · intro k _hk
          rw [Nat.div_div_eq_div_mul]
      _ = ∑ k ∈ (n / a).divisors,
          (ArithmeticFunction.moebius k : ℝ) := by
        rw [← Nat.sum_divisorsAntidiagonal'
            (fun x _y ↦ (ArithmeticFunction.moebius x : ℝ)),
          Nat.sum_divisorsAntidiagonal
            (fun x _y ↦ (ArithmeticFunction.moebius x : ℝ))]
      _ = if n / a = 1 then 1 else 0 := by
        exact_mod_cast
          (Erdos390.Full.HeadPattern.Pattern.sum_moebius_divisors
            (a := n / a))
      _ = if n = a then 1 else 0 := by
        by_cases hna : n = a
        · subst n
          rw [Nat.div_self ha]
          simp
        · have hquotNe : n / a ≠ 1 := by
            intro hquot
            exact hna
              (Nat.eq_of_dvd_of_div_eq_one han hquot).symm
          simp [hna, hquotNe]
  · have hna : n ≠ a := by
      intro h
      subst n
      exact han (Nat.dvd_refl a)
    rw [if_neg hna]
    apply Finset.sum_eq_zero
    intro d hd
    have hdDivN := (Nat.mem_divisors.mp hd).1
    have had : ¬a ∣ d := by
      intro had
      exact han (had.trans hdDivN)
    simp [had]

/-- Mobius inversion for sums over multiples inside the downward-closed
finite support `S(P,R)`.  This is the exact inverse relation used by the
canonical Selberg coefficients below. -/
theorem tangentSelberg_upper_moebius_inversion
    {P R t : ℕ} (ht : t ∈ tangentSelbergLambdaSupport P R)
    (F : ℕ → ℝ) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        if t ∣ d then
          ∑ r ∈ tangentSelbergLambdaSupport P R,
            if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) * F r
            else 0
        else 0) = F t := by
  classical
  let S := tangentSelbergLambdaSupport P R
  have htPos := tangentSelbergLambdaSupport_pos ht
  change
    (∑ d ∈ S, if t ∣ d then
      ∑ r ∈ S, if d ∣ r then
        (ArithmeticFunction.moebius (r / d) : ℝ) * F r else 0
      else 0) = F t
  calc
    (∑ d ∈ S, if t ∣ d then
      ∑ r ∈ S, if d ∣ r then
        (ArithmeticFunction.moebius (r / d) : ℝ) * F r else 0
      else 0) =
        ∑ d ∈ S, ∑ r ∈ S,
          if t ∣ d ∧ d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) * F r
          else 0 := by
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases htd : t ∣ d
      · simp only [htd, true_and, if_true]
      · simp [htd]
    _ = ∑ r ∈ S, ∑ d ∈ S,
        if t ∣ d ∧ d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) * F r
        else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ r ∈ S, F r *
        (∑ d ∈ S, if t ∣ d ∧ d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      by_cases htd : t ∣ d <;> by_cases hdr : d ∣ r <;>
        simp [htd, hdr, mul_comm]
    _ = ∑ r ∈ S, F r * (if r = t then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      have hrData := mem_tangentSelbergLambdaSupport.mp hr
      have hrPos := tangentSelbergLambdaSupport_pos hr
      have hfilter : S.filter (fun d ↦ d ∣ r) = r.divisors := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨_hdS, hdr⟩
          exact ⟨hdr, hrPos.ne'⟩
        · rintro ⟨hdr, _hr0⟩
          have hdLeR : d ≤ R :=
            (Nat.le_of_dvd hrPos hdr).trans hrData.2
          exact ⟨mem_tangentSelbergLambdaSupport.mpr
            ⟨⟨hdr.trans hrData.1.1, hrData.1.2⟩, hdLeR⟩, hdr⟩
      calc
        (∑ d ∈ S, if t ∣ d ∧ d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) else 0) =
            ∑ d ∈ S.filter (fun d ↦ d ∣ r),
              if t ∣ d then
                (ArithmeticFunction.moebius (r / d) : ℝ)
              else 0 := by
          rw [Finset.sum_filter]
          apply Finset.sum_congr rfl
          intro d _hd
          by_cases htd : t ∣ d <;> by_cases hdr : d ∣ r <;>
            simp [htd, hdr]
        _ = ∑ d ∈ r.divisors,
              if t ∣ d then
                (ArithmeticFunction.moebius (r / d) : ℝ)
              else 0 := by rw [hfilter]
        _ = if r = t then 1 else 0 :=
          tangent_sum_moebius_quotients_over_divisors htPos hrPos
    _ = F t := by
      have htS : t ∈ S := ht
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq']
      rw [if_pos htS]

/-- The finite diagonal density sum on the level support. -/
def tangentSelbergDensitySum (P R : ℕ) : ℝ :=
  ∑ r ∈ tangentSelbergLambdaSupport P R,
    (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ)

theorem tangentSelbergDensitySum_pos
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    0 < tangentSelbergDensitySum P R := by
  have hOneMem := one_mem_tangentSelbergLambdaSupport hP hR
  have htermNonneg : ∀ r ∈ tangentSelbergLambdaSupport P R,
      0 ≤ (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) := by
    intro r hr
    have hrPos := tangentSelbergLambdaSupport_pos hr
    have htotientPos : (0 : ℝ) < (r.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hrPos
    exact div_nonneg (sq_nonneg _) htotientPos.le
  calc
    0 < (1 : ℝ) := zero_lt_one
    _ = (ArithmeticFunction.moebius 1 : ℝ) ^ 2 /
        ((1 : ℕ).totient : ℝ) := by norm_num
    _ ≤ tangentSelbergDensitySum P R := by
      exact Finset.single_le_sum htermNonneg hOneMem

/-- Selberg's diagonal density sum is the sharp Cauchy--Schwarz lower bound
for every normalized finite Lambda family. -/
theorem tangentSelbergDensitySum_inv_le_quadratic
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    1 / tangentSelbergDensitySum P R ≤
      ∑ d ∈ tangentSelbergLambdaSupport P R,
        ∑ e ∈ tangentSelbergLambdaSupport P R,
          lambda d * lambda e / (Nat.lcm d e : ℝ) := by
  classical
  let S := tangentSelbergLambdaSupport P R
  let Y := tangentSelbergDiagonalTransform P R lambda
  have hconstraint :
      (∑ r ∈ S, (ArithmeticFunction.moebius r : ℝ) * Y r) = 1 := by
    simpa only [S, Y, hlambdaOne] using
      tangentSelberg_moebius_diagonal_constraint hP hR lambda
  have htotientPos (r : ℕ) (hr : r ∈ S) :
      (0 : ℝ) < (r.totient : ℝ) := by
    have hrPos := tangentSelbergLambdaSupport_pos hr
    exact_mod_cast Nat.totient_pos.mpr hrPos
  have hfirstNonneg : ∀ r ∈ S,
      0 ≤ (ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ) := by
    intro r hr
    exact div_nonneg (sq_nonneg _) (htotientPos r hr).le
  have hsecondNonneg : ∀ r ∈ S,
      0 ≤ (r.totient : ℝ) * Y r ^ 2 := by
    intro r _hr
    exact mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have htermSquare : ∀ r ∈ S,
      ((ArithmeticFunction.moebius r : ℝ) * Y r) ^ 2 =
        ((ArithmeticFunction.moebius r : ℝ) ^ 2 / (r.totient : ℝ)) *
          ((r.totient : ℝ) * Y r ^ 2) := by
    intro r hr
    have htotientNe := (htotientPos r hr).ne'
    field_simp [htotientNe]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul S
    hfirstNonneg hsecondNonneg htermSquare
  have hsubset : S ⊆ P.divisors := by
    exact Finset.filter_subset _ _
  have hdiagonalSubset :
      (∑ r ∈ S, (r.totient : ℝ) * Y r ^ 2) ≤
        ∑ r ∈ P.divisors, (r.totient : ℝ) * Y r ^ 2 := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun r _hrP _hrS ↦
        mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))
  have hGPos := tangentSelbergDensitySum_pos hP hR
  have hmainDiagonal :=
    tangentSelbergLambdaSquare_quadraticDiagonalization
      (R := R) hP lambda
  have honeLe :
      1 ≤ tangentSelbergDensitySum P R *
        (∑ d ∈ tangentSelbergLambdaSupport P R,
          ∑ e ∈ tangentSelbergLambdaSupport P R,
            lambda d * lambda e / (Nat.lcm d e : ℝ)) := by
    rw [hmainDiagonal]
    calc
      1 = (∑ r ∈ S,
          (ArithmeticFunction.moebius r : ℝ) * Y r) ^ 2 := by
        rw [hconstraint]
        norm_num
      _ ≤ (∑ r ∈ S,
          (ArithmeticFunction.moebius r : ℝ) ^ 2 /
            (r.totient : ℝ)) *
          (∑ r ∈ S, (r.totient : ℝ) * Y r ^ 2) := hcs
      _ ≤ tangentSelbergDensitySum P R *
          (∑ r ∈ P.divisors, (r.totient : ℝ) * Y r ^ 2) := by
        rw [tangentSelbergDensitySum]
        exact mul_le_mul_of_nonneg_left hdiagonalSubset
          (Finset.sum_nonneg hfirstNonneg)
  apply (div_le_iff₀ hGPos).2
  simpa only [one_mul, mul_comm] using honeLe

/-! ## Sharp finite coefficient norm -/

/-- Grouping pairs by lcm loses at most the triangle inequality: the full
coefficient `l1` norm is bounded by the square of the Lambda `l1` norm. -/
theorem tangentSelbergLambdaSquareCoefficient_l1_le
    {P R : ℕ} (hP : 0 < P) (lambda : ℕ → ℝ) :
    (∑ q ∈ P.divisors,
        |tangentSelbergLambdaSquareCoefficient P R lambda q|) ≤
      (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 := by
  classical
  let S := tangentSelbergLambdaSupport P R
  calc
    (∑ q ∈ P.divisors,
        |tangentSelbergLambdaSquareCoefficient P R lambda q|) ≤
        ∑ q ∈ P.divisors, ∑ d ∈ S, ∑ e ∈ S,
          |if Nat.lcm d e = q then lambda d * lambda e else 0| := by
      apply Finset.sum_le_sum
      intro q _hq
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun d _hd ↦
          Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ d ∈ S, ∑ e ∈ S, |lambda d * lambda e| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      have hdP : d ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp hd).1).1
      have heP : e ∣ P :=
        (Nat.mem_divisors.mp (Finset.mem_filter.mp he).1).1
      have hlcmMem : Nat.lcm d e ∈ P.divisors :=
        Nat.mem_divisors.mpr ⟨Nat.lcm_dvd hdP heP, hP.ne'⟩
      rw [Finset.sum_eq_single (Nat.lcm d e)]
      · rw [if_pos rfl, abs_mul]
      · intro q _hq hqNe
        rw [if_neg hqNe.symm, abs_zero]
      · exact fun hnotMem ↦ (hnotMem hlcmMem).elim
    _ = (∑ d ∈ S, |lambda d|) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro d _hd
      apply Finset.sum_congr rfl
      intro e _he
      exact abs_mul (lambda d) (lambda e)

/-! ## A concrete interval upper sieve -/

/-- Concrete Lambda-squared interval theorem.  Its main term is the exact
quadratic form and its endpoint error is the square of the Lambda `l1`
norm. -/
theorem reducedResidueIoc_card_le_lambdaSquare
    {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (lambda : ℕ → ℝ) (hlambdaOne : lambda 1 = 1) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (∑ d ∈ tangentSelbergLambdaSupport P R,
            ∑ e ∈ tangentSelbergLambdaSupport P R,
              lambda d * lambda e / (Nat.lcm d e : ℝ)) +
        (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 := by
  have hPPos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
  have hupper := reducedResidueIoc_card_le_abstractSelberg_l1
    (lo := lo) (hi := hi) hP
    (tangentSelbergLambdaSquareCoefficient P R lambda)
    (tangentSelbergLambdaSquareCoefficient_isUpperMoebius
      hPPos hR lambda hlambdaOne)
  rw [tangentIntervalReciprocalSieve_lambdaSquare_mainSum hP lambda] at hupper
  exact hupper.trans (add_le_add_right
    (tangentSelbergLambdaSquareCoefficient_l1_le hPPos lambda) _)

/-- Explicit coefficient-estimate interface.  Bounds for the quadratic form
and Lambda norm immediately give the classical two-term Selberg shape,
with no loss in either displayed constant. -/
theorem reducedResidueIoc_card_le_lambdaSquare_of_bounds
    {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
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
      ((hi - lo : ℕ) : ℝ) * mainBound + lambdaBound ^ 2 := by
  have hraw := reducedResidueIoc_card_le_lambdaSquare
    (lo := lo) (hi := hi) hP hR lambda hlambdaOne
  have hlength : (0 : ℝ) ≤ ((hi - lo : ℕ) : ℝ) := Nat.cast_nonneg _
  have hlambdaNonneg :
      0 ≤ ∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d| :=
    Finset.sum_nonneg fun d _hd ↦ abs_nonneg (lambda d)
  have hlambdaBoundNonneg : 0 ≤ lambdaBound :=
    hlambdaNonneg.trans hlambda
  have hsquare :
      (∑ d ∈ tangentSelbergLambdaSupport P R, |lambda d|) ^ 2 ≤
        lambdaBound ^ 2 := by
    nlinarith
  exact hraw.trans (add_le_add
    (mul_le_mul_of_nonneg_left hmain hlength) hsquare)

/-- Paper-level specialization `R=y^2`, so the squared coefficient bound
has exactly the `y^4/(log y)^2` scale. -/
theorem reducedResidueIoc_card_le_lambdaSquare_paperShape
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
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 := by
  have h := reducedResidueIoc_card_le_lambdaSquare_of_bounds
    (lo := lo) (hi := hi) hP (one_le_pow₀ hy) lambda hlambdaOne
      hmain hlambda
  calc
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
        ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
          (Clambda * (y : ℝ) ^ 2 / Real.log (y : ℝ)) ^ 2 := h
    _ = ((hi - lo : ℕ) : ℝ) * (Cmain / Real.log (y : ℝ)) +
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 := by ring

/-! ## Canonical finite Selberg weights -/

/-- Explicit finite Selberg weight obtained by Mobius-inverting the
diagonal target `mu(r)/(phi(r) G)`. -/
def tangentSelbergCanonicalLambda (P R d : ℕ) : ℝ :=
  if d ∈ tangentSelbergLambdaSupport P R then
    (d : ℝ) / tangentSelbergDensitySum P R *
      ∑ r ∈ tangentSelbergLambdaSupport P R,
        if d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) *
              (ArithmeticFunction.moebius r : ℝ) /
            (r.totient : ℝ)
        else 0
  else 0

/-- On its finite support, division by the index exposes the literal upper
Mobius inverse used to define the canonical weight. -/
theorem tangentSelbergCanonicalLambda_div
    {P R d : ℕ} (_hP : 0 < P) (_hR : 1 ≤ R)
    (hd : d ∈ tangentSelbergLambdaSupport P R) :
    tangentSelbergCanonicalLambda P R d / (d : ℝ) =
      (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
              ((ArithmeticFunction.moebius r : ℝ) / (r.totient : ℝ))
          else 0 := by
  have hdPos := tangentSelbergLambdaSupport_pos hd
  have hdReal : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
  rw [tangentSelbergCanonicalLambda, if_pos hd]
  calc
    ((d : ℝ) / tangentSelbergDensitySum P R *
        (∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
                (ArithmeticFunction.moebius r : ℝ) /
              (r.totient : ℝ)
          else 0)) / (d : ℝ) =
        (1 / tangentSelbergDensitySum P R) *
          (∑ r ∈ tangentSelbergLambdaSupport P R,
            if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) *
                  (ArithmeticFunction.moebius r : ℝ) /
                (r.totient : ℝ)
            else 0) := by
      rw [div_eq_mul_inv]
      have hcancel : (d : ℝ) * (d : ℝ)⁻¹ = 1 :=
        mul_inv_cancel₀ hdReal
      calc
        ((d : ℝ) / tangentSelbergDensitySum P R *
            (∑ r ∈ tangentSelbergLambdaSupport P R,
              if d ∣ r then
                (ArithmeticFunction.moebius (r / d) : ℝ) *
                    (ArithmeticFunction.moebius r : ℝ) /
                  (r.totient : ℝ)
              else 0)) * (d : ℝ)⁻¹ =
            ((d : ℝ) * (d : ℝ)⁻¹) *
              (1 / tangentSelbergDensitySum P R) *
                (∑ r ∈ tangentSelbergLambdaSupport P R,
                  if d ∣ r then
                    (ArithmeticFunction.moebius (r / d) : ℝ) *
                        (ArithmeticFunction.moebius r : ℝ) /
                      (r.totient : ℝ)
                  else 0) := by ring
        _ = _ := by rw [hcancel, one_mul]
    _ = (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
              ((ArithmeticFunction.moebius r : ℝ) / (r.totient : ℝ))
          else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _hr
      by_cases hdr : d ∣ r
      · simp only [hdr, if_true]
        ring
      · simp [hdr]

/-- The diagonal transform of the canonical weight equals the target
`mu(t)/(phi(t) G)` at every retained divisor. -/
theorem tangentSelbergCanonicalLambda_diagonalTransform_of_mem
    {P R t : ℕ} (hP : 0 < P) (hR : 1 ≤ R)
    (ht : t ∈ tangentSelbergLambdaSupport P R) :
    tangentSelbergDiagonalTransform P R
        (tangentSelbergCanonicalLambda P R) t =
      (ArithmeticFunction.moebius t : ℝ) /
        ((t.totient : ℝ) * tangentSelbergDensitySum P R) := by
  let S := tangentSelbergLambdaSupport P R
  let F : ℕ → ℝ := fun r ↦
    (ArithmeticFunction.moebius r : ℝ) / (r.totient : ℝ)
  have hinversion := tangentSelberg_upper_moebius_inversion ht F
  rw [tangentSelbergDiagonalTransform]
  change
    (∑ d ∈ S, if t ∣ d then
      tangentSelbergCanonicalLambda P R d / (d : ℝ) else 0) = _
  calc
    (∑ d ∈ S, if t ∣ d then
      tangentSelbergCanonicalLambda P R d / (d : ℝ) else 0) =
        (1 / tangentSelbergDensitySum P R) *
          (∑ d ∈ S, if t ∣ d then
            ∑ r ∈ S, if d ∣ r then
              (ArithmeticFunction.moebius (r / d) : ℝ) * F r
            else 0
          else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d hd
      by_cases htd : t ∣ d
      · simp only [htd, if_true]
        exact tangentSelbergCanonicalLambda_div hP hR hd
      · simp [htd]
    _ = (1 / tangentSelbergDensitySum P R) * F t := by
      rw [hinversion]
    _ = (ArithmeticFunction.moebius t : ℝ) /
        ((t.totient : ℝ) * tangentSelbergDensitySum P R) := by
      dsimp only [F]
      ring

/-- Total form of the canonical diagonal target.  Outside the level
support the transform vanishes because a divisor of a retained index is
itself retained. -/
theorem tangentSelbergCanonicalLambda_diagonalTransform
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) (t : ℕ) :
    tangentSelbergDiagonalTransform P R
        (tangentSelbergCanonicalLambda P R) t =
      if t ∈ tangentSelbergLambdaSupport P R then
        (ArithmeticFunction.moebius t : ℝ) /
          ((t.totient : ℝ) * tangentSelbergDensitySum P R)
      else 0 := by
  by_cases ht : t ∈ tangentSelbergLambdaSupport P R
  · rw [if_pos ht]
    exact tangentSelbergCanonicalLambda_diagonalTransform_of_mem
      hP hR ht
  · rw [if_neg ht, tangentSelbergDiagonalTransform]
    apply Finset.sum_eq_zero
    intro d hd
    have hdData := mem_tangentSelbergLambdaSupport.mp hd
    have hdPos := tangentSelbergLambdaSupport_pos hd
    have hnotDvd : ¬t ∣ d := by
      intro htd
      have htLeR : t ≤ R :=
        (Nat.le_of_dvd hdPos htd).trans hdData.2
      exact ht (mem_tangentSelbergLambdaSupport.mpr
        ⟨⟨htd.trans hdData.1.1, hdData.1.2⟩, htLeR⟩)
    simp [hnotDvd]

/-- Exact finite optimization identity for the canonical Selberg weights:
their quadratic main term attains the Cauchy--Schwarz lower bound `1/G`. -/
theorem tangentSelbergCanonicalLambda_quadratic_eq_invDensity
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
      ∑ e ∈ tangentSelbergLambdaSupport P R,
        tangentSelbergCanonicalLambda P R d *
            tangentSelbergCanonicalLambda P R e /
          (Nat.lcm d e : ℝ)) =
      1 / tangentSelbergDensitySum P R := by
  classical
  let S := tangentSelbergLambdaSupport P R
  have hGNe : tangentSelbergDensitySum P R ≠ 0 :=
    (tangentSelbergDensitySum_pos hP hR).ne'
  have hsubset : S ⊆ P.divisors := Finset.filter_subset _ _
  have hfilter : P.divisors.filter (fun r ↦ r ∈ S) = S := by
    ext r
    simp only [Finset.mem_filter]
    constructor
    · exact fun hr ↦ hr.2
    · exact fun hr ↦ ⟨hsubset hr, hr⟩
  rw [tangentSelbergLambdaSquare_quadraticDiagonalization hP]
  calc
    (∑ r ∈ P.divisors, (r.totient : ℝ) *
        tangentSelbergDiagonalTransform P R
          (tangentSelbergCanonicalLambda P R) r ^ 2) =
        ∑ r ∈ P.divisors,
          if r ∈ S then
            (r.totient : ℝ) *
              ((ArithmeticFunction.moebius r : ℝ) /
                ((r.totient : ℝ) * tangentSelbergDensitySum P R)) ^ 2
          else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      rw [tangentSelbergCanonicalLambda_diagonalTransform hP hR]
      by_cases hrS : r ∈ S <;> simp [S, hrS]
    _ = ∑ r ∈ S, (r.totient : ℝ) *
        ((ArithmeticFunction.moebius r : ℝ) /
          ((r.totient : ℝ) * tangentSelbergDensitySum P R)) ^ 2 := by
      rw [← Finset.sum_filter, hfilter]
    _ = ∑ r ∈ S,
        (1 / tangentSelbergDensitySum P R ^ 2) *
          ((ArithmeticFunction.moebius r : ℝ) ^ 2 /
            (r.totient : ℝ)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrPos := tangentSelbergLambdaSupport_pos hr
      have htotientNe : (r.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hrPos).ne'
      field_simp [htotientNe, hGNe]
    _ = (1 / tangentSelbergDensitySum P R ^ 2) *
        (∑ r ∈ S,
          (ArithmeticFunction.moebius r : ℝ) ^ 2 /
            (r.totient : ℝ)) := by
      rw [Finset.mul_sum]
    _ = (1 / tangentSelbergDensitySum P R ^ 2) *
        tangentSelbergDensitySum P R := by
      change
        (1 / tangentSelbergDensitySum P R ^ 2) *
            tangentSelbergDensitySum P R =
          (1 / tangentSelbergDensitySum P R ^ 2) *
            tangentSelbergDensitySum P R
      rfl
    _ = 1 / tangentSelbergDensitySum P R := by
      field_simp [hGNe]

/-- The canonical finite weights have the normalization required by the
Lambda-squared majorant. -/
theorem tangentSelbergCanonicalLambda_one
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    tangentSelbergCanonicalLambda P R 1 = 1 := by
  have hOneMem := one_mem_tangentSelbergLambdaSupport hP hR
  have hGNe : tangentSelbergDensitySum P R ≠ 0 :=
    (tangentSelbergDensitySum_pos hP hR).ne'
  rw [tangentSelbergCanonicalLambda, if_pos hOneMem]
  have hsum :
      (∑ r ∈ tangentSelbergLambdaSupport P R,
        if 1 ∣ r then
          (ArithmeticFunction.moebius (r / 1) : ℝ) *
              (ArithmeticFunction.moebius r : ℝ) /
            (r.totient : ℝ)
        else 0) = tangentSelbergDensitySum P R := by
    rw [tangentSelbergDensitySum]
    apply Finset.sum_congr rfl
    intro r _hr
    simp only [one_dvd, if_true, Nat.div_one]
    ring
  rw [hsum]
  field_simp [hGNe]
  norm_num

theorem tangentSelbergCanonicalLambdaSquareCoefficient_isUpperMoebius
    {P R : ℕ} (hP : 0 < P) (hR : 1 ≤ R) :
    BoundingSieve.IsUpperMoebius
      (tangentSelbergLambdaSquareCoefficient P R
        (tangentSelbergCanonicalLambda P R)) :=
  tangentSelbergLambdaSquareCoefficient_isUpperMoebius
    hP hR _ (tangentSelbergCanonicalLambda_one hP hR)

/-- For squarefree `P` and `1 ≤ R`, the concrete upper sieve with the
canonical finite Selberg weights, before rewriting the quadratic expression
by its exact optimized value. -/
theorem reducedResidueIoc_card_le_canonicalLambdaSquare
    {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (∑ d ∈ tangentSelbergLambdaSupport P R,
            ∑ e ∈ tangentSelbergLambdaSupport P R,
              tangentSelbergCanonicalLambda P R d *
                  tangentSelbergCanonicalLambda P R e /
                (Nat.lcm d e : ℝ)) +
        (∑ d ∈ tangentSelbergLambdaSupport P R,
          |tangentSelbergCanonicalLambda P R d|) ^ 2 :=
  reducedResidueIoc_card_le_lambdaSquare hP hR _
    (tangentSelbergCanonicalLambda_one
      (Nat.pos_of_ne_zero hP.ne_zero) hR)

/-- Canonical upper sieve after exact finite optimization of its main
quadratic form.  Only estimates for `G(P,R)` and the displayed Lambda norm
remain. -/
theorem reducedResidueIoc_card_le_canonicalLambdaSquare_density
    {P R lo hi : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    ((reducedResidueIoc P lo hi).card : ℝ) ≤
      ((hi - lo : ℕ) : ℝ) *
          (1 / tangentSelbergDensitySum P R) +
        (∑ d ∈ tangentSelbergLambdaSupport P R,
          |tangentSelbergCanonicalLambda P R d|) ^ 2 := by
  have h := reducedResidueIoc_card_le_canonicalLambdaSquare
    (lo := lo) (hi := hi) hP hR
  rw [tangentSelbergCanonicalLambda_quadratic_eq_invDensity
    (Nat.pos_of_ne_zero hP.ne_zero) hR] at h
  exact h

/-- Canonical `R=y^2` specialization.  Supplying the two remaining
analytic estimates gives exactly the paper's
`H/log y + y^4/(log y)^2` shape. -/
theorem reducedResidueIoc_card_le_canonicalLambdaSquare_paperShape
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
        Clambda ^ 2 * (y : ℝ) ^ 4 / Real.log (y : ℝ) ^ 2 := by
  apply reducedResidueIoc_card_le_lambdaSquare_paperShape
    hP hy (tangentSelbergCanonicalLambda P (y ^ 2))
      (tangentSelbergCanonicalLambda_one
        (Nat.pos_of_ne_zero hP.ne_zero) (one_le_pow₀ hy))
  · rw [tangentSelbergCanonicalLambda_quadratic_eq_invDensity
      (Nat.pos_of_ne_zero hP.ne_zero) (one_le_pow₀ hy)]
    exact hdensity
  · exact hlambda

end

end Erdos390.WholePaper
