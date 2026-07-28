import Erdos390.WholePaper.TangentExceptionalLambdaSquareSieve
import Erdos390.Full.PrimeBandQuadrature
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.PSeries

/-!
# Analytic bounds for the canonical exceptional-row Lambda-squared sieve

This file closes the two analytic inputs left open by
`TangentExceptionalLambdaSquareSieve`.  The constants are deliberately
coarse and fixed.  The PNT error constant and cutoff inherited from
`PrimeBandQuadrature` are named noncomputable choices, rather than numerical
values.  The proof has three ingredients.

* The verified interval Mertens theorem in `Full.PrimeBandQuadrature`
  gives a lower bound for the Euler product
  `prod_{p <= y} (1 + 1/(p-1))`.
* A logarithmic first-moment argument shows that truncating the squarefree
  divisor sum at `y^2` retains at least one tenth of that Euler product.
* A nonnegative Dirichlet-convolution majorant bounds the canonical
  Lambda `l1` norm by `exp 4 * y^2 / G`.

Thus the only constants in the final result are a named finite Mertens
loss, `10 * exp(loss)` for the main term, and an additional factor `exp 4`
for the Lambda norm.  No prime-product or coefficient estimate is assumed.
-/

open scoped BigOperators ArithmeticFunction ArithmeticFunction.Moebius
  ArithmeticFunction.sigma ArithmeticFunction.zeta
open Filter Set Topology

namespace Erdos390.WholePaper

noncomputable section

open Erdos390.Full.PrimeSums
open Erdos390.Full.PrimeBandQuadrature

/-! ## Multiplicative functions used in the Euler-product ledgers -/

/-- The total arithmetic function `1 / phi(n)`, with value zero at zero. -/
def tangentReciprocalTotientArithmeticFunction : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else 1 / (n.totient : ℝ), by simp⟩

theorem tangentReciprocalTotientArithmeticFunction_isMultiplicative :
    tangentReciprocalTotientArithmeticFunction.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [tangentReciprocalTotientArithmeticFunction], ?_⟩
  intro m n hm hn hmn
  simp only [tangentReciprocalTotientArithmeticFunction,
    ArithmeticFunction.coe_mk, hm, hn, mul_ne_zero hm hn, if_false,
    Nat.totient_mul hmn, Nat.cast_mul]
  field_simp

@[simp]
theorem tangentReciprocalTotientArithmeticFunction_apply_of_pos
    {n : ℕ} (hn : 0 < n) :
    tangentReciprocalTotientArithmeticFunction n =
      1 / (n.totient : ℝ) := by
  simp [tangentReciprocalTotientArithmeticFunction, hn.ne']

@[simp]
theorem tangentReciprocalTotientArithmeticFunction_apply_prime
    {p : ℕ} (hp : p.Prime) :
    tangentReciprocalTotientArithmeticFunction p =
      1 / ((p : ℝ) - 1) := by
  rw [tangentReciprocalTotientArithmeticFunction_apply_of_pos hp.pos,
    Nat.totient_prime hp]
  simp only [Nat.cast_sub hp.one_le, Nat.cast_one]

/-- Pointwise `sigma_1(n) / phi(n)`. -/
def tangentSigmaTotientRatioArithmeticFunction : ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (((ArithmeticFunction.sigma 1 : ArithmeticFunction ℕ) :
      ArithmeticFunction ℝ))
    tangentReciprocalTotientArithmeticFunction

theorem tangentSigmaTotientRatioArithmeticFunction_isMultiplicative :
    tangentSigmaTotientRatioArithmeticFunction.IsMultiplicative :=
  (ArithmeticFunction.isMultiplicative_sigma.natCast).pmul
    tangentReciprocalTotientArithmeticFunction_isMultiplicative

@[simp]
theorem tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
    {n : ℕ} (hn : 0 < n) :
    tangentSigmaTotientRatioArithmeticFunction n =
      ((ArithmeticFunction.sigma 1 n : ℕ) : ℝ) /
        (n.totient : ℝ) := by
  rw [tangentSigmaTotientRatioArithmeticFunction,
    ArithmeticFunction.pmul_apply,
    tangentReciprocalTotientArithmeticFunction_apply_of_pos hn]
  simp only [ArithmeticFunction.natCoe_apply]
  ring

/-- The nonnegative squarefree-supported multiplicative majorant
`mu(n)^2 prod_{p | n} (4/p)`. -/
def tangentSquarefreeFourOverPrimeArithmeticFunction :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    (ArithmeticFunction.pmul
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
        ArithmeticFunction ℝ))
      (((ArithmeticFunction.moebius : ArithmeticFunction ℤ) :
        ArithmeticFunction ℝ)))
    (ArithmeticFunction.prodPrimeFactors
      (fun p ↦ 4 / (p : ℝ)))

theorem tangentSquarefreeFourOverPrimeArithmeticFunction_isMultiplicative :
    tangentSquarefreeFourOverPrimeArithmeticFunction.IsMultiplicative :=
  ((ArithmeticFunction.isMultiplicative_moebius.intCast.pmul
      ArithmeticFunction.isMultiplicative_moebius.intCast).pmul
    (ArithmeticFunction.IsMultiplicative.prodPrimeFactors
      (fun p ↦ 4 / (p : ℝ))))

theorem tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg
    (n : ℕ) :
    0 ≤ tangentSquarefreeFourOverPrimeArithmeticFunction n := by
  rw [tangentSquarefreeFourOverPrimeArithmeticFunction,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  have hprod :
      0 ≤ (ArithmeticFunction.prodPrimeFactors
        (fun p ↦ 4 / (p : ℝ))) n := by
    by_cases hn : n = 0
    · subst n
      simp [ArithmeticFunction.prodPrimeFactors]
    · rw [ArithmeticFunction.prodPrimeFactors_apply hn]
      exact Finset.prod_nonneg fun p _hp ↦ by positivity
  exact mul_nonneg (mul_self_nonneg _) hprod

@[simp]
theorem tangentSquarefreeFourOverPrimeArithmeticFunction_apply_prime
    {p : ℕ} (hp : p.Prime) :
    tangentSquarefreeFourOverPrimeArithmeticFunction p =
      4 / (p : ℝ) := by
  have hmuZ :=
    ArithmeticFunction.moebius_sq_eq_one_of_squarefree hp.squarefree
  have hmuR : (ArithmeticFunction.moebius p : ℝ) ^ 2 = 1 := by
    exact_mod_cast hmuZ
  simp [tangentSquarefreeFourOverPrimeArithmeticFunction,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.prodPrimeFactors_apply,
    hp.ne_zero, hp]
  simpa only [pow_two] using hmuR

theorem tangentSquarefreeFourOverPrimeArithmeticFunction_eq_zero_of_not_squarefree
    {n : ℕ} (hn : ¬Squarefree n) :
    tangentSquarefreeFourOverPrimeArithmeticFunction n = 0 := by
  rw [tangentSquarefreeFourOverPrimeArithmeticFunction,
    ArithmeticFunction.pmul_apply, ArithmeticFunction.pmul_apply]
  simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hn]

/-- The previous majorant divided pointwise by `n`.  Its Euler factor at a
prime is `4/p^2`. -/
def tangentSquarefreeFourOverSquareArithmeticFunction :
    ArithmeticFunction ℝ :=
  ArithmeticFunction.pmul
    tangentSquarefreeFourOverPrimeArithmeticFunction
    tangentReciprocalArithmeticFunction

theorem tangentSquarefreeFourOverSquareArithmeticFunction_isMultiplicative :
    tangentSquarefreeFourOverSquareArithmeticFunction.IsMultiplicative :=
  tangentSquarefreeFourOverPrimeArithmeticFunction_isMultiplicative.pmul
    tangentReciprocalArithmeticFunction_isMultiplicative

theorem tangentSquarefreeFourOverSquareArithmeticFunction_nonneg
    (n : ℕ) :
    0 ≤ tangentSquarefreeFourOverSquareArithmeticFunction n := by
  rw [tangentSquarefreeFourOverSquareArithmeticFunction,
    ArithmeticFunction.pmul_apply]
  exact mul_nonneg
    (tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg n)
    (by
      by_cases hn : n = 0
      · subst n
        simp [tangentReciprocalArithmeticFunction]
      · simp [tangentReciprocalArithmeticFunction, hn])

@[simp]
theorem tangentSquarefreeFourOverSquareArithmeticFunction_apply_prime
    {p : ℕ} (hp : p.Prime) :
    tangentSquarefreeFourOverSquareArithmeticFunction p =
      4 / (p : ℝ) ^ 2 := by
  rw [tangentSquarefreeFourOverSquareArithmeticFunction,
    ArithmeticFunction.pmul_apply,
    tangentSquarefreeFourOverPrimeArithmeticFunction_apply_prime hp,
    tangentReciprocalArithmeticFunction_apply_of_pos hp.pos]
  ring

/-! ## Full density and logarithmic first moment -/

/-- The untruncated squarefree Selberg density attached to `P`. -/
def tangentSelbergFullDensitySum (P : ℕ) : ℝ :=
  ∑ r ∈ P.divisors, 1 / (r.totient : ℝ)

/-- Its logarithmic first moment. -/
def tangentSelbergFullLogMoment (P : ℕ) : ℝ :=
  ∑ r ∈ P.divisors,
    Real.log (r : ℝ) / (r.totient : ℝ)

theorem tangentSelbergFullDensitySum_eq_primeProduct
    {P : ℕ} (hP : Squarefree P) :
    tangentSelbergFullDensitySum P =
      ∏ p ∈ P.primeFactors, (1 + 1 / ((p : ℝ) - 1)) := by
  have hEuler :=
    tangentReciprocalTotientArithmeticFunction_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      hP
  rw [tangentSelbergFullDensitySum]
  symm
  calc
    (∏ p ∈ P.primeFactors, (1 + 1 / ((p : ℝ) - 1))) =
        ∏ p ∈ P.primeFactors,
          (1 + tangentReciprocalTotientArithmeticFunction p) := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [tangentReciprocalTotientArithmeticFunction_apply_prime
        (Nat.prime_of_mem_primeFactors hp)]
    _ = ∑ r ∈ P.divisors,
        tangentReciprocalTotientArithmeticFunction r := hEuler
    _ = ∑ r ∈ P.divisors, 1 / (r.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [tangentReciprocalTotientArithmeticFunction_apply_of_pos
        (Nat.pos_of_mem_divisors hr)]

theorem tangentSelbergDensitySum_eq_reciprocalTotient
    {P R : ℕ} (hP : Squarefree P) :
    tangentSelbergDensitySum P R =
      ∑ r ∈ tangentSelbergLambdaSupport P R,
        1 / (r.totient : ℝ) := by
  rw [tangentSelbergDensitySum]
  apply Finset.sum_congr rfl
  intro r hr
  have hrData := mem_tangentSelbergLambdaSupport.mp hr
  have hrsq : Squarefree r :=
    hP.squarefree_of_dvd hrData.1.1
  have hmuZ := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hrsq
  have hmuR : (ArithmeticFunction.moebius r : ℝ) ^ 2 = 1 := by
    exact_mod_cast hmuZ
  rw [hmuR]

/-! A powerset moment inequality.  It is the finite probabilistic estimate
behind the truncation: the first moment of independent nonnegative local
weights is at most their partition function times `sum b_p a_p`. -/

theorem sum_powerset_sum_mul_prod_le
    {s : Finset ℕ} (a b : ℕ → ℝ)
    (ha : ∀ p ∈ s, 0 ≤ a p) (hb : ∀ p ∈ s, 0 ≤ b p) :
    (∑ t ∈ s.powerset,
        (∑ p ∈ t, b p) * ∏ p ∈ t, a p) ≤
      (∏ p ∈ s, (1 + a p)) * ∑ p ∈ s, b p * a p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      have hap : 0 ≤ a p := ha p (Finset.mem_insert_self p s)
      have hbp : 0 ≤ b p := hb p (Finset.mem_insert_self p s)
      have haS : ∀ q ∈ s, 0 ≤ a q := by
        intro q hq
        exact ha q (Finset.mem_insert_of_mem hq)
      have hbS : ∀ q ∈ s, 0 ≤ b q := by
        intro q hq
        exact hb q (Finset.mem_insert_of_mem hq)
      let M : ℝ := ∑ t ∈ s.powerset,
        (∑ q ∈ t, b q) * ∏ q ∈ t, a q
      let W : ℝ := ∏ q ∈ s, (1 + a q)
      let B : ℝ := ∑ q ∈ s, b q * a q
      have hM : M ≤ W * B := by
        simpa only [M, W, B] using ih haS hbS
      have hW : 0 ≤ W := by
        dsimp only [W]
        exact Finset.prod_nonneg fun q hq ↦ by
          exact add_nonneg zero_le_one (haS q hq)
      have hexpand :
          (∑ t ∈ (insert p s).powerset,
              (∑ q ∈ t, b q) * ∏ q ∈ t, a q) =
            M + a p * b p * W + a p * M := by
        have hinsert :
          (∑ t ∈ s.powerset,
              (∑ q ∈ insert p t, b q) *
                ∏ q ∈ insert p t, a q) =
            a p * b p * W + a p * M := by
          calc
            (∑ t ∈ s.powerset,
                (∑ q ∈ insert p t, b q) *
                  ∏ q ∈ insert p t, a q) =
                ∑ t ∈ s.powerset,
                  ((a p * b p) * (∏ q ∈ t, a q) +
                    a p * ((∑ q ∈ t, b q) * (∏ q ∈ t, a q))) := by
              apply Finset.sum_congr rfl
              intro t ht
              have hpt : p ∉ t :=
                Finset.notMem_of_mem_powerset_of_notMem ht hp
              rw [Finset.sum_insert hpt, Finset.prod_insert hpt]
              ring
            _ = a p * b p * W + a p * M := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum,
                ← Finset.mul_sum, ← Finset.prod_one_add]
        rw [Finset.sum_powerset_insert hp, hinsert]
        change M + (a p * b p * W + a p * M) =
          M + a p * b p * W + a p * M
        ring
      have hscaled : a p * M ≤ a p * (W * B) :=
        mul_le_mul_of_nonneg_left hM hap
      rw [hexpand, Finset.prod_insert hp, Finset.sum_insert hp]
      change M + a p * b p * W + a p * M ≤
        (1 + a p) * W * (b p * a p + B)
      nlinarith [hscaled,
        mul_nonneg hap (mul_nonneg hap (mul_nonneg hbp hW))]

theorem tangentSelbergFullLogMoment_le
    {P : ℕ} (hP : Squarefree P) :
    tangentSelbergFullLogMoment P ≤
      tangentSelbergFullDensitySum P *
        (∑ p ∈ P.primeFactors,
          Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
  classical
  let a : ℕ → ℝ := fun p ↦ 1 / ((p : ℝ) - 1)
  let b : ℕ → ℝ := fun p ↦ Real.log (p : ℝ)
  have hprime (p : ℕ) (hp : p ∈ P.primeFactors) : p.Prime :=
    Nat.prime_of_mem_primeFactors hp
  have ha : ∀ p ∈ P.primeFactors, 0 ≤ a p := by
    intro p hp
    dsimp only [a]
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (hprime p hp).two_le
    exact one_div_nonneg.mpr (by linarith)
  have hb : ∀ p ∈ P.primeFactors, 0 ≤ b p := by
    intro p hp
    dsimp only [b]
    exact Real.log_nonneg (by
      exact_mod_cast (hprime p hp).one_le)
  have hpowerset := sum_powerset_sum_mul_prod_le a b ha hb
  have hdivisors :
      tangentSelbergFullLogMoment P =
        ∑ t ∈ P.primeFactors.powerset,
          (∑ p ∈ t, b p) * ∏ p ∈ t, a p := by
    rw [tangentSelbergFullLogMoment,
      ← Nat.divisors_filter_squarefree_of_squarefree hP,
      Nat.sum_divisors_filter_squarefree hP.ne_zero]
    simp only [Nat.factors_eq]
    apply Finset.sum_congr rfl
    intro t ht
    rw [t.prod_val, Function.id_def]
    have htSub : t ⊆ P.primeFactors := Finset.mem_powerset.mp ht
    have htPrime : ∀ p ∈ t, p.Prime := by
      intro p hp
      exact hprime p (htSub hp)
    have hprodPos : 0 < ∏ p ∈ t, p :=
      Finset.prod_pos fun p hp ↦ (htPrime p hp).pos
    have hlog :
        Real.log ((∏ p ∈ t, p : ℕ) : ℝ) = ∑ p ∈ t, b p := by
      rw [Nat.cast_prod, Real.log_prod]
      intro p hp
      exact_mod_cast (htPrime p hp).ne_zero
    have hrecip :
        1 / (((∏ p ∈ t, p : ℕ).totient : ℕ) : ℝ) =
          ∏ p ∈ t, a p := by
      have hmap :=
        tangentReciprocalTotientArithmeticFunction_isMultiplicative.map_prod_of_prime
          t htPrime
      rw [tangentReciprocalTotientArithmeticFunction_apply_of_pos hprodPos]
        at hmap
      calc
        1 / (((∏ p ∈ t, p : ℕ).totient : ℕ) : ℝ) =
            ∏ p ∈ t,
              tangentReciprocalTotientArithmeticFunction p := hmap
        _ = ∏ p ∈ t, a p := by
          apply Finset.prod_congr rfl
          intro p hp
          rw [tangentReciprocalTotientArithmeticFunction_apply_prime
            (htPrime p hp)]
    rw [hlog, div_eq_mul_inv]
    have hrecip' :
        ((((∏ p ∈ t, p : ℕ).totient : ℕ) : ℝ))⁻¹ =
          ∏ p ∈ t, a p := by
      simpa only [one_div] using hrecip
    rw [hrecip']
  have hdensity :
      tangentSelbergFullDensitySum P =
        ∏ p ∈ P.primeFactors, (1 + a p) := by
    simpa only [a] using tangentSelbergFullDensitySum_eq_primeProduct hP
  rw [hdivisors, hdensity]
  simpa only [a, b, div_eq_mul_inv, one_mul] using hpowerset

/-! ## Prime sums at the rough-head modulus -/

theorem roughHeadModulus_primeFactors (y : ℕ) :
    (roughHeadModulus y).primeFactors = primesUpTo y := by
  rw [roughHeadModulus]
  exact Nat.primeFactors_prod fun p hp ↦ (mem_primesUpTo.mp hp).1

theorem wholePaper_primesUpTo_eq_full_primesUpTo (y : ℕ) :
    primesUpTo y = Erdos390.Full.PrimeSums.primesUpTo y := by
  ext p
  simp [mem_primesUpTo, Erdos390.Full.PrimeSums.primesUpTo,
    and_comm]

theorem roughHead_primeFactor_logMoment_le_fullPrimeSums
    (y : ℕ) :
    (∑ p ∈ (roughHeadModulus y).primeFactors,
        Real.log (p : ℝ) / ((p : ℝ) - 1)) ≤
      fullLogReciprocalSum y + fullReciprocalSum y := by
  rw [roughHeadModulus_primeFactors,
    wholePaper_primesUpTo_eq_full_primesUpTo]
  rw [fullLogReciprocalSum, fullReciprocalSum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p hp
  have hpPrime : p.Prime := by
    have hpData : p ≤ y ∧ p.Prime := by
      simpa [Erdos390.Full.PrimeSums.primesUpTo] using hp
    exact hpData.2
  have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hpPredPos : (0 : ℝ) < (p : ℝ) - 1 := by
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hpPrime.two_le
    linarith
  have hlogLe : Real.log (p : ℝ) ≤ (p : ℝ) - 1 :=
    Real.log_le_sub_one_of_pos hpPos
  have hcorrection :
      Real.log (p : ℝ) /
          ((p : ℝ) * ((p : ℝ) - 1)) ≤
        1 / (p : ℝ) := by
    calc
      Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1)) =
          (Real.log (p : ℝ) / ((p : ℝ) - 1)) /
            (p : ℝ) := by
        field_simp [hpPos.ne', hpPredPos.ne']
      _ ≤ 1 / (p : ℝ) := by
        apply div_le_div_of_nonneg_right _ hpPos.le
        exact (div_le_one hpPredPos).2 hlogLe
  calc
    Real.log (p : ℝ) / ((p : ℝ) - 1) =
        Real.log (p : ℝ) / (p : ℝ) +
          Real.log (p : ℝ) /
            ((p : ℝ) * ((p : ℝ) - 1)) := by
      field_simp [hpPos.ne', hpPredPos.ne']
      ring
    _ ≤ Real.log (p : ℝ) / (p : ℝ) + 1 / (p : ℝ) :=
      by
        simpa only [add_comm] using
          add_le_add_right hcorrection (Real.log (p : ℝ) / (p : ℝ))

/-- The elementary Chebyshev bounds already give the strict coefficient
needed for logarithmic truncation: eventually the `1/(p-1)` logarithmic
moment is at most `9/5 log y`. -/
theorem eventually_fullPrimeMoment_le_nine_fifths_log :
    ∀ᶠ y : ℕ in atTop,
      fullLogReciprocalSum y + fullReciprocalSum y ≤
        (9 / 5 : ℝ) * Real.log (y : ℝ) := by
  let L : ℕ → ℝ := fun y ↦ Real.log (y : ℝ)
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hinvL : Tendsto (fun y : ℕ ↦ 1 / L y) atTop (nhds 0) := by
    have hone : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    exact hone.div_atTop hLTop
  have hlogRatio :
      Tendsto (fun y : ℕ ↦ Real.log (L y) / L y)
        atTop (nhds 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hmajor : Tendsto (fun y : ℕ ↦
      (2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (L y) - Real.log (Real.log 2))) / L y)
      atTop (nhds 0) := by
    have hzero : Tendsto (fun y : ℕ ↦
        (2 * Real.log 4) * (1 / L y) +
          (3 * Real.log 4) * (Real.log (L y) / L y) -
          (3 * Real.log 4 * Real.log (Real.log 2)) * (1 / L y))
        atTop (nhds 0) := by
      simpa only [mul_zero, add_zero, sub_zero] using
        ((tendsto_const_nhds.mul hinvL).add
          (tendsto_const_nhds.mul hlogRatio)).sub
            (tendsto_const_nhds.mul hinvL)
    apply hzero.congr'
    filter_upwards with y
    ring
  have hmajorSmall : ∀ᶠ y : ℕ in atTop,
      (2 * Real.log 4 + 3 * Real.log 4 *
        (Real.log (L y) - Real.log (Real.log 2))) / L y ≤
        (1 / 5 : ℝ) :=
    hmajor.eventually (eventually_le_nhds (by norm_num))
  have hlog4Upper : Real.log 4 ≤ (7 / 5 : ℝ) := by
    have hlog4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num,
        Real.log_mul (by norm_num) (by norm_num)]
      ring
    rw [hlog4]
    nlinarith [Real.log_two_lt_d9]
  have hlog4Nonneg : 0 ≤ Real.log 4 :=
    Real.log_nonneg (by norm_num)
  filter_upwards [eventually_ge_atTop 2,
    hLTop.eventually (eventually_ge_atTop (7 : ℝ)),
    hmajorSmall] with y hy2 hL7 hsmall
  have hLPos : 0 < L y := by linarith
  have hrecipRaw := fullReciprocalSum_le y hy2
  have hrecipDiv : fullReciprocalSum y / L y ≤ (1 / 5 : ℝ) := by
    calc
      fullReciprocalSum y / L y ≤
          (2 * Real.log 4 + 3 * Real.log 4 *
            (Real.log (L y) - Real.log (Real.log 2))) / L y := by
        exact div_le_div_of_nonneg_right hrecipRaw hLPos.le
      _ ≤ (1 / 5 : ℝ) := hsmall
  have hrecip :
      fullReciprocalSum y ≤ (1 / 5 : ℝ) * L y := by
    exact (div_le_iff₀ hLPos).mp hrecipDiv
  have hlogRaw := fullLogReciprocalSum_le y hy2
  have hlog :
      fullLogReciprocalSum y ≤ (8 / 5 : ℝ) * L y := by
    calc
      fullLogReciprocalSum y ≤ Real.log 4 * (1 + L y) := hlogRaw
      _ ≤ (8 / 5 : ℝ) * L y := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlog4Upper)
          (sub_nonneg.mpr hL7)]
  dsimp only [L] at hrecip hlog ⊢
  linarith

theorem eventually_roughHead_fullLogMoment_le_nine_fifths :
    ∀ᶠ y : ℕ in atTop,
      tangentSelbergFullLogMoment (roughHeadModulus y) ≤
        (9 / 5 : ℝ) * Real.log (y : ℝ) *
          tangentSelbergFullDensitySum (roughHeadModulus y) := by
  filter_upwards [eventually_fullPrimeMoment_le_nine_fifths_log]
      with y hprime
  have hEulerMoment := tangentSelbergFullLogMoment_le
    (roughHeadModulus_squarefree y)
  have hfactorNonneg :
      0 ≤ tangentSelbergFullDensitySum (roughHeadModulus y) := by
    rw [tangentSelbergFullDensitySum]
    exact Finset.sum_nonneg fun r hr ↦ by
      have hrPos := Nat.pos_of_mem_divisors hr
      have hphi : (0 : ℝ) < (r.totient : ℝ) := by
        exact_mod_cast Nat.totient_pos.mpr hrPos
      positivity
  calc
    tangentSelbergFullLogMoment (roughHeadModulus y) ≤
        tangentSelbergFullDensitySum (roughHeadModulus y) *
          (∑ p ∈ (roughHeadModulus y).primeFactors,
            Real.log (p : ℝ) / ((p : ℝ) - 1)) := hEulerMoment
    _ ≤ tangentSelbergFullDensitySum (roughHeadModulus y) *
        (fullLogReciprocalSum y + fullReciprocalSum y) := by
      exact mul_le_mul_of_nonneg_left
        (roughHead_primeFactor_logMoment_le_fullPrimeSums y) hfactorNonneg
    _ ≤ tangentSelbergFullDensitySum (roughHeadModulus y) *
        ((9 / 5 : ℝ) * Real.log (y : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hprime hfactorNonneg
    _ = (9 / 5 : ℝ) * Real.log (y : ℝ) *
        tangentSelbergFullDensitySum (roughHeadModulus y) := by ring

/-! ## Mertens lower bound for the full Euler product -/

/-- A fixed admissible left endpoint for the verified interval Mertens
estimate. -/
def tangentSelbergMertensBase : ℕ :=
  max fullReciprocalSumUniformCutoff 2

theorem tangentSelbergMertensBase_ge_cutoff :
    fullReciprocalSumUniformCutoff ≤ tangentSelbergMertensBase :=
  le_max_left _ _

theorem tangentSelbergMertensBase_ge_two :
    2 ≤ tangentSelbergMertensBase :=
  le_max_right _ _

/-- The fixed finite loss obtained by anchoring the verified interval
Mertens estimate at `tangentSelbergMertensBase`. -/
def tangentSelbergMertensLoss : ℝ :=
  |fullReciprocalSum tangentSelbergMertensBase| +
    |Real.log (Real.log (tangentSelbergMertensBase : ℝ))| +
    5 * fullReciprocalSumUniformConstant /
      Real.log (tangentSelbergMertensBase : ℝ) ^ 3

theorem tangentSelbergMertensLoss_nonneg :
    0 ≤ tangentSelbergMertensLoss := by
  have hbaseOne : 1 < tangentSelbergMertensBase :=
    lt_of_lt_of_le (by norm_num) tangentSelbergMertensBase_ge_two
  have hlog : 0 < Real.log (tangentSelbergMertensBase : ℝ) :=
    Real.log_pos (by
      exact_mod_cast hbaseOne)
  have hC := fullReciprocalSumUniformConstant_pos
  unfold tangentSelbergMertensLoss
  positivity

theorem fullReciprocalSum_ge_logLog_sub_tangentSelbergMertensLoss
    {y : ℕ} (hy : tangentSelbergMertensBase ≤ y) :
    Real.log (Real.log (y : ℝ)) - tangentSelbergMertensLoss ≤
      fullReciprocalSum y := by
  let A := tangentSelbergMertensBase
  have hquad := fullReciprocalSumUniform_bound A y
    tangentSelbergMertensBase_ge_cutoff hy
  have hlower :
      -(5 * fullReciprocalSumUniformConstant /
          Real.log (A : ℝ) ^ 3) ≤
        fullReciprocalSum y - fullReciprocalSum A -
          (Real.log (Real.log (y : ℝ)) -
            Real.log (Real.log (A : ℝ))) := by
    exact (neg_le_neg hquad).trans (neg_abs_le _)
  have hsumAbs :
      -|fullReciprocalSum A| ≤ fullReciprocalSum A :=
    neg_abs_le _
  have hlogAbs :
      -|Real.log (Real.log (A : ℝ))| ≤
        -Real.log (Real.log (A : ℝ)) := by
    exact neg_le_neg (le_abs_self _)
  dsimp only [A] at hlower hsumAbs hlogAbs ⊢
  unfold tangentSelbergMertensLoss
  linarith

private theorem exp_one_div_prime_le_one_add_inv_pred
    {p : ℕ} (hp : p.Prime) :
    Real.exp (1 / (p : ℝ)) ≤
      1 + 1 / ((p : ℝ) - 1) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hpPred : (0 : ℝ) < (p : ℝ) - 1 := by
    have hpTwo : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hp.two_le
    linarith
  have hfactor : (0 : ℝ) < 1 + 1 / ((p : ℝ) - 1) := by
    positivity
  have hlog := Real.one_sub_inv_le_log_of_pos hfactor
  have hid :
      1 - (1 + 1 / ((p : ℝ) - 1))⁻¹ = 1 / (p : ℝ) := by
    field_simp [hpR.ne', hpPred.ne']
    ring
  rw [hid] at hlog
  calc
    Real.exp (1 / (p : ℝ)) ≤
        Real.exp (Real.log (1 + 1 / ((p : ℝ) - 1))) :=
      Real.exp_le_exp.mpr hlog
    _ = 1 + 1 / ((p : ℝ) - 1) := Real.exp_log hfactor

theorem exp_fullReciprocalSum_le_roughHeadFullDensity (y : ℕ) :
    Real.exp (fullReciprocalSum y) ≤
      tangentSelbergFullDensitySum (roughHeadModulus y) := by
  rw [tangentSelbergFullDensitySum_eq_primeProduct
    (roughHeadModulus_squarefree y), roughHeadModulus_primeFactors,
    wholePaper_primesUpTo_eq_full_primesUpTo,
    fullReciprocalSum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    have hpPrime : p.Prime := by
      have hpData : p ≤ y ∧ p.Prime := by
        simpa [Erdos390.Full.PrimeSums.primesUpTo] using hp
      exact hpData.2
    exact exp_one_div_prime_le_one_add_inv_pred hpPrime

theorem roughHeadFullDensity_ge_exp_neg_loss_mul_log
    {y : ℕ} (hy : tangentSelbergMertensBase ≤ y) :
    Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) ≤
      tangentSelbergFullDensitySum (roughHeadModulus y) := by
  have hy2 : 2 ≤ y := tangentSelbergMertensBase_ge_two.trans hy
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hMertens :=
    fullReciprocalSum_ge_logLog_sub_tangentSelbergMertensLoss hy
  calc
    Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) =
        Real.exp (Real.log (Real.log (y : ℝ)) -
          tangentSelbergMertensLoss) := by
      rw [Real.exp_sub, Real.exp_log hlogPos]
      rw [Real.exp_neg]
      ring
    _ ≤ Real.exp (fullReciprocalSum y) :=
      Real.exp_le_exp.mpr hMertens
    _ ≤ tangentSelbergFullDensitySum (roughHeadModulus y) :=
      exp_fullReciprocalSum_le_roughHeadFullDensity y

/-! ## Retaining a fixed fraction below level `y^2` -/

theorem tangentSelbergFullDensitySum_le_density_add_logTail
    {P R : ℕ} (hP : Squarefree P) (hR : 1 < R) :
    tangentSelbergFullDensitySum P ≤
      tangentSelbergDensitySum P R +
        tangentSelbergFullLogMoment P / Real.log (R : ℝ) := by
  classical
  let w : ℕ → ℝ := fun r ↦ 1 / (r.totient : ℝ)
  let tail := P.divisors.filter (fun r ↦ ¬r ≤ R)
  have hlogR : 0 < Real.log (R : ℝ) :=
    Real.log_pos (by exact_mod_cast hR)
  have hw (r : ℕ) (hr : r ∈ P.divisors) : 0 ≤ w r := by
    have hrPos := Nat.pos_of_mem_divisors hr
    have hphi : (0 : ℝ) < (r.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr hrPos
    dsimp only [w]
    positivity
  have htailTerm (r : ℕ) (hr : r ∈ tail) :
      w r ≤ Real.log (r : ℝ) / Real.log (R : ℝ) * w r := by
    have hrData := Finset.mem_filter.mp hr
    have hRr : R < r := by omega
    have hRPos : (0 : ℝ) < (R : ℝ) := by
      exact_mod_cast (Nat.zero_lt_one.trans hR)
    have hlogLe : Real.log (R : ℝ) ≤ Real.log (r : ℝ) :=
      Real.log_le_log hRPos (by exact_mod_cast hRr.le)
    have hone : (1 : ℝ) ≤
        Real.log (r : ℝ) / Real.log (R : ℝ) :=
      (le_div_iff₀ hlogR).2 (by simpa using hlogLe)
    have hwr := hw r hrData.1
    nlinarith
  have htail :
      (∑ r ∈ tail, w r) ≤
        tangentSelbergFullLogMoment P / Real.log (R : ℝ) := by
    calc
      (∑ r ∈ tail, w r) ≤
          ∑ r ∈ tail,
            Real.log (r : ℝ) / Real.log (R : ℝ) * w r := by
        exact Finset.sum_le_sum fun r hr ↦ htailTerm r hr
      _ = (∑ r ∈ tail,
          Real.log (r : ℝ) / (r.totient : ℝ)) /
            Real.log (R : ℝ) := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro r _hr
        dsimp only [w]
        ring
      _ ≤ tangentSelbergFullLogMoment P / Real.log (R : ℝ) := by
        apply div_le_div_of_nonneg_right _ hlogR.le
        rw [tangentSelbergFullLogMoment]
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro r hr _hrTail
        have hrPos := Nat.pos_of_mem_divisors hr
        have hlogNonneg : 0 ≤ Real.log (r : ℝ) :=
          Real.log_nonneg (by exact_mod_cast hrPos)
        have hphi : (0 : ℝ) < (r.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr hrPos
        positivity
  have hsplit :
      tangentSelbergFullDensitySum P =
        (∑ r ∈ tangentSelbergLambdaSupport P R, w r) +
          ∑ r ∈ tail, w r := by
    rw [tangentSelbergFullDensitySum, tangentSelbergLambdaSupport]
    dsimp only [tail]
    simpa only [w] using
      (Finset.sum_filter_add_sum_filter_not P.divisors
        (fun r ↦ r ≤ R) w).symm
  rw [hsplit, tangentSelbergDensitySum_eq_reciprocalTotient hP]
  dsimp only [w]
  exact add_le_add_right htail _

theorem eventually_roughHead_density_ge_one_tenth_fullDensity :
    ∀ᶠ y : ℕ in atTop,
      tangentSelbergFullDensitySum (roughHeadModulus y) / 10 ≤
        tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_roughHead_fullLogMoment_le_nine_fifths]
      with y hy2 hmoment
  let D := tangentSelbergFullDensitySum (roughHeadModulus y)
  let G := tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2)
  let M := tangentSelbergFullLogMoment (roughHeadModulus y)
  have hyLog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hySq : 1 < y ^ 2 := by nlinarith
  have hlogSq : Real.log ((y ^ 2 : ℕ) : ℝ) =
      2 * Real.log (y : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  have htruncate := tangentSelbergFullDensitySum_le_density_add_logTail
    (roughHeadModulus_squarefree y) hySq
  have htail :
      M / Real.log ((y ^ 2 : ℕ) : ℝ) ≤ (9 / 10 : ℝ) * D := by
    rw [hlogSq]
    apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log (y : ℝ))).2
    dsimp only [M, D]
    nlinarith [hmoment]
  dsimp only [D, G, M] at htruncate htail ⊢
  linarith

/-! ## A universal `exp 4` coefficient-mean bound -/

theorem tangentSigmaTotientRatio_le_fourConvolution_of_squarefree
    {r : ℕ} (hr : Squarefree r) :
    ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
        (r.totient : ℝ) ≤
      (tangentSquarefreeFourOverPrimeArithmeticFunction *
        (ζ : ArithmeticFunction ℝ)) r := by
  let A := tangentSigmaTotientRatioArithmeticFunction
  let H := tangentSquarefreeFourOverPrimeArithmeticFunction
  have hAprod :=
    tangentSigmaTotientRatioArithmeticFunction_isMultiplicative.prod_primeFactors hr
  have hHprod :=
    tangentSquarefreeFourOverPrimeArithmeticFunction_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      hr
  have hlocal : ∀ p ∈ r.primeFactors,
      A p ≤ 1 + H p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
    have hpPred : (0 : ℝ) < (p : ℝ) - 1 := by
      have hpOneR : (1 : ℝ) < (p : ℝ) := by
        exact_mod_cast hpPrime.one_lt
      linarith
    have hsigma : ArithmeticFunction.sigma 1 p = p + 1 := by
      rw [← pow_one p,
        ArithmeticFunction.sigma_apply_prime_pow hpPrime]
      simp
    rw [show A p = ((ArithmeticFunction.sigma 1 p : ℕ) : ℝ) /
          (p.totient : ℝ) by
        exact tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
          hpPrime.pos,
      hsigma, Nat.totient_prime hpPrime]
    rw [show H p = 4 / (p : ℝ) by
      exact tangentSquarefreeFourOverPrimeArithmeticFunction_apply_prime
        hpPrime]
    rw [Nat.cast_add, Nat.cast_sub hpPrime.one_le, Nat.cast_one]
    have hp2R : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast hpPrime.two_le
    have hfrac :
        2 / ((p : ℝ) - 1) ≤ 4 / (p : ℝ) := by
      apply (div_le_div_iff₀ hpPred hpR).2
      nlinarith
    calc
      ((p : ℝ) + 1) / ((p : ℝ) - 1) =
          1 + 2 / ((p : ℝ) - 1) := by
        field_simp [hpPred.ne']
        ring
      _ ≤ 1 + 4 / (p : ℝ) := add_le_add_right hfrac 1
  have hAnonneg : ∀ p ∈ r.primeFactors, 0 ≤ A p := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    rw [show A p = ((ArithmeticFunction.sigma 1 p : ℕ) : ℝ) /
          (p.totient : ℝ) by
      exact tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
        hpPrime.pos]
    positivity
  calc
    ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) = A r := by
      symm
      exact tangentSigmaTotientRatioArithmeticFunction_apply_of_pos
        (Nat.pos_of_ne_zero hr.ne_zero)
    _ = ∏ p ∈ r.primeFactors, A p := hAprod.symm
    _ ≤ ∏ p ∈ r.primeFactors, (1 + H p) := by
      exact Finset.prod_le_prod hAnonneg hlocal
    _ = ∑ d ∈ r.divisors, H d := hHprod
    _ = (H * (ζ : ArithmeticFunction ℝ)) r := by
      rw [ArithmeticFunction.coe_mul_zeta_apply]
    _ = (tangentSquarefreeFourOverPrimeArithmeticFunction *
        (ζ : ArithmeticFunction ℝ)) r := rfl

theorem tangent_fourOverPrime_convolution_nonneg (r : ℕ) :
    0 ≤ (tangentSquarefreeFourOverPrimeArithmeticFunction *
      (ζ : ArithmeticFunction ℝ)) r := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  exact Finset.sum_nonneg fun d _hd ↦
    tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg d

private theorem roughHead_prime_reciprocalSquareSum_le_one
    {R : ℕ} (hR : 1 ≤ R) :
    (∑ p ∈ primesUpTo R, 1 / (p : ℝ) ^ 2) ≤ 1 := by
  have hsubset : primesUpTo R ⊆ Finset.Ioc 1 R := by
    intro p hp
    have hpData := mem_primesUpTo.mp hp
    exact Finset.mem_Ioc.mpr ⟨hpData.1.one_lt, hpData.2⟩
  calc
    (∑ p ∈ primesUpTo R, 1 / (p : ℝ) ^ 2) ≤
        ∑ n ∈ Finset.Ioc 1 R, 1 / (n : ℝ) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n hn _hnPrime
      positivity
    _ ≤ (1 : ℝ)⁻¹ - (R : ℝ)⁻¹ := by
      simpa only [one_div, Nat.cast_one] using
        (sum_Ioc_inv_sq_le_sub (α := ℝ)
          (k := 1) (n := R) one_ne_zero hR)
    _ ≤ 1 := by
      norm_num

theorem roughHead_fourOverSquareEulerProduct_le_exp_four
    {R : ℕ} (hR : 1 ≤ R) :
    (∏ p ∈ primesUpTo R, (1 + 4 / (p : ℝ) ^ 2)) ≤
      Real.exp 4 := by
  calc
    (∏ p ∈ primesUpTo R, (1 + 4 / (p : ℝ) ^ 2)) ≤
        ∏ p ∈ primesUpTo R, Real.exp (4 / (p : ℝ) ^ 2) := by
      apply Finset.prod_le_prod
      · intro p hp
        have hpPrime := (mem_primesUpTo.mp hp).1
        have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPrime.pos
        positivity
      · intro p hp
        simpa only [add_comm] using
          Real.add_one_le_exp (4 / (p : ℝ) ^ 2)
    _ = Real.exp (∑ p ∈ primesUpTo R, 4 / (p : ℝ) ^ 2) := by
      rw [Real.exp_sum]
    _ ≤ Real.exp 4 := by
      apply Real.exp_le_exp.mpr
      calc
        (∑ p ∈ primesUpTo R, 4 / (p : ℝ) ^ 2) =
            4 * ∑ p ∈ primesUpTo R, 1 / (p : ℝ) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        _ ≤ 4 * 1 := by
          exact mul_le_mul_of_nonneg_left
            (roughHead_prime_reciprocalSquareSum_le_one hR) (by norm_num)
        _ = 4 := by norm_num

private theorem squarefree_le_dvd_roughHeadModulus
    {q R : ℕ} (hqPos : 0 < q) (hqR : q ≤ R) (hqsq : Squarefree q) :
    q ∣ roughHeadModulus R := by
  have hsubset : q.primeFactors ⊆ primesUpTo R := by
    intro p hp
    have hpPrime := Nat.prime_of_mem_primeFactors hp
    have hpDvd := Nat.dvd_of_mem_primeFactors hp
    exact mem_primesUpTo.mpr
      ⟨hpPrime, (Nat.le_of_dvd hqPos hpDvd).trans hqR⟩
  rw [← Nat.prod_primeFactors_of_squarefree hqsq, roughHeadModulus]
  exact Finset.prod_dvd_prod_of_subset q.primeFactors (primesUpTo R) id
    hsubset

theorem sum_fourOverSquare_le_exp_four
    {R : ℕ} (hR : 1 ≤ R) :
    (∑ q ∈ Finset.Ioc 0 R,
        tangentSquarefreeFourOverSquareArithmeticFunction q) ≤
      Real.exp 4 := by
  let K := tangentSquarefreeFourOverSquareArithmeticFunction
  have hfilter :
      (∑ q ∈ Finset.Ioc 0 R, K q) =
        ∑ q ∈ (Finset.Ioc 0 R).filter Squarefree, K q := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro q hq
    by_cases hsq : Squarefree q
    · simp [hsq]
    · have hzero : K q = 0 := by
        dsimp only [K, tangentSquarefreeFourOverSquareArithmeticFunction]
        rw [ArithmeticFunction.pmul_apply,
          tangentSquarefreeFourOverPrimeArithmeticFunction_eq_zero_of_not_squarefree
            hsq,
          zero_mul]
      simp [hsq, hzero]
  have hsubset : (Finset.Ioc 0 R).filter Squarefree ⊆
      (roughHeadModulus R).divisors := by
    intro q hq
    have hqData := Finset.mem_filter.mp hq
    have hqIoc := Finset.mem_Ioc.mp hqData.1
    exact Nat.mem_divisors.mpr
      ⟨squarefree_le_dvd_roughHeadModulus hqIoc.1 hqIoc.2 hqData.2,
        (roughHeadModulus_pos R).ne'⟩
  have hEuler :=
    tangentSquarefreeFourOverSquareArithmeticFunction_isMultiplicative.prodPrimeFactors_one_add_of_squarefree
      (roughHeadModulus_squarefree R)
  calc
    (∑ q ∈ Finset.Ioc 0 R, K q) =
        ∑ q ∈ (Finset.Ioc 0 R).filter Squarefree, K q := hfilter
    _ ≤ ∑ q ∈ (roughHeadModulus R).divisors, K q := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro q hq _hqSmall
      exact tangentSquarefreeFourOverSquareArithmeticFunction_nonneg q
    _ = ∏ p ∈ (roughHeadModulus R).primeFactors,
        (1 + K p) := hEuler.symm
    _ = ∏ p ∈ primesUpTo R, (1 + 4 / (p : ℝ) ^ 2) := by
      rw [roughHeadModulus_primeFactors]
      apply Finset.prod_congr rfl
      intro p hp
      rw [show K p = 4 / (p : ℝ) ^ 2 by
        exact tangentSquarefreeFourOverSquareArithmeticFunction_apply_prime
          (mem_primesUpTo.mp hp).1]
    _ ≤ Real.exp 4 := roughHead_fourOverSquareEulerProduct_le_exp_four hR

theorem tangentSelbergSigmaTotientMean_le
    {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ r ∈ tangentSelbergLambdaSupport P R,
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ)) ≤
      Real.exp 4 * (R : ℝ) := by
  let H := tangentSquarefreeFourOverPrimeArithmeticFunction
  let K := tangentSquarefreeFourOverSquareArithmeticFunction
  let C := H * (ζ : ArithmeticFunction ℝ)
  have hsupport : tangentSelbergLambdaSupport P R ⊆ Finset.Ioc 0 R := by
    intro r hr
    have hrData := mem_tangentSelbergLambdaSupport.mp hr
    exact Finset.mem_Ioc.mpr
      ⟨tangentSelbergLambdaSupport_pos hr, hrData.2⟩
  have hpoint : ∀ r ∈ tangentSelbergLambdaSupport P R,
      ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) ≤ C r := by
    intro r hr
    have hrData := mem_tangentSelbergLambdaSupport.mp hr
    have hrsq := hP.squarefree_of_dvd hrData.1.1
    simpa only [C] using
      tangentSigmaTotientRatio_le_fourConvolution_of_squarefree hrsq
  have hconv :
      (∑ r ∈ Finset.Ioc 0 R, C r) =
        ∑ q ∈ Finset.Ioc 0 R, H q * ((R / q : ℕ) : ℝ) := by
    simpa only [C] using
      ArithmeticFunction.sum_Ioc_mul_zeta_eq_sum H R
  have hswitch :
      (∑ q ∈ Finset.Ioc 0 R, H q * ((R / q : ℕ) : ℝ)) ≤
        (R : ℝ) * ∑ q ∈ Finset.Ioc 0 R, K q := by
    calc
      (∑ q ∈ Finset.Ioc 0 R,
          H q * ((R / q : ℕ) : ℝ)) ≤
          ∑ q ∈ Finset.Ioc 0 R,
            H q * ((R : ℝ) / (q : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left Nat.cast_div_le
        exact tangentSquarefreeFourOverPrimeArithmeticFunction_nonneg q
      _ = (R : ℝ) * ∑ q ∈ Finset.Ioc 0 R, K q := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        have hqPos := (Finset.mem_Ioc.mp hq).1
        rw [show K q = H q * (1 / (q : ℝ)) by
          dsimp only [K, tangentSquarefreeFourOverSquareArithmeticFunction]
          rw [ArithmeticFunction.pmul_apply,
            tangentReciprocalArithmeticFunction_apply_of_pos hqPos]]
        ring
  calc
    (∑ r ∈ tangentSelbergLambdaSupport P R,
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ)) ≤
        ∑ r ∈ tangentSelbergLambdaSupport P R, C r := by
      exact Finset.sum_le_sum hpoint
    _ ≤ ∑ r ∈ Finset.Ioc 0 R, C r := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsupport
      intro r hr _hrS
      exact tangent_fourOverPrime_convolution_nonneg r
    _ = ∑ q ∈ Finset.Ioc 0 R,
        H q * ((R / q : ℕ) : ℝ) := hconv
    _ ≤ (R : ℝ) * ∑ q ∈ Finset.Ioc 0 R, K q := hswitch
    _ ≤ (R : ℝ) * Real.exp 4 := by
      exact mul_le_mul_of_nonneg_left (sum_fourOverSquare_le_exp_four hR)
        (Nat.cast_nonneg R)
    _ = Real.exp 4 * (R : ℝ) := by ring

/-! ## The canonical Lambda norm -/

theorem tangentSelbergCanonicalLambda_abs_le
    {P R d : ℕ} (hP : Squarefree P) (hR : 1 ≤ R)
    (hd : d ∈ tangentSelbergLambdaSupport P R) :
    |tangentSelbergCanonicalLambda P R d| ≤
      (d : ℝ) / tangentSelbergDensitySum P R *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
  let S := tangentSelbergLambdaSupport P R
  have hPPos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
  have hGPos : 0 < tangentSelbergDensitySum P R :=
    tangentSelbergDensitySum_pos hPPos hR
  have hdPos := tangentSelbergLambdaSupport_pos hd
  have hfactor : 0 ≤ (d : ℝ) / tangentSelbergDensitySum P R := by
    positivity
  rw [tangentSelbergCanonicalLambda, if_pos hd, abs_mul,
    abs_of_nonneg hfactor]
  apply mul_le_mul_of_nonneg_left _ hfactor
  calc
    |∑ r ∈ S,
        if d ∣ r then
          (ArithmeticFunction.moebius (r / d) : ℝ) *
              (ArithmeticFunction.moebius r : ℝ) /
            (r.totient : ℝ)
        else 0| ≤
        ∑ r ∈ S,
          |if d ∣ r then
            (ArithmeticFunction.moebius (r / d) : ℝ) *
                (ArithmeticFunction.moebius r : ℝ) /
              (r.totient : ℝ)
          else 0| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ r ∈ S,
        if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hdr : d ∣ r
      · have hrData := mem_tangentSelbergLambdaSupport.mp hr
        have hrsq : Squarefree r := hP.squarefree_of_dvd hrData.1.1
        have hquotDvd : r / d ∣ r := by
          refine ⟨d, ?_⟩
          exact (Nat.div_mul_cancel hdr).symm
        have hquotSq : Squarefree (r / d) :=
          hrsq.squarefree_of_dvd hquotDvd
        have hmuQuotZ :=
          ArithmeticFunction.abs_moebius_eq_one_of_squarefree hquotSq
        have hmuRZ :=
          ArithmeticFunction.abs_moebius_eq_one_of_squarefree hrsq
        have hmuQuot :
            |(ArithmeticFunction.moebius (r / d) : ℝ)| = 1 := by
          exact_mod_cast hmuQuotZ
        have hmuR : |(ArithmeticFunction.moebius r : ℝ)| = 1 := by
          exact_mod_cast hmuRZ
        have hrPos := tangentSelbergLambdaSupport_pos hr
        have hphi : (0 : ℝ) < (r.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr hrPos
        simp only [hdr, if_true, abs_div, abs_mul, hmuQuot, hmuR,
          one_mul, abs_of_pos hphi]
      · simp [hdr]

theorem tangentSelbergCanonicalLambda_l1_le_sigmaTotientMean
    {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
      (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
            (r.totient : ℝ) := by
  classical
  let S := tangentSelbergLambdaSupport P R
  let G := tangentSelbergDensitySum P R
  have hcoeff : ∀ d ∈ S,
      |tangentSelbergCanonicalLambda P R d| ≤
        (d : ℝ) / G *
          ∑ r ∈ S, if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
    intro d hd
    simpa only [S, G] using
      tangentSelbergCanonicalLambda_abs_le hP hR hd
  have hdivisorSum : ∀ r ∈ S,
      (∑ d ∈ S, if d ∣ r then (d : ℝ) else 0) =
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) := by
    intro r hr
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
    rw [← Finset.sum_filter, hfilter,
      ← Nat.cast_sum, ← ArithmeticFunction.sigma_one_apply]
  calc
    (∑ d ∈ S, |tangentSelbergCanonicalLambda P R d|) ≤
        ∑ d ∈ S, (d : ℝ) / G *
          ∑ r ∈ S,
            if d ∣ r then 1 / (r.totient : ℝ) else 0 := by
      exact Finset.sum_le_sum hcoeff
    _ = ∑ r ∈ S, (1 / G) *
        ∑ d ∈ S,
          if d ∣ r then (d : ℝ) / (r.totient : ℝ) else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hdr : d ∣ r
      · simp only [hdr, if_true]
        ring
      · simp [hdr]
    _ = ∑ r ∈ S, (1 / G) *
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hinner :
        (∑ d ∈ S,
            if d ∣ r then (d : ℝ) / (r.totient : ℝ) else 0) =
            (∑ d ∈ S, if d ∣ r then (d : ℝ) else 0) /
              (r.totient : ℝ) := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro d hd
          by_cases hdr : d ∣ r <;> simp [hdr]
      rw [hinner, hdivisorSum r hr]
      ring
    _ = (1 / G) * ∑ r ∈ S,
        ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
          (r.totient : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ = (1 / tangentSelbergDensitySum P R) *
        ∑ r ∈ tangentSelbergLambdaSupport P R,
          ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
            (r.totient : ℝ) := rfl

theorem tangentSelbergCanonicalLambda_l1_le_exp_four_mul_level_div_density
    {P R : ℕ} (hP : Squarefree P) (hR : 1 ≤ R) :
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
      Real.exp 4 * (R : ℝ) /
        tangentSelbergDensitySum P R := by
  have hPPos : 0 < P := Nat.pos_of_ne_zero hP.ne_zero
  have hGPos := tangentSelbergDensitySum_pos hPPos hR
  have hmean := tangentSelbergSigmaTotientMean_le hP hR
  calc
    (∑ d ∈ tangentSelbergLambdaSupport P R,
        |tangentSelbergCanonicalLambda P R d|) ≤
        (1 / tangentSelbergDensitySum P R) *
          ∑ r ∈ tangentSelbergLambdaSupport P R,
            ((ArithmeticFunction.sigma 1 r : ℕ) : ℝ) /
              (r.totient : ℝ) :=
      tangentSelbergCanonicalLambda_l1_le_sigmaTotientMean hP hR
    _ ≤ (1 / tangentSelbergDensitySum P R) *
        (Real.exp 4 * (R : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hmean (by positivity)
    _ = Real.exp 4 * (R : ℝ) /
        tangentSelbergDensitySum P R := by ring

/-! ## Fixed eventual constants and the closed interval theorem -/

/-- Fixed named main-term constant. -/
def tangentSelbergCanonicalMainConstant : ℝ :=
  10 * Real.exp tangentSelbergMertensLoss

/-- Fixed named canonical-Lambda `l1`-norm constant.  Its square is the
coefficient of the `y^4 / log(y)^2` endpoint term in the final interval
estimate. -/
def tangentSelbergCanonicalLambdaConstant : ℝ :=
  Real.exp 4 * tangentSelbergCanonicalMainConstant

theorem tangentSelbergCanonicalMainConstant_pos :
    0 < tangentSelbergCanonicalMainConstant := by
  unfold tangentSelbergCanonicalMainConstant
  positivity

theorem tangentSelbergCanonicalLambdaConstant_pos :
    0 < tangentSelbergCanonicalLambdaConstant := by
  unfold tangentSelbergCanonicalLambdaConstant
  exact mul_pos (Real.exp_pos 4) tangentSelbergCanonicalMainConstant_pos

/-- The two coefficient estimates needed by the canonical paper-shape
theorem, with fixed named constants and one common eventual cutoff. -/
theorem eventually_tangentSelbergCanonical_coefficientBounds :
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
            Real.log (y : ℝ) := by
  filter_upwards [eventually_ge_atTop tangentSelbergMertensBase,
    eventually_roughHead_density_ge_one_tenth_fullDensity]
      with y hyBase hfraction
  have hy2 : 2 ≤ y := tangentSelbergMertensBase_ge_two.trans hyBase
  have hyOne : 1 ≤ y := by omega
  have hlogPos : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hGPos :
      0 < tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) :=
    tangentSelbergDensitySum_pos (roughHeadModulus_pos y)
      (one_le_pow₀ hyOne)
  have hfull := roughHeadFullDensity_ge_exp_neg_loss_mul_log hyBase
  have hlower :
      Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) / 10 ≤
        tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
    calc
      Real.exp (-tangentSelbergMertensLoss) * Real.log (y : ℝ) / 10 ≤
          tangentSelbergFullDensitySum (roughHeadModulus y) / 10 := by
        exact div_le_div_of_nonneg_right hfull (by norm_num)
      _ ≤ tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) :=
        hfraction
  have hcross :
      Real.log (y : ℝ) ≤
        tangentSelbergCanonicalMainConstant *
          tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
    calc
      Real.log (y : ℝ) =
          tangentSelbergCanonicalMainConstant *
            (Real.exp (-tangentSelbergMertensLoss) *
              Real.log (y : ℝ) / 10) := by
        unfold tangentSelbergCanonicalMainConstant
        rw [Real.exp_neg]
        field_simp [Real.exp_ne_zero]
      _ ≤ tangentSelbergCanonicalMainConstant *
          tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) := by
        exact mul_le_mul_of_nonneg_left hlower
          tangentSelbergCanonicalMainConstant_pos.le
  have hdensity :
      1 / tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) ≤
        tangentSelbergCanonicalMainConstant / Real.log (y : ℝ) := by
    apply (div_le_div_iff₀ hGPos hlogPos).2
    simpa only [one_mul] using hcross
  have hnormRaw :=
    tangentSelbergCanonicalLambda_l1_le_exp_four_mul_level_div_density
      (P := roughHeadModulus y) (R := y ^ 2)
      (roughHeadModulus_squarefree y) (one_le_pow₀ hyOne)
  have hfactorNonneg :
      0 ≤ Real.exp 4 * (y : ℝ) ^ 2 := by positivity
  have hnorm :
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
        tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
          Real.log (y : ℝ) := by
    calc
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
          Real.exp 4 * ((y ^ 2 : ℕ) : ℝ) /
            tangentSelbergDensitySum (roughHeadModulus y) (y ^ 2) :=
        hnormRaw
      _ = (Real.exp 4 * (y : ℝ) ^ 2) *
          (1 / tangentSelbergDensitySum
            (roughHeadModulus y) (y ^ 2)) := by
        rw [Nat.cast_pow]
        ring
      _ ≤ (Real.exp 4 * (y : ℝ) ^ 2) *
          (tangentSelbergCanonicalMainConstant /
            Real.log (y : ℝ)) := by
        exact mul_le_mul_of_nonneg_left hdensity hfactorNonneg
      _ = tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
          Real.log (y : ℝ) := by
        unfold tangentSelbergCanonicalLambdaConstant
        ring
  exact ⟨hdensity, hnorm⟩

theorem eventually_tangentSelbergCanonical_invDensity_le :
    ∀ᶠ y : ℕ in atTop,
      1 / tangentSelbergDensitySum
          (roughHeadModulus y) (y ^ 2) ≤
        tangentSelbergCanonicalMainConstant / Real.log (y : ℝ) :=
  eventually_tangentSelbergCanonical_coefficientBounds.mono
    fun _ h ↦ h.1

theorem eventually_tangentSelbergCanonical_l1_le :
    ∀ᶠ y : ℕ in atTop,
      (∑ d ∈ tangentSelbergLambdaSupport
          (roughHeadModulus y) (y ^ 2),
          |tangentSelbergCanonicalLambda
            (roughHeadModulus y) (y ^ 2) d|) ≤
        tangentSelbergCanonicalLambdaConstant * (y : ℝ) ^ 2 /
          Real.log (y : ℝ) :=
  eventually_tangentSelbergCanonical_coefficientBounds.mono
    fun _ h ↦ h.2

/-- Natural-number cutoff form of the two bounds, exposing a common
threshold at least `2` so that every logarithmic denominator is positive. -/
theorem exists_tangentSelbergCanonical_coefficientBounds_cutoff :
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
              Real.log (y : ℝ) := by
  have hbounds := eventually_tangentSelbergCanonical_coefficientBounds
  rw [eventually_atTop] at hbounds
  obtain ⟨Y, hY⟩ := hbounds
  refine ⟨max 2 Y, le_max_left _ _, fun y hy ↦ ?_⟩
  exact hY y ((le_max_right 2 Y).trans hy)

/-- Assumption-free eventual paper-shape interval estimate for the actual
rough-head modulus and the actual canonical finite Selberg weights. -/
theorem eventually_reducedResidueIoc_card_le_canonicalLambdaSquare_roughHead :
    ∀ᶠ y : ℕ in atTop, ∀ lo hi : ℕ,
      ((reducedResidueIoc (roughHeadModulus y) lo hi).card : ℝ) ≤
        ((hi - lo : ℕ) : ℝ) *
            (tangentSelbergCanonicalMainConstant /
              Real.log (y : ℝ)) +
          tangentSelbergCanonicalLambdaConstant ^ 2 * (y : ℝ) ^ 4 /
            Real.log (y : ℝ) ^ 2 := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_tangentSelbergCanonical_coefficientBounds]
      with y hy2 hbounds
  intro lo hi
  exact reducedResidueIoc_card_le_canonicalLambdaSquare_paperShape
    (roughHeadModulus_squarefree y) (by omega) hbounds.1 hbounds.2

end

end Erdos390.WholePaper
