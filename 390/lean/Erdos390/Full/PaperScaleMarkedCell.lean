import Erdos390.Full.PaperScaleEndpoint
import Erdos390.Full.DivisibilityMomentBounds

/-!
# Paper-scale common main term for marked structured cells

The raw structured-cell asymptotic is a finite sum of endpoint Dickman
terms.  This module performs the algebraic closure required in the paper:
the head Möbius coefficient is evaluated exactly, and the endpoint terms
are compared with one common Dickman translate before normalization.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.PaperScaleMarkedCell

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic
open StructuredCellAsymptotic
open DivisibilityMomentBounds

noncomputable section

/-! ## Exact closure of the head Möbius coefficient -/

private def reciprocalAF : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else 1 / (n : ℝ), by simp⟩

private theorem reciprocalAF_isMultiplicative :
    reciprocalAF.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [reciprocalAF], ?_⟩
  intro m n hm hn hcop
  simp only [reciprocalAF, ArithmeticFunction.coe_mk, hm, hn,
    mul_ne_zero hm hn, if_false, Nat.cast_mul]
  field_simp

private theorem modulus_squarefree (P : Pattern) : Squarefree P.modulus := by
  unfold Pattern.modulus
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (P.prime_mem p hp) (P.prime_mem q hq)).mpr hpq)
  · intro p hp
    exact (P.prime_mem p hp).squarefree

/-- The exact identity
`sum_{a | M_H} mu(a)/a = phi(M_H)/M_H`, in the real field used by the
analytic estimates. -/
theorem sum_moebius_div_inv_eq_totient_ratio (P : Pattern) :
    (∑ a ∈ P.modulus.divisors,
        (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) =
      (P.modulus.totient : ℝ) / (P.modulus : ℝ) := by
  have hprod := reciprocalAF_isMultiplicative.prodPrimeFactors_one_sub_of_squarefree
    reciprocalAF (modulus_squarefree P)
  have hprod' :
      (∏ p ∈ P.modulus.primeFactors, (1 - 1 / (p : ℝ))) =
        ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) := by
    calc
      _ = ∏ p ∈ P.modulus.primeFactors, (1 - reciprocalAF p) := by
        apply Finset.prod_congr rfl
        intro p hp
        have hp0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
        simp [reciprocalAF, hp0]
      _ = ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) * reciprocalAF a := hprod
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a ha
        have ha0 := (Nat.pos_of_mem_divisors ha).ne'
        simp [reciprocalAF, ha0, div_eq_mul_inv]
  have htotQ := Nat.totient_eq_mul_prod_factors P.modulus
  have htotR :
      (P.modulus.totient : ℝ) =
        (P.modulus : ℝ) *
          ∏ p ∈ P.modulus.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hcast := congrArg (fun q : ℚ => (q : ℝ)) htotQ
    norm_num at hcast
    simpa [one_div] using hcast
  rw [← hprod']
  have hmod : (P.modulus : ℝ) ≠ 0 := by
    exact_mod_cast P.modulus_ne_zero
  apply (eq_div_iff hmod).2
  nlinarith

/-- The fixed positive density of a prescribed head valuation pattern. -/
def headDensity (P : Pattern) : ℝ :=
  (1 / (P.factor : ℝ)) *
    ((P.modulus.totient : ℝ) / (P.modulus : ℝ))

theorem headDensity_pos (P : Pattern) : 0 < headDensity P := by
  have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
  have hmod : (0 : ℝ) < (P.modulus : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero P.modulus_ne_zero
  have htot : (0 : ℝ) < (P.modulus.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.pos_of_ne_zero P.modulus_ne_zero)
  exact mul_pos (one_div_pos.mpr hfactor) (div_pos htot hmod)

/-- Möbius closure including the forced head factor. -/
theorem head_moebius_coefficient_eq_density (P : Pattern) :
    (1 / (P.factor : ℝ)) *
        (∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) / (a : ℝ)) =
      headDensity P := by
  rw [sum_moebius_div_inv_eq_totient_ratio]
  rfl

/-! ## The common paper-scale main term -/

/-- The single main term remaining after both endpoint specialization and
head Möbius closure. -/
def paperMarkedMain (P : Pattern) (A B : ℝ) (n d : ℕ) : ℝ :=
  headDensity P * ((B - A) * (n : ℝ) / (d : ℝ)) *
    rho (paperDivisorCoordinate n d)

/-- The positive unmarked density of one fixed physical/head cell. -/
def paperCellDensity (P : Pattern) (A B : ℝ) : ℝ :=
  headDensity P * (B - A) * rho DickmanBasic.U

theorem paperCellDensity_pos (P : Pattern) {A B : ℝ} (hAB : A < B) :
    0 < paperCellDensity P A B := by
  exact mul_pos (mul_pos (headDensity_pos P) (sub_pos.mpr hAB)) rho_U_pos

/-- The paper's normalized marked-divisor main term. -/
def paperDivisibilityMain (n d : ℕ) : ℝ :=
  (rho (paperDivisorCoordinate n d) / rho DickmanBasic.U) / (d : ℝ)

@[simp] theorem paperDivisorCoordinate_one (n : ℕ) :
    paperDivisorCoordinate n 1 = DickmanBasic.U := by
  simp [paperDivisorCoordinate]

@[simp] theorem paperDivisibilityMain_one (n : ℕ) :
    paperDivisibilityMain n 1 = 1 := by
  simp [paperDivisibilityMain, rho_U_ne_zero]

theorem paperMarkedMain_eq_density_mul_divisibility
    (P : Pattern) (A B : ℝ) {n d : ℕ} (hd : 0 < d) :
    paperMarkedMain P A B n d =
      paperCellDensity P A B * (n : ℝ) * paperDivisibilityMain n d := by
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hrho : rho DickmanBasic.U ≠ 0 := rho_U_ne_zero
  unfold paperMarkedMain paperCellDensity paperDivisibilityMain
  field_simp [hdR, hrho]

@[simp] theorem paperMarkedMain_one (P : Pattern) (A B : ℝ) (n : ℕ) :
    paperMarkedMain P A B n 1 = paperCellDensity P A B * (n : ℝ) := by
  rw [paperMarkedMain_eq_density_mul_divisibility P A B (n := n)
    (d := 1) (by omega), paperDivisibilityMain_one]
  ring

/-- Four marks keep the paper coordinate inside the range on which the
constructed Dickman function is positive. -/
theorem paperDivisorCoordinate_mem_zero_five {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisorCoordinate n d ∧ paperDivisorCoordinate n d ≤ 5 := by
  have hnpos : 0 < n := by omega
  have hypos : 0 < y n := y_pos hnpos
  have hylog : 0 < Real.log (y n) := by
    rw [log_y hnpos]
    exact mul_pos (by norm_num) (L_pos hn)
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hlogd0 : 0 ≤ Real.log (d : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hd)
  have hyNatPos : 0 < yNat n := by
    by_contra hnot
    have hyNat0 : yNat n = 0 := Nat.eq_zero_of_not_pos hnot
    simp [hyNat0] at hd4
    omega
  have hyNatRpos : (0 : ℝ) < (yNat n : ℝ) := by exact_mod_cast hyNatPos
  have hdCast : (d : ℝ) ≤ (yNat n : ℝ) ^ 4 := by exact_mod_cast hd4
  have hlogdNat : Real.log (d : ℝ) ≤
      4 * Real.log (yNat n : ℝ) := by
    have h := Real.log_le_log hdR hdCast
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  have hyNatUpper : (yNat n : ℝ) ≤ y n :=
    Nat.floor_le hypos.le
  have hlogNatY : Real.log (yNat n : ℝ) ≤ Real.log (y n) :=
    Real.log_le_log hyNatRpos hyNatUpper
  have hlogdY : Real.log (d : ℝ) ≤ 4 * Real.log (y n) := by
    calc
      Real.log (d : ℝ) ≤ 4 * Real.log (yNat n : ℝ) := hlogdNat
      _ ≤ 4 * Real.log (y n) := by linarith
  have hquot0 : 0 ≤ Real.log (d : ℝ) / Real.log (y n) :=
    div_nonneg hlogd0 hylog.le
  have hquot4 : Real.log (d : ℝ) / Real.log (y n) ≤ 4 :=
    (div_le_iff₀ hylog).2 (by simpa using hlogdY)
  unfold paperDivisorCoordinate DickmanBasic.U
  constructor <;> linarith

theorem paperDivisibilityMain_nonneg_le {n d : ℕ}
    (hn : 1 < n) (hd : 0 < d) (hd4 : d ≤ yNat n ^ 4) :
    0 ≤ paperDivisibilityMain n d ∧
      paperDivisibilityMain n d ≤
        1 / (rho DickmanBasic.U * (d : ℝ)) := by
  have hv := paperDivisorCoordinate_mem_zero_five hn hd hd4
  have hrv : 0 < rho (paperDivisorCoordinate n d) :=
    rho_pos_on_zero_five hv.1 hv.2
  have hrv1 : rho (paperDivisorCoordinate n d) ≤ 1 :=
    FriableAsymptotic.rho_le_one_of_le_five hv.2
  have hrU : 0 < rho DickmanBasic.U := rho_U_pos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  unfold paperDivisibilityMain
  constructor
  · positivity
  · rw [div_div]
    exact div_le_div_of_nonneg_right hrv1 (mul_pos hrU hdR).le

/-- Once every endpoint has the same Dickman translate, the complete
Möbius sum is exactly the paper's head-density main term. -/
theorem common_endpoint_sum_eq_paperMarkedMain
    (P : Pattern) (A B R : ℝ) {n d : ℕ} (hd : 0 < d) :
    (∑ a ∈ P.modulus.divisors,
        (ArithmeticFunction.moebius a : ℝ) *
          ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) * R -
            (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) * R)) =
      headDensity P * ((B - A) * (n : ℝ) / (d : ℝ)) * R := by
  have hfactor : (P.factor : ℝ) ≠ 0 := by
    exact_mod_cast P.factor_ne_zero
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  calc
    _ = ((1 / (P.factor : ℝ)) *
          (∑ a ∈ P.modulus.divisors,
            (ArithmeticFunction.moebius a : ℝ) / (a : ℝ))) *
        ((B - A) * (n : ℝ) / (d : ℝ)) * R := by
      rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      have haR : (a : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.pos_of_mem_divisors ha).ne'
      norm_num only [Nat.cast_mul]
      field_simp [hfactor, haR, hdR]
    _ = headDensity P * ((B - A) * (n : ℝ) / (d : ℝ)) * R := by
      rw [head_moebius_coefficient_eq_density]

/-- Fixed coefficient in the error of one physical endpoint. -/
def endpointCoefficient (C : ℝ) (g : ℕ) : ℝ :=
  2 + 5 * (Real.log 2 + |Real.log C - Real.log (g : ℝ)|) +
    (45 / 2 : ℝ) * Real.log 2

theorem endpointCoefficient_nonneg (C : ℝ) (g : ℕ) :
    0 ≤ endpointCoefficient C g := by
  unfold endpointCoefficient
  positivity

/-- Total fixed endpoint-error coefficient after head inclusion--exclusion. -/
def endpointFamilyCoefficient (P : Pattern) (C : ℝ) : ℝ :=
  ∑ a ∈ P.modulus.divisors,
    |(ArithmeticFunction.moebius a : ℝ)| *
      (endpointCoefficient C (P.factor * a) *
        C / ((P.factor * a : ℕ) : ℝ))

theorem endpointFamilyCoefficient_nonneg (P : Pattern) {C : ℝ}
    (hC : 0 ≤ C) : 0 ≤ endpointFamilyCoefficient P C := by
  unfold endpointFamilyCoefficient
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg
      (mul_nonneg (endpointCoefficient_nonneg C (P.factor * a)) hC)
      (by positivity))

/-- Uniformly replacing every head-divisor endpoint by the common paper
translate costs only `O(n/(d log n))`; the right-hand coefficient is a
fixed finite sum depending on the head pattern and physical endpoints. -/
theorem headDivisorMain_sum_sub_common_le
    (P : Pattern) {A B : ℝ} {n d : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hn : 1 < n) (hd : 0 < d)
    (hd4 : d ≤ yNat n ^ 4) (hy2 : 2 ≤ y n)
    (hlogLower : (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ))
    (hmarginA : ∀ a ∈ P.modulus.divisors,
      4 ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      L n ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ))
    (hmarginB : ∀ a ∈ P.modulus.divisors,
      4 ≤ B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      L n ≤ B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ))
    (hlogA : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ))
    (hlogB : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ)) :
    |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a) -
        ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) *
            ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))| ≤
      (endpointFamilyCoefficient P B + endpointFamilyCoefficient P A) *
        (n : ℝ) / ((d : ℝ) * L n) := by
  have hL : 0 < L n := L_pos hn
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a ∈ P.modulus.divisors,
        (headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a -
          (ArithmeticFunction.moebius a : ℝ) *
            ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)))| ≤
      ∑ a ∈ P.modulus.divisors,
        |headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a -
          (ArithmeticFunction.moebius a : ℝ) *
            ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (endpointCoefficient B (P.factor * a) *
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n +
            endpointCoefficient A (P.factor * a) *
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n) := by
      apply Finset.sum_le_sum
      intro a ha
      have hEndB := endpointMain_common_paper_bound B n
        (P.factor * a) d hB hn
        (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
          (Nat.pos_of_mem_divisors ha)) hd hd4 hy2 hlogLower
        (hmarginB a ha).1 (hmarginB a ha).2 (hlogB a ha)
      have hEndA := endpointMain_common_paper_bound A n
        (P.factor * a) d hA hn
        (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
          (Nat.pos_of_mem_divisors ha)) hd hd4 hy2 hlogLower
        (hmarginA a ha).1 (hmarginA a ha).2 (hlogA a ha)
      rw [show
        headDivisorMain P (physicalBound A n) (physicalBound B n)
              (yNat n) d a -
            (ArithmeticFunction.moebius a : ℝ) *
              ((B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                  rho (paperDivisorCoordinate n d) -
                (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                  rho (paperDivisorCoordinate n d)) =
          (ArithmeticFunction.moebius a : ℝ) *
            ((endpointMain (physicalBound B n / (P.factor * a * d))
                (yNat n) -
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)) -
             (endpointMain (physicalBound A n / (P.factor * a * d))
                (yNat n) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))) by
        unfold headDivisorMain
        ring]
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have hEndB' :
          |endpointMain (physicalBound B n / (P.factor * a * d)) (yNat n) -
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)| ≤
            endpointCoefficient B (P.factor * a) *
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n := by
        simpa only [endpointCoefficient] using hEndB
      have hEndA' :
          |endpointMain (physicalBound A n / (P.factor * a * d)) (yNat n) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)| ≤
            endpointCoefficient A (P.factor * a) *
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) / L n := by
        simpa only [endpointCoefficient] using hEndA
      calc
        |_ - _| ≤ |endpointMain
              (physicalBound B n / (P.factor * a * d)) (yNat n) -
            (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
              rho (paperDivisorCoordinate n d)| +
          |endpointMain (physicalBound A n / (P.factor * a * d)) (yNat n) -
            (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
              rho (paperDivisorCoordinate n d)| := by
          rw [sub_eq_add_neg]
          simpa only [abs_neg] using abs_add_le
            (endpointMain (physicalBound B n / (P.factor * a * d)) (yNat n) -
              (B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d))
            (-(endpointMain (physicalBound A n / (P.factor * a * d)) (yNat n) -
              (A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ)) *
                rho (paperDivisorCoordinate n d)))
        _ ≤ _ := add_le_add hEndB' hEndA'
    _ = (endpointFamilyCoefficient P B + endpointFamilyCoefficient P A) *
        (n : ℝ) / ((d : ℝ) * L n) := by
      unfold endpointFamilyCoefficient
      have hdist (f : ℕ → ℝ) :
          (∑ a ∈ P.modulus.divisors, f a) * (n : ℝ) /
              ((d : ℝ) * L n) =
            ∑ a ∈ P.modulus.divisors,
              f a * (n : ℝ) / ((d : ℝ) * L n) := by
        rw [Finset.sum_mul, Finset.sum_div]
      rw [add_mul, add_div, hdist, hdist, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a ha
      have hfactor : (0 : ℝ) < (P.factor : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero P.factor_ne_zero
      have haR : (0 : ℝ) < (a : ℝ) := by
        exact_mod_cast Nat.pos_of_mem_divisors ha
      norm_num only [Nat.cast_mul]
      field_simp [hfactor.ne', haR.ne', hdR.ne', hL.ne']

/-- Fixed total variation of the finite head Möbius ledger. -/
def headMoebiusMass (P : Pattern) : ℝ :=
  ∑ a ∈ P.modulus.divisors, |(ArithmeticFunction.moebius a : ℝ)|

theorem headMoebiusMass_nonneg (P : Pattern) : 0 ≤ headMoebiusMass P := by
  unfold headMoebiusMass
  positivity

/-- The termwise error returned by the unconditional structured-cell
theorem is uniformly `O(n/(d log n))` on the complete four-mark range. -/
theorem raw_head_error_sum_le
    (P : Pattern) {A B K : ℝ} {n d : ℕ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hn : 1 < n) (hd : 0 < d)
    (hlogLower : (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ)) :
    (∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (K *
            ((((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) +
              (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ)) /
            Real.log (yNat n : ℝ))) ≤
      (5 * K * (B + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * L n) := by
  have hL : 0 < L n := L_pos hn
  have hs : 0 < Real.log (yNat n : ℝ) :=
    (by positivity : 0 < (1 / 5 : ℝ) * L n).trans_le hlogLower
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hinvLog : 1 / Real.log (yNat n : ℝ) ≤ 5 / L n := by
    apply (div_le_div_iff₀ hs hL).2
    simpa only [one_mul] using (show L n ≤
      5 * Real.log (yNat n : ℝ) by linarith)
  have hterm (C : ℝ) (hC : 0 ≤ C) (a : ℕ)
      (ha : a ∈ P.modulus.divisors) :
      ((((physicalBound C n) / (P.factor * a * d) : ℕ) : ℝ)) ≤
        C * (n : ℝ) / (d : ℝ) := by
    have hfactor : 0 < P.factor := Nat.pos_of_ne_zero P.factor_ne_zero
    have haPos : 0 < a := Nat.pos_of_mem_divisors ha
    have hq : 0 < P.factor * a * d := by positivity
    have hcastDiv :
        ((((physicalBound C n) / (P.factor * a * d) : ℕ) : ℝ)) ≤
          (physicalBound C n : ℝ) /
            ((P.factor * a * d : ℕ) : ℝ) := Nat.cast_div_le
    have hfloor : (physicalBound C n : ℝ) ≤ C * (n : ℝ) :=
      Nat.floor_le (mul_nonneg hC (Nat.cast_nonneg n))
    have hden : (d : ℝ) ≤ ((P.factor * a * d : ℕ) : ℝ) := by
      norm_num only [Nat.cast_mul]
      have : (1 : ℝ) ≤ (P.factor : ℝ) * (a : ℝ) := by
        exact_mod_cast mul_pos hfactor haPos
      nlinarith [hdR]
    calc
      _ ≤ (physicalBound C n : ℝ) /
          ((P.factor * a * d : ℕ) : ℝ) := hcastDiv
      _ ≤ (C * (n : ℝ)) / ((P.factor * a * d : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right hfloor (by positivity)
      _ ≤ C * (n : ℝ) / (d : ℝ) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg hC (Nat.cast_nonneg n)) hdR hden
  calc
    _ ≤ ∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (K * (((B + A) * (n : ℝ) / (d : ℝ)) /
            Real.log (yNat n : ℝ))) := by
      apply Finset.sum_le_sum
      intro a ha
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      calc
        K * ((((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) +
              (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ)) /
            Real.log (yNat n : ℝ) ≤
          (K * ((B + A) * (n : ℝ) / (d : ℝ))) /
            Real.log (yNat n : ℝ) := by
          apply div_le_div_of_nonneg_right _ hs.le
          exact mul_le_mul_of_nonneg_left
            (by
              calc
                (((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) +
                    (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ) ≤
                  B * (n : ℝ) / (d : ℝ) + A * (n : ℝ) / (d : ℝ) :=
                    add_le_add (hterm B hB a ha) (hterm A hA a ha)
                _ = (B + A) * (n : ℝ) / (d : ℝ) := by ring)
            hK
        _ = K * (((B + A) * (n : ℝ) / (d : ℝ)) /
            Real.log (yNat n : ℝ)) := by ring
    _ = headMoebiusMass P *
        (K * (((B + A) * (n : ℝ) / (d : ℝ)) /
          Real.log (yNat n : ℝ))) := by
      unfold headMoebiusMass
      rw [Finset.sum_mul]
    _ = (headMoebiusMass P * K * (B + A) * (n : ℝ) / (d : ℝ)) *
        (1 / Real.log (yNat n : ℝ)) := by ring
    _ ≤ (headMoebiusMass P * K * (B + A) * (n : ℝ) / (d : ℝ)) *
        (5 / L n) := by
      apply mul_le_mul_of_nonneg_left hinvLog
      exact div_nonneg
        (mul_nonneg
          (mul_nonneg
            (mul_nonneg (headMoebiusMass_nonneg P) hK) (add_nonneg hB hA))
          (Nat.cast_nonneg n))
        hdR.le
    _ = (5 * K * (B + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * L n) := by ring

/-! ## Normalization algebra -/

/-- A quantitative ratio lemma which keeps the denominator lower bound
explicit.  It is used below with `y` equal to the actual unmarked cell
cardinality and `q` equal to its positive paper main term. -/
private theorem abs_normalized_ratio_sub_le
    {x y q t E F : ℝ} (hq : 0 < q) (hyhalf : q / 2 ≤ y)
    (hx : |x - q * t| ≤ E) (hy : |y - q| ≤ F) (ht : 0 ≤ t) :
    |x / y - t| ≤ 2 * (E + t * F) / q := by
  have hypos : 0 < y := (half_pos hq).trans_le hyhalf
  have hE : 0 ≤ E := (abs_nonneg (x - q * t)).trans hx
  have hF : 0 ≤ F := (abs_nonneg (y - q)).trans hy
  have hnum : 0 ≤ E + t * F := add_nonneg hE (mul_nonneg ht hF)
  have hinv : 1 / y ≤ 2 / q := by
    apply (div_le_div_iff₀ hypos hq).2
    linarith
  have hid : x / y - t = (x - q * t + t * (q - y)) / y := by
    field_simp [hypos.ne']
    ring
  rw [hid, abs_div, abs_of_pos hypos]
  calc
    |x - q * t + t * (q - y)| / y ≤
        (|x - q * t| + |t * (q - y)|) / y := by
      exact div_le_div_of_nonneg_right (abs_add_le _ _) hypos.le
    _ = (|x - q * t| + t * |y - q|) / y := by
      rw [abs_mul, abs_of_nonneg ht, abs_sub_comm q y]
    _ ≤ (E + t * F) / y := by
      apply div_le_div_of_nonneg_right _ hypos.le
      exact add_le_add hx (mul_le_mul_of_nonneg_left hy ht)
    _ = (E + t * F) * (1 / y) := by ring
    _ ≤ (E + t * F) * (2 / q) :=
      mul_le_mul_of_nonneg_left hinv hnum
    _ = 2 * (E + t * F) / q := by ring

/-- The actual uniform divisor probability is exactly the marked/unmarked
cardinality ratio. -/
theorem uniformAverage_divInd_eq_markedCell_ratio
    (P : Pattern) (lo hi y d : ℕ) :
    uniformAverage (structuredCell P lo hi y) (divInd d) =
      ((markedCell P lo hi y d).card : ℝ) /
        ((structuredCell P lo hi y).card : ℝ) := by
  unfold uniformAverage markedCell
  rw [sum_divInd_eq_card_filter]

/-- Paper-level four-mark count with a single common Dickman translate.
All endpoint, floor, logarithmic-range, and head Möbius errors have been
absorbed into one constant depending only on the fixed cell data. -/
theorem exists_uniform_markedCell_paper_main_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n d : ℕ},
      N₀ ≤ n → 0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) -
          paperMarkedMain P A B n d| ≤
        K * (n : ℝ) / ((d : ℝ) * L n) := by
  obtain ⟨Kraw, hKraw, Y₀, hraw⟩ :=
    exists_uniform_markedCell_dickman_sum_bound
  obtain ⟨NmarginA, hmarginA₀⟩ := exists_endpoint_margin_threshold P hA
  obtain ⟨NmarginB, hmarginB₀⟩ :=
    exists_endpoint_margin_threshold P (hA.trans hAB)
  obtain ⟨NlogA, hlogA₀⟩ := exists_physicalBound_log_range hA
  obtain ⟨NlogB, hlogB₀⟩ :=
    exists_physicalBound_log_range (hA.trans hAB)
  let H : ℕ := max Y₀ (max P.modulus 2)
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hyEvent : ∀ᶠ n : ℕ in Filter.atTop, (H : ℝ) ≤ y n :=
    hyTop.eventually (Filter.eventually_ge_atTop (H : ℝ))
  have hlogEvent := FriableAsymptotic.eventually_one_fifth_L_le_log_yNat
  have hscaleAll : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (H : ℝ) ≤ y n ∧
        (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hyEvent, hlogEvent] with
      n hn hy hlog
    exact ⟨hn, hy, hlog⟩
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscaleAll
  let N₀ := max NmarginA (max NmarginB (max NlogA (max NlogB Nscale)))
  let K : ℝ := 1 + 5 * Kraw * (B + A) * headMoebiusMass P +
    endpointFamilyCoefficient P B + endpointFamilyCoefficient P A
  have hB : 0 < B := hA.trans hAB
  have hrawCoeff0 :
      0 ≤ 5 * Kraw * (B + A) * headMoebiusMass P := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) hKraw.le) (add_nonneg hB.le hA.le))
      (headMoebiusMass_nonneg P)
  have hK : 0 < K := by
    dsimp only [K]
    have hEndB0 := endpointFamilyCoefficient_nonneg P hB.le
    have hEndA0 := endpointFamilyCoefficient_nonneg P hA.le
    linarith
  refine ⟨K, hK, N₀, ?_⟩
  intro n d hNn hd hd4 hdsmooth hcop
  have hNmA : NmarginA ≤ n := by
    dsimp only [N₀] at hNn
    omega
  have hNmB : NmarginB ≤ n := by
    dsimp only [N₀] at hNn
    omega
  have hNlA : NlogA ≤ n := by
    dsimp only [N₀] at hNn
    omega
  have hNlB : NlogB ≤ n := by
    dsimp only [N₀] at hNn
    omega
  have hNs : Nscale ≤ n := by
    dsimp only [N₀] at hNn
    omega
  obtain ⟨hn, hyH, hlogLower⟩ := hNscale n hNs
  have hnpos : 0 < n := by omega
  have hL : 0 < L n := L_pos hn
  have hHy : H ≤ yNat n := Nat.le_floor hyH
  have hY₀ : Y₀ ≤ yNat n :=
    (le_max_left Y₀ (max P.modulus 2)).trans hHy
  have hmodY : P.modulus ≤ yNat n :=
    (le_max_left P.modulus 2).trans
      ((le_max_right Y₀ (max P.modulus 2)).trans hHy)
  have hyNat2 : 2 ≤ yNat n :=
    (le_max_right P.modulus 2).trans
      ((le_max_right Y₀ (max P.modulus 2)).trans hHy)
  have hy2 : (2 : ℝ) ≤ y n := by
    exact (by exact_mod_cast hyNat2 : (2 : ℝ) ≤ (yNat n : ℝ)).trans
      (Nat.floor_le (Scale.y_pos hnpos).le)
  have hhead : ∀ p ∈ P.primes, p ≤ yNat n := by
    intro p hp
    have hpDvd : p ∣ P.modulus := by
      unfold Pattern.modulus
      exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero P.modulus_ne_zero) hpDvd).trans hmodY
  have hlohi : physicalBound A n ≤ physicalBound B n := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_right hAB.le (Nat.cast_nonneg n)
  have hmarginA : ∀ a ∈ P.modulus.divisors,
      4 ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      L n ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) := by
    intro a ha
    exact hmarginA₀ hNmA ha hd hd4
  have hmarginB : ∀ a ∈ P.modulus.divisors,
      4 ≤ B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      L n ≤ B * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) := by
    intro a ha
    exact hmarginB₀ hNmB ha hd hd4
  have hlogA : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ) := by
    intro a ha
    exact hlogA₀ hNlA (mul_pos
      (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
        (Nat.pos_of_mem_divisors ha)) hd)
  have hlogB : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound B n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ) := by
    intro a ha
    exact hlogB₀ hNlB (mul_pos
      (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
        (Nat.pos_of_mem_divisors ha)) hd)
  have hraw₀ := hraw P hY₀ hlohi hhead hd hdsmooth hcop hlogA hlogB
  have hraw₁ :
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) -
        ∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a| ≤
      (5 * Kraw * (B + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * L n) :=
    hraw₀.trans (raw_head_error_sum_le P hA.le hB.le hKraw.le hn hd hlogLower)
  have hcommon := headDivisorMain_sum_sub_common_le P hA hB hn hd hd4
    hy2 hlogLower hmarginA hmarginB hlogA hlogB
  have hcollapse := common_endpoint_sum_eq_paperMarkedMain P A B
    (rho (paperDivisorCoordinate n d)) (n := n) (d := d) hd
  have hcommon' :
      |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a) - paperMarkedMain P A B n d| ≤
        (endpointFamilyCoefficient P B + endpointFamilyCoefficient P A) *
          (n : ℝ) / ((d : ℝ) * L n) := by
    unfold paperMarkedMain
    rw [← hcollapse]
    exact hcommon
  have hscale : 0 ≤ (n : ℝ) / ((d : ℝ) * L n) := by positivity
  calc
    |((markedCell P (physicalBound A n) (physicalBound B n)
          (yNat n) d).card : ℝ) - paperMarkedMain P A B n d| ≤
      |((markedCell P (physicalBound A n) (physicalBound B n)
          (yNat n) d).card : ℝ) -
        ∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a| +
      |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound B n)
            (yNat n) d a) - paperMarkedMain P A B n d| :=
        abs_sub_le _ _ _
    _ ≤ (5 * Kraw * (B + A) * headMoebiusMass P) *
          (n : ℝ) / ((d : ℝ) * L n) +
        (endpointFamilyCoefficient P B + endpointFamilyCoefficient P A) *
          (n : ℝ) / ((d : ℝ) * L n) := add_le_add hraw₁ hcommon'
    _ = (5 * Kraw * (B + A) * headMoebiusMass P +
          endpointFamilyCoefficient P B + endpointFamilyCoefficient P A) *
        ((n : ℝ) / ((d : ℝ) * L n)) := by ring
    _ ≤ K * ((n : ℝ) / ((d : ℝ) * L n)) := by
      apply mul_le_mul_of_nonneg_right _ hscale
      dsimp only [K]
      linarith
    _ = K * (n : ℝ) / ((d : ℝ) * L n) := by ring

/-- The unmarked structured cell has a fixed positive linear density.  This
is the normalization lower bound used by all subsequent compact tilts. -/
theorem exists_structuredCell_density_lower_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      paperCellDensity P A B * (n : ℝ) / 2 ≤
        ((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) := by
  obtain ⟨K, hK, Ncount, hcount⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAB
  let c : ℝ := paperCellDensity P A B
  have hc : 0 < c := paperCellDensity_pos P hAB
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hyTop : Filter.Tendsto (fun n : ℕ => y n)
      Filter.atTop Filter.atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hlarge : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (2 : ℝ) ≤ y n ∧ 2 * K / c ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hyTop.eventually (Filter.eventually_ge_atTop (2 : ℝ)),
      hLTop.eventually (Filter.eventually_ge_atTop (2 * K / c))] with
      n hn hy hden
    exact ⟨hn, hy, hden⟩
  obtain ⟨Nlarge, hNlarge⟩ := Filter.eventually_atTop.mp hlarge
  refine ⟨max Ncount Nlarge, ?_⟩
  intro n hN
  have hNc : Ncount ≤ n := by omega
  have hNl : Nlarge ≤ n := by omega
  obtain ⟨hn, hy, hden⟩ := hNlarge n hNl
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hL : 0 < L n := L_pos hn
  have hyNat2 : 2 ≤ yNat n := Nat.le_floor hy
  have h1d4 : 1 ≤ yNat n ^ 4 := by
    exact pow_pos (by omega : 0 < yNat n) 4
  have hbase₀ := hcount (n := n) (d := 1) hNc (by omega) h1d4
    (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hbase :
      |((structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).card : ℝ) - c * (n : ℝ)| ≤
        K * (n : ℝ) / L n := by
    simpa [c, markedCell] using hbase₀
  have hscale : 2 * K ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hden
    simpa [mul_comm] using this
  have hKdiv : K / L n ≤ c / 2 := by
    apply (div_le_iff₀ hL).2
    nlinarith [hscale]
  have herr : K * (n : ℝ) / L n ≤ c * (n : ℝ) / 2 := by
    calc
      K * (n : ℝ) / L n = (K / L n) * (n : ℝ) := by ring
      _ ≤ (c / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hKdiv hnR.le
      _ = c * (n : ℝ) / 2 := by ring
  have hlower := (abs_le.mp (hbase.trans herr)).1
  dsimp only [c] at hlower ⊢
  linarith

/-- Paper-level normalized four-mark probability.  For every fixed physical
interval and head pattern, the actual uniform law on the finite structured
cell is eventually nonempty and its divisor probability has the common
Dickman translate, uniformly for all admissible `d ≤ yNat n ^ 4`. -/
theorem exists_uniform_uniformAverage_divInd_paper_bound
    (P : Pattern) {A B : ℝ} (hA : 0 < A) (hAB : A < B) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n d : ℕ},
      N₀ ≤ n → 0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      (structuredCell P (physicalBound A n) (physicalBound B n)
          (yNat n)).Nonempty ∧
      |uniformAverage
          (structuredCell P (physicalBound A n) (physicalBound B n)
            (yNat n))
          (divInd d) - paperDivisibilityMain n d| ≤
        K / ((d : ℝ) * L n) := by
  obtain ⟨K₀, hK₀, Ncount, hcount⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAB
  let c : ℝ := paperCellDensity P A B
  have hc : 0 < c := paperCellDensity_pos P hAB
  have hrU : 0 < rho DickmanBasic.U := rho_U_pos
  let K : ℝ := 2 * K₀ * (1 + 1 / rho DickmanBasic.U) / c
  have hK : 0 < K := by
    dsimp only [K]
    exact div_pos
      (mul_pos (mul_pos (by norm_num) hK₀)
        (add_pos_of_pos_of_nonneg zero_lt_one (one_div_nonneg.mpr hrU.le))) hc
  have hLTop : Filter.Tendsto L Filter.atTop Filter.atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdenEvent : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ 2 * K₀ / c ≤ L n := by
    filter_upwards [Filter.eventually_gt_atTop 1,
      hLTop.eventually
        (Filter.eventually_ge_atTop (2 * K₀ / c))] with n hn hden
    exact ⟨hn, hden⟩
  obtain ⟨Nden, hNden⟩ := Filter.eventually_atTop.mp hdenEvent
  let N₀ := max Ncount Nden
  refine ⟨K, hK, N₀, ?_⟩
  intro n d hN hd hd4 hdsmooth hcop
  have hNcount : Ncount ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNden' : Nden ≤ n := by
    dsimp only [N₀] at hN
    omega
  obtain ⟨hn, hden⟩ := hNden n hNden'
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnpos
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hL : 0 < L n := L_pos hn
  have hq : 0 < c * (n : ℝ) := mul_pos hc hnR
  have hscale : 2 * K₀ ≤ c * L n := by
    have := (div_le_iff₀ hc).1 hden
    simpa [mul_comm] using this
  let S : Finset ℕ :=
    structuredCell P (physicalBound A n) (physicalBound B n) (yNat n)
  have h1d4 : 1 ≤ yNat n ^ 4 := (show 1 ≤ d by omega).trans hd4
  have hbase₀ := hcount (n := n) (d := 1) hNcount (by omega)
    h1d4 (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hbase :
      |(S.card : ℝ) - c * (n : ℝ)| ≤ K₀ * (n : ℝ) / L n := by
    simpa [S, c, markedCell] using hbase₀
  have hKdiv : K₀ / L n ≤ c / 2 := by
    apply (div_le_iff₀ hL).2
    nlinarith [hscale]
  have hhalfError : K₀ * (n : ℝ) / L n ≤ c * (n : ℝ) / 2 := by
    calc
      K₀ * (n : ℝ) / L n = (K₀ / L n) * (n : ℝ) := by ring
      _ ≤ (c / 2) * (n : ℝ) :=
        mul_le_mul_of_nonneg_right hKdiv hnR.le
      _ = c * (n : ℝ) / 2 := by ring
  have hbaseHalf :
      |(S.card : ℝ) - c * (n : ℝ)| ≤ c * (n : ℝ) / 2 :=
    hbase.trans hhalfError
  have hScardHalf : c * (n : ℝ) / 2 ≤ (S.card : ℝ) := by
    have hlower := (abs_le.mp hbaseHalf).1
    linarith
  have hScardR : 0 < (S.card : ℝ) :=
    (half_pos hq).trans_le hScardHalf
  have hScard : 0 < S.card := by exact_mod_cast hScardR
  have hSnonempty : S.Nonempty := Finset.card_pos.mp hScard
  have hmarked₀ := hcount (n := n) (d := d) hNcount hd hd4
    hdsmooth hcop
  have hmarked :
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) -
          (c * (n : ℝ)) * paperDivisibilityMain n d| ≤
        K₀ * (n : ℝ) / ((d : ℝ) * L n) := by
    rw [paperMarkedMain_eq_density_mul_divisibility P A B hd] at hmarked₀
    simpa [c, mul_assoc] using hmarked₀
  have ht := paperDivisibilityMain_nonneg_le hn hd hd4
  have hratio := abs_normalized_ratio_sub_le hq hScardHalf hmarked hbase ht.1
  have hFnonneg : 0 ≤ K₀ * (n : ℝ) / L n := by positivity
  have htF :
      paperDivisibilityMain n d * (K₀ * (n : ℝ) / L n) ≤
        (1 / (rho DickmanBasic.U * (d : ℝ))) *
          (K₀ * (n : ℝ) / L n) :=
    mul_le_mul_of_nonneg_right ht.2 hFnonneg
  have hEF :
      K₀ * (n : ℝ) / ((d : ℝ) * L n) +
          paperDivisibilityMain n d * (K₀ * (n : ℝ) / L n) ≤
        (K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n) := by
    calc
      K₀ * (n : ℝ) / ((d : ℝ) * L n) +
          paperDivisibilityMain n d * (K₀ * (n : ℝ) / L n) ≤
        K₀ * (n : ℝ) / ((d : ℝ) * L n) +
          (1 / (rho DickmanBasic.U * (d : ℝ))) *
            (K₀ * (n : ℝ) / L n) := by linarith [htF]
      _ = (K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n) := by ring
  have hratio' :
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) / (S.card : ℝ) -
          paperDivisibilityMain n d| ≤
        2 * ((K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n)) / (c * (n : ℝ)) := by
    exact hratio.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hEF (by norm_num)) hq.le)
  have hfinal :
      |((markedCell P (physicalBound A n) (physicalBound B n)
            (yNat n) d).card : ℝ) / (S.card : ℝ) -
          paperDivisibilityMain n d| ≤ K / ((d : ℝ) * L n) := by
    calc
      _ ≤ 2 * ((K₀ * (1 + 1 / rho DickmanBasic.U)) * (n : ℝ) /
          ((d : ℝ) * L n)) / (c * (n : ℝ)) := hratio'
      _ = K / ((d : ℝ) * L n) := by
        dsimp only [K]
        field_simp [hc.ne', hrU.ne', hnR.ne', hdR.ne', hL.ne']
  refine ⟨?_, ?_⟩
  · simpa only [S] using hSnonempty
  · rw [uniformAverage_divInd_eq_markedCell_ratio]
    simpa only [S] using hfinal

end

end Erdos390.Full.PaperScaleMarkedCell
