import Erdos390.Full.MarkedFriableAsymptotic

/-!
# Unconditional Dickman estimate for the actual structured cells

This file composes the exact head-pattern inclusion--exclusion identity with
the proved uniform friable-number estimate.  In particular, the theorem below
does not assume a marked-cell asymptotic: its only analytic hypotheses are the
explicit logarithmic-range inequalities at the finitely many endpoints.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.StructuredCellAsymptotic

open ArithmeticModel DickmanBasic Scale
open StructuredCells HeadPattern MarkedFriableAsymptotic

/-- The Dickman main term at one integral endpoint. -/
noncomputable def endpointMain (X y : ℕ) : ℝ :=
  (X : ℝ) * rho (FriableAsymptotic.dickmanU X y)

/-- The signed main term contributed by one head inclusion--exclusion
divisor. -/
noncomputable def headDivisorMain (P : Pattern) (lo hi y d a : ℕ) : ℝ :=
  (ArithmeticFunction.moebius a : ℝ) *
    (endpointMain (hi / (P.factor * a * d)) y -
      endpointMain (lo / (P.factor * a * d)) y)

/-- Real-cast form of the exact finite inclusion--exclusion identity, after
reindexing every smooth multiple by division. -/
theorem markedCell_card_real_eq_smoothInterval_sum
    (P : Pattern) {lo hi y d : ℕ}
    (hhead : ∀ p ∈ P.primes, p ≤ y)
    (hdpos : 0 < d) (hdsmooth : d ∈ Nat.smoothNumbers (y + 1))
    (hcop : Nat.Coprime d P.modulus) :
    ((markedCell P lo hi y d).card : ℝ) =
      ∑ a ∈ P.modulus.divisors,
        (ArithmeticFunction.moebius a : ℝ) *
          ((smoothInterval (lo / (P.factor * a * d))
            (hi / (P.factor * a * d)) y).card : ℝ) := by
  have hZ := markedCell_card_inclusion_exclusion P
    (lo := lo) (hi := hi) (y := y) (d := d) hcop
  have h := congrArg (fun z : ℤ ↦ (z : ℝ)) hZ
  simp only [Int.cast_natCast, Int.cast_sum, Int.cast_mul] at h
  calc
    ((markedCell P lo hi y d).card : ℝ) =
        ∑ a ∈ P.modulus.divisors,
          (ArithmeticFunction.moebius a : ℝ) *
            (((smoothInterval lo hi y).filter
              (P.factor * a * d ∣ ·)).card : ℝ) := h
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a haDiv
      have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
      have hapos : 0 < a :=
        Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero P.modulus_ne_zero)
      have hDpos : 0 < P.factor * a * d :=
        mul_pos (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero) hapos) hdpos
      have haSmooth : a ∈ Nat.smoothNumbers (y + 1) :=
        Nat.mem_smoothNumbers_of_dvd (modulus_mem_smoothNumbers P hhead) ha
      have hDSmooth : P.factor * a * d ∈ Nat.smoothNumbers (y + 1) :=
        Nat.mul_mem_smoothNumbers
          (Nat.mul_mem_smoothNumbers
            (factor_mem_smoothNumbers P hhead) haSmooth)
          hdsmooth
      rw [smooth_multiple_card_eq_quotient_interval hDpos hDSmooth]

/-- The actual marked structured-cell count is uniformly approximated by
the finite sum of Dickman endpoint main terms.  The error ledger is written
term by term, so no unproved dependence on the fixed head pattern is hidden.
-/
theorem exists_uniform_markedCell_dickman_sum_bound :
    ∃ K : ℝ, 0 < K ∧ ∃ Y₀ : ℕ, ∀ (P : Pattern) {lo hi y d : ℕ},
      Y₀ ≤ y → lo ≤ hi →
      (∀ p ∈ P.primes, p ≤ y) →
      0 < d → d ∈ Nat.smoothNumbers (y + 1) →
      Nat.Coprime d P.modulus →
      (∀ a ∈ P.modulus.divisors,
        Real.log ((lo / (P.factor * a * d) : ℕ) : ℝ) ≤
          5 * Real.log (y : ℝ)) →
      (∀ a ∈ P.modulus.divisors,
        Real.log ((hi / (P.factor * a * d) : ℕ) : ℝ) ≤
          5 * Real.log (y : ℝ)) →
      |((markedCell P lo hi y d).card : ℝ) -
          ∑ a ∈ P.modulus.divisors, headDivisorMain P lo hi y d a| ≤
        ∑ a ∈ P.modulus.divisors,
          |(ArithmeticFunction.moebius a : ℝ)| *
            (K *
              (((hi / (P.factor * a * d) : ℕ) : ℝ) +
                ((lo / (P.factor * a * d) : ℕ) : ℝ)) /
              Real.log (y : ℝ)) := by
  obtain ⟨K, hK, Y₀, hinterval⟩ :=
    exists_uniform_smoothInterval_dickman_bound
  refine ⟨K, hK, Y₀, ?_⟩
  intro P lo hi y d hy hlohi hhead hdpos hdsmooth hcop hloglo hloghi
  rw [markedCell_card_real_eq_smoothInterval_sum P hhead hdpos
    hdsmooth hcop]
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ a ∈ P.modulus.divisors,
          ((ArithmeticFunction.moebius a : ℝ) *
              ((smoothInterval (lo / (P.factor * a * d))
                (hi / (P.factor * a * d)) y).card : ℝ) -
            headDivisorMain P lo hi y d a)| ≤
        ∑ a ∈ P.modulus.divisors,
        |((ArithmeticFunction.moebius a : ℝ) *
              ((smoothInterval (lo / (P.factor * a * d))
                (hi / (P.factor * a * d)) y).card : ℝ) -
            headDivisorMain P lo hi y d a)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a ∈ P.modulus.divisors,
        |(ArithmeticFunction.moebius a : ℝ)| *
          (K *
            (((hi / (P.factor * a * d) : ℕ) : ℝ) +
              ((lo / (P.factor * a * d) : ℕ) : ℝ)) /
            Real.log (y : ℝ)) := by
      apply Finset.sum_le_sum
      intro a ha
      let Xhi := hi / (P.factor * a * d)
      let Xlo := lo / (P.factor * a * d)
      have hXlohi : Xlo ≤ Xhi := Nat.div_le_div_right hlohi
      have hinter := hinterval hy hXlohi (hloglo a ha) (hloghi a ha)
      have herr :
          |((smoothInterval Xlo Xhi y).card : ℝ) -
              (endpointMain Xhi y - endpointMain Xlo y)| ≤
            K * ((Xhi : ℝ) + (Xlo : ℝ)) / Real.log (y : ℝ) := by
        simpa only [endpointMain] using hinter
      rw [show
        (ArithmeticFunction.moebius a : ℝ) *
              ((smoothInterval Xlo Xhi y).card : ℝ) -
            headDivisorMain P lo hi y d a =
          (ArithmeticFunction.moebius a : ℝ) *
            (((smoothInterval Xlo Xhi y).card : ℝ) -
              (endpointMain Xhi y - endpointMain Xlo y)) by
        simp only [headDivisorMain, Xhi, Xlo]
        ring]
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [Xhi, Xlo] using herr) (abs_nonneg _)

end Erdos390.Full.StructuredCellAsymptotic
