import Erdos390.Full.HeadPattern
import Mathlib.NumberTheory.SmoothNumbers

/-!
# Exact structured-cell reductions

This file defines the actual finite smooth intervals and exact head cells.
It proves the finite inclusion--exclusion identity before any use of a
friable-number asymptotic.
-/

open scoped BigOperators ArithmeticFunction.Moebius

namespace Erdos390.Full.StructuredCells

open HeadPattern

/-- Positive `y`-smooth integers in `(lo, hi]`.  Mathlib's
`smoothNumbers (y+1)` means that all prime factors are at most `y`. -/
def smoothInterval (lo hi y : ℕ) : Finset ℕ :=
  (Nat.smoothNumbersUpTo hi (y + 1)).filter (lo < ·)

/-- The exact finite friable counting function used in this development;
`psi X y` counts positive integers at most `X` whose prime factors are at
most `y`. -/
def psi (X y : ℕ) : ℕ :=
  (Nat.smoothNumbersUpTo X (y + 1)).card

/-- A finite structured cell with exact head valuations. -/
def structuredCell (P : Pattern) (lo hi y : ℕ) : Finset ℕ :=
  (smoothInterval lo hi y).filter P.Matches

/-- The part of a structured cell divisible by a marked integer `d`. -/
def markedCell (P : Pattern) (lo hi y d : ℕ) : Finset ℕ :=
  (structuredCell P lo hi y).filter (d ∣ ·)

@[simp] theorem mem_smoothInterval {lo hi y m : ℕ} :
    m ∈ smoothInterval lo hi y ↔
      lo < m ∧ m ≤ hi ∧ m ∈ Nat.smoothNumbers (y + 1) := by
  simp only [smoothInterval, Finset.mem_filter, Nat.mem_smoothNumbersUpTo]
  tauto

theorem pos_of_mem_smoothInterval {lo hi y m : ℕ}
    (hm : m ∈ smoothInterval lo hi y) : 0 < m := by
  exact (Nat.mem_smoothNumbers.mp (mem_smoothInterval.mp hm).2.2).1.bot_lt

theorem smoothNumbersUpTo_mono {X₁ X₂ y : ℕ} (hX : X₁ ≤ X₂) :
    Nat.smoothNumbersUpTo X₁ (y + 1) ⊆
      Nat.smoothNumbersUpTo X₂ (y + 1) := by
  intro m hm
  rw [Nat.mem_smoothNumbersUpTo] at hm ⊢
  exact ⟨hm.1.trans hX, hm.2⟩

/-- An exact interval count is a difference of two `psi` values. -/
theorem smoothInterval_card_eq_psi_sub {lo hi y : ℕ} (hlohi : lo ≤ hi) :
    (smoothInterval lo hi y).card = psi hi y - psi lo y := by
  have hset : smoothInterval lo hi y =
      Nat.smoothNumbersUpTo hi (y + 1) \
        Nat.smoothNumbersUpTo lo (y + 1) := by
    ext m
    simp only [mem_smoothInterval, Finset.mem_sdiff,
      Nat.mem_smoothNumbersUpTo]
    constructor
    · rintro ⟨hlom, hmhi, hsmooth⟩
      exact ⟨⟨hmhi, hsmooth⟩, fun hlow ↦ (Nat.not_le_of_lt hlom) hlow.1⟩
    · rintro ⟨⟨hmhi, hsmooth⟩, hnotlow⟩
      refine ⟨?_, hmhi, hsmooth⟩
      by_contra hnlt
      exact hnotlow ⟨Nat.le_of_not_gt hnlt, hsmooth⟩
  rw [hset, Finset.card_sdiff]
  have hinter :
      Nat.smoothNumbersUpTo lo (y + 1) ∩
          Nat.smoothNumbersUpTo hi (y + 1) =
        Nat.smoothNumbersUpTo lo (y + 1) := by
    exact Finset.inter_eq_left.mpr (smoothNumbersUpTo_mono hlohi)
  rw [hinter]
  rfl

@[simp] theorem mem_structuredCell {P : Pattern} {lo hi y m : ℕ} :
    m ∈ structuredCell P lo hi y ↔
      m ∈ smoothInterval lo hi y ∧ P.Matches m := by
  simp [structuredCell]

@[simp] theorem mem_markedCell {P : Pattern} {lo hi y d m : ℕ} :
    m ∈ markedCell P lo hi y d ↔
      m ∈ smoothInterval lo hi y ∧ P.Matches m ∧ d ∣ m := by
  simp [markedCell, structuredCell, and_assoc, and_left_comm]

theorem coprime_factor_of_coprime_modulus (P : Pattern) {d : ℕ}
    (hcop : Nat.Coprime d P.modulus) : Nat.Coprime d P.factor := by
  rw [Pattern.factor, Nat.coprime_prod_right_iff]
  intro p hp
  apply Nat.Coprime.pow_right
  rw [Pattern.modulus, Nat.coprime_prod_right_iff] at hcop
  exact hcop p hp

theorem pow_mem_smoothNumbers {z p : ℕ}
    (hp : p ∈ Nat.smoothNumbers z) (e : ℕ) :
    p ^ e ∈ Nat.smoothNumbers z := by
  induction e with
  | zero => simp [Nat.mem_smoothNumbers]
  | succ e ih =>
      rw [pow_succ]
      exact Nat.mul_mem_smoothNumbers ih hp

theorem factor_mem_smoothNumbers (P : Pattern) {y : ℕ}
    (hhead : ∀ p ∈ P.primes, p ≤ y) :
    P.factor ∈ Nat.smoothNumbers (y + 1) := by
  rw [Pattern.factor]
  apply Finset.prod_induction (s := P.primes)
    (fun p ↦ p ^ P.exponent p)
    (fun z ↦ z ∈ Nat.smoothNumbers (y + 1))
    (fun _ _ ha hb ↦ Nat.mul_mem_smoothNumbers ha hb)
    (by simp [Nat.mem_smoothNumbers])
  intro p hp
  apply pow_mem_smoothNumbers
  exact Nat.mem_smoothNumbers_of_lt (P.prime_mem p hp).pos
    (Nat.lt_succ_of_le (hhead p hp))

theorem modulus_mem_smoothNumbers (P : Pattern) {y : ℕ}
    (hhead : ∀ p ∈ P.primes, p ≤ y) :
    P.modulus ∈ Nat.smoothNumbers (y + 1) := by
  rw [Pattern.modulus]
  apply Finset.prod_induction (s := P.primes)
    (fun p ↦ p)
    (fun z ↦ z ∈ Nat.smoothNumbers (y + 1))
    (fun _ _ ha hb ↦ Nat.mul_mem_smoothNumbers ha hb)
    (by simp [Nat.mem_smoothNumbers])
  intro p hp
  exact Nat.mem_smoothNumbers_of_lt (P.prime_mem p hp).pos
    (Nat.lt_succ_of_le (hhead p hp))

/-- Under the paper's coprimality condition `(d,M_H)=1`, the three
divisibility conditions appearing after head inclusion--exclusion combine
into one marked divisor. -/
theorem combined_dvd_iff (P : Pattern) {m d a : ℕ}
    (hcop : Nat.Coprime d P.modulus) (ha : a ∣ P.modulus) :
    (d ∣ m ∧ P.factor ∣ m ∧ a ∣ m / P.factor) ↔
      P.factor * a * d ∣ m := by
  constructor
  · rintro ⟨hd, hfac, haquot⟩
    have hfa : P.factor * a ∣ m :=
      (Nat.dvd_div_iff_mul_dvd hfac).mp haquot
    have hcopa : Nat.Coprime d a := Nat.Coprime.of_dvd_right ha hcop
    have hcopfa : Nat.Coprime d (P.factor * a) :=
      (coprime_factor_of_coprime_modulus P hcop).mul_right hcopa
    have hprod : d * (P.factor * a) ∣ m :=
      hcopfa.mul_dvd_of_dvd_of_dvd hd hfa
    simpa [mul_assoc, mul_comm, mul_left_comm] using hprod
  · intro hprod
    have hfac : P.factor ∣ m :=
      (dvd_mul_right P.factor (a * d)).trans (by
        simpa [mul_assoc] using hprod)
    have hd : d ∣ m := by
      have : d ∣ P.factor * a * d := by simp
      exact this.trans hprod
    refine ⟨hd, hfac, ?_⟩
    apply (Nat.dvd_div_iff_mul_dvd hfac).mpr
    have : P.factor * a ∣ P.factor * a * d := dvd_mul_right _ _
    exact this.trans hprod

/-- Exact reindexing of smooth multiples by division.  This is the finite
identity that turns each inclusion--exclusion term into a difference of two
friable counting functions. -/
theorem smooth_multiple_card_eq_quotient_interval {lo hi y D : ℕ}
    (hDpos : 0 < D) (hDsmooth : D ∈ Nat.smoothNumbers (y + 1)) :
    ((smoothInterval lo hi y).filter (D ∣ ·)).card =
      (smoothInterval (lo / D) (hi / D) y).card := by
  classical
  apply Finset.card_bij (fun m _ ↦ m / D)
  · intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨hminterval, hDvd⟩ := hm
    obtain ⟨hlom, hmhi, hsmooth⟩ := mem_smoothInterval.mp hminterval
    apply mem_smoothInterval.mpr
    refine ⟨(Nat.div_lt_iff_lt_mul hDpos).mpr ?_,
      (Nat.le_div_iff_mul_le hDpos).mpr ?_, ?_⟩
    · simpa [Nat.div_mul_cancel hDvd] using hlom
    · simpa [Nat.div_mul_cancel hDvd] using hmhi
    · exact Nat.mem_smoothNumbers_of_dvd hsmooth (Nat.div_dvd_of_dvd hDvd)
  · intro m₁ hm₁ m₂ hm₂ heq
    rw [Finset.mem_filter] at hm₁ hm₂
    calc
      m₁ = m₁ / D * D := (Nat.div_mul_cancel hm₁.2).symm
      _ = m₂ / D * D := by rw [heq]
      _ = m₂ := Nat.div_mul_cancel hm₂.2
  · intro k hk
    refine ⟨k * D, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨?_, by simp⟩
      obtain ⟨hlok, hkhi, hksmooth⟩ := mem_smoothInterval.mp hk
      apply mem_smoothInterval.mpr
      exact ⟨(Nat.div_lt_iff_lt_mul hDpos).mp hlok,
        (Nat.le_div_iff_mul_le hDpos).mp hkhi,
        Nat.mul_mem_smoothNumbers hksmooth hDsmooth⟩
    · exact Nat.mul_div_left k hDpos

/-- Exact finite count reduction corresponding to the paper's head-pattern
inclusion--exclusion formula.  The right side contains only ordinary smooth
multiple counts; no asymptotic estimate has entered. -/
theorem markedCell_card_inclusion_exclusion (P : Pattern)
    {lo hi y d : ℕ} (hcop : Nat.Coprime d P.modulus) :
    ((markedCell P lo hi y d).card : ℤ) =
      ∑ a ∈ P.modulus.divisors,
        ArithmeticFunction.moebius a *
          (((smoothInterval lo hi y).filter
            (P.factor * a * d ∣ ·)).card : ℤ) := by
  classical
  rw [markedCell]
  simp only [structuredCell, Finset.filter_filter]
  rw [Finset.card_filter]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  calc
    (∑ m ∈ smoothInterval lo hi y,
        if P.Matches m ∧ d ∣ m then (1 : ℤ) else 0) =
      ∑ m ∈ smoothInterval lo hi y,
        if d ∣ m then
          (if P.factor ∣ m then
            ∑ a ∈ P.modulus.divisors,
              if a ∣ m / P.factor then ArithmeticFunction.moebius a else 0
           else 0)
        else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          have hm0 : m ≠ 0 := (pos_of_mem_smoothInterval hm).ne'
          by_cases hd : d ∣ m
          · simpa [hd, and_comm] using
              P.match_indicator_eq_inclusion_exclusion hm0
          · simp [hd]
    _ = ∑ a ∈ P.modulus.divisors,
        ArithmeticFunction.moebius a *
          (((smoothInterval lo hi y).filter
            (P.factor * a * d ∣ ·)).card : ℤ) := by
      have hpoint (m : ℕ) :
          (if d ∣ m then
            (if P.factor ∣ m then
              ∑ a ∈ P.modulus.divisors,
                if a ∣ m / P.factor then ArithmeticFunction.moebius a else 0
             else 0)
           else 0) =
            ∑ a ∈ P.modulus.divisors,
              ArithmeticFunction.moebius a *
                if P.factor * a * d ∣ m then 1 else 0 := by
        by_cases hd : d ∣ m
        · rw [if_pos hd]
          by_cases hfac : P.factor ∣ m
          · rw [if_pos hfac]
            apply Finset.sum_congr rfl
            intro a haDiv
            have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
            have hiff := combined_dvd_iff P (m := m) (d := d) (a := a) hcop ha
            by_cases haq : a ∣ m / P.factor
            · have hprod : P.factor * a * d ∣ m :=
                hiff.mp ⟨hd, hfac, haq⟩
              simp [haq, hprod]
            · have hnprod : ¬ P.factor * a * d ∣ m := by
                intro hprod
                exact haq (hiff.mpr hprod).2.2
              simp [haq, hnprod]
          · rw [if_neg hfac]
            symm
            apply Finset.sum_eq_zero
            intro a haDiv
            have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
            have hnprod : ¬ P.factor * a * d ∣ m := by
              intro hprod
              exact hfac (combined_dvd_iff P hcop ha |>.mpr hprod).2.1
            simp [hnprod]
        · rw [if_neg hd]
          symm
          apply Finset.sum_eq_zero
          intro a haDiv
          have ha : a ∣ P.modulus := (Nat.mem_divisors.mp haDiv).1
          have hnprod : ¬ P.factor * a * d ∣ m := by
            intro hprod
            exact hd (combined_dvd_iff P hcop ha |>.mpr hprod).1
          simp [hnprod]
      simp_rw [hpoint]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a haDiv
      rw [← Finset.mul_sum]
      simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite,
        Nat.cast_one, Nat.cast_zero]

/-- The exact `Psi` identity underlying the marked structured-cell estimate.
This is the natural-endpoint version of equation (6.5) in the paper. -/
theorem markedCell_card_eq_psi_sum (P : Pattern) {lo hi y d : ℕ}
    (hlohi : lo ≤ hi) (hhead : ∀ p ∈ P.primes, p ≤ y)
    (hdpos : 0 < d) (hdsmooth : d ∈ Nat.smoothNumbers (y + 1))
    (hcop : Nat.Coprime d P.modulus) :
    ((markedCell P lo hi y d).card : ℤ) =
      ∑ a ∈ P.modulus.divisors,
        ArithmeticFunction.moebius a *
          ((psi (hi / (P.factor * a * d)) y -
            psi (lo / (P.factor * a * d)) y : ℕ) : ℤ) := by
  rw [markedCell_card_inclusion_exclusion P hcop]
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
      (Nat.mul_mem_smoothNumbers (factor_mem_smoothNumbers P hhead) haSmooth)
      hdsmooth
  rw [smooth_multiple_card_eq_quotient_interval hDpos hDSmooth]
  rw [smoothInterval_card_eq_psi_sub (Nat.div_le_div_right hlohi)]

end Erdos390.Full.StructuredCells
