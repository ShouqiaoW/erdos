import Erdos536.FactorialInsertion
import Erdos536.FiveStateRooted
import Erdos536.LocalPrimeBand
import Erdos536.PrimeBandEvent
import Erdos536.PrimeBandTimeChange

/-!
# Finite collision estimates for the prime-band construction

This file isolates the exact finite ingredients of the rooted collision
argument.  The nine-mark geometry is completely enumerated, including the
`8`, `3`, and `6` factors occurring at the first and second canonical
pivots.  We also prove a general one-point insertion small-ball lemma.  Its
specialization to parameters `q p = 1 / (3*p)` is the missing-petal pivot
used after the root has been exposed.
-/

open scoped BigOperators
open Finset

noncomputable section

namespace Erdos536

/-! ## The exact nine-mark geometry -/

/-- A coordinate of a nine-valued mark, represented by `-1,0,1`. -/
abbrev SignedDigit := Fin 3

/-- The integer represented by a signed digit. -/
def signedDigitValue (a : SignedDigit) : ℤ :=
  (a.1 : ℤ) - 1

/-- The mark space `{-1,0,1}²`. -/
abbrev NineMark := SignedDigit × SignedDigit

/-- The zero mark. -/
def zeroNineMark : NineMark := (1, 1)

/-- The determinant of the two columns represented by two marks. -/
def nineMarkDet (v w : NineMark) : ℤ :=
  signedDigitValue v.1 * signedDigitValue w.2 -
    signedDigitValue v.2 * signedDigitValue w.1

/-- Real collinearity of two marks is equivalent here to vanishing of
their integer determinant. -/
def NineMarkCollinear (v w : NineMark) : Prop :=
  nineMarkDet v w = 0

instance (v w : NineMark) : Decidable (NineMarkCollinear v w) := by
  unfold NineMarkCollinear
  exact Int.instDecidableEq _ _

@[simp]
theorem signedDigitValue_eq_zero_iff (a : SignedDigit) :
    signedDigitValue a = 0 ↔ a = 1 := by
  fin_cases a <;> decide

@[simp]
theorem nineMark_eq_zero_iff (v : NineMark) :
    v = zeroNineMark ↔
      signedDigitValue v.1 = 0 ∧ signedDigitValue v.2 = 0 := by
  rcases v with ⟨a, b⟩
  simp [zeroNineMark]

/-- There are eight nonzero marks. -/
theorem card_nonzeroNineMark :
    Fintype.card {v : NineMark // v ≠ zeroNineMark} = 8 := by
  decide

/-- Exactly three of the nine marks lie on the real line through a fixed
nonzero mark. -/
theorem card_nineMarkCollinear (v : NineMark)
    (hv : v ≠ zeroNineMark) :
    Fintype.card {w : NineMark // NineMarkCollinear v w} = 3 := by
  rcases v with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [zeroNineMark] at hv <;> decide

/-- Exactly six marks lie outside the real line through a fixed nonzero
mark. -/
theorem card_nineMarkNoncollinear (v : NineMark)
    (hv : v ≠ zeroNineMark) :
    Fintype.card {w : NineMark // ¬NineMarkCollinear v w} = 6 := by
  rcases v with ⟨a, b⟩
  fin_cases a <;> fin_cases b <;>
    simp [zeroNineMark] at hv <;> decide

/-- A noncollinear ordered pair has a nonzero integral determinant. -/
theorem one_le_abs_nineMarkDet {v w : NineMark}
    (hvw : ¬NineMarkCollinear v w) :
    (1 : ℤ) ≤ |nineMarkDet v w| := by
  exact Int.one_le_abs hvw

/-- Every coordinate of a mark has absolute value at most one. -/
theorem abs_signedDigitValue_le_one (a : SignedDigit) :
    |signedDigitValue a| ≤ 1 := by
  fin_cases a <;> norm_num [signedDigitValue]

/-- Real value of a signed digit. -/
def signedDigitReal (a : SignedDigit) : ℝ :=
  (signedDigitValue a : ℝ)

/-- The two coordinates of the linear combination of two nine-marks. -/
def nineMarkLinearFirst
    (v q : NineMark) (x y : ℝ) : ℝ :=
  signedDigitReal v.1 * x + signedDigitReal q.1 * y

def nineMarkLinearSecond
    (v q : NineMark) (x y : ℝ) : ℝ :=
  signedDigitReal v.2 * x + signedDigitReal q.2 * y

def nineMarkDetReal (v q : NineMark) : ℝ :=
  signedDigitReal v.1 * signedDigitReal q.2 -
    signedDigitReal v.2 * signedDigitReal q.1

theorem nineMarkDetReal_eq_cast (v q : NineMark) :
    nineMarkDetReal v q = (nineMarkDet v q : ℝ) := by
  simp [nineMarkDetReal, nineMarkDet, signedDigitReal]

theorem one_le_abs_nineMarkDetReal
    {v q : NineMark} (hvq : ¬ NineMarkCollinear v q) :
    (1 : ℝ) ≤ |nineMarkDetReal v q| := by
  rw [nineMarkDetReal_eq_cast, ← Int.cast_abs]
  exact_mod_cast one_le_abs_nineMarkDet hvq

theorem abs_signedDigitReal_le_one (a : SignedDigit) :
    |signedDigitReal a| ≤ 1 := by
  rw [signedDigitReal, ← Int.cast_abs]
  exact_mod_cast abs_signedDigitValue_le_one a

/-- A noncollinear pair of marks turns a two-dimensional small-ball event
into two independent translated intervals of width `4*w`. -/
theorem noncollinear_twoPivot_forces_intervals
    {v q : NineMark} (hvq : ¬ NineMarkCollinear v q)
    {x y z₁ z₂ w : ℝ} (hw : 0 ≤ w)
    (hfirst :
      |nineMarkLinearFirst v q x y - z₁| ≤ w)
    (hsecond :
      |nineMarkLinearSecond v q x y - z₂| ≤ w) :
    let centerX :=
      (signedDigitReal q.2 * z₁ -
        signedDigitReal q.1 * z₂) /
          nineMarkDetReal v q
    let centerY :=
      (-signedDigitReal v.2 * z₁ +
        signedDigitReal v.1 * z₂) /
          nineMarkDetReal v q
    centerX - 2 * w ≤ x ∧
      x ≤ (centerX - 2 * w) + 4 * w ∧
      centerY - 2 * w ≤ y ∧
      y ≤ (centerY - 2 * w) + 4 * w := by
  dsimp only
  let D := nineMarkDetReal v q
  let targetX :=
    signedDigitReal q.2 * z₁ -
      signedDigitReal q.1 * z₂
  let targetY :=
    -signedDigitReal v.2 * z₁ +
      signedDigitReal v.1 * z₂
  have hDabs : (1 : ℝ) ≤ |D| := by
    exact one_le_abs_nineMarkDetReal hvq
  have hDpos : 0 < |D| :=
    zero_lt_one.trans_le hDabs
  have hDne : D ≠ 0 := by
    exact (abs_pos.mp hDpos)
  have herrorX :
      |D * x - targetX| ≤ 2 * w := by
    have hid :
        D * x - targetX =
          signedDigitReal q.2 *
              (nineMarkLinearFirst v q x y - z₁) -
            signedDigitReal q.1 *
              (nineMarkLinearSecond v q x y - z₂) := by
      dsimp [D, targetX, nineMarkDetReal,
        nineMarkLinearFirst, nineMarkLinearSecond]
      ring
    rw [hid]
    calc
      |signedDigitReal q.2 *
              (nineMarkLinearFirst v q x y - z₁) -
            signedDigitReal q.1 *
              (nineMarkLinearSecond v q x y - z₂)| ≤
          |signedDigitReal q.2 *
              (nineMarkLinearFirst v q x y - z₁)| +
            |signedDigitReal q.1 *
              (nineMarkLinearSecond v q x y - z₂)| :=
        abs_sub _ _
      _ = |signedDigitReal q.2| *
              |nineMarkLinearFirst v q x y - z₁| +
            |signedDigitReal q.1| *
              |nineMarkLinearSecond v q x y - z₂| := by
        rw [abs_mul, abs_mul]
      _ ≤ 1 * w + 1 * w := by
        apply add_le_add
        · exact mul_le_mul
            (abs_signedDigitReal_le_one q.2) hfirst
            (abs_nonneg _) (by norm_num)
        · exact mul_le_mul
            (abs_signedDigitReal_le_one q.1) hsecond
            (abs_nonneg _) (by norm_num)
      _ = 2 * w := by ring
  have herrorY :
      |D * y - targetY| ≤ 2 * w := by
    have hid :
        D * y - targetY =
          -signedDigitReal v.2 *
              (nineMarkLinearFirst v q x y - z₁) +
            signedDigitReal v.1 *
              (nineMarkLinearSecond v q x y - z₂) := by
      dsimp [D, targetY, nineMarkDetReal,
        nineMarkLinearFirst, nineMarkLinearSecond]
      ring
    rw [hid]
    calc
      |-signedDigitReal v.2 *
              (nineMarkLinearFirst v q x y - z₁) +
            signedDigitReal v.1 *
              (nineMarkLinearSecond v q x y - z₂)| ≤
          |-signedDigitReal v.2 *
              (nineMarkLinearFirst v q x y - z₁)| +
            |signedDigitReal v.1 *
              (nineMarkLinearSecond v q x y - z₂)| :=
        abs_add_le _ _
      _ = |signedDigitReal v.2| *
              |nineMarkLinearFirst v q x y - z₁| +
            |signedDigitReal v.1| *
              |nineMarkLinearSecond v q x y - z₂| := by
        rw [abs_mul, abs_mul, abs_neg]
      _ ≤ 1 * w + 1 * w := by
        apply add_le_add
        · exact mul_le_mul
            (abs_signedDigitReal_le_one v.2) hfirst
            (abs_nonneg _) (by norm_num)
        · exact mul_le_mul
            (abs_signedDigitReal_le_one v.1) hsecond
            (abs_nonneg _) (by norm_num)
      _ = 2 * w := by ring
  have hcenterX :
      |x - targetX / D| ≤ 2 * w := by
    have hquot :
        |x - targetX / D| =
          |D * x - targetX| / |D| := by
      rw [show x - targetX / D =
          (D * x - targetX) / D by
            field_simp [hDne]]
      exact abs_div _ _
    rw [hquot]
    calc
      |D * x - targetX| / |D| ≤
          (2 * w) / |D| :=
        div_le_div_of_nonneg_right herrorX hDpos.le
      _ ≤ 2 * w := by
        apply (div_le_iff₀ hDpos).2
        nlinarith
  have hcenterY :
      |y - targetY / D| ≤ 2 * w := by
    have hquot :
        |y - targetY / D| =
          |D * y - targetY| / |D| := by
      rw [show y - targetY / D =
          (D * y - targetY) / D by
            field_simp [hDne]]
      exact abs_div _ _
    rw [hquot]
    calc
      |D * y - targetY| / |D| ≤
          (2 * w) / |D| :=
        div_le_div_of_nonneg_right herrorY hDpos.le
      _ ≤ 2 * w := by
        apply (div_le_iff₀ hDpos).2
        nlinarith
  have hx := abs_le.mp hcenterX
  have hy := abs_le.mp hcenterY
  dsimp [D, targetX, targetY] at hx hy ⊢
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Data remaining after fixing the ranks of the first nonzero mark and
the first subsequent mark outside its line.  `middle` records the marks
strictly between the two pivots, and `tail` the unrestricted later marks. -/
abbrev RankTwoMarkData (middleLength tailLength : ℕ) :=
  Σ v : {v : NineMark // v ≠ zeroNineMark},
    (Fin middleLength →
      {w : NineMark // NineMarkCollinear v.1 w}) ×
    {w : NineMark // ¬NineMarkCollinear v.1 w} ×
    (Fin tailLength → NineMark)

/-- Data remaining after fixing the rank of the first nonzero mark in a
rank-one sequence. -/
abbrev RankOneMarkData (tailLength : ℕ) :=
  Σ v : {v : NineMark // v ≠ zeroNineMark},
    Fin tailLength →
      {w : NineMark // NineMarkCollinear v.1 w}

/-- Exact count `8 · 3^m · 6 · 9^t` for the two-pivot mark data. -/
theorem card_rankTwoMarkData (middleLength tailLength : ℕ) :
    Fintype.card (RankTwoMarkData middleLength tailLength) =
      8 * 3 ^ middleLength * 6 * 9 ^ tailLength := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ v : {v : NineMark // v ≠ zeroNineMark},
        Fintype.card
          ((Fin middleLength →
              {w : NineMark // NineMarkCollinear v.1 w}) ×
            {w : NineMark // ¬NineMarkCollinear v.1 w} ×
            (Fin tailLength → NineMark))) =
        ∑ _v : {v : NineMark // v ≠ zeroNineMark},
          3 ^ middleLength * (6 * 9 ^ tailLength) := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Fintype.card_prod, Fintype.card_prod,
        Fintype.card_pi_const, Fintype.card_pi_const,
        card_nineMarkCollinear v.1 v.2,
        card_nineMarkNoncollinear v.1 v.2]
      norm_num
    _ = 8 * (3 ^ middleLength * (6 * 9 ^ tailLength)) := by
      rw [Finset.sum_const, Finset.card_univ,
        card_nonzeroNineMark]
      simp
    _ = 8 * 3 ^ middleLength * 6 * 9 ^ tailLength := by ring

/-- Exact count `8 · 3^t` for the rank-one mark data. -/
theorem card_rankOneMarkData (tailLength : ℕ) :
    Fintype.card (RankOneMarkData tailLength) =
      8 * 3 ^ tailLength := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ v : {v : NineMark // v ≠ zeroNineMark},
        Fintype.card
          (Fin tailLength →
            {w : NineMark // NineMarkCollinear v.1 w})) =
        ∑ _v : {v : NineMark // v ≠ zeroNineMark},
          3 ^ tailLength := by
      apply Finset.sum_congr rfl
      intro v _hv
      rw [Fintype.card_pi_const,
        card_nineMarkCollinear v.1 v.2]
    _ = 8 * 3 ^ tailLength := by
      rw [Finset.sum_const, Finset.card_univ,
        card_nonzeroNineMark]
      simp

/-! ## Summing the canonical pivot ranks -/

/-- The geometric mass assigned to a one-indexed pivot rank, written with
a zero-indexed Lean argument. -/
def pivotRankDecay (i : ℕ) : ℝ :=
  (1 / 3 : ℝ) ^ (i + 1)

theorem pivotRankDecay_nonneg (i : ℕ) :
    0 ≤ pivotRankDecay i := by
  exact pow_nonneg (by norm_num) _

/-- Partial version of the convergent rank series from the manuscript. -/
def pivotRankSeries (ell : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ i ∈ Finset.range K, pivotRankDecay i / ell i

/-- The rank-two contribution after the local two-prime estimate has been
inserted.  The strict rank ordering is retained explicitly. -/
def twoPivotRankContribution
    (ell : ℕ → ℝ) (K : ℕ) (C w : ℝ) : ℝ :=
  ∑ i ∈ Finset.range K,
    ∑ j ∈ Finset.range K,
      if i < j then
        16 * C * w ^ 2 *
          ((pivotRankDecay i / ell i) *
            (pivotRankDecay j / ell j))
      else 0

/-- The pivotal summability estimate: the exact `16` from the nine-mark
enumeration is harmless once the weighted rank series is bounded. -/
theorem twoPivotRankContribution_le
    {ell : ℕ → ℝ} {K : ℕ} {C w L : ℝ}
    (hell : ∀ i < K, 0 < ell i)
    (hC : 0 ≤ C) (hL : 0 ≤ L)
    (hseries : pivotRankSeries ell K ≤ L) :
    twoPivotRankContribution ell K C w ≤
      16 * C * w ^ 2 * L ^ 2 := by
  have hterm (i : ℕ) (hi : i ∈ Finset.range K) :
      0 ≤ pivotRankDecay i / ell i :=
    div_nonneg (pivotRankDecay_nonneg i)
      (hell i (Finset.mem_range.mp hi)).le
  calc
    twoPivotRankContribution ell K C w ≤
        ∑ i ∈ Finset.range K,
          ∑ j ∈ Finset.range K,
            16 * C * w ^ 2 *
              ((pivotRankDecay i / ell i) *
                (pivotRankDecay j / ell j)) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      split_ifs
      · exact le_rfl
      · exact mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num) hC) (sq_nonneg w))
          (mul_nonneg (hterm i hi) (hterm j hj))
    _ = 16 * C * w ^ 2 * (pivotRankSeries ell K) ^ 2 := by
      have hsquare :
          (∑ i ∈ Finset.range K,
              pivotRankDecay i / ell i) ^ 2 =
            ∑ i ∈ Finset.range K,
              ∑ j ∈ Finset.range K,
                (pivotRankDecay i / ell i) *
                  (pivotRankDecay j / ell j) := by
        rw [pow_two, Finset.sum_mul_sum]
      rw [pivotRankSeries, hsquare]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [Finset.mul_sum]
    _ ≤ 16 * C * w ^ 2 * L ^ 2 := by
      apply mul_le_mul_of_nonneg_left
      · exact (sq_le_sq₀
          (Finset.sum_nonneg fun i hi => hterm i hi) hL).2 hseries
      · positivity

/-- The rank-one contribution, before using decay at the depth horizon. -/
def onePivotRankContribution
    (ell : ℕ → ℝ) (K : ℕ) (C w : ℝ) : ℝ :=
  8 * C * w * (1 / 3 : ℝ) ^ K * pivotRankSeries ell K

/-- The endpoint decay converts the rank-one contribution into an
`O(w²)` error. -/
theorem onePivotRankContribution_le
    {ell : ℕ → ℝ} {K : ℕ} {C w L E : ℝ}
    (hell : ∀ i < K, 0 < ell i)
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hseries : pivotRankSeries ell K ≤ L)
    (hendpoint : (1 / 3 : ℝ) ^ K ≤ E * w)
    (hE : 0 ≤ E) :
    onePivotRankContribution ell K C w ≤
      8 * C * E * L * w ^ 2 := by
  have hseriesNonneg :
      0 ≤ pivotRankSeries ell K := by
    apply Finset.sum_nonneg
    intro i hi
    exact div_nonneg (pivotRankDecay_nonneg i)
      (hell i (Finset.mem_range.mp hi)).le
  rw [onePivotRankContribution]
  calc
    8 * C * w * (1 / 3 : ℝ) ^ K *
          pivotRankSeries ell K ≤
        8 * C * w * (E * w) * pivotRankSeries ell K := by
      gcongr
    _ ≤ 8 * C * w * (E * w) * L := by
      gcongr
    _ = 8 * C * E * L * w ^ 2 := by ring

/-! ## A finite one-point small-ball estimate -/

/-- The sum of a scalar weight over a selected subset. -/
def selectedWeightSum {α : Type*} [DecidableEq α]
    (u : α → ℝ) (S : Finset α) : ℝ :=
  ∑ p ∈ S, u p

/-- A selected subset hits an eligible point and its total weight lies in
the closed interval `[a,b]`. -/
def SelectedIntervalEvent {α : Type*} [DecidableEq α]
    (eligible : α → Prop) (u : α → ℝ) (a b : ℝ)
    (S : Finset α) : Prop :=
  (∃ p ∈ S, eligible p) ∧
    a ≤ selectedWeightSum u S ∧ selectedWeightSum u S ≤ b

/-- The finite mass of a subset event under independent Bernoulli
parameters. -/
noncomputable def subsetEventMass {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (E : Finset α → Prop) : ℝ := by
  classical
  exact ∑ S ∈ P.powerset, if E S then subsetWeight P q S else 0

/-- One-point factorial insertion turns a local odds bound into a
small-ball bound.  This deliberately overcounts all eligible selected
points; the existence of at least one such point is enough for the desired
upper bound and avoids any measurable choice of a canonical pivot. -/
theorem subsetEventMass_selectedInterval_le
    {α : Type*} [DecidableEq α]
    (P : Finset α) (q u : α → ℝ)
    (eligible : α → Prop) [DecidablePred eligible]
    (a b L : ℝ)
    (hq0 : ∀ p ∈ P, 0 ≤ q p)
    (hq1 : ∀ p ∈ P, q p < 1)
    (hlocal : ∀ A ∈ P.powerset,
      (∑ p ∈ P \ A,
        if eligible p ∧
            a ≤ u p + selectedWeightSum u A ∧
            u p + selectedWeightSum u A ≤ b
        then q p / (1 - q p) else 0) ≤ L) :
    subsetEventMass P q
        (SelectedIntervalEvent eligible u a b) ≤ L := by
  classical
  let F : Finset α → α → ℝ := fun S p =>
    if eligible p ∧
        a ≤ selectedWeightSum u S ∧
        selectedWeightSum u S ≤ b
    then 1 else 0
  have hpoint (S : Finset α) (hSP : S ∈ P.powerset) :
      (if SelectedIntervalEvent eligible u a b S
        then subsetWeight P q S else 0) ≤
      ∑ p ∈ S, subsetWeight P q S * F S p := by
    by_cases hE : SelectedIntervalEvent eligible u a b S
    · rw [if_pos hE]
      obtain ⟨p, hpS, hpEligible⟩ := hE.1
      have hweight :
          0 ≤ subsetWeight P q S :=
        subsetWeight_nonneg
          (fun x hx => hq0 x hx)
          (fun x hx => (hq1 x hx).le)
          (Finset.mem_powerset.mp hSP)
      calc
        subsetWeight P q S =
            subsetWeight P q S * F S p := by
              simp [F, hpEligible, hE.2.1, hE.2.2]
        _ ≤ ∑ x ∈ S, subsetWeight P q S * F S x := by
              apply Finset.single_le_sum
                (s := S)
                (f := fun x => subsetWeight P q S * F S x)
              · intro x hx
                dsimp [F]
                split_ifs
                · simpa using hweight
                · norm_num
              · exact hpS
    · rw [if_neg hE]
      apply Finset.sum_nonneg
      intro p hp
      exact mul_nonneg
        (subsetWeight_nonneg
          (fun x hx => hq0 x hx)
          (fun x hx => (hq1 x hx).le)
          (Finset.mem_powerset.mp hSP))
        (by dsimp [F]; split_ifs <;> norm_num)
  calc
    subsetEventMass P q
        (SelectedIntervalEvent eligible u a b) ≤
        ∑ S ∈ P.powerset,
          ∑ p ∈ S, subsetWeight P q S * F S p := by
      rw [subsetEventMass]
      exact Finset.sum_le_sum fun S hS => hpoint S hS
    _ =
        ∑ A ∈ P.powerset, ∑ p ∈ P \ A,
          subsetWeight P q A * (q p / (1 - q p)) *
            F (insert p A) p := by
      exact factorialInsertion_one_odds P q F
        (fun p hp => (hq1 p hp).ne)
    _ ≤ ∑ A ∈ P.powerset, subsetWeight P q A * L := by
      apply Finset.sum_le_sum
      intro A hA
      have hAweight :
          0 ≤ subsetWeight P q A :=
        subsetWeight_nonneg
          (fun x hx => hq0 x hx)
          (fun x hx => (hq1 x hx).le)
          (Finset.mem_powerset.mp hA)
      have hfactor :
          (∑ p ∈ P \ A,
              subsetWeight P q A * (q p / (1 - q p)) *
                F (insert p A) p) =
            subsetWeight P q A *
              ∑ p ∈ P \ A,
                (q p / (1 - q p)) * F (insert p A) p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p _hp
        ring
      rw [hfactor]
      apply mul_le_mul_of_nonneg_left _ hAweight
      have hlocal' := hlocal A hA
      convert hlocal' using 1
      apply Finset.sum_congr rfl
      intro p hp
      have hpA : p ∉ A := (Finset.mem_sdiff.mp hp).2
      simp [F, selectedWeightSum, hpA]
    _ = L := by
      rw [← Finset.sum_mul, sum_subsetWeight]
      simp

/-! ## The missing-petal parameter -/

/-- Conditional on absence from one represented support, the missing petal
selects a prime with probability `1/(3p)`. -/
def missingPetalParameter (p : ℕ) : ℝ :=
  1 / (3 * (p : ℝ))

theorem missingPetalParameter_nonneg (p : ℕ) :
    0 ≤ missingPetalParameter p := by
  exact div_nonneg zero_le_one (by positivity)

theorem missingPetalParameter_lt_one {p : ℕ} (hp : 0 < p) :
    missingPetalParameter p < 1 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [missingPetalParameter, div_lt_one (by positivity)]
  nlinarith

/-- Exact odds of the missing-petal Bernoulli variable. -/
theorem missingPetal_odds_eq {p : ℕ} (hp : 0 < p) :
    missingPetalParameter p / (1 - missingPetalParameter p) =
      1 / (3 * (p : ℝ) - 1) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [missingPetalParameter]
  field_simp

/-- The missing-petal odds are bounded by the reciprocal-prime weight used
in the local prime-mass estimate. -/
theorem missingPetal_odds_le_reciprocal {p : ℕ} (hp : 0 < p) :
    missingPetalParameter p / (1 - missingPetalParameter p) ≤
      1 / (p : ℝ) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hpOne : (1 : ℝ) ≤ p := by exact_mod_cast hp
  rw [missingPetal_odds_eq hp]
  apply one_div_le_one_div_of_le hpR
  nlinarith

/-- Missing-petal small-ball estimate in the exact form needed by the
prime-band proof.  The only analytic input is the displayed local
reciprocal-mass bound; all Bernoulli and insertion bookkeeping is proved
here. -/
theorem subsetEventMass_missingPetal_le
    (P : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) [DecidablePred eligible]
    (a b L : ℝ)
    (hPpos : ∀ p ∈ P, 0 < p)
    (hlocal : ∀ A ∈ P.powerset,
      (∑ p ∈ P \ A,
        if eligible p ∧
            a ≤ u p + selectedWeightSum u A ∧
            u p + selectedWeightSum u A ≤ b
        then 1 / (p : ℝ) else 0) ≤ L) :
    subsetEventMass P missingPetalParameter
        (SelectedIntervalEvent eligible u a b) ≤ L := by
  apply subsetEventMass_selectedInterval_le
    P missingPetalParameter u eligible a b L
  · intro p _hp
    exact missingPetalParameter_nonneg p
  · intro p hp
    exact missingPetalParameter_lt_one (hPpos p hp)
  · intro A hA
    calc
      (∑ p ∈ P \ A,
          if eligible p ∧
              a ≤ u p + selectedWeightSum u A ∧
              u p + selectedWeightSum u A ≤ b
          then missingPetalParameter p /
            (1 - missingPetalParameter p) else 0) ≤
          ∑ p ∈ P \ A,
            if eligible p ∧
                a ≤ u p + selectedWeightSum u A ∧
                u p + selectedWeightSum u A ≤ b
            then 1 / (p : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs
        · exact missingPetal_odds_le_reciprocal
            (hPpos p (Finset.mem_sdiff.mp hp).1)
        · exact le_rfl
      _ ≤ L := hlocal A hA

/-- Reciprocal-prime mass in a translated scalar window. -/
def reciprocalWindowMass
    (P : Finset ℕ) (u : ℕ → ℝ) (eligible : ℕ → Prop)
    (x width : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ P,
    if eligible p ∧ x ≤ u p ∧ u p ≤ x + width
    then 1 / (p : ℝ) else 0

/-- A uniform local reciprocal-window estimate is sufficient for the
missing-petal small-ball bound.  Translation by the already selected
residual set is performed exactly in the proof. -/
theorem subsetEventMass_missingPetal_le_of_window
    (P : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) [DecidablePred eligible]
    (a b L : ℝ)
    (hPpos : ∀ p ∈ P, 0 < p)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMass P u eligible x (b - a) ≤ L) :
    subsetEventMass P missingPetalParameter
        (SelectedIntervalEvent eligible u a b) ≤ L := by
  apply subsetEventMass_missingPetal_le
    P u eligible a b L hPpos
  intro A hA
  let x : ℝ := a - selectedWeightSum u A
  have heq :
      (∑ p ∈ P \ A,
        if eligible p ∧
            a ≤ u p + selectedWeightSum u A ∧
            u p + selectedWeightSum u A ≤ b
        then 1 / (p : ℝ) else 0) =
      ∑ p ∈ P \ A,
        if eligible p ∧ x ≤ u p ∧ u p ≤ x + (b - a)
        then 1 / (p : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro p _hp
    congr 1
    apply propext
    dsimp [x]
    constructor <;> rintro ⟨heligible, hlower, hupper⟩
    · exact ⟨heligible, by linarith, by linarith⟩
    · exact ⟨heligible, by linarith, by linarith⟩
  rw [heq]
  calc
    (∑ p ∈ P \ A,
        if eligible p ∧ x ≤ u p ∧ u p ≤ x + (b - a)
        then 1 / (p : ℝ) else 0) ≤
      ∑ p ∈ P,
        if eligible p ∧ x ≤ u p ∧ u p ≤ x + (b - a)
        then 1 / (p : ℝ) else 0 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.sdiff_subset)
      intro p _hpP _hpDiff
      split_ifs
      · exact div_nonneg zero_le_one (Nat.cast_nonneg p)
      · exact le_rfl
    _ = reciprocalWindowMass P u eligible x (b - a) := by
      unfold reciprocalWindowMass
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases h :
          eligible p ∧ x ≤ u p ∧ u p ≤ x + (b - a) <;>
        simp [h]
    _ ≤ L := hwindow x

/-- Reciprocal-window mass after attaching a positive natural size to each
point of an arbitrary finite type. -/
def reciprocalWindowMassAlong
    {α : Type*} [DecidableEq α]
    (P : Finset α) (n : α → ℕ)
    (u : α → ℝ) (eligible : α → Prop)
    (x width : ℝ) : ℝ := by
  classical
  exact ∑ p ∈ P,
    if eligible p ∧ x ≤ u p ∧ u p ≤ x + width
    then 1 / (n p : ℝ) else 0

/-- Reciprocal mass of ordered distinct pivot pairs satisfying a
two-dimensional small-ball constraint. -/
def twoPivotReciprocalMassAlong
    {α : Type*} [DecidableEq α]
    (P : Finset α) (n : α → ℕ) (u : α → ℝ)
    (eligible : α → Prop)
    (v q : NineMark) (z₁ z₂ w : ℝ) : ℝ := by
  classical
  exact
    ∑ p ∈ P, ∑ r ∈ P,
      if p ≠ r ∧ eligible p ∧ eligible r ∧
          |nineMarkLinearFirst v q (u p) (u r) - z₁| ≤ w ∧
          |nineMarkLinearSecond v q (u p) (u r) - z₂| ≤ w
      then (1 / (n p : ℝ)) * (1 / (n r : ℝ))
      else 0

/-- The determinant argument reduces the local two-pivot estimate to the
square of a one-dimensional reciprocal-window bound. -/
theorem twoPivotReciprocalMassAlong_le_sq_window
    {α : Type*} [DecidableEq α]
    (P : Finset α) (n : α → ℕ) (u : α → ℝ)
    (eligible : α → Prop) [DecidablePred eligible]
    {v q : NineMark} (hvq : ¬ NineMarkCollinear v q)
    (z₁ z₂ w L : ℝ) (hw : 0 ≤ w) (hL : 0 ≤ L)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
        P n u eligible x (4 * w) ≤ L) :
    twoPivotReciprocalMassAlong
        P n u eligible v q z₁ z₂ w ≤ L ^ 2 := by
  classical
  let centerP :=
    (signedDigitReal q.2 * z₁ -
      signedDigitReal q.1 * z₂) /
        nineMarkDetReal v q
  let centerQ :=
    (-signedDigitReal v.2 * z₁ +
      signedDigitReal v.1 * z₂) /
        nineMarkDetReal v q
  let a := centerP - 2 * w
  let b := centerQ - 2 * w
  have hmassP :
      0 ≤ reciprocalWindowMassAlong
        P n u eligible a (4 * w) := by
    unfold reciprocalWindowMassAlong
    apply Finset.sum_nonneg
    intro p _hp
    split_ifs
    · positivity
    · exact le_rfl
  have hmassQ :
      0 ≤ reciprocalWindowMassAlong
        P n u eligible b (4 * w) := by
    unfold reciprocalWindowMassAlong
    apply Finset.sum_nonneg
    intro p _hp
    split_ifs
    · positivity
    · exact le_rfl
  calc
    twoPivotReciprocalMassAlong
        P n u eligible v q z₁ z₂ w ≤
      reciprocalWindowMassAlong P n u eligible a (4 * w) *
        reciprocalWindowMassAlong P n u eligible b (4 * w) := by
      unfold twoPivotReciprocalMassAlong
      unfold reciprocalWindowMassAlong
      rw [Finset.sum_mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro r hr
      by_cases hevent :
          p ≠ r ∧ eligible p ∧ eligible r ∧
            |nineMarkLinearFirst v q (u p) (u r) - z₁| ≤ w ∧
            |nineMarkLinearSecond v q (u p) (u r) - z₂| ≤ w
      · have hinterval :=
          noncollinear_twoPivot_forces_intervals
            hvq hw hevent.2.2.2.1 hevent.2.2.2.2
        have hpInterval :
            eligible p ∧ a ≤ u p ∧ u p ≤ a + 4 * w := by
          exact ⟨hevent.2.1, by
            simpa only [a, centerP] using hinterval.1, by
            simpa only [a, centerP] using hinterval.2.1⟩
        have hrInterval :
            eligible r ∧ b ≤ u r ∧ u r ≤ b + 4 * w := by
          exact ⟨hevent.2.2.1, by
            simpa only [b, centerQ] using hinterval.2.2.1, by
            simpa only [b, centerQ] using hinterval.2.2.2⟩
        simp [hevent, hpInterval, hrInterval]
      · rw [if_neg hevent]
        apply mul_nonneg
        · split_ifs
          · exact div_nonneg zero_le_one
              (Nat.cast_nonneg (n p))
          · exact le_rfl
        · split_ifs
          · exact div_nonneg zero_le_one
              (Nat.cast_nonneg (n r))
          · exact le_rfl
    _ ≤ L * L :=
      mul_le_mul (hwindow a) (hwindow b) hmassQ hL
    _ = L ^ 2 := by ring

theorem reciprocalWindowMassAlong_mono
    {α : Type*} [DecidableEq α]
    {P Q : Finset α} (hPQ : P ⊆ Q)
    (n : α → ℕ) (u : α → ℝ) (eligible : α → Prop)
    (x width : ℝ) :
    reciprocalWindowMassAlong P n u eligible x width ≤
      reciprocalWindowMassAlong Q n u eligible x width := by
  classical
  unfold reciprocalWindowMassAlong
  apply Finset.sum_le_sum_of_subset_of_nonneg hPQ
  intro p _hpQ _hpP
  split_ifs
  · exact div_nonneg zero_le_one (Nat.cast_nonneg (n p))
  · exact le_rfl

/-- A depth cutoff gives a lower bound on normalized logarithmic
position. -/
theorem normalizedLogWeight_lower_of_depth_le
    {N : ℝ} {p : ℕ} {d : ℝ}
    (hweight : 0 < normalizedLogWeight N p)
    (hdepth : normalizedLogDepth N p ≤ d) :
    Real.exp (-d) ≤ normalizedLogWeight N p := by
  have hlog :
      -d ≤ Real.log (normalizedLogWeight N p) := by
    unfold normalizedLogDepth at hdepth
    linarith
  calc
    Real.exp (-d) ≤
        Real.exp (Real.log (normalizedLogWeight N p)) :=
      Real.exp_le_exp.mpr hlog
    _ = normalizedLogWeight N p :=
      Real.exp_log hweight

/-- An inclusive normalized-log window is contained in a slightly
enlarged `LocalPrimeBand`.  The fixed `log 4` padding absorbs both
integer endpoint roundings exactly. -/
theorem mem_localPrimeBand_of_normalizedLogWindow
    {N p : ℕ} {x h : ℝ}
    (hN : 0 < N) (hp : p.Prime)
    (hlower : x ≤ normalizedLogWeight (N : ℝ) p)
    (hupper :
      normalizedLogWeight (N : ℝ) p ≤
        x + h / (N : ℝ)) :
    p ∈ LocalPrimeBand.localPrimeBand N
      (x - Real.log 4 / (N : ℝ))
      (h + Real.log 4) := by
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast hp.pos
  have hpTwoR : (2 : ℝ) ≤ p := by
    exact_mod_cast hp.two_le
  have hNx :
      (N : ℝ) * x ≤ Real.log (p : ℝ) := by
    simpa only [mul_comm] using
      (le_div_iff₀ hNR).mp hlower
  have hlogUpper :
      Real.log (p : ℝ) ≤ (N : ℝ) * x + h := by
    have hu := (div_le_iff₀ hNR).mp hupper
    calc
      Real.log (p : ℝ) ≤
          (x + h / (N : ℝ)) * (N : ℝ) := hu
      _ = (N : ℝ) * x + h := by
        field_simp [hNR.ne']
  have hexpNx :
      Real.exp ((N : ℝ) * x) ≤ (p : ℝ) := by
    calc
      Real.exp ((N : ℝ) * x) ≤
          Real.exp (Real.log (p : ℝ)) :=
        Real.exp_le_exp.mpr hNx
      _ = (p : ℝ) := Real.exp_log hpR
  have hpad :
      Real.exp
          ((N : ℝ) *
            (x - Real.log 4 / (N : ℝ))) ≤
        (p : ℝ) - 1 := by
    calc
      Real.exp
          ((N : ℝ) *
            (x - Real.log 4 / (N : ℝ))) =
          Real.exp ((N : ℝ) * x) / 4 := by
        have hexponent :
            (N : ℝ) *
                (x - Real.log 4 / (N : ℝ)) =
              (N : ℝ) * x - Real.log 4 := by
          field_simp [hNR.ne']
        rw [hexponent, Real.exp_sub,
          Real.exp_log (by norm_num : (0 : ℝ) < 4)]
      _ ≤ (p : ℝ) / 4 :=
        div_le_div_of_nonneg_right hexpNx (by norm_num)
      _ ≤ (p : ℝ) - 1 := by
        nlinarith
  have hlowerEndpoint :
      LocalPrimeBand.localLowerEndpoint N
          (x - Real.log 4 / (N : ℝ)) ≤ p - 1 := by
    unfold LocalPrimeBand.localLowerEndpoint
      PrimeSums.expEndpoint
    apply Nat.ceil_le.mpr
    simpa [Nat.cast_sub hp.one_le] using hpad
  have hpExpUpper :
      (p : ℝ) ≤
        Real.exp ((N : ℝ) * x + h) := by
    calc
      (p : ℝ) = Real.exp (Real.log (p : ℝ)) :=
        (Real.exp_log hpR).symm
      _ ≤ Real.exp ((N : ℝ) * x + h) :=
        Real.exp_le_exp.mpr hlogUpper
  have hlowerReal :
      Real.exp
          ((N : ℝ) *
            (x - Real.log 4 / (N : ℝ))) ≤
        (LocalPrimeBand.localLowerEndpoint N
          (x - Real.log 4 / (N : ℝ)) : ℝ) := by
    exact Nat.le_ceil _
  have hfactor :
      Real.exp ((N : ℝ) * x + h) ≤
        Real.exp (h + Real.log 4) *
          (LocalPrimeBand.localLowerEndpoint N
            (x - Real.log 4 / (N : ℝ)) : ℝ) := by
    calc
      Real.exp ((N : ℝ) * x + h) =
          Real.exp (h + Real.log 4) *
            Real.exp
              ((N : ℝ) *
                (x - Real.log 4 / (N : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        field_simp [hNR.ne']
        ring
      _ ≤ Real.exp (h + Real.log 4) *
          (LocalPrimeBand.localLowerEndpoint N
            (x - Real.log 4 / (N : ℝ)) : ℝ) :=
        mul_le_mul_of_nonneg_left hlowerReal (Real.exp_nonneg _)
  have hupperReal :
      (p : ℝ) ≤
        (LocalPrimeBand.localUpperEndpoint N
          (x - Real.log 4 / (N : ℝ))
          (h + Real.log 4) : ℝ) := by
    exact (hpExpUpper.trans hfactor).trans (Nat.le_ceil _)
  rw [LocalPrimeBand.mem_localPrimeBand]
  refine ⟨hp, hlowerEndpoint.trans_lt ?_, ?_⟩
  · exact Nat.sub_lt hp.pos (by decide)
  · exact_mod_cast hupperReal

/-- Convert the normalized-log reciprocal window appearing in the
missing-petal insertion argument to the established local-prime-band
mass.  The factor `2` changes `1/p` into the probability-compatible
weight `1/(p+1)`. -/
theorem reciprocalWindowMassAlong_le_localBandShifted
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {N : ℕ} (hN : 0 < N)
    (eligible : ↥R → Prop) [DecidablePred eligible]
    (x h : ℝ) (hh : 0 ≤ h) :
    reciprocalWindowMassAlong
        Finset.univ (fun p : ↥R => p.1)
        (fun p : ↥R => normalizedLogWeight (N : ℝ) p.1)
        eligible x (h / (N : ℝ)) ≤
      2 * LocalPrimeBand.localBandShiftedReciprocalMass
        N (x - Real.log 4 / (N : ℝ))
          (h + Real.log 4) := by
  classical
  let W : Finset ↥R := Finset.univ.filter fun p =>
    eligible p ∧
      x ≤ normalizedLogWeight (N : ℝ) p.1 ∧
      normalizedLogWeight (N : ℝ) p.1 ≤
        x + h / (N : ℝ)
  have hwindowSum :
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight (N : ℝ) p.1)
          eligible x (h / (N : ℝ)) =
        ∑ p ∈ W, 1 / (p.1 : ℝ) := by
    unfold reciprocalWindowMassAlong
    dsimp [W]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _hp
    by_cases hcondition :
        eligible p ∧
          x ≤ normalizedLogWeight (N : ℝ) p.1 ∧
          normalizedLogWeight (N : ℝ) p.1 ≤
            x + h / (N : ℝ) <;>
      simp [hcondition]
  have hvalueSum :
      (∑ p ∈ W, 1 / (p.1 : ℝ)) =
        ∑ p ∈ subtypeSupportVal W, 1 / (p : ℝ) := by
    rw [subtypeSupportVal, Finset.sum_map]
    rfl
  have hsubset :
      subtypeSupportVal W ⊆
        LocalPrimeBand.localPrimeBand N
          (x - Real.log 4 / (N : ℝ))
          (h + Real.log 4) := by
    intro p hpW
    obtain ⟨hpR, hpWsub⟩ :=
      mem_subtypeSupportVal.mp hpW
    have hpData :
        eligible (⟨p, hpR⟩ : ↥R) ∧
          x ≤ normalizedLogWeight (N : ℝ) p ∧
          normalizedLogWeight (N : ℝ) p ≤
            x + h / (N : ℝ) := by
      simpa [W] using hpWsub
    exact mem_localPrimeBand_of_normalizedLogWindow
      hN (hR p hpR) hpData.2.1 hpData.2.2
  have hpadNonneg :
      0 ≤ h + Real.log 4 := by
    exact add_nonneg hh (Real.log_nonneg (by norm_num))
  rw [hwindowSum, hvalueSum,
    LocalPrimeBand.localBandShiftedReciprocalMass_eq_sum
      hpadNonneg]
  calc
    (∑ p ∈ subtypeSupportVal W, 1 / (p : ℝ)) ≤
        ∑ p ∈ LocalPrimeBand.localPrimeBand N
          (x - Real.log 4 / (N : ℝ))
          (h + Real.log 4), 1 / (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro p _hpBand _hpW
      exact div_nonneg zero_le_one (Nat.cast_nonneg p)
    _ ≤ ∑ p ∈ LocalPrimeBand.localPrimeBand N
          (x - Real.log 4 / (N : ℝ))
          (h + Real.log 4),
          2 / ((p : ℝ) + 1) := by
      apply Finset.sum_le_sum
      intro p hpBand
      have hpPrime :=
        (LocalPrimeBand.mem_localPrimeBand.mp hpBand).1
      have hpR : (0 : ℝ) < p := by
        exact_mod_cast hpPrime.pos
      have hpOneR : (1 : ℝ) ≤ p := by
        exact_mod_cast hpPrime.one_le
      have hpR1 : (0 : ℝ) < (p : ℝ) + 1 := by
        positivity
      apply (div_le_div_iff₀ hpR hpR1).2
      nlinarith
    _ = 2 *
        ∑ p ∈ LocalPrimeBand.localPrimeBand N
          (x - Real.log 4 / (N : ℝ))
          (h + Real.log 4),
          1 / ((p : ℝ) + 1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

/-- Uniform local-prime-band control implies the exact translated
reciprocal-window estimate at scale `η / N`.  The depth cutoff supplies
the positive lower center; if a translated window lies below that center,
its eligible part is empty. -/
theorem reciprocalWindowMassAlong_normalized_le_of_localBand
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {N : ℕ} (hN : 0 < N)
    {η d K : ℝ} (hη : 0 < η)
    (hsize :
      (2 * η + Real.log 4) / (N : ℝ) ≤
        Real.exp (-d) / 2)
    (hlocal : ∀ t : ℝ, Real.exp (-d) / 2 ≤ t →
      LocalPrimeBand.localBandShiftedReciprocalMass
          N t (2 * η + Real.log 4) ≤
        K / (N : ℝ)) :
    ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight (N : ℝ) p.1)
          (fun p : ↥R =>
            normalizedLogDepth (N : ℝ) p.1 ≤ d)
          x (2 * (η / (N : ℝ))) ≤
        2 * K / (N : ℝ) := by
  classical
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hpadNonneg :
      0 ≤ 2 * η + Real.log 4 := by
    exact add_nonneg (mul_nonneg (by norm_num) hη.le)
      (Real.log_nonneg (by norm_num))
  have hKdiv : 0 ≤ K / (N : ℝ) := by
    exact
      (LocalPrimeBand.localBandShiftedReciprocalMass_nonneg
        hpadNonneg).trans
      (hlocal (Real.exp (-d) / 2) le_rfl)
  intro x
  let t := x - Real.log 4 / (N : ℝ)
  by_cases ht : Real.exp (-d) / 2 ≤ t
  · have hbridge :=
      reciprocalWindowMassAlong_le_localBandShifted
        hR hN
        (fun p : ↥R =>
          normalizedLogDepth (N : ℝ) p.1 ≤ d)
        x (2 * η) (mul_nonneg (by norm_num) hη.le)
    have hwidth :
        (2 * η) / (N : ℝ) =
          2 * (η / (N : ℝ)) := by
      ring
    rw [hwidth] at hbridge
    calc
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight (N : ℝ) p.1)
          (fun p : ↥R =>
            normalizedLogDepth (N : ℝ) p.1 ≤ d)
          x (2 * (η / (N : ℝ))) ≤
        2 * LocalPrimeBand.localBandShiftedReciprocalMass
          N t (2 * η + Real.log 4) := by
        simpa only [t] using hbridge
      _ ≤ 2 * (K / (N : ℝ)) :=
        mul_le_mul_of_nonneg_left (hlocal t ht) (by norm_num)
      _ = 2 * K / (N : ℝ) := by
        ring
  · have hzero :
        reciprocalWindowMassAlong
            Finset.univ (fun p : ↥R => p.1)
            (fun p : ↥R =>
              normalizedLogWeight (N : ℝ) p.1)
            (fun p : ↥R =>
              normalizedLogDepth (N : ℝ) p.1 ≤ d)
            x (2 * (η / (N : ℝ))) = 0 := by
      unfold reciprocalWindowMassAlong
      apply Finset.sum_eq_zero
      intro p _hp
      by_cases hpData :
          normalizedLogDepth (N : ℝ) p.1 ≤ d ∧
            x ≤ normalizedLogWeight (N : ℝ) p.1 ∧
            normalizedLogWeight (N : ℝ) p.1 ≤
              x + 2 * (η / (N : ℝ))
      · have hpPrime := hR p.1 p.2
        have hpOneR : (1 : ℝ) < p.1 := by
          exact_mod_cast hpPrime.one_lt
        have hweight :
            0 < normalizedLogWeight (N : ℝ) p.1 := by
          unfold normalizedLogWeight
          exact div_pos (Real.log_pos hpOneR) hNR
        have hposition :
            Real.exp (-d) ≤
              normalizedLogWeight (N : ℝ) p.1 :=
          normalizedLogWeight_lower_of_depth_le
            hweight hpData.1
        have hxLower :
            Real.exp (-d) -
                2 * (η / (N : ℝ)) ≤ x := by
          linarith [hpData.2.2, hposition]
        have hcenterLower :
            Real.exp (-d) -
                (2 * η + Real.log 4) / (N : ℝ) ≤
              t := by
          dsimp [t]
          calc
            Real.exp (-d) -
                  (2 * η + Real.log 4) / (N : ℝ) =
                (Real.exp (-d) -
                    2 * (η / (N : ℝ))) -
                  Real.log 4 / (N : ℝ) := by
              ring
            _ ≤ x - Real.log 4 / (N : ℝ) :=
              sub_le_sub_right hxLower _
        have hcut :
            Real.exp (-d) / 2 ≤
              Real.exp (-d) -
                (2 * η + Real.log 4) / (N : ℝ) := by
          linarith
        exact False.elim (ht (hcut.trans hcenterLower))
      · simp [hpData]
    rw [hzero]
    rw [show 2 * K / (N : ℝ) =
        2 * (K / (N : ℝ)) by ring]
    exact mul_nonneg (by norm_num) hKdiv

/-- Arbitrary-finite-type version of the missing-petal translated-window
bound.  This is the form used on the subtype of primes outside an exposed
root support. -/
theorem subsetEventMass_missingPetalAlong_le_of_window
    {α : Type*} [DecidableEq α]
    (P : Finset α) (n : α → ℕ) (u : α → ℝ)
    (eligible : α → Prop) [DecidablePred eligible]
    (a b L : ℝ)
    (hnpos : ∀ p ∈ P, 0 < n p)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong P n u eligible x (b - a) ≤ L) :
    subsetEventMass P
        (fun p => missingPetalParameter (n p))
        (SelectedIntervalEvent eligible u a b) ≤ L := by
  apply subsetEventMass_selectedInterval_le
    P (fun p => missingPetalParameter (n p))
      u eligible a b L
  · intro p _hp
    exact missingPetalParameter_nonneg (n p)
  · intro p hp
    exact missingPetalParameter_lt_one (hnpos p hp)
  · intro A hA
    let x : ℝ := a - selectedWeightSum u A
    calc
      (∑ p ∈ P \ A,
          if eligible p ∧
              a ≤ u p + selectedWeightSum u A ∧
              u p + selectedWeightSum u A ≤ b
          then missingPetalParameter (n p) /
            (1 - missingPetalParameter (n p)) else 0) ≤
        ∑ p ∈ P \ A,
          if eligible p ∧
              a ≤ u p + selectedWeightSum u A ∧
              u p + selectedWeightSum u A ≤ b
          then 1 / (n p : ℝ) else 0 := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs
        · exact missingPetal_odds_le_reciprocal
            (hnpos p (Finset.mem_sdiff.mp hp).1)
        · exact le_rfl
      _ = ∑ p ∈ P \ A,
          if eligible p ∧ x ≤ u p ∧ u p ≤ x + (b - a)
          then 1 / (n p : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p _hp
        congr 1
        apply propext
        dsimp [x]
        constructor <;> rintro ⟨heligible, hlower, hupper⟩
        · exact ⟨heligible, by linarith, by linarith⟩
        · exact ⟨heligible, by linarith, by linarith⟩
      _ ≤ ∑ p ∈ P,
          if eligible p ∧ x ≤ u p ∧ u p ≤ x + (b - a)
          then 1 / (n p : ℝ) else 0 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          Finset.sdiff_subset
        intro p _hp _hpDiff
        split_ifs
        · exact div_nonneg zero_le_one (Nat.cast_nonneg (n p))
        · exact le_rfl
      _ = reciprocalWindowMassAlong
          P n u eligible x (b - a) := by
        unfold reciprocalWindowMassAlong
        apply Finset.sum_congr rfl
        intro p _hp
        by_cases h :
            eligible p ∧ x ≤ u p ∧ u p ≤ x + (b - a) <;>
          simp [h]
      _ ≤ L := hwindow x

theorem subsetEventMass_nonneg
    {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ) (E : Finset α → Prop)
    (hq0 : ∀ p ∈ P, 0 ≤ q p)
    (hq1 : ∀ p ∈ P, q p ≤ 1) :
    0 ≤ subsetEventMass P q E := by
  classical
  rw [subsetEventMass]
  apply Finset.sum_nonneg
  intro S hS
  split_ifs
  · exact subsetWeight_nonneg hq0 hq1
      (Finset.mem_powerset.mp hS)
  · exact le_rfl

/-- Two independent missing-petal completions multiply the one-copy
small-ball estimate. -/
theorem sq_subsetEventMass_missingPetal_le
    (P : Finset ℕ) (u : ℕ → ℝ)
    (eligible : ℕ → Prop) [DecidablePred eligible]
    (a b L : ℝ)
    (hPpos : ∀ p ∈ P, 0 < p)
    (hL : 0 ≤ L)
    (hlocal : ∀ A ∈ P.powerset,
      (∑ p ∈ P \ A,
        if eligible p ∧
            a ≤ u p + selectedWeightSum u A ∧
            u p + selectedWeightSum u A ≤ b
        then 1 / (p : ℝ) else 0) ≤ L) :
    (subsetEventMass P missingPetalParameter
        (SelectedIntervalEvent eligible u a b)) ^ 2 ≤ L ^ 2 := by
  have hmass :
      subsetEventMass P missingPetalParameter
          (SelectedIntervalEvent eligible u a b) ≤ L :=
    subsetEventMass_missingPetal_le
      P u eligible a b L hPpos hlocal
  have hnonneg :
      0 ≤ subsetEventMass P missingPetalParameter
        (SelectedIntervalEvent eligible u a b) :=
    subsetEventMass_nonneg P missingPetalParameter
      (SelectedIntervalEvent eligible u a b)
      (fun p _hp => missingPetalParameter_nonneg p)
      (fun p hp =>
        (missingPetalParameter_lt_one (hPpos p hp)).le)
  exact (sq_le_sq₀ hnonneg hL).2 hmass

theorem subsetEventMass_mono
    {α : Type*} [DecidableEq α]
    (P : Finset α) (q : α → ℝ)
    (E F : Finset α → Prop)
    (hq0 : ∀ p ∈ P, 0 ≤ q p)
    (hq1 : ∀ p ∈ P, q p ≤ 1)
    (hEF : ∀ S ∈ P.powerset, E S → F S) :
    subsetEventMass P q E ≤ subsetEventMass P q F := by
  classical
  unfold subsetEventMass
  apply Finset.sum_le_sum
  intro S hS
  by_cases hE : E S
  · rw [if_pos hE, if_pos (hEF S hS hE)]
  · rw [if_neg hE]
    split_ifs
    · exact subsetWeight_nonneg hq0 hq1
        (Finset.mem_powerset.mp hS)
    · exact le_rfl

/-! ## What the actual prime-band event forces on the exposed root -/

/-- The three active labels visible in the support represented by state
`s`: the common label and the two petals other than `s`. -/
def representedActiveLabels (s : Fin 3) : Finset ActiveFiveLabel :=
  Finset.univ.erase (some s)

@[simp]
theorem card_representedActiveLabels (s : Fin 3) :
    (representedActiveLabels s).card = 3 := by
  simp [representedActiveLabels]

theorem activeFiveLabel_injective :
    Function.Injective activeFiveLabel := by
  intro l m
  fin_cases l <;> fin_cases m <;>
    simp [activeFiveLabel, petalLabel]

/-- A five-state label is visible in represented state `s` exactly when it
is one of the represented active labels. -/
theorem fiveLabelIncluded_iff_exists_representedActiveLabel
    (s : Fin 3) (l : FiveLabel) :
    fiveLabelIncluded s l ↔
      ∃ a ∈ representedActiveLabels s, l = activeFiveLabel a := by
  fin_cases s <;> fin_cases l <;> decide

/-- The depth prefix of the represented root support. -/
noncomputable def fiveStateDepthPrefix
    (R : Finset ℕ) (T : ℝ) (s : Fin 3)
    (c : FiveConfiguration R) (d : ℝ) : Finset ↥R :=
  Finset.univ.filter fun p =>
    fiveLabelIncluded s (c p) ∧ normalizedLogDepth T p.1 ≤ d

@[simp]
theorem mem_fiveStateDepthPrefix
    {R : Finset ℕ} {T d : ℝ} {s : Fin 3}
    {c : FiveConfiguration R} {p : ↥R} :
    p ∈ fiveStateDepthPrefix R T s c d ↔
      fiveLabelIncluded s (c p) ∧
        normalizedLogDepth T p.1 ≤ d := by
  simp [fiveStateDepthPrefix]

/-- The represented root prefix is the disjoint union of the three visible
active-label prefixes. -/
theorem fiveStateDepthPrefix_eq_biUnion
    (R : Finset ℕ) (T : ℝ) (s : Fin 3)
    (c : FiveConfiguration R) (d : ℝ) :
    fiveStateDepthPrefix R T s c d =
      (representedActiveLabels s).biUnion
        fun l => fiveLabelDepthPrefix R T c l d := by
  ext p
  constructor
  · intro hp
    have hroot := mem_fiveStateDepthPrefix.mp hp
    obtain ⟨l, hl, hlabel⟩ :=
      (fiveLabelIncluded_iff_exists_representedActiveLabel
        s (c p)).mp hroot.1
    apply Finset.mem_biUnion.mpr
    refine ⟨l, hl, ?_⟩
    exact mem_fiveLabelDepthPrefix.mpr
      ⟨hlabel, hroot.2⟩
  · intro hp
    obtain ⟨l, hl, hpPrefix⟩ :=
      Finset.mem_biUnion.mp hp
    have hpData := mem_fiveLabelDepthPrefix.mp hpPrefix
    apply mem_fiveStateDepthPrefix.mpr
    refine ⟨?_, hpData.2⟩
    apply
      (fiveLabelIncluded_iff_exists_representedActiveLabel
        s (c p)).mpr
    exact ⟨l, hl, hpData.1⟩

theorem fiveLabelDepthPrefix_disjoint
    {R : Finset ℕ} {T d : ℝ} {c : FiveConfiguration R}
    {l m : ActiveFiveLabel} (hlm : l ≠ m) :
    Disjoint (fiveLabelDepthPrefix R T c l d)
      (fiveLabelDepthPrefix R T c m d) := by
  rw [Finset.disjoint_left]
  intro p hpL hpM
  have hL := (mem_fiveLabelDepthPrefix.mp hpL).1
  have hM := (mem_fiveLabelDepthPrefix.mp hpM).1
  exact hlm (activeFiveLabel_injective (hL.symm.trans hM))

/-- Every accepted configuration gives the exposed root the combined
prefix profile of its three visible active labels. -/
theorem fivePrimeBandEvent_rootPrefix
    {R : Finset ℕ} {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {c : FiveConfiguration R}
    (hc : fivePrimeBandEvent
      R T lower upper w depths threshold c)
    (s : Fin 3) {d : ℝ} (hd : d ∈ depths) :
    3 * threshold d ≤
      (fiveStateDepthPrefix R T s c d).card := by
  have hdisjoint :
      Set.PairwiseDisjoint
        (↑(representedActiveLabels s) : Set ActiveFiveLabel)
        (fun l => fiveLabelDepthPrefix R T c l d) := by
    intro l _hl m _hm hlm
    exact fiveLabelDepthPrefix_disjoint hlm
  have hsum :
      (∑ l ∈ representedActiveLabels s, threshold d) ≤
        ∑ l ∈ representedActiveLabels s,
          (fiveLabelDepthPrefix R T c l d).card := by
    apply Finset.sum_le_sum
    intro l hl
    exact fivePrimeBandEvent_prefix hc l hd
  rw [← Finset.card_biUnion hdisjoint,
    ← fiveStateDepthPrefix_eq_biUnion] at hsum
  simpa [card_representedActiveLabels, mul_comm] using hsum

/-! ## A finite root-fiber multiplication principle -/

/-- Weighted mass of a predicate on a finite type. -/
def finiteWeightedMass
    {X : Type*} [Fintype X] (k : X → ℝ) (E : X → Prop) : ℝ := by
  classical
  exact ∑ x : X, if E x then k x else 0

/-- Weighted mass in one fiber of a finite observation. -/
def finiteFiberMass
    {X O : Type*} [Fintype X] [DecidableEq O]
    (k : X → ℝ) (obs : X → O) (o : O)
    (E : X → Prop) : ℝ := by
  classical
  exact ∑ x : X, if obs x = o ∧ E x then k x else 0

theorem finiteWeightedMass_eq_sum_fiber
    {X O : Type*} [Fintype X] [Fintype O] [DecidableEq O]
    (k : X → ℝ) (obs : X → O) (E : X → Prop) :
    finiteWeightedMass k E =
      ∑ o : O, finiteFiberMass k obs o E := by
  classical
  unfold finiteWeightedMass finiteFiberMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hE : E x
  · simp [hE]
  · simp [hE]

/-- If the full event is contained in a root-good event and a missing-part
event, and the latter contracts every root fiber by `m`, then a root-good
mass bound `r` gives the product bound `m*r`. -/
theorem finiteFiberEventMass_le_mul
    {X O : Type*} [Fintype X] [Fintype O] [DecidableEq O]
    (k : X → ℝ) (obs : X → O)
    (event missingGood : X → Prop) (rootGood : O → Prop)
    [DecidablePred rootGood]
    (m r : ℝ)
    (hk : ∀ x, 0 ≤ k x)
    (hm : 0 ≤ m)
    (hevent : ∀ x, event x →
      rootGood (obs x) ∧ missingGood x)
    (hfiber : ∀ o : O,
      finiteFiberMass k obs o missingGood ≤
        m * finiteFiberMass k obs o (fun _ => True))
    (hroot :
      (∑ o : O,
        if rootGood o
        then finiteFiberMass k obs o (fun _ => True)
        else 0) ≤ r) :
    finiteWeightedMass k event ≤ m * r := by
  classical
  have heventFiber (o : O) :
      finiteFiberMass k obs o event ≤
        if rootGood o
        then finiteFiberMass k obs o missingGood
        else 0 := by
    unfold finiteFiberMass
    by_cases hgood : rootGood o
    · rw [if_pos hgood]
      apply Finset.sum_le_sum
      intro x _hx
      by_cases hx : obs x = o ∧ event x
      · rw [if_pos hx]
        have hmissing := (hevent x hx.2).2
        rw [if_pos ⟨hx.1, hmissing⟩]
      · rw [if_neg hx]
        split_ifs
        · exact hk x
        · exact le_rfl
    · rw [if_neg hgood]
      apply Finset.sum_nonpos
      intro x _hx
      by_cases hx : obs x = o ∧ event x
      · have hrootX := (hevent x hx.2).1
        exact False.elim (hgood (hx.1 ▸ hrootX))
      · rw [if_neg hx]
  calc
    finiteWeightedMass k event =
        ∑ o : O, finiteFiberMass k obs o event :=
      finiteWeightedMass_eq_sum_fiber k obs event
    _ ≤ ∑ o : O,
        if rootGood o
        then finiteFiberMass k obs o missingGood
        else 0 :=
      Finset.sum_le_sum fun o _ho => heventFiber o
    _ ≤ ∑ o : O,
        if rootGood o
        then m * finiteFiberMass k obs o (fun _ => True)
        else 0 := by
      apply Finset.sum_le_sum
      intro o _ho
      by_cases hgood : rootGood o
      · simp only [hgood, if_true]
        exact hfiber o
      · simp [hgood]
    _ = m * ∑ o : O,
        if rootGood o
        then finiteFiberMass k obs o (fun _ => True)
        else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro o _ho
      by_cases hgood : rootGood o <;> simp [hgood]
    _ ≤ m * r := mul_le_mul_of_nonneg_left hroot hm

/-! ## Exact two-completion expansion of the rooted collision -/

/-- The collision mass expanded as two configurations sharing an explicitly
summed represented support. -/
noncomputable def fiveRootPairMass
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3) : ℝ :=
  ∑ S : Finset ↥P,
    ∑ c : FiveConfiguration P,
      ∑ d : FiveConfiguration P,
        (if B c ∧ fiveStateSupport P s c = S
          then fiveConfigurationWeight P r c else 0) *
        (if B d ∧ fiveStateSupport P s d = S
          then fiveConfigurationWeight P r d else 0) /
        subtypeBernoulliWeight P r S

/-- The rooted collision is exactly the annealed mass of two completions
sharing their represented support. -/
theorem fiveRootPairMass_eq_collision
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3) :
    fiveRootPairMass P r B s = fiveRootCollision P r B s := by
  classical
  rw [fiveRootPairMass, fiveRootCollision]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [fiveEventSupportMass, pow_two, Finset.sum_mul_sum]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [Finset.sum_div]

/-! ## The exposed-root observation for the actual five-state pair -/

/-- A support together with two completions. -/
abbrev FiveRootPairSample
    {α : Type*} [DecidableEq α] (P : Finset α) :=
  Finset ↥P × FiveConfiguration P × FiveConfiguration P

/-- The atomic annealed pair weight. -/
noncomputable def fiveRootPairAtom
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (s : Fin 3)
    (x : FiveRootPairSample P) : ℝ :=
  if fiveStateSupport P s x.2.1 = x.1 ∧
      fiveStateSupport P s x.2.2 = x.1
  then
    fiveConfigurationWeight P r x.2.1 *
      fiveConfigurationWeight P r x.2.2 /
      subtypeBernoulliWeight P r x.1
  else 0

theorem fiveConfigurationWeight_nonneg
    {α : Type*} [DecidableEq α]
    {P : Finset α} {r : α → ℝ}
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hr34 : ∀ p ∈ P, r p ≤ 3 / 4)
    (c : FiveConfiguration P) :
    0 ≤ fiveConfigurationWeight P r c := by
  rw [fiveConfigurationWeight]
  apply Finset.prod_nonneg
  intro p _hp
  exact fiveLabelWeight_nonneg
    (hr0 p.1 p.2) (hr34 p.1 p.2) (c p)

theorem fiveRootPairAtom_nonneg
    {α : Type*} [DecidableEq α]
    {P : Finset α} {r : α → ℝ} {s : Fin 3}
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hr34 : ∀ p ∈ P, r p ≤ 3 / 4)
    (hrpos : ∀ p ∈ P, 0 < r p)
    (hr1 : ∀ p ∈ P, r p < 1)
    (x : FiveRootPairSample P) :
    0 ≤ fiveRootPairAtom P r s x := by
  rw [fiveRootPairAtom]
  split_ifs
  · exact div_nonneg
      (mul_nonneg
        (fiveConfigurationWeight_nonneg hr0 hr34 x.2.1)
        (fiveConfigurationWeight_nonneg hr0 hr34 x.2.2))
      (subtypeBernoulliWeight_pos hrpos hr1 x.1).le
  · exact le_rfl

/-- The actual rooted collision is the weighted mass of two accepted
completions in the explicit pair sample space. -/
theorem finiteWeightedMass_pairEvent_eq_collision
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3) :
    finiteWeightedMass (fiveRootPairAtom P r s)
        (fun x : FiveRootPairSample P => B x.2.1 ∧ B x.2.2) =
      fiveRootCollision P r B s := by
  classical
  rw [← fiveRootPairMass_eq_collision P r B s]
  unfold finiteWeightedMass fiveRootPairMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _hc
  apply Finset.sum_congr rfl
  intro d _hd
  rw [fiveRootPairAtom]
  by_cases hBc : B c
  · by_cases hBd : B d
    · by_cases hcS : fiveStateSupport P s c = S
      · by_cases hdS : fiveStateSupport P s d = S
        · simp [hBc, hBd, hcS, hdS]
        · simp [hBc, hBd, hcS, hdS]
      · simp [hBc, hcS]
    · simp [hBd]
  · simp [hBc]

/-- Remove everything outside the represented root, retaining the visible
root label at every represented prime. -/
def rootPartLabel (s : Fin 3) (l : FiveLabel) : FiveLabel :=
  if fiveLabelIncluded s l then l else 0

def fiveRootPart
    {α : Type*} [DecidableEq α] (P : Finset α) (s : Fin 3)
    (c : FiveConfiguration P) : FiveConfiguration P :=
  fun p => rootPartLabel s (c p)

@[simp]
theorem fiveLabelIncluded_zero (s : Fin 3) :
    ¬fiveLabelIncluded s (0 : FiveLabel) := by
  fin_cases s <;> decide

@[simp]
theorem fiveLabelIncluded_rootPartLabel
    (s : Fin 3) (l : FiveLabel) :
    fiveLabelIncluded s (rootPartLabel s l) ↔
      fiveLabelIncluded s l := by
  by_cases h : fiveLabelIncluded s l
  · simp [rootPartLabel, h]
  · simp [rootPartLabel, h]

theorem fiveStateSupport_rootPart
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3) (c : FiveConfiguration P) :
    fiveStateSupport P s (fiveRootPart P s c) =
      fiveStateSupport P s c := by
  ext p
  simp [mem_fiveStateSupport, fiveRootPart]

@[simp]
theorem rootPartLabel_idempotent
    (s : Fin 3) (l : FiveLabel) :
    rootPartLabel s (rootPartLabel s l) = rootPartLabel s l := by
  by_cases h : fiveLabelIncluded s l <;>
    simp [rootPartLabel, h]

@[simp]
theorem fiveRootPart_idempotent
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3) (c : FiveConfiguration P) :
    fiveRootPart P s (fiveRootPart P s c) =
      fiveRootPart P s c := by
  funext p
  exact rootPartLabel_idempotent s (c p)

theorem fiveStateDepthPrefix_rootPart
    (R : Finset ℕ) (T : ℝ) (s : Fin 3)
    (c : FiveConfiguration R) (d : ℝ) :
    fiveStateDepthPrefix R T s (fiveRootPart R s c) d =
      fiveStateDepthPrefix R T s c d := by
  ext p
  simp [mem_fiveStateDepthPrefix, fiveRootPart]

theorem fiveLabelDepthPrefix_rootPart_of_represented
    (R : Finset ℕ) (T : ℝ) (s : Fin 3)
    (c : FiveConfiguration R)
    {l : ActiveFiveLabel}
    (hl : l ∈ representedActiveLabels s)
    (d : ℝ) :
    fiveLabelDepthPrefix R T (fiveRootPart R s c) l d =
      fiveLabelDepthPrefix R T c l d := by
  ext p
  simp only [mem_fiveLabelDepthPrefix, fiveRootPart]
  have hincluded :
      fiveLabelIncluded s (activeFiveLabel l) := by
    exact
      (fiveLabelIncluded_iff_exists_representedActiveLabel
        s (activeFiveLabel l)).mpr
      ⟨l, hl, rfl⟩
  constructor
  · rintro ⟨hp, hdepth⟩
    refine ⟨?_, hdepth⟩
    rw [rootPartLabel] at hp
    split at hp
    · exact hp
    · have hzero : (0 : FiveLabel) ≠ activeFiveLabel l := by
        cases l with
        | none => decide
        | some t =>
            fin_cases t <;> decide
      exact False.elim (hzero hp)
  · rintro ⟨hp, hdepth⟩
    refine ⟨?_, hdepth⟩
    rw [rootPartLabel, if_pos]
    · exact hp
    · simpa [hp] using hincluded

theorem fiveLabelPrefixCount_rootPart_of_represented
    (R : Finset ℕ) (T : ℝ) (s : Fin 3)
    (c : FiveConfiguration R)
    {l : ActiveFiveLabel}
    (hl : l ∈ representedActiveLabels s)
    (d : ℝ) :
    fiveLabelPrefixCount R T (fiveRootPart R s c) l d =
      fiveLabelPrefixCount R T c l d := by
  unfold fiveLabelPrefixCount
  rw [fiveLabelDepthPrefix_rootPart_of_represented
    R T s c hl d]

theorem fiveLabelIncluded_petal_iff
    (s t : Fin 3) :
    fiveLabelIncluded s (petalLabel t) ↔ t ≠ s := by
  fin_cases s <;> fin_cases t <;>
    decide

theorem fivePetalNormalizedTotal_rootPart
    (R : Finset ℕ) (T : ℝ) (s t : Fin 3)
    (c : FiveConfiguration R) (hts : t ≠ s) :
    fivePetalNormalizedTotal R T (fiveRootPart R s c) t =
      fivePetalNormalizedTotal R T c t := by
  rw [fivePetalNormalizedTotal, fivePetalNormalizedTotal,
    fiveActiveLabelNormalizedTotal,
    fiveActiveLabelNormalizedTotal]
  congr 1
  ext p
  simp only [fiveActiveLabelSubtype, Finset.mem_filter,
    Finset.mem_univ, true_and, fiveRootPart]
  have hincluded :
      fiveLabelIncluded s (petalLabel t) :=
    (fiveLabelIncluded_petal_iff s t).mpr hts
  constructor
  · intro hp
    rw [rootPartLabel] at hp
    split at hp
    · exact hp
    · have hzero : (0 : FiveLabel) ≠ petalLabel t := by
        fin_cases t <;> decide
      exact False.elim (hzero hp)
  · intro hp
    rw [rootPartLabel, if_pos]
    · exact hp
    · simpa [hp, activeFiveLabel] using hincluded

/-- A canonical petal different from `s`. -/
def otherPetal (s : Fin 3) : Fin 3 :=
  ⟨(s.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩

theorem otherPetal_ne (s : Fin 3) :
    otherPetal s ≠ s := by
  fin_cases s <;> decide

/-- The second petal different from `s`. -/
def secondOtherPetal (s : Fin 3) : Fin 3 :=
  ⟨(s.1 + 2) % 3, Nat.mod_lt _ (by decide)⟩

theorem secondOtherPetal_ne (s : Fin 3) :
    secondOtherPetal s ≠ s := by
  fin_cases s <;> decide

theorem secondOtherPetal_ne_otherPetal (s : Fin 3) :
    secondOtherPetal s ≠ otherPetal s := by
  fin_cases s <;> decide

/-- Encode the three visible root labels as `-1,0,1`: the two visible
petals receive the signs and the common label receives zero. -/
def visibleLabelOfDigit (s : Fin 3) (a : SignedDigit) : FiveLabel :=
  if a = 0 then petalLabel (secondOtherPetal s)
  else if a = 1 then 1
  else petalLabel (otherPetal s)

def visibleDigitOfLabel (s : Fin 3) (l : FiveLabel) : SignedDigit :=
  if l = petalLabel (secondOtherPetal s) then 0
  else if l = 1 then 1 else 2

@[simp]
theorem visibleLabelOfDigit_included
    (s : Fin 3) (a : SignedDigit) :
    fiveLabelIncluded s (visibleLabelOfDigit s a) := by
  fin_cases s <;> fin_cases a <;>
    decide

@[simp]
theorem visibleDigitOfLabel_visibleLabelOfDigit
    (s : Fin 3) (a : SignedDigit) :
    visibleDigitOfLabel s (visibleLabelOfDigit s a) = a := by
  fin_cases s <;> fin_cases a <;>
    decide

theorem visibleLabelOfDigit_visibleDigitOfLabel
    (s : Fin 3) (l : FiveLabel)
    (hl : fiveLabelIncluded s l) :
    visibleLabelOfDigit s (visibleDigitOfLabel s l) = l := by
  fin_cases s <;> fin_cases l <;>
    simp_all [visibleLabelOfDigit, visibleDigitOfLabel,
      fiveLabelIncluded, petalLabel, otherPetal,
      secondOtherPetal]

/-- The finite observation that exposes the common support and both root
colourings, but hides the two missing-petal processes. -/
abbrev FiveRootObservation
    {α : Type*} [DecidableEq α] (P : Finset α) :=
  Finset ↥P × FiveConfiguration P × FiveConfiguration P

def fiveRootObservation
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3)
    (x : FiveRootPairSample P) : FiveRootObservation P :=
  (x.1, fiveRootPart P s x.2.1, fiveRootPart P s x.2.2)

/-- The subset assigned to the petal omitted by represented state `s`. -/
def missingPetalSupport
    {α : Type*} [DecidableEq α] (P : Finset α) (s : Fin 3)
    (c : FiveConfiguration P) : Finset ↥P :=
  Finset.univ.filter fun p => c p = petalLabel s

/-- Reconstruct a completion from its masked root and its missing petal. -/
def reconstructRootCompletion
    {α : Type*} [DecidableEq α] (P : Finset α) (s : Fin 3)
    (root : FiveConfiguration P) (M : Finset ↥P) :
    FiveConfiguration P :=
  fun p => if p ∈ M then petalLabel s else root p

theorem rootPartLabel_eq_self_iff (s : Fin 3) (l : FiveLabel) :
    rootPartLabel s l = l ↔ l ≠ petalLabel s := by
  fin_cases s <;> fin_cases l <;> decide

@[simp]
theorem rootPartLabel_petal (s : Fin 3) :
    rootPartLabel s (petalLabel s) = 0 := by
  fin_cases s <;> decide

theorem reconstruct_missingPetalSupport
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3) (c : FiveConfiguration P) :
    reconstructRootCompletion P s (fiveRootPart P s c)
        (missingPetalSupport P s c) = c := by
  funext p
  by_cases hp : c p = petalLabel s
  · simp [reconstructRootCompletion, missingPetalSupport, hp]
  · simp [reconstructRootCompletion, missingPetalSupport,
      fiveRootPart, rootPartLabel_eq_self_iff, hp]

theorem missingPetalSupport_subset_complement
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3) (c : FiveConfiguration P) :
    missingPetalSupport P s c ⊆
      Finset.univ \ fiveStateSupport P s c := by
  intro p hp
  have hpMissing :
      c p = petalLabel s := by
    simpa [missingPetalSupport] using hp
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_univ p, ?_⟩
  rw [mem_fiveStateSupport]
  simpa [hpMissing] using
    (fiveLabelIncluded_petal_iff s s).not.mpr
      (not_ne_iff.mpr rfl)

/-- A masked root together with its represented support is internally
consistent. -/
def IsValidExposedRoot
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3)
    (S : Finset ↥P) (root : FiveConfiguration P) : Prop :=
  fiveRootPart P s root = root ∧
    fiveStateSupport P s root = S

theorem isValidExposedRoot_of_fiber
    {α : Type*} [DecidableEq α]
    {P : Finset α} {s : Fin 3}
    {S : Finset ↥P} {root c : FiveConfiguration P}
    (hroot : fiveRootPart P s c = root)
    (hsupport : fiveStateSupport P s c = S) :
    IsValidExposedRoot P s S root := by
  constructor
  · rw [← hroot]
    exact fiveRootPart_idempotent P s c
  · rw [← hroot, fiveStateSupport_rootPart, hsupport]

theorem validExposedRoot_zero_outside
    {α : Type*} [DecidableEq α]
    {P : Finset α} {s : Fin 3}
    {S : Finset ↥P} {root : FiveConfiguration P}
    (hvalid : IsValidExposedRoot P s S root)
    {p : ↥P} (hp : p ∉ S) :
    root p = 0 := by
  have hpNotSupport : p ∉ fiveStateSupport P s root := by
    simpa [hvalid.2] using hp
  have hpExcluded : ¬fiveLabelIncluded s (root p) := by
    simpa [mem_fiveStateSupport] using hpNotSupport
  have hfix := congrFun hvalid.1 p
  rw [fiveRootPart, rootPartLabel, if_neg hpExcluded] at hfix
  exact hfix.symm

theorem validExposedRoot_ne_missing
    {α : Type*} [DecidableEq α]
    {P : Finset α} {s : Fin 3}
    {S : Finset ↥P} {root : FiveConfiguration P}
    (hvalid : IsValidExposedRoot P s S root)
    (p : ↥P) :
    root p ≠ petalLabel s := by
  have hfix := congrFun hvalid.1 p
  rw [fiveRootPart, rootPartLabel_eq_self_iff] at hfix
  exact hfix

/-- One nine-mark at every point of a represented support. -/
abbrev SupportNineMarking
    {α : Type*} [DecidableEq α] {P : Finset α}
    (S : Finset ↥P) :=
  ↥S → NineMark

/-- Splitting off one newly inserted point also splits its nine-mark off
the support marking.  This is the finite reindexing used inside annealed
factorial insertion. -/
noncomputable def supportMarkingInsertEquiv
    {α : Type*} [DecidableEq α] {P : Finset α}
    {A : Finset ↥P} {p : ↥P} (hpA : p ∉ A) :
    SupportNineMarking (insert p A) ≃
      NineMark × SupportNineMarking A :=
  ((Finset.subtypeInsertEquivOption hpA).arrowCongr
      (Equiv.refl NineMark)).trans Equiv.piOptionEquivProd

@[simp]
theorem supportMarkingInsertEquiv_fst
    {α : Type*} [DecidableEq α] {P : Finset α}
    {A : Finset ↥P} {p : ↥P} (hpA : p ∉ A)
    (m : SupportNineMarking (insert p A)) :
    (supportMarkingInsertEquiv hpA m).1 =
      m ⟨p, mem_insert_self p A⟩ := by
  rfl

@[simp]
theorem supportMarkingInsertEquiv_snd
    {α : Type*} [DecidableEq α] {P : Finset α}
    {A : Finset ↥P} {p : ↥P} (hpA : p ∉ A)
    (m : SupportNineMarking (insert p A))
    (a : ↥A) :
    (supportMarkingInsertEquiv hpA m).2 a =
      m ⟨a.1, mem_insert_of_mem a.2⟩ := by
  rfl

@[simp]
theorem supportMarkingInsertEquiv_symm_head
    {α : Type*} [DecidableEq α] {P : Finset α}
    {A : Finset ↥P} {p : ↥P} (hpA : p ∉ A)
    (v : NineMark) (m : SupportNineMarking A) :
    (supportMarkingInsertEquiv hpA).symm (v, m)
        ⟨p, mem_insert_self p A⟩ = v := by
  have h :=
    supportMarkingInsertEquiv_fst hpA
      ((supportMarkingInsertEquiv hpA).symm (v, m))
  simpa using h.symm

@[simp]
theorem supportMarkingInsertEquiv_symm_tail
    {α : Type*} [DecidableEq α] {P : Finset α}
    {A : Finset ↥P} {p : ↥P} (hpA : p ∉ A)
    (v : NineMark) (m : SupportNineMarking A)
    (a : ↥A) :
    (supportMarkingInsertEquiv hpA).symm (v, m)
        ⟨a.1, mem_insert_of_mem a.2⟩ = m a := by
  have h :=
    congrFun
      (congrArg Prod.snd
        ((supportMarkingInsertEquiv hpA).apply_symm_apply (v, m))) a
  exact h

def supportMarkRootFirst
    {α : Type*} [DecidableEq α] {P : Finset α}
    (s : Fin 3) (S : Finset ↥P)
    (m : SupportNineMarking S) :
    FiveConfiguration P :=
  fun p =>
    if hp : p ∈ S
    then visibleLabelOfDigit s (m ⟨p, hp⟩).1
    else 0

def supportMarkRootSecond
    {α : Type*} [DecidableEq α] {P : Finset α}
    (s : Fin 3) (S : Finset ↥P)
    (m : SupportNineMarking S) :
    FiveConfiguration P :=
  fun p =>
    if hp : p ∈ S
    then visibleLabelOfDigit s (m ⟨p, hp⟩).2
    else 0

theorem supportMarkRootFirst_valid
    {α : Type*} [DecidableEq α] {P : Finset α}
    (s : Fin 3) (S : Finset ↥P)
    (m : SupportNineMarking S) :
    IsValidExposedRoot P s S
      (supportMarkRootFirst s S m) := by
  constructor
  · funext p
    by_cases hp : p ∈ S
    · simp [fiveRootPart, supportMarkRootFirst,
        rootPartLabel, hp]
    · simp [fiveRootPart, supportMarkRootFirst,
        rootPartLabel, hp]
  · ext p
    by_cases hp : p ∈ S
    · simp [fiveStateSupport, supportMarkRootFirst, hp]
    · simp [fiveStateSupport, supportMarkRootFirst, hp]

theorem supportMarkRootSecond_valid
    {α : Type*} [DecidableEq α] {P : Finset α}
    (s : Fin 3) (S : Finset ↥P)
    (m : SupportNineMarking S) :
    IsValidExposedRoot P s S
      (supportMarkRootSecond s S m) := by
  constructor
  · funext p
    by_cases hp : p ∈ S
    · simp [fiveRootPart, supportMarkRootSecond,
        rootPartLabel, hp]
    · simp [fiveRootPart, supportMarkRootSecond,
        rootPartLabel, hp]
  · ext p
    by_cases hp : p ∈ S
    · simp [fiveStateSupport, supportMarkRootSecond, hp]
    · simp [fiveStateSupport, supportMarkRootSecond, hp]

abbrev ValidExposedRootPair
    {α : Type*} [DecidableEq α] (P : Finset α)
    (s : Fin 3) (S : Finset ↥P) :=
  {roots : FiveConfiguration P × FiveConfiguration P //
    IsValidExposedRoot P s S roots.1 ∧
      IsValidExposedRoot P s S roots.2}

/-- Exact identification of a pair of exposed three-colour roots with
one nine-mark at each represented support point. -/
noncomputable def validExposedRootPairEquivSupportNineMarking
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3) (S : Finset ↥P) :
    ValidExposedRootPair P s S ≃ SupportNineMarking S where
  toFun roots := fun p =>
    (visibleDigitOfLabel s (roots.1.1 p.1),
      visibleDigitOfLabel s (roots.1.2 p.1))
  invFun m :=
    ⟨(supportMarkRootFirst s S m,
        supportMarkRootSecond s S m),
      supportMarkRootFirst_valid s S m,
      supportMarkRootSecond_valid s S m⟩
  left_inv roots := by
    apply Subtype.ext
    apply Prod.ext
    · funext p
      by_cases hp : p ∈ S
      · have hpSupport :
            p ∈ fiveStateSupport P s roots.1.1 := by
          simpa only [roots.2.1.2] using hp
        have hpIncluded :
            fiveLabelIncluded s (roots.1.1 p) :=
          (mem_fiveStateSupport P s roots.1.1 p).mp
            hpSupport
        simp [supportMarkRootFirst, hp,
          visibleLabelOfDigit_visibleDigitOfLabel
            s (roots.1.1 p) hpIncluded]
      · have hpZero :=
          validExposedRoot_zero_outside roots.2.1 hp
        simp [supportMarkRootFirst, hp, hpZero]
    · funext p
      by_cases hp : p ∈ S
      · have hpSupport :
            p ∈ fiveStateSupport P s roots.1.2 := by
          simpa only [roots.2.2.2] using hp
        have hpIncluded :
            fiveLabelIncluded s (roots.1.2 p) :=
          (mem_fiveStateSupport P s roots.1.2 p).mp
            hpSupport
        simp [supportMarkRootSecond, hp,
          visibleLabelOfDigit_visibleDigitOfLabel
            s (roots.1.2 p) hpIncluded]
      · have hpZero :=
          validExposedRoot_zero_outside roots.2.2 hp
        simp [supportMarkRootSecond, hp, hpZero]
  right_inv m := by
    funext p
    apply Prod.ext <;>
      simp [supportMarkRootFirst, supportMarkRootSecond, p.2]

theorem card_validExposedRootPair
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3) (S : Finset ↥P) :
    Fintype.card (ValidExposedRootPair P s S) =
      9 ^ S.card := by
  rw [Fintype.card_congr
    (validExposedRootPairEquivSupportNineMarking P s S)]
  simp only [SupportNineMarking, Fintype.card_fun,
    Fintype.card_coe]
  norm_num

noncomputable def supportMarkFirstNormalizedSum
    (R : Finset ℕ) (T : ℝ)
    (S : Finset ↥R) (m : SupportNineMarking S) : ℝ :=
  ∑ p : ↥R,
    if hp : p ∈ S
    then signedDigitReal (m ⟨p, hp⟩).1 *
      normalizedLogWeight T p.1
    else 0

noncomputable def supportMarkSecondNormalizedSum
    (R : Finset ℕ) (T : ℝ)
    (S : Finset ↥R) (m : SupportNineMarking S) : ℝ :=
  ∑ p : ↥R,
    if hp : p ∈ S
    then signedDigitReal (m ⟨p, hp⟩).2 *
      normalizedLogWeight T p.1
    else 0

theorem supportMarkFirstNormalizedSum_insert
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A)
    (v : NineMark) (m : SupportNineMarking A) :
    supportMarkFirstNormalizedSum R T (insert p A)
        ((supportMarkingInsertEquiv hpA).symm (v, m)) =
      signedDigitReal v.1 * normalizedLogWeight T p.1 +
        supportMarkFirstNormalizedSum R T A m := by
  unfold supportMarkFirstNormalizedSum
  let base : ↥R → ℝ := fun a =>
    if ha : a ∈ A
    then signedDigitReal (m ⟨a, ha⟩).1 *
      normalizedLogWeight T a.1
    else 0
  have hpoint (a : ↥R) :
      (if ha : a ∈ insert p A
        then signedDigitReal
            ((supportMarkingInsertEquiv hpA).symm
              (v, m) ⟨a, ha⟩).1 *
            normalizedLogWeight T a.1
        else 0) =
      (if a = p
        then signedDigitReal v.1 *
          normalizedLogWeight T p.1
        else 0) + base a := by
    by_cases hap : a = p
    · subst a
      simp [base, hpA]
    · by_cases haA : a ∈ A
      · have htail :=
          supportMarkingInsertEquiv_symm_tail hpA v m
            ⟨a, haA⟩
        simp [base, hap, haA, htail]
      · simp [base, hap, haA]
  calc
    (∑ a : ↥R,
        if ha : a ∈ insert p A
        then signedDigitReal
            ((supportMarkingInsertEquiv hpA).symm
              (v, m) ⟨a, ha⟩).1 *
            normalizedLogWeight T a.1
        else 0) =
        ∑ a : ↥R,
          ((if a = p
            then signedDigitReal v.1 *
              normalizedLogWeight T p.1
            else 0) + base a) := by
      apply Fintype.sum_congr
      exact hpoint
    _ = (∑ a : ↥R,
          if a = p
          then signedDigitReal v.1 *
            normalizedLogWeight T p.1
          else 0) + ∑ a : ↥R, base a := by
      rw [Finset.sum_add_distrib]
    _ = signedDigitReal v.1 *
          normalizedLogWeight T p.1 +
        ∑ a : ↥R, base a := by
      rw [Fintype.sum_ite_eq' p]
    _ = signedDigitReal v.1 *
          normalizedLogWeight T p.1 +
        ∑ a : ↥R,
          if ha : a ∈ A
          then signedDigitReal (m ⟨a, ha⟩).1 *
            normalizedLogWeight T a.1
          else 0 := by
      rfl

theorem supportMarkSecondNormalizedSum_insert
    {R : Finset ℕ} {T : ℝ}
    {A : Finset ↥R} {p : ↥R} (hpA : p ∉ A)
    (v : NineMark) (m : SupportNineMarking A) :
    supportMarkSecondNormalizedSum R T (insert p A)
        ((supportMarkingInsertEquiv hpA).symm (v, m)) =
      signedDigitReal v.2 * normalizedLogWeight T p.1 +
        supportMarkSecondNormalizedSum R T A m := by
  unfold supportMarkSecondNormalizedSum
  let base : ↥R → ℝ := fun a =>
    if ha : a ∈ A
    then signedDigitReal (m ⟨a, ha⟩).2 *
      normalizedLogWeight T a.1
    else 0
  have hpoint (a : ↥R) :
      (if ha : a ∈ insert p A
        then signedDigitReal
            ((supportMarkingInsertEquiv hpA).symm
              (v, m) ⟨a, ha⟩).2 *
            normalizedLogWeight T a.1
        else 0) =
      (if a = p
        then signedDigitReal v.2 *
          normalizedLogWeight T p.1
        else 0) + base a := by
    by_cases hap : a = p
    · subst a
      simp [base, hpA]
    · by_cases haA : a ∈ A
      · have htail :=
          supportMarkingInsertEquiv_symm_tail hpA v m
            ⟨a, haA⟩
        simp [base, hap, haA, htail]
      · simp [base, hap, haA]
  calc
    (∑ a : ↥R,
        if ha : a ∈ insert p A
        then signedDigitReal
            ((supportMarkingInsertEquiv hpA).symm
              (v, m) ⟨a, ha⟩).2 *
            normalizedLogWeight T a.1
        else 0) =
        ∑ a : ↥R,
          ((if a = p
            then signedDigitReal v.2 *
              normalizedLogWeight T p.1
            else 0) + base a) := by
      apply Fintype.sum_congr
      exact hpoint
    _ = (∑ a : ↥R,
          if a = p
          then signedDigitReal v.2 *
            normalizedLogWeight T p.1
          else 0) + ∑ a : ↥R, base a := by
      rw [Finset.sum_add_distrib]
    _ = signedDigitReal v.2 *
          normalizedLogWeight T p.1 +
        ∑ a : ↥R, base a := by
      rw [Fintype.sum_ite_eq' p]
    _ = signedDigitReal v.2 *
          normalizedLogWeight T p.1 +
        ∑ a : ↥R,
          if ha : a ∈ A
          then signedDigitReal (m ⟨a, ha⟩).2 *
            normalizedLogWeight T a.1
          else 0 := by
      rfl

theorem supportMarkRootFirst_petalDifference
    (R : Finset ℕ) (T : ℝ) (s : Fin 3)
    (S : Finset ↥R) (m : SupportNineMarking S) :
    fivePetalNormalizedTotal R T
          (supportMarkRootFirst s S m) (otherPetal s) -
        fivePetalNormalizedTotal R T
          (supportMarkRootFirst s S m) (secondOtherPetal s) =
      supportMarkFirstNormalizedSum R T S m := by
  unfold fivePetalNormalizedTotal
    fiveActiveLabelNormalizedTotal
    fiveActiveLabelSubtype
    supportMarkFirstNormalizedSum
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpS : p ∈ S
  · generalize hmark : (m ⟨p, hpS⟩).1 = a
    fin_cases s <;> fin_cases a <;>
      simp [supportMarkRootFirst, hpS, hmark,
        visibleLabelOfDigit, otherPetal, secondOtherPetal,
        activeFiveLabel, petalLabel, signedDigitReal,
        signedDigitValue]
  · have hroot :
        supportMarkRootFirst s S m p = 0 := by
      simp [supportMarkRootFirst, hpS]
    rw [hroot]
    simp [hpS, activeFiveLabel, petalLabel]

theorem supportMarkRootSecond_petalDifference
    (R : Finset ℕ) (T : ℝ) (s : Fin 3)
    (S : Finset ↥R) (m : SupportNineMarking S) :
    fivePetalNormalizedTotal R T
          (supportMarkRootSecond s S m) (otherPetal s) -
        fivePetalNormalizedTotal R T
          (supportMarkRootSecond s S m) (secondOtherPetal s) =
      supportMarkSecondNormalizedSum R T S m := by
  unfold fivePetalNormalizedTotal
    fiveActiveLabelNormalizedTotal
    fiveActiveLabelSubtype
    supportMarkSecondNormalizedSum
  rw [Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases hpS : p ∈ S
  · generalize hmark : (m ⟨p, hpS⟩).2 = a
    fin_cases s <;> fin_cases a <;>
      simp [supportMarkRootSecond, hpS, hmark,
        visibleLabelOfDigit, otherPetal, secondOtherPetal,
        activeFiveLabel, petalLabel, signedDigitReal,
        signedDigitValue]
  · have hroot :
        supportMarkRootSecond s S m p = 0 := by
      simp [supportMarkRootSecond, hpS]
    rw [hroot]
    simp [hpS, activeFiveLabel, petalLabel]

def SupportMarkSmallBall
    (R : Finset ℕ) (T w : ℝ)
    (S : Finset ↥R) (m : SupportNineMarking S) : Prop :=
  |supportMarkFirstNormalizedSum R T S m| ≤ w ∧
    |supportMarkSecondNormalizedSum R T S m| ≤ w

theorem rootPart_reconstruct
    {α : Type*} [DecidableEq α]
    {P : Finset α} {s : Fin 3}
    {S : Finset ↥P} {root : FiveConfiguration P}
    (hvalid : IsValidExposedRoot P s S root)
    {M : Finset ↥P} (hM : M ⊆ Finset.univ \ S) :
    fiveRootPart P s (reconstructRootCompletion P s root M) =
      root := by
  funext p
  by_cases hpM : p ∈ M
  · have hpS : p ∉ S :=
      (Finset.mem_sdiff.mp (hM hpM)).2
    simp [fiveRootPart, reconstructRootCompletion, hpM,
      validExposedRoot_zero_outside hvalid hpS]
  · simp only [fiveRootPart, reconstructRootCompletion, hpM, if_false]
    simpa [fiveRootPart] using congrFun hvalid.1 p

theorem support_reconstruct
    {α : Type*} [DecidableEq α]
    {P : Finset α} {s : Fin 3}
    {S : Finset ↥P} {root : FiveConfiguration P}
    (hvalid : IsValidExposedRoot P s S root)
    {M : Finset ↥P} (hM : M ⊆ Finset.univ \ S) :
    fiveStateSupport P s (reconstructRootCompletion P s root M) = S := by
  rw [← fiveStateSupport_rootPart]
  rw [rootPart_reconstruct hvalid hM, hvalid.2]

theorem missingPetalSupport_reconstruct
    {α : Type*} [DecidableEq α]
    {P : Finset α} {s : Fin 3}
    {S : Finset ↥P} {root : FiveConfiguration P}
    (hvalid : IsValidExposedRoot P s S root)
    {M : Finset ↥P} (_hM : M ⊆ Finset.univ \ S) :
    missingPetalSupport P s
        (reconstructRootCompletion P s root M) = M := by
  ext p
  by_cases hpM : p ∈ M
  · simp [missingPetalSupport, reconstructRootCompletion, hpM]
  · simp [missingPetalSupport, reconstructRootCompletion, hpM,
      validExposedRoot_ne_missing hvalid p]

/-- Exact finite parametrization of a completion fiber by subsets of the
missing-petal complement. -/
noncomputable def completionFiberEquiv
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3)
    (S : Finset ↥P) (root : FiveConfiguration P)
    (hvalid : IsValidExposedRoot P s S root) :
    {c : FiveConfiguration P //
      fiveRootPart P s c = root ∧
        fiveStateSupport P s c = S} ≃
    {M : Finset ↥P // M ⊆ Finset.univ \ S} where
  toFun c :=
    ⟨missingPetalSupport P s c.1,
      by simpa [c.2.2] using
        missingPetalSupport_subset_complement P s c.1⟩
  invFun M :=
    ⟨reconstructRootCompletion P s root M.1,
      rootPart_reconstruct hvalid M.2,
      support_reconstruct hvalid M.2⟩
  left_inv c := by
    apply Subtype.ext
    change reconstructRootCompletion P s root
        (missingPetalSupport P s c.1) = c.1
    calc
      reconstructRootCompletion P s root
          (missingPetalSupport P s c.1) =
        reconstructRootCompletion P s (fiveRootPart P s c.1)
          (missingPetalSupport P s c.1) := by
            exact congrArg
              (fun r => reconstructRootCompletion P s r
                (missingPetalSupport P s c.1))
              c.2.1.symm
      _ = c.1 := reconstruct_missingPetalSupport P s c.1
  right_inv M := by
    apply Subtype.ext
    exact missingPetalSupport_reconstruct hvalid M.2

/-- The reconstructed missing-petal total is the scalar weight sum of the
missing subset. -/
theorem fivePetalNormalizedTotal_reconstruct_missing
    {R : Finset ℕ} {T : ℝ} {s : Fin 3}
    {S : Finset ↥R} {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root)
    {M : Finset ↥R} (hM : M ⊆ Finset.univ \ S) :
    fivePetalNormalizedTotal R T
        (reconstructRootCompletion R s root M) s =
      selectedWeightSum
        (fun p : ↥R => normalizedLogWeight T p.1) M := by
  rw [fivePetalNormalizedTotal,
    fiveActiveLabelNormalizedTotal,
    fiveActiveLabelSubtype_some]
  change
    (∑ p ∈ missingPetalSupport R s
      (reconstructRootCompletion R s root M),
      normalizedLogWeight T p.1) =
      selectedWeightSum
        (fun p : ↥R => normalizedLogWeight T p.1) M
  rw [missingPetalSupport_reconstruct hvalid hM]
  rfl

/-- Reconstruction leaves every visible petal total unchanged. -/
theorem fivePetalNormalizedTotal_reconstruct_visible
    {R : Finset ℕ} {T : ℝ} {s t : Fin 3}
    {S : Finset ↥R} {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root)
    {M : Finset ↥R} (hM : M ⊆ Finset.univ \ S)
    (hts : t ≠ s) :
    fivePetalNormalizedTotal R T
        (reconstructRootCompletion R s root M) t =
      fivePetalNormalizedTotal R T root t := by
  calc
    fivePetalNormalizedTotal R T
        (reconstructRootCompletion R s root M) t =
      fivePetalNormalizedTotal R T
        (fiveRootPart R s
          (reconstructRootCompletion R s root M)) t :=
        (fivePetalNormalizedTotal_rootPart
          R T s t (reconstructRootCompletion R s root M) hts).symm
    _ = fivePetalNormalizedTotal R T root t := by
      rw [rootPart_reconstruct hvalid hM]

/-- Weight of the fixed exposed root before the missing petal is sampled. -/
noncomputable def exposedRootBaseWeight
    (R : Finset ℕ) (_s : Fin 3)
    (S : Finset ↥R) (root : FiveConfiguration R) : ℝ :=
  ∏ p : ↥R,
    if p ∈ S
    then fiveLabelWeight (reciprocalBernoulli p.1) (root p)
    else 1 - reciprocalBernoulli p.1

theorem missingPetal_local_factor
    {p : ℕ} (hp : 0 < p) (s : Fin 3) :
    (1 - reciprocalBernoulli p) * missingPetalParameter p =
      fiveLabelWeight (reciprocalBernoulli p) (petalLabel s) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  fin_cases s <;>
    simp [reciprocalBernoulli, missingPetalParameter,
      fiveLabelWeight, petalLabel] <;>
    field_simp <;> ring

theorem unused_local_factor
    {p : ℕ} (hp : 0 < p) :
    (1 - reciprocalBernoulli p) *
        (1 - missingPetalParameter p) =
      fiveLabelWeight (reciprocalBernoulli p) 0 := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  simp [reciprocalBernoulli, missingPetalParameter,
    fiveLabelWeight]
  field_simp
  ring

theorem subsetWeight_eq_univ_product
    {α : Type*} [Fintype α] [DecidableEq α]
    (Q M : Finset α) (q : α → ℝ) (hM : M ⊆ Q) :
    subsetWeight Q q M =
      ∏ p : α,
        if p ∈ M then q p
        else if p ∈ Q then 1 - q p else 1 := by
  rw [subsetWeight]
  have hpoint (p : α) :
      (if p ∈ M then q p
        else if p ∈ Q then 1 - q p else 1) =
      if p ∈ Q
      then (if p ∈ M then q p else 1 - q p)
      else 1 := by
    by_cases hpM : p ∈ M
    · have hpQ := hM hpM
      simp [hpM, hpQ]
    · by_cases hpQ : p ∈ Q <;> simp [hpM, hpQ]
  simp_rw [hpoint]
  rw [Finset.prod_ite]
  simp only [Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.filter_notMem_eq_sdiff, Finset.prod_const_one,
    mul_one]
  rw [Finset.prod_ite]
  congr 1
  · rw [Finset.filter_mem_eq_inter,
      Finset.inter_eq_right.mpr hM]
  · rw [Finset.filter_notMem_eq_sdiff]

/-- Exact product-law factorization of the missing-petal completion. -/
theorem fiveConfigurationWeight_reconstruct
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {s : Fin 3} {S : Finset ↥R}
    {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root)
    {M : Finset ↥R} (hM : M ⊆ Finset.univ \ S) :
    fiveConfigurationWeight R reciprocalBernoulli
        (reconstructRootCompletion R s root M) =
      exposedRootBaseWeight R s S root *
        subsetWeight (Finset.univ \ S)
          (fun p : ↥R => missingPetalParameter p.1) M := by
  rw [fiveConfigurationWeight,
    subsetWeight_eq_univ_product
      (Finset.univ \ S) M
      (fun p : ↥R => missingPetalParameter p.1) hM,
    exposedRootBaseWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p _hp
  by_cases hpS : p ∈ S
  · have hpM : p ∉ M := by
      intro hpM
      exact (Finset.mem_sdiff.mp (hM hpM)).2 hpS
    simp [reconstructRootCompletion, hpS, hpM]
  · have hpZero := validExposedRoot_zero_outside hvalid hpS
    by_cases hpM : p ∈ M
    · have hpPos := (hR p.1 p.2).pos
      simp only [reconstructRootCompletion, hpM, if_true,
        hpS, Finset.mem_sdiff, Finset.mem_univ, true_and]
      simp only [if_false]
      exact (missingPetal_local_factor hpPos s).symm
    · have hpPos := (hR p.1 p.2).pos
      simp only [reconstructRootCompletion, hpM, if_false,
        hpS, Finset.mem_sdiff, Finset.mem_univ, true_and]
      rw [hpZero]
      exact (unused_local_factor hpPos).symm

/-- Unnormalized mass of one completion in a fixed exposed-root fiber. -/
noncomputable def fiveCompletionFiberMass
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (s : Fin 3)
    (S : Finset ↥P) (root : FiveConfiguration P)
    (E : FiveConfiguration P → Prop) : ℝ := by
  classical
  exact ∑ c : FiveConfiguration P,
    if fiveRootPart P s c = root ∧
      fiveStateSupport P s c = S ∧ E c
    then fiveConfigurationWeight P r c else 0

theorem fiveCompletionFiberMass_nonneg
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (s : Fin 3) (S : Finset ↥R)
    (root : FiveConfiguration R)
    (E : FiveConfiguration R → Prop) :
    0 ≤ fiveCompletionFiberMass
      R reciprocalBernoulli s S root E := by
  classical
  unfold fiveCompletionFiberMass
  apply Finset.sum_nonneg
  intro c _hc
  split_ifs
  · exact fiveConfigurationWeight_nonneg
      (fun p _hp => reciprocalBernoulli_nonneg p)
      (fun p hp => reciprocalBernoulli_le_three_quarters
        (Nat.one_le_iff_ne_zero.mpr (hR p hp).ne_zero))
      c
  · exact le_rfl

theorem fiveCompletionFiberMass_eq_zero_of_invalid
    {α : Type*} [DecidableEq α]
    {P : Finset α} {r : α → ℝ} {s : Fin 3}
    {S : Finset ↥P} {root : FiveConfiguration P}
    (hinvalid : ¬ IsValidExposedRoot P s S root)
    (E : FiveConfiguration P → Prop) :
    fiveCompletionFiberMass P r s S root E = 0 := by
  classical
  unfold fiveCompletionFiberMass
  apply Finset.sum_eq_zero
  intro c _hc
  by_cases h :
      fiveRootPart P s c = root ∧
        fiveStateSupport P s c = S ∧ E c
  · exact False.elim
      (hinvalid (isValidExposedRoot_of_fiber h.1 h.2.1))
  · simp [h]

/-- The completion-fiber mass is exactly a Bernoulli subset-event mass on
the missing petal, multiplied by the exposed-root base weight. -/
theorem fiveCompletionFiberMass_eq_subsetEventMass
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {s : Fin 3} {S : Finset ↥R}
    {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root)
    (E : FiveConfiguration R → Prop) :
    fiveCompletionFiberMass R reciprocalBernoulli s S root E =
      exposedRootBaseWeight R s S root *
        subsetEventMass (Finset.univ \ S)
          (fun p : ↥R => missingPetalParameter p.1)
          (fun M => E (reconstructRootCompletion R s root M)) := by
  classical
  let F : FiveConfiguration R → Prop := fun c =>
    fiveRootPart R s c = root ∧ fiveStateSupport R s c = S
  calc
    fiveCompletionFiberMass R reciprocalBernoulli s S root E =
        ∑ c : FiveConfiguration R,
          if F c
          then if E c
            then fiveConfigurationWeight R reciprocalBernoulli c
            else 0
          else 0 := by
      unfold fiveCompletionFiberMass
      apply Finset.sum_congr rfl
      intro c _hc
      by_cases hF : F c
      · by_cases hE : E c <;> simp [F, hF, hE]
      · rw [if_neg]
        · simp [hF]
        · intro h
          exact hF ⟨h.1, h.2.1⟩
    _ = ∑ c : {c : FiveConfiguration R // F c},
          if E c.1
          then fiveConfigurationWeight R reciprocalBernoulli c.1
          else 0 := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_subtype
        (p := F) (Finset.univ.filter F) (by simp) (fun c =>
          if E c
          then fiveConfigurationWeight R reciprocalBernoulli c
          else 0)]
    _ = ∑ M : {M : Finset ↥R // M ⊆ Finset.univ \ S},
          if E (reconstructRootCompletion R s root M.1)
          then fiveConfigurationWeight R reciprocalBernoulli
            (reconstructRootCompletion R s root M.1)
          else 0 := by
      apply Fintype.sum_equiv
        (completionFiberEquiv R s S root hvalid)
      intro c
      have hcEq := congrArg Subtype.val
        ((completionFiberEquiv R s S root hvalid).left_inv c)
      exact (congrArg
        (fun z : FiveConfiguration R =>
          if E z
          then fiveConfigurationWeight R reciprocalBernoulli z
          else 0) hcEq).symm
    _ = ∑ M ∈ (Finset.univ \ S).powerset,
          if E (reconstructRootCompletion R s root M)
          then fiveConfigurationWeight R reciprocalBernoulli
            (reconstructRootCompletion R s root M)
          else 0 := by
      rw [Finset.sum_subtype
        (p := fun M : Finset ↥R => M ⊆ Finset.univ \ S)
        ((Finset.univ \ S).powerset) (by simp)
        (fun M =>
          if E (reconstructRootCompletion R s root M)
          then fiveConfigurationWeight R reciprocalBernoulli
            (reconstructRootCompletion R s root M)
          else 0)]
    _ = exposedRootBaseWeight R s S root *
        subsetEventMass (Finset.univ \ S)
          (fun p : ↥R => missingPetalParameter p.1)
          (fun M => E (reconstructRootCompletion R s root M)) := by
      unfold subsetEventMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro M hM
      have hMsub := Finset.mem_powerset.mp hM
      rw [fiveConfigurationWeight_reconstruct hR hvalid hMsub]
      by_cases hE : E (reconstructRootCompletion R s root M) <;>
        simp [hE]

theorem fiveCompletionFiberMass_true
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {s : Fin 3} {S : Finset ↥R}
    {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root) :
    fiveCompletionFiberMass R reciprocalBernoulli s S root
        (fun _ => True) =
      exposedRootBaseWeight R s S root := by
  rw [fiveCompletionFiberMass_eq_subsetEventMass hR hvalid]
  unfold subsetEventMass
  simp only [if_true]
  rw [sum_subsetWeight, mul_one]

theorem exposedRootBaseWeight_eq_supportMarkMass
    {R : Finset ℕ}
    {s : Fin 3} {S : Finset ↥R}
    {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root) :
    exposedRootBaseWeight R s S root =
      subtypeBernoulliWeight R reciprocalBernoulli S *
        (1 / 3 : ℝ) ^ S.card := by
  have hlabel (p : ↥R) (hpS : p ∈ S) :
      fiveLabelWeight (reciprocalBernoulli p.1) (root p) =
        reciprocalBernoulli p.1 / 3 := by
    have hpSupport :
        p ∈ fiveStateSupport R s root := by
      simpa only [hvalid.2] using hpS
    have hpIncluded :
        fiveLabelIncluded s (root p) :=
      (mem_fiveStateSupport R s root p).mp hpSupport
    have hpNe : root p ≠ 0 := by
      intro hpZero
      rw [hpZero] at hpIncluded
      exact fiveLabelIncluded_zero s hpIncluded
    simp [fiveLabelWeight, hpNe]
  have hprod :
      (∏ p ∈ S,
          fiveLabelWeight
            (reciprocalBernoulli p.1) (root p)) =
        (∏ p ∈ S, reciprocalBernoulli p.1) *
          (1 / 3 : ℝ) ^ S.card := by
    calc
      (∏ p ∈ S,
          fiveLabelWeight
            (reciprocalBernoulli p.1) (root p)) =
          ∏ p ∈ S,
            (reciprocalBernoulli p.1 * (1 / 3 : ℝ)) := by
        apply Finset.prod_congr rfl
        intro p hp
        rw [hlabel p hp]
        ring
      _ = (∏ p ∈ S, reciprocalBernoulli p.1) *
          ∏ _p ∈ S, (1 / 3 : ℝ) := by
        rw [Finset.prod_mul_distrib]
      _ = (∏ p ∈ S, reciprocalBernoulli p.1) *
          (1 / 3 : ℝ) ^ S.card := by
        rw [Finset.prod_const]
  rw [exposedRootBaseWeight, subtypeBernoulliWeight,
    Finset.prod_ite, Finset.filter_mem_eq_inter,
    Finset.univ_inter, Finset.filter_notMem_eq_sdiff,
    hprod]
  ring

theorem exposedRootBaseWeight_nonneg
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {s : Fin 3} {S : Finset ↥R}
    {root : FiveConfiguration R} :
    0 ≤ exposedRootBaseWeight R s S root := by
  rw [exposedRootBaseWeight]
  apply Finset.prod_nonneg
  intro p _hp
  by_cases hpS : p ∈ S
  · rw [if_pos hpS]
    exact fiveLabelWeight_nonneg
      (reciprocalBernoulli_nonneg p.1)
      (reciprocalBernoulli_le_three_quarters
        (Nat.one_le_iff_ne_zero.mpr (hR p.1 p.2).ne_zero))
      (root p)
  · rw [if_neg hpS]
    exact sub_nonneg.mpr
      (reciprocalBernoulli_le_three_quarters
        (Nat.one_le_iff_ne_zero.mpr (hR p.1 p.2).ne_zero) |>.trans
        (by norm_num))

/-- A uniform translated-window estimate contracts any completion event
which forces the missing subset into the corresponding interval event. -/
theorem fiveCompletionFiberMass_le_of_window
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {s : Fin 3} {S : Finset ↥R}
    {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root)
    (E : FiveConfiguration R → Prop)
    (eligible : ↥R → Prop) [DecidablePred eligible]
    (u : ↥R → ℝ) (a b L : ℝ)
    (hforces : ∀ M : Finset ↥R,
      M ⊆ Finset.univ \ S →
      E (reconstructRootCompletion R s root M) →
      SelectedIntervalEvent eligible u a b M)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          (Finset.univ \ S) (fun p : ↥R => p.1)
          u eligible x (b - a) ≤ L) :
    fiveCompletionFiberMass R reciprocalBernoulli s S root E ≤
      L * fiveCompletionFiberMass R reciprocalBernoulli s S root
        (fun _ => True) := by
  have hnpos :
      ∀ p ∈ Finset.univ \ S, 0 < p.1 :=
    fun p _hp => (hR p.1 p.2).pos
  have hq0 :
      ∀ p ∈ Finset.univ \ S,
        0 ≤ missingPetalParameter p.1 :=
    fun p _hp => missingPetalParameter_nonneg p.1
  have hq1 :
      ∀ p ∈ Finset.univ \ S,
        missingPetalParameter p.1 ≤ 1 :=
    fun p hp =>
      (missingPetalParameter_lt_one (hnpos p hp)).le
  have hselected :
      subsetEventMass (Finset.univ \ S)
          (fun p : ↥R => missingPetalParameter p.1)
          (SelectedIntervalEvent eligible u a b) ≤ L :=
    subsetEventMass_missingPetalAlong_le_of_window
      (Finset.univ \ S) (fun p : ↥R => p.1)
      u eligible a b L hnpos hwindow
  have hevent :
      subsetEventMass (Finset.univ \ S)
          (fun p : ↥R => missingPetalParameter p.1)
          (fun M => E (reconstructRootCompletion R s root M)) ≤ L := by
    exact (subsetEventMass_mono
      (Finset.univ \ S)
      (fun p : ↥R => missingPetalParameter p.1)
      (fun M => E (reconstructRootCompletion R s root M))
      (SelectedIntervalEvent eligible u a b)
      hq0 hq1
      (fun M hM hE =>
        hforces M (Finset.mem_powerset.mp hM) hE)).trans hselected
  rw [fiveCompletionFiberMass_eq_subsetEventMass hR hvalid,
    fiveCompletionFiberMass_true hR hvalid]
  calc
    exposedRootBaseWeight R s S root *
        subsetEventMass (Finset.univ \ S)
          (fun p : ↥R => missingPetalParameter p.1)
          (fun M => E (reconstructRootCompletion R s root M)) ≤
      exposedRootBaseWeight R s S root * L :=
        mul_le_mul_of_nonneg_left hevent
          (exposedRootBaseWeight_nonneg hR)
    _ = L * exposedRootBaseWeight R s S root := mul_comm _ _

/-- Concrete one-completion missing-petal contraction for the prime-band
event.  Only the uniform reciprocal-window estimate remains as input. -/
theorem fiveCompletionPrimeBandEvent_le_of_window
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀)
    {s : Fin 3} {S : Finset ↥R}
    {root : FiveConfiguration R}
    (hvalid : IsValidExposedRoot R s S root)
    (L : ℝ)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          (Finset.univ \ S) (fun p : ↥R => p.1)
          (fun p : ↥R => normalizedLogWeight T p.1)
          (fun p : ↥R => normalizedLogDepth T p.1 ≤ d₀)
          x (2 * w) ≤ L) :
    fiveCompletionFiberMass R reciprocalBernoulli s S root
        (fun c =>
          fivePrimeBandEvent
            R T lower upper w depths threshold c) ≤
      L * fiveCompletionFiberMass R reciprocalBernoulli s S root
        (fun _ => True) := by
  let t := otherPetal s
  have hts : t ≠ s := otherPetal_ne s
  let y := fivePetalNormalizedTotal R T root t
  apply fiveCompletionFiberMass_le_of_window
    hR hvalid
    (fun c =>
      fivePrimeBandEvent
        R T lower upper w depths threshold c)
    (fun p : ↥R => normalizedLogDepth T p.1 ≤ d₀)
    (fun p : ↥R => normalizedLogWeight T p.1)
    (y - w) (y + w) L
  · intro M hM hc
    let c := reconstructRootCompletion R s root M
    have hprefix :=
      fivePrimeBandEvent_prefix hc (some s) hd₀
    have hcount :
        1 ≤ fiveLabelPrefixCount R T c (some s) d₀ :=
      hthreshold.trans hprefix
    have hnonempty :
        (fiveLabelDepthPrefix R T c (some s) d₀).Nonempty := by
      rw [← Finset.card_pos]
      exact Nat.zero_lt_one.trans_le hcount
    obtain ⟨p, hpPrefix⟩ := hnonempty
    have hpData := mem_fiveLabelDepthPrefix.mp hpPrefix
    have hpMissing :
        p ∈ missingPetalSupport R s c := by
      simpa [missingPetalSupport, activeFiveLabel] using hpData.1
    have hpM : p ∈ M := by
      rw [show c = reconstructRootCompletion R s root M from rfl,
        missingPetalSupport_reconstruct hvalid hM] at hpMissing
      exact hpMissing
    have hmissingTotal :=
      fivePetalNormalizedTotal_reconstruct_missing
        (T := T) hvalid hM
    have hvisibleTotal :=
      fivePetalNormalizedTotal_reconstruct_visible
        (T := T) hvalid hM hts
    have hbalance :=
      fivePrimeBandEvent_petalBalance hc s t
    have habs := abs_le.mp hbalance
    have hvisibleOther :
        fivePetalNormalizedTotal R T
            (reconstructRootCompletion R s root M) (otherPetal s) =
          fivePetalNormalizedTotal R T root (otherPetal s) := by
      simpa [t] using hvisibleTotal
    have habsOther :
        -w ≤
            fivePetalNormalizedTotal R T
                (reconstructRootCompletion R s root M) s -
              fivePetalNormalizedTotal R T
                (reconstructRootCompletion R s root M) (otherPetal s) ∧
          fivePetalNormalizedTotal R T
                (reconstructRootCompletion R s root M) s -
              fivePetalNormalizedTotal R T
                (reconstructRootCompletion R s root M) (otherPetal s) ≤
            w := by
      simpa [t] using habs
    refine ⟨⟨p, hpM, hpData.2⟩, ?_, ?_⟩
    · dsimp [y, t]
      rw [← hmissingTotal]
      linarith [habsOther.1, hvisibleOther]
    · dsimp [y, t]
      rw [← hmissingTotal]
      linarith [habsOther.2, hvisibleOther]
  · intro x
    have hwidth : (y + w) - (y - w) = 2 * w := by
      ring
    simpa only [hwidth] using hwindow x

/-- A separated pair event with a common represented support. -/
def fiveSeparatedPairEvent
    {α : Type*} [DecidableEq α]
    (P : Finset α) (s : Fin 3)
    (E₁ E₂ : FiveConfiguration P → Prop)
    (x : FiveRootPairSample P) : Prop :=
  E₁ x.2.1 ∧ E₂ x.2.2 ∧
    fiveStateSupport P s x.2.1 = x.1 ∧
    fiveStateSupport P s x.2.2 = x.1

/-- After the root observation is fixed, the two completions factor
exactly. -/
theorem finiteFiberMass_separatedPair
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (s : Fin 3)
    (E₁ E₂ : FiveConfiguration P → Prop)
    (o : FiveRootObservation P) :
    finiteFiberMass
        (fiveRootPairAtom P r s)
        (fiveRootObservation P s) o
        (fiveSeparatedPairEvent P s E₁ E₂) =
      fiveCompletionFiberMass P r s o.1 o.2.1 E₁ *
        fiveCompletionFiberMass P r s o.1 o.2.2 E₂ /
        subtypeBernoulliWeight P r o.1 := by
  classical
  rcases o with ⟨S, root₁, root₂⟩
  change
    finiteFiberMass
        (fiveRootPairAtom P r s)
        (fiveRootObservation P s) (S, root₁, root₂)
        (fiveSeparatedPairEvent P s E₁ E₂) =
      fiveCompletionFiberMass P r s S root₁ E₁ *
        fiveCompletionFiberMass P r s S root₂ E₂ /
        subtypeBernoulliWeight P r S
  unfold finiteFiberMass
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single S]
  · rw [Fintype.sum_prod_type]
    unfold fiveCompletionFiberMass
    rw [Finset.sum_mul_sum, Finset.sum_div]
    simp_rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _hc
    apply Finset.sum_congr rfl
    intro d _hd
    rw [fiveRootPairAtom]
    by_cases hcRoot : fiveRootPart P s c = root₁
    · by_cases hdRoot : fiveRootPart P s d = root₂
      · by_cases hcSupport : fiveStateSupport P s c = S
        · by_cases hdSupport : fiveStateSupport P s d = S
          · by_cases hcE : E₁ c
            · by_cases hdE : E₂ d
              · simp [fiveRootObservation, fiveSeparatedPairEvent,
                  hcRoot, hdRoot, hcSupport, hdSupport, hcE, hdE]
              · simp [fiveRootObservation, fiveSeparatedPairEvent,
                  hcRoot, hdRoot, hcSupport, hdSupport, hcE, hdE]
            · simp [fiveRootObservation, fiveSeparatedPairEvent,
                hcRoot, hdRoot, hcSupport, hdSupport, hcE]
          · simp [fiveRootObservation, fiveSeparatedPairEvent,
              hcRoot, hdRoot, hcSupport, hdSupport]
        · simp [fiveRootObservation, fiveSeparatedPairEvent,
            hcRoot, hdRoot, hcSupport]
      · simp [fiveRootObservation, fiveSeparatedPairEvent,
          hcRoot, hdRoot]
    · simp [fiveRootObservation, fiveSeparatedPairEvent, hcRoot]
  · intro S _hS hSo
    apply Finset.sum_eq_zero
    intro cd _hcd
    simp [fiveRootObservation, hSo]
  · simp

/-- The support clauses in `fiveSeparatedPairEvent` do not alter the full
fiber mass, since the pair atom itself vanishes off the common-support
locus. -/
theorem finiteFiberMass_true_eq_separatedTrue
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (s : Fin 3)
    (o : FiveRootObservation P) :
    finiteFiberMass
        (fiveRootPairAtom P r s)
        (fiveRootObservation P s) o (fun _ => True) =
      finiteFiberMass
        (fiveRootPairAtom P r s)
        (fiveRootObservation P s) o
        (fiveSeparatedPairEvent P s
          (fun _ => True) (fun _ => True)) := by
  classical
  unfold finiteFiberMass
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hs :
      fiveStateSupport P s x.2.1 = x.1 ∧
        fiveStateSupport P s x.2.2 = x.1
  · rcases hs with ⟨hc, hd⟩
    simp [fiveSeparatedPairEvent, hc, hd]
  · have hzero : fiveRootPairAtom P r s x = 0 := by
      simp [fiveRootPairAtom, hs]
    simp [hzero]

theorem finiteFiberMass_true_factor
    {α : Type*} [DecidableEq α]
    (P : Finset α) (r : α → ℝ) (s : Fin 3)
    (o : FiveRootObservation P) :
    finiteFiberMass
        (fiveRootPairAtom P r s)
        (fiveRootObservation P s) o (fun _ => True) =
      fiveCompletionFiberMass P r s o.1 o.2.1 (fun _ => True) *
        fiveCompletionFiberMass P r s o.1 o.2.2 (fun _ => True) /
        subtypeBernoulliWeight P r o.1 := by
  rw [finiteFiberMass_true_eq_separatedTrue]
  exact finiteFiberMass_separatedPair
    P r s (fun _ => True) (fun _ => True) o

/-- A valid exposed-root pair has exactly the Bernoulli support mass
times the uniform nine-mark mass `9^{-|S|}`. -/
theorem finiteFiberMass_true_eq_supportNineMarkMass
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {s : Fin 3} {S : Finset ↥R}
    {root₁ root₂ : FiveConfiguration R}
    (hvalid₁ : IsValidExposedRoot R s S root₁)
    (hvalid₂ : IsValidExposedRoot R s S root₂) :
    finiteFiberMass
        (fiveRootPairAtom R reciprocalBernoulli s)
        (fiveRootObservation R s) (S, root₁, root₂)
        (fun _ => True) =
      subtypeBernoulliWeight R reciprocalBernoulli S *
        (1 / 9 : ℝ) ^ S.card := by
  have hmu :
      0 < subtypeBernoulliWeight
        R reciprocalBernoulli S := by
    apply subtypeBernoulliWeight_pos
    · intro p _hp
      rw [reciprocalBernoulli]
      positivity
    · intro p hp
      have hpOne : (1 : ℝ) ≤ p := by
        exact_mod_cast (hR p hp).one_le
      rw [reciprocalBernoulli,
        div_lt_one (by positivity)]
      linarith
  have hpow :
      (1 / 3 : ℝ) ^ S.card *
          (1 / 3 : ℝ) ^ S.card =
        (1 / 9 : ℝ) ^ S.card := by
    rw [← mul_pow]
    congr 1
    norm_num
  rw [finiteFiberMass_true_factor,
    fiveCompletionFiberMass_true hR hvalid₁,
    fiveCompletionFiberMass_true hR hvalid₂,
    exposedRootBaseWeight_eq_supportMarkMass hvalid₁,
    exposedRootBaseWeight_eq_supportMarkMass hvalid₂]
  field_simp [hmu.ne']
  rw [pow_two, hpow]

/-- The accepted-pair predicate, including the common-support constraints
on which the annealed atom is supported. -/
def fivePrimeBandAcceptedPair
    (R : Finset ℕ) (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (x : FiveRootPairSample R) : Prop :=
  fivePrimeBandEvent R T lower upper w depths threshold x.2.1 ∧
  fivePrimeBandEvent R T lower upper w depths threshold x.2.2 ∧
  fiveStateSupport R s x.2.1 = x.1 ∧
  fiveStateSupport R s x.2.2 = x.1

/-- The root-good event used by the two-pivot estimate.  Both exposed
colourings retain the full delayed prefix profile on each of their three
visible active labels; this stronger information is essential to exclude
large rank-zero atoms. -/
def PrimeBandRootGood
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (o : FiveRootObservation R) : Prop :=
  (∀ l : ↥(representedActiveLabels s), ∀ d : ↥depths,
      threshold d.1 ≤
        fiveLabelPrefixCount R T o.2.1 l.1 d.1) ∧
  (∀ l : ↥(representedActiveLabels s), ∀ d : ↥depths,
      threshold d.1 ≤
        fiveLabelPrefixCount R T o.2.2 l.1 d.1) ∧
  (∀ t u : Fin 3, t ≠ s → u ≠ s →
      |fivePetalNormalizedTotal R T o.2.1 t -
        fivePetalNormalizedTotal R T o.2.1 u| ≤ w) ∧
  (∀ t u : Fin 3, t ≠ s → u ≠ s →
      |fivePetalNormalizedTotal R T o.2.2 t -
        fivePetalNormalizedTotal R T o.2.2 u| ≤ w)

theorem primeBandRootGood_supportMark_smallBall
    {R : Finset ℕ} {T w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {S : Finset ↥R}
    {m : SupportNineMarking S}
    (hgood : PrimeBandRootGood R T w depths threshold s
      (S, supportMarkRootFirst s S m,
        supportMarkRootSecond s S m)) :
    SupportMarkSmallBall R T w S m := by
  constructor
  · have hbalance :=
      hgood.2.2.1
        (otherPetal s) (secondOtherPetal s)
        (otherPetal_ne s) (secondOtherPetal_ne s)
    rw [supportMarkRootFirst_petalDifference] at hbalance
    exact hbalance
  · have hbalance :=
      hgood.2.2.2
        (otherPetal s) (secondOtherPetal s)
        (otherPetal_ne s) (secondOtherPetal_ne s)
    rw [supportMarkRootSecond_petalDifference] at hbalance
    exact hbalance

/-- Conditional root-colouring mass on a fixed represented support.
Each valid pair of root colourings has uniform mass `9^{-|S|}`; the
Bernoulli support mass is deliberately left outside. -/
noncomputable def primeBandRootColorMass
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (S : Finset ↥R) : ℝ := by
  classical
  exact
    ∑ root₁ : FiveConfiguration R,
      ∑ root₂ : FiveConfiguration R,
        if IsValidExposedRoot R s S root₁ ∧
            IsValidExposedRoot R s S root₂ ∧
            PrimeBandRootGood R T w depths threshold s
              (S, root₁, root₂)
        then (1 / 9 : ℝ) ^ S.card else 0

theorem primeBandRootColorMass_eq_sum_supportMarking
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (S : Finset ↥R)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)] :
    primeBandRootColorMass
        R T w depths threshold s S =
      ∑ m : SupportNineMarking S,
        if PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m)
        then (1 / 9 : ℝ) ^ S.card else 0 := by
  classical
  let F : FiveConfiguration R × FiveConfiguration R → Prop :=
    fun roots =>
      IsValidExposedRoot R s S roots.1 ∧
        IsValidExposedRoot R s S roots.2
  calc
    primeBandRootColorMass
        R T w depths threshold s S =
      ∑ roots : FiveConfiguration R × FiveConfiguration R,
        if F roots
        then
          if PrimeBandRootGood R T w depths threshold s
              (S, roots.1, roots.2)
          then (1 / 9 : ℝ) ^ S.card else 0
        else 0 := by
      unfold primeBandRootColorMass
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro root₁ _hroot₁
      apply Finset.sum_congr rfl
      intro root₂ _hroot₂
      by_cases hF : F (root₁, root₂)
      · by_cases hgood :
            PrimeBandRootGood R T w depths threshold s
              (S, root₁, root₂) <;>
          simp [F, hF, hgood]
      · have hnot :
            ¬(IsValidExposedRoot R s S root₁ ∧
              IsValidExposedRoot R s S root₂ ∧
              PrimeBandRootGood R T w depths threshold s
                (S, root₁, root₂)) := by
          intro h
          exact hF ⟨h.1, h.2.1⟩
        simp [F, hF, hnot]
    _ = ∑ roots : ValidExposedRootPair R s S,
        if PrimeBandRootGood R T w depths threshold s
            (S, roots.1.1, roots.1.2)
        then (1 / 9 : ℝ) ^ S.card else 0 := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_subtype
        (p := F) (Finset.univ.filter F) (by simp)
        (fun roots =>
          if PrimeBandRootGood R T w depths threshold s
              (S, roots.1, roots.2)
          then (1 / 9 : ℝ) ^ S.card else 0)]
    _ = ∑ m : SupportNineMarking S,
        if PrimeBandRootGood R T w depths threshold s
            (S, supportMarkRootFirst s S m,
              supportMarkRootSecond s S m)
        then (1 / 9 : ℝ) ^ S.card else 0 := by
      apply Fintype.sum_equiv
        (validExposedRootPairEquivSupportNineMarking
          R s S)
      intro roots
      have hleft :=
        congrArg Subtype.val
          ((validExposedRootPairEquivSupportNineMarking
            R s S).left_inv roots)
      exact (congrArg
        (fun pair :
            FiveConfiguration R × FiveConfiguration R =>
          if PrimeBandRootGood R T w depths threshold s
              (S, pair.1, pair.2)
          then (1 / 9 : ℝ) ^ S.card else 0)
        hleft).symm

theorem primeBandRootColorMass_nonneg
    (R : Finset ℕ) (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (S : Finset ↥R) :
    0 ≤ primeBandRootColorMass
      R T w depths threshold s S := by
  classical
  unfold primeBandRootColorMass
  apply Finset.sum_nonneg
  intro root₁ _hroot₁
  apply Finset.sum_nonneg
  intro root₂ _hroot₂
  split_ifs
  · positivity
  · exact le_rfl

/-- Annealed marked-support mass of the two-dimensional root small-ball
event.  Unlike a fixed-support estimate, this retains the Bernoulli
support weights required by factorial insertion. -/
noncomputable def annealedSupportMarkSmallBallMass
    (R : Finset ℕ) (T w : ℝ) : ℝ := by
  classical
  exact
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        ∑ m : SupportNineMarking S,
          if SupportMarkSmallBall R T w S m
          then (1 / 9 : ℝ) ^ S.card else 0

def SupportMarkRankTwo
    {R : Finset ℕ} {S : Finset ↥R}
    (m : SupportNineMarking S) : Prop :=
  ∃ p q : ↥S, p ≠ q ∧
    ¬ NineMarkCollinear (m p) (m q)

def SupportMarkRankZero
    {R : Finset ℕ} {S : Finset ↥R}
    (m : SupportNineMarking S) : Prop :=
  ∀ p : ↥S, m p = zeroNineMark

def SupportMarkRankOne
    {R : Finset ℕ} {S : Finset ↥R}
    (m : SupportNineMarking S) : Prop :=
  ¬ SupportMarkRankTwo m ∧
    ∃ p : ↥S, m p ≠ zeroNineMark

theorem supportMark_rank_trichotomy
    {R : Finset ℕ} {S : Finset ↥R}
    (m : SupportNineMarking S) :
    SupportMarkRankTwo m ∨
      SupportMarkRankOne m ∨
      SupportMarkRankZero m := by
  classical
  by_cases htwo : SupportMarkRankTwo m
  · exact Or.inl htwo
  · by_cases hzero : SupportMarkRankZero m
    · exact Or.inr (Or.inr hzero)
    · apply Or.inr
      apply Or.inl
      refine ⟨htwo, ?_⟩
      unfold SupportMarkRankZero at hzero
      exact Classical.not_forall.mp hzero

/-- Exact disintegration of the aggregate root-good mass: first sample
the Bernoulli represented support, then two independent uniform
three-colour roots, equivalently one uniform nine-mark at each support
point. -/
theorem primeBandRootGoodMass_eq_sum_supportColorMass
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)] :
    (∑ o : FiveRootObservation R,
      if PrimeBandRootGood R T w depths threshold s o
      then
        finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o (fun _ => True)
      else 0) =
    ∑ S : Finset ↥R,
      subtypeBernoulliWeight R reciprocalBernoulli S *
        primeBandRootColorMass
          R T w depths threshold s S := by
  classical
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro S _hS
  rw [Fintype.sum_prod_type]
  unfold primeBandRootColorMass
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root₁ _hroot₁
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro root₂ _hroot₂
  by_cases hvalid₁ :
      IsValidExposedRoot R s S root₁
  · by_cases hvalid₂ :
        IsValidExposedRoot R s S root₂
    · by_cases hgood :
          PrimeBandRootGood R T w depths threshold s
            (S, root₁, root₂)
      · rw [if_pos hgood,
          if_pos ⟨hvalid₁, hvalid₂, hgood⟩,
          finiteFiberMass_true_eq_supportNineMarkMass
            hR hvalid₁ hvalid₂]
      · simp [hgood]
    · have hzero :
          finiteFiberMass
              (fiveRootPairAtom R reciprocalBernoulli s)
              (fiveRootObservation R s)
              (S, root₁, root₂) (fun _ => True) = 0 := by
        rw [finiteFiberMass_true_factor,
          fiveCompletionFiberMass_eq_zero_of_invalid
            hvalid₂ (fun _ => True)]
        simp
      simp [hvalid₂, hzero]
  · have hzero :
        finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s)
            (S, root₁, root₂) (fun _ => True) = 0 := by
      rw [finiteFiberMass_true_factor,
        fiveCompletionFiberMass_eq_zero_of_invalid
          hvalid₁ (fun _ => True)]
      simp
    simp [hvalid₁, hzero]

theorem primeBandRootGoodMass_le_annealedSupportMarkSmallBallMass
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)] :
    (∑ o : FiveRootObservation R,
      if PrimeBandRootGood R T w depths threshold s o
      then
        finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o (fun _ => True)
      else 0) ≤
      annealedSupportMarkSmallBallMass R T w := by
  rw [primeBandRootGoodMass_eq_sum_supportColorMass
    hR T w depths threshold s]
  unfold annealedSupportMarkSmallBallMass
  apply Finset.sum_le_sum
  intro S _hS
  apply mul_le_mul_of_nonneg_left
  · rw [primeBandRootColorMass_eq_sum_supportMarking
      R T w depths threshold s S]
    apply Finset.sum_le_sum
    intro m _hm
    by_cases hgood :
        PrimeBandRootGood R T w depths threshold s
          (S, supportMarkRootFirst s S m,
            supportMarkRootSecond s S m)
    · rw [if_pos hgood,
        if_pos (primeBandRootGood_supportMark_smallBall hgood)]
    · rw [if_neg hgood]
      split_ifs
      · positivity
      · exact le_rfl
  · apply subtypeBernoulliWeight_nonneg
    · intro p _hp
      exact reciprocalBernoulli_nonneg p
    · intro p hp
      have hpOne : (1 : ℝ) ≤ p := by
        exact_mod_cast (hR p hp).one_le
      rw [reciprocalBernoulli]
      apply (div_le_one (by positivity)).mpr
      linarith

/-- Diagnostic conditional reduction only.  A uniform `O(w²)`
supportwise bound is generally false; the actual estimate must retain
the Bernoulli support weights and use annealed factorial insertion. -/
theorem primeBandRootGoodMass_le_of_rootColorMass
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) (A : ℝ)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)]
    (hcolor : ∀ S : Finset ↥R,
      primeBandRootColorMass
        R T w depths threshold s S ≤ A) :
    (∑ o : FiveRootObservation R,
      if PrimeBandRootGood R T w depths threshold s o
      then
        finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o (fun _ => True)
      else 0) ≤ A := by
  rw [primeBandRootGoodMass_eq_sum_supportColorMass
    hR T w depths threshold s]
  calc
    (∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          primeBandRootColorMass
            R T w depths threshold s S) ≤
      ∑ S : Finset ↥R,
        subtypeBernoulliWeight R reciprocalBernoulli S *
          A := by
      apply Finset.sum_le_sum
      intro S _hS
      apply mul_le_mul_of_nonneg_left (hcolor S)
      apply subtypeBernoulliWeight_nonneg
      · intro p _hp
        exact reciprocalBernoulli_nonneg p
      · intro p hp
        have hpOne : (1 : ℝ) ≤ p := by
          exact_mod_cast (hR p hp).one_le
        rw [reciprocalBernoulli]
        apply (div_le_one (by positivity)).mpr
        linarith
    _ = A := by
      rw [← Finset.sum_mul,
        sum_subtypeBernoulliWeight, one_mul]

theorem fivePrimeBandAcceptedPair_rootGood
    {R : Finset ℕ} {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {s : Fin 3} {x : FiveRootPairSample R}
    (hx : fivePrimeBandAcceptedPair
      R T lower upper w depths threshold s x) :
    PrimeBandRootGood R T w depths threshold s
      (fiveRootObservation R s x) := by
  rcases hx with ⟨hc, hd, _hcSupport, _hdSupport⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro l depth
    have hprefix :=
      fivePrimeBandEvent_prefix hc l.1 depth.2
    simpa [fiveRootObservation,
      fiveLabelPrefixCount_rootPart_of_represented
        R T s x.2.1 l.2 depth.1] using hprefix
  · intro l depth
    have hprefix :=
      fivePrimeBandEvent_prefix hd l.1 depth.2
    simpa [fiveRootObservation,
      fiveLabelPrefixCount_rootPart_of_represented
        R T s x.2.2 l.2 depth.1] using hprefix
  · intro t u hts hus
    rw [fiveRootObservation,
      fivePetalNormalizedTotal_rootPart R T s t x.2.1 hts,
      fivePetalNormalizedTotal_rootPart R T s u x.2.1 hus]
    exact fivePrimeBandEvent_petalBalance hc t u
  · intro t u hts hus
    rw [fiveRootObservation,
      fivePetalNormalizedTotal_rootPart R T s t x.2.2 hts,
      fivePetalNormalizedTotal_rootPart R T s u x.2.2 hus]
    exact fivePrimeBandEvent_petalBalance hd t u

/-- Adding the support constraints to the accepted-pair predicate does not
change its weighted mass, because the pair atom vanishes off them. -/
theorem finiteWeightedMass_acceptedPair_eq_collision
    (R : Finset ℕ) (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3) :
    finiteWeightedMass
        (fiveRootPairAtom R reciprocalBernoulli s)
        (fivePrimeBandAcceptedPair
          R T lower upper w depths threshold s) =
      fiveRootCollision R reciprocalBernoulli
        (fivePrimeBandEvent
          R T lower upper w depths threshold) s := by
  classical
  rw [← finiteWeightedMass_pairEvent_eq_collision
    R reciprocalBernoulli
    (fivePrimeBandEvent
      R T lower upper w depths threshold) s]
  unfold finiteWeightedMass
  apply Finset.sum_congr rfl
  intro x _hx
  rw [fiveRootPairAtom]
  by_cases hc :
      fivePrimeBandEvent
        R T lower upper w depths threshold x.2.1
  · by_cases hd :
      fivePrimeBandEvent
        R T lower upper w depths threshold x.2.2
    · by_cases hcSupport : fiveStateSupport R s x.2.1 = x.1
      · by_cases hdSupport : fiveStateSupport R s x.2.2 = x.1
        · simp [fivePrimeBandAcceptedPair, hc, hd,
            hcSupport, hdSupport]
        · simp [fivePrimeBandAcceptedPair, hc, hd,
            hcSupport, hdSupport]
      · simp [fivePrimeBandAcceptedPair, hc, hd, hcSupport]
    · simp [fivePrimeBandAcceptedPair, hd]
  · simp [fivePrimeBandAcceptedPair, hc]

/-- In every exposed-root observation, the two hidden missing-petal
processes independently contribute one translated-window factor.  A
single full-support reciprocal-window bound therefore gives the required
`L^2` contraction, including observations with inconsistent roots (whose
fiber mass is zero). -/
theorem finiteFiberMass_acceptedPair_le_of_window
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀)
    {s : Fin 3} (o : FiveRootObservation R)
    (L : ℝ) (hL : 0 ≤ L)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R => normalizedLogWeight T p.1)
          (fun p : ↥R => normalizedLogDepth T p.1 ≤ d₀)
          x (2 * w) ≤ L) :
    finiteFiberMass
        (fiveRootPairAtom R reciprocalBernoulli s)
        (fiveRootObservation R s) o
        (fivePrimeBandAcceptedPair
          R T lower upper w depths threshold s) ≤
      L ^ 2 *
        finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o (fun _ => True) := by
  classical
  rcases o with ⟨S, root₁, root₂⟩
  let B : FiveConfiguration R → Prop := fun c =>
    fivePrimeBandEvent R T lower upper w depths threshold c
  change
    finiteFiberMass
        (fiveRootPairAtom R reciprocalBernoulli s)
        (fiveRootObservation R s) (S, root₁, root₂)
        (fiveSeparatedPairEvent R s B B) ≤
      L ^ 2 *
        finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) (S, root₁, root₂)
          (fun _ => True)
  by_cases hvalid₁ : IsValidExposedRoot R s S root₁
  · by_cases hvalid₂ : IsValidExposedRoot R s S root₂
    · have hwindowS : ∀ x : ℝ,
          reciprocalWindowMassAlong
              (Finset.univ \ S) (fun p : ↥R => p.1)
              (fun p : ↥R => normalizedLogWeight T p.1)
              (fun p : ↥R =>
                normalizedLogDepth T p.1 ≤ d₀)
              x (2 * w) ≤ L := by
        intro x
        exact
          (reciprocalWindowMassAlong_mono
            Finset.sdiff_subset
            (fun p : ↥R => p.1)
            (fun p : ↥R => normalizedLogWeight T p.1)
            (fun p : ↥R =>
              normalizedLogDepth T p.1 ≤ d₀)
            x (2 * w)).trans (hwindow x)
      have hfirst :=
        fiveCompletionPrimeBandEvent_le_of_window
          (lower := lower) (upper := upper) (w := w)
          hR hd₀ hthreshold hvalid₁ L hwindowS
      have hsecond :=
        fiveCompletionPrimeBandEvent_le_of_window
          (lower := lower) (upper := upper) (w := w)
          hR hd₀ hthreshold hvalid₂ L hwindowS
      have hfirstNonneg :
          0 ≤ fiveCompletionFiberMass
            R reciprocalBernoulli s S root₁ B :=
        fiveCompletionFiberMass_nonneg
          hR s S root₁ B
      have hsecondNonneg :
          0 ≤ fiveCompletionFiberMass
            R reciprocalBernoulli s S root₂ B :=
        fiveCompletionFiberMass_nonneg
          hR s S root₂ B
      have htrueFirstNonneg :
          0 ≤ fiveCompletionFiberMass
            R reciprocalBernoulli s S root₁
              (fun _ => True) :=
        fiveCompletionFiberMass_nonneg
          hR s S root₁ (fun _ => True)
      have hproduct :
          fiveCompletionFiberMass
                R reciprocalBernoulli s S root₁ B *
              fiveCompletionFiberMass
                R reciprocalBernoulli s S root₂ B ≤
            (L * fiveCompletionFiberMass
                R reciprocalBernoulli s S root₁
                  (fun _ => True)) *
              (L * fiveCompletionFiberMass
                R reciprocalBernoulli s S root₂
                  (fun _ => True)) := by
        exact mul_le_mul hfirst hsecond hsecondNonneg
          (mul_nonneg hL htrueFirstNonneg)
      have hmu :
          0 < subtypeBernoulliWeight
            R reciprocalBernoulli S := by
        apply subtypeBernoulliWeight_pos
        · intro p _hp
          rw [reciprocalBernoulli]
          positivity
        · intro p hp
          have hpOne : (1 : ℝ) ≤ p := by
            exact_mod_cast
              (Nat.one_le_iff_ne_zero.mpr
                (hR p hp).ne_zero)
          rw [reciprocalBernoulli,
            div_lt_one (by positivity)]
          linarith
      rw [finiteFiberMass_separatedPair,
        finiteFiberMass_true_factor]
      calc
        fiveCompletionFiberMass
              R reciprocalBernoulli s S root₁ B *
            fiveCompletionFiberMass
              R reciprocalBernoulli s S root₂ B /
              subtypeBernoulliWeight
                R reciprocalBernoulli S ≤
          (L * fiveCompletionFiberMass
              R reciprocalBernoulli s S root₁
                (fun _ => True)) *
            (L * fiveCompletionFiberMass
              R reciprocalBernoulli s S root₂
                (fun _ => True)) /
              subtypeBernoulliWeight
                R reciprocalBernoulli S :=
          (div_le_div_iff_of_pos_right hmu).2 hproduct
        _ = L ^ 2 *
            (fiveCompletionFiberMass
                  R reciprocalBernoulli s S root₁
                    (fun _ => True) *
                fiveCompletionFiberMass
                  R reciprocalBernoulli s S root₂
                    (fun _ => True) /
                subtypeBernoulliWeight
                  R reciprocalBernoulli S) := by
          ring
    · rw [finiteFiberMass_separatedPair,
        finiteFiberMass_true_factor,
        fiveCompletionFiberMass_eq_zero_of_invalid
          hvalid₂ B,
        fiveCompletionFiberMass_eq_zero_of_invalid
          hvalid₂ (fun _ => True)]
      simp
  · rw [finiteFiberMass_separatedPair,
      finiteFiberMass_true_factor,
      fiveCompletionFiberMass_eq_zero_of_invalid
        hvalid₁ B,
      fiveCompletionFiberMass_eq_zero_of_invalid
        hvalid₁ (fun _ => True)]
    simp

/-- The explicit constant produced by the rank-two, rank-one, and rank-zero
parts of the rooted small-ball proof. -/
def primeBandRootSmallBallConstant
    (Ctwo Cone L Eone Ezero : ℝ) : ℝ :=
  16 * Ctwo * L ^ 2 + 8 * Cone * Eone * L + Ezero

/-- Assemble the rank-two, rank-one, and rank-zero estimates into the
explicit root small-ball constant.  The hypothesis `hdecompose` is exactly
the canonical rank trichotomy; the remaining hypotheses are the local
two-pivot bound, the convergent rank-series bound, and endpoint decay. -/
theorem rootSmallBall_le_explicit_constant
    {rootMass : ℝ} {ell : ℕ → ℝ} {K : ℕ}
    {Ctwo Cone w L Eone Ezero : ℝ}
    (hell : ∀ i < K, 0 < ell i)
    (hCtwo : 0 ≤ Ctwo) (hCone : 0 ≤ Cone)
    (hw : 0 ≤ w) (hL : 0 ≤ L) (hEone : 0 ≤ Eone)
    (hseries : pivotRankSeries ell K ≤ L)
    (hendpoint : (1 / 3 : ℝ) ^ K ≤ Eone * w)
    (hdecompose :
      rootMass ≤
        twoPivotRankContribution ell K Ctwo w +
        onePivotRankContribution ell K Cone w +
        Ezero * w ^ 2) :
    rootMass ≤
      primeBandRootSmallBallConstant
        Ctwo Cone L Eone Ezero * w ^ 2 := by
  have htwo :=
    twoPivotRankContribution_le
      (w := w) hell hCtwo hL hseries
  have hone :=
    onePivotRankContribution_le
      (w := w) hell hCone hw hseries hendpoint hEone
  calc
    rootMass ≤
        twoPivotRankContribution ell K Ctwo w +
          onePivotRankContribution ell K Cone w +
          Ezero * w ^ 2 := hdecompose
    _ ≤ (16 * Ctwo * w ^ 2 * L ^ 2) +
          (8 * Cone * Eone * L * w ^ 2) +
          Ezero * w ^ 2 := by
      gcongr
    _ = primeBandRootSmallBallConstant
          Ctwo Cone L Eone Ezero * w ^ 2 := by
      rw [primeBandRootSmallBallConstant]
      ring

/-- Exact finite reduction of the actual rooted collision estimate.  The
`hroot` hypothesis is the output of the two-pivot/rank summation, with its
constant displayed above.  The `hmissing` hypothesis is the uniform
two-copy missing-petal contraction inside every exposed-root fiber.

The conclusion is the manuscript's `C*w^4` bound, with no asymptotic
notation and no hidden probability-space interface. -/
theorem fiveRootCollision_le_of_twoPivot_and_missing
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (s : Fin 3)
    (Ctwo Cone L Eone Ezero Cmissing : ℝ)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)]
    (hCmissing : 0 ≤ Cmissing)
    (hroot :
      (∑ o : FiveRootObservation R,
        if PrimeBandRootGood R T w depths threshold s o
        then
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o (fun _ => True)
        else 0) ≤
      primeBandRootSmallBallConstant
        Ctwo Cone L Eone Ezero * w ^ 2)
    (hmissing : ∀ o : FiveRootObservation R,
      finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o
          (fivePrimeBandAcceptedPair
            R T lower upper w depths threshold s) ≤
        (Cmissing * w ^ 2) *
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o (fun _ => True)) :
    fiveRootCollision R reciprocalBernoulli
        (fivePrimeBandEvent
          R T lower upper w depths threshold) s ≤
      primeBandRootSmallBallConstant
        Ctwo Cone L Eone Ezero * Cmissing * w ^ 4 := by
  classical
  let rootGood : FiveRootObservation R → Prop :=
    PrimeBandRootGood R T w depths threshold s
  let event : FiveRootPairSample R → Prop :=
    fivePrimeBandAcceptedPair
      R T lower upper w depths threshold s
  letI : DecidablePred rootGood := by
    intro o
    change Decidable
      (PrimeBandRootGood R T w depths threshold s o)
    infer_instance
  have hr0 : ∀ p ∈ R, 0 ≤ reciprocalBernoulli p :=
    fun p _hp => reciprocalBernoulli_nonneg p
  have hr34 : ∀ p ∈ R, reciprocalBernoulli p ≤ 3 / 4 :=
    fun p hp => reciprocalBernoulli_le_three_quarters
      (Nat.one_le_iff_ne_zero.mpr (hR p hp).ne_zero)
  have hrpos : ∀ p ∈ R, 0 < reciprocalBernoulli p := by
    intro p _hp
    rw [reciprocalBernoulli]
    positivity
  have hr1 : ∀ p ∈ R, reciprocalBernoulli p < 1 := by
    intro p hp
    have hpOne : (1 : ℝ) ≤ p := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr
        (hR p hp).ne_zero)
    rw [reciprocalBernoulli, div_lt_one (by positivity)]
    linarith
  have hmain :=
    finiteFiberEventMass_le_mul
      (fiveRootPairAtom R reciprocalBernoulli s)
      (fiveRootObservation R s)
      event event rootGood
      (Cmissing * w ^ 2)
      (primeBandRootSmallBallConstant
        Ctwo Cone L Eone Ezero * w ^ 2)
      (fun x => fiveRootPairAtom_nonneg
        hr0 hr34 hrpos hr1 x)
      (mul_nonneg hCmissing (sq_nonneg w))
      (fun x hx => ⟨fivePrimeBandAcceptedPair_rootGood hx, hx⟩)
      hmissing hroot
  rw [finiteWeightedMass_acceptedPair_eq_collision
    R T lower upper w depths threshold s] at hmain
  calc
    fiveRootCollision R reciprocalBernoulli
        (fivePrimeBandEvent
          R T lower upper w depths threshold) s ≤
        (Cmissing * w ^ 2) *
          (primeBandRootSmallBallConstant
            Ctwo Cone L Eone Ezero * w ^ 2) := hmain
    _ = primeBandRootSmallBallConstant
          Ctwo Cone L Eone Ezero * Cmissing * w ^ 4 := by ring

/-- Collision assembly with the missing-petal hypothesis discharged by
the translated reciprocal-window estimate.  Thus the only analytic
inputs left are the exposed-root two-pivot estimate `hroot` and the
one-dimensional prime-window estimate `hwindow`. -/
theorem fiveRootCollision_le_of_twoPivot_and_window
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀)
    (s : Fin 3)
    (Ctwo Cone Lrank Eone Ezero Cwindow : ℝ)
    [DecidablePred
      (PrimeBandRootGood R T w depths threshold s)]
    (hw : 0 ≤ w) (hCwindow : 0 ≤ Cwindow)
    (hroot :
      (∑ o : FiveRootObservation R,
        if PrimeBandRootGood R T w depths threshold s o
        then
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o (fun _ => True)
        else 0) ≤
      primeBandRootSmallBallConstant
        Ctwo Cone Lrank Eone Ezero * w ^ 2)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R => normalizedLogWeight T p.1)
          (fun p : ↥R => normalizedLogDepth T p.1 ≤ d₀)
          x (2 * w) ≤ Cwindow * w) :
    fiveRootCollision R reciprocalBernoulli
        (fivePrimeBandEvent
          R T lower upper w depths threshold) s ≤
      primeBandRootSmallBallConstant
          Ctwo Cone Lrank Eone Ezero *
        Cwindow ^ 2 * w ^ 4 := by
  have hmissing : ∀ o : FiveRootObservation R,
      finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o
          (fivePrimeBandAcceptedPair
            R T lower upper w depths threshold s) ≤
        (Cwindow ^ 2 * w ^ 2) *
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o
            (fun _ => True) := by
    intro o
    have hfiber :=
      finiteFiberMass_acceptedPair_le_of_window
        (lower := lower) (upper := upper) (w := w) (s := s)
        hR hd₀ hthreshold o (Cwindow * w)
        (mul_nonneg hCwindow hw) hwindow
    calc
      finiteFiberMass
          (fiveRootPairAtom R reciprocalBernoulli s)
          (fiveRootObservation R s) o
          (fivePrimeBandAcceptedPair
            R T lower upper w depths threshold s) ≤
        (Cwindow * w) ^ 2 *
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o
            (fun _ => True) := hfiber
      _ = (Cwindow ^ 2 * w ^ 2) *
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o
            (fun _ => True) := by
        ring
  exact fiveRootCollision_le_of_twoPivot_and_missing
    hR T lower upper w depths threshold s
    Ctwo Cone Lrank Eone Ezero (Cwindow ^ 2)
    (sq_nonneg Cwindow) hroot hmissing

/-- Fully local-prime-band-facing collision estimate at normalized scale
`N` and target width `η / N`.  This is the form specialized to
`N = T^2` on `quadraticPrimeBand T a`: the only prime-theoretic input is
the uniform local-band upper bound `hlocal`. -/
theorem fiveRootCollision_le_of_twoPivot_and_localBand
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {N : ℕ} (hN : 0 < N)
    (lower upper η : ℝ) (hη : 0 < η)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀)
    (s : Fin 3)
    (Ctwo Cone Lrank Eone Ezero Klocal : ℝ)
    [DecidablePred
      (PrimeBandRootGood R (N : ℝ)
        (η / (N : ℝ)) depths threshold s)]
    (hsize :
      (2 * η + Real.log 4) / (N : ℝ) ≤
        Real.exp (-d₀) / 2)
    (hroot :
      (∑ o : FiveRootObservation R,
        if PrimeBandRootGood R (N : ℝ)
            (η / (N : ℝ)) depths threshold s o
        then
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o (fun _ => True)
        else 0) ≤
      primeBandRootSmallBallConstant
          Ctwo Cone Lrank Eone Ezero *
        (η / (N : ℝ)) ^ 2)
    (hlocal : ∀ t : ℝ, Real.exp (-d₀) / 2 ≤ t →
      LocalPrimeBand.localBandShiftedReciprocalMass
          N t (2 * η + Real.log 4) ≤
        Klocal / (N : ℝ)) :
    fiveRootCollision R reciprocalBernoulli
        (fivePrimeBandEvent
          R (N : ℝ) lower upper (η / (N : ℝ))
          depths threshold) s ≤
      primeBandRootSmallBallConstant
          Ctwo Cone Lrank Eone Ezero *
        (2 * Klocal / η) ^ 2 *
          (η / (N : ℝ)) ^ 4 := by
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hpadNonneg :
      0 ≤ 2 * η + Real.log 4 := by
    exact add_nonneg (mul_nonneg (by norm_num) hη.le)
      (Real.log_nonneg (by norm_num))
  have hKdiv : 0 ≤ Klocal / (N : ℝ) := by
    exact
      (LocalPrimeBand.localBandShiftedReciprocalMass_nonneg
        hpadNonneg).trans
      (hlocal (Real.exp (-d₀) / 2) le_rfl)
  have hKlocal : 0 ≤ Klocal := by
    have hm :
        0 ≤ (Klocal / (N : ℝ)) * (N : ℝ) :=
      mul_nonneg hKdiv hNR.le
    have heq :
        (Klocal / (N : ℝ)) * (N : ℝ) =
          Klocal := by
      field_simp [hNR.ne']
    rwa [heq] at hm
  have hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight (N : ℝ) p.1)
          (fun p : ↥R =>
            normalizedLogDepth (N : ℝ) p.1 ≤ d₀)
          x (2 * (η / (N : ℝ))) ≤
        (2 * Klocal / η) * (η / (N : ℝ)) := by
    intro x
    have hx :=
      reciprocalWindowMassAlong_normalized_le_of_localBand
        hR hN hη hsize hlocal x
    calc
      reciprocalWindowMassAlong
          Finset.univ (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight (N : ℝ) p.1)
          (fun p : ↥R =>
            normalizedLogDepth (N : ℝ) p.1 ≤ d₀)
          x (2 * (η / (N : ℝ))) ≤
        2 * Klocal / (N : ℝ) := hx
      _ = (2 * Klocal / η) *
          (η / (N : ℝ)) := by
        field_simp [hη.ne', hNR.ne']
  exact fiveRootCollision_le_of_twoPivot_and_window
    hR (N : ℝ) lower upper (η / (N : ℝ))
    depths threshold hd₀ hthreshold s
    Ctwo Cone Lrank Eone Ezero (2 * Klocal / η)
    (div_nonneg hη.le hNR.le)
    (div_nonneg (mul_nonneg (by norm_num) hKlocal) hη.le)
    hroot hwindow

/-- End-to-end finite collision assembly from the canonical pivot-rank
decomposition and a local-prime-band estimate.  The combinatorial
constants `16` and `8` are supplied by the exact nine-mark enumeration
inside `rootSmallBall_le_explicit_constant`; no aggregate `hroot`
hypothesis remains. -/
theorem fiveRootCollision_le_of_rankDecomposition_and_localBand
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {N : ℕ} (hN : 0 < N)
    (lower upper η : ℝ) (hη : 0 < η)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀)
    (s : Fin 3)
    (ell : ℕ → ℝ) (Kpivot : ℕ)
    (Ctwo Cone Lrank Eone Ezero Klocal : ℝ)
    [DecidablePred
      (PrimeBandRootGood R (N : ℝ)
        (η / (N : ℝ)) depths threshold s)]
    (hell : ∀ i < Kpivot, 0 < ell i)
    (hCtwo : 0 ≤ Ctwo) (hCone : 0 ≤ Cone)
    (hLrank : 0 ≤ Lrank) (hEone : 0 ≤ Eone)
    (hseries : pivotRankSeries ell Kpivot ≤ Lrank)
    (hendpoint :
      (1 / 3 : ℝ) ^ Kpivot ≤
        Eone * (η / (N : ℝ)))
    (hdecompose :
      (∑ o : FiveRootObservation R,
        if PrimeBandRootGood R (N : ℝ)
            (η / (N : ℝ)) depths threshold s o
        then
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o (fun _ => True)
        else 0) ≤
      twoPivotRankContribution ell Kpivot Ctwo
          (η / (N : ℝ)) +
        onePivotRankContribution ell Kpivot Cone
          (η / (N : ℝ)) +
        Ezero * (η / (N : ℝ)) ^ 2)
    (hsize :
      (2 * η + Real.log 4) / (N : ℝ) ≤
        Real.exp (-d₀) / 2)
    (hlocal : ∀ t : ℝ, Real.exp (-d₀) / 2 ≤ t →
      LocalPrimeBand.localBandShiftedReciprocalMass
          N t (2 * η + Real.log 4) ≤
        Klocal / (N : ℝ)) :
    fiveRootCollision R reciprocalBernoulli
        (fivePrimeBandEvent
          R (N : ℝ) lower upper (η / (N : ℝ))
          depths threshold) s ≤
      primeBandRootSmallBallConstant
          Ctwo Cone Lrank Eone Ezero *
        (2 * Klocal / η) ^ 2 *
          (η / (N : ℝ)) ^ 4 := by
  have hw : 0 ≤ η / (N : ℝ) :=
    div_nonneg hη.le (Nat.cast_nonneg N)
  have hroot :
      (∑ o : FiveRootObservation R,
        if PrimeBandRootGood R (N : ℝ)
            (η / (N : ℝ)) depths threshold s o
        then
          finiteFiberMass
            (fiveRootPairAtom R reciprocalBernoulli s)
            (fiveRootObservation R s) o (fun _ => True)
        else 0) ≤
      primeBandRootSmallBallConstant
          Ctwo Cone Lrank Eone Ezero *
        (η / (N : ℝ)) ^ 2 := by
    exact rootSmallBall_le_explicit_constant
      hell hCtwo hCone hw hLrank hEone
      hseries hendpoint hdecompose
  exact fiveRootCollision_le_of_twoPivot_and_localBand
    hR hN lower upper η hη depths threshold
    hd₀ hthreshold s
    Ctwo Cone Lrank Eone Ezero Klocal
    hsize hroot hlocal

end Erdos536
