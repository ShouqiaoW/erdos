import Erdos390.Full.ConditionedPoissonLimit

/-!
# Uniqueness of the global Dickman delay equation

The exact-total density identification eventually produces a density shape
which is constant on the first unit interval and satisfies the Dickman delay
equation thereafter.  This file proves that such a shape is necessarily a
scalar multiple of the method-of-steps solution `rhoGlobal`.

The endpoint `x = 1` is not differentiable two-sided.  We prove and use its
right derivative explicitly, so the induction across successive unit
intervals has no hidden endpoint convention.
-/

open Filter Set
open scoped Interval

noncomputable section

namespace Erdos390.Full.DickmanUniqueness

open MeasureTheory
open DickmanBasic ConditionedPoissonLimit

/-- The global Dickman function has right derivative `-1` at its first birth
point. -/
lemma hasDerivWithinAt_rhoGlobal_one :
    HasDerivWithinAt rhoGlobal (-1) (Ici (1 : ℝ)) 1 := by
  let q : ℝ → ℝ := fun t => rhoApprox 1 (t - 1) / safeDenom t
  let branch : ℝ → ℝ := fun x => 1 - ∫ t in (1 : ℝ)..x, q t
  have hq : Continuous q := by
    simpa only [q] using continuous_stepIntegrand 1
  have hprimitive : HasDerivAt
      (fun x : ℝ => ∫ t in (1 : ℝ)..x, q t) (q 1) 1 :=
    (hq.integral_hasStrictDerivAt 1 1).hasDerivAt
  have hqone : q 1 = 1 := by
    simp [q, rhoApprox, safeDenom]
  have hbranch : HasDerivAt branch (-1) 1 := by
    have h := (hasDerivAt_const (1 : ℝ) (1 : ℝ)).sub hprimitive
    simpa only [branch, Pi.sub_apply, hqone, zero_sub] using h
  have heq : rhoGlobal =ᶠ[nhdsWithin (1 : ℝ) (Ici (1 : ℝ))] branch := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds
        (Iio_mem_nhds (show (1 : ℝ) < 2 by norm_num)),
      self_mem_nhdsWithin] with x hx2 hx1
    have hxle : x ≤ (2 : ℕ) := by norm_num; exact hx2.le
    rw [rhoGlobal_eq_rhoApprox_of_le_nat 2 hxle]
    by_cases hx : x = 1
    · subst x
      simp [branch, rhoApprox]
    · have h1x : 1 < x := lt_of_le_of_ne hx1 (Ne.symm hx)
      rw [rhoApprox_succ_of_one_lt 1 h1x]
  exact hbranch.hasDerivWithinAt.congr_of_eventuallyEq_of_mem heq (by simp)

/-- Scalar multiples have the corresponding right derivative at `1`. -/
lemma hasDerivWithinAt_smul_rhoGlobal_one (c : ℝ) :
    HasDerivWithinAt (fun x => c * rhoGlobal x) (-c)
      (Ici (1 : ℝ)) 1 := by
  convert hasDerivWithinAt_rhoGlobal_one.const_mul c using 1
  ring

/-- Uniqueness for the normalized global delay equation.  The derivative at
`1` is deliberately a right derivative; for `x > 1` the hypothesis can of
course be supplied by an ordinary derivative. -/
theorem eq_smul_rhoGlobal_of_delay
    (g : ℝ → ℝ) (c : ℝ)
    (hgcont : Continuous g)
    (hbase : ∀ x, x ≤ 1 → g x = c)
    (hdelay : ∀ x, 1 ≤ x →
      HasDerivWithinAt g (-g (x - 1) / x) (Ici x) x) :
    ∀ x, g x = c * rhoGlobal x := by
  have hstage : ∀ n : ℕ, ∀ x : ℝ, x ≤ (n : ℝ) + 1 →
      g x = c * rhoGlobal x := by
    intro n
    induction n with
    | zero =>
        intro x hx
        rw [hbase x (by simpa using hx), rhoGlobal_eq_one_of_le_one (by simpa using hx)]
        ring
    | succ n ih =>
        intro x hx
        by_cases hxold : x ≤ (n : ℝ) + 1
        · exact ih x hxold
        · let a : ℝ := (n : ℝ) + 1
          let b : ℝ := (n : ℝ) + 2
          have hab : a ≤ b := by dsimp [a, b]; linarith
          have hxmem : x ∈ Icc a b := by
            constructor
            · exact le_of_not_ge hxold
            · dsimp [b]
              norm_num [Nat.cast_add, Nat.cast_one, add_assoc] at hx ⊢
              exact hx
          have hinit : g a = c * rhoGlobal a := by
            apply ih
            simp [a]
          have hderivG : ∀ y ∈ Ico a b,
              HasDerivWithinAt g (-g (y - 1) / y) (Ici y) y := by
            intro y hy
            apply hdelay y
            dsimp [a] at hy
            have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
            exact (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1).trans hy.1
          have hderivRho : ∀ y ∈ Ico a b,
              HasDerivWithinAt (fun z => c * rhoGlobal z)
                (-g (y - 1) / y) (Ici y) y := by
            intro y hy
            have hyOne : 1 ≤ y := by
              dsimp [a] at hy
              have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              exact (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1).trans hy.1
            have hym1 : y - 1 ≤ (n : ℝ) + 1 := by
              dsimp [b] at hy
              linarith [hy.2]
            have hprev := ih (y - 1) hym1
            by_cases hyEq : y = 1
            · subst y
              convert hasDerivWithinAt_smul_rhoGlobal_one c using 1
              · rw [hprev]
                simp [rhoGlobal_eq_one_of_le_one]
            · have hyGt : 1 < y := lt_of_le_of_ne hyOne (Ne.symm hyEq)
              have hrho := (hasDerivAt_rhoGlobal hyGt).const_mul c
              have hrhoWithin : HasDerivWithinAt
                  (fun z => c * rhoGlobal z)
                  (c * (-rhoGlobal (y - 1) / y)) (Ici y) y :=
                hrho.hasDerivWithinAt
              convert hrhoWithin using 1
              rw [hprev]
              ring
          exact eq_of_has_deriv_right_eq hderivG hderivRho
            hgcont.continuousOn
            ((continuous_const.mul continuous_rhoGlobal).continuousOn)
            hinit x hxmem
  intro x
  exact hstage ⌈x⌉₊ x (by
    have hxceil : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
    linarith)

/-- Natural half-line version for a density shape.  No behavior at negative
arguments is assumed: the proof continuously extends the initial constant
branch to the left and invokes the global uniqueness theorem. -/
theorem eq_smul_rhoGlobal_of_delay_nonneg
    (g : ℝ → ℝ) (c : ℝ)
    (hgcont : ContinuousOn g (Ici (0 : ℝ)))
    (hbase : ∀ x ∈ Icc (0 : ℝ) 1, g x = c)
    (hdelay : ∀ x, 1 ≤ x →
      HasDerivWithinAt g (-g (x - 1) / x) (Ici x) x) :
    ∀ x, 0 ≤ x → g x = c * rhoGlobal x := by
  let gext : ℝ → ℝ := fun x => if x ≤ 0 then c else g x
  have hgextCont : Continuous gext := by
    unfold gext
    apply continuous_if_le continuous_id continuous_const
      continuous_const.continuousOn hgcont
    intro x hx
    have hx0 : x = 0 := by simpa using hx
    subst x
    exact (hbase 0 (by norm_num)).symm
  have hgextBase : ∀ x, x ≤ 1 → gext x = c := by
    intro x hx
    by_cases hx0 : x ≤ 0
    · simp [gext, hx0]
    · have hxpos : 0 < x := lt_of_not_ge hx0
      change (if x ≤ 0 then c else g x) = c
      rw [if_neg (not_le.mpr hxpos)]
      exact hbase x ⟨hxpos.le, hx⟩
  have hgextDelay : ∀ x, 1 ≤ x →
      HasDerivWithinAt gext (-gext (x - 1) / x) (Ici x) x := by
    intro x hx
    have heq : ∀ z ∈ Ici x, gext z = g z := by
      intro z hz
      have hzpos : 0 < z := zero_lt_one.trans_le (hx.trans hz)
      simp [gext, not_le.mpr hzpos]
    have hd := (hdelay x hx).congr heq (heq x (by simp))
    have hprev : gext (x - 1) = g (x - 1) := by
      by_cases hxeq : x = 1
      · subst x
        simp [gext, hbase 0 (by norm_num)]
      · have hxgt : 1 < x := lt_of_le_of_ne hx (Ne.symm hxeq)
        simp [gext, not_le.mpr (sub_pos.mpr hxgt)]
    rw [hprev]
    exact hd
  have hglobal := eq_smul_rhoGlobal_of_delay gext c hgextCont
    hgextBase hgextDelay
  intro x hx
  have heq : gext x = g x := by
    by_cases hx0 : x = 0
    · subst x
      simp [gext, hbase 0 (by norm_num)]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      simp [gext, not_le.mpr hxpos]
  rw [← heq]
  exact hglobal x

end Erdos390.Full.DickmanUniqueness
