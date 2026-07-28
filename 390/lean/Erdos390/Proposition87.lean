import Mathlib

/-!
# The finite and ODE algebra behind Proposition 8.7

The analytic inputs to the nonlinear fit (uniform covariance gaps, relative row
errors, and existence of an integral curve inside the preselected box) are kept as
explicit hypotheses.  This file proves the block solve, the slow-coordinate and
effective-velocity ledgers, compatibility recovery, and the straight-target chain
rule with no hidden limiting assertion.
-/

open Metric Set

namespace Erdos390

section BlockInverse

variable {Q : Type*} [AddCommGroup Q] [Module ℝ Q]

/-- The one-dimensional Schur complement left after the fast block has been
inverted. -/
def slowSchurScalar (A : Q ≃ₗ[ℝ] Q) (b : Q) (ell : Q →ₗ[ℝ] ℝ) (d : ℝ) : ℝ :=
  d - ell (A.symm b)

/-- The slow coordinate in the inverse of the augmented block system. -/
noncomputable def blockSlowCoordinate (A : Q ≃ₗ[ℝ] Q) (b : Q) (ell : Q →ₗ[ℝ] ℝ)
    (d : ℝ) (vQ : Q) (vg : ℝ) : ℝ :=
  (vg - ell (A.symm vQ)) / slowSchurScalar A b ell d

/-- The fast coordinate obtained after solving for the slow coordinate. -/
noncomputable def blockFastCoordinate (A : Q ≃ₗ[ℝ] Q) (b : Q) (ell : Q →ₗ[ℝ] ℝ)
    (d : ℝ) (vQ : Q) (vg : ℝ) : Q :=
  A.symm (vQ - blockSlowCoordinate A b ell d vQ vg • b)

/-- Exact inverse algebra for the augmented fast/slow block. -/
theorem augmented_block_inverse
    (A : Q ≃ₗ[ℝ] Q) (b : Q) (ell : Q →ₗ[ℝ] ℝ)
    (d : ℝ) (vQ : Q) (vg : ℝ)
    (hσ : slowSchurScalar A b ell d ≠ 0) :
    A (blockFastCoordinate A b ell d vQ vg) +
          blockSlowCoordinate A b ell d vQ vg • b = vQ ∧
      ell (blockFastCoordinate A b ell d vQ vg) +
          d * blockSlowCoordinate A b ell d vQ vg = vg := by
  constructor
  · simp [blockFastCoordinate]
  · let lambda : ℝ := blockSlowCoordinate A b ell d vQ vg
    have hlambda : lambda * slowSchurScalar A b ell d = vg - ell (A.symm vQ) := by
      dsimp [lambda, blockSlowCoordinate]
      exact div_mul_cancel₀ _ hσ
    calc
      ell (blockFastCoordinate A b ell d vQ vg) +
            d * blockSlowCoordinate A b ell d vQ vg
          = ell (A.symm vQ) - lambda * ell (A.symm b) + d * lambda := by
              simp [blockFastCoordinate, lambda, smul_eq_mul]
      _ = ell (A.symm vQ) + lambda * slowSchurScalar A b ell d := by
            simp only [slowSchurScalar]
            ring
      _ = ell (A.symm vQ) + (vg - ell (A.symm vQ)) := by rw [hlambda]
      _ = vg := by ring

end BlockInverse

section SlowCoordinateBounds

/-- The scale-invariant form of the slow-coordinate estimate.  Its hypotheses
make the `w²` Schur gap and the `w` compensated numerator explicit. -/
theorem slow_coordinate_scaled_bound
    (num σ w cσ Cnum : ℝ)
    (hw : 0 < w) (hcσ : 0 < cσ) (hCnum : 0 ≤ Cnum)
    (hσ : cσ * w ^ 2 ≤ |σ|) (hnum : |num| ≤ Cnum * w) :
    w * |num / σ| ≤ Cnum / cσ := by
  have hσpos : 0 < |σ| := by
    have : 0 < cσ * w ^ 2 := mul_pos hcσ (sq_pos_of_pos hw)
    exact this.trans_le hσ
  have hleft : w * |num| ≤ Cnum * w ^ 2 := by
    have := mul_le_mul_of_nonneg_left hnum (le_of_lt hw)
    nlinarith
  have hratio : 0 ≤ Cnum / cσ := div_nonneg hCnum (le_of_lt hcσ)
  have hright : Cnum * w ^ 2 ≤ (Cnum / cσ) * |σ| := by
    calc
      Cnum * w ^ 2 = (Cnum / cσ) * (cσ * w ^ 2) := by
        field_simp
      _ ≤ (Cnum / cσ) * |σ| := mul_le_mul_of_nonneg_left hσ hratio
  rw [abs_div, ← mul_div_assoc]
  exact (div_le_iff₀ hσpos).2 (hleft.trans hright)

/-- The familiar `O(1 / w)` version of `slow_coordinate_scaled_bound`. -/
theorem slow_coordinate_bound
    (num σ w cσ Cnum : ℝ)
    (hw : 0 < w) (hcσ : 0 < cσ) (hCnum : 0 ≤ Cnum)
    (hσ : cσ * w ^ 2 ≤ |σ|) (hnum : |num| ≤ Cnum * w) :
    |num / σ| ≤ (Cnum / cσ) / w := by
  apply (le_div_iff₀ hw).2
  rw [mul_comm]
  exact slow_coordinate_scaled_bound num σ w cσ Cnum hw hcσ hCnum hσ hnum

/-- A `w`-sized compensated coefficient multiplied by the `1/w` slow velocity
gives a box-independent contribution to every prime row. -/
theorem effective_prime_velocity_bound
    (base coeff lambda w Cbase Ccoeff Cslow : ℝ)
    (hw : 0 < w) (hCslow : 0 ≤ Cslow)
    (hbase : |base| ≤ Cbase)
    (hcoeff : |coeff| ≤ Ccoeff * w)
    (hlambda : |lambda| ≤ Cslow / w) :
    |base + lambda * coeff| ≤ Cbase + Cslow * Ccoeff := by
  have hquot : 0 ≤ Cslow / w := div_nonneg hCslow (le_of_lt hw)
  have hmul : |lambda| * |coeff| ≤ (Cslow / w) * (Ccoeff * w) :=
    mul_le_mul hlambda hcoeff (abs_nonneg coeff) hquot
  calc
    |base + lambda * coeff| ≤ |base| + |lambda * coeff| := abs_add_le _ _
    _ = |base| + |lambda| * |coeff| := by rw [abs_mul]
    _ ≤ Cbase + (Cslow / w) * (Ccoeff * w) := add_le_add hbase hmul
    _ = Cbase + Cslow * Ccoeff := by field_simp

end SlowCoordinateBounds

section GaugeAnnihilator

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A linear functional which vanishes on the gauge hyperplane is a multiple of
the gauge.  This is the finite-dimensional annihilator step used to recover the
one compatibility relation omitted from the quotient solve. -/
theorem functional_eq_gauge_multiple
    (gauge residual : E →ₗ[ℝ] ℝ) (r : E)
    (hr : gauge r ≠ 0)
    (hker : ∀ x, gauge x = 0 → residual x = 0) :
    ∀ x, residual x = (residual r / gauge r) * gauge x := by
  intro x
  let c : ℝ := gauge x / gauge r
  let v : E := x - c • r
  have hvgauge : gauge v = 0 := by
    dsimp [v, c]
    simp only [map_sub, map_smul]
    rw [smul_eq_mul, div_mul_cancel₀ _ hr, sub_self]
  have hvresidual : residual v = 0 := hker v hvgauge
  have hxdecomp : x = v + c • r := by
    dsimp [v]
    abel
  calc
    residual x = residual v + c • residual r := by rw [hxdecomp, map_add, map_smul]
    _ = c * residual r := by rw [hvresidual, zero_add, smul_eq_mul]
    _ = (residual r / gauge r) * gauge x := by
      dsimp [c]
      field_simp

/-- If the remaining exact relation also kills a transverse vector, the residual
functional is zero everywhere. -/
theorem gauge_annihilator_recovery
    (gauge residual : E →ₗ[ℝ] ℝ) (r : E)
    (hgauge : gauge r ≠ 0)
    (hker : ∀ x, gauge x = 0 → residual x = 0)
    (htransverse : residual r = 0) :
    residual = 0 := by
  ext x
  rw [functional_eq_gauge_multiple gauge residual r hgauge hker x,
    htransverse, zero_div, zero_mul]
  rfl

end GaugeAnnihilator

section PrechosenBox

variable {E : Type*} [PseudoMetricSpace E]

/-- A path with a box-independent speed bound stays in a ball whose margin was
chosen before the path was constructed.  This is the finite noncircular core of
the `C_*` then `B_*` continuation argument: the only radius hypothesis is the
displayed, prior inequality. -/
theorem prechosen_closedBall_containment
    (ξ : ℝ → E) (center : E) (K : NNReal) (B : ℝ)
    (hLip : LipschitzOnWith K ξ (Icc (0 : ℝ) 1))
    (hmargin : dist (ξ 0) center + (K : ℝ) ≤ B) :
    MapsTo ξ (Icc (0 : ℝ) 1) (closedBall center B) := by
  intro t ht
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  have htime : dist t 0 ≤ 1 := by
    rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    exact ht.2
  have hstep : dist (ξ t) (ξ 0) ≤ (K : ℝ) := by
    exact (hLip.dist_le_mul t ht 0 hzero).trans
      (mul_le_of_le_one_right K.coe_nonneg htime)
  rw [mem_closedBall]
  calc
    dist (ξ t) center ≤ dist (ξ t) (ξ 0) + dist (ξ 0) center :=
      dist_triangle _ _ _
    _ ≤ (K : ℝ) + dist (ξ 0) center := add_le_add_left hstep _
    _ = dist (ξ 0) center + (K : ℝ) := add_comm _ _
    _ ≤ B := hmargin

end PrechosenBox

section StraightTarget

variable {E Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Explicit path-existence hypothesis for the nonlinear continuation step.

In the paper this proposition is discharged by Picard--Lindelöf together with the
preselected-box continuation estimate.  Keeping it as a named predicate prevents
the chain-rule algebra below from silently assuming that the path remains in the
box. -/
def HasStraightTargetPath (Ω : Set E) (v : E → E) (x₀ : E) : Prop :=
  ∃ ξ : ℝ → E, ξ 0 = x₀ ∧
    (∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ Ω) ∧
    ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt ξ (v (ξ t)) (Icc (0 : ℝ) 1) t

/-- Picard--Lindelöf produces the explicitly named straight-target path and,
crucially, the constructed path remains in the same closed ball on which the
vector-field hypotheses were checked. -/
theorem hasStraightTargetPath_of_picard [CompleteSpace E]
    (v : E → E) (x₀ : E) (a L K : NNReal)
    (hpl : IsPicardLindelof (fun _ : ℝ => v)
      (⟨0, left_mem_Icc.mpr zero_le_one⟩ : Icc (0 : ℝ) 1) x₀ a 0 L K) :
    HasStraightTargetPath (closedBall x₀ a) v x₀ := by
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hpl
    (mem_closedBall_self le_rfl)
  refine ⟨α.compProj, ?_, ?_, ?_⟩
  · rw [ODE.FunSpace.compProj_of_mem (left_mem_Icc.mpr zero_le_one), ← hα,
      ODE.FunSpace.next_apply₀]
  · intro t _
    exact α.compProj_mem_closedBall hpl.mul_max_le
  · intro t ht
    apply ODE.hasDerivWithinAt_picard_Icc
      (⟨0, left_mem_Icc.mpr zero_le_one⟩ : Icc (0 : ℝ) 1).2 hpl.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ => α.compProj_mem_closedBall hpl.mul_max_le) x₀ ht |>.congr_of_mem _ ht
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

/-- A directly usable time-independent Picard package.  The radius `a` is fixed
before the ODE is solved, and `L ≤ a` is exactly the unit-time continuation
budget. -/
theorem hasStraightTargetPath_of_lipschitz [CompleteSpace E]
    (v : E → E) (x₀ : E) (a L K : NNReal)
    (hbound : ∀ x ∈ closedBall x₀ a, ‖v x‖ ≤ (L : ℝ))
    (hlipschitz : LipschitzOnWith K v (closedBall x₀ a))
    (hmargin : L ≤ a) :
    HasStraightTargetPath (closedBall x₀ a) v x₀ := by
  let tzero : Icc (0 : ℝ) 1 := ⟨0, left_mem_Icc.mpr zero_le_one⟩
  have hpl : IsPicardLindelof (fun _ : ℝ => v) tzero x₀ a 0 L K := by
    apply IsPicardLindelof.of_time_independent hbound hlipschitz
    simpa [tzero] using hmargin
  simpa [tzero] using hasStraightTargetPath_of_picard v x₀ a L K hpl

/-- Along a path solving `ξ' = v(ξ)`, the identity `DM(ξ)v(ξ)=τ` forces
the moment map to move on the exact straight target `M(x₀)+tτ`. -/
theorem straight_target_chain_rule
    (Ω : Set E) (v : E → E) (M : E → Y)
    (J : E → E →L[ℝ] Y) (x₀ : E) (τ : Y)
    (hpath : HasStraightTargetPath Ω v x₀)
    (hM : ∀ x ∈ Ω, HasFDerivAt M (J x) x)
    (hsolve : ∀ x ∈ Ω, J x (v x) = τ) :
    ∃ ξ : ℝ → E, ξ 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ Ω) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt ξ (v (ξ t)) (Icc (0 : ℝ) 1) t) ∧
      M (ξ 1) = M x₀ + τ := by
  obtain ⟨ξ, hξzero, hξmem, hξderiv⟩ := hpath
  let F : ℝ → Y := fun t => M (ξ t)
  let G : ℝ → Y := fun t => M (ξ 0) + t • τ
  have hFderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt F τ (Icc (0 : ℝ) 1) t := by
    intro t ht
    have hcomp := (hM (ξ t) (hξmem t ht)).comp_hasDerivWithinAt t (hξderiv t ht)
    simpa only [F, Function.comp_apply, hsolve (ξ t) (hξmem t ht)] using hcomp
  have hGderiv : ∀ t ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt G τ (Icc (0 : ℝ) 1) t := by
    intro t _
    have hlinear : HasDerivAt (fun s : ℝ => s • τ) τ t :=
      by simpa using (hasDerivAt_id t).smul_const τ
    exact hlinear.const_add (M (ξ 0)) |>.hasDerivWithinAt
  have hunique : UniqueDiffOn ℝ (Icc (0 : ℝ) 1) := uniqueDiffOn_Icc zero_lt_one
  have hFG : (Icc (0 : ℝ) 1).EqOn F G := by
    apply (convex_Icc (0 : ℝ) 1).eqOn_of_fderivWithin_eq
        (fun t ht => (hFderiv t ht).differentiableWithinAt)
        (fun t ht => (hGderiv t ht).differentiableWithinAt) hunique
    · intro t ht
      rw [(hFderiv t ht).hasFDerivWithinAt.fderivWithin (hunique t ht),
        (hGderiv t ht).hasFDerivWithinAt.fderivWithin (hunique t ht)]
    · exact left_mem_Icc.mpr zero_le_one
    · simp [F, G]
  refine ⟨ξ, hξzero, hξmem, hξderiv, ?_⟩
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := right_mem_Icc.mpr zero_le_one
  have := hFG hone
  dsimp [F, G] at this
  simpa [hξzero] using this

/-- Packaged nonlinear-fit conclusion: the prechosen closed-ball hypotheses give
an actual Picard path, and the chain rule makes the target displacement exact. -/
theorem straight_target_fit_of_lipschitz [CompleteSpace E]
    (v : E → E) (M : E → Y) (J : E → E →L[ℝ] Y)
    (x₀ : E) (τ : Y) (a L K : NNReal)
    (hbound : ∀ x ∈ closedBall x₀ a, ‖v x‖ ≤ (L : ℝ))
    (hlipschitz : LipschitzOnWith K v (closedBall x₀ a))
    (hmargin : L ≤ a)
    (hM : ∀ x ∈ closedBall x₀ a, HasFDerivAt M (J x) x)
    (hsolve : ∀ x ∈ closedBall x₀ a, J x (v x) = τ) :
    ∃ ξ : ℝ → E, ξ 0 = x₀ ∧
      (∀ t ∈ Icc (0 : ℝ) 1, ξ t ∈ closedBall x₀ a) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt ξ (v (ξ t)) (Icc (0 : ℝ) 1) t) ∧
      M (ξ 1) = M x₀ + τ := by
  exact straight_target_chain_rule (closedBall x₀ a) v M J x₀ τ
    (hasStraightTargetPath_of_lipschitz v x₀ a L K hbound hlipschitz hmargin)
    hM hsolve

end StraightTarget

end Erdos390
