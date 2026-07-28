import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field

/-!
# Exact algebra of the tangent flow

A tangent request replaces weight at `t * a` by the same weight at `s * a`.
This file defines the simultaneous finite update on actual natural-number
coordinates and proves its exact linear invariants.  In particular, the full
valuation of the common multiplier cancels; no squarefreeness or coprimality
assumption on that multiplier is needed.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Real point mass at one natural-number coordinate. -/
def tangentPointMass (b a : ℕ) : ℝ :=
  if a = b then 1 else 0

/-- The signed coordinate change made by finitely many directed requests. -/
def tangentDelta {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (a : ℕ) : ℝ :=
  ∑ e ∈ requests, weight e *
    (tangentPointMass (source e * multiplier e) a -
      tangentPointMass (target e * multiplier e) a)

/-- Apply all tangent requests to a selector. -/
def tangentUpdate {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (a : ℕ) : ℝ :=
  x a + tangentDelta requests source target multiplier weight a

theorem sum_tangentPointMass_mul
    {A : Finset ℕ} {b : ℕ} (hb : b ∈ A) (value : ℕ → ℝ) :
    ∑ a ∈ A, tangentPointMass b a * value a = value b := by
  rw [Finset.sum_eq_single b]
  · simp [tangentPointMass]
  · intro a ha hab
    simp [tangentPointMass, hab]
  · exact fun hnot ↦ (hnot hb).elim

/-- Master finite-sum identity: testing the coordinate update against any
function gives the directed endpoint difference for every request. -/
theorem tangentDelta_weightedSum
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (A : Finset ℕ) (value : ℕ → ℝ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A) :
    ∑ a ∈ A,
        tangentDelta requests source target multiplier weight a * value a =
      ∑ e ∈ requests, weight e *
        (value (source e * multiplier e) -
          value (target e * multiplier e)) := by
  simp only [tangentDelta, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  calc
    (∑ a ∈ A,
        weight e *
            (tangentPointMass (source e * multiplier e) a -
              tangentPointMass (target e * multiplier e) a) * value a) =
        weight e *
            (∑ a ∈ A,
              tangentPointMass (source e * multiplier e) a * value a) -
          weight e *
            (∑ a ∈ A,
              tangentPointMass (target e * multiplier e) a * value a) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _ha
      ring
    _ = weight e *
        (value (source e * multiplier e) -
          value (target e * multiplier e)) := by
      rw [sum_tangentPointMass_mul (hsource e he) value,
        sum_tangentPointMass_mul (htarget e he) value]
      ring

/-- Weighted sums after the update equal the old sums plus the request
boundary tested against the same function. -/
theorem tangentUpdate_weightedSum
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (value : ℕ → ℝ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A) :
    ∑ a ∈ A,
        tangentUpdate requests source target multiplier weight x a * value a =
      (∑ a ∈ A, x a * value a) +
        ∑ e ∈ requests, weight e *
          (value (source e * multiplier e) -
            value (target e * multiplier e)) := by
  simp only [tangentUpdate, add_mul, Finset.sum_add_distrib]
  rw [tangentDelta_weightedSum requests source target multiplier weight A
    value hsource htarget]

/-- The complete factorization vector of the common multiplier cancels. -/
theorem tangent_endpoint_factorization_sub
    {source target multiplier p : ℕ}
    (hsource : source ≠ 0) (htarget : target ≠ 0)
    (hmultiplier : multiplier ≠ 0) :
    (((source * multiplier).factorization p : ℕ) : ℝ) -
        (((target * multiplier).factorization p : ℕ) : ℝ) =
      (source.factorization p : ℝ) - (target.factorization p : ℝ) := by
  rw [Nat.factorization_mul hsource hmultiplier,
    Nat.factorization_mul htarget hmultiplier]
  simp only [Finsupp.add_apply, Nat.cast_add]
  ring

/-- Exact valuation update, expressed only through source and target labels. -/
theorem tangentUpdate_valuation
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (p : ℕ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, source e ≠ 0)
    (htargetPos : ∀ e ∈ requests, target e ≠ 0)
    (hmultiplierPos : ∀ e ∈ requests, multiplier e ≠ 0) :
    ∑ a ∈ A,
        tangentUpdate requests source target multiplier weight x a *
          (a.factorization p : ℝ) =
      (∑ a ∈ A, x a * (a.factorization p : ℝ)) +
        ∑ e ∈ requests, weight e *
          ((source e).factorization p - (target e).factorization p : ℝ) := by
  rw [tangentUpdate_weightedSum requests source target multiplier weight x A
    (fun a ↦ (a.factorization p : ℝ)) hsourceMem htargetMem]
  apply congrArg (fun z : ℝ ↦ (∑ a ∈ A, x a * (a.factorization p : ℝ)) + z)
  apply Finset.sum_congr rfl
  intro e he
  rw [tangent_endpoint_factorization_sub
    (hsourcePos e he) (htargetPos e he) (hmultiplierPos e he)]

/-- If the directed label boundary is the residual valuation vector, the
updated selector has the exact target valuation. -/
theorem tangentUpdate_valuation_eq_target
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (targetValuation : ℕ → ℝ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, source e ≠ 0)
    (htargetPos : ∀ e ∈ requests, target e ≠ 0)
    (hmultiplierPos : ∀ e ∈ requests, multiplier e ≠ 0)
    (hboundary : ∀ p : ℕ,
      ∑ e ∈ requests, weight e *
          ((source e).factorization p - (target e).factorization p : ℝ) =
        targetValuation p -
          ∑ a ∈ A, x a * (a.factorization p : ℝ)) :
    ∀ p : ℕ,
      ∑ a ∈ A,
          tangentUpdate requests source target multiplier weight x a *
            (a.factorization p : ℝ) = targetValuation p := by
  intro p
  rw [tangentUpdate_valuation requests source target multiplier weight x A p
    hsourceMem htargetMem hsourcePos htargetPos hmultiplierPos,
    hboundary p]
  ring

/-- Every request preserves the total selector mass. -/
theorem tangentUpdate_mass
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A) :
    ∑ a ∈ A,
        tangentUpdate requests source target multiplier weight x a =
      ∑ a ∈ A, x a := by
  have hsum := tangentUpdate_weightedSum requests source target multiplier
    weight x A (fun _ ↦ 1) hsource htarget
  simpa using hsum

/-- Staying in the same complete-signature row preserves its exact row sum. -/
theorem tangentUpdate_signatureRow
    {ι σ : Type*} [DecidableEq σ]
    (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ) (signature : ℕ → σ) (row : σ)
    (hsource : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htarget : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsame : ∀ e ∈ requests,
      signature (source e * multiplier e) =
        signature (target e * multiplier e)) :
    ∑ a ∈ A.filter (fun a ↦ signature a = row),
        tangentUpdate requests source target multiplier weight x a =
      ∑ a ∈ A.filter (fun a ↦ signature a = row), x a := by
  let indicator : ℕ → ℝ := fun a ↦
    if signature a = row then 1 else 0
  have hweighted := tangentUpdate_weightedSum requests source target multiplier
    weight x A indicator hsource htarget
  have hboundary :
      ∑ e ∈ requests, weight e *
        (indicator (source e * multiplier e) -
          indicator (target e * multiplier e)) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    simp only [indicator, hsame e he, sub_self, mul_zero]
  rw [hboundary, add_zero] at hweighted
  simpa only [indicator, Finset.sum_filter, ite_mul, mul_ite, one_mul,
    mul_one, zero_mul, mul_zero]
    using hweighted

/-- The ordinary logarithm of a common multiplier cancels exactly. -/
theorem tangent_endpoint_log_sub
    {source target multiplier : ℕ}
    (hsource : 0 < source) (htarget : 0 < target)
    (hmultiplier : 0 < multiplier) :
    Real.log ((source * multiplier : ℕ) : ℝ) -
        Real.log ((target * multiplier : ℕ) : ℝ) =
      Real.log (source : ℝ) - Real.log (target : ℝ) := by
  push_cast
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)]
  ring

/-- A prime-log balanced directed flow preserves the ordinary logarithmic
sum of the selector. -/
theorem tangentUpdate_log
    {ι : Type*} (requests : Finset ι)
    (source target multiplier : ι → ℕ) (weight : ι → ℝ)
    (x : ℕ → ℝ) (A : Finset ℕ)
    (hsourceMem : ∀ e ∈ requests, source e * multiplier e ∈ A)
    (htargetMem : ∀ e ∈ requests, target e * multiplier e ∈ A)
    (hsourcePos : ∀ e ∈ requests, 0 < source e)
    (htargetPos : ∀ e ∈ requests, 0 < target e)
    (hmultiplierPos : ∀ e ∈ requests, 0 < multiplier e)
    (hlogBalance :
      ∑ e ∈ requests, weight e *
        (Real.log (source e : ℝ) - Real.log (target e : ℝ)) = 0) :
    ∑ a ∈ A,
        tangentUpdate requests source target multiplier weight x a *
          Real.log (a : ℝ) =
      ∑ a ∈ A, x a * Real.log (a : ℝ) := by
  rw [tangentUpdate_weightedSum requests source target multiplier weight x A
    (fun a ↦ Real.log (a : ℝ)) hsourceMem htargetMem]
  have hendpoint :
      (∑ e ∈ requests, weight e *
        (Real.log ((source e * multiplier e : ℕ) : ℝ) -
          Real.log ((target e * multiplier e : ℕ) : ℝ))) =
        ∑ e ∈ requests, weight e *
          (Real.log (source e : ℝ) - Real.log (target e : ℝ)) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [tangent_endpoint_log_sub
      (hsourcePos e he) (htargetPos e he) (hmultiplierPos e he)]
  rw [hendpoint, hlogBalance, add_zero]

end

end Erdos390.WholePaper
