import Erdos390.Full.PaperBridgeFit

/-!
# Primewise moment transport along the actual bridge ODE

The paper obtains the post-bridge bound for each marked prime by integrating
the covariance row along the nonlinear moment-fitting path.  This file proves
that passage for the genuine finite exponential family.  It is not an
asymptotic contract: the derivative is the exact covariance derivative of the
finite active moment, and the endpoint estimate is a direct mean-value bound
on the interval `[0,1]`.
-/

open Metric Set

namespace Erdos390.Full

noncomputable section

namespace FiniteExponentialFamily

variable {Omega Param : Type*} [Fintype Omega]
  [NormedAddCommGroup Param] [NormedSpace Real Param]
  [FiniteDimensional Real Param]

/-- Exact endpoint transport for an arbitrary marked statistic.  A bound for
the normalized covariance row along a differentiable path gives the active
moment change with the paper's exact factor `baseMass / scale`.

This is the rigorous finite-dimensional replacement for the phrase
"multiply by `q_n/L` and integrate the marked row along the ODE". -/
theorem abs_moment_path_sub_le_of_covariance_bound
    (fam : FiniteExponentialFamily Omega Param)
    (F : Omega -> Real) (path velocity : Real -> Param) (C : Real)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |fam.covariance F (fun omega => fam.score omega (velocity t))
          (path t)| <= C) :
    |fam.moment F (path 1) - fam.moment F (path 0)| <=
      (fam.baseMass / fam.scale) * C := by
  let momentPath : Real -> Real := fun t => fam.moment F (path t)
  let momentDeriv : Real -> Real := fun t =>
    (fam.baseMass / fam.scale) *
      fam.covariance F (fun omega => fam.score omega (velocity t)) (path t)
  have hderiv : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt momentPath (momentDeriv t) (Icc (0 : Real) 1) t := by
    intro t ht
    have hcomp := (fam.hasFDerivAt_moment_covariance F (path t)).comp_hasDerivWithinAt
      t (hpath t ht)
    simpa only [momentPath, momentDeriv, Function.comp_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul,
      fam.covarianceScore_apply F (path t) (velocity t)] using hcomp
  have hbound : ∀ t ∈ Icc (0 : Real) 1,
      ‖momentDeriv t‖ <= (fam.baseMass / fam.scale) * C := by
    intro t ht
    have hfactor : 0 <= fam.baseMass / fam.scale :=
      div_nonneg (le_of_lt fam.baseMass_positive) (le_of_lt fam.scale_pos)
    simp only [Real.norm_eq_abs, momentDeriv, abs_mul,
      abs_of_nonneg hfactor]
    exact mul_le_mul_of_nonneg_left (hcov t ht) hfactor
  have hmv := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    hderiv hbound (convex_Icc (0 : Real) 1)
    (show (0 : Real) ∈ Icc 0 1 by norm_num)
    (show (1 : Real) ∈ Icc 0 1 by norm_num)
  simpa only [momentPath, Real.norm_eq_abs, sub_zero, norm_one, mul_one]
    using hmv

end FiniteExponentialFamily

namespace PaperBridgeFit

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The actual marked valuation statistic at the natural-number coordinate
represented by a structured sample. -/
def markedValuation (p : Nat) (m : B.sampleData.Sample) : Real :=
  ArithmeticModel.valuation p (B.sampleData.value m)

/-- Exact marked-prime transport along an arbitrary differentiable parameter
path in the concrete bridge family.  The covariance hypothesis is precisely
the row estimate proved by Lemma 8.6; no endpoint estimate is assumed. -/
theorem abs_markedMoment_path_sub_le_of_covariance_bound
    [Nonempty Head]
    (p : Nat) (path velocity : Real -> B.ParamSpace) (C : Real)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m => B.vectorFamily.scalarFamily.score m (velocity t))
          (path t)| <= C) :
    |B.paperMoment (B.markedValuation p) (path 1) -
        B.paperMoment (B.markedValuation p) (path 0)| <=
      (B.q / B.L) * C := by
  have h := B.vectorFamily.scalarFamily.abs_moment_path_sub_le_of_covariance_bound
      (B.markedValuation p) path velocity C hpath hcov
  change |B.paperMoment (B.markedValuation p) (path 1) -
      B.paperMoment (B.markedValuation p) (path 0)| <=
    (B.vectorFamily.baseMass / B.L) * C at h
  rw [B.vectorFamily_baseMass] at h
  exact h

/-- Paper-scaled form of the preceding theorem.  A normalized row
`Cprime / p` changes the actual valuation moment by exactly at most
`q_n Cprime / (p L)`. -/
theorem abs_markedMoment_path_sub_le_div_prime
    [Nonempty Head]
    (p : Nat) (hp : 0 < p)
    (path velocity : Real -> B.ParamSpace) (Cprime : Real)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m => B.vectorFamily.scalarFamily.score m (velocity t))
          (path t)| <= Cprime / (p : Real)) :
    |B.paperMoment (B.markedValuation p) (path 1) -
        B.paperMoment (B.markedValuation p) (path 0)| <=
      B.q * Cprime / ((p : Real) * B.L) := by
  have h := B.abs_markedMoment_path_sub_le_of_covariance_bound
    p path velocity (Cprime / (p : Real)) hpath hcov
  calc
    |B.paperMoment (B.markedValuation p) (path 1) -
          B.paperMoment (B.markedValuation p) (path 0)|
        <= (B.q / B.L) * (Cprime / (p : Real)) := h
    _ = B.q * Cprime / ((p : Real) * B.L) := by
      field_simp [ne_of_gt B.L_pos, by exact_mod_cast hp]

/-- Combination with the pre-bridge marked residual.  This is the exact
finite inequality used at the end of Proposition 8.7: the bridge row adds
its rate constant to the already fixed rough-stage constant, while an upper
bound `q_n <= Cmass * N` converts the active mass to the paper's `N` scale. -/
theorem abs_target_sub_markedMoment_one_le_of_initial_rate
    [Nonempty Head]
    (p : Nat) (hp : 0 < p)
    (path velocity : Real -> B.ParamSpace)
    (target N Cinitial Cmass Crow : Real)
    (hCrow : 0 <= Crow)
    (hq : B.q <= Cmass * N)
    (hpath : ∀ t ∈ Icc (0 : Real) 1,
      HasDerivWithinAt path (velocity t) (Icc (0 : Real) 1) t)
    (hcov : ∀ t ∈ Icc (0 : Real) 1,
      |B.vectorFamily.scalarFamily.covariance
          (B.markedValuation p)
          (fun m => B.vectorFamily.scalarFamily.score m (velocity t))
          (path t)| <= Crow / (p : Real))
    (hinitial :
      |target - B.paperMoment (B.markedValuation p) (path 0)| <=
        Cinitial * N / ((p : Real) * B.L)) :
    |target - B.paperMoment (B.markedValuation p) (path 1)| <=
      (Cinitial + Cmass * Crow) * N / ((p : Real) * B.L) := by
  have htransport := B.abs_markedMoment_path_sub_le_div_prime
    p hp path velocity Crow hpath hcov
  have hden : 0 <= (p : Real) * B.L := by
    exact mul_nonneg (by exact_mod_cast (Nat.zero_le p)) (le_of_lt B.L_pos)
  have hbridge :
      |B.paperMoment (B.markedValuation p) (path 0) -
          B.paperMoment (B.markedValuation p) (path 1)| <=
        (Cmass * N) * Crow / ((p : Real) * B.L) := by
    rw [abs_sub_comm]
    exact htransport.trans
      (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hq hCrow) hden)
  calc
    |target - B.paperMoment (B.markedValuation p) (path 1)| =
        |(target - B.paperMoment (B.markedValuation p) (path 0)) +
          (B.paperMoment (B.markedValuation p) (path 0) -
            B.paperMoment (B.markedValuation p) (path 1))| := by ring_nf
    _ <= |target - B.paperMoment (B.markedValuation p) (path 0)| +
        |B.paperMoment (B.markedValuation p) (path 0) -
          B.paperMoment (B.markedValuation p) (path 1)| := abs_add_le _ _
    _ <= Cinitial * N / ((p : Real) * B.L) +
        (Cmass * N) * Crow / ((p : Real) * B.L) :=
      add_le_add hinitial hbridge
    _ = (Cinitial + Cmass * Crow) * N /
        ((p : Real) * B.L) := by ring

end BridgeData

end PaperBridgeFit

end

end Erdos390.Full
