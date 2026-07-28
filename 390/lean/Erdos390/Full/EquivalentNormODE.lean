import Erdos390.Full.NonlinearFitODE

/-!
# Straight-target continuation in a preselected equivalent norm

The paper controls the nonlinear bridge in an effective norm rather than in
the ambient Euclidean norm.  This file records the exact transport needed for
that argument.  A continuous linear equivalence identifies the effective
parameter space with the original one; Picard--Lindelof is run on the closed
ball in the effective space, and the resulting path is then mapped back.

The theorem below constructs the path.  In particular it does not assume an
integral curve or a continuation principle.  Its hypotheses are precisely the
boxwise smoothness, speed, derivative, and solve identities that the arithmetic
Schur analysis supplies.
-/

open Metric Set

namespace Erdos390.Full.EquivalentNormODE

noncomputable section

section GenericTransport

variable {E F Y : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- Non-circular straight-target lift in a norm transported by a continuous
linear equivalence.  The radius and every hypothesis on its closed ball are
fixed before the path is constructed. -/
theorem exists_straightTargetLift_on_preselectedEquivalentBall
    (e : F ≃L[ℝ] E)
    (v : E → E) (M : E → Y) (J : E → E →L[ℝ] Y)
    (x0 : E) (target : Y) (a speed : NNReal)
    (hsmooth : ContDiffOn ℝ 1
      (fun z : F => e.symm (v (e z)))
      (closedBall (e.symm x0) (a : ℝ)))
    (hbound : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      ‖e.symm (v (e z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a)
    (hM : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      HasFDerivAt M (J (e z)) (e z))
    (hsolve : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      J (e z) (v (e z)) = target) :
    ∃ path : ℝ → E,
      path 0 = x0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        e.symm (path t) ∈ closedBall (e.symm x0) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path (v (path t)) (Icc (0 : ℝ) 1) t) ∧
      M (path 1) = M x0 + target := by
  let vF : F → F := fun z => e.symm (v (e z))
  let MF : F → Y := fun z => M (e z)
  let JF : F → F →L[ℝ] Y := fun z => (J (e z)).comp e.toContinuousLinearMap
  obtain ⟨K, hK⟩ := hsmooth.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall (e.symm x0) (a : ℝ))
    (isCompact_closedBall (e.symm x0) (a : ℝ))
  have hMF : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      HasFDerivAt MF (JF z) z := by
    intro z hz
    simpa only [MF, JF] using
      (hM z hz).comp z e.hasFDerivAt
  have hsolveF : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      JF z (vF z) = target := by
    intro z hz
    simpa [JF, vF] using hsolve z hz
  obtain ⟨pathF, hzero, hball, hderiv, hend⟩ :=
    Erdos390.straight_target_fit_of_lipschitz
      vF MF JF (e.symm x0) target a speed K
      (by simpa only [vF] using hbound) hK hmargin hMF hsolveF
  let path : ℝ → E := fun t => e (pathF t)
  refine ⟨path, ?_, ?_, ?_, ?_⟩
  · simp only [path, hzero, ContinuousLinearEquiv.apply_symm_apply]
  · intro t ht
    simpa only [path, ContinuousLinearEquiv.symm_apply_apply] using hball t ht
  · intro t ht
    have hcomp := e.hasFDerivAt.comp_hasDerivWithinAt t (hderiv t ht)
    simpa [path, vF] using hcomp
  · simpa only [path, MF, ContinuousLinearEquiv.apply_symm_apply] using hend

end GenericTransport

namespace VectorExponentialFamily

variable {Omega E F : Type*} [Fintype Omega]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [FiniteDimensional ℝ F]

/-- Effective-norm continuation for the actual finite exponential family.
The covariance gap proves both Jacobian inversion and local smoothness.  The
only additional quantitative input is the effective velocity bound on the
box; the path, its confinement, and the exact endpoint are conclusions. -/
theorem exists_straightTargetLift_on_preselectedEquivalentBall
    (vf : Erdos390.Full.VectorExponentialFamily Omega E)
    (e : F ≃L[ℝ] E) (x0 target : E) (a speed : NNReal)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      vf.HasCovarianceGap gamma (e z))
    (hbound : ∀ z ∈ closedBall (e.symm x0) (a : ℝ),
      ‖e.symm (vf.vectorField target (e z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a) :
    ∃ path : ℝ → E,
      path 0 = x0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        e.symm (path t) ∈ closedBall (e.symm x0) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (vf.vectorField target (path t)) (Icc (0 : ℝ) 1) t) ∧
      vf.vectorMoment (path 1) = vf.vectorMoment x0 + target := by
  have hsmooth : ContDiffOn ℝ 1
      (fun z : F => e.symm (vf.vectorField target (e z)))
      (closedBall (e.symm x0) (a : ℝ)) := by
    intro z hz
    have hv : ContDiffAt ℝ 1 (vf.vectorField target) (e z) :=
      vf.vectorField_contDiffAt target hgamma (hgap z hz)
    have hinner : ContDiffAt ℝ 1
        (fun y : F => vf.vectorField target (e y)) z :=
      hv.comp z e.contDiff.contDiffAt
    exact (e.symm.contDiff.contDiffAt.comp z hinner).contDiffWithinAt
  exact Erdos390.Full.EquivalentNormODE.exists_straightTargetLift_on_preselectedEquivalentBall
    e (vf.vectorField target) vf.vectorMoment vf.jacobian x0 target a speed
    hsmooth hbound hmargin
    (fun z _ => vf.hasFDerivAt_vectorMoment (e z))
    (fun z hz => vf.jacobian_vectorField target hgamma (hgap z hz))

end VectorExponentialFamily

end

end Erdos390.Full.EquivalentNormODE
