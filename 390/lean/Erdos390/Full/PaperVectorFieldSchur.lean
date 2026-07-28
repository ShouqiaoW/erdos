import Erdos390.Full.PaperBridgeFit

/-!
# Exact Schur decomposition of the paper vector field

The nonlinear ODE uses the literal vector field

`(D M(xi))^{-1} target`.

This file proves, for the actual finite covariance operator and the actual
paper coordinates, that its main and nuisance coordinate blocks are obtained
by the same exact Schur solve used in Lemmas 8.4 and 8.6.  No inverse estimate,
covariance gap, or marked-row estimate is packaged as data here.  The only
positivity hypotheses are the pointwise gaps needed to make the two displayed
finite linear maps invertible.
-/

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Projection of a paper parameter onto the quotient/slow coordinates. -/
def mainPart (x : B.ParamSpace) : B.MainSpace :=
  (EuclideanSpace.equiv (MainCoord B.GaugeIndex) ℝ).symm
    (fun c => match c with
      | .gauge j => x (MomentCoord.gauge j)
      | .slow => x MomentCoord.slow)

/-- Projection of a paper parameter onto the physical/head coordinates. -/
def nuisancePart (x : B.ParamSpace) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => x MomentCoord.physical
      | .head h => x (MomentCoord.head h))

@[simp] theorem mainPart_gauge (x : B.ParamSpace) (j : B.GaugeIndex) :
    B.mainPart x (MainCoord.gauge j) = x (MomentCoord.gauge j) := rfl

@[simp] theorem mainPart_slow (x : B.ParamSpace) :
    B.mainPart x MainCoord.slow = x MomentCoord.slow := rfl

@[simp] theorem nuisancePart_physical (x : B.ParamSpace) :
    B.nuisancePart x NuisanceCoord.physical = x MomentCoord.physical := rfl

@[simp] theorem nuisancePart_head (x : B.ParamSpace) (h : B.HeadIndex) :
    B.nuisancePart x (NuisanceCoord.head h) = x (MomentCoord.head h) := rfl

/-- The two coordinate projections recombine to the original parameter. -/
theorem combine_mainPart_nuisancePart (x : B.ParamSpace) :
    B.combine (B.mainPart x) (B.nuisancePart x) = x := by
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  cases c <;> simp [combine]

/-- The main coordinate projection is the adjoint of the main inclusion. -/
theorem mainEmbedding_adjoint_apply (x : B.ParamSpace) :
    B.mainEmbeddingCLM.adjoint x = B.mainPart x := by
  apply ext_inner_left ℝ
  intro u
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hx := B.combine_mainPart_nuisancePart x
  change inner ℝ (B.mainEmbed u) x = inner ℝ u (B.mainPart x)
  calc
    inner ℝ (B.mainEmbed u) x =
        inner ℝ (B.mainEmbed u)
          (B.combine (B.mainPart x) (B.nuisancePart x)) := by rw [hx]
    _ = inner ℝ u (B.mainPart x) :=
      B.inner_mainEmbed_combine u (B.mainPart x) (B.nuisancePart x)

/-- The nuisance coordinate projection is the adjoint of the nuisance
inclusion. -/
theorem nuisanceEmbedding_adjoint_apply (x : B.ParamSpace) :
    B.nuisanceEmbeddingCLM.adjoint x = B.nuisancePart x := by
  apply ext_inner_left ℝ
  intro z
  rw [ContinuousLinearMap.adjoint_inner_right]
  have hx := B.combine_mainPart_nuisancePart x
  change inner ℝ (B.nuisanceEmbed z) x = inner ℝ z (B.nuisancePart x)
  calc
    inner ℝ (B.nuisanceEmbed z) x =
        inner ℝ (B.nuisanceEmbed z)
          (B.combine (B.mainPart x) (B.nuisancePart x)) := by rw [hx]
    _ = inner ℝ z (B.nuisancePart x) :=
      B.inner_nuisanceEmbed_combine z (B.nuisancePart x) (B.mainPart x)

/-- The normalized covariance operator sends the actual inverse-Jacobian
vector field to the normalized paper target. -/
theorem covarianceOperator_vectorField [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : B.vectorFamily.HasCovarianceGap gamma xi) :
    B.covarianceOperator xi
        (B.vectorFamily.vectorField (B.targetVector Delta) xi) =
      B.normalizedTarget Delta := by
  rw [covarianceOperator, ContinuousLinearMap.smul_apply,
    B.vectorFamily.jacobian_vectorField (B.targetVector Delta) hgamma hgap]
  rfl

/-- Exact nuisance block of the actual covariance equation. -/
theorem nuisancePart_covarianceOperator_combine [Nonempty Head]
    (xi : B.ParamSpace) (u : B.MainSpace) (z : B.NuisanceSpace) :
    B.nuisancePart (B.covarianceOperator xi (B.combine u z)) =
      B.crossCovarianceOperator xi u +
        B.nuisanceCovarianceOperator xi z := by
  rw [← B.nuisanceEmbedding_adjoint_apply]
  change B.nuisanceEmbeddingCLM.adjoint
      (B.covarianceOperator xi (B.mainEmbed u + B.nuisanceEmbed z)) =
    B.nuisanceEmbeddingCLM.adjoint
        (B.covarianceOperator xi (B.mainEmbed u)) +
      B.nuisanceEmbeddingCLM.adjoint
        (B.covarianceOperator xi (B.nuisanceEmbed z))
  simp only [map_add]

/-- Exact main block after inserting the actual nuisance regression. -/
theorem mainPart_covarianceOperator_schurResidual [Nonempty Head]
    (xi : B.ParamSpace) {gammaNuisance : ℝ}
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (u : B.MainSpace) :
    B.mainPart (B.covarianceOperator xi
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)) =
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u := by
  rw [← B.mainEmbedding_adjoint_apply]
  simp only [exactSchurCovarianceOperator,
    ContinuousLinearMap.comp_apply, B.exactSchurEmbeddingCLM_apply]

@[simp] theorem nuisancePart_normalizedTarget [Nonempty Head]
    (Delta : Band → ℝ) :
    B.nuisancePart (B.normalizedTarget Delta) = 0 := by
  apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
  funext c
  cases c <;> simp [nuisancePart, normalizedTarget, targetVector,
    unscaledTarget, coordScale]

set_option maxHeartbeats 1000000 in
/-- The actual inverse-Jacobian vector field is exactly a Schur residual,
and its main coordinate solves the literal Schur equation. -/
theorem vectorField_eq_schurResidual_and_mainEquation [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z)) :
    let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
    let u := B.mainPart v
    v = B.schurResidual
        (B.exactNuisanceRegression xi hgammaNuisance hGamma) u ∧
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u =
        B.mainPart (B.normalizedTarget Delta) := by
  dsimp only
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  let z := B.nuisancePart v
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hvDecomp : B.combine u z = v := by
    exact B.combine_mainPart_nuisancePart v
  have hsolve : B.covarianceOperator xi v = B.normalizedTarget Delta :=
    B.covarianceOperator_vectorField xi Delta hgammaFull hFull
  have hnuisance :
      B.crossCovarianceOperator xi u +
        B.nuisanceCovarianceOperator xi z = 0 := by
    have h := congrArg B.nuisancePart hsolve
    rw [← hvDecomp, B.nuisancePart_covarianceOperator_combine,
      B.nuisancePart_normalizedTarget] at h
    exact h
  have hz : z = -R u := by
    apply B.nuisanceCovarianceOperator_injective xi hgammaNuisance hGamma
    have hRu : B.nuisanceCovarianceOperator xi (R u) =
        B.crossCovarianceOperator xi u := by
      exact B.exactNuisanceRegression_solve xi hgammaNuisance hGamma u
    rw [map_neg, hRu]
    rw [eq_neg_iff_add_eq_zero]
    calc
      B.nuisanceCovarianceOperator xi z +
          B.crossCovarianceOperator xi u =
        B.crossCovarianceOperator xi u +
          B.nuisanceCovarianceOperator xi z := add_comm _ _
      _ = 0 := hnuisance
  have hvSchur : v = B.schurResidual R u := by
    rw [← hvDecomp, hz]
    rfl
  refine ⟨?_, ?_⟩
  · simpa only [v, u, R] using hvSchur
  · have hmain := congrArg B.mainPart hsolve
    rw [hvSchur,
      B.mainPart_covarianceOperator_schurResidual] at hmain
    simpa only [u, R] using hmain

/-- If the actual Schur operator has been constructed as an equivalence,
the main coordinate of the vector field is its genuine inverse applied to
the genuine normalized target. -/
theorem mainPart_vectorField_eq_exactSchurEquiv_symm [Nonempty Head]
    (xi : B.ParamSpace) (Delta : Band → ℝ)
    {gammaFull gammaNuisance : ℝ}
    (hgammaFull : 0 < gammaFull)
    (hFull : B.vectorFamily.HasCovarianceGap gammaFull xi)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (e : B.MainSpace ≃L[ℝ] B.MainSpace)
    (he : ∀ u, e u =
      B.exactSchurCovarianceOperator xi hgammaNuisance hGamma u) :
    B.mainPart
        (B.vectorFamily.vectorField (B.targetVector Delta) xi) =
      e.symm (B.mainPart (B.normalizedTarget Delta)) := by
  let v := B.vectorFamily.vectorField (B.targetVector Delta) xi
  let u := B.mainPart v
  have hmain :=
    (B.vectorField_eq_schurResidual_and_mainEquation xi Delta
      hgammaFull hFull hgammaNuisance hGamma).2
  have heu : e u = B.mainPart (B.normalizedTarget Delta) := by
    rw [he]
    simpa only [u, v] using hmain
  have := congrArg e.symm heu
  simpa only [e.symm_apply_apply, u, v] using this

/-- A pointwise full covariance gap obtained from the two literal Schur
blocks with a constant which is uniform in the parameter.  The nuisance
regression is the actual finite operator `Gamma_{xi,n}^{-1} B_{xi,n}`;
the only uniformization is the already proved canonical bound for the
cross-covariance operator.  Thus a proposition-level theorem can consume
the nuisance and main/slow gaps separately, without assuming the full
Jacobian gap as an additional analytic input. -/
theorem hasCovarianceGap_of_uniform_exactSchur [Nonempty Head]
    (xi : B.ParamSpace) (gammaMain gammaNuisance : ℝ)
    (hgammaMain : 0 < gammaMain)
    (hgammaNuisance : 0 < gammaNuisance)
    (hGamma : ∀ z, gammaNuisance * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (hSchur : ∀ u, gammaMain * ‖u‖ ^ 2 ≤
      inner ℝ
        (B.schurResidual
          (B.exactNuisanceRegression xi hgammaNuisance hGamma) u)
        (B.covarianceOperator xi
          (B.schurResidual
            (B.exactNuisanceRegression xi hgammaNuisance hGamma) u))) :
    B.vectorFamily.HasCovarianceGap
      (min gammaMain gammaNuisance /
        (3 + 2 * (B.canonicalCrossBound / gammaNuisance) ^ 2)) xi := by
  let R := B.exactNuisanceRegression xi hgammaNuisance hGamma
  have hC : 0 ≤ B.canonicalCrossBound / gammaNuisance :=
    div_nonneg B.canonicalCrossBound_nonneg hgammaNuisance.le
  apply B.hasCovarianceGap_of_schur xi R
    (B.canonicalCrossBound / gammaNuisance)
    gammaMain gammaNuisance hC hgammaMain hgammaNuisance
  · intro u
    dsimp only [R]
    calc
      ‖B.exactNuisanceRegression xi hgammaNuisance hGamma u‖ ≤
          (‖B.crossCovarianceOperator xi‖ / gammaNuisance) * ‖u‖ :=
        B.exactNuisanceRegression_norm_le xi hgammaNuisance hGamma u
      _ ≤ (B.canonicalCrossBound / gammaNuisance) * ‖u‖ := by
        exact mul_le_mul_of_nonneg_right
          (div_le_div_of_nonneg_right
            (B.crossCovarianceOperator_norm_le_canonicalCrossBound xi)
            hgammaNuisance.le)
          (norm_nonneg u)
  · dsimp only [R]
    exact B.exactNuisanceRegression_isRegression
      xi hgammaNuisance hGamma
  · dsimp only [R]
    exact hSchur
  · intro z
    simpa only [nuisanceCovarianceOperator,
      ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.adjoint_inner_right] using hGamma z

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
