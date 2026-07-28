import Erdos390.Full.NuisanceCovariance

/-!
# Constructing affine-spanning certificates

The nuisance gap only needs the explicit cell-pattern differences to span
the nuisance space.  This file turns that checkable kernel statement into
the continuous reconstruction map required by `AffineSpanningCertificate`.
-/

namespace Erdos390.Full

noncomputable section

namespace PatternMixture

variable {Cell Nuisance : Type*} [Fintype Cell]
  [NormedAddCommGroup Nuisance] [InnerProductSpace ℝ Nuisance]

theorem pairDifferenceAnalysis_eq_zero_iff
    (mix : PatternMixture Cell Nuisance) (x : Nuisance) :
    mix.pairDifferenceAnalysis x = 0 ↔
      ∀ i j, inner ℝ x (mix.pattern i - mix.pattern j) = 0 := by
  constructor
  · intro hzero i j
    have hcoord := congrArg
      (fun z : EuclideanSpace ℝ (Cell × Cell) ↦
        (EuclideanSpace.equiv (Cell × Cell) ℝ z) (i, j)) hzero
    simpa [mix.pairDifferenceAnalysis_apply x (i, j), real_inner_comm] using hcoord
  · intro horth
    apply (EuclideanSpace.equiv (Cell × Cell) ℝ).injective
    funext ij
    simpa [mix.pairDifferenceAnalysis_apply x ij, real_inner_comm]
      using horth ij.1 ij.2

/-- A purely affine-spanning kernel check yields the reconstruction
certificate.  No covariance inequality is assumed. -/
theorem exists_affineSpanningCertificate_of_kernel
    (mix : PatternMixture Cell Nuisance)
    (hkernel : ∀ x,
      (∀ i j, inner ℝ x (mix.pattern i - mix.pattern j) = 0) → x = 0) :
    Nonempty (AffineSpanningCertificate mix) := by
  have hinj : Function.Injective mix.pairDifferenceAnalysis := by
    intro x y hxy
    have hzero : mix.pairDifferenceAnalysis (x - y) = 0 := by
      rw [map_sub, hxy, sub_self]
    have hsub : x - y = 0 :=
      hkernel (x - y) ((mix.pairDifferenceAnalysis_eq_zero_iff (x - y)).mp hzero)
    exact sub_eq_zero.mp hsub
  have hker : mix.pairDifferenceAnalysis.toLinearMap.ker = ⊥ :=
    LinearMap.ker_eq_bot.mpr hinj
  obtain ⟨g, hg⟩ :=
    LinearMap.exists_leftInverse_of_injective
      mix.pairDifferenceAnalysis.toLinearMap hker
  let gcont : EuclideanSpace ℝ (Cell × Cell) →L[ℝ] Nuisance :=
    LinearMap.toContinuousLinearMap g
  refine ⟨⟨gcont, ?_⟩⟩
  ext x
  have hx := LinearMap.congr_fun hg x
  simpa [gcont] using hx

end PatternMixture

end

end Erdos390.Full
