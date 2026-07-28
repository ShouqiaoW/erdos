import Erdos390.Full.EquivalentNormODE
import Erdos390.Full.PaperBridgeFit

/-!
# The concrete effective parameter norm of Proposition 8.7

The paper controls a parameter by three quantities: the largest effective
prime fugacity, the Euclidean nuisance block, and the scaled slow parameter
`w * lambda`.  The slow coordinate of `BridgeData.ParamSpace` is already
`w * lambda`.  We therefore map the actual parameter space injectively into
the product of these three normed spaces and use the norm inherited by the
range.  This gives a genuine complete finite-dimensional normed space and a
continuous linear equivalence back to the original parameter space, exactly
the input required by `EquivalentNormODE`.
-/

open scoped BigOperators
open Metric Set

namespace Erdos390.Full.PaperBridgeFit
namespace BridgeData

open ArithmeticBandGeometry

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The full band coefficient reconstructed from the quotient gauge. -/
def bandParameter (xi : B.ParamSpace) (j : Band) : ℝ :=
  if h : j = B.lowBand then
    -∑ k : B.GaugeIndex,
      B.lowRatio k * xi (MomentCoord.gauge k)
  else
    xi (MomentCoord.gauge ⟨j, h⟩)

@[simp]
theorem bandParameter_gauge (xi : B.ParamSpace) (j : B.GaugeIndex) :
    B.bandParameter xi j.1 = xi (MomentCoord.gauge j) := by
  simp [bandParameter, j.2]

@[simp]
theorem bandParameter_low (xi : B.ParamSpace) :
    B.bandParameter xi B.lowBand =
      -∑ k : B.GaugeIndex,
        B.lowRatio k * xi (MomentCoord.gauge k) := by
  simp [bandParameter]

theorem bandParameter_add (x y : B.ParamSpace) (j : Band) :
    B.bandParameter (x + y) j =
      B.bandParameter x j + B.bandParameter y j := by
  by_cases h : j = B.lowBand
  · simp only [bandParameter, h, ↓reduceDIte, PiLp.add_apply]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    ring
  · simp [bandParameter, h]

theorem bandParameter_smul (a : ℝ) (x : B.ParamSpace) (j : Band) :
    B.bandParameter (a • x) j = a * B.bandParameter x j := by
  by_cases h : j = B.lowBand
  · simp only [bandParameter, h, ↓reduceDIte, PiLp.smul_apply, smul_eq_mul]
    rw [mul_neg]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  · simp [bandParameter, h, smul_eq_mul]

/-- The literal coefficient of `v_p` in the exponent represented by `xi`.
The division by `w` converts the stored slow coordinate back to `lambda`. -/
def effectivePrimeCoefficient (xi : B.ParamSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) : ℝ :=
  B.bandParameter xi (B.partition.band p) +
    (xi MomentCoord.slow / B.w) * B.primeDeviation p

theorem effectivePrimeCoefficient_add (x y : B.ParamSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (x + y) p =
      B.effectivePrimeCoefficient x p +
        B.effectivePrimeCoefficient y p := by
  simp only [effectivePrimeCoefficient, B.bandParameter_add, PiLp.add_apply,
    add_div]
  ring

theorem effectivePrimeCoefficient_smul (a : ℝ) (x : B.ParamSpace)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    B.effectivePrimeCoefficient (a • x) p =
      a * B.effectivePrimeCoefficient x p := by
  simp only [effectivePrimeCoefficient, B.bandParameter_smul,
    PiLp.smul_apply, smul_eq_mul]
  field_simp [ne_of_gt B.w_pos]

/-- The physical/head block extracted from an actual parameter. -/
def nuisanceParameter (xi : B.ParamSpace) : B.NuisanceSpace :=
  (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).symm
    (fun c => match c with
      | .physical => xi MomentCoord.physical
      | .head h => xi (MomentCoord.head h))

@[simp]
theorem nuisanceParameter_physical (xi : B.ParamSpace) :
    B.nuisanceParameter xi NuisanceCoord.physical =
      xi MomentCoord.physical := rfl

@[simp]
theorem nuisanceParameter_head (xi : B.ParamSpace) (h : B.HeadIndex) :
    B.nuisanceParameter xi (NuisanceCoord.head h) =
      xi (MomentCoord.head h) := rfl

/-- Product space carrying the max versions of the three effective
coordinates.  Its norm is uniformly equivalent (within a factor three) to
the sum convention used in the paper. -/
abbrev EffectiveAmbient :=
  (((BandPrime B.sampleData.n B.sampleData.W → ℝ) × B.NuisanceSpace) × ℝ)

def effectiveCoordinateLinearMap : B.ParamSpace →ₗ[ℝ] B.EffectiveAmbient where
  toFun xi :=
    (((fun p => B.effectivePrimeCoefficient xi p), B.nuisanceParameter xi),
      xi MomentCoord.slow)
  map_add' x y := by
    apply Prod.ext
    · apply Prod.ext
      · funext p
        exact B.effectivePrimeCoefficient_add x y p
      · apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
        funext c
        cases c <;> rfl
    · rfl
  map_smul' a x := by
    apply Prod.ext
    · apply Prod.ext
      · funext p
        exact B.effectivePrimeCoefficient_smul a x p
      · apply (EuclideanSpace.equiv (NuisanceCoord B.HeadIndex) ℝ).injective
        funext c
        cases c <;> rfl
    · rfl

@[simp]
theorem effectiveCoordinateLinearMap_apply (xi : B.ParamSpace) :
    B.effectiveCoordinateLinearMap xi =
      (((fun p => B.effectivePrimeCoefficient xi p), B.nuisanceParameter xi),
        xi MomentCoord.slow) := rfl

theorem effectiveCoordinateLinearMap_injective :
    Function.Injective B.effectiveCoordinateLinearMap := by
  intro x y hxy
  apply (EuclideanSpace.equiv B.Coord ℝ).injective
  funext c
  have hslow : x MomentCoord.slow = y MomentCoord.slow :=
    congrArg (fun z : B.EffectiveAmbient => z.2) hxy
  cases c with
  | slow => exact hslow
  | physical =>
      have h := congrArg
        (fun z : B.EffectiveAmbient => z.1.2 NuisanceCoord.physical) hxy
      exact h
  | head h =>
      have hz := congrArg
        (fun z : B.EffectiveAmbient => z.1.2 (NuisanceCoord.head h)) hxy
      exact hz
  | gauge j =>
      obtain ⟨p, hp⟩ := B.partition.fiber_nonempty j.1
      have hpBand : B.partition.band p = j.1 := hp
      have hpEq := congrArg
        (fun z : B.EffectiveAmbient => z.1.1 p) hxy
      simp only [effectiveCoordinateLinearMap_apply,
        effectivePrimeCoefficient, hpBand, B.bandParameter_gauge] at hpEq
      rw [hslow] at hpEq
      exact add_right_cancel hpEq

/-- Continuous version of the concrete effective-coordinate injection. -/
def effectiveCoordinateCLM : B.ParamSpace →L[ℝ] B.EffectiveAmbient :=
  B.effectiveCoordinateLinearMap.toContinuousLinearMap

theorem effectiveCoordinateCLM_injective :
    Function.Injective B.effectiveCoordinateCLM :=
  B.effectiveCoordinateLinearMap_injective

/-- The effective parameter space is the closed range of the concrete
coordinate map. -/
abbrev EffectiveParamSpace :=
  LinearMap.range B.effectiveCoordinateCLM.toLinearMap

theorem effectiveCoordinateCLM_range_closed :
    IsClosed (Set.range B.effectiveCoordinateCLM) := by
  have hker : LinearMap.ker B.effectiveCoordinateCLM.toLinearMap = ⊥ :=
    LinearMap.ker_eq_bot.mpr B.effectiveCoordinateCLM_injective
  exact (LinearMap.isClosedEmbedding_of_injective hker).isClosed_range

/-- Continuous linear equivalence from the effective normed space back to
the original Euclidean parameter space. -/
def effectiveParamEquiv : B.EffectiveParamSpace ≃L[ℝ] B.ParamSpace :=
  (B.effectiveCoordinateCLM.equivRange
    B.effectiveCoordinateCLM_injective
    B.effectiveCoordinateCLM_range_closed).symm

/-- The sum convention used in the paper: largest prime fugacity, nuisance
norm, and the stored slow coordinate `w * lambda`. -/
def paperEffectiveSize (xi : B.ParamSpace) : ℝ :=
  ‖fun p => B.effectivePrimeCoefficient xi p‖ +
    ‖B.nuisanceParameter xi‖ + |xi MomentCoord.slow|

theorem paperEffectiveSize_nonneg (xi : B.ParamSpace) :
    0 ≤ B.paperEffectiveSize xi := by
  unfold paperEffectiveSize
  positivity

/-- The inherited range norm is exactly the maximum of the three paper
coordinates. -/
theorem norm_effectiveCoordinateCLM_eq (xi : B.ParamSpace) :
    ‖B.effectiveCoordinateCLM xi‖ =
      max (max ‖fun p => B.effectivePrimeCoefficient xi p‖
        ‖B.nuisanceParameter xi‖) |xi MomentCoord.slow| := by
  rfl

/-- The max norm is bounded by the paper's sum convention. -/
theorem norm_effectiveCoordinateCLM_le_paperEffectiveSize
    (xi : B.ParamSpace) :
    ‖B.effectiveCoordinateCLM xi‖ ≤ B.paperEffectiveSize xi := by
  rw [B.norm_effectiveCoordinateCLM_eq]
  unfold paperEffectiveSize
  apply max_le
  · apply max_le
    · linarith [norm_nonneg (fun p => B.effectivePrimeCoefficient xi p),
        norm_nonneg (B.nuisanceParameter xi),
        abs_nonneg (xi MomentCoord.slow)]
    · linarith [norm_nonneg (fun p => B.effectivePrimeCoefficient xi p),
        norm_nonneg (B.nuisanceParameter xi),
        abs_nonneg (xi MomentCoord.slow)]
  · linarith [norm_nonneg (fun p => B.effectivePrimeCoefficient xi p),
      norm_nonneg (B.nuisanceParameter xi),
      abs_nonneg (xi MomentCoord.slow)]

/-- Conversely the paper's sum convention is at most three times the max
norm.  The constant is absolute and independent of the number of bands. -/
theorem paperEffectiveSize_le_three_mul_norm_effectiveCoordinateCLM
    (xi : B.ParamSpace) :
    B.paperEffectiveSize xi ≤ 3 * ‖B.effectiveCoordinateCLM xi‖ := by
  let a := ‖fun p => B.effectivePrimeCoefficient xi p‖
  let b := ‖B.nuisanceParameter xi‖
  let c := |xi MomentCoord.slow|
  let m := max (max a b) c
  have ha : a ≤ m := le_trans (le_max_left _ _) (le_max_left _ _)
  have hb : b ≤ m := le_trans (le_max_right _ _) (le_max_left _ _)
  have hc : c ≤ m := le_max_right _ _
  have hm : ‖B.effectiveCoordinateCLM xi‖ = m := by
    simpa only [a, b, c, m] using B.norm_effectiveCoordinateCLM_eq xi
  unfold paperEffectiveSize
  dsimp only [a, b, c] at ha hb hc
  rw [hm]
  linarith

@[simp]
theorem effectiveCoordinateCLM_effectiveParamEquiv
    (z : B.EffectiveParamSpace) :
    B.effectiveCoordinateCLM (B.effectiveParamEquiv z) = z.1 := by
  have h := B.effectiveParamEquiv.symm_apply_apply z
  exact congrArg Subtype.val h

@[simp]
theorem norm_effectiveParamEquiv_symm (xi : B.ParamSpace) :
    ‖B.effectiveParamEquiv.symm xi‖ =
      ‖B.effectiveCoordinateCLM xi‖ := by
  rfl

/-- A radius in the inherited effective max norm implies the literal paper
box with radius three times as large.  This is the dimension-free conversion
used in the non-circular ODE argument. -/
theorem paperEffectiveSize_effectiveParamEquiv_le
    (z : B.EffectiveParamSpace) :
    B.paperEffectiveSize (B.effectiveParamEquiv z) ≤ 3 * ‖z‖ := by
  calc
    B.paperEffectiveSize (B.effectiveParamEquiv z)
        ≤ 3 * ‖B.effectiveCoordinateCLM (B.effectiveParamEquiv z)‖ :=
      B.paperEffectiveSize_le_three_mul_norm_effectiveCoordinateCLM _
    _ = 3 * ‖z‖ := by
      rw [B.effectiveCoordinateCLM_effectiveParamEquiv]
      rfl

/-! ## Non-circular ODE transport in the literal paper norm -/

/-- The finite exponential-family ODE on a ball chosen in the effective
paper norm.  The path is constructed, remains in the preselected box, and
has the exact raw endpoint.  The two analytic hypotheses are deliberately
stated on that same preselected ball so a later theorem can discharge them
from Lemmas 8.4--8.6 without changing norms or choosing a box a posteriori. -/
theorem exists_paperFit_on_preselectedEffectiveBall [Nonempty Head]
    (Delta : Band → ℝ) (a speed : NNReal) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gamma (B.effectiveParamEquiv z))
    (hbound : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta)
          (B.effectiveParamEquiv z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      ∀ c : B.Coord,
        B.paperMoment (fun m => B.rawStatistic m c) (path 1) =
          B.paperMoment (fun m => B.rawStatistic m c) 0 +
            B.unscaledTarget Delta c := by
  obtain ⟨path, hzero, hball, hderiv, hend⟩ :=
    Erdos390.Full.EquivalentNormODE.VectorExponentialFamily.exists_straightTargetLift_on_preselectedEquivalentBall
        B.vectorFamily B.effectiveParamEquiv (0 : B.ParamSpace)
        (B.targetVector Delta) a speed hgamma
        (by simpa using hgap) (by simpa using hbound) hmargin
  have hballZero : ∀ t ∈ Icc (0 : ℝ) 1,
      B.effectiveParamEquiv.symm (path t) ∈
        closedBall (0 : B.EffectiveParamSpace) (a : ℝ) := by
    simpa using hball
  refine ⟨path, hzero, hballZero, ?_, hderiv, ?_⟩
  · intro t ht
    let z : B.EffectiveParamSpace := B.effectiveParamEquiv.symm (path t)
    have hzBall : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) :=
      hballZero t ht
    have hzNorm : ‖z‖ ≤ (a : ℝ) := by
      simpa only [mem_closedBall, dist_zero_right] using hzBall
    have hpath : B.effectiveParamEquiv z = path t := by
      exact B.effectiveParamEquiv.apply_symm_apply (path t)
    rw [← hpath]
    exact (B.paperEffectiveSize_effectiveParamEquiv_le z).trans
      (mul_le_mul_of_nonneg_left hzNorm (by norm_num))
  · exact (B.endpoint_iff_paperMoments Delta 0 (path 1)).mp hend

/-- Exact individual-band endpoint form of the effective-norm ODE. -/
theorem exists_paperFit_allBands_on_preselectedEffectiveBall
    [Nonempty Head]
    (hcompat : B.HasPrimeLogCompatibility)
    (Delta : Band → ℝ) (a speed : NNReal) {gamma : ℝ}
    (hgamma : 0 < gamma)
    (hgap : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      B.vectorFamily.HasCovarianceGap gamma (B.effectiveParamEquiv z))
    (hbound : ∀ z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ),
      ‖B.effectiveParamEquiv.symm
        (B.vectorFamily.vectorField (B.targetVector Delta)
          (B.effectiveParamEquiv z))‖ ≤ (speed : ℝ))
    (hmargin : speed ≤ a) :
    ∃ path : ℝ → B.ParamSpace,
      path 0 = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.effectiveParamEquiv.symm (path t) ∈
          closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        B.paperEffectiveSize (path t) ≤ 3 * (a : ℝ)) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        HasDerivWithinAt path
          (B.vectorFamily.vectorField (B.targetVector Delta) (path t))
          (Icc (0 : ℝ) 1) t) ∧
      ∀ j : Band,
        B.paperMoment (B.bandScore j) (path 1) =
          B.paperMoment (B.bandScore j) 0 + Delta j := by
  obtain ⟨path, hzero, hball, hsize, hderiv, hraw⟩ :=
    B.exists_paperFit_on_preselectedEffectiveBall Delta a speed hgamma
      hgap hbound hmargin
  exact ⟨path, hzero, hball, hsize, hderiv,
    B.rawEndpoint_recovers_all_bandMoments hcompat Delta 0 (path 1) hraw⟩

end

end BridgeData
end Erdos390.Full.PaperBridgeFit
