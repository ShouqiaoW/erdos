import Erdos390.WholePaper.BankPaperFourFiveProductMeasureTelescope
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Fixed-simplex kernels for the four/five chamber

For `m = j - 1`, the paper moves the continuum ordered-prime kernel to the
fixed simplex

`Delta_m = {z_i >= 0, sum z_i <= 1}`

by writing `T = u - j` and `s_i = 1 + T z_i`.  The resulting integrand is

`T^m / (prod_i (1 + T z_i) * (1 + T * (1 - sum_i z_i)))`.

This file defines that expression literally for every finite dimension,
proves its parameter derivative, justifies differentiation under the
compact-simplex integral, and packages the four kernels needed in the
ordered mixture.  On `4.1 <= u <= 4.7`, all relevant parameters satisfy
`0 < T < 3`, so every denominator is bounded away from zero.  Compactness
then supplies one common bound for the mixture and its continuous first
derivative.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## The fixed simplex and its rational integrand -/

/-- The closed `m`-simplex in its usual `m` free coordinates. -/
def fourFiveClosedSimplex (m : Nat) : Set (Fin m -> Real) :=
  {z | (∀ i, 0 <= z i) ∧ (∑ i, z i) <= 1}

theorem isClosed_fourFiveClosedSimplex (m : Nat) :
    IsClosed (fourFiveClosedSimplex m) := by
  have hnonneg : IsClosed {z : Fin m -> Real | ∀ i, 0 <= z i} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun i =>
      isClosed_le continuous_const (continuous_apply i)
  have hsum : IsClosed {z : Fin m -> Real | (∑ i, z i) <= 1} := by
    exact isClosed_le
      (continuous_finset_sum Finset.univ fun i _hi => continuous_apply i)
      continuous_const
  simpa only [fourFiveClosedSimplex, Set.setOf_and] using hnonneg.inter hsum

theorem fourFiveClosedSimplex_subset_Icc (m : Nat) :
    fourFiveClosedSimplex m ⊆
      Set.Icc (0 : Fin m -> Real) (1 : Fin m -> Real) := by
  intro z hz
  constructor
  · intro i
    simpa only [Pi.zero_apply] using hz.1 i
  · intro i
    change z i <= 1
    exact (Finset.single_le_sum (fun k _hk => hz.1 k)
      (Finset.mem_univ i)).trans hz.2

theorem isCompact_fourFiveClosedSimplex (m : Nat) :
    IsCompact (fourFiveClosedSimplex m) :=
  isCompact_Icc.of_isClosed_subset
    (isClosed_fourFiveClosedSimplex m)
    (fourFiveClosedSimplex_subset_Icc m)

/-- Product of the `m` ordinary transformed prime coordinates. -/
def fourFiveSimplexFactorProduct
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  ∏ i, (1 + T * z i)

/-- Derivative of `fourFiveSimplexFactorProduct` in the parameter `T`. -/
def fourFiveSimplexFactorProductDerivative
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  ∑ i ∈ Finset.univ,
    (∏ k ∈ Finset.univ.erase i, (1 + T * z k)) * z i

/-- The final, slack-coordinate factor. -/
def fourFiveSimplexRemainderFactor
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  1 + T * (1 - ∑ i, z i)

/-- Full denominator in the transformed fixed-simplex kernel. -/
def fourFiveSimplexDenominator
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  fourFiveSimplexFactorProduct m T z *
    fourFiveSimplexRemainderFactor m T z

/-- Parameter derivative of the full denominator. -/
def fourFiveSimplexDenominatorDerivative
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  fourFiveSimplexFactorProductDerivative m T z *
      fourFiveSimplexRemainderFactor m T z +
    fourFiveSimplexFactorProduct m T z * (1 - ∑ i, z i)

/-- The paper's transformed fixed-simplex integrand, including its Jacobian
factor `T^m`. -/
def fourFiveFixedSimplexIntegrand
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  T ^ m / fourFiveSimplexDenominator m T z

/-- Explicit first derivative of the transformed integrand in `T`. -/
def fourFiveFixedSimplexIntegrandDerivative
    (m : Nat) (T : Real) (z : Fin m -> Real) : Real :=
  (((m : Real) * T ^ (m - 1)) *
        fourFiveSimplexDenominator m T z -
      T ^ m * fourFiveSimplexDenominatorDerivative m T z) /
    fourFiveSimplexDenominator m T z ^ 2

theorem fourFiveSimplexDenominator_pos
    {m : Nat} {T : Real} {z : Fin m -> Real}
    (hT : 0 <= T) (hz : z ∈ fourFiveClosedSimplex m) :
    0 < fourFiveSimplexDenominator m T z := by
  have hfactor : ∀ i : Fin m, 0 < 1 + T * z i := by
    intro i
    have hmul : 0 <= T * z i := mul_nonneg hT (hz.1 i)
    linarith
  have hprod : 0 < fourFiveSimplexFactorProduct m T z := by
    unfold fourFiveSimplexFactorProduct
    exact Finset.prod_pos fun i _hi => hfactor i
  have hslack : 0 <= 1 - ∑ i, z i := sub_nonneg.mpr hz.2
  have hrem : 0 < fourFiveSimplexRemainderFactor m T z := by
    unfold fourFiveSimplexRemainderFactor
    have := mul_nonneg hT hslack
    linarith
  exact mul_pos hprod hrem

private theorem continuous_fourFiveSimplexDenominator (m : Nat) :
    Continuous (fun p : Real × (Fin m -> Real) =>
      fourFiveSimplexDenominator m p.1 p.2) := by
  unfold fourFiveSimplexDenominator fourFiveSimplexFactorProduct
    fourFiveSimplexRemainderFactor
  fun_prop

private theorem continuous_fourFiveSimplexDenominatorDerivative (m : Nat) :
    Continuous (fun p : Real × (Fin m -> Real) =>
      fourFiveSimplexDenominatorDerivative m p.1 p.2) := by
  unfold fourFiveSimplexDenominatorDerivative
    fourFiveSimplexFactorProductDerivative
    fourFiveSimplexFactorProduct fourFiveSimplexRemainderFactor
  fun_prop

theorem continuousOn_fourFiveFixedSimplexIntegrand (m : Nat) :
    ContinuousOn
      (fun p : Real × (Fin m -> Real) =>
        fourFiveFixedSimplexIntegrand m p.1 p.2)
      (Set.Icc (0 : Real) 3 ×ˢ fourFiveClosedSimplex m) := by
  intro p hp
  have hden : 0 < fourFiveSimplexDenominator m p.1 p.2 :=
    fourFiveSimplexDenominator_pos hp.1.1 hp.2
  apply ContinuousAt.continuousWithinAt
  unfold fourFiveFixedSimplexIntegrand
  exact (continuousAt_fst.pow m).div
    (continuous_fourFiveSimplexDenominator m).continuousAt hden.ne'

theorem continuousOn_fourFiveFixedSimplexIntegrandDerivative (m : Nat) :
    ContinuousOn
      (fun p : Real × (Fin m -> Real) =>
        fourFiveFixedSimplexIntegrandDerivative m p.1 p.2)
      (Set.Icc (0 : Real) 3 ×ˢ fourFiveClosedSimplex m) := by
  intro p hp
  have hden : 0 < fourFiveSimplexDenominator m p.1 p.2 :=
    fourFiveSimplexDenominator_pos hp.1.1 hp.2
  apply ContinuousAt.continuousWithinAt
  unfold fourFiveFixedSimplexIntegrandDerivative
  have hnum : ContinuousAt
      (fun q : Real × (Fin m -> Real) =>
        (((m : Real) * q.1 ^ (m - 1)) *
              fourFiveSimplexDenominator m q.1 q.2 -
            q.1 ^ m *
              fourFiveSimplexDenominatorDerivative m q.1 q.2)) p := by
    exact ((continuousAt_const.mul (continuousAt_fst.pow (m - 1))).mul
      (continuous_fourFiveSimplexDenominator m).continuousAt).sub
        ((continuousAt_fst.pow m).mul
          (continuous_fourFiveSimplexDenominatorDerivative m).continuousAt)
  exact hnum.div
    ((continuous_fourFiveSimplexDenominator m).continuousAt.pow 2)
    (pow_ne_zero 2 hden.ne')

private theorem hasDerivAt_fourFiveSimplexFactorProduct
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    HasDerivAt (fun t => fourFiveSimplexFactorProduct m t z)
      (fourFiveSimplexFactorProductDerivative m T z) T := by
  have hfactor : ∀ i ∈ (Finset.univ : Finset (Fin m)),
      HasDerivAt (fun t : Real => 1 + t * z i) (z i) T := by
    intro i _hi
    convert (hasDerivAt_const T (1 : Real)).add
      ((hasDerivAt_id T).mul_const (z i)) using 1
    ring
  simpa [fourFiveSimplexFactorProduct,
    fourFiveSimplexFactorProductDerivative, smul_eq_mul] using
      (HasDerivAt.fun_finset_prod hfactor)

private theorem hasDerivAt_fourFiveSimplexRemainderFactor
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    HasDerivAt (fun t => fourFiveSimplexRemainderFactor m t z)
      (1 - ∑ i, z i) T := by
  convert (hasDerivAt_const T (1 : Real)).add
    ((hasDerivAt_id T).mul_const (1 - ∑ i, z i)) using 1
  ring

private theorem hasDerivAt_fourFiveSimplexDenominator
    (m : Nat) (T : Real) (z : Fin m -> Real) :
    HasDerivAt (fun t => fourFiveSimplexDenominator m t z)
      (fourFiveSimplexDenominatorDerivative m T z) T := by
  have hp := hasDerivAt_fourFiveSimplexFactorProduct m T z
  have hr := hasDerivAt_fourFiveSimplexRemainderFactor m T z
  simpa [fourFiveSimplexDenominator,
    fourFiveSimplexDenominatorDerivative] using hp.mul hr

theorem hasDerivAt_fourFiveFixedSimplexIntegrand
    {m : Nat} {T : Real} {z : Fin m -> Real}
    (hT : 0 <= T) (hz : z ∈ fourFiveClosedSimplex m) :
    HasDerivAt (fun t => fourFiveFixedSimplexIntegrand m t z)
      (fourFiveFixedSimplexIntegrandDerivative m T z) T := by
  have hpow : HasDerivAt (fun t : Real => t ^ m)
      ((m : Real) * T ^ (m - 1)) T :=
    hasDerivAt_pow m T
  have hden := hasDerivAt_fourFiveSimplexDenominator m T z
  have hdenne : fourFiveSimplexDenominator m T z ≠ 0 :=
    (fourFiveSimplexDenominator_pos hT hz).ne'
  simpa [fourFiveFixedSimplexIntegrand,
    fourFiveFixedSimplexIntegrandDerivative] using
      hpow.div hden hdenne

/-! ## Differentiation under the compact-simplex integral -/

/-- The fixed-simplex continuum kernel in `m` free coordinates. -/
def fourFiveFixedSimplexKernel (m : Nat) (T : Real) : Real :=
  ∫ z in fourFiveClosedSimplex m,
    fourFiveFixedSimplexIntegrand m T z

/-- Integral of the explicit parameter derivative. -/
def fourFiveFixedSimplexKernelDerivative (m : Nat) (T : Real) : Real :=
  ∫ z in fourFiveClosedSimplex m,
    fourFiveFixedSimplexIntegrandDerivative m T z

private theorem integrable_fourFiveFixedSimplexIntegrand
    {m : Nat} {T : Real} (hT : T ∈ Set.Icc (0 : Real) 3) :
    Integrable (fourFiveFixedSimplexIntegrand m T)
      (volume.restrict (fourFiveClosedSimplex m)) := by
  change IntegrableOn (fourFiveFixedSimplexIntegrand m T)
    (fourFiveClosedSimplex m) volume
  apply ContinuousOn.integrableOn_compact
    (isCompact_fourFiveClosedSimplex m)
  exact (continuousOn_fourFiveFixedSimplexIntegrand m).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => ⟨hT, hz⟩)

private theorem integrable_fourFiveFixedSimplexIntegrandDerivative
    {m : Nat} {T : Real} (hT : T ∈ Set.Icc (0 : Real) 3) :
    Integrable (fourFiveFixedSimplexIntegrandDerivative m T)
      (volume.restrict (fourFiveClosedSimplex m)) := by
  change IntegrableOn (fourFiveFixedSimplexIntegrandDerivative m T)
    (fourFiveClosedSimplex m) volume
  apply ContinuousOn.integrableOn_compact
    (isCompact_fourFiveClosedSimplex m)
  exact (continuousOn_fourFiveFixedSimplexIntegrandDerivative m).comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun z hz => ⟨hT, hz⟩)

theorem hasDerivAt_fourFiveFixedSimplexKernel
    {m : Nat} {T : Real} (hT : T ∈ Set.Ioo (0 : Real) 3) :
    HasDerivAt (fourFiveFixedSimplexKernel m)
      (fourFiveFixedSimplexKernelDerivative m T) T := by
  let P : Set (Real × (Fin m -> Real)) :=
    Set.Icc (0 : Real) 3 ×ˢ fourFiveClosedSimplex m
  have hPcompact : IsCompact P :=
    isCompact_Icc.prod (isCompact_fourFiveClosedSimplex m)
  obtain ⟨C, hC⟩ := hPcompact.exists_bound_of_continuousOn
    (continuousOn_fourFiveFixedSimplexIntegrandDerivative m)
  have hsimplexMeas : MeasurableSet (fourFiveClosedSimplex m) :=
    (isClosed_fourFiveClosedSimplex m).measurableSet
  have hnhds : Set.Ioo (0 : Real) 3 ∈ nhds T :=
    Ioo_mem_nhds hT.1 hT.2
  have hresult := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (fourFiveClosedSimplex m))
    (F := fourFiveFixedSimplexIntegrand m)
    (x₀ := T)
    (bound := fun _ : Fin m -> Real => C)
    (s := Set.Ioo (0 : Real) 3) hnhds
    (by
      filter_upwards [hnhds] with t ht
      exact (integrable_fourFiveFixedSimplexIntegrand
        ⟨ht.1.le, ht.2.le⟩).aestronglyMeasurable)
    (integrable_fourFiveFixedSimplexIntegrand
      ⟨hT.1.le, hT.2.le⟩)
    (F' := fourFiveFixedSimplexIntegrandDerivative m)
    (integrable_fourFiveFixedSimplexIntegrandDerivative
      ⟨hT.1.le, hT.2.le⟩).aestronglyMeasurable
    (by
      filter_upwards [ae_restrict_mem hsimplexMeas] with z hz
      intro t ht
      exact hC (t, z) ⟨⟨ht.1.le, ht.2.le⟩, hz⟩)
    (by
      change IntegrableOn (fun _ : Fin m -> Real => C)
        (fourFiveClosedSimplex m) volume
      exact integrableOn_const
        (isCompact_fourFiveClosedSimplex m).measure_ne_top)
    (by
      filter_upwards [ae_restrict_mem hsimplexMeas] with z hz
      intro t ht
      exact hasDerivAt_fourFiveFixedSimplexIntegrand ht.1.le hz)
  simpa [fourFiveFixedSimplexKernel,
    fourFiveFixedSimplexKernelDerivative] using hresult.2

theorem continuousOn_fourFiveFixedSimplexKernelDerivative (m : Nat) :
    ContinuousOn (fourFiveFixedSimplexKernelDerivative m)
      (Set.Icc (0 : Real) 3) := by
  let P : Set (Real × (Fin m -> Real)) :=
    Set.Icc (0 : Real) 3 ×ˢ fourFiveClosedSimplex m
  have hPcompact : IsCompact P :=
    isCompact_Icc.prod (isCompact_fourFiveClosedSimplex m)
  obtain ⟨C, hC⟩ := hPcompact.exists_bound_of_continuousOn
    (continuousOn_fourFiveFixedSimplexIntegrandDerivative m)
  have hsimplexMeas : MeasurableSet (fourFiveClosedSimplex m) :=
    (isClosed_fourFiveClosedSimplex m).measurableSet
  unfold fourFiveFixedSimplexKernelDerivative
  apply continuousOn_of_dominated
    (μ := volume.restrict (fourFiveClosedSimplex m))
    (bound := fun _ : Fin m -> Real => C)
  · intro t ht
    exact (integrable_fourFiveFixedSimplexIntegrandDerivative ht).aestronglyMeasurable
  · intro t ht
    filter_upwards [ae_restrict_mem hsimplexMeas] with z hz
    exact hC (t, z) ⟨ht, hz⟩
  · change IntegrableOn (fun _ : Fin m -> Real => C)
      (fourFiveClosedSimplex m) volume
    exact integrableOn_const
      (isCompact_fourFiveClosedSimplex m).measure_ne_top
  · filter_upwards [ae_restrict_mem hsimplexMeas] with z hz
    exact (continuousOn_fourFiveFixedSimplexIntegrandDerivative m).comp
      (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, hz⟩)

theorem continuousOn_fourFiveFixedSimplexKernel (m : Nat) :
    ContinuousOn (fourFiveFixedSimplexKernel m)
      (Set.Icc ((1 : Real) / 10) ((27 : Real) / 10)) := by
  intro T hT
  have hTopen : T ∈ Set.Ioo (0 : Real) 3 := by
    constructor <;> linarith [hT.1, hT.2]
  exact (hasDerivAt_fourFiveFixedSimplexKernel hTopen).continuousAt.continuousWithinAt

/-! ## The four ordered continuum kernels -/

/-- `j = 1`: no preceding reciprocal-prime coordinate. -/
def fourFiveContinuumKernelOne (u : Real) : Real := u⁻¹

/-- `j = 2`: one-dimensional fixed simplex. -/
def fourFiveContinuumKernelTwo (u : Real) : Real :=
  fourFiveFixedSimplexKernel 1 (u - 2)

/-- `j = 3`: two-dimensional fixed simplex. -/
def fourFiveContinuumKernelThree (u : Real) : Real :=
  fourFiveFixedSimplexKernel 2 (u - 3)

/-- `j = 4`: three-dimensional fixed simplex. -/
def fourFiveContinuumKernelFour (u : Real) : Real :=
  fourFiveFixedSimplexKernel 3 (u - 4)

def fourFiveContinuumKernelOneDerivative (u : Real) : Real :=
  -(u ^ 2)⁻¹

def fourFiveContinuumKernelTwoDerivative (u : Real) : Real :=
  fourFiveFixedSimplexKernelDerivative 1 (u - 2)

def fourFiveContinuumKernelThreeDerivative (u : Real) : Real :=
  fourFiveFixedSimplexKernelDerivative 2 (u - 3)

def fourFiveContinuumKernelFourDerivative (u : Real) : Real :=
  fourFiveFixedSimplexKernelDerivative 3 (u - 4)

theorem hasDerivAt_fourFiveContinuumKernelOne
    {u : Real} (hu : u ≠ 0) :
    HasDerivAt fourFiveContinuumKernelOne
      (fourFiveContinuumKernelOneDerivative u) u := by
  simpa [fourFiveContinuumKernelOne,
    fourFiveContinuumKernelOneDerivative] using hasDerivAt_inv hu

theorem hasDerivAt_fourFiveContinuumKernelTwo
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumKernelTwo
      (fourFiveContinuumKernelTwoDerivative u) u := by
  have hT : u - 2 ∈ Set.Ioo (0 : Real) 3 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := hasDerivAt_fourFiveFixedSimplexKernel (m := 1) hT
  convert h.comp u ((hasDerivAt_id u).sub_const 2) using 1;
    simp [fourFiveContinuumKernelTwoDerivative]

theorem hasDerivAt_fourFiveContinuumKernelThree
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumKernelThree
      (fourFiveContinuumKernelThreeDerivative u) u := by
  have hT : u - 3 ∈ Set.Ioo (0 : Real) 3 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := hasDerivAt_fourFiveFixedSimplexKernel (m := 2) hT
  convert h.comp u ((hasDerivAt_id u).sub_const 3) using 1;
    simp [fourFiveContinuumKernelThreeDerivative]

theorem hasDerivAt_fourFiveContinuumKernelFour
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumKernelFour
      (fourFiveContinuumKernelFourDerivative u) u := by
  have hT : u - 4 ∈ Set.Ioo (0 : Real) 3 := by
    constructor <;> linarith [hu.1, hu.2]
  have h := hasDerivAt_fourFiveFixedSimplexKernel (m := 3) hT
  convert h.comp u ((hasDerivAt_id u).sub_const 4) using 1;
    simp [fourFiveContinuumKernelFourDerivative]

private theorem continuousOn_fourFiveContinuumKernelTwoDerivative :
    ContinuousOn fourFiveContinuumKernelTwoDerivative
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
  unfold fourFiveContinuumKernelTwoDerivative
  exact (continuousOn_fourFiveFixedSimplexKernelDerivative 1).comp
    (continuous_id.sub continuous_const).continuousOn
    (by intro u hu; constructor <;> linarith [hu.1, hu.2])

private theorem continuousOn_fourFiveContinuumKernelThreeDerivative :
    ContinuousOn fourFiveContinuumKernelThreeDerivative
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
  unfold fourFiveContinuumKernelThreeDerivative
  exact (continuousOn_fourFiveFixedSimplexKernelDerivative 2).comp
    (continuous_id.sub continuous_const).continuousOn
    (by intro u hu; constructor <;> linarith [hu.1, hu.2])

private theorem continuousOn_fourFiveContinuumKernelFourDerivative :
    ContinuousOn fourFiveContinuumKernelFourDerivative
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
  unfold fourFiveContinuumKernelFourDerivative
  exact (continuousOn_fourFiveFixedSimplexKernelDerivative 3).comp
    (continuous_id.sub continuous_const).continuousOn
    (by intro u hu; constructor <;> linarith [hu.1, hu.2])

/-- Factorially weighted continuum kernel corresponding to the ordered
mixture `N_1 + N_2/2! + N_3/3! + N_4/4!`. -/
def fourFiveContinuumMixtureKernel (u : Real) : Real :=
  fourFiveContinuumKernelOne u +
    fourFiveContinuumKernelTwo u / 2 +
    fourFiveContinuumKernelThree u / 6 +
    fourFiveContinuumKernelFour u / 24

/-- Continuous first derivative of the mixture kernel. -/
def fourFiveContinuumMixtureKernelDerivative (u : Real) : Real :=
  fourFiveContinuumKernelOneDerivative u +
    fourFiveContinuumKernelTwoDerivative u / 2 +
    fourFiveContinuumKernelThreeDerivative u / 6 +
    fourFiveContinuumKernelFourDerivative u / 24

theorem hasDerivAt_fourFiveContinuumMixtureKernel
    {u : Real} (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    HasDerivAt fourFiveContinuumMixtureKernel
      (fourFiveContinuumMixtureKernelDerivative u) u := by
  have hu0 : u ≠ 0 := by linarith [hu.1]
  have h1 := hasDerivAt_fourFiveContinuumKernelOne hu0
  have h2 := (hasDerivAt_fourFiveContinuumKernelTwo hu).div_const 2
  have h3 := (hasDerivAt_fourFiveContinuumKernelThree hu).div_const 6
  have h4 := (hasDerivAt_fourFiveContinuumKernelFour hu).div_const 24
  simpa [fourFiveContinuumMixtureKernel,
    fourFiveContinuumMixtureKernelDerivative] using
      ((h1.add h2).add h3).add h4

theorem continuousOn_fourFiveContinuumMixtureKernel :
    ContinuousOn fourFiveContinuumMixtureKernel
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
  intro u hu
  exact (hasDerivAt_fourFiveContinuumMixtureKernel hu).continuousAt.continuousWithinAt

theorem continuousOn_fourFiveContinuumMixtureKernelDerivative :
    ContinuousOn fourFiveContinuumMixtureKernelDerivative
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
  unfold fourFiveContinuumMixtureKernelDerivative
  have h1 : ContinuousOn fourFiveContinuumKernelOneDerivative
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
    intro u hu
    unfold fourFiveContinuumKernelOneDerivative
    have hu0 : u ≠ 0 := by linarith [hu.1]
    exact (((continuousAt_id.pow 2).inv₀
      (pow_ne_zero 2 hu0)).neg).continuousWithinAt
  exact (((h1.add
      (continuousOn_fourFiveContinuumKernelTwoDerivative.div_const 2)).add
      (continuousOn_fourFiveContinuumKernelThreeDerivative.div_const 6)).add
      (continuousOn_fourFiveContinuumKernelFourDerivative.div_const 24))

/-- One compact constant bounds the paper's mixture kernel and its first
derivative on the padded four/five range. -/
theorem exists_fourFiveContinuumMixtureKernel_uniform_C1_bound :
    ∃ C : Real, 0 < C ∧
      ∀ u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
        |fourFiveContinuumMixtureKernel u| <= C ∧
        |fourFiveContinuumMixtureKernelDerivative u| <= C := by
  obtain ⟨C0, hC0⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuousOn_fourFiveContinuumMixtureKernel
  obtain ⟨C1, hC1⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuousOn_fourFiveContinuumMixtureKernelDerivative
  have hu : ((41 : Real) / 10) ∈
      Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by norm_num
  have hC0nonneg : 0 <= C0 :=
    (norm_nonneg (fourFiveContinuumMixtureKernel ((41 : Real) / 10))).trans
      (hC0 _ hu)
  have hC1nonneg : 0 <= C1 :=
    (norm_nonneg
      (fourFiveContinuumMixtureKernelDerivative ((41 : Real) / 10))).trans
      (hC1 _ hu)
  refine ⟨1 + C0 + C1, by linarith, ?_⟩
  intro u hu
  constructor
  · have h := hC0 u hu
    rw [Real.norm_eq_abs] at h
    linarith
  · have h := hC1 u hu
    rw [Real.norm_eq_abs] at h
    linarith

end Erdos390.WholePaper.BankPaperRealization
