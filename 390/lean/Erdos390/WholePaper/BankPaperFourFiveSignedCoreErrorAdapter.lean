import Erdos390.WholePaper.BankPaperFourFiveRealCommonDomainIdentification
import Erdos390.WholePaper.RoughSaiasSharpCanonicalRowPaperScale

/-!
# Error adapter from the four/five assembly to a signed smooth core

The four/five continuum calculation ends with a completely explicit error
ledger.  This file performs the remaining algebra needed by the signed
exceptional-core argument:

* compress the four factorially weighted assembly errors to one
  `Z / log(y)^3` bound;
* add the repeated-prime transfer and convert `log(y)` to the paper scale
  `L`;
* freeze the continuum mixture kernel at one reference logarithmic
  coordinate;
* expose the exact balanced normalization for the paper multiplicity
  `K0 + 1`;
* combine three independently estimated physical intervals without losing
  the signed periodic main term.

The module deliberately does not identify a literal smooth-core fibre with
the three rough intervals.  That finite reindexing is an independent input
to the final connector.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Compression of the explicit four-layer error ledger -/

/-- The factorial mass polynomial occurring in the four endpoint errors. -/
def fourFiveEndpointFactorialMassPolynomial (M : Real) : Real :=
  1 + M / 2 + M ^ 2 / 6 + M ^ 3 / 24

/-- The factorial mass polynomial occurring in both the BV and cell errors.

Indeed, after division by `2!`, `3!`, and `4!`, the coefficients
`2,4,6` become `1,2/3,1/4`. -/
def fourFiveTransferFactorialMassPolynomial (M : Real) : Real :=
  1 + 2 * M / 3 + M ^ 2 / 4

theorem fourFiveEndpointFactorialMassPolynomial_nonneg
    {M : Real} (hM : 0 <= M) :
    0 <= fourFiveEndpointFactorialMassPolynomial M := by
  unfold fourFiveEndpointFactorialMassPolynomial
  positivity

theorem fourFiveTransferFactorialMassPolynomial_nonneg
    {M : Real} (hM : 0 <= M) :
    0 <= fourFiveTransferFactorialMassPolynomial M := by
  unfold fourFiveTransferFactorialMassPolynomial
  positivity

/-- One constant paying the endpoint, reciprocal-prime BV, and Lebesgue-cell
parts of the fully bounded assembly after they are put over `log(y)^3`. -/
def fourFiveSignedCoreAssemblyLogCubeConstant
    (C M : Real) : Real :=
  3 * C * fourFiveEndpointFactorialMassPolynomial M +
    (5 * fullReciprocalSumUniformConstant + 1) *
      fourFiveTransferFactorialMassPolynomial M

theorem fourFiveSignedCoreAssemblyLogCubeConstant_nonneg
    {C M : Real} (hC : 0 <= C) (hM : 0 <= M) :
    0 <= fourFiveSignedCoreAssemblyLogCubeConstant C M := by
  unfold fourFiveSignedCoreAssemblyLogCubeConstant
  have hU : 0 <= fullReciprocalSumUniformConstant :=
    fullReciprocalSumUniformConstant_pos.le
  have hendpoint :=
    fourFiveEndpointFactorialMassPolynomial_nonneg hM
  have htransfer :=
    fourFiveTransferFactorialMassPolynomial_nonneg hM
  positivity

/-- The literal fully bounded assembly error is `O(Z/log(y)^3)`.

The assumptions `B <= Z`, `log(y) <= y`, and `1 <= log(y)` are precisely
the elementary scale facts used in the conversion.  No asymptotic theorem
is hidden in this statement. -/
theorem fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube
    {C M Z : Real} {y A B : Nat}
    (hC : 0 <= C) (hM : 0 <= M)
    (hy : 2 <= y) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hlogOne : 1 <= Real.log (y : Real))
    (hlogLeY : Real.log (y : Real) <= (y : Real))
    (hZ : (B : Real) <= Z) (hZ0 : 0 <= Z)
    (hprimeMass : fourFivePrimeCoordinateReciprocalMass y B <= M) :
    fourFiveRealEndpointFullyBoundedAssemblyError C y A B M <=
      fourFiveSignedCoreAssemblyLogCubeConstant C M *
        (Z / Real.log (y : Real) ^ 3) := by
  let s := Real.log (y : Real)
  let length := (B : Real) - (A : Real)
  let q := 3 * C * (B : Real) / s ^ 5
  let outer := (1 / s) * length
  let E := fourFiveReciprocalBVError y
  let mesh := fourFiveLogLogCellMeshBound y
  have hs : 0 < s := by
    dsimp only [s]
    linarith
  have hyReal : (0 : Real) < (y : Real) := by positivity
  have hlength0 : 0 <= length := by
    dsimp only [length]
    exact sub_nonneg.mpr (by exact_mod_cast hAB)
  have hlength : length <= Z := by
    dsimp only [length]
    have hA0 : (0 : Real) <= (A : Real) := by positivity
    linarith
  have hq0 : 0 <= q := by
    dsimp only [q, s]
    positivity
  have hE0 : 0 <= E := by
    dsimp only [E]
    exact (fourFiveReciprocalBVError_pos hcut).le
  have hmesh0 : 0 <= mesh := by
    dsimp only [mesh]
    exact (fourFiveLogLogCellMeshBound_pos hy).le
  have houter0 : 0 <= outer := by
    dsimp only [outer]
    positivity
  have hend0 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 0) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  have hend1 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 1) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  have hend2 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 2) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  have hend3 :=
    fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
      (C := C) (M := M) (m := 3) (y := y) (A := A) (B := B)
      hC hy hprimeMass
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 0 y A B <=
        q * M ^ 0 at hend0
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 1 y A B <=
        q * M ^ 1 at hend1
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 2 y A B <=
        q * M ^ 2 at hend2
  change
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C 3 y A B <=
        q * M ^ 3 at hend3
  have hledger :
      fourFiveRealEndpointFullyBoundedAssemblyError C y A B M <=
        q * fourFiveEndpointFactorialMassPolynomial M +
          (outer * E + outer * mesh) *
            fourFiveTransferFactorialMassPolynomial M := by
    norm_num [pow_zero, pow_one] at hend0 hend1
    rw [show
      fourFiveRealEndpointFullyBoundedAssemblyError C y A B M =
        fourFiveOrderedLastPrimeRealEndpointErrorLayer C 0 y A B +
          fourFiveOrderedLastPrimeRealEndpointErrorLayer C 1 y A B / 2 +
          fourFiveOrderedLastPrimeRealEndpointErrorLayer C 2 y A B / 6 +
          fourFiveOrderedLastPrimeRealEndpointErrorLayer C 3 y A B / 24 +
          (outer * E + outer * mesh) *
            fourFiveTransferFactorialMassPolynomial M by
      unfold fourFiveRealEndpointFullyBoundedAssemblyError
        fourFiveFactorialErrorLedger
        fourFiveTransferFactorialMassPolynomial
      dsimp [fourFiveMovingFaceProductError,
        fourFiveLebesgueCellAggregationBudget,
        fourFivePhysicalOuterScaledBVError, outer, E, mesh]
      ring]
    unfold fourFiveEndpointFactorialMassPolynomial
    nlinarith [hend0, hend1, hend2, hend3]
  have hsThreeFour : s ^ 3 <= s ^ 4 := by
    have hsOne : 1 <= s := by simpa only [s] using hlogOne
    calc
      s ^ 3 = s ^ 3 * 1 := by ring
      _ <= s ^ 3 * s :=
        mul_le_mul_of_nonneg_left hsOne (pow_nonneg hs.le 3)
      _ = s ^ 4 := by ring
  have hsThreeFive : s ^ 3 <= s ^ 5 := by
    have hsOne : 1 <= s := by simpa only [s] using hlogOne
    have hsSq : 1 <= s ^ 2 := one_le_pow₀ (n := 2) hsOne
    calc
      s ^ 3 = s ^ 3 * 1 := by ring
      _ <= s ^ 3 * s ^ 2 :=
        mul_le_mul_of_nonneg_left hsSq (pow_nonneg hs.le 3)
      _ = s ^ 5 := by ring
  have hq :
      q <= 3 * C * (Z / s ^ 3) := by
    dsimp only [q]
    have hnum : 0 <= 3 * C * (B : Real) := by positivity
    calc
      3 * C * (B : Real) / s ^ 5 <=
          3 * C * (B : Real) / s ^ 3 :=
        div_le_div_of_nonneg_left hnum (pow_pos hs 3) hsThreeFive
      _ <= 3 * C * Z / s ^ 3 := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hZ (by positivity))
          (pow_pos hs 3).le
      _ = 3 * C * (Z / s ^ 3) := by ring
  have hBV :
      outer * E <=
        (5 * fullReciprocalSumUniformConstant) *
          (Z / s ^ 3) := by
    have hdiv :
        length / s ^ 4 <= Z / s ^ 3 := by
      apply (div_le_div_iff₀ (pow_pos hs 4) (pow_pos hs 3)).2
      calc
        length * s ^ 3 <= Z * s ^ 3 :=
          mul_le_mul_of_nonneg_right hlength (pow_nonneg hs.le 3)
        _ <= Z * s ^ 4 :=
          mul_le_mul_of_nonneg_left hsThreeFour hZ0
    dsimp only [outer, E, s]
    unfold fourFiveReciprocalBVError
    calc
      (1 / Real.log (y : Real)) * length *
          (5 * fullReciprocalSumUniformConstant /
            Real.log (y : Real) ^ 3) =
        (5 * fullReciprocalSumUniformConstant) *
          (length / Real.log (y : Real) ^ 4) := by ring
      _ <=
        (5 * fullReciprocalSumUniformConstant) *
          (Z / Real.log (y : Real) ^ 3) :=
        mul_le_mul_of_nonneg_left hdiv
          (mul_nonneg (by norm_num)
            fullReciprocalSumUniformConstant_pos.le)
  have hmesh :
      outer * mesh <= Z / s ^ 3 := by
    have hbase :
        length / ((y : Real) * s ^ 2) <= Z / s ^ 3 := by
      apply (div_le_div_iff₀
        (mul_pos hyReal (pow_pos hs 2)) (pow_pos hs 3)).2
      have hlengthLog : length * s <= Z * (y : Real) := by
        calc
          length * s <= Z * s :=
            mul_le_mul_of_nonneg_right hlength hs.le
          _ <= Z * (y : Real) :=
            mul_le_mul_of_nonneg_left
              (by simpa only [s] using hlogLeY) hZ0
      calc
        length * s ^ 3 = (length * s) * s ^ 2 := by ring
        _ <= (Z * (y : Real)) * s ^ 2 :=
          mul_le_mul_of_nonneg_right hlengthLog (pow_nonneg hs.le 2)
        _ = Z * ((y : Real) * s ^ 2) := by ring
    dsimp only [outer, mesh, s]
    unfold fourFiveLogLogCellMeshBound
    calc
      (1 / Real.log (y : Real)) * length *
          (1 / ((y : Real) * Real.log (y : Real))) =
        length /
          ((y : Real) * Real.log (y : Real) ^ 2) := by ring
      _ <= Z / Real.log (y : Real) ^ 3 := hbase
  have htransfer :
      outer * E + outer * mesh <=
        (5 * fullReciprocalSumUniformConstant + 1) *
          (Z / s ^ 3) := by
    calc
      outer * E + outer * mesh <=
          (5 * fullReciprocalSumUniformConstant) *
              (Z / s ^ 3) +
            Z / s ^ 3 := add_le_add hBV hmesh
      _ =
          (5 * fullReciprocalSumUniformConstant + 1) *
            (Z / s ^ 3) := by ring
  have hendpointPoly :=
    fourFiveEndpointFactorialMassPolynomial_nonneg hM
  have htransferPoly :=
    fourFiveTransferFactorialMassPolynomial_nonneg hM
  calc
    fourFiveRealEndpointFullyBoundedAssemblyError C y A B M <=
        q * fourFiveEndpointFactorialMassPolynomial M +
          (outer * E + outer * mesh) *
            fourFiveTransferFactorialMassPolynomial M := hledger
    _ <=
        (3 * C * (Z / s ^ 3)) *
            fourFiveEndpointFactorialMassPolynomial M +
          ((5 * fullReciprocalSumUniformConstant + 1) *
            (Z / s ^ 3)) *
              fourFiveTransferFactorialMassPolynomial M :=
      add_le_add
        (mul_le_mul_of_nonneg_right hq hendpointPoly)
        (mul_le_mul_of_nonneg_right htransfer htransferPoly)
    _ =
        fourFiveSignedCoreAssemblyLogCubeConstant C M *
          (Z / Real.log (y : Real) ^ 3) := by
      dsimp only [s]
      unfold fourFiveSignedCoreAssemblyLogCubeConstant
      ring

/-- Add the exact ordered-to-rough transfer and convert `log(y)` to `L`.

This theorem consumes the ordered-mixture estimate produced by the fully
bounded FourFive assembly.  It is therefore a clean rate boundary for each
physical interval used by the signed-core reindexing. -/
theorem abs_fourFiveRoughInterval_card_sub_mixtureIntegral_le_paperRate
    {C M Z Lpaper : Real} {y A B : Nat}
    (hC : 0 <= C) (hM : 0 <= M)
    (hy : 2 <= y) (hA : 1 <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hOmega : B < (y + 1) ^ 5) (hyB : y <= B)
    (hlogOne : 1 <= Real.log (y : Real))
    (hlogLeY : Real.log (y : Real) <= (y : Real))
    (hlogCubeLeY : Real.log (y : Real) ^ 3 <= (y : Real))
    (hZ : (B : Real) <= Z) (hZ0 : 0 <= Z)
    (hL : 0 < Lpaper)
    (hlogLower : (1 / 5 : Real) * Lpaper <= Real.log (y : Real))
    (hprimeMass : fourFivePrimeCoordinateReciprocalMass y B <= M)
    (hordered : FourFiveOrderedPrimeMixtureEstimate y A B
      (fourFiveContinuumMixtureIntegralMain y A B)
      (fourFiveRealEndpointFullyBoundedAssemblyError C y A B M)) :
    abs (((fourFiveRoughInterval y A B).card : Real) -
        fourFiveContinuumMixtureIntegralMain y A B) <=
      (125 *
        (1 + fourFiveSignedCoreAssemblyLogCubeConstant C M)) *
          (Z / Lpaper ^ 3) := by
  have hlogPos : 0 < Real.log (y : Real) := by linarith
  have hassembly :=
    fourFiveRealEndpointFullyBoundedAssemblyError_le_logCube
      hC hM hy hAB hcut hlogOne hlogLeY hZ hZ0 hprimeMass
  have hrough :=
    abs_fourFiveRoughInterval_card_sub_mainTerm_le_div_add_error
      hA hOmega (by omega : 0 < y) hyB hordered
  have hrepeated :
      (B : Real) / (y : Real) <=
        Z / Real.log (y : Real) ^ 3 := by
    apply (div_le_div_iff₀
      (by positivity : (0 : Real) < (y : Real))
      (pow_pos hlogPos 3)).2
    calc
      (B : Real) * Real.log (y : Real) ^ 3 <=
          Z * Real.log (y : Real) ^ 3 :=
        mul_le_mul_of_nonneg_right hZ (pow_nonneg hlogPos.le 3)
      _ <= Z * (y : Real) :=
        mul_le_mul_of_nonneg_left hlogCubeLeY hZ0
  have hlogRate :
      Z / Real.log (y : Real) ^ 3 <= 125 * (Z / Lpaper ^ 3) := by
    have hfive :
        Lpaper <= 5 * Real.log (y : Real) := by
      nlinarith [hlogLower]
    have hpow :
        Lpaper ^ 3 <=
          (5 * Real.log (y : Real)) ^ 3 :=
      pow_le_pow_left₀ hL.le hfive 3
    rw [show 125 * (Z / Lpaper ^ 3) =
      (125 * Z) / Lpaper ^ 3 by ring]
    apply (div_le_div_iff₀
      (pow_pos hlogPos 3) (pow_pos hL 3)).2
    calc
      Z * Lpaper ^ 3 <=
          Z * (5 * Real.log (y : Real)) ^ 3 :=
        mul_le_mul_of_nonneg_left hpow hZ0
      _ = 125 * Z * Real.log (y : Real) ^ 3 := by ring
      _ = (125 * Z) * Real.log (y : Real) ^ 3 := by ring
  have hconstant0 :
      0 <= fourFiveSignedCoreAssemblyLogCubeConstant C M :=
    fourFiveSignedCoreAssemblyLogCubeConstant_nonneg hC hM
  calc
    abs (((fourFiveRoughInterval y A B).card : Real) -
        fourFiveContinuumMixtureIntegralMain y A B) <=
      (B : Real) / (y : Real) +
        fourFiveRealEndpointFullyBoundedAssemblyError C y A B M := hrough
    _ <= Z / Real.log (y : Real) ^ 3 +
        fourFiveSignedCoreAssemblyLogCubeConstant C M *
          (Z / Real.log (y : Real) ^ 3) :=
      add_le_add hrepeated hassembly
    _ =
        (1 + fourFiveSignedCoreAssemblyLogCubeConstant C M) *
          (Z / Real.log (y : Real) ^ 3) := by ring
    _ <=
        (1 + fourFiveSignedCoreAssemblyLogCubeConstant C M) *
          (125 * (Z / Lpaper ^ 3)) :=
      mul_le_mul_of_nonneg_left hlogRate (by linarith [hconstant0])
    _ =
        (125 *
          (1 + fourFiveSignedCoreAssemblyLogCubeConstant C M)) *
            (Z / Lpaper ^ 3) := by ring

/-! ## Freezing the common continuum kernel -/

/-- The compact `C^1` certificate gives the literal Lipschitz estimate
needed to freeze the mixture kernel at one reference point. -/
theorem abs_fourFiveContinuumMixtureKernel_sub_le_of_C1
    {C u v : Real}
    (hu : u ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hv : v ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (_hC : 0 <= C)
    (hderiv : ∀ x ∈
      Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
      |fourFiveContinuumMixtureKernelDerivative x| <= C) :
    |fourFiveContinuumMixtureKernel u -
        fourFiveContinuumMixtureKernel v| <= C * |u - v| := by
  have hdiff (x : Real)
      (hx : x ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      DifferentiableAt Real fourFiveContinuumMixtureKernel x :=
    (hasDerivAt_fourFiveContinuumMixtureKernel hx).differentiableAt
  have hbound (x : Real)
      (hx : x ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
      ‖deriv fourFiveContinuumMixtureKernel x‖ <= C := by
    rw [(hasDerivAt_fourFiveContinuumMixtureKernel hx).deriv,
      Real.norm_eq_abs]
    exact hderiv x hx
  simpa only [Real.norm_eq_abs] using
    Convex.norm_image_sub_le_of_norm_deriv_le
      hdiff hbound
      (convex_Icc ((41 : Real) / 10) ((47 : Real) / 10))
      hv hu

/-- Paper-range hypotheses also supply interval integrability of the common
mixture kernel.  This is the integrability input used by kernel freezing. -/
theorem intervalIntegrable_fourFiveContinuumMixtureKernel_of_paperRange
    {y A B : Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      Real.log t / Real.log (y : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    IntervalIntegrable
      (fun t : Real => fourFiveContinuumMixtureKernel
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real) := by
  have hABReal : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hyReal : (0 : Real) < (y : Real) := by positivity
  have hyAReal : (y : Real) <= (A : Real) := by exact_mod_cast hyA
  have hcoord : ContinuousOn
      (fun t : Real => Real.log t / Real.log (y : Real))
      (Set.Icc (A : Real) (B : Real)) := by
    intro t ht
    have ht0 : t ≠ 0 :=
      ne_of_gt (hyReal.trans_le (hyAReal.trans ht.1))
    exact ((Real.continuousAt_log ht0).div_const
      (Real.log (y : Real))).continuousWithinAt
  exact
    (continuousOn_fourFiveContinuumMixtureKernel.comp'
      hcoord hrange).intervalIntegrable_of_Icc hABReal

/-- Freeze the one-integral continuum main at `u0`.

`D` is a geometric bound for the normalized logarithmic displacement on the
physical interval.  This separates the universal kernel argument from the
three interval-specific endpoint geometry. -/
theorem abs_fourFiveContinuumMixtureIntegralMain_sub_frozen_le
    {y A B : Nat} {C D u0 : Real}
    (hAB : A <= B)
    (hlog : 0 < Real.log (y : Real))
    (hC : 0 <= C) (_hD : 0 <= D)
    (hu0 : u0 ∈ Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      Real.log t / Real.log (y : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hdisplacement : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      |Real.log t / Real.log (y : Real) - u0| <= D)
    (hderiv : ∀ x ∈
      Set.Icc ((41 : Real) / 10) ((47 : Real) / 10),
      |fourFiveContinuumMixtureKernelDerivative x| <= C)
    (hintegrable : IntervalIntegrable
      (fun t : Real => fourFiveContinuumMixtureKernel
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real)) :
    |fourFiveContinuumMixtureIntegralMain y A B -
        (((B : Real) - (A : Real)) / Real.log (y : Real)) *
          fourFiveContinuumMixtureKernel u0| <=
      ((((B : Real) - (A : Real)) / Real.log (y : Real)) * C) * D := by
  let F : Real -> Real := fun t =>
    fourFiveContinuumMixtureKernel
      (Real.log t / Real.log (y : Real))
  let K0 := fourFiveContinuumMixtureKernel u0
  have hABReal : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hlength0 : 0 <= (B : Real) - (A : Real) := sub_nonneg.mpr hABReal
  have hpoint (t : Real) (ht : t ∈ Set.uIcc (A : Real) (B : Real)) :
      |F t - K0| <= C * D := by
    have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
      simpa only [Set.uIcc_of_le hABReal] using ht
    exact
      (abs_fourFiveContinuumMixtureKernel_sub_le_of_C1
        (hrange t htIcc) hu0 hC hderiv).trans
        (mul_le_mul_of_nonneg_left (hdisplacement t htIcc) hC)
  have hnorm :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun t => F t - K0)
      (fun t ht => by
        simpa only [Real.norm_eq_abs] using
          hpoint t (Set.uIoc_subset_uIcc ht))
  have hrewrite :
      fourFiveContinuumMixtureIntegralMain y A B -
          (((B : Real) - (A : Real)) / Real.log (y : Real)) * K0 =
        (1 / Real.log (y : Real)) *
          (∫ t in (A : Real)..(B : Real), F t - K0) := by
    unfold fourFiveContinuumMixtureIntegralMain
    rw [intervalIntegral.integral_sub hintegrable intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hrewrite, abs_mul, abs_of_nonneg (one_div_nonneg.mpr hlog.le)]
  calc
    (1 / Real.log (y : Real)) *
        |∫ t in (A : Real)..(B : Real), F t - K0| <=
      (1 / Real.log (y : Real)) *
        ((C * D) * |(B : Real) - (A : Real)|) :=
      mul_le_mul_of_nonneg_left
        (by simpa only [Real.norm_eq_abs] using hnorm)
        (one_div_nonneg.mpr hlog.le)
    _ =
      ((((B : Real) - (A : Real)) / Real.log (y : Real)) * C) * D := by
      rw [abs_of_nonneg hlength0]
      ring

/-! ### Quotient endpoints and ideal physical lengths -/

/-- The integer length of a divided half-open interval differs from its
ideal real divided length by at most one. -/
theorem abs_natQuotientIntervalLength_sub_realLength_le_one
    {lo hi b : Nat} (hb : 0 < b) (hlohi : lo <= hi) :
    |((((hi / b - lo / b : Nat) : Real)) -
        (((hi - lo : Nat) : Real) / (b : Real)))| <= 1 := by
  exact
    (quotientIocLength_sub_realLengthDiv_abs_lt_one
      (D := b) (lo := lo) (hi := hi) hb hlohi).le

/-- Combine an arithmetic-to-continuum error, kernel freezing at the literal
integer interval length, and the single quotient-endpoint discrepancy.

This small triangle lemma is what turns the natural endpoints used by
`fourFiveRoughInterval` into the ideal lengths appearing in the balanced
normalization. -/
theorem abs_count_sub_idealFrozen_le
    {count main kernel literalLength idealLength
      arithmeticError freezeError endpointError kernelBound : Real}
    (harithmetic : |count - main| <= arithmeticError)
    (hfreeze : |main - kernel * literalLength| <= freezeError)
    (hlength : |literalLength - idealLength| <= endpointError)
    (hkernel : |kernel| <= kernelBound)
    (_hendpoint : 0 <= endpointError) (hkernelBound : 0 <= kernelBound) :
    |count - kernel * idealLength| <=
      arithmeticError + freezeError + kernelBound * endpointError := by
  have hkernelLength :
      |kernel * literalLength - kernel * idealLength| <=
        kernelBound * endpointError := by
    rw [← mul_sub, abs_mul]
    exact mul_le_mul hkernel hlength (abs_nonneg _)
      hkernelBound
  calc
    |count - kernel * idealLength| =
        |(count - main) +
          (main - kernel * literalLength) +
          (kernel * literalLength - kernel * idealLength)| := by ring_nf
    _ <= |count - main| +
        |main - kernel * literalLength| +
        |kernel * literalLength - kernel * idealLength| := by
      exact (abs_add_le _ _).trans
        (add_le_add_left (abs_add_le _ _) _)
    _ <= arithmeticError + freezeError +
        kernelBound * endpointError :=
      add_le_add (add_le_add harithmetic hfreeze) hkernelLength

/-! ## Exact `K0+1` balance and signed three-interval algebra -/

/-- Exact physical-length normalization after division by one positive
smooth core.  The indicator is the literal head-free indicator, so the
right side is exactly the mean-zero periodic core coefficient. -/
theorem roughHeadBalancedAlpha_succ_div_core_normalization
    {W K0 n h b : Nat} {beta ell : Real}
    (hKh : 0 < (K0 + 1) * h) :
    (h : Real) / (b : Real) -
        (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
          (roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
              (((K0 + 1) * h : Nat) : Real) / (b : Real) +
            (beta / ell) *
              (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real)) =
      ((h : Real) / (b : Real)) *
        roughHeadPeriodicCoreCoefficient W b := by
  have hdelta : roughHeadDensity W ≠ 0 :=
    (roughHeadDensity_pos W).ne'
  have hnormalization :=
    roughHeadBalancedAlpha_length_normalization
      (W := W) (n := n) (h := h) (K := K0 + 1)
      (beta := beta) (L := ell) hKh
  have hinside :
      roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
            (((K0 + 1) * h : Nat) : Real) +
          (beta / ell) *
            (((n - (K0 + 1) * h : Nat) : Real)) =
        (h : Real) / roughHeadDensity W := by
    apply (eq_div_iff hdelta).2
    simpa only [mul_comm] using hnormalization
  have hinsideDiv :
      roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
            (((K0 + 1) * h : Nat) : Real) / (b : Real) +
          (beta / ell) *
            (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real) =
        ((h : Real) / roughHeadDensity W) / (b : Real) := by
    rw [← add_div, hinside]
  by_cases hcop : Nat.Coprime b (roughHeadModulus W)
  · rw [if_pos hcop]
    unfold roughHeadPeriodicCoreCoefficient
    rw [if_pos hcop, hinsideDiv]
    ring
  · rw [if_neg hcop]
    unfold roughHeadPeriodicCoreCoefficient
    rw [if_neg hcop]
    ring

/-- Three independently frozen physical intervals retain the exact signed
periodic main term after balanced normalization.

This is the clean input boundary expected from the finite smooth-core
reindexing: `Nplus`, `Nhigh`, and `Nbroad` are the three real interval
counts after that reindexing. -/
theorem abs_balanced_three_interval_sub_periodic_frozen_le
    {W K0 n h b : Nat} {beta ell logY kernelValue : Real}
    {Nplus Nhigh Nbroad Eplus Ehigh Ebroad : Real}
    (hKh : 0 < (K0 + 1) * h)
    (hplus :
      |Nplus -
        (kernelValue / logY) * ((h : Real) / (b : Real))| <= Eplus)
    (hhigh :
      |Nhigh -
        (kernelValue / logY) *
          ((((K0 + 1) * h : Nat) : Real) / (b : Real))| <= Ehigh)
    (hbroad :
      |Nbroad -
        (kernelValue / logY) *
          ((((n - (K0 + 1) * h : Nat) : Real)) / (b : Real))| <=
            Ebroad) :
    |Nplus -
        (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
          (roughHeadBalancedAlpha W n h (K0 + 1) beta ell * Nhigh +
            (beta / ell) * Nbroad) -
        ((kernelValue / logY) * ((h : Real) / (b : Real)) *
          roughHeadPeriodicCoreCoefficient W b)| <=
      Eplus +
        |roughHeadBalancedAlpha W n h (K0 + 1) beta ell| * Ehigh +
        |beta / ell| * Ebroad := by
  let g : Real :=
    if Nat.Coprime b (roughHeadModulus W) then 1 else 0
  let alpha := roughHeadBalancedAlpha W n h (K0 + 1) beta ell
  let q := beta / ell
  let k := kernelValue / logY
  let lplus := (h : Real) / (b : Real)
  let lhigh := (((K0 + 1) * h : Nat) : Real) / (b : Real)
  let lbroad := (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real)
  have hnormalize :
      lplus - g * (alpha * lhigh + q * lbroad) =
        lplus * roughHeadPeriodicCoreCoefficient W b := by
    dsimp only [g, alpha, q, lplus, lhigh, lbroad]
    calc
      (h : Real) / (b : Real) -
          (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
            (roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
                ((((K0 + 1) * h : Nat) : Real) / (b : Real)) +
              (beta / ell) *
                ((((n - (K0 + 1) * h : Nat) : Real)) / (b : Real))) =
        (h : Real) / (b : Real) -
          (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
            (roughHeadBalancedAlpha W n h (K0 + 1) beta ell *
                  (((K0 + 1) * h : Nat) : Real) / (b : Real) +
              (beta / ell) *
                  (((n - (K0 + 1) * h : Nat) : Real)) / (b : Real)) := by
        ring
      _ = ((h : Real) / (b : Real)) *
          roughHeadPeriodicCoreCoefficient W b :=
        roughHeadBalancedAlpha_succ_div_core_normalization
          (W := W) (K0 := K0) (n := n) (h := h) (b := b)
          (beta := beta) (ell := ell) hKh
  have hg : |g| <= 1 := by
    dsimp only [g]
    by_cases hcop : Nat.Coprime b (roughHeadModulus W)
    · calc
        |if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0| =
            1 := by rw [if_pos hcop, abs_one]
        _ <= 1 := le_rfl
    · calc
        |if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0| =
            0 := by rw [if_neg hcop, abs_zero]
        _ <= 1 := zero_le_one
  have hrewrite :
      Nplus - g * (alpha * Nhigh + q * Nbroad) -
          (k * lplus * roughHeadPeriodicCoreCoefficient W b) =
        (Nplus - k * lplus) -
          g * (alpha * (Nhigh - k * lhigh) +
            q * (Nbroad - k * lbroad)) := by
    calc
      Nplus - g * (alpha * Nhigh + q * Nbroad) -
          (k * lplus * roughHeadPeriodicCoreCoefficient W b) =
        Nplus - g * (alpha * Nhigh + q * Nbroad) -
          k * (lplus * roughHeadPeriodicCoreCoefficient W b) := by ring
      _ =
        Nplus - g * (alpha * Nhigh + q * Nbroad) -
          k * (lplus - g * (alpha * lhigh + q * lbroad)) := by
        rw [hnormalize]
      _ =
        (Nplus - k * lplus) -
          g * (alpha * (Nhigh - k * lhigh) +
            q * (Nbroad - k * lbroad)) := by ring
  change
    |Nplus - g * (alpha * Nhigh + q * Nbroad) -
        (k * lplus * roughHeadPeriodicCoreCoefficient W b)| <= _
  rw [hrewrite]
  have hinner :
      |alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad)| <=
        |alpha| * Ehigh + |q| * Ebroad := by
    calc
      |alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad)| <=
        |alpha * (Nhigh - k * lhigh)| +
          |q * (Nbroad - k * lbroad)| := abs_add_le _ _
      _ =
        |alpha| * |Nhigh - k * lhigh| +
          |q| * |Nbroad - k * lbroad| := by
        rw [abs_mul, abs_mul]
      _ <= |alpha| * Ehigh + |q| * Ebroad :=
        add_le_add
          (mul_le_mul_of_nonneg_left
            (by simpa only [alpha, k, lhigh] using hhigh)
            (abs_nonneg alpha))
          (mul_le_mul_of_nonneg_left
            (by simpa only [q, k, lbroad] using hbroad)
            (abs_nonneg q))
  have hinnerRhs0 :
      0 <= |alpha| * Ehigh + |q| * Ebroad := by
    have hEhigh0 : 0 <= Ehigh :=
      (abs_nonneg (Nhigh - k * lhigh)).trans
        (by simpa only [alpha, k, lhigh] using hhigh)
    have hEbroad0 : 0 <= Ebroad :=
      (abs_nonneg (Nbroad - k * lbroad)).trans
        (by simpa only [q, k, lbroad] using hbroad)
    positivity
  calc
    |(Nplus - k * lplus) -
        g * (alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad))| <=
      |Nplus - k * lplus| +
        |g * (alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad))| := abs_sub _ _
    _ =
      |Nplus - k * lplus| +
        |g| * |alpha * (Nhigh - k * lhigh) +
          q * (Nbroad - k * lbroad)| := by rw [abs_mul]
    _ <=
      Eplus + |g| * (|alpha| * Ehigh + |q| * Ebroad) :=
      add_le_add
        (by simpa only [k, lplus] using hplus)
        (mul_le_mul_of_nonneg_left hinner (abs_nonneg g))
    _ <= Eplus + 1 * (|alpha| * Ehigh + |q| * Ebroad) :=
      add_le_add_right
        (mul_le_mul_of_nonneg_right hg hinnerRhs0) Eplus
    _ =
      Eplus + |alpha| * Ehigh + |q| * Ebroad := by ring

/-- Paper-scale corollary of the preceding algebra.

The two short intervals may be estimated at `Z/L^3+1`, whereas the broad
interval is only needed at `Z/L^2+1`: its coefficient `beta/L` supplies the
missing logarithm. -/
theorem abs_balanced_three_interval_sub_periodic_frozen_le_paperRate
    {W K0 n b : Nat} {c beta kernelValue : Real}
    {Nplus Nhigh Nbroad Cplus Chigh Cbroad Z : Real}
    (hc : 0 < c) (hn : 2 <= n)
    (hLone : 1 <= L n) (hZ : 0 <= Z)
    (hplus :
      |Nplus -
        (kernelValue / Real.log (yNat n : Real)) *
          ((upperTailLength c n : Real) / (b : Real))| <=
        Cplus * (Z / L n ^ 3 + 1))
    (hhigh :
      |Nhigh -
        (kernelValue / Real.log (yNat n : Real)) *
          ((((K0 + 1) * upperTailLength c n : Nat) : Real) /
            (b : Real))| <=
        Chigh * (Z / L n ^ 3 + 1))
    (hbroad :
      |Nbroad -
        (kernelValue / Real.log (yNat n : Real)) *
          ((((n - (K0 + 1) * upperTailLength c n : Nat) : Real)) /
            (b : Real))| <=
        Cbroad * (Z / L n ^ 2 + 1))
    (_hCplus : 0 <= Cplus) (hChigh : 0 <= Chigh)
    (hCbroad : 0 <= Cbroad) :
    |Nplus -
        (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n) * Nhigh +
            (beta / L n) * Nbroad) -
        ((kernelValue / Real.log (yNat n : Real)) *
          ((upperTailLength c n : Real) / (b : Real)) *
            roughHeadPeriodicCoreCoefficient W b)| <=
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        |beta| * Cbroad) *
          (Z / L n ^ 3 + 1) := by
  have hscale : 0 < secondOrderScale n := secondOrderScale_pos hn
  have htailPos : 0 < upperTailLength c n := by
    unfold upperTailLength
    exact Nat.ceil_pos.mpr (mul_pos hc hscale)
  have hKh : 0 < (K0 + 1) * upperTailLength c n :=
    Nat.mul_pos (by omega) htailPos
  have hbase :=
    abs_balanced_three_interval_sub_periodic_frozen_le
      (W := W) (K0 := K0) (n := n)
      (h := upperTailLength c n) (b := b)
      (beta := beta) (ell := L n)
      (logY := Real.log (yNat n : Real))
      (kernelValue := kernelValue)
      (Nplus := Nplus) (Nhigh := Nhigh) (Nbroad := Nbroad)
      (Eplus := Cplus * (Z / L n ^ 3 + 1))
      (Ehigh := Chigh * (Z / L n ^ 3 + 1))
      (Ebroad := Cbroad * (Z / L n ^ 2 + 1))
      hKh hplus hhigh hbroad
  have halpha :
      |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n)| <=
        roughBalancedAlphaConstant W K0 c beta := by
    simpa only [roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  have hL : 0 < L n := L_pos (by omega)
  have hshort0 : 0 <= Z / L n ^ 3 + 1 := by positivity
  have hbroadScale :
      (1 / L n) * (Z / L n ^ 2 + 1) <=
        Z / L n ^ 3 + 1 := by
    have hinv : 1 / L n <= 1 := (div_le_one hL).2 hLone
    calc
      (1 / L n) * (Z / L n ^ 2 + 1) =
          Z / L n ^ 3 + 1 / L n := by ring
      _ <= Z / L n ^ 3 + 1 := add_le_add_right hinv _
  calc
    _ <=
      Cplus * (Z / L n ^ 3 + 1) +
        |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
          beta (L n)| *
          (Chigh * (Z / L n ^ 3 + 1)) +
        |beta / L n| *
          (Cbroad * (Z / L n ^ 2 + 1)) := hbase
    _ <=
      Cplus * (Z / L n ^ 3 + 1) +
        roughBalancedAlphaConstant W K0 c beta *
          (Chigh * (Z / L n ^ 3 + 1)) +
        |beta| * Cbroad * (Z / L n ^ 3 + 1) := by
      have hhighTerm :
          |roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n)| *
              (Chigh * (Z / L n ^ 3 + 1)) <=
            roughBalancedAlphaConstant W K0 c beta *
              (Chigh * (Z / L n ^ 3 + 1)) :=
        mul_le_mul_of_nonneg_right halpha
          (mul_nonneg hChigh hshort0)
      have hbroadTerm :
          |beta / L n| * (Cbroad * (Z / L n ^ 2 + 1)) <=
            |beta| * Cbroad * (Z / L n ^ 3 + 1) := by
        calc
          |beta / L n| * (Cbroad * (Z / L n ^ 2 + 1)) <=
              (|beta| / L n) *
                (Cbroad * (Z / L n ^ 2 + 1)) := by
            rw [abs_div, abs_of_pos hL]
          _ =
              (|beta| * Cbroad) *
                ((1 / L n) * (Z / L n ^ 2 + 1)) := by ring
          _ <= (|beta| * Cbroad) * (Z / L n ^ 3 + 1) :=
            mul_le_mul_of_nonneg_left hbroadScale
              (mul_nonneg (abs_nonneg beta) hCbroad)
      exact add_le_add (add_le_add le_rfl hhighTerm) hbroadTerm
    _ =
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        |beta| * Cbroad) *
          (Z / L n ^ 3 + 1) := by ring

/-! ## Positive cutoff-band algebra -/

/-- Pure positive three-interval cutoff adapter.

This theorem makes no claim that the clipped physical intervals satisfy the
three displayed size bounds.  Once those bounds are supplied, it gives the
paper's `Z/L^2+1` cutoff rate.  The broad interval is allowed the weaker
`Z/L+1` estimate because its literal coefficient is `beta/L`. -/
theorem abs_balanced_three_interval_cutoff_le_paperRate
    {W K0 n b : Nat} {c beta : Real}
    {Nplus Nhigh Nbroad Cplus Chigh Cbroad Z : Real}
    (hc : 0 < c) (hn : 2 <= n)
    (hLone : 1 <= L n) (hZ : 0 <= Z)
    (hNplus : 0 <= Nplus) (hNhigh : 0 <= Nhigh)
    (hNbroad : 0 <= Nbroad)
    (hplus : Nplus <= Cplus * (Z / L n ^ 2 + 1))
    (hhigh : Nhigh <= Chigh * (Z / L n ^ 2 + 1))
    (hbroad : Nbroad <= Cbroad * (Z / L n + 1))
    (_hCplus : 0 <= Cplus) (hChigh : 0 <= Chigh)
    (hCbroad : 0 <= Cbroad) :
    |Nplus -
        (if Nat.Coprime b (roughHeadModulus W) then (1 : Real) else 0) *
          (roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
              beta (L n) * Nhigh +
            (beta / L n) * Nbroad)| <=
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        |beta| * Cbroad) *
          (Z / L n ^ 2 + 1) := by
  let g : Real :=
    if Nat.Coprime b (roughHeadModulus W) then 1 else 0
  let alpha :=
    roughHeadBalancedAlpha W n (upperTailLength c n) (K0 + 1)
      beta (L n)
  let q := beta / L n
  have hg : |g| <= 1 := by
    dsimp only [g]
    by_cases hcop : Nat.Coprime b (roughHeadModulus W)
    · rw [if_pos hcop]
      exact (abs_one : |(1 : Real)| = 1).le
    · simp only [if_neg hcop, abs_zero, zero_le_one]
  have halpha :
      |alpha| <= roughBalancedAlphaConstant W K0 c beta := by
    simpa only [alpha, roughBalancedAlphaConstant] using
      roughHeadBalancedAlpha_succ_abs_le W K0 hc hn
  have hL : 0 < L n := L_pos (by omega)
  have hshort0 : 0 <= Z / L n ^ 2 + 1 := by positivity
  have hbroadScale :
      (1 / L n) * (Z / L n + 1) <= Z / L n ^ 2 + 1 := by
    have hinv : 1 / L n <= 1 := (div_le_one hL).2 hLone
    calc
      (1 / L n) * (Z / L n + 1) =
          Z / L n ^ 2 + 1 / L n := by ring
      _ <= Z / L n ^ 2 + 1 := add_le_add_right hinv _
  have hraw :
      |Nplus - g * (alpha * Nhigh + q * Nbroad)| <=
        Nplus + |alpha| * Nhigh + |q| * Nbroad := by
    calc
      |Nplus - g * (alpha * Nhigh + q * Nbroad)| <=
          |Nplus| + |g * (alpha * Nhigh + q * Nbroad)| :=
        abs_sub _ _
      _ = Nplus + |g| * |alpha * Nhigh + q * Nbroad| := by
        rw [abs_of_nonneg hNplus, abs_mul]
      _ <= Nplus + 1 * |alpha * Nhigh + q * Nbroad| :=
        add_le_add_right
          (mul_le_mul_of_nonneg_right hg (abs_nonneg _)) Nplus
      _ <= Nplus + (|alpha| * Nhigh + |q| * Nbroad) := by
        rw [one_mul]
        exact add_le_add_right
          ((abs_add_le _ _).trans_eq (by
            rw [abs_mul, abs_mul, abs_of_nonneg hNhigh,
              abs_of_nonneg hNbroad])) Nplus
      _ = Nplus + |alpha| * Nhigh + |q| * Nbroad := by
        rw [add_assoc]
  change
    |Nplus - g * (alpha * Nhigh + q * Nbroad)| <= _
  calc
    |Nplus - g * (alpha * Nhigh + q * Nbroad)| <=
        Nplus + |alpha| * Nhigh + |q| * Nbroad := hraw
    _ <=
        Cplus * (Z / L n ^ 2 + 1) +
          roughBalancedAlphaConstant W K0 c beta *
            (Chigh * (Z / L n ^ 2 + 1)) +
          |beta| * Cbroad * (Z / L n ^ 2 + 1) := by
      have hhighTerm :
          |alpha| * Nhigh <=
            roughBalancedAlphaConstant W K0 c beta *
              (Chigh * (Z / L n ^ 2 + 1)) := by
        calc
          |alpha| * Nhigh <= |alpha| *
              (Chigh * (Z / L n ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_left hhigh (abs_nonneg alpha)
          _ <= roughBalancedAlphaConstant W K0 c beta *
              (Chigh * (Z / L n ^ 2 + 1)) :=
            mul_le_mul_of_nonneg_right halpha
              (mul_nonneg hChigh hshort0)
      have hbroadTerm :
          |q| * Nbroad <=
            |beta| * Cbroad * (Z / L n ^ 2 + 1) := by
        calc
          |q| * Nbroad <= |q| * (Cbroad * (Z / L n + 1)) :=
            mul_le_mul_of_nonneg_left hbroad (abs_nonneg q)
          _ = (|beta| * Cbroad) *
              ((1 / L n) * (Z / L n + 1)) := by
            dsimp only [q]
            rw [abs_div, abs_of_pos hL]
            ring
          _ <= (|beta| * Cbroad) * (Z / L n ^ 2 + 1) :=
            mul_le_mul_of_nonneg_left hbroadScale
              (mul_nonneg (abs_nonneg beta) hCbroad)
      exact add_le_add (add_le_add hplus hhighTerm) hbroadTerm
    _ =
      (Cplus +
        roughBalancedAlphaConstant W K0 c beta * Chigh +
        |beta| * Cbroad) *
          (Z / L n ^ 2 + 1) := by ring

end BankPaperRealization

end

end Erdos390.WholePaper
