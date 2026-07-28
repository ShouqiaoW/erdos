import Erdos390.WholePaper.BankPaperFourFiveOrderedMixtureAssembly
import Erdos390.WholePaper.BankPaperFourFiveRealLastPrimeEndpoint

/-!
# Exact decomposition of the last-prime/continuum bridge

The final ordered-mixture assembly deliberately exposes one analytic bridge.
This file splits that bridge into literal intermediate quantities, without
adding a hypothesis or an assumed estimate.

For a layer with `m = 0,1,2,3` preceding prime coordinates we insert

1. the physical `t`-integral with the actual reciprocal-prime product;
2. the corresponding product of continuum log-log cells, identified exactly
   with products of literal Lebesgue cell integrals;
3. the untransformed logarithmic moving-simplex integral;
4. the already constructed fixed-simplex layer `K_1,...,K_4`.

The three genuinely new interfaces are therefore the physical endpoint
change, cell aggregation (including right-endpoint/strict-face effects), and
the moving-to-fixed-simplex change of variables.  The reciprocal-prime
product replacement remains a separate interface supplied by the existing
product-measure telescope.

Every error below is the absolute value of a displayed difference.  The
`productBudgetOverrun` is the positive part left after charging the existing
moving-face budget.  Consequently the final bridge is a theorem for arbitrary
`E,M`; later quantitative work only has to show that the explicit three new
errors and the overrun have the desired size.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## Physical and cellwise intermediate layers -/

/-- The logarithmic coordinate of a real physical variable. -/
def fourFiveRealLogCoordinate (y : Nat) (t : Real) : Real :=
  Real.log t / Real.log (y : Real)

/-- The prefix product, embedded in the physical real variable. -/
def fourFivePrefixProductReal
    {m : Nat} (q : Fin m -> Nat) : Real :=
  ((∏ i, q i : Nat) : Real)

theorem fourFivePrefixProductReal_pos
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    0 < fourFivePrefixProductReal q := by
  unfold fourFivePrefixProductReal
  exact_mod_cast fourFiveOrderedPrimePrefix_prod_pos hq

/-- The exact last-prime logarithmic integral after the linear substitution
`t = qv`.  Its endpoints are still the literal integer-quotient endpoints;
only the integration variable has changed. -/
def fourFiveLastPrimePhysicalIntegral
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Real :=
  if fourFiveLastPrimeLower q y A <= fourFiveLastPrimeUpper q B then
    (fourFivePrefixProductReal q)⁻¹ *
      ∫ t in
          fourFivePrefixProductReal q *
              (fourFiveLastPrimeLower q y A : Real)..
          fourFivePrefixProductReal q *
              (fourFiveLastPrimeUpper q B : Real),
        1 / Real.log (t / fourFivePrefixProductReal q)
  else 0

/-- Exact per-prefix physical change of variables. -/
theorem fourFiveLastPrimeIntegral_eq_physicalIntegral
    {m y A B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeIntegral q y A B =
      fourFiveLastPrimePhysicalIntegral q y A B := by
  have hQpos : 0 < fourFivePrefixProductReal q :=
    fourFivePrefixProductReal_pos hq
  have hQne : fourFivePrefixProductReal q ≠ 0 := hQpos.ne'
  by_cases hLU : fourFiveLastPrimeLower q y A <=
      fourFiveLastPrimeUpper q B
  · simp only [fourFiveLastPrimeIntegral,
      fourFiveLastPrimePhysicalIntegral, hLU, if_true]
    have hsubst := intervalIntegral.integral_comp_mul_left
      (fun t : Real =>
        1 / Real.log (t / fourFivePrefixProductReal q)) hQne
      (a := (fourFiveLastPrimeLower q y A : Real))
      (b := (fourFiveLastPrimeUpper q B : Real))
    calc
      (∫ v in (fourFiveLastPrimeLower q y A : Real)..
          (fourFiveLastPrimeUpper q B : Real), 1 / Real.log v) =
          ∫ v in (fourFiveLastPrimeLower q y A : Real)..
            (fourFiveLastPrimeUpper q B : Real),
            1 / Real.log
              (fourFivePrefixProductReal q * v /
                fourFivePrefixProductReal q) := by
        apply intervalIntegral.integral_congr
        intro v _hv
        change 1 / Real.log v =
          1 / Real.log
            (fourFivePrefixProductReal q * v /
              fourFivePrefixProductReal q)
        rw [mul_div_cancel_left₀ v hQne]
      _ = (fourFivePrefixProductReal q)⁻¹ *
          ∫ t in
              fourFivePrefixProductReal q *
                  (fourFiveLastPrimeLower q y A : Real)..
              fourFivePrefixProductReal q *
                  (fourFiveLastPrimeUpper q B : Real),
            1 / Real.log (t / fourFivePrefixProductReal q) := by
        simpa only [smul_eq_mul] using hsubst
  · simp [fourFiveLastPrimeIntegral,
      fourFiveLastPrimePhysicalIntegral, hLU]

/-- Sum of the exactly transformed physical prefix integrals. -/
def fourFiveOrderedLastPrimePhysicalLayer
    (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimePhysicalIntegral q y A B

theorem fourFiveOrderedLastPrimeIntegralLayer_eq_physicalLayer
    (m y A B : Nat) :
    fourFiveOrderedLastPrimeIntegralLayer m y A B =
      fourFiveOrderedLastPrimePhysicalLayer m y A B := by
  unfold fourFiveOrderedLastPrimeIntegralLayer
    fourFiveOrderedLastPrimePhysicalLayer
  apply Finset.sum_congr rfl
  intro q hq
  exact fourFiveLastPrimeIntegral_eq_physicalIntegral hq

/-- The common physical `t`-integral after exposing the last prime, with the
remaining `m` coordinates still carrying the actual reciprocal-prime atoms.
Only the four layers used by the ordered mixture are retained. -/
def fourFivePhysicalActualMovingLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveActualReciprocalProductOne
            (fourFiveMovingSimplexKernelOne y y
              (fourFiveRealLogCoordinate y t)) y B
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveActualReciprocalProductTwo
            (fourFiveMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t)) y B
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveActualReciprocalProductThree
            (fourFiveMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y t)) y B
  | _ => 0

/-- The same physical layer after replacing every actual reciprocal-prime
atom by its continuum log-log cell mass. -/
def fourFivePhysicalContinuumCellLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveContinuumLogLogProductOne
            (fourFiveMovingSimplexKernelOne y y
              (fourFiveRealLogCoordinate y t)) y B
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveContinuumLogLogProductTwo
            (fourFiveMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t)) y B
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveContinuumLogLogProductThree
            (fourFiveMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y t)) y B
  | _ => 0

/-- The continuum-cell layer written with the literal cell integrals
`integral_(n-1)^n dx/(x log x)`. -/
def fourFivePhysicalLebesgueCellLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLebesgueCellProductOne
            (fourFiveMovingSimplexKernelOne y y
              (fourFiveRealLogCoordinate y t)) y B
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLebesgueCellProductTwo
            (fourFiveMovingSimplexKernelTwo y y
              (fourFiveRealLogCoordinate y t)) y B
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLebesgueCellProductThree
            (fourFiveMovingSimplexKernelThree y y
              (fourFiveRealLogCoordinate y t)) y B
  | _ => 0

/-! ## The literal logarithmic moving simplex -/

/-- The untransformed logarithmic simplex for `m` preceding coordinates.
The last logarithmic coordinate is the slack `u - sum s`. -/
def fourFiveLogarithmicMovingSimplex
    (m : Nat) (u : Real) : Set (Fin m -> Real) :=
  {s | (∀ i, 1 <= s i) ∧ (∑ i, s i) <= u - 1}

/-- Density on the logarithmic moving simplex.  It is the image of
`prod dx_i/(x_i log x_i)` together with the exposed last-prime factor. -/
def fourFiveLogarithmicMovingSimplexIntegrand
    (m : Nat) (u : Real) (s : Fin m -> Real) : Real :=
  (∏ i, (s i)⁻¹) * (u - ∑ i, s i)⁻¹

/-- Literal untransformed moving-simplex kernel. -/
def fourFiveLogarithmicMovingSimplexKernel
    (m : Nat) (u : Real) : Real :=
  ∫ s in fourFiveLogarithmicMovingSimplex m u,
    fourFiveLogarithmicMovingSimplexIntegrand m u s

/-- The physical outer integral of the literal moving-simplex kernel. -/
def fourFivePhysicalMovingSimplexLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹
  | 1 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLogarithmicMovingSimplexKernel 1
            (fourFiveRealLogCoordinate y t)
  | 2 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLogarithmicMovingSimplexKernel 2
            (fourFiveRealLogCoordinate y t)
  | 3 =>
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFiveLogarithmicMovingSimplexKernel 3
            (fourFiveRealLogCoordinate y t)
  | _ => 0

/-- The already constructed fixed-simplex target, indexed by the number of
preceding coordinates rather than by the total layer number. -/
def fourFiveFixedContinuumLayer
    (m y A B : Nat) : Real :=
  match m with
  | 0 => fourFiveContinuumLayerOneMain y A B
  | 1 => fourFiveContinuumLayerTwoMain y A B
  | 2 => fourFiveContinuumLayerThreeMain y A B
  | 3 => fourFiveContinuumLayerFourMain y A B
  | _ => 0

/-! ## Exact cell-to-Lebesgue equalities under the outer integral -/

theorem fourFivePhysicalContinuumCellLayer_zero_eq_lebesgue
    (y A B : Nat) :
    fourFivePhysicalContinuumCellLayer 0 y A B =
      fourFivePhysicalLebesgueCellLayer 0 y A B := by
  rfl

theorem fourFivePhysicalContinuumCellLayer_one_eq_lebesgue
    {y A B : Nat} (hy : 2 <= y) :
    fourFivePhysicalContinuumCellLayer 1 y A B =
      fourFivePhysicalLebesgueCellLayer 1 y A B := by
  unfold fourFivePhysicalContinuumCellLayer
    fourFivePhysicalLebesgueCellLayer
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t _ht
  exact fourFiveContinuumLogLogProductOne_eq_lebesgueCells
    (fourFiveMovingSimplexKernelOne y y
      (fourFiveRealLogCoordinate y t)) hy

theorem fourFivePhysicalContinuumCellLayer_two_eq_lebesgue
    {y A B : Nat} (hy : 2 <= y) :
    fourFivePhysicalContinuumCellLayer 2 y A B =
      fourFivePhysicalLebesgueCellLayer 2 y A B := by
  unfold fourFivePhysicalContinuumCellLayer
    fourFivePhysicalLebesgueCellLayer
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t _ht
  exact fourFiveContinuumLogLogProductTwo_eq_lebesgueCells
    (fourFiveMovingSimplexKernelTwo y y
      (fourFiveRealLogCoordinate y t)) hy

theorem fourFivePhysicalContinuumCellLayer_three_eq_lebesgue
    {y A B : Nat} (hy : 2 <= y) :
    fourFivePhysicalContinuumCellLayer 3 y A B =
      fourFivePhysicalLebesgueCellLayer 3 y A B := by
  unfold fourFivePhysicalContinuumCellLayer
    fourFivePhysicalLebesgueCellLayer
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t _ht
  exact fourFiveContinuumLogLogProductThree_eq_lebesgueCells
    (fourFiveMovingSimplexKernelThree y y
      (fourFiveRealLogCoordinate y t)) hy

/-! ## Pointwise reuse of the moving-face product telescope -/

/-- At every physical outer variable, the one-coordinate actual/cell
integrands have exactly the already-proved `2 E` loss. -/
theorem abs_fourFivePhysicalMovingProductOne_sub_cell_le
    {y B : Nat} {t : Real}
    (hy : 2 <= y) (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hyB : y <= B) :
    abs (fourFiveActualReciprocalProductOne
          (fourFiveMovingSimplexKernelOne y y
            (fourFiveRealLogCoordinate y t)) y B -
        fourFiveContinuumLogLogProductOne
          (fourFiveMovingSimplexKernelOne y y
            (fourFiveRealLogCoordinate y t)) y B) <=
      2 * fourFiveReciprocalBVError y := by
  exact abs_fourFiveMovingSimplexProductOne_sub_continuum_le
    hy le_rfl hcut hyB

/-- At every physical outer variable, the two-coordinate actual/cell
integrands have the existing `4 E M` loss. -/
theorem abs_fourFivePhysicalMovingProductTwo_sub_cell_le
    {y B : Nat} {t M : Real}
    (hy : 2 <= y) (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hyB : y <= B)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M) :
    abs (fourFiveActualReciprocalProductTwo
          (fourFiveMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y t)) y B -
        fourFiveContinuumLogLogProductTwo
          (fourFiveMovingSimplexKernelTwo y y
            (fourFiveRealLogCoordinate y t)) y B) <=
      4 * fourFiveReciprocalBVError y * M := by
  exact abs_fourFiveMovingSimplexProductTwo_sub_continuum_le
    hy le_rfl hcut hyB hactualMass hcontinuumMass

/-- At every physical outer variable, the three-coordinate actual/cell
integrands have the existing `6 E M^2` loss. -/
theorem abs_fourFivePhysicalMovingProductThree_sub_cell_le
    {y B : Nat} {t M : Real}
    (hy : 2 <= y) (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hyB : y <= B)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M) :
    abs (fourFiveActualReciprocalProductThree
          (fourFiveMovingSimplexKernelThree y y
            (fourFiveRealLogCoordinate y t)) y B -
        fourFiveContinuumLogLogProductThree
          (fourFiveMovingSimplexKernelThree y y
            (fourFiveRealLogCoordinate y t)) y B) <=
      6 * fourFiveReciprocalBVError y * M ^ 2 := by
  exact abs_fourFiveMovingSimplexProductThree_sub_continuum_le
    hy le_rfl hcut hyB hactualMass hcontinuumMass

/-! ## Three new exact error interfaces and the existing product interface -/

/-- Piece 1: exact last-prime endpoints versus the common physical
actual-product `t`-integral. -/
def fourFiveLastPrimePhysicalChangeError
    (m y A B : Nat) : Real :=
  abs (fourFiveOrderedLastPrimeIntegralLayer m y A B -
    fourFivePhysicalActualMovingLayer m y A B)

/-- After the exact per-prefix substitution, Piece 1 is only the common
physical-domain/endpoint discrepancy. -/
def fourFiveLastPrimeCommonDomainError
    (m y A B : Nat) : Real :=
  abs (fourFiveOrderedLastPrimePhysicalLayer m y A B -
    fourFivePhysicalActualMovingLayer m y A B)

theorem fourFiveLastPrimePhysicalChangeError_eq_commonDomainError
    (m y A B : Nat) :
    fourFiveLastPrimePhysicalChangeError m y A B =
      fourFiveLastPrimeCommonDomainError m y A B := by
  unfold fourFiveLastPrimePhysicalChangeError
    fourFiveLastPrimeCommonDomainError
  rw [fourFiveOrderedLastPrimeIntegralLayer_eq_physicalLayer]

/-- Existing interface: actual reciprocal-prime products versus continuum
log-log cell products. -/
def fourFivePhysicalProductReplacementError
    (m y A B : Nat) : Real :=
  abs (fourFivePhysicalActualMovingLayer m y A B -
    fourFivePhysicalContinuumCellLayer m y A B)

/-- Piece 2: right-endpoint Lebesgue cells, including their strict moving
faces, versus the literal moving simplex. -/
def fourFiveLebesgueCellAggregationError
    (m y A B : Nat) : Real :=
  abs (fourFivePhysicalLebesgueCellLayer m y A B -
    fourFivePhysicalMovingSimplexLayer m y A B)

/-- Piece 3: the literal moving simplex versus the fixed-simplex kernel
`K_(m+1)`. -/
def fourFiveMovingToFixedSimplexError
    (m y A B : Nat) : Real :=
  abs (fourFivePhysicalMovingSimplexLayer m y A B -
    fourFiveFixedContinuumLayer m y A B)

/-- Positive part of the exact product replacement not already charged to
the existing moving-face product budget. -/
def fourFivePhysicalProductBudgetOverrun
    (m y A B : Nat) (E M : Real) : Real :=
  max 0 (fourFivePhysicalProductReplacementError m y A B -
    fourFiveMovingFaceProductError m E M)

/-- The exact residual budget assigned to the three new interfaces, plus
any explicitly visible overrun of the pre-existing product budget. -/
def fourFiveExactContinuumBridgeCellError
    (m y A B : Nat) (E M : Real) : Real :=
  fourFiveLastPrimePhysicalChangeError m y A B +
    fourFiveLebesgueCellAggregationError m y A B +
    fourFiveMovingToFixedSimplexError m y A B +
    fourFivePhysicalProductBudgetOverrun m y A B E M

/-! The zero-prefix layer has no product, cell-aggregation, or simplex
change-of-variables loss.  Only its literal last-prime endpoint change can
remain in the exact bridge ledger. -/

theorem fourFivePhysicalActualMovingLayer_zero_eq_fixed
    (y A B : Nat) :
    fourFivePhysicalActualMovingLayer 0 y A B =
      fourFiveFixedContinuumLayer 0 y A B := by
  rfl

theorem fourFivePhysicalProductReplacementError_zero
    (y A B : Nat) :
    fourFivePhysicalProductReplacementError 0 y A B = 0 := by
  simp [fourFivePhysicalProductReplacementError,
    fourFivePhysicalActualMovingLayer,
    fourFivePhysicalContinuumCellLayer]

theorem fourFiveLebesgueCellAggregationError_zero
    (y A B : Nat) :
    fourFiveLebesgueCellAggregationError 0 y A B = 0 := by
  simp [fourFiveLebesgueCellAggregationError,
    fourFivePhysicalLebesgueCellLayer,
    fourFivePhysicalMovingSimplexLayer]

theorem fourFiveMovingToFixedSimplexError_zero
    (y A B : Nat) :
    fourFiveMovingToFixedSimplexError 0 y A B = 0 := by
  simp [fourFiveMovingToFixedSimplexError,
    fourFivePhysicalMovingSimplexLayer, fourFiveFixedContinuumLayer,
    fourFiveContinuumLayerOneMain, fourFiveContinuumKernelOne,
    fourFiveRealLogCoordinate]

theorem fourFivePhysicalProductBudgetOverrun_zero
    (y A B : Nat) (E M : Real) :
    fourFivePhysicalProductBudgetOverrun 0 y A B E M = 0 := by
  simp [fourFivePhysicalProductBudgetOverrun,
    fourFivePhysicalProductReplacementError_zero,
    fourFiveMovingFaceProductError]

theorem fourFiveExactContinuumBridgeCellError_zero
    (y A B : Nat) (E M : Real) :
    fourFiveExactContinuumBridgeCellError 0 y A B E M =
      fourFiveLastPrimePhysicalChangeError 0 y A B := by
  simp [fourFiveExactContinuumBridgeCellError,
    fourFiveLebesgueCellAggregationError_zero,
    fourFiveMovingToFixedSimplexError_zero,
    fourFivePhysicalProductBudgetOverrun_zero]

theorem fourFivePhysicalProductReplacementError_le_budget_add_overrun
    (m y A B : Nat) (E M : Real) :
    fourFivePhysicalProductReplacementError m y A B <=
      fourFiveMovingFaceProductError m E M +
        fourFivePhysicalProductBudgetOverrun m y A B E M := by
  unfold fourFivePhysicalProductBudgetOverrun
  have hmax :
      fourFivePhysicalProductReplacementError m y A B -
          fourFiveMovingFaceProductError m E M <=
        max 0 (fourFivePhysicalProductReplacementError m y A B -
          fourFiveMovingFaceProductError m E M) :=
    le_max_right _ _
  linarith

/-! ## Pure four-stage triangle ledger -/

private theorem abs_add_four_le
    (a b c d : Real) :
    abs (a + b + c + d) <= abs a + abs b + abs c + abs d := by
  calc
    abs (a + b + c + d) <= abs (a + b + c) + abs d := abs_add_le _ _
    _ <= (abs (a + b) + abs c) + abs d := by
      linarith [abs_add_le (a + b) c]
    _ <= (abs a + abs b + abs c) + abs d := by
      linarith [abs_add_le a b]

private theorem abs_sub_le_four_stage
    (a b c d e f : Real) (hcd : c = d) :
    abs (a - f) <=
      abs (a - b) + abs (b - c) + abs (d - e) + abs (e - f) := by
  have hsplit :
      a - f = (a - b) + (b - c) + (d - e) + (e - f) := by
    rw [hcd]
    ring
  rw [hsplit]
  exact abs_add_four_le _ _ _ _

private theorem fourFiveExactLayerDecomposition
    (m y A B : Nat)
    (hcell : fourFivePhysicalContinuumCellLayer m y A B =
      fourFivePhysicalLebesgueCellLayer m y A B) :
    abs (fourFiveOrderedLastPrimeIntegralLayer m y A B -
        fourFiveFixedContinuumLayer m y A B) <=
      fourFiveLastPrimePhysicalChangeError m y A B +
        fourFivePhysicalProductReplacementError m y A B +
        fourFiveLebesgueCellAggregationError m y A B +
        fourFiveMovingToFixedSimplexError m y A B := by
  simpa only [fourFiveLastPrimePhysicalChangeError,
    fourFivePhysicalProductReplacementError,
    fourFiveLebesgueCellAggregationError,
    fourFiveMovingToFixedSimplexError] using
      abs_sub_le_four_stage
        (fourFiveOrderedLastPrimeIntegralLayer m y A B)
        (fourFivePhysicalActualMovingLayer m y A B)
        (fourFivePhysicalContinuumCellLayer m y A B)
        (fourFivePhysicalLebesgueCellLayer m y A B)
        (fourFivePhysicalMovingSimplexLayer m y A B)
        (fourFiveFixedContinuumLayer m y A B) hcell

/-- Exact bridge bound in one of the four layers.  No estimate is assumed:
the residual cell budget is the displayed sum of the three new interface
errors and the positive product-budget overrun. -/
theorem abs_fourFiveLastPrimeIntegralLayer_sub_fixedContinuumLayer_le_exact
    {m y A B : Nat} (hm : m <= 3) (hy : 2 <= y)
    (E M : Real) :
    abs (fourFiveOrderedLastPrimeIntegralLayer m y A B -
        fourFiveFixedContinuumLayer m y A B) <=
      fourFiveMovingFaceProductError m E M +
        fourFiveExactContinuumBridgeCellError m y A B E M := by
  have hcell : fourFivePhysicalContinuumCellLayer m y A B =
      fourFivePhysicalLebesgueCellLayer m y A B := by
    interval_cases m
    · exact fourFivePhysicalContinuumCellLayer_zero_eq_lebesgue y A B
    · exact fourFivePhysicalContinuumCellLayer_one_eq_lebesgue hy
    · exact fourFivePhysicalContinuumCellLayer_two_eq_lebesgue hy
    · exact fourFivePhysicalContinuumCellLayer_three_eq_lebesgue hy
  have hdecomp := fourFiveExactLayerDecomposition m y A B hcell
  have hproduct :=
    fourFivePhysicalProductReplacementError_le_budget_add_overrun
      m y A B E M
  unfold fourFiveExactContinuumBridgeCellError
  calc
    abs (fourFiveOrderedLastPrimeIntegralLayer m y A B -
        fourFiveFixedContinuumLayer m y A B) <=
      fourFiveLastPrimePhysicalChangeError m y A B +
        fourFivePhysicalProductReplacementError m y A B +
        fourFiveLebesgueCellAggregationError m y A B +
        fourFiveMovingToFixedSimplexError m y A B := hdecomp
    _ <= fourFiveLastPrimePhysicalChangeError m y A B +
        (fourFiveMovingFaceProductError m E M +
          fourFivePhysicalProductBudgetOverrun m y A B E M) +
        fourFiveLebesgueCellAggregationError m y A B +
        fourFiveMovingToFixedSimplexError m y A B := by
      gcongr
    _ = fourFiveMovingFaceProductError m E M +
        (fourFiveLastPrimePhysicalChangeError m y A B +
          fourFiveLebesgueCellAggregationError m y A B +
          fourFiveMovingToFixedSimplexError m y A B +
          fourFivePhysicalProductBudgetOverrun m y A B E M) := by
      ring

/-! ## Discharging the assembly bridge without a new contract -/

/-- The original four-line bridge proposition, instantiated with the exact
three-piece residual ledgers, is unconditional apart from `y >= 2`. -/
theorem fourFiveLastPrimeToContinuumBridge_exactDecomposition
    {y A B : Nat} (hy : 2 <= y) (E M : Real) :
    FourFiveLastPrimeToContinuumBridge y A B E M
      (fourFiveExactContinuumBridgeCellError 0 y A B E M)
      (fourFiveExactContinuumBridgeCellError 1 y A B E M)
      (fourFiveExactContinuumBridgeCellError 2 y A B E M)
      (fourFiveExactContinuumBridgeCellError 3 y A B E M) := by
  unfold FourFiveLastPrimeToContinuumBridge
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h :=
      abs_fourFiveLastPrimeIntegralLayer_sub_fixedContinuumLayer_le_exact
        (m := 0) (y := y) (A := A) (B := B) (by norm_num) hy E M
    simpa [fourFiveFixedContinuumLayer,
      fourFiveMovingFaceProductError] using h
  · have h :=
      abs_fourFiveLastPrimeIntegralLayer_sub_fixedContinuumLayer_le_exact
        (m := 1) (y := y) (A := A) (B := B) (by norm_num) hy E M
    simpa [fourFiveFixedContinuumLayer] using h
  · have h :=
      abs_fourFiveLastPrimeIntegralLayer_sub_fixedContinuumLayer_le_exact
        (m := 2) (y := y) (A := A) (B := B) (by norm_num) hy E M
    simpa [fourFiveFixedContinuumLayer] using h
  · have h :=
      abs_fourFiveLastPrimeIntegralLayer_sub_fixedContinuumLayer_le_exact
        (m := 3) (y := y) (A := A) (B := B) (by norm_num) hy E M
    simpa [fourFiveFixedContinuumLayer] using h

/-- Final ordered-mixture estimate with no continuum-bridge hypothesis.  Its
four cell entries are the exact three-piece residual ledgers above. -/
theorem fourFiveOrderedPrimeMixtureEstimate_of_exactContinuumDecomposition
    {y A B : Nat} {C X0 E M : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hyX0 : X0 <= (y : Real))
    (hy2 : 2 <= y)
    (hPNT : ∀ a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (fourFiveContinuumOrderedMixtureMain y A B)
      (fourFiveOrderedMixtureAssemblyError C y A B E M
        (fourFiveExactContinuumBridgeCellError 0 y A B E M)
        (fourFiveExactContinuumBridgeCellError 1 y A B E M)
        (fourFiveExactContinuumBridgeCellError 2 y A B E M)
        (fourFiveExactContinuumBridgeCellError 3 y A B E M)) := by
  exact fourFiveOrderedPrimeMixtureEstimate_of_lastPrime_continuumBridge
    (y := y) (A := A) (B := B) (C := C) (X0 := X0) (E := E) (M := M)
    hC hX0 hyX0 hPNT
      (fourFiveLastPrimeToContinuumBridge_exactDecomposition
        (y := y) (A := A) (B := B) hy2 E M)

end Erdos390.WholePaper.BankPaperRealization
