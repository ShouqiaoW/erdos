import Erdos390.WholePaper.BankPaperFourFiveCellLebesgueIdentification

/-!
# Final factorial assembly for the ordered four/five mixture

This file is the algebraic terminus of the ordered-prime calculation.  It
defines the four fixed-simplex continuum layer mains, records the exact
`1, 1/2!, 1/3!, 1/4!` error ledger, and turns four layerwise estimates into
the repository's `FourFiveOrderedPrimeMixtureEstimate` proposition.

The second assembly theorem plugs in the exact last-prime endpoint estimates
from `BankPaperFourFiveOrderedLastPrimeExpansion`.  Its only remaining input
is the displayed four-layer bridge from the last-prime logarithmic integrals
to the fixed-simplex continuum layers.  The bridge budget exposes separately
the already-proved moving-face telescope losses

`0, 2 E, 4 E M, 6 E M^2`

and user-supplied cell-quadrature losses.  Thus the still-missing analytic
step is explicit in the theorem statement rather than hidden in a new axiom.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

/-! ## The four fixed-simplex layer main terms -/

def fourFiveContinuumLayerOneMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelOne
        (Real.log t / Real.log (y : Real))

def fourFiveContinuumLayerTwoMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelTwo
        (Real.log t / Real.log (y : Real))

def fourFiveContinuumLayerThreeMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelThree
        (Real.log t / Real.log (y : Real))

def fourFiveContinuumLayerFourMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumKernelFour
        (Real.log t / Real.log (y : Real))

/-- The exact factorial mixture of the four continuum layer mains. -/
def fourFiveContinuumOrderedMixtureMain (y A B : Nat) : Real :=
  fourFiveContinuumLayerOneMain y A B +
    fourFiveContinuumLayerTwoMain y A B / 2 +
    fourFiveContinuumLayerThreeMain y A B / 6 +
    fourFiveContinuumLayerFourMain y A B / 24

/-- The same main term written as one integral of the already constructed
mixture kernel.  Equality with `fourFiveContinuumOrderedMixtureMain` follows
from ordinary linearity once the four displayed integrands are known to be
interval-integrable. -/
def fourFiveContinuumMixtureIntegralMain (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) *
    ∫ t in (A : Real)..(B : Real),
      fourFiveContinuumMixtureKernel
        (Real.log t / Real.log (y : Real))

/-- The layerwise and single-integral presentations agree whenever the four
layer integrands are interval-integrable.  This is finite linearity of the
outer integral; no Fubini interchange is involved. -/
theorem
    fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
    {y A B : Nat}
    (h1 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelOne
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real))
    (h2 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelTwo
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real))
    (h3 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelThree
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real))
    (h4 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelFour
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real)) :
    fourFiveContinuumOrderedMixtureMain y A B =
      fourFiveContinuumMixtureIntegralMain y A B := by
  have h12 := h1.add (h2.div_const 2)
  have h123 := h12.add (h3.div_const 6)
  have hintegral :
      (∫ t in (A : Real)..(B : Real),
        fourFiveContinuumMixtureKernel
          (Real.log t / Real.log (y : Real))) =
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
            (Real.log t / Real.log (y : Real))) +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelTwo
            (Real.log t / Real.log (y : Real))) / 2 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelThree
            (Real.log t / Real.log (y : Real))) / 6 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelFour
            (Real.log t / Real.log (y : Real))) / 24 := by
    unfold fourFiveContinuumMixtureKernel
    calc
      (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
              (Real.log t / Real.log (y : Real)) +
            fourFiveContinuumKernelTwo
                (Real.log t / Real.log (y : Real)) / 2 +
            fourFiveContinuumKernelThree
                (Real.log t / Real.log (y : Real)) / 6 +
            fourFiveContinuumKernelFour
                (Real.log t / Real.log (y : Real)) / 24) =
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
                (Real.log t / Real.log (y : Real)) +
              fourFiveContinuumKernelTwo
                  (Real.log t / Real.log (y : Real)) / 2 +
              fourFiveContinuumKernelThree
                  (Real.log t / Real.log (y : Real)) / 6) +
          ∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real)) / 24 :=
        intervalIntegral.integral_add h123 (h4.div_const 24)
      _ =
        ((∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
                (Real.log t / Real.log (y : Real)) +
              fourFiveContinuumKernelTwo
                (Real.log t / Real.log (y : Real)) / 2) +
            ∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelThree
                (Real.log t / Real.log (y : Real)) / 6) +
          ∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real)) / 24 := by
        exact congrArg
          (fun z : Real => z +
            (∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelFour
                (Real.log t / Real.log (y : Real)) / 24))
          (intervalIntegral.integral_add h12 (h3.div_const 6))
      _ =
        (((∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelOne
              (Real.log t / Real.log (y : Real))) +
            ∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelTwo
                (Real.log t / Real.log (y : Real)) / 2) +
            ∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelThree
                (Real.log t / Real.log (y : Real)) / 6) +
          ∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real)) / 24 := by
        exact congrArg
          (fun z : Real =>
            (z +
              (∫ t in (A : Real)..(B : Real),
                fourFiveContinuumKernelThree
                  (Real.log t / Real.log (y : Real)) / 6)) +
            (∫ t in (A : Real)..(B : Real),
              fourFiveContinuumKernelFour
                (Real.log t / Real.log (y : Real)) / 24))
          (intervalIntegral.integral_add h1 (h2.div_const 2))
      _ =
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelOne
            (Real.log t / Real.log (y : Real))) +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelTwo
            (Real.log t / Real.log (y : Real))) / 2 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelThree
            (Real.log t / Real.log (y : Real))) / 6 +
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumKernelFour
            (Real.log t / Real.log (y : Real))) / 24 := by
        simp only [intervalIntegral.integral_div]
  calc
    fourFiveContinuumOrderedMixtureMain y A B =
        (1 / Real.log (y : Real)) *
          ((∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelOne
              (Real.log t / Real.log (y : Real))) +
          (∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelTwo
              (Real.log t / Real.log (y : Real))) / 2 +
          (∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelThree
              (Real.log t / Real.log (y : Real))) / 6 +
          (∫ t in (A : Real)..(B : Real),
            fourFiveContinuumKernelFour
              (Real.log t / Real.log (y : Real))) / 24) := by
      unfold fourFiveContinuumOrderedMixtureMain
        fourFiveContinuumLayerOneMain fourFiveContinuumLayerTwoMain
        fourFiveContinuumLayerThreeMain fourFiveContinuumLayerFourMain
      ring
    _ = (1 / Real.log (y : Real)) *
        (∫ t in (A : Real)..(B : Real),
          fourFiveContinuumMixtureKernel
            (Real.log t / Real.log (y : Real))) :=
      congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
        hintegral.symm
    _ = fourFiveContinuumMixtureIntegralMain y A B := by
      rfl

/-- In the actual four/five chamber, the standard positive-endpoint
assumptions and the padded logarithmic-coordinate range discharge all four
interval-integrability hypotheses in the finite-linearity theorem above. -/
theorem
    fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_paperRange
    {y A B : Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      Real.log t / Real.log (y : Real) ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) :
    fourFiveContinuumOrderedMixtureMain y A B =
      fourFiveContinuumMixtureIntegralMain y A B := by
  have hAB' : (A : Real) <= (B : Real) := by
    exact_mod_cast hAB
  have hypos : (0 : Real) < (y : Real) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hy)
  have hyA' : (y : Real) <= (A : Real) := by
    exact_mod_cast hyA
  have hcoord : ContinuousOn
      (fun t : Real => Real.log t / Real.log (y : Real))
      (Set.Icc (A : Real) (B : Real)) := by
    intro t ht
    have ht0 : t ≠ 0 :=
      ne_of_gt (hypos.trans_le (hyA'.trans ht.1))
    exact ((Real.continuousAt_log ht0).div_const
      (Real.log (y : Real))).continuousWithinAt
  have hk1 : ContinuousOn fourFiveContinuumKernelOne
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
    intro u hu
    exact (hasDerivAt_fourFiveContinuumKernelOne
      (by linarith [hu.1])).continuousAt.continuousWithinAt
  have hk2 : ContinuousOn fourFiveContinuumKernelTwo
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
    intro u hu
    exact (hasDerivAt_fourFiveContinuumKernelTwo
      hu).continuousAt.continuousWithinAt
  have hk3 : ContinuousOn fourFiveContinuumKernelThree
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
    intro u hu
    exact (hasDerivAt_fourFiveContinuumKernelThree
      hu).continuousAt.continuousWithinAt
  have hk4 : ContinuousOn fourFiveContinuumKernelFour
      (Set.Icc ((41 : Real) / 10) ((47 : Real) / 10)) := by
    intro u hu
    exact (hasDerivAt_fourFiveContinuumKernelFour
      hu).continuousAt.continuousWithinAt
  have h1 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelOne
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real) :=
    (hk1.comp' hcoord hrange).intervalIntegrable_of_Icc hAB'
  have h2 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelTwo
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real) :=
    (hk2.comp' hcoord hrange).intervalIntegrable_of_Icc hAB'
  have h3 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelThree
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real) :=
    (hk3.comp' hcoord hrange).intervalIntegrable_of_Icc hAB'
  have h4 : IntervalIntegrable
      (fun t : Real => fourFiveContinuumKernelFour
        (Real.log t / Real.log (y : Real)))
      MeasureTheory.volume (A : Real) (B : Real) :=
    (hk4.comp' hcoord hrange).intervalIntegrable_of_Icc hAB'
  exact
    fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_intervalIntegrable
      h1 h2 h3 h4

/-- Exact factorial weighting of four nonnegative error ledgers. -/
def fourFiveFactorialErrorLedger
    (e1 e2 e3 e4 : Real) : Real :=
  e1 + e2 / 2 + e3 / 6 + e4 / 24

/-- The finite definition of the ordered mixture enumerated layer by layer. -/
theorem fourFiveOrderedPrimeMixture_eq_explicitLayers
    (y A B : Nat) :
    fourFiveOrderedPrimeMixture y A B =
      (fourFiveOrderedPrimeLayerMass 1 y A B : Real) +
      (fourFiveOrderedPrimeLayerMass 2 y A B : Real) / 2 +
      (fourFiveOrderedPrimeLayerMass 3 y A B : Real) / 6 +
      (fourFiveOrderedPrimeLayerMass 4 y A B : Real) / 24 := by
  norm_num [fourFiveOrderedPrimeMixture, Finset.sum_Icc_succ_top]

/-! ## Pure factorial error assembly -/

/-- Four layerwise estimates imply the final ordered-mixture estimate with
the exact factorial ledger. -/
theorem fourFiveOrderedPrimeMixtureEstimate_of_layerBounds
    {y A B : Nat} {L1 L2 L3 L4 e1 e2 e3 e4 : Real}
    (h1 : abs ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) <= e1)
    (h2 : abs ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) <= e2)
    (h3 : abs ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) <= e3)
    (h4 : abs ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) <= e4) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (L1 + L2 / 2 + L3 / 6 + L4 / 24)
      (fourFiveFactorialErrorLedger e1 e2 e3 e4) := by
  unfold FourFiveOrderedPrimeMixtureEstimate
  rw [fourFiveOrderedPrimeMixture_eq_explicitLayers]
  unfold fourFiveFactorialErrorLedger
  have h2' :
      abs (((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2) <=
        e2 / 2 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right h2 (by norm_num)
  have h3' :
      abs (((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6) <=
        e3 / 6 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right h3 (by norm_num)
  have h4' :
      abs (((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24) <=
        e4 / 24 := by
    rw [abs_div]
    norm_num
    exact div_le_div_of_nonneg_right h4 (by norm_num)
  have hrewrite :
      (fourFiveOrderedPrimeLayerMass 1 y A B : Real) +
          (fourFiveOrderedPrimeLayerMass 2 y A B : Real) / 2 +
          (fourFiveOrderedPrimeLayerMass 3 y A B : Real) / 6 +
          (fourFiveOrderedPrimeLayerMass 4 y A B : Real) / 24 -
        (L1 + L2 / 2 + L3 / 6 + L4 / 24) =
      ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
        ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2 +
        ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6 +
        ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24 := by
    ring
  rw [hrewrite]
  calc
    abs (((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
          ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2 +
          ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6 +
          ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24) <=
        abs ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
          abs (((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2) +
          abs (((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6) +
          abs (((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24) := by
      calc
        abs (((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
            ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2 +
            ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6 +
            ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24) <=
          abs (((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
            ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2 +
            ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6) +
          abs (((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24) :=
            abs_add_le _ _
        _ <= (abs (((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
              ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2) +
            abs (((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6)) +
          abs (((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24) :=
            by
              have htriangle := abs_add_le
                (((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
                  ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2)
                (((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6)
              linarith
        _ <= (abs ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1) +
              abs (((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2) +
            abs (((fourFiveOrderedPrimeLayerMass 3 y A B : Real) - L3) / 6)) +
          abs (((fourFiveOrderedPrimeLayerMass 4 y A B : Real) - L4) / 24) :=
            by
              have htriangle := abs_add_le
                ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) - L1)
                (((fourFiveOrderedPrimeLayerMass 2 y A B : Real) - L2) / 2)
              linarith
    _ <= e1 + e2 / 2 + e3 / 6 + e4 / 24 := by
      exact add_le_add (add_le_add (add_le_add h1 h2') h3') h4'

/-! ## The exact remaining bridge contract -/

/-- Product-telescope loss in a layer with `m = 0,1,2,3` preceding prime
coordinates.  These are exactly the constants proved by the moving-face BV
instantiations: `V = 2` times the `m`-term product telescope. -/
def fourFiveMovingFaceProductError
    (m : Nat) (E M : Real) : Real :=
  match m with
  | 0 => 0
  | 1 => 2 * E
  | 2 => 4 * E * M
  | 3 => 6 * E * M ^ 2
  | _ => 0

/-- Four explicit bridge estimates from the post-last-prime main terms to
the fixed-simplex continuum layers.  The first summand in each budget is
the proved product-measure telescope loss; `cell0,...,cell3` isolate the
remaining cell quadrature / physical change-of-variables loss. -/
def FourFiveLastPrimeToContinuumBridge
    (y A B : Nat) (E M cell0 cell1 cell2 cell3 : Real) : Prop :=
  abs (fourFiveOrderedLastPrimeIntegralLayer 0 y A B -
      fourFiveContinuumLayerOneMain y A B) <= cell0 ∧
  abs (fourFiveOrderedLastPrimeIntegralLayer 1 y A B -
      fourFiveContinuumLayerTwoMain y A B) <=
        fourFiveMovingFaceProductError 1 E M + cell1 ∧
  abs (fourFiveOrderedLastPrimeIntegralLayer 2 y A B -
      fourFiveContinuumLayerThreeMain y A B) <=
        fourFiveMovingFaceProductError 2 E M + cell2 ∧
  abs (fourFiveOrderedLastPrimeIntegralLayer 3 y A B -
      fourFiveContinuumLayerFourMain y A B) <=
        fourFiveMovingFaceProductError 3 E M + cell3

/-- Full exact error ledger: last-prime endpoint losses, moving-face product
losses, and cell quadrature losses, all with factorial weights. -/
def fourFiveOrderedMixtureAssemblyError
    (C : Real) (y A B : Nat) (E M cell0 cell1 cell2 cell3 : Real) : Real :=
  fourFiveFactorialErrorLedger
    (fourFiveOrderedLastPrimeEndpointErrorLayer C 0 y A B + cell0)
    (fourFiveOrderedLastPrimeEndpointErrorLayer C 1 y A B +
      fourFiveMovingFaceProductError 1 E M + cell1)
    (fourFiveOrderedLastPrimeEndpointErrorLayer C 2 y A B +
      fourFiveMovingFaceProductError 2 E M + cell2)
    (fourFiveOrderedLastPrimeEndpointErrorLayer C 3 y A B +
      fourFiveMovingFaceProductError 3 E M + cell3)

/-- Final ordered-mixture assembly.  All finite combinatorics, exact moving
prime endpoints, fifth-log endpoint losses, factorial constants, and
moving-face product constants are discharged here.  The only hypothesis not
already supplied by an earlier theorem is the explicit four-line continuum
bridge above. -/
theorem fourFiveOrderedPrimeMixtureEstimate_of_lastPrime_continuumBridge
    {y A B : Nat} {C X0 E M cell0 cell1 cell2 cell3 : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hy : X0 <= (y : Real))
    (hPNT : ∀ a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5)
    (hbridge : FourFiveLastPrimeToContinuumBridge
      y A B E M cell0 cell1 cell2 cell3) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (fourFiveContinuumOrderedMixtureMain y A B)
      (fourFiveOrderedMixtureAssemblyError
        C y A B E M cell0 cell1 cell2 cell3) := by
  have hend0 := abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le
    (m := 0) (y := y) (A := A) (B := B) hC hX0 hy hPNT
  have hend1 := abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le
    (m := 1) (y := y) (A := A) (B := B) hC hX0 hy hPNT
  have hend2 := abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le
    (m := 2) (y := y) (A := A) (B := B) hC hX0 hy hPNT
  have hend3 := abs_fourFiveOrderedPrimeLayerMass_sub_lastPrimeIntegral_le
    (m := 3) (y := y) (A := A) (B := B) hC hX0 hy hPNT
  have hlayer0 :
      abs ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) -
          fourFiveContinuumLayerOneMain y A B) <=
        fourFiveOrderedLastPrimeEndpointErrorLayer C 0 y A B + cell0 := by
    calc
      abs ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) -
          fourFiveContinuumLayerOneMain y A B) <=
        abs ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) -
          fourFiveOrderedLastPrimeIntegralLayer 0 y A B) +
        abs (fourFiveOrderedLastPrimeIntegralLayer 0 y A B -
          fourFiveContinuumLayerOneMain y A B) := by
            rw [show
              (fourFiveOrderedPrimeLayerMass 1 y A B : Real) -
                  fourFiveContinuumLayerOneMain y A B =
                ((fourFiveOrderedPrimeLayerMass 1 y A B : Real) -
                  fourFiveOrderedLastPrimeIntegralLayer 0 y A B) +
                (fourFiveOrderedLastPrimeIntegralLayer 0 y A B -
                  fourFiveContinuumLayerOneMain y A B) by ring]
            exact abs_add_le _ _
      _ <= fourFiveOrderedLastPrimeEndpointErrorLayer C 0 y A B + cell0 :=
        add_le_add hend0 hbridge.1
  have hlayer1 :
      abs ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) -
          fourFiveContinuumLayerTwoMain y A B) <=
        fourFiveOrderedLastPrimeEndpointErrorLayer C 1 y A B +
          fourFiveMovingFaceProductError 1 E M + cell1 := by
    calc
      abs ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) -
          fourFiveContinuumLayerTwoMain y A B) <=
        abs ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) -
          fourFiveOrderedLastPrimeIntegralLayer 1 y A B) +
        abs (fourFiveOrderedLastPrimeIntegralLayer 1 y A B -
          fourFiveContinuumLayerTwoMain y A B) := by
            rw [show
              (fourFiveOrderedPrimeLayerMass 2 y A B : Real) -
                  fourFiveContinuumLayerTwoMain y A B =
                ((fourFiveOrderedPrimeLayerMass 2 y A B : Real) -
                  fourFiveOrderedLastPrimeIntegralLayer 1 y A B) +
                (fourFiveOrderedLastPrimeIntegralLayer 1 y A B -
                  fourFiveContinuumLayerTwoMain y A B) by ring]
            exact abs_add_le _ _
      _ <= fourFiveOrderedLastPrimeEndpointErrorLayer C 1 y A B +
          (fourFiveMovingFaceProductError 1 E M + cell1) :=
        add_le_add hend1 hbridge.2.1
      _ = fourFiveOrderedLastPrimeEndpointErrorLayer C 1 y A B +
          fourFiveMovingFaceProductError 1 E M + cell1 := by ring
  have hlayer2 :
      abs ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) -
          fourFiveContinuumLayerThreeMain y A B) <=
        fourFiveOrderedLastPrimeEndpointErrorLayer C 2 y A B +
          fourFiveMovingFaceProductError 2 E M + cell2 := by
    calc
      abs ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) -
          fourFiveContinuumLayerThreeMain y A B) <=
        abs ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) -
          fourFiveOrderedLastPrimeIntegralLayer 2 y A B) +
        abs (fourFiveOrderedLastPrimeIntegralLayer 2 y A B -
          fourFiveContinuumLayerThreeMain y A B) := by
            rw [show
              (fourFiveOrderedPrimeLayerMass 3 y A B : Real) -
                  fourFiveContinuumLayerThreeMain y A B =
                ((fourFiveOrderedPrimeLayerMass 3 y A B : Real) -
                  fourFiveOrderedLastPrimeIntegralLayer 2 y A B) +
                (fourFiveOrderedLastPrimeIntegralLayer 2 y A B -
                  fourFiveContinuumLayerThreeMain y A B) by ring]
            exact abs_add_le _ _
      _ <= fourFiveOrderedLastPrimeEndpointErrorLayer C 2 y A B +
          (fourFiveMovingFaceProductError 2 E M + cell2) :=
        add_le_add hend2 hbridge.2.2.1
      _ = fourFiveOrderedLastPrimeEndpointErrorLayer C 2 y A B +
          fourFiveMovingFaceProductError 2 E M + cell2 := by ring
  have hlayer3 :
      abs ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) -
          fourFiveContinuumLayerFourMain y A B) <=
        fourFiveOrderedLastPrimeEndpointErrorLayer C 3 y A B +
          fourFiveMovingFaceProductError 3 E M + cell3 := by
    calc
      abs ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) -
          fourFiveContinuumLayerFourMain y A B) <=
        abs ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) -
          fourFiveOrderedLastPrimeIntegralLayer 3 y A B) +
        abs (fourFiveOrderedLastPrimeIntegralLayer 3 y A B -
          fourFiveContinuumLayerFourMain y A B) := by
            rw [show
              (fourFiveOrderedPrimeLayerMass 4 y A B : Real) -
                  fourFiveContinuumLayerFourMain y A B =
                ((fourFiveOrderedPrimeLayerMass 4 y A B : Real) -
                  fourFiveOrderedLastPrimeIntegralLayer 3 y A B) +
                (fourFiveOrderedLastPrimeIntegralLayer 3 y A B -
                  fourFiveContinuumLayerFourMain y A B) by ring]
            exact abs_add_le _ _
      _ <= fourFiveOrderedLastPrimeEndpointErrorLayer C 3 y A B +
          (fourFiveMovingFaceProductError 3 E M + cell3) :=
        add_le_add hend3 hbridge.2.2.2
      _ = fourFiveOrderedLastPrimeEndpointErrorLayer C 3 y A B +
          fourFiveMovingFaceProductError 3 E M + cell3 := by ring
  unfold fourFiveContinuumOrderedMixtureMain
    fourFiveOrderedMixtureAssemblyError
  exact fourFiveOrderedPrimeMixtureEstimate_of_layerBounds
    hlayer0 hlayer1 hlayer2 hlayer3

/-- Unconditional endpoint-witness version of the final assembly. -/
theorem exists_fourFiveOrderedPrimeMixtureEstimate_of_continuumBridge :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      ∀ {y A B : Nat} {E M cell0 cell1 cell2 cell3 : Real},
        X0 <= (y : Real) ->
        FourFiveLastPrimeToContinuumBridge
          y A B E M cell0 cell1 cell2 cell3 ->
        FourFiveOrderedPrimeMixtureEstimate y A B
          (fourFiveContinuumOrderedMixtureMain y A B)
          (fourFiveOrderedMixtureAssemblyError
            C y A B E M cell0 cell1 cell2 cell3) := by
  obtain ⟨C, hC, X0, hX0, hPNT⟩ :=
    exists_abs_fourFivePrimeCounting_sub_integral_inv_log_le
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro y A B E M cell0 cell1 cell2 cell3 hy hbridge
  exact fourFiveOrderedPrimeMixtureEstimate_of_lastPrime_continuumBridge
    hC hX0 hy hPNT hbridge

end Erdos390.WholePaper.BankPaperRealization
