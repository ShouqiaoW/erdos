import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction
import Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement

/-!
# Actual active measure carried by the protected additive refinement

The canonical scaled active seed has exact literal mass `q`.  The protected
additive refinement places its ambient push-forward below the pre-selector
by construction: on every active coordinate it is the active weight plus
the nonnegative protected constant `betaProt / L`.

This file joins those two independent facts.  It proves the minimized
coordinate-fit predicate, candidate nonnegativity, and hence the full
actual-active-measure constructor on the literal guarded candidate set.
The first connector below records the older, stronger hypothesis that all
structured active values lie in the guarded *broad* correction pool.  That
hypothesis is false for the nonzero paper head vertices: the correction pool
is head-free.  The second half of the file therefore gives the literal
paper-faithful placement.  It extends the protected refinement only on the
finite structured active image, which already lies in the guarded smooth
row, and leaves the old refinement unchanged on its whole correction pool.
Its exact capacity predicate is discharged either pointwise or from the
existing cell-density/base-weight bound.

No rounded-selector transport is asserted here.  Replacing a smooth row
can change its integer row sum and prime moments; those equalities are the
separate additive-ledger boundary recorded by the refinement module.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Pointwise fit and feasibility -/

/-- On every structured active coordinate, the additive refinement carries
the canonical scaled seed.  The protected summand only contributes a
nonnegative reserve. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_coordinateFit
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbetaProt : 0 <= betaProt)
    (hactiveBroad : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1) :
    BankPaperCanonicalActualCoordinateFit B.sampleData T
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)) q := by
  intro m
  rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
    B R certificate baseSelector
      (bankPaperCanonicalScaledActiveSeed T q) (hactiveBroad m),
    bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      B.sampleData T q hsep m]
  exact le_add_of_nonneg_left (div_nonneg hbetaProt B.L_pos.le)

/-- A nonnegative base selector and nonnegative protected/active pieces make
the additive refinement nonnegative on the entire guarded candidate set. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_nonneg
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hq : 0 <= q) (hbetaProt : 0 <= betaProt)
    (hbaseSelectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet
        certificate deltaStar K,
      0 <= bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) a := by
  intro a ha
  by_cases hpool : a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1
  · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hpool]
    exact add_nonneg (div_nonneg hbetaProt B.L_pos.le)
      (bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg T hq a)
  · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
      B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hpool]
    exact hbaseSelectorNonneg a ha

/-! ## Full guarded actual-measure constructor -/

/-- The protected additive refinement carries the literal canonical active
measure on the guarded candidate set.  Besides the existing interval/guard
geometry, its only local inputs are nonnegativity and membership of each
structured active value in the refined smooth broad pool. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_of_additiveRefinement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a)
    (hactiveBroad : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q))
      (bankPaperCanonicalScaledActiveSeed T q) := by
  apply bankPaperCanonicalActualActiveMeasureConstructor_guarded_of_coordinateFit
    B R certificate deltaStar T
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q))
      q hq hsep hKh hlower hupper hnotGuard
  · exact bankPaperCanonicalGuardedSmoothAdditiveRefinement_nonneg
      B R certificate deltaStar betaProt baseSelector T q
        (zero_le_one.trans hq) hbetaProt hbaseSelectorNonneg
  · exact bankPaperCanonicalGuardedSmoothAdditiveRefinement_coordinateFit
      B R certificate deltaStar betaProt baseSelector T q hsep
        hbetaProt hactiveBroad

/-! ## Structured placement on the whole guarded smooth row

The broad correction pool is the head-free part of the smooth row, whereas
the structured sample contains the nonzero paper head vertices as well.  The
following selector therefore keeps the protected refinement on its original
pool and, at every remaining structured active value, installs precisely the
active seed (the protected layer is zero there). -/

/-- Fixed physical endpoints in `[1,2]` put every structured value in the
literal interval `(n,2n]`. -/
theorem bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n) :
    (forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.value m <= 2 * B.sampleData.n := by
  constructor
  · intro m
    have hnlo : B.sampleData.n <=
        B.sampleData.lo (B.sampleData.cellOf m).2 := by
      rw [hlo]
      unfold physicalBound
      apply Nat.le_floor
      exact_mod_cast (show (B.sampleData.n : Real) <=
        I.lower (B.sampleData.cellOf m).2 *
          (B.sampleData.n : Real) by
        nlinarith [show (0 : Real) <= (B.sampleData.n : Real) by
          positivity,
          hlowerOne (B.sampleData.cellOf m).2])
    exact hnlo.trans_lt (B.sampleData.lo_lt_value m)
  · intro m
    let sigma := (B.sampleData.cellOf m).2
    have hvalue : B.sampleData.value m <=
        physicalBound (I.upper sigma) B.sampleData.n := by
      simpa only [sigma, hhi] using B.sampleData.value_le_hi m
    have hupperPos : 0 < I.upper sigma :=
      (I.lower_pos sigma).trans (I.lower_lt_upper sigma)
    have hfloor :
        (physicalBound (I.upper sigma) B.sampleData.n : Real) <=
          I.upper sigma * (B.sampleData.n : Real) := by
      unfold physicalBound
      exact Nat.floor_le
        (mul_nonneg hupperPos.le (by positivity))
    have htwo : I.upper sigma * (B.sampleData.n : Real) <=
        2 * (B.sampleData.n : Real) :=
      mul_le_mul_of_nonneg_right (hupperTwo sigma) (by positivity)
    have hbound : physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n := by
      have hcast := hfloor.trans htwo
      exact_mod_cast hcast
    exact hvalue.trans hbound

/-- Physical fixed-partition endpoints, pointwise rough-guard avoidance, and the rough tail
inequality place every structured head cell in the guarded smooth row. -/
theorem bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  have hbounds := bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    B I hlowerOne hupperTwo hlo hhi
  intro a ha
  apply bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
    B R certificate deltaStar hKh hbounds.1 hbounds.2 hnotGuard
  exact mem_bankPaperCanonicalBridgeActiveValues.mpr
    (mem_bankPaperCanonicalStructuredActiveValues.mp ha)

/-- The structured active image has the guarded-smooth-row support already
proved by the rough-row geometry.  This is the exact support theorem needed
below; no ratio-cell occupancy hypothesis enters this placement. -/
theorem bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  intro a ha
  apply bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
    B R certificate deltaStar hKh hlower hupper hnotGuard
  exact mem_bankPaperCanonicalBridgeActiveValues.mpr
    (mem_bankPaperCanonicalStructuredActiveValues.mp ha)

/-- Extend the protected additive refinement from the head-free correction
pool to the complete finite image of the structured sample.  On an active
value outside the correction pool, the protected layer reduces to zero. -/
def bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (a : Nat) : Real :=
  if a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData then
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
        deltaStar betaProt a +
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed a
  else
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
      deltaStar betaProt baseSelector activeSeed a

@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
          deltaStar betaProt a +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData activeSeed a := by
  simp [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector, ha]

@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∉ bankPaperCanonicalStructuredActiveValues B.sampleData) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed a := by
  simp [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector, ha]

/-- On the original correction pool the extended selector is exactly the
old protected refinement, including at the two zero-head active cells. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K) B R certificate
        deltaStar betaProt baseSelector activeSeed a := by
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector activeSeed hactive,
    bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
      B R certificate ha,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector activeSeed ha]
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector activeSeed hactive]

/-- If both possible modification supports are known to lie in the smooth
row, the extended selector leaves every coordinate outside that row equal to
the supplied base selector. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {a : Nat}
    (ha : a ∉ R.roughCanonicalGuardedRow certificate deltaStar K 1) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed a =
      baseSelector a := by
  have hnotActive :
      a ∉ bankPaperCanonicalStructuredActiveValues B.sampleData := by
    intro hactive
    exact ha (hactiveSmooth hactive)
  have hnotPool :
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 := by
    intro hpool
    exact ha
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 hpool)
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector activeSeed hnotActive,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
      B R certificate baseSelector activeSeed hnotPool]

/-- The protected layer is nonnegative everywhere, not merely on its pool. -/
theorem bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (hbetaProt : 0 <= betaProt)
    (a : Nat) :
    0 <= bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate deltaStar betaProt a := by
  by_cases ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool
      certificate deltaStar B.sampleData.W K 1
  · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
      B R certificate ha]
    exact div_nonneg hbetaProt B.L_pos.le
  · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
      B R certificate ha]

/-- Every structured coordinate carries its scaled active seed, whether or
not its head pattern is trivial. -/
@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (m : B.sampleData.Sample) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)
          (B.sampleData.value m) =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
          deltaStar betaProt (B.sampleData.value m) +
        bankPaperCanonicalScaledActiveSeed T q m := by
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q)
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
    bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      B.sampleData T q hsep m]

/-- At a structured head cell outside the head-free correction pool, the
placement selector is exactly the active seed and has no protected summand. -/
@[simp] theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value_of_not_mem_pool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (m : B.sampleData.Sample)
    (hnotPool : B.sampleData.value m ∉
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)
          (B.sampleData.value m) =
      bankPaperCanonicalScaledActiveSeed T q m := by
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
      (K := K) B R certificate deltaStar betaProt baseSelector T q hsep m,
    bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
      B R certificate hnotPool,
    zero_add]

/-! ## Exact frozen remainder of the corrected placement -/

/-- On the original head-free correction pool, the corrected placement has
the same literal frozen remainder `betaProt / L` as the old refinement. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_of_mem_pool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K))
        (bankPaperCanonicalActualFrozenWeight B.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed)
          activeSeed) a =
      betaProt / B.L := by
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
  have haCandidate : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K :=
    (mem_completeRoughRowFiber.mp
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 ha)).1
  rw [if_pos haCandidate,
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
      B R certificate baseSelector activeSeed ha,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector activeSeed ha]
  ring

/-- At a structured active value outside the correction pool, the corrected
placement is wholly active, so its tagged frozen remainder is exactly zero.
This is the literal Section 8 behavior of every nonzero head cell. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_zero_of_value_of_not_mem_pool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (m : B.sampleData.Sample)
    (hCandidate : B.sampleData.value m ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
    (hnotPool : B.sampleData.value m ∉
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K))
        (bankPaperCanonicalActualFrozenWeight B.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed)
          activeSeed) (B.sampleData.value m) = 0 := by
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight,
    if_pos hCandidate,
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector activeSeed
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
    bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
      B R certificate hnotPool]
  ring

/-- Exact two-case frozen ledger at every structured active value: protected
constant on the correction pool and zero on all other head cells. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_of_value
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (m : B.sampleData.Sample)
    (hCandidate : B.sampleData.value m ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K))
        (bankPaperCanonicalActualFrozenWeight B.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed)
          activeSeed) (B.sampleData.value m) =
      if B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1 then
        betaProt / B.L
      else 0 := by
  by_cases hpool : B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1
  · rw [if_pos hpool]
    exact
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_of_mem_pool
        B R certificate baseSelector activeSeed hpool
  · rw [if_neg hpool]
    exact
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_zero_of_value_of_not_mem_pool
        B R certificate baseSelector activeSeed m hCandidate hpool

/-- The corrected structured placement has coordinate fit without the false
head-free-support premise. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbetaProt : 0 <= betaProt) :
    BankPaperCanonicalActualCoordinateFit B.sampleData T
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)) q := by
  intro m
  rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
    (K := K) B R certificate deltaStar betaProt baseSelector T q hsep m]
  exact le_add_of_nonneg_left
    (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
      (K := K) (deltaStar := deltaStar)
      B R certificate hbetaProt (B.sampleData.value m))

/-- Nonnegative base, protected, and active layers give a nonnegative
corrected selector on the complete guarded candidate set. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_nonneg
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hq : 0 <= q) (hbetaProt : 0 <= betaProt)
    (hbaseSelectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet
        certificate deltaStar K,
      0 <= bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) a := by
  intro a ha
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hactive]
    exact add_nonneg
      (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
        (K := K) (deltaStar := deltaStar)
        B R certificate hbetaProt a)
      (bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg T hq a)
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hactive]
    exact bankPaperCanonicalGuardedSmoothAdditiveRefinement_nonneg
      B R certificate deltaStar betaProt baseSelector T q hq hbetaProt
        hbaseSelectorNonneg a ha

/-! ## Exact coordinate capacity and selector feasibility -/

/-- Minimal finite capacity needed by the structured placement: the
protected constant fits at inactive correction coordinates, and the exact
protected-plus-seed weight fits at every tagged active coordinate. -/
def BankPaperCanonicalStructuredAdditivePlacementCapacity
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (T : BarycentricTarget B.sampleData) (q : Real) : Prop :=
  betaProt / B.L <= 1 ∧
    forall m : B.sampleData.Sample,
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
          deltaStar betaProt (B.sampleData.value m) +
        bankPaperCanonicalScaledActiveSeed T q m <= 1

/-- The exact capacity predicate is sufficient for full `[0,1]`
feasibility on the guarded candidate set. -/
theorem bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hq : 0 <= q) (hbetaProt : 0 <= betaProt)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbaseSelectorFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      baseSelector a ∈ Set.Icc (0 : Real) 1)
    (hcapacity : BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q) :
    ∀ a ∈ R.roughCanonicalGuardedCandidateSet
        certificate deltaStar K,
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalScaledActiveSeed T q) a ∈
        Set.Icc (0 : Real) 1 := by
  intro a haCandidate
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · obtain ⟨m, hm⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp hactive
    subst a
    rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
      (K := K) B R certificate deltaStar betaProt baseSelector T q hsep m]
    exact ⟨add_nonneg
      (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
        (K := K) (deltaStar := deltaStar)
        B R certificate hbetaProt (B.sampleData.value m))
      (bankPaperCanonicalScaledActiveSeed_nonneg T hq m),
      hcapacity.2 m⟩
  · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) hactive]
    by_cases hpool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
        B R certificate baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) hpool]
      have hzero :
          bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
        apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
        intro m hm
        exact hactive
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hm⟩)
      rw [hzero, add_zero]
      exact ⟨div_nonneg hbetaProt B.L_pos.le, hcapacity.1⟩
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
        B R certificate baseSelector
          (bankPaperCanonicalScaledActiveSeed T q) hpool]
      exact hbaseSelectorFeasible a haCandidate

/-- A pointwise `Cactive/L` active-seed bound and one fixed large-`L`
inequality imply the exact placement capacity. -/
theorem bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hbetaProt : 0 <= betaProt)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <= Cactive / B.L)
    (hlarge : betaProt + Cactive <= B.L) :
    BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q := by
  constructor
  · have hbetaLe : betaProt <= B.L :=
      (le_add_of_nonneg_right hCactive).trans hlarge
    calc
      betaProt / B.L <= B.L / B.L :=
        div_le_div_of_nonneg_right hbetaLe B.L_pos.le
      _ = 1 := div_self (ne_of_gt B.L_pos)
  · intro m
    have hprotected :
        bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
            deltaStar betaProt (B.sampleData.value m) <=
          betaProt / B.L := by
      by_cases hpool : B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1
      · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate hpool]
      · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
          B R certificate hpool]
        exact div_nonneg hbetaProt B.L_pos.le
    calc
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K) B R certificate
            deltaStar betaProt (B.sampleData.value m) +
          bankPaperCanonicalScaledActiveSeed T q m <=
        betaProt / B.L + Cactive / B.L :=
          add_le_add hprotected (hactiveSeed m)
      _ = (betaProt + Cactive) / B.L := by ring
      _ <= B.L / B.L :=
        div_le_div_of_nonneg_right hlarge B.L_pos.le
      _ = 1 := div_self (ne_of_gt B.L_pos)

/-- Existing baseline cell-mass and guard-deleted cell-cardinality estimates
supply the pointwise bound in the preceding theorem.  This is the finite
capacity connector to the fixed-partition density ledger. -/
theorem bankPaperCanonicalStructuredAdditivePlacementCapacity_of_cellDensity
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (T : BarycentricTarget B.sampleData) (q : Real)
    (hq : 0 < q) (hbetaProt : 0 <= betaProt)
    (hbaselineEq : B.baseline = T.activeMassBaseline q hq)
    (Cmass density : Real) (hCmass : 0 <= Cmass)
    (hdensity : 0 < density)
    (hmass : forall cell : Cell Head,
      B.baseline.cellMass cell <=
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : forall cell : Cell Head,
      density * (B.sampleData.n : Real) <=
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density <= B.L) :
    BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q := by
  have hB := B.baseline_baseWeight_le_of_cell_density
    Cmass density hCmass hdensity hmass hcard
  have hactiveSeed : forall m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <=
        (Cmass / density) / B.L := by
    intro m
    calc
      bankPaperCanonicalScaledActiveSeed T q m =
          (T.activeMassBaseline q hq).baseWeight m :=
        (T.activeMassBaseline_baseWeight q hq m).symm
      _ = B.baseline.baseWeight m := by
        exact congrArg
          (fun A : BaselineAllocation B.sampleData => A.baseWeight m)
          hbaselineEq.symm
      _ <= Cmass / (density * B.L) := hB m
      _ = (Cmass / density) / B.L := by
        field_simp [ne_of_gt hdensity, ne_of_gt B.L_pos]
  exact bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
    (K := K) B R certificate deltaStar betaProt T q hbetaProt
      (Cmass / density) (div_nonneg hCmass hdensity.le)
      hactiveSeed hlarge

/-! ## Full guarded constructor with the corrected placement -/

/-- The complete actual-active-measure constructor on the guarded candidate
set.  Unlike the older refinement connector, it requires only the real
interval support and pointwise rough-guard avoidance; no head-free-support
premise remains. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_of_structuredAdditivePlacement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= baseSelector a) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q))
      (bankPaperCanonicalScaledActiveSeed T q) := by
  apply bankPaperCanonicalActualActiveMeasureConstructor_guarded_of_coordinateFit
    B R certificate deltaStar T
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q))
      q hq hsep hKh hlower hupper hnotGuard
  · exact bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_nonneg
      B R certificate deltaStar betaProt baseSelector T q
        (zero_le_one.trans hq) hbetaProt hbaseSelectorNonneg
  · exact bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit
      (K := K) B R certificate deltaStar betaProt baseSelector T q hsep
        hbetaProt

/-- Constructor and `[0,1]` selector feasibility packaged together.  The
capacity premise is exactly the one discharged above by cell density. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      baseSelector a ∈ Set.Icc (0 : Real) 1)
    (hcapacity : BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalScaledActiveSeed T q))
        (bankPaperCanonicalScaledActiveSeed T q) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector
              (bankPaperCanonicalScaledActiveSeed T q) a ∈
          Set.Icc (0 : Real) 1) := by
  constructor
  · exact bankPaperCanonicalActualActiveMeasureConstructor_of_structuredAdditivePlacement
      B R certificate deltaStar betaProt baseSelector T q hq hsep
        hKh hlower hupper hnotGuard hbetaProt
        (fun a ha => (hbaseSelectorFeasible a ha).1)
  · exact bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_mem_Icc
      B R certificate deltaStar betaProt baseSelector T q
        (zero_le_one.trans hq) hbetaProt hsep hbaseSelectorFeasible hcapacity

/-- Fixed physical endpoints discharge both numerical support inequalities
in the constructor-plus-feasibility package. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_physicalIntervals
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      baseSelector a ∈ Set.Icc (0 : Real) 1)
    (hcapacity : BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt T q) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalScaledActiveSeed T q))
        (bankPaperCanonicalScaledActiveSeed T q) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector
              (bankPaperCanonicalScaledActiveSeed T q) a ∈
          Set.Icc (0 : Real) 1) := by
  have hbounds := bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
    B I hlowerOne hupperTwo hlo hhi
  exact
    bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement
      B R certificate deltaStar betaProt baseSelector T q hq hsep
        hKh hbounds.1 hbounds.2 hnotGuard hbetaProt
        hbaseSelectorFeasible hcapacity

/-- One-shot Section 8 placement connector.  The physical fixed partition
supplies candidate support, while the literal scaled baseline and
guard-deleted cell density supply the exact coordinate ceiling. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_cellDensity
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (T : BarycentricTarget B.sampleData) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 <= betaProt)
    (hbaseSelectorFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      baseSelector a ∈ Set.Icc (0 : Real) 1)
    (hbaselineEq : B.baseline = T.activeMassBaseline q
      (zero_lt_one.trans_le hq))
    (Cmass density : Real) (hCmass : 0 <= Cmass)
    (hdensity : 0 < density)
    (hmass : forall cell : Cell Head,
      B.baseline.cellMass cell <=
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : forall cell : Cell Head,
      density * (B.sampleData.n : Real) <=
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density <= B.L) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalScaledActiveSeed T q))
        (bankPaperCanonicalScaledActiveSeed T q) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt baseSelector
              (bankPaperCanonicalScaledActiveSeed T q) a ∈
          Set.Icc (0 : Real) 1) := by
  have hcapacity :=
    bankPaperCanonicalStructuredAdditivePlacementCapacity_of_cellDensity
      (K := K) B R certificate deltaStar betaProt T q
        (zero_lt_one.trans_le hq) hbetaProt hbaselineEq
        Cmass density hCmass hdensity hmass hcard hlarge
  exact
    bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_physicalIntervals
      B R certificate deltaStar betaProt baseSelector T q hq hsep
        I hlowerOne hupperTwo hlo hhi hKh hnotGuard hbetaProt
        hbaseSelectorFeasible hcapacity

end BankPaperRealization

end

end Erdos390.WholePaper
