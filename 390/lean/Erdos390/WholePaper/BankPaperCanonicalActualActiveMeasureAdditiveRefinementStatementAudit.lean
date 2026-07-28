import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureAdditiveRefinement

/-!
# Statement audit for the additive actual-active-measure connector

The expanded example exposes the exact output selector and active seed.
The final census contains every public theorem in the connector.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

example
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
          Set.Icc (0 : Real) 1) :=
  bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement
    B R certificate deltaStar betaProt baseSelector T q hq hsep
      hKh hlower hupper hnotGuard hbetaProt hbaseSelectorFeasible hcapacity

/-! ## Complete public theorem census -/

#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_coordinateFit
#check bankPaperCanonicalGuardedSmoothAdditiveRefinement_nonneg
#check bankPaperCanonicalActualActiveMeasureConstructor_of_additiveRefinement
#check bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
#check bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
#check bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_not_mem
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_base_outside_smoothRow
#check bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_scaled_apply_of_value_of_not_mem_pool
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_of_mem_pool
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_zero_of_value_of_not_mem_pool
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_frozenAmbientWeight_eq_of_value
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_nonneg
#check BankPaperCanonicalStructuredAdditivePlacementCapacity
#check bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_mem_Icc
#check bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
#check bankPaperCanonicalStructuredAdditivePlacementCapacity_of_cellDensity
#check bankPaperCanonicalActualActiveMeasureConstructor_of_structuredAdditivePlacement
#check bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement
#check bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_physicalIntervals
#check bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_cellDensity

end BankPaperRealization

end

end Erdos390.WholePaper
