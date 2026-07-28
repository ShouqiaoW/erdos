import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction

/-!
# Statement audit for the actual active-measure construction

The expanded checks expose the forced scaled seed, its exact literal mass,
and the minimized coordinate-fit equivalence.  The final census contains
every public declaration in the source module.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

example
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) (m : D.Sample) :
    bankPaperCanonicalScaledActiveSeed T q m =
        q * T.baseline.baseWeight m ∧
      bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalScaledActiveSeed T q) = q := by
  exact ⟨rfl,
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed T q⟩

example
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
        preSelector (bankPaperCanonicalScaledActiveSeed T q) ↔
      1 <= q ∧
        (forall m : D.Sample,
          q * T.baseline.baseWeight m <= preSelector (D.value m)) := by
  simpa only [BankPaperCanonicalActualCoordinateFit,
    bankPaperCanonicalScaledActiveSeed] using
      (bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
        D T candidates preSelector q hsep hvalues hselectorNonneg)

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I) :
    bankPaperCanonicalPaperDataActiveSeed
        B I hlo hhi Rhead Kphysical =
      bankPaperCanonicalScaledActiveSeed
        (B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical)
        Rhead.activeMass := by
  rfl

/-! ## Complete public declaration census -/

#check bankPaperCanonicalScaledActiveSeed
#check bankPaperCanonicalScaledActiveSeed_nonneg
#check bankPaperCanonicalScaledActiveSeed_pos
#check bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg
#check bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
#check bankPaperCanonicalStructuredActiveValues
#check mem_bankPaperCanonicalStructuredActiveValues
#check bankPaperCanonicalScaledActivePreSelector
#check bankPaperCanonicalActualActiveMeasureConstructor_self
#check exists_bankPaperCanonicalActualActiveMeasureConstructor
#check BankPaperCanonicalActualActivePlacement
#check bankPaperCanonicalActualActiveMeasureConstructor_scaled_iff
#check bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
#check BankPaperCanonicalActualCoordinateFit
#check bankPaperCanonicalActualActivePlacement_of_coordinateFit
#check bankPaperCanonicalActualActivePlacement_iff_coordinateFit
#check bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
#check bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
#check bankPaperCanonicalZeroPreSelector_not_coordinateFit
#check bankPaperCanonicalStructuredValue_mem_guardedCandidates
#check bankPaperCanonicalActualActiveMeasureConstructor_guarded_of_coordinateFit
#check exists_bankPaperCanonicalActualActiveMeasureConstructor_of_guardedBridge
#check bankPaperCanonicalPaperDataActiveSeed
#check bankPaperCanonicalLiteralActiveMass_paperDataActiveSeed

end

end Erdos390.WholePaper
