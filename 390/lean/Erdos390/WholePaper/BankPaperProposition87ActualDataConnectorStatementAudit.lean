import Erdos390.WholePaper.BankPaperProposition87ActualDataConnector

/-!
# Statement audit for the actual Proposition 8.7 paper-data connector

The expanded checks expose the three choices which must not be normalized
away: `q_n` is the sum of the active seed, the protected frozen remainder is
`preSelector - activeSeedAmbient`, and the P87 active marked target is the
selector-tail target minus that frozen contribution.  The final census lists
every public declaration in the source module.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

example
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) :
    bankPaperCanonicalLiteralActiveMass D activeSeed =
        ∑ m, activeSeed m ∧
      (BankPaperCanonicalActualActiveMeasureConstructor
          D T candidates preSelector activeSeed ↔
        let q := ∑ m : D.Sample, activeSeed m
        1 <= q ∧
          (forall m : D.Sample,
            activeSeed m = q * T.baseline.baseWeight m) ∧
          (∀ m : D.Sample, D.value m ∈ candidates) ∧
          ∀ a ∈ candidates,
            bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a <=
              preSelector a) := by
  exact ⟨rfl, Iff.rfl⟩

example
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (candidates : Finset Nat)
    (preSelector : Nat -> Real) (activeSeed : D.Sample -> Real)
    (a : Nat) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          D candidates preSelector activeSeed) a =
      if a ∈ candidates then
        preSelector a -
          bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a
      else 0 := by
  exact frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight
    D candidates preSelector activeSeed a

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (p : Nat) :
    bankPaperCanonicalActualActiveMarkedTarget B R certificate
        fixed candidates preSelector activeSeed p =
      ((certificate.selectorTailTarget R fixed).factorization p : Real) -
        ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
              B.sampleData candidates preSelector activeSeed a *
            valuation p (bankPaperCanonicalActualFrozenValue a) := by
  rfl

/-! ## Complete public declaration census -/

#check bankPaperCanonicalLiteralActiveMass
#check bankPaperCanonicalActiveSeedAmbientWeight
#check BankPaperCanonicalActualActiveMeasureConstructor
#check bankPaperCanonicalLiteralActiveMass_one_le
#check bankPaperCanonicalLiteralActiveMass_pos
#check bankPaperCanonicalActiveSeed_eq_mass_mul_baseline
#check bankPaperCanonicalActiveSeed_value_mem_candidates
#check bankPaperCanonicalActiveSeed_nonneg
#check bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector
#check bankPaperCanonicalLiteralQMass
#check eventually_one_le_bankPaperCanonicalLiteralQMass
#check canonical_proposition87_actualPaperData
#check bankPaperCanonicalActualBridgeData
#check bankPaperCanonicalActualBridgeData_sampleData
#check bankPaperCanonicalActualBridgeData_q
#check bankPaperCanonicalActualBridgeData_baseWeight
#check BankPaperCanonicalActualFrozenIndex
#check bankPaperCanonicalActualFrozenValue
#check bankPaperCanonicalActualFrozenWeight
#check bankPaperCanonicalActiveSeedAmbientWeight_nonneg
#check bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_mem
#check sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass
#check frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight
#check bankPaperCanonicalActualFrozenWeight_mem_Icc
#check sum_bankPaperCanonicalActualFrozenWeight
#check exists_bankPaperCanonicalActualP87IntegerQuota
#check BridgeData.activeCoordinateWeight_zero_eq_baseline
#check BridgeData.ambientActiveWeight_zero_eq_activeSeedAmbient
#check bankPaperCanonicalActualSelectorAt_zero_eq_preSelector
#check bankPaperCanonicalActualP87SelectorSupport_eq_candidates
#check bankPaperCanonicalActualActiveMarkedTarget
#check bankPaperCanonicalActualP87EndpointSelector
#check bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget
#check bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
#check bankPaperCanonicalActualInitial_deficit_eq_activeResidual
#check bankPaperCanonicalActualP87EndpointSelector_eq_zero_of_not_mem
#check bankPaperCanonicalActualActiveValues_subset_smoothRow
#check StructuredSampleData.valuation_eq_zero_of_yNat_lt
#check Erdos390.WholePaper.BridgeData.paperMoment_markedValuation_eq_zero_of_yNat_lt
#check sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
#check bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
#check BridgeData.sum_ambientActiveWeight_eq_q_of_values_mem
#check BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
#check bankPaperCanonicalActualP87EndpointSelector_eq
#check sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector
#check bankPaperCanonicalGuardedSmoothFlexibleQuota_actualP87Endpoint
#check bankPaperCanonicalActualP87EndpointSelector_rowIntegral
#check bankPaperCanonicalActualP87PointwiseUpper
#check bankPaperCanonicalActualP87EndpointSelector_deficitSupportedOnPrimeBand
#check bankPaperCanonicalActualP87EndpointSelector_bandBalance
#check bankPaperCanonicalActualP87EndpointSelector_primeBandBalance
#check bankPaperCanonicalActualP87EndpointSelector_pointwise
#check exists_bankPaperCanonicalActualP87EndpointSelector
#check bankPaperCanonicalGuardedContinuation_with_actualPrebridge

end

end Erdos390.WholePaper
