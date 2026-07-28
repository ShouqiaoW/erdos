import Erdos390.Full.PaperCanonicalActiveMassBaseline

/-! Statement audit for the literal-active-mass baseline variant. -/

namespace Erdos390.Full

open PaperGuardCensus PaperBridgeFit

noncomputable section

example
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (q : Real) (hq : 0 < q) :
    (T.activeMassBaseline q hq).totalMass = q ∧
      (∀ c : Cell Head,
        (T.activeMassBaseline q hq).normalizedCellMass c =
          T.cellProbability c) := by
  exact ⟨T.activeMassBaseline_totalMass q hq,
    T.activeMassBaseline_normalizedCellMass q hq⟩

#check PaperGuardCensus.BarycentricTarget.activeMassBaseline
#check PaperGuardCensus.BarycentricTarget.activeMassBaseline_totalMass
#check PaperGuardCensus.BarycentricTarget.activeMassBaseline_normalizedCellMass
#check PaperGuardCensus.BarycentricTarget.activeMassBaseline_baseWeight
#check PaperGuardCensus.BarycentricTarget.activeMassBaseline_baseWeight_sum
#check PaperGuardCensus.BarycentricTarget.activeMassBaseline_ne_baseline_of_ne_one
#check PaperBridgeFit.BridgeData.q_eq_of_baseline_eq_activeMassBaseline
#check PaperBridgeFit.BridgeData.paperMoment_physicalScore_zero_eq_activeMass_mul_mu
#check PaperBridgeFit.BridgeData.paperMoment_physicalScore_zero_eq_reserveActiveMass_mul_mu

end

end Erdos390.Full
