import Erdos390.WholePaper.BankPaperProposition87EndpointSelector

/-!
# Statement audit for the Proposition 8.7 endpoint selector

The expanded checks below make the two essential interface choices visible:
the selector is the ambient frozen-plus-active sum on `Nat`, and its marked
residual uses the literal finite push-forward support.  The final census
lists every public declaration in the source module.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

example
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 0 < q)
    (M : RegularRelativeMesh.Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : RegularMeshPrimeCutoffs.ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    let B := bankPaperCanonicalActiveMassBridgeData
      D T q hq M hdelta hn hW S referenceHead hw
    B.sampleData = D ∧ B.baseline = T.activeMassBaseline q hq ∧
      B.q = q := by
  simp

example
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
    (path : Real → B.ParamSpace) (t : Real) (x : Nat) :
    bankPaperProposition87SelectorAt
        B fixedValue fixedWeight path t x =
      BridgeData.frozenAmbientWeight fixedValue fixedWeight x +
        B.ambientActiveWeight (path t) x := by
  rfl

example
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
    (markedTarget : Nat → Real)
    (path : Real → B.ParamSpace) (p : Nat) :
    bankPaperProposition87FullMarkedResidual
        B fixedValue fixedWeight markedTarget path p =
      bankPaperProposition87FullMarkedTarget
          fixedValue fixedWeight markedTarget p -
        ∑ x ∈ bankPaperProposition87SelectorSupport B fixedValue,
          bankPaperProposition87EndpointSelector
              B fixedValue fixedWeight path x * valuation p x := by
  rfl

#check bankPaperCanonicalActiveMassBridgeData
#check bankPaperCanonicalActiveMassBridgeData_sampleData
#check bankPaperCanonicalActiveMassBridgeData_baseline
#check bankPaperCanonicalActiveMassBridgeData_q
#check bankPaperProposition87SelectorSupport
#check bankPaperProposition87SelectorAt
#check bankPaperProposition87EndpointSelector
#check fixedValue_mem_bankPaperProposition87SelectorSupport
#check sampleValue_mem_bankPaperProposition87SelectorSupport
#check bankPaperProposition87SelectorAt_eq_zero_of_not_mem_support
#check sum_bankPaperProposition87SelectorAt_mul
#check sum_bankPaperProposition87SelectorAt
#check bankPaperProposition87FullMarkedTarget
#check bankPaperProposition87FullMarkedResidual
#check bankPaperProposition87FullMarkedResidual_eq_activeResidual
#check bankPaperProposition87FullMarkedResidual_band_sum_eq_zero
#check abs_bankPaperProposition87FullMarkedResidual_le
#check bankPaperProposition87EndpointSelector_mem_Icc_of_path
#check sum_bankPaperProposition87EndpointSelector_eq_quota_of_path
#check bankPaperProposition87Selector_lowPrimeMoment_preserved_of_path
#check exists_bankPaperProposition87EndpointSelector
#check Erdos390.Full.PaperBridgeFit.BridgeData.hasPaperProposition87Conclusion_of_normalizedLawCompanion
#check Erdos390.Full.PaperBridgeFit.BridgeData.canonical_activeMass_proposition87_of_normalizedLawCompanion
#check Erdos390.Full.PaperBridgeFit.BridgeData.canonical_proposition87_activeMassLiteralBandBalance
#check Erdos390.Full.PaperBridgeFit.CanonicalProposition87VaryingActiveMassLiteralBalanceStatement
#check Erdos390.Full.PaperBridgeFit.BridgeData.canonical_proposition87_varyingActiveMassLiteralBandBalance

end

end Erdos390.WholePaper
