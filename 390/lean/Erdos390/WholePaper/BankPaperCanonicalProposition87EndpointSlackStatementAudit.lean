import Erdos390.WholePaper.BankPaperCanonicalProposition87EndpointSlack

/-!
# Statement audit for guarded P87 endpoint slack

The inventory contains one definition and eleven theorems.  The expanded
examples expose the only remaining construction estimate and the exact
frozen-plus-active witnesses; the two long Section 9 adapters are checked at
their fully elaborated public types.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

#check BankPaperCanonicalGuardedSmoothProtectedWindow
#check frozenAmbientWeight_subtype_apply
#check frozenAmbientWeight_subtypeRemainder_eq_preSelector
#check bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeBounds
#check bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeRemainder
#check bankPaperProposition87AmbientActiveWeight_le_of_effectiveScoreBound
#check bankPaperProposition87AmbientActiveWeight_endpoint_le_of_path
#check eventually_bankPaperProposition87EndpointSlack_logReserve
#check bankPaperProposition87AmbientActiveWeight_eq_zero_on_nonsmoothPool
#check exists_bankPaperProposition87EndpointSelector_smoothSlackLayers

namespace BankPaperRealization

#check guardedEndpointSlackConstruction_of_proposition87EndpointSelector
#check proposition87EndpointSelector_candidateSetEndpointInputs

end BankPaperRealization

example
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (sigma Cfixed : Real) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
        B R certificate deltaStar fixedValue fixedWeight sigma Cfixed ↔
      ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        sigma / B.L <=
            BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∧
          BridgeData.frozenAmbientWeight fixedValue fixedWeight x <=
            Cfixed / B.L := by
  rfl

example
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (xi : B.ParamSpace) (Rbound Cactive : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= Rbound)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L) :
    forall x : Nat,
      B.ambientActiveWeight xi x <=
        Real.exp (2 * Rbound) * Cactive / B.L :=
  bankPaperProposition87AmbientActiveWeight_le_of_effectiveScoreBound
    B hsep xi Rbound Cactive hscore hCactive hactive

end

end Erdos390.WholePaper
