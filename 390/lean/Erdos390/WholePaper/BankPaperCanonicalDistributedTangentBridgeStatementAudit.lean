import Erdos390.WholePaper.BankPaperCanonicalDistributedTangentBridge

/-! # Expanded statement audit for the canonical distributed boundary -/

open scoped BigOperators
open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

example {n W : Nat} :
    tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime n W) <= yNat n ^ 2 :=
  tangentDistributedSupportCount_canonical_le_yNat_sq

example :
    Tendsto
      (fun n : Nat => (yNat n : Real) ^ 3 / (n : Real))
      atTop (nhds 0) :=
  tangentDistributed_yNat_cubed_div_self_tendsto_zero

example (W : Nat) {density : Real} (hdensity : 0 < density) :
    ∀ᶠ n : Nat in atTop,
      tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)) <=
        density ^ 2 / 96 :=
  eventually_tangentDistributedPaperCeilingBudget_canonical_le W hdensity

#check tangentDistributedPaperCeilingBudget_canonical_le_yNat_cubic
#check tangentDistributedPaperCeilingBudget_canonical_tendsto_zero

example {n W : Nat} {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (residual : BankPaperCanonicalTangentPrime n W -> Real)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (ratioUpper : Real)
    (hgeometry : TangentRatioCellGeometry
      bankPaperCanonicalTangentPrimeLabel bandOf cellIndex ratioUpper)
    {edge : BankPaperCanonicalTangentPrime n W ×
        BankPaperCanonicalTangentPrime n W}
    (hedge : edge ∈ tangentPositiveFlowEdges
      (tangentRatioCellEarthmoverFlow
        lastCell residual bandOf cellIndex)) :
    (((max (bankPaperCanonicalTangentPrimeLabel edge.1)
          (bankPaperCanonicalTangentPrimeLabel edge.2) : Nat) : Real) /
      ((min (bankPaperCanonicalTangentPrimeLabel edge.1)
          (bankPaperCanonicalTangentPrimeLabel edge.2) : Nat) : Real)) <=
        ratioUpper :=
  bankPaperCanonical_ratioCellEarthmover_positiveEdge_locality
    lastCell residual bandOf cellIndex ratioUpper hgeometry hedge

example {n W : Nat}
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (L sigma : Real)
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) :
    bankPaperCanonicalDistributedTangentRequestSource request =
        bankPaperCanonicalTangentPrimeLabel request.1.1.1 ∧
      bankPaperCanonicalDistributedTangentRequestTarget request =
        bankPaperCanonicalTangentPrimeLabel request.1.1.2 := by
  constructor <;> rfl

#check bankPaperCanonicalDistributedTangentLowerCard
#check bankPaperCanonicalDistributedTangentUpdatedSelector

example
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (x : Nat -> Real)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates x)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates x p) ∧
      forall q : Nat,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges flow) L sigma
                (fun edge :
                    BankPaperCanonicalTangentPrime n W ×
                      BankPaperCanonicalTangentPrime n W =>
                  flow edge.1 edge.2),
            tangentSplitRequestWeight request *
              (((tangentSplitRequestSource
                    (tangentStarEdgeSource
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real) -
                ((tangentSplitRequestTarget
                    (tangentStarEdgeTarget
                      bankPaperCanonicalTangentPrimeLabel)
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates x q :=
  bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
    R certificate fixed candidates x flow hflow hdivergence
      hsupport L sigma

#check bankPaperCanonicalRoundedSelector_distributedBoundary
#check bankPaperCanonicalSelectorRowIntegral_and_distributedBoundary
#check bankPaperCanonicalRoundedSelector_ratioCellCutTraffic_le_prefixUpper
#check bankPaperCanonicalRoundedSelector_ratioCellCutTraffic_le_tailPointwiseUpper
#check bankPaperCanonicalRoundedSelector_weightedResidual_le_pointwiseUpper
#check bankPaperCanonicalRoundedSelector_weightedPortLoad_le_pointwisePortUpper
#check bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
#check bankPaperCanonicalRoundedSelector_ratioCellEarthmover_positiveIncident
#check bankPaperCanonicalRoundedSelector_ratioCellDistributedBoundary

end

end Erdos390.WholePaper
