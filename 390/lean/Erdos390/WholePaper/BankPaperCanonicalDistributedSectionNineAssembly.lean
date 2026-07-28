import Erdos390.WholePaper.BankPaperCanonicalDistributedPostChoice
import Erdos390.WholePaper.BankAnchorCollisionFree

/-!
# Finite canonical Section 9 assembly with a distributed earthmover

This is the finite, star-free Section 9 assembly.  The flow is not an
existential input: it is the explicit ratio-cell earthmover applied to the
literal canonical selector residual.  The distributed residual census
chooses collision-free clean multipliers, and
`exists_canonicalDistributedPostTangentOutput_of_multiplier` applies the
resulting update.

The hypotheses left visible here are the genuine upstream inputs:

* the rounded selector state and the occupied ratio-cell geometry;
* the total-traffic and weighted incident analytic estimates, followed by
  their paper main/error/ceiling budget inequalities;
* the clean-list lower bound and its endpoint scale;
* selector slack on members of the clean lists; and
* the precharged selector-tail divisibility needed by the final valuation
  certificate.

There is no pivot, star-locality hypothesis, requestwise collision-smallness
assumption, or supplied final collision conclusion.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- Assemble the complete finite distributed tangent stage from the paper
traffic budgets and the clean-list lower theorem.

The conclusion exposes the selected clean multipliers and their endpoint
distinctness, the exact divergence and factorization boundary of the
explicit earthmover, and the concrete post-tangent selector update. -/
theorem exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets
    {c : Real} {depth n W K h X0 : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed : Finset Nat)
    (selector : Nat -> Real)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed (roughRawCandidateSet n h K)
        bandOf cellIndex pointwiseUpper prefixUpper selector)
    (density L sigma N : Real)
    (trafficConstant incidentConstant tangentConstant width : Real)
    (trafficError incidentError weightedResidual weightedPort : Real)
    (hKh : K * h <= n)
    (hn : 0 < n)
    (hdensity : 0 < density) (hL : 0 < L) (hsigma : 0 < sigma)
    (hN : 0 < N) (hscale : L * N = (n : Real))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (hresidual : forall p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          |bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector p| <=
        weightedResidual)
    (hport : forall p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
          tangentRatioCellUniformPortLoad
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex p <= weightedPort)
    (htotal : tangentDistributedTotalTrafficLedger
        (V := BankPaperCanonicalTangentPrime n W)
        (bankPaperCanonicalTangentResidual (W := W)
          R certificate fixed (roughRawCandidateSet n h K) selector)
        (tangentRatioCellCanonicalCutTraffic lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector)
          bandOf cellIndex) <=
      trafficConstant * tangentConstant * N * width + trafficError * N)
    (hweightedIncident : weightedResidual + 2 * weightedPort <=
      incidentConstant * tangentConstant * N * width + incidentError * N)
    (hmain : tangentDistributedPaperMainBudget
        trafficConstant incidentConstant tangentConstant width sigma <=
      density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
        trafficError incidentError sigma <= density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget n (yNat n)
        (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W)) <= density ^ 2 / 96)
    (hlowerPos : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      0 < bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request)
    (hlower : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request <=
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex))
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex edge.1 edge.2)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      forall side,
        density * n <=
          (bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request : Real) *
            tangentEndpointLabel
              bankPaperCanonicalDistributedTangentRequestSource
              bankPaperCanonicalDistributedTangentRequestTarget
              side request)
    (hslack : forall request :
        BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed (roughRawCandidateSet n h K) selector)
            bandOf cellIndex) L sigma,
      forall multiplier,
        multiplier ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed (roughRawCandidateSet n h K)
                      selector)
                  bandOf cellIndex))
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              L sigma
              (fun edge : BankPaperCanonicalTangentPrime n W ×
                  BankPaperCanonicalTangentPrime n W =>
                tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed (roughRawCandidateSet n h K)
                      selector)
                  bandOf cellIndex edge.1 edge.2)
              n K h (roughHeadModulus W) X0 (yNat n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional) request ->
          (sigma / L <= selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestSource request *
                  multiplier) <= 1 - sigma / L) ∧
            (sigma / L <= selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) ∧
              selector
                (bankPaperCanonicalDistributedTangentRequestTarget request *
                  multiplier) <= 1 - sigma / L)) :
    ∃ multiplier : BankPaperCanonicalDistributedTangentSplitRequest
        (tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector)
          bandOf cellIndex) L sigma -> Nat,
      (forall request,
        multiplier request ∈
          tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed (roughRawCandidateSet n h K) selector)
                bandOf cellIndex))
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed (roughRawCandidateSet n h K) selector)
                bandOf cellIndex edge.1 edge.2)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests
          (tangentPositiveFlowEdges
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex)) L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex edge.1 edge.2))
        bankPaperCanonicalDistributedTangentRequestSource
        bankPaperCanonicalDistributedTangentRequestTarget multiplier ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        tangentFlowDivergence
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex) p =
          bankPaperCanonicalTangentResidual
            R certificate fixed (roughRawCandidateSet n h K) selector p) ∧
      (forall q : Nat,
        (∑ request : BankPaperCanonicalDistributedTangentSplitRequest
              (tangentRatioCellEarthmoverFlow lastCell
                (bankPaperCanonicalTangentResidual
                  R certificate fixed (roughRawCandidateSet n h K) selector)
                bandOf cellIndex) L sigma,
            tangentSplitRequestWeight request *
              (((bankPaperCanonicalDistributedTangentRequestSource
                    request).factorization q : Real) -
                ((bankPaperCanonicalDistributedTangentRequestTarget
                    request).factorization q : Real))) =
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed (roughRawCandidateSet n h K) selector q) ∧
      ∃ output : BankPaperCanonicalPostTangentOutput R certificate
          (roughRawCandidateSet n h K) fixed,
        output.selector =
          bankPaperCanonicalDistributedTangentUpdatedSelector
            (tangentRatioCellEarthmoverFlow lastCell
              (bankPaperCanonicalTangentResidual
                R certificate fixed (roughRawCandidateSet n h K) selector)
              bandOf cellIndex) L sigma multiplier selector := by
  let candidates := roughRawCandidateSet n h K
  let residual := bankPaperCanonicalTangentResidual (W := W)
    R certificate fixed candidates selector
  let portLoad := tangentRatioCellUniformPortLoad residual bandOf cellIndex
  let cutTraffic := tangentRatioCellCanonicalCutTraffic
    lastCell residual bandOf cellIndex
  let flow := tangentRatioCellEarthmoverFlow
    lastCell residual bandOf cellIndex
  let lowerCard : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma -> Nat :=
    fun request => bankPaperCanonicalDistributedTangentLowerCard
      (density := density) request
  have S' : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector := by
    simpa only [candidates] using S
  have hspec := bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
    R certificate fixed candidates lastCell bandOf cellIndex
      pointwiseUpper prefixUpper selector S' hindex hoccupied
  have hboundary :=
    bankPaperCanonicalRoundedSelector_ratioCellDistributedBoundary
      R certificate fixed candidates lastCell bandOf cellIndex
        pointwiseUpper prefixUpper selector S' hindex hoccupied L sigma
  have hpositiveEndpoints : forall {source target},
      0 < flow source target -> source ≠ target := by
    intro source target hpositive
    exact tangentRatioCellEarthmoverFlow_positive_endpoints_ne
      lastCell residual bandOf cellIndex hpositive
  have hpositiveIncident : forall p,
      tangentIncidentFlowMass
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
          (bankPaperCanonicalTangentPrimeLabel p) <=
        |residual p| + 2 * portLoad p := by
    intro p
    exact bankPaperCanonicalRoundedSelector_ratioCellEarthmover_positiveIncident
      R certificate fixed candidates lastCell bandOf cellIndex
        pointwiseUpper prefixUpper selector S' hindex hoccupied p
  have hyLeNat : yNat n <= n := by
    have hthree : 3 * yNat n <= n := R.three_mul_yNat_le_n
    omega
  have hyLe : (yNat n : Real) <= (n : Real) := by
    exact_mod_cast hyLeNat
  have hySqNat : yNat n * yNat n <= n :=
    bankAnchor_yNat_mul_self_le_self hn
  have hySqMul : (yNat n : Real) * (yNat n : Real) <= (n : Real) := by
    exact_mod_cast hySqNat
  have hySq : (yNat n : Real) ^ 2 <= (n : Real) := by
    simpa only [pow_two] using hySqMul
  have hresidual' : forall p,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * |residual p| <=
        weightedResidual := by
    simpa only [residual, candidates] using hresidual
  have hport' : forall p,
      (bankPaperCanonicalTangentPrimeLabel p : Real) * portLoad p <=
        weightedPort := by
    simpa only [portLoad, residual, candidates] using hport
  have htotal' : tangentDistributedTotalTrafficLedger residual cutTraffic <=
      trafficConstant * tangentConstant * N * width + trafficError * N := by
    simpa only [cutTraffic, residual, candidates] using htotal
  have hlowerPos' : forall request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      0 < lowerCard request := by
    simpa only [lowerCard, flow, residual, candidates] using hlowerPos
  have hlower' : forall request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      lowerCard request <=
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card := by
    simpa only [lowerCard, flow, residual, candidates] using hlower
  have hlowerScale' : forall request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      forall side,
        density * n <= (lowerCard request : Real) *
          tangentEndpointLabel
            bankPaperCanonicalDistributedTangentRequestSource
            bankPaperCanonicalDistributedTangentRequestTarget side request := by
    simpa only [lowerCard, flow, residual, candidates] using hlowerScale
  have hcensus :=
    R.tangentPaperDistributedSplitEndpointsDistinct_of_residualCensus
      certificate fixedExceptional K h (roughHeadModulus W) X0
      bankPaperCanonicalTangentPrimeLabel residual portLoad cutTraffic flow
      hspec.1 hspec.2.1 hpositiveEndpoints hspec.2.2.2.1
      hpositiveIncident bankPaperCanonicalTangentPrimeLabel_injective
      bankPaperCanonicalTangentPrimeLabel_prime
      weightedResidual weightedPort hresidual' hport' (yNat n) density
      hn hdensity bankPaperCanonicalTangentPrimeLabel_le_yNat hyLe hySq
      hL hsigma hN hscale
      trafficConstant incidentConstant tangentConstant width
      trafficError incidentError htotal' hweightedIncident
      hmain herror hceiling lowerCard hlowerPos' hlower' hlowerScale'
  obtain ⟨multiplier, hmultiplierMem, hdistinct⟩ := hcensus.2.2
  have hsourceSlack : forall request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      sigma / L <= selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            multiplier request) <= 1 - sigma / L := by
    intro request
    have h := (hslack request (multiplier request) (by
      simpa only [flow, residual, candidates] using
        hmultiplierMem request)).1
    simpa only [flow, residual, candidates] using h
  have htargetSlack : forall request :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma,
      sigma / L <= selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            multiplier request) <= 1 - sigma / L := by
    intro request
    have h := (hslack request (multiplier request) (by
      simpa only [flow, residual, candidates] using
        hmultiplierMem request)).2
    simpa only [flow, residual, candidates] using h
  have hpost :=
    R.exists_canonicalDistributedPostTangentOutput_of_multiplier
      certificate fixedExceptional fixed selector bandOf cellIndex
      pointwiseUpper prefixUpper S' flow hspec.1 hspec.2.1 L sigma hKh
      hL hsigma hfixedPositive hchargeDvd multiplier hmultiplierMem
      hdistinct hsourceSlack htargetSlack
  obtain ⟨output, houtput⟩ := hpost
  refine ⟨multiplier, ?_, ?_, ?_, ?_, output, ?_⟩
  · simpa only [flow, residual, candidates] using hmultiplierMem
  · simpa only [flow, residual, candidates,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hdistinct
  · simpa only [candidates] using hboundary.1
  · simpa only [candidates,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget] using hboundary.2
  · simpa only [flow, residual, candidates] using houtput

end BankPaperRealization

end

end Erdos390.WholePaper
