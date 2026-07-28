import Erdos390.WholePaper.TangentPaperCleanListAbsorption
import Erdos390.WholePaper.BankPaperCanonicalDistributedTangentBridge
import Erdos390.WholePaper.BankPaperCanonicalPrefixQuadrature

/-!
# Distributed canonical clean-list adapter

The absorbed clean-list theorem is uniform in every permitted unordered
prime pair `(u,v)`, whereas the distributed tangent assembly indexes its
lists by split requests of the explicit ratio-cell earthmover.  This module
performs only that finite reindexing.

For a request, its two endpoint labels are prime-band members.  Their
maximum and minimum therefore satisfy all elementary prime and cutoff
conditions of the absorbed theorem.  `TangentRatioCellGeometry` supplies
the sole nontrivial conversion: positive earthmover support has endpoint
ratio at most `r0`.  No list estimate, cell occupancy statement, traffic
bound, or selector slack is assumed or reproved here.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- The paper clean-list lower bound, positivity, and endpoint scale for
every split request of the explicit distributed ratio-cell earthmover.

All analytic losses are already absorbed by
`eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed`.
The additional input here is exactly the fixed-ratio geometry needed to
show that the two labels underlying each positive-flow request form a
permitted pair. -/
theorem eventually_canonicalDistributedSectionNineCleanListLower_absorbed
    (W K : Nat) {c r0 deltaStar : Real}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : Nat in atTop,
      ∀ (depth : Nat) (left right : Nat → Nat)
        (changed : Finset Nat),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional : Finset Nat),
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band],
      ∀ (lastCell : Band → Nat)
        (residual : BankPaperCanonicalTangentPrime n W → Real)
        (bandOf : BankPaperCanonicalTangentPrime n W → Band)
        (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
        (L sigma : Real),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
        bandOf cellIndex r0 →
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        0 < bankPaperCanonicalDistributedTangentLowerCard
          (density := tangentPaperCleanListDensity W r0) request) ∧
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        bankPaperCanonicalDistributedTangentLowerCard
            (density := tangentPaperCleanListDensity W r0) request ≤
          (tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges
              (tangentRatioCellEarthmoverFlow lastCell residual
                bandOf cellIndex))
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (fun edge : BankPaperCanonicalTangentPrime n W ×
                BankPaperCanonicalTangentPrime n W =>
              tangentRatioCellEarthmoverFlow lastCell residual
                bandOf cellIndex edge.1 edge.2)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card) ∧
      ∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          (tangentRatioCellEarthmoverFlow lastCell residual
            bandOf cellIndex) L sigma,
        ∀ side,
          tangentPaperCleanListDensity W r0 * n ≤
            (bankPaperCanonicalDistributedTangentLowerCard
              (density := tangentPaperCleanListDensity W r0)
              request : Real) *
              tangentEndpointLabel
                bankPaperCanonicalDistributedTangentRequestSource
                bankPaperCanonicalDistributedTangentRequestTarget
                side request := by
  have hclean :=
    eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed
      W K hc hr0one hr0three hdelta hdeltaUpper hmainSmall
  filter_upwards [hclean] with n hcleanN
  intro depth left right changed R certificate fixedExceptional
    Band _instBandFintype _instBandDecidable
    lastCell residual bandOf cellIndex L sigma
    hfixedTail hTwoW hPrefix hyCutoff hgeometry
  let flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real :=
    tangentRatioCellEarthmoverFlow lastCell residual bandOf cellIndex
  let edges := tangentPositiveFlowEdges flow
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let edgeFlow :
      BankPaperCanonicalTangentPrime n W ×
          BankPaperCanonicalTangentPrime n W → Real :=
    fun edge => flow edge.1 edge.2
  let requestSource :=
    tangentSplitRequestSource
      (edges := edges) (L := L) (sigma := sigma) (flow := edgeFlow) source
  let requestTarget :=
    tangentSplitRequestTarget
      (edges := edges) (L := L) (sigma := sigma) (flow := edgeFlow) target
  have hrequestPrime :
      ∀ request : TangentSplitRequest edges L sigma edgeFlow,
        (requestSource request).Prime ∧
          (requestTarget request).Prime := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hrequestBand :
      ∀ request : TangentSplitRequest edges L sigma edgeFlow,
        (W < requestSource request ∧
            requestSource request ≤ yNat n) ∧
          (W < requestTarget request ∧
            requestTarget request ≤ yNat n) := by
    intro request
    constructor
    · constructor
      · simpa only [requestSource, source, tangentSplitRequestSource,
          tangentSplitRequestEdge, tangentStarEdgeSource] using
          cutoff_lt_of_mem_primeBand request.1.1.1.2
      · simpa only [requestSource, source, tangentSplitRequestSource,
          tangentSplitRequestEdge, tangentStarEdgeSource] using
          le_yNat_of_mem_primeBand request.1.1.1.2
    · constructor
      · simpa only [requestTarget, target, tangentSplitRequestTarget,
          tangentSplitRequestEdge, tangentStarEdgeTarget] using
          cutoff_lt_of_mem_primeBand request.1.1.2.2
      · simpa only [requestTarget, target, tangentSplitRequestTarget,
          tangentSplitRequestEdge, tangentStarEdgeTarget] using
          le_yNat_of_mem_primeBand request.1.1.2.2
  have hcleanData :
      ∀ request : TangentSplitRequest edges L sigma edgeFlow,
        0 < tangentEffectiveLowerCard
            (tangentPaperCleanListDensity W r0) n
            (min (requestSource request) (requestTarget request)) ∧
          tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n
              (min (requestSource request) (requestTarget request)) ≤
            (tangentCleanCommonMultiplierList n K
              (upperTailLength c n) (roughHeadModulus W)
              (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
              (max (requestSource request) (requestTarget request))
              (min (requestSource request) (requestTarget request))
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet
                certificate fixedExceptional)).card ∧
          tangentPaperCleanListDensity W r0 * n ≤
            (tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n
              (min (requestSource request)
                (requestTarget request)) : Real) *
              max (requestSource request) (requestTarget request) ∧
          tangentPaperCleanListDensity W r0 * n ≤
            (tangentEffectiveLowerCard
              (tangentPaperCleanListDensity W r0) n
              (min (requestSource request)
                (requestTarget request)) : Real) *
              min (requestSource request) (requestTarget request) := by
    intro request
    let u := max (requestSource request) (requestTarget request)
    let v := min (requestSource request) (requestTarget request)
    have huPrime : u.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [u, max_eq_right hst] using
          (hrequestPrime request).2
      · simpa only [u, max_eq_left hts] using
          (hrequestPrime request).1
    have hvPrime : v.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [v, min_eq_left hst] using
          (hrequestPrime request).1
      · simpa only [v, min_eq_right hts] using
          (hrequestPrime request).2
    have hWv : W < v :=
      lt_min (hrequestBand request).1.1 (hrequestBand request).2.1
    have hvu : v ≤ u := min_le_max
    have huy : u ≤ yNat n :=
      max_le (hrequestBand request).1.2 (hrequestBand request).2.2
    have hedge : request.1.1 ∈ tangentPositiveFlowEdges
        (tangentRatioCellEarthmoverFlow lastCell residual
          bandOf cellIndex) := by
      simpa only [edges, flow] using request.1.2
    have hratioEdge :=
      bankPaperCanonical_ratioCellEarthmover_positiveEdge_locality
        lastCell residual bandOf cellIndex r0 hgeometry hedge
    have hratio : (u : Real) / (v : Real) ≤ r0 := by
      simpa only [u, v, requestSource, requestTarget, source, target,
        tangentSplitRequestSource, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeSource,
        tangentStarEdgeTarget] using hratioEdge
    exact hcleanN c depth
      (upperEndpoint n (upperTailLength c n)) u v left right changed
      R certificate fixedExceptional hfixedTail hTwoW hPrefix hWv hvu huy
      hyCutoff huPrime hvPrime hratio
  constructor
  · intro request
    simpa only [bankPaperCanonicalDistributedTangentLowerCard,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget,
      requestSource, requestTarget, edges, source, target, edgeFlow, flow]
      using (hcleanData request).1
  constructor
  · intro request
    simpa only [bankPaperCanonicalDistributedTangentLowerCard,
      bankPaperCanonicalDistributedTangentRequestSource,
      bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitCleanMultiplierLists, tangentCleanMultiplierLists,
      requestSource, requestTarget, edges, source, target, edgeFlow, flow]
      using (hcleanData request).2.1
  · intro request side
    have hminScale := (hcleanData request).2.2.2
    cases side with
    | source =>
        have hminSource :
            ((min (requestSource request) (requestTarget request) : Nat) :
                Real) <= (requestSource request : Real) := by
          exact_mod_cast
            (min_le_left (requestSource request) (requestTarget request))
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            hminSource
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalDistributedTangentLowerCard,
          bankPaperCanonicalDistributedTangentRequestSource,
          bankPaperCanonicalDistributedTangentRequestTarget,
          tangentEndpointLabel, requestSource, requestTarget, edges,
          source, target, edgeFlow, flow] using hscale
    | target =>
        have hminTarget :
            ((min (requestSource request) (requestTarget request) : Nat) :
                Real) <= (requestTarget request : Real) := by
          exact_mod_cast
            (min_le_right (requestSource request) (requestTarget request))
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            hminTarget
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalDistributedTangentLowerCard,
          bankPaperCanonicalDistributedTangentRequestSource,
          bankPaperCanonicalDistributedTangentRequestTarget,
          tangentEndpointLabel, requestSource, requestTarget, edges,
          source, target, edgeFlow, flow] using hscale

end BankPaperRealization

/-! ## Harmonic pointwise specialization -/

/-- A rounded selector with the paper harmonic pointwise majorant satisfies
the weighted-residual premise of the distributed assembly with
`weightedResidual = scale`. -/
theorem bankPaperCanonicalRoundedSelector_weightedResidual_le_harmonicScale
    {c : Real} {depth n W : Nat} {left right : Nat → Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W → Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W → Nat)
    (prefixUpper : Band → Nat → Real)
    (scale : Real) (selector : Nat → Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        (bankPaperCanonicalHarmonicPointwiseUpper scale)
        prefixUpper selector)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| ≤ scale := by
  calc
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
          |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| ≤
        (bankPaperCanonicalTangentPrimeLabel p : Real) *
          bankPaperCanonicalHarmonicPointwiseUpper scale p :=
      bankPaperCanonicalRoundedSelector_weightedResidual_le_pointwiseUpper
        R certificate fixed candidates bandOf cellIndex
          (bankPaperCanonicalHarmonicPointwiseUpper scale)
          prefixUpper selector S p
    _ = scale :=
      bankPaperCanonicalTangentPrimeLabel_mul_harmonicPointwiseUpper
        scale p

end

end Erdos390.WholePaper
