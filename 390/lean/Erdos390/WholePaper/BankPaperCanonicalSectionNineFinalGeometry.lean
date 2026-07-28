import Erdos390.WholePaper.BankPaperAnchorExactificationGuards
import Erdos390.WholePaper.BankPaperCanonicalActualP87RatioCellTrafficConnector
import Erdos390.WholePaper.BankPaperCanonicalDistributedCandidateSet
import Erdos390.WholePaper.BankPaperCanonicalGuardLocalRowLedger
import Erdos390.WholePaper.BankPaperCanonicalPostHfitSlackConnector
import Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometry
import Erdos390.WholePaper.BankPaperPrechargeExactificationBridge

/-!
# Literal Section 9 final geometry

This file joins the last three finite interfaces before the existing
post-tangent continuation:

* the actual Proposition 8.7 endpoint and its guarded slack package;
* the canonical occupied ratio-cell geometry and actual-`q` traffic ledger;
* the finite distributed clean-multiplier supplier on guarded candidates.

The conclusion deliberately stops at a post-tangent output, its exact
distributed update, and the interval/collision geometry required downstream.
It does not repeat the exactification or upper-endpoint terminal.

One collision input remains explicit.  The existing realization API does not
prove that the fixed exceptional factors avoid the full actual component
census.  `BankPaperCanonicalSectionNineFixedComponentCollisionFree` names
exactly that missing finite statement.  It is used only to deduce that the
fixed factors avoid every Boolean exactification state.  Candidate--bank
disjointness, in contrast, follows from the literal five-family numerical
guard and is proved here.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Exactification states belong to the literal numerical guard -/

/-- State one of an actual path component is the orientation-aware alternate
precharge value of the corresponding global request. -/
@[simp] theorem pathStateOneValue_eq_prechargeAlternateStateValue
    {n M : Nat} (R : BankPaperRealization n M)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (component : BankPaperPathComponent slot) :
    R.pathStateOneValue slot component =
      R.prechargeAlternateStateValue
        (bankPaperPathComponentRequest slot component) := by
  cases component <;> rfl

/-- Every Boolean exactification state is already one of the two precharge
state families deleted by the literal guarded candidate set. -/
theorem exactificationState_subset_roughCanonicalGuardSet
    {c : Real} {depth n h : Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (slot : SignedBankSlot (bankRoundingBetaOnSupport n))
    (selected : Bool) :
    R.exactificationState slot selected ⊆
      R.roughCanonicalGuardSet certificate deltaStar := by
  intro occurrence hoccurrence
  cases selected with
  | false =>
      rw [R.exactificationState_false, pathStateZero, indexedPathState,
        Finset.mem_image] at hoccurrence
      obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
      have hbase :
          R.pathStateZeroValue (bankPaperOppositeSlot slot) component ∈
            R.prechargeBaseState := by
        rw [R.pathStateZeroValue_eq_prechargeBaseStateValue]
        exact R.prechargeBaseStateValue_mem_prechargeBaseState
          (bankPaperPathComponentRequest
            (bankPaperOppositeSlot slot) component)
      simp [roughCanonicalGuardSet, tangentPaperNumericalGuardSet]
  | true =>
      rw [R.exactificationState_true, pathStateOne, indexedPathState,
        Finset.mem_image] at hoccurrence
      obtain ⟨component, _hcomponent, rfl⟩ := hoccurrence
      have halternate :
          R.pathStateOneValue (bankPaperOppositeSlot slot) component ∈
            R.prechargeAlternateState := by
        rw [R.pathStateOneValue_eq_prechargeAlternateStateValue]
        exact R.prechargeAlternateStateValue_mem_prechargeAlternateState
          (bankPaperPathComponentRequest
            (bankPaperOppositeSlot slot) component)
      simp [roughCanonicalGuardSet, tangentPaperNumericalGuardSet]

/-! ## The exact final finite geometry -/

/-- The one collision statement not supplied by the guarded-candidate
construction: fixed exceptional factors avoid every actual bank-component
occurrence.  Keeping the global census here permits direct reuse of
`disjoint_exactificationState_of_disjoint_allComponentOccurrences`. -/
def BankPaperCanonicalSectionNineFixedComponentCollisionFree
    {c : Real} {n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (deltaStar : Real) : Prop :=
  Disjoint (R.paperFixedExceptionalFactors deltaStar)
    R.allComponentOccurrences

/-- The seven geometric facts outside
`BankPaperCanonicalPostTangentOutput` for the literal guarded candidates and
fixed exceptional factors.  Tail-charge divisibility is intentionally not a
geometry field and remains an input of the finite assembly theorem below. -/
def BankPaperCanonicalSectionNineFinalGeometry
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat) : Prop :=
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let fixed := R.paperFixedExceptionalFactors deltaStar
  candidates ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
    fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
    Disjoint fixed candidates ∧
    (∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected)) ∧
    (∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected)) ∧
    Disjoint certificate.anchors fixed ∧
    Disjoint certificate.anchors candidates

/-- All final geometry except the explicitly named fixed-component collision
is forced by the literal intervals and the five-family numerical guard. -/
theorem bankPaperCanonicalSectionNineFinalGeometry_of_fixedComponentCollisionFree
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hKh : K * upperTailLength c n ≤ n)
    (hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar) :
    R.BankPaperCanonicalSectionNineFinalGeometry
      certificate deltaStar K := by
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let guard := R.roughCanonicalGuardSet certificate deltaStar
  have hcandidateInterval :
      candidates ⊆
        factorInterval n (upperEndpoint n (upperTailLength c n)) := by
    intro a ha
    have hraw :
        a ∈ roughRawCandidateSet n (upperTailLength c n) K :=
      R.roughCanonicalGuardedCandidateSet_subset_rawCandidateSet
        certificate deltaStar K ha
    rw [roughRawCandidateSet_eq_Ioc hKh] at hraw
    simp only [factorInterval, Finset.mem_Ioc] at hraw ⊢
    unfold upperEndpoint
    omega
  have hfixedInterval :
      fixed ⊆
        factorInterval n (upperEndpoint n (upperTailLength c n)) := by
    intro a ha
    have htail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar ha
    simp only [factorInterval, Finset.mem_Ioc] at htail ⊢
    omega
  have hcandidateGuard : Disjoint candidates guard := by
    exact R.roughCanonicalGuardedCandidateSet_disjoint_guardSet
      certificate deltaStar K
  have hfixedGuard : fixed ⊆ guard := by
    intro a ha
    simp [guard, fixed, roughCanonicalGuardSet,
      tangentPaperNumericalGuardSet, ha]
  have hanchorsGuard : certificate.anchors ⊆ guard := by
    intro a ha
    simp [guard, roughCanonicalGuardSet,
      tangentPaperNumericalGuardSet, ha]
  have hfixedCandidate : Disjoint fixed candidates := by
    exact (hcandidateGuard.mono Finset.Subset.rfl hfixedGuard).symm
  have hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected) := by
    intro slot selected
    exact R.disjoint_exactificationState_of_disjoint_allComponentOccurrences
      fixed hfixedComponents slot selected
  have hcandidateBank : ∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected) := by
    intro slot selected
    exact hcandidateGuard.mono Finset.Subset.rfl
      (R.exactificationState_subset_roughCanonicalGuardSet
        certificate deltaStar slot selected)
  have hanchorsFixed : Disjoint certificate.anchors fixed := by
    rw [Finset.disjoint_left]
    intro a haAnchor haFixed
    have haAnchorInterval := certificate.anchors_subset haAnchor
    have haFixedInterval :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
    simp only [Finset.mem_Ioc] at haAnchorInterval haFixedInterval
    omega
  have hanchorsCandidate : Disjoint certificate.anchors candidates := by
    exact (hcandidateGuard.mono Finset.Subset.rfl hanchorsGuard).symm
  unfold BankPaperCanonicalSectionNineFinalGeometry
  exact ⟨hcandidateInterval, hfixedInterval, hfixedCandidate, hfixedBank,
    hcandidateBank, hanchorsFixed, hanchorsCandidate⟩

/-! ## Reusable finite flow and output package -/

/-- The literal canonical ratio-cell earthmover used by the final connector.
Naming it once keeps the clean-list premise and the final payload
definitionally synchronized. -/
def bankPaperCanonicalSectionNineRatioCellFlow
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {c : Real} {depth n W : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (K : Nat)
    (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W) (rho : Real)
    (selector : Nat → Real) :
    BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real :=
  tangentRatioCellEarthmoverFlow
    (bankPaperCanonicalLastRatioCell M (n := n) (W := W) rho)
    (bankPaperCanonicalTangentResidual (W := W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      selector)
    (bankPaperCanonicalExponentBandOf M hdelta hn hW S)
    (bankPaperCanonicalRatioCellIndex M hdelta hn hW S rho)

/-- Strong finite output of the connector: a clean multiplier family,
endpoint collision-freedom, exact flow and factorization boundaries, the
literal updated selector, tail-charge divisibility, and all final geometry. -/
def BankPaperCanonicalSectionNineFinalPayload
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (selector : Nat → Real)
    (flow : BankPaperCanonicalTangentPrime n W →
      BankPaperCanonicalTangentPrime n W → Real)
    (L sigma : Real) : Prop :=
  ∃ multiplier :
      BankPaperCanonicalDistributedTangentSplitRequest flow L sigma → Nat,
    (∀ request,
      multiplier request ∈
        tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2)
          n K (upperTailLength c n) (roughHeadModulus W)
          (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet certificate
            (R.paperFixedExceptionalFactors deltaStar)) request) ∧
    TangentEndpointsDistinct
        (tangentSplitRequests
          (tangentPositiveFlowEdges flow) L sigma
          (fun edge : BankPaperCanonicalTangentPrime n W ×
              BankPaperCanonicalTangentPrime n W =>
            flow edge.1 edge.2))
        bankPaperCanonicalDistributedTangentRequestSource
        bankPaperCanonicalDistributedTangentRequestTarget multiplier ∧
    (∀ p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          selector p) ∧
    (∀ q : Nat,
      (∑ request : BankPaperCanonicalDistributedTangentSplitRequest
            flow L sigma,
          tangentSplitRequestWeight request *
            (((bankPaperCanonicalDistributedTangentRequestSource
                  request).factorization q : Real) -
              ((bankPaperCanonicalDistributedTangentRequestTarget
                  request).factorization q : Real))) =
        bankPaperCanonicalSelectorValuationDeficit R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          selector q) ∧
    ∃ output : BankPaperCanonicalPostTangentOutput R certificate
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (R.paperFixedExceptionalFactors deltaStar),
      (output.selector =
          bankPaperCanonicalDistributedTangentUpdatedSelector
            flow L sigma multiplier selector) ∧
        (R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget) ∧
        R.BankPaperCanonicalSectionNineFinalGeometry
          certificate deltaStar K

/-! ## Actual Post-Hfit/P87 finite composition -/

/-- Feed the literal Post-Hfit endpoint, actual-`q` P87 traffic bounds,
occupied canonical ratio cells, and clean-list estimates into the finite
distributed supplier.  The conclusion also retains the fixed-ratio locality
part of the canonical cell geometry rather than discarding it after the
occupancy projections are used.

The scalar main/error/ceiling budgets and the actual-scale comparison remain
visible finite hypotheses.  The raw traffic-error coefficient is used
literally; replacing it by the eventual upper coefficient is a separate
monotonicity step.  The only geometric collision premise is the named
fixed-component statement above.

The Section 9 finite geometry only uses the rounded tangent input and
the guarded endpoint slack from the Post-Hfit package.  This source-agnostic
form exposes exactly those two inputs, so any verified selector source can
feed the existing distributed construction. -/
theorem bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta sigma : Real)
    (_radius : NNReal) (Cpost : Real)
    (endpoint : Nat → Real)
    (hdelta : 0 < delta) (hWtwo : 2 ≤ B.sampleData.W)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition : B.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S)
    (r0 rho tangentConstant N density : Real)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 ≤ tangentConstant) (hN : 0 < N)
    (hscaleDom : Cpost * B.q / B.L ≤
      tangentConstant * N / Real.log (y B.sampleData.n))
    (hMertens : fullReciprocalSumUniformCutoff ≤ B.sampleData.W)
    (hPNT : TangentFixedRatioPrimeCountLower B.sampleData.W rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied
      B.sampleData.W rho)
    (hTwo : ∀ k : Fin M.cellCount,
      2 ≤ scalePoint B.sampleData.n (M.lower k))
    (Hmoment : RegularMeshPrimeCutoffs.Mesh.MomentReady M
      (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta B.n_gt_one (by omega) S))
    (HselectorPartition :
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        B.partition.band
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho)
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
          B.partition.band
          (bankPaperCanonicalRatioCellIndex
            M hdelta B.n_gt_one (by omega) S rho))
        endpoint)
    (Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W (K0 + 1)
        alpha beta B.L sigma endpoint)
    (hKh : (K0 + 1) * upperTailLength c B.sampleData.n ≤
      B.sampleData.n)
    (hdensity : 0 < density) (hsigma : 0 < sigma)
    (hscale : B.L * N = (B.sampleData.n : Real))
    (hchargeDvd :
      R.selectorTailCharge (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree deltaStar)
    (hmain : tangentDistributedPaperMainBudget
      (bankPaperCanonicalRatioCellTrafficConstant rho)
      (bankPaperCanonicalRatioCellIncidentConstant rho)
      tangentConstant (delta + M.ratio) sigma ≤ density ^ 2 / 48)
    (herror : tangentDistributedPaperErrorBudget
      (bankPaperCanonicalRatioCellTrafficErrorCoefficient M
        B.sampleData.n B.sampleData.W rho tangentConstant)
      (bankPaperCanonicalRatioCellIncidentErrorCoefficient
        B.sampleData.W B.sampleData.n rho tangentConstant)
      sigma ≤ density ^ 2 / 96)
    (hceiling : tangentDistributedPaperCeilingBudget
      B.sampleData.n (yNat B.sampleData.n)
      (tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W)) ≤ density ^ 2 / 96)
    (hlowerPos :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        0 < bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request)
    (hlower :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request ≤
          (tangentSplitCleanMultiplierLists
            (tangentPositiveFlowEdges flow)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            B.L sigma
            (fun edge : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W ×
                BankPaperCanonicalTangentPrime
                  B.sampleData.n B.sampleData.W =>
              flow edge.1 edge.2)
            B.sampleData.n (K0 + 1)
            (upperTailLength c B.sampleData.n)
            (roughHeadModulus B.sampleData.W)
            (tangentPaperExceptionalCutoff deltaStar B.sampleData.n)
            (yNat B.sampleData.n) R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet certificate
              (R.paperFixedExceptionalFactors deltaStar))
            request).card)
    (hlowerScale :
      let flow :=
        R.bankPaperCanonicalSectionNineRatioCellFlow
          M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
            (by omega) S rho endpoint
      ∀ request :
          BankPaperCanonicalDistributedTangentSplitRequest
            flow B.L sigma,
        ∀ side,
          density * B.sampleData.n ≤
            (bankPaperCanonicalDistributedTangentLowerCard
              (density := density) request : Real) *
              tangentEndpointLabel
                bankPaperCanonicalDistributedTangentRequestSource
                bankPaperCanonicalDistributedTangentRequestTarget
                side request) :
    R.BankPaperCanonicalSectionNineFinalPayload (K := K0 + 1)
      certificate deltaStar
      endpoint
      (R.bankPaperCanonicalSectionNineRatioCellFlow
        M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
        (by omega) S rho endpoint)
      B.L sigma ∧
    TangentRatioCellGeometry bankPaperCanonicalTangentPrimeLabel
      (bankPaperCanonicalExponentBandOf
        M hdelta B.n_gt_one (by omega) S)
      (bankPaperCanonicalRatioCellIndex
        M hdelta B.n_gt_one (by omega) S rho) r0 := by
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar (K0 + 1)
  let lastCell :=
    bankPaperCanonicalLastRatioCell M
      (n := B.sampleData.n) (W := B.sampleData.W) rho
  let bandOf :=
    bankPaperCanonicalExponentBandOf
      M hdelta B.n_gt_one (by omega) S
  let cellIndex :=
    bankPaperCanonicalRatioCellIndex
      M hdelta B.n_gt_one (by omega) S rho
  let pointwiseUpper :=
    bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost
  let prefixUpper :=
    tangentRatioCellTailPointwiseUpper pointwiseUpper bandOf cellIndex
  let residual :=
    bankPaperCanonicalTangentResidual (W := B.sampleData.W) R certificate
      fixed candidates endpoint
  let paperScale :=
    tangentConstant * N / Real.log (y B.sampleData.n)
  let weightedPort :=
    bankPaperCanonicalRatioCellUniformPortMajorant M
      B.sampleData.n B.sampleData.W rho paperScale
  let trafficError :=
    bankPaperCanonicalRatioCellTrafficErrorCoefficient M
      B.sampleData.n B.sampleData.W rho tangentConstant
  let incidentError :=
    bankPaperCanonicalRatioCellIncidentErrorCoefficient
      B.sampleData.W B.sampleData.n rho tangentConstant
  let flow :=
    tangentRatioCellEarthmoverFlow lastCell residual bandOf cellIndex
  have Hselector :
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
        fixed candidates bandOf cellIndex pointwiseUpper prefixUpper
        endpoint := by
    simpa only [bandOf, prefixUpper, bankPaperCanonicalExponentBandOf,
      hpartition] using HselectorPartition
  have hgeometry :=
    bankPaperCanonical_ratioCellGeometry_spec
      M hdelta B.n_gt_one (by omega) S hrho hratio hprime
  have htraffic :=
    bankPaperCanonical_actualP87RatioCellPaperTraffic_of_scale_le
      M B R certificate fixed candidates endpoint hdelta hWtwo S
      hpartition hrho htangent hN.le hscaleDom hMertens hPNT
      hTwo Hmoment HselectorPartition
  have hendpointInputs :=
    R.guardedEndpointSlackConstruction_candidateSetEndpointInputs
      certificate deltaStar
      alpha beta
      (flow := flow) endpoint hKh Hslack
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have htail :=
      R.paperFixedExceptionalFactors_subset_tail deltaStar ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  have hcleanPos : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
      0 < bankPaperCanonicalDistributedTangentLowerCard
        (density := density) request := by
    simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
      candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
      hlowerPos
  have hcleanCard : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
      bankPaperCanonicalDistributedTangentLowerCard
          (density := density) request ≤
        (tangentSplitCleanMultiplierLists
          (tangentPositiveFlowEdges flow)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          B.L sigma
          (fun edge : BankPaperCanonicalTangentPrime
              B.sampleData.n B.sampleData.W ×
              BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W =>
            flow edge.1 edge.2)
          B.sampleData.n (K0 + 1)
          (upperTailLength c B.sampleData.n)
          (roughHeadModulus B.sampleData.W)
          (tangentPaperExceptionalCutoff deltaStar B.sampleData.n)
          (yNat B.sampleData.n) R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet certificate fixed)
          request).card := by
    simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
      candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
      hlower
  have hcleanScale : ∀ request :
      BankPaperCanonicalDistributedTangentSplitRequest flow B.L sigma,
      ∀ side,
        density * B.sampleData.n ≤
          (bankPaperCanonicalDistributedTangentLowerCard
            (density := density) request : Real) *
            tangentEndpointLabel
              bankPaperCanonicalDistributedTangentRequestSource
              bankPaperCanonicalDistributedTangentRequestTarget
              side request := by
    simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
      candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
      hlowerScale
  have hsupplier :=
    R.exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates
      certificate fixed fixed candidates endpoint
      lastCell bandOf cellIndex pointwiseUpper prefixUpper Hselector
      density B.L sigma N
      (bankPaperCanonicalRatioCellTrafficConstant rho)
      (bankPaperCanonicalRatioCellIncidentConstant rho)
      tangentConstant (delta + M.ratio)
      trafficError incidentError paperScale weightedPort
      (Nat.zero_lt_of_lt B.n_gt_one) hdensity B.L_pos hsigma hN hscale
      hfixedPositive hchargeDvd hgeometry.1 hgeometry.2.1
      (by
        simpa only [residual, paperScale] using htraffic.1)
      (by
        simpa only [residual, bandOf, cellIndex, weightedPort] using
          htraffic.2.1)
      (by
        simpa only [residual, lastCell, bandOf, cellIndex, trafficError]
          using htraffic.2.2.1)
      (by
        simpa only [paperScale, weightedPort, incidentError] using
          htraffic.2.2.2.le)
      hmain herror hceiling hcleanPos hcleanCard hcleanScale
      hendpointInputs.1 hendpointInputs.2
  obtain ⟨multiplier, hmultiplier, hdistinct, hdivergence,
    hboundary, output, houtput⟩ := hsupplier
  have hfinalGeometry :=
    R.bankPaperCanonicalSectionNineFinalGeometry_of_fixedComponentCollisionFree
      certificate deltaStar hKh hfixedComponents
  constructor
  · refine ⟨multiplier, ?_, ?_, ?_, ?_, output, ?_, hchargeDvd,
      hfinalGeometry⟩
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hmultiplier
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hdistinct
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hdivergence
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        hboundary
    · simpa only [flow, residual, lastCell, bandOf, cellIndex, fixed,
        candidates, bankPaperCanonicalSectionNineRatioCellFlow] using
        houtput
  · exact hgeometry.2.2

end BankPaperRealization

end

end Erdos390.WholePaper
