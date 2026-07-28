import Erdos390.WholePaper.BankPaperCanonicalTangentResidualBridge
import Erdos390.WholePaper.TangentStarSplitRequestBridge
import Erdos390.WholePaper.TangentCanonicalCleanListLower
import Erdos390.WholePaper.TangentPairArithmetic
import Erdos390.WholePaper.TangentCollisionFreeFeasibility
import Erdos390.WholePaper.RoughSaiasUnconditionalDownstream
import Erdos390.WholePaper.BankPaperCanonicalUpperConstructionEventually

/-!
# Canonical Section 9 assembly reduction

This file assembles the already-proved finite pieces of the tangent stage.
Starting from an explicitly supplied pre-tangent selector, it uses the
literal prime-band residual, star transport, request splitting, canonical
clean-list lower bounds, pair arithmetic, the `1/8` census budget, and the
collision-free endpoint theorem.  The selected common multipliers are then
fed to the actual `tangentUpdate`; feasibility, complete-rough row sums, and
the selector-tail valuation are proved for that update.

The construction does not hide the remaining selector theorem.  Its finite
inputs still include selector feasibility and row integrality, prime-band
balance and support, uniform endpoint slack on every clean list, and the
displayed request-wise list-loss and traffic smallness comparisons.  The
final continuation wrapper also retains the genuinely geometric disjointness
conditions.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-! ## Canonical request notation -/

/-- Strictly positive star edges for the literal selector valuation
residual. -/
def bankPaperCanonicalTangentEdges
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) :
    Finset (BankPaperCanonicalTangentPrime n W ×
      BankPaperCanonicalTangentPrime n W) :=
  tangentStarPositiveEdges pivot
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates x)

/-- Edge weight on the preceding positive star support. -/
def bankPaperCanonicalTangentEdgeFlow
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W)
    (edge : BankPaperCanonicalTangentPrime n W ×
      BankPaperCanonicalTangentPrime n W) : ℝ :=
  tangentStarEdgeFlow pivot
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates x) edge

/-- Literal split-request type for the canonical residual star. -/
abbrev BankPaperCanonicalTangentSplitRequest
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) (L sigma : ℝ) :=
  TangentSplitRequest
    (bankPaperCanonicalTangentEdges
      R certificate fixed candidates x pivot) L sigma
    (bankPaperCanonicalTangentEdgeFlow
      R certificate fixed candidates x pivot)

/-- Natural source-prime label of a canonical split request. -/
def bankPaperCanonicalTangentRequestSource
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) (L sigma : ℝ) :
    BankPaperCanonicalTangentSplitRequest
      R certificate fixed candidates x pivot L sigma → ℕ :=
  tangentSplitRequestSource
    (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)

/-- Natural target-prime label of a canonical split request. -/
def bankPaperCanonicalTangentRequestTarget
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) (L sigma : ℝ) :
    BankPaperCanonicalTangentSplitRequest
      R certificate fixed candidates x pivot L sigma → ℕ :=
  tangentSplitRequestTarget
    (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)

/-- Effective lower card chosen at the smaller request endpoint. -/
def bankPaperCanonicalTangentLowerCard
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) (L sigma density : ℝ)
    (request : BankPaperCanonicalTangentSplitRequest
      R certificate fixed candidates x pivot L sigma) : ℕ :=
  tangentEffectiveLowerCard density n
    (min
      (bankPaperCanonicalTangentRequestSource
        R certificate fixed candidates x pivot L sigma request)
      (bankPaperCanonicalTangentRequestTarget
        R certificate fixed candidates x pivot L sigma request))

/-- The actual selector produced after applying every canonical split
request with its chosen common multiplier. -/
def bankPaperCanonicalTangentUpdatedSelector
    {c : ℝ} {depth n W : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W) (L sigma : ℝ)
    (multiplier : BankPaperCanonicalTangentSplitRequest
      R certificate fixed candidates x pivot L sigma → ℕ) : ℕ → ℝ :=
  tangentUpdate
    (tangentSplitRequests
      (bankPaperCanonicalTangentEdges
        R certificate fixed candidates x pivot) L sigma
      (bankPaperCanonicalTangentEdgeFlow
        R certificate fixed candidates x pivot))
    (bankPaperCanonicalTangentRequestSource
      R certificate fixed candidates x pivot L sigma)
    (bankPaperCanonicalTangentRequestTarget
      R certificate fixed candidates x pivot L sigma)
    multiplier tangentSplitRequestWeight x

/-! ## Deterministic endpoint facts for clean multipliers -/

/-- Every member of a split clean list is positive. -/
theorem tangentSplitCleanMultiplier_pos
    {E : Type*} {edges : Finset E} {source target : E → ℕ}
    {L sigma : ℝ} {flow : E → ℝ}
    {n K h Phead X0 y : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : ℕ}
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    0 < multiplier := by
  have hclean : multiplier ∈ tangentCleanCommonMultiplierList
      n K h Phead X0 y
        (max (tangentSplitRequestSource source request)
          (tangentSplitRequestTarget target request))
        (min (tangentSplitRequestSource source request)
          (tangentSplitRequestTarget target request))
        dedicatedRows numericalGuards := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists] using hmultiplier
  have hlower := (mem_tangentCleanCommonMultiplierList.mp hclean).1.1
  exact (Nat.zero_le _).trans_lt hlower

/-- Clean-list endpoints lie in the literal raw selector candidate set.
This is the exact candidate-closure fact needed by `tangentUpdate`. -/
theorem tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
    {E : Type*} {edges : Finset E} {source target : E → ℕ}
    {L sigma : ℝ} {flow : E → ℝ}
    {n K h Phead X0 y : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (request : TangentSplitRequest edges L sigma flow) {multiplier : ℕ}
    (hsourcePos : 0 < tangentSplitRequestSource source request)
    (htargetPos : 0 < tangentSplitRequestTarget target request)
    (hKh : K * h ≤ n)
    (hmultiplier : multiplier ∈
      tangentSplitCleanMultiplierLists edges source target L sigma flow
        n K h Phead X0 y dedicatedRows numericalGuards request) :
    tangentSplitRequestSource source request * multiplier ∈
        roughRawCandidateSet n h K ∧
      tangentSplitRequestTarget target request * multiplier ∈
        roughRawCandidateSet n h K := by
  let s := tangentSplitRequestSource source request
  let t := tangentSplitRequestTarget target request
  have hclean : multiplier ∈ tangentCleanCommonMultiplierList
      n K h Phead X0 y (max s t) (min s t)
        dedicatedRows numericalGuards := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists, s, t] using hmultiplier
  have hinterval : multiplier ∈
      tangentCommonMultiplierInterval n K h (max s t) (min s t) :=
    mem_tangentCommonMultiplierInterval.mpr
      (mem_tangentCleanCommonMultiplierList.mp hclean).1
  have hmaxPos : 0 < max s t :=
    hsourcePos.trans_le (le_max_left _ _)
  have hminPos : 0 < min s t := lt_min hsourcePos htargetPos
  have hendpoints := tangentCommonMultiplierInterval_endpoints
    hmaxPos hminPos min_le_max hinterval
  have hsIoc : s * multiplier ∈
      Finset.Ioc n (tangentBroadUpper n K h) := by
    rcases le_total s t with hst | hts
    · simpa only [min_eq_left hst] using hendpoints.2
    · simpa only [max_eq_left hts] using hendpoints.1
  have htIoc : t * multiplier ∈
      Finset.Ioc n (tangentBroadUpper n K h) := by
    rcases le_total s t with hst | hts
    · simpa only [max_eq_right hst] using hendpoints.1
    · simpa only [min_eq_right hts] using hendpoints.2
  rw [roughRawCandidateSet_eq_Ioc hKh]
  constructor
  · exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp hsIoc).1,
        (Finset.mem_Ioc.mp hsIoc).2.trans
          (tangentBroadUpper_le_two_mul n K h)⟩
  · exact Finset.mem_Ioc.mpr
      ⟨(Finset.mem_Ioc.mp htIoc).1,
        (Finset.mem_Ioc.mp htIoc).2.trans
          (tangentBroadUpper_le_two_mul n K h)⟩

/-- Multiplying two permitted prime labels by the same positive common
multiplier keeps the two endpoints in the same complete-rough row. -/
theorem tangentSplitEndpoints_completeRoughLabel_eq
    {y source target multiplier : ℕ}
    (hsourcePos : 0 < source) (htargetPos : 0 < target)
    (hsourceLe : source ≤ y) (htargetLe : target ≤ y)
    (hmultiplierPos : 0 < multiplier) :
    completeRoughLabel y (source * multiplier) =
      completeRoughLabel y (target * multiplier) := by
  calc
    completeRoughLabel y (source * multiplier) =
        completeRoughLabel y multiplier :=
      completeRoughLabel_small_left_mul
        hsourcePos hsourceLe hmultiplierPos
    _ = completeRoughLabel y (target * multiplier) :=
      (completeRoughLabel_small_left_mul
        htargetPos htargetLe hmultiplierPos).symm

/-! ## Finite Section 9 assembly once clean-list lower bounds are available -/

namespace BankPaperRealization

/-- Finite assembly of the canonical tangent stage.

The three clean-list hypotheses are exactly the outputs supplied eventually
by `eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical`.
Everything after them is constructed here: pair arithmetic, the `1/8`
collision budget, distinct common multipliers, the actual tangent update,
row preservation, and exact selector-tail valuation. -/
theorem exists_canonicalSectionNinePostTangentOutput_of_cleanListLower
    {c : ℝ} {depth n W K h X0 : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
    (pivot : BankPaperCanonicalTangentPrime n W)
    (density L sigma : ℝ)
    (hKh : K * h ≤ n)
    (hn : 0 < n) (hyLe : (yNat n : ℝ) ≤ n)
    (hySq : (yNat n : ℝ) ^ 2 ≤ n)
    (hdensity : 0 < density) (hL : 0 < L) (hsigma : 0 < sigma)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hfeasible : ∀ a ∈ roughRawCandidateSet n h K,
      0 ≤ x a ∧ x a ≤ 1)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral n
      (roughRawCandidateSet n h K) x)
    (hbalance : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed (roughRawCandidateSet n h K) x)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed (roughRawCandidateSet n h K) x)
    (hlowerPos : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      0 < bankPaperCanonicalTangentLowerCard
        R certificate fixed (roughRawCandidateSet n h K) x pivot
          L sigma density request)
    (hlower : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      bankPaperCanonicalTangentLowerCard
          R certificate fixed (roughRawCandidateSet n h K) x pivot
            L sigma density request ≤
        (tangentSplitCleanMultiplierLists
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card)
    (hlowerScale : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      ∀ side,
        density * n ≤
          (bankPaperCanonicalTangentLowerCard
            R certificate fixed (roughRawCandidateSet n h K) x pivot
              L sigma density request : ℝ) *
            tangentEndpointLabel
              (bankPaperCanonicalTangentRequestSource
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma)
              (bankPaperCanonicalTangentRequestTarget
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma) side request)
    (hslack : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      ∀ multiplier,
        multiplier ∈ tangentSplitCleanMultiplierLists
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request →
        (sigma / L ≤ x
              (bankPaperCanonicalTangentRequestSource
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ∧
            x (bankPaperCanonicalTangentRequestSource
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ≤ 1 - sigma / L) ∧
          (sigma / L ≤ x
              (bankPaperCanonicalTangentRequestTarget
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ∧
            x (bankPaperCanonicalTangentRequestTarget
                R certificate fixed (roughRawCandidateSet n h K) x pivot
                  L sigma request * multiplier) ≤ 1 - sigma / L))
    (hsmall : ∀ request : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      4 * (tangentSplitCensusTotalRequestUpper L sigma
            (tangentStarResidualL1
              (bankPaperCanonicalTangentResidual (W := W)
                R certificate fixed
                (roughRawCandidateSet n h K) x))
            (tangentStarSupportCount
              (BankPaperCanonicalTangentPrime n W)) / n) +
        ((bankPaperCanonicalTangentRequestSource
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentStarLabelIncidentTraffic pivot
              (bankPaperCanonicalTangentResidual R certificate fixed
                (roughRawCandidateSet n h K) x)
              bankPaperCanonicalTangentPrimeLabel)
            (tangentStarSupportCount
              (BankPaperCanonicalTangentPrime n W))
            (bankPaperCanonicalTangentRequestSource
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request) / n) +
        ((bankPaperCanonicalTangentRequestTarget
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request : ℝ) *
          tangentSplitCensusLabelRequestUpper L sigma
            (tangentStarLabelIncidentTraffic pivot
              (bankPaperCanonicalTangentResidual R certificate fixed
                (roughRawCandidateSet n h K) x)
              bankPaperCanonicalTangentPrimeLabel)
            (tangentStarSupportCount
              (BankPaperCanonicalTangentPrime n W))
            (bankPaperCanonicalTangentRequestTarget
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma request) / n) ≤ density ^ 2 / 24) :
    ∃ multiplier : BankPaperCanonicalTangentSplitRequest
        R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma → ℕ,
      (∀ request,
        multiplier request ∈ tangentSplitCleanMultiplierLists
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request) ∧
      TangentEndpointsDistinct
        (tangentSplitRequests
          (bankPaperCanonicalTangentEdges
            R certificate fixed (roughRawCandidateSet n h K) x pivot)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow
            R certificate fixed (roughRawCandidateSet n h K) x pivot))
        (bankPaperCanonicalTangentRequestSource
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma)
        (bankPaperCanonicalTangentRequestTarget
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma)
        multiplier ∧
      (∀ p : BankPaperCanonicalTangentPrime n W,
        tangentFlowDivergence
            (tangentStarFlow pivot
              (bankPaperCanonicalTangentResidual R certificate fixed
                (roughRawCandidateSet n h K) x)) p =
          bankPaperCanonicalTangentResidual R certificate fixed
            (roughRawCandidateSet n h K) x p) ∧
      (∀ q,
        (∑ request : BankPaperCanonicalTangentSplitRequest
              R certificate fixed (roughRawCandidateSet n h K) x pivot
                L sigma,
            tangentSplitRequestWeight request *
              (((bankPaperCanonicalTangentRequestSource
                    R certificate fixed (roughRawCandidateSet n h K) x pivot
                      L sigma request).factorization q : ℝ) -
                ((bankPaperCanonicalTangentRequestTarget
                    R certificate fixed (roughRawCandidateSet n h K) x pivot
                      L sigma request).factorization q : ℝ))) =
          bankPaperCanonicalSelectorValuationDeficit R certificate fixed
            (roughRawCandidateSet n h K) x q) ∧
      ∃ output : BankPaperCanonicalPostTangentOutput R certificate
          (roughRawCandidateSet n h K) fixed,
        output.selector =
          bankPaperCanonicalTangentUpdatedSelector R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma multiplier := by
  let candidates := roughRawCandidateSet n h K
  let residual := bankPaperCanonicalTangentResidual (W := W)
    R certificate fixed candidates x
  let edges := bankPaperCanonicalTangentEdges
    R certificate fixed candidates x pivot
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let flow := bankPaperCanonicalTangentEdgeFlow
    R certificate fixed candidates x pivot
  let requests := tangentSplitRequests edges L sigma flow
  let requestSource : TangentSplitRequest edges L sigma flow → ℕ :=
    tangentSplitRequestSource source
  let requestTarget : TangentSplitRequest edges L sigma flow → ℕ :=
    tangentSplitRequestTarget target
  let lowerCard : TangentSplitRequest edges L sigma flow → ℕ :=
    fun request ↦ tangentEffectiveLowerCard density n
      (min (requestSource request) (requestTarget request))
  have hcanonical :=
    bankPaperCanonicalSelectorRowIntegral_and_tangentStarBoundary
      R certificate fixed candidates x hrowIntegral pivot hbalance hsupport
        L sigma
  have hlabelInjective : Function.Injective
      (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W)) :=
    bankPaperCanonicalTangentPrimeLabel_injective
  have hlabelPrime : ∀ p : BankPaperCanonicalTangentPrime n W,
      (bankPaperCanonicalTangentPrimeLabel p).Prime :=
    bankPaperCanonicalTangentPrimeLabel_prime
  have hlabelUpper : ∀ p : BankPaperCanonicalTangentPrime n W,
      bankPaperCanonicalTangentPrimeLabel p ≤ yNat n :=
    bankPaperCanonicalTangentPrimeLabel_le_yNat
  have hlowerPos' : ∀ request : TangentSplitRequest edges L sigma flow,
      0 < lowerCard request := by
    simpa only [lowerCard, requestSource, requestTarget,
      bankPaperCanonicalTangentLowerCard,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget, edges, source, target, flow,
      candidates, bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using hlowerPos
  have hlower' : ∀ request : TangentSplitRequest edges L sigma flow,
      lowerCard request ≤
        (tangentSplitCleanMultiplierLists edges source target L sigma flow
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card := by
    simpa only [lowerCard, requestSource, requestTarget,
      bankPaperCanonicalTangentLowerCard,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget, edges, source, target, flow,
      candidates, bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using hlower
  have hlowerScale' : ∀ request : TangentSplitRequest edges L sigma flow,
      ∀ side,
        density * n ≤ (lowerCard request : ℝ) *
          tangentEndpointLabel requestSource requestTarget side request := by
    simpa only [lowerCard, requestSource, requestTarget,
      bankPaperCanonicalTangentLowerCard,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget, edges, source, target, flow,
      candidates, bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using hlowerScale
  have hsum : (∑ p : BankPaperCanonicalTangentPrime n W, residual p) = 0 := by
    simpa only [residual, candidates] using hcanonical.2.1
  have hstar :=
    R.tangentPaperStarSplitEndpointsDistinct_of_residualL1Census
      certificate fixedExceptional K h (roughHeadModulus W) X0 pivot
      residual bankPaperCanonicalTangentPrimeLabel hsum hlabelInjective
      hlabelPrime
      (tangentStarLabelIncidentTraffic pivot residual
        bankPaperCanonicalTangentPrimeLabel)
      (fun _q ↦ le_rfl) (yNat n) density hn hdensity hlabelUpper hyLe hySq
      hL hsigma lowerCard hlowerPos' hlower' hlowerScale'
      (by
        simpa only [residual, edges, source, target, flow, requestSource,
          requestTarget, candidates, bankPaperCanonicalTangentEdges,
          bankPaperCanonicalTangentEdgeFlow,
          bankPaperCanonicalTangentRequestSource,
          bankPaperCanonicalTangentRequestTarget] using hsmall)
  obtain ⟨multiplier, hmultiplierMem, hdistinct⟩ := hstar.2.2
  have hrequestPrime : ∀ request : TangentSplitRequest edges L sigma flow,
      (requestSource request).Prime ∧ (requestTarget request).Prime := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        hlabelPrime request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        hlabelPrime request.1.1.2
  have hrequestUpper : ∀ request : TangentSplitRequest edges L sigma flow,
      requestSource request ≤ yNat n ∧ requestTarget request ≤ yNat n := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        hlabelUpper request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        hlabelUpper request.1.1.2
  have hmultiplierPos : ∀ request : TangentSplitRequest edges L sigma flow,
      0 < multiplier request := by
    intro request
    exact tangentSplitCleanMultiplier_pos request (hmultiplierMem request)
  have hendpointMem : ∀ request : TangentSplitRequest edges L sigma flow,
      requestSource request * multiplier request ∈ candidates ∧
        requestTarget request * multiplier request ∈ candidates := by
    intro request
    exact tangentSplitCleanMultiplier_endpoints_mem_roughRawCandidateSet
      request (hrequestPrime request).1.pos (hrequestPrime request).2.pos
        hKh (hmultiplierMem request)
  have hsameRow : ∀ request : TangentSplitRequest edges L sigma flow,
      completeRoughLabel (yNat n)
          (requestSource request * multiplier request) =
        completeRoughLabel (yNat n)
          (requestTarget request * multiplier request) := by
    intro request
    exact tangentSplitEndpoints_completeRoughLabel_eq
      (hrequestPrime request).1.pos (hrequestPrime request).2.pos
      (hrequestUpper request).1 (hrequestUpper request).2
      (hmultiplierPos request)
  have hflowPos : ∀ edge ∈ edges, 0 < flow edge := by
    intro edge hedge
    simpa only [edges, flow, bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow, tangentStarEdgeFlow] using
      (mem_tangentStarPositiveEdges.mp hedge)
  have hsourceSlack : ∀ request : TangentSplitRequest edges L sigma flow,
      sigma / L ≤ x (requestSource request * multiplier request) ∧
        x (requestSource request * multiplier request) ≤ 1 - sigma / L := by
    intro request
    simpa only [requestSource, requestTarget, edges, source, target, flow,
      candidates, bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget] using
      (hslack request (multiplier request) (hmultiplierMem request)).1
  have htargetSlack : ∀ request : TangentSplitRequest edges L sigma flow,
      sigma / L ≤ x (requestTarget request * multiplier request) ∧
        x (requestTarget request * multiplier request) ≤ 1 - sigma / L := by
    intro request
    simpa only [requestSource, requestTarget, edges, source, target, flow,
      candidates, bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget] using
      (hslack request (multiplier request) (hmultiplierMem request)).2
  have hfeasibleUpdate := tangentSplitUpdate_feasible_and_margin
    edges source target flow hflowPos hL hsigma multiplier x candidates
      hdistinct hsourceSlack htargetSlack hfeasible
  have hrowPreserve : ∀ label,
      ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          tangentUpdate requests requestSource requestTarget multiplier
            tangentSplitRequestWeight x a =
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label, x a := by
    intro label
    simpa only [completeRoughRowFiber] using
      tangentUpdate_signatureRow requests requestSource requestTarget
        multiplier tangentSplitRequestWeight x candidates
        (completeRoughLabel (yNat n)) label
        (fun request _hrequest ↦ (hendpointMem request).1)
        (fun request _hrequest ↦ (hendpointMem request).2)
        (fun request _hrequest ↦ hsameRow request)
  have hrowIntegralUpdate :
      BankPaperCanonicalSelectorRowIntegral n candidates
        (tangentUpdate requests requestSource requestTarget multiplier
          tangentSplitRequestWeight x) := by
    intro label hlabel
    obtain ⟨k, hk⟩ := hrowIntegral label hlabel
    exact ⟨k, (hrowPreserve label).trans hk⟩
  have hboundary : ∀ q,
      ∑ request ∈ requests,
          tangentSplitRequestWeight request *
            ((requestSource request).factorization q -
              (requestTarget request).factorization q : ℝ) =
        ((certificate.selectorTailTarget R fixed).factorization q : ℝ) -
          ∑ a ∈ candidates, x a * (a.factorization q : ℝ) := by
    intro q
    simpa only [requests, tangentSplitRequests, requestSource, requestTarget,
      source, target, edges, flow, residual, candidates,
      bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget,
      bankPaperCanonicalSelectorValuationDeficit] using hcanonical.2.2.2 q
  have hresidualValuation : ∀ q,
      ∑ a ∈ candidates,
          tangentUpdate requests requestSource requestTarget multiplier
              tangentSplitRequestWeight x a * (a.factorization q : ℝ) =
        ((certificate.selectorTailTarget R fixed).factorization q : ℝ) :=
    tangentUpdate_valuation_eq_target requests requestSource requestTarget
      multiplier tangentSplitRequestWeight x candidates
      (fun q ↦ ((certificate.selectorTailTarget R fixed).factorization q : ℝ))
      (fun request _hrequest ↦ (hendpointMem request).1)
      (fun request _hrequest ↦ (hendpointMem request).2)
      (fun request _hrequest ↦ (hrequestPrime request).1.ne_zero)
      (fun request _hrequest ↦ (hrequestPrime request).2.ne_zero)
      (fun request _hrequest ↦ (hmultiplierPos request).ne') hboundary
  have hchargedValuation : ∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q :
            ℝ) +
          ∑ a ∈ candidates,
            tangentUpdate requests requestSource requestTarget multiplier
                tangentSplitRequestWeight x a * (a.factorization q : ℝ) =
        (certificate.prechargedTailTarget.factorization q : ℝ) := by
    apply (certificate.valuationCertificate_iff_selectorTailTarget
      R fixed
        (fun q ↦ ∑ a ∈ candidates,
          tangentUpdate requests requestSource requestTarget multiplier
              tangentSplitRequestWeight x a * (a.factorization q : ℝ))
        hfixedPositive hchargeDvd).2
    exact hresidualValuation
  let output : BankPaperCanonicalPostTangentOutput R certificate
      candidates fixed := {
    selector := tangentUpdate requests requestSource requestTarget multiplier
      tangentSplitRequestWeight x
    feasible := fun a ha ↦ hfeasibleUpdate.1 a ha
    rowIntegral := hrowIntegralUpdate
    valuationCertificate := hchargedValuation }
  refine ⟨multiplier, ?_, ?_, ?_, ?_, output, ?_⟩
  · simpa only [edges, source, target, flow, candidates,
      bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using hmultiplierMem
  · simpa only [requests, requestSource, requestTarget, edges, source, target,
      flow, candidates, bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget] using hdistinct
  · simpa only [residual, candidates] using hcanonical.2.2.1
  · simpa only [residual, candidates,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget] using hcanonical.2.2.2
  · rfl

end BankPaperRealization

namespace BankPaperRealization

/-- Eventual Section 9 assembly with the canonical clean-list theorem
actually substituted.  The conclusion exposes both membership of the chosen
multipliers in the literal clean lists and endpoint distinctness, alongside
the concrete post-tangent output whose selector is the actual update. -/
theorem eventually_exists_canonicalSectionNinePostTangentOutput :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : ℝ) (depth W K h X0 : ℕ),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
        (pivot : BankPaperCanonicalTangentPrime n W)
        (density L sigma : ℝ),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        n /
            min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) ≤
          tangentBroadUpper n K h /
            max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        tangentEffectiveLowerCard density n
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) +
            tangentCanonicalExceptionalNatUpper n K h X0 (yNat n)
              (max
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request))
              (min
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)) +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K h
            (max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))) →
      K * h ≤ n → 0 < n →
      (yNat n : ℝ) ≤ n → (yNat n : ℝ) ^ 2 ≤ n →
      0 < density → 0 < L → 0 < sigma →
      (∀ a ∈ fixed, 0 < a) →
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget →
      (∀ a ∈ roughRawCandidateSet n h K, 0 ≤ x a ∧ x a ≤ 1) →
      BankPaperCanonicalSelectorRowIntegral n
        (roughRawCandidateSet n h K) x →
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed (roughRawCandidateSet n h K) x →
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed (roughRawCandidateSet n h K) x →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        ∀ multiplier,
          multiplier ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request →
          (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ∧
              x (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ∧
              x (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request *
                    multiplier) ≤ 1 - sigma / L)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        4 * (tangentSplitCensusTotalRequestUpper L sigma
              (tangentStarResidualL1
                (bankPaperCanonicalTangentResidual (W := W)
                  R certificate fixed
                  (roughRawCandidateSet n h K) x))
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W)) / n) +
          ((bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n h K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) / n) +
          ((bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n h K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) / n) ≤
            density ^ 2 / 24) →
      ∃ multiplier : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma →
            ℕ,
        (∀ request,
          multiplier request ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot))
          (bankPaperCanonicalTangentRequestSource R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma)
          (bankPaperCanonicalTangentRequestTarget R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma)
          multiplier ∧
        ∃ output : BankPaperCanonicalPostTangentOutput R certificate
            (roughRawCandidateSet n h K) fixed,
          output.selector =
            bankPaperCanonicalTangentUpdatedSelector R certificate fixed
              (roughRawCandidateSet n h K) x pivot L sigma multiplier := by
  filter_upwards
    [eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical]
      with n hclean
  intro c depth W K h X0 R certificate fixedExceptional
    fixed x pivot density L sigma hfixedTail hTwoW hPrefix hyCutoff
    hinterval harithmetic hKh hn hyLe hySq hdensity hL hsigma
    hfixedPositive hchargeDvd hfeasible hrowIntegral hbalance hsupport
    hslack hsmall
  let candidates := roughRawCandidateSet n h K
  let edges := bankPaperCanonicalTangentEdges
    R certificate fixed candidates x pivot
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let flow := bankPaperCanonicalTangentEdgeFlow
    R certificate fixed candidates x pivot
  let requestSource : TangentSplitRequest edges L sigma flow → ℕ :=
    tangentSplitRequestSource source
  let requestTarget : TangentSplitRequest edges L sigma flow → ℕ :=
    tangentSplitRequestTarget target
  have hrequestPrime : ∀ request : TangentSplitRequest edges L sigma flow,
      (requestSource request).Prime ∧ (requestTarget request).Prime := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hrequestBand : ∀ request : TangentSplitRequest edges L sigma flow,
      (W < requestSource request ∧ requestSource request ≤ yNat n) ∧
        (W < requestTarget request ∧ requestTarget request ≤ yNat n) := by
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
  have hcleanData : ∀ request : TangentSplitRequest edges L sigma flow,
      0 < tangentEffectiveLowerCard density n
          (min (requestSource request) (requestTarget request)) ∧
        tangentEffectiveLowerCard density n
            (min (requestSource request) (requestTarget request)) ≤
          (tangentCleanCommonMultiplierList n K h (roughHeadModulus W) X0
            (yNat n) (max (requestSource request) (requestTarget request))
            (min (requestSource request) (requestTarget request))
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional)).card ∧
        density * n ≤
          (tangentEffectiveLowerCard density n
              (min (requestSource request) (requestTarget request)) : ℝ) *
            max (requestSource request) (requestTarget request) ∧
        density * n ≤
          (tangentEffectiveLowerCard density n
              (min (requestSource request) (requestTarget request)) : ℝ) *
            min (requestSource request) (requestTarget request) := by
    intro request
    let u := max (requestSource request) (requestTarget request)
    let v := min (requestSource request) (requestTarget request)
    have huPrime : u.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [u, max_eq_right hst] using (hrequestPrime request).2
      · simpa only [u, max_eq_left hts] using (hrequestPrime request).1
    have hvPrime : v.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [v, min_eq_left hst] using (hrequestPrime request).1
      · simpa only [v, min_eq_right hts] using (hrequestPrime request).2
    have hWv : W < v :=
      lt_min (hrequestBand request).1.1 (hrequestBand request).2.1
    have huv : v ≤ u := min_le_max
    have huy : u ≤ yNat n :=
      max_le (hrequestBand request).1.2 (hrequestBand request).2.2
    have hinterval' : n / v ≤ tangentBroadUpper n K h / u := by
      simpa only [u, v, requestSource, requestTarget, edges, source, target,
        flow, candidates, bankPaperCanonicalTangentEdges,
        bankPaperCanonicalTangentEdgeFlow,
        bankPaperCanonicalTangentRequestSource,
        bankPaperCanonicalTangentRequestTarget] using hinterval request
    have harithmetic' :
        tangentEffectiveLowerCard density n v +
            tangentCanonicalExceptionalNatUpper
              n K h X0 (yNat n) u v +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K h u v := by
      simpa only [u, v, requestSource, requestTarget, edges, source, target,
        flow, candidates, bankPaperCanonicalTangentEdges,
        bankPaperCanonicalTangentEdgeFlow,
        bankPaperCanonicalTangentRequestSource,
        bankPaperCanonicalTangentRequestTarget] using harithmetic request
    exact hclean c depth (upperEndpoint n (upperTailLength c n)) W K h X0
      u v R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth) R certificate fixedExceptional density
      hfixedTail hTwoW hPrefix hWv huv huy hyCutoff huPrime hvPrime
      hdensity hinterval' harithmetic'
  have hlowerPos : ∀ request : BankPaperCanonicalTangentSplitRequest
      R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      0 < bankPaperCanonicalTangentLowerCard R certificate fixed
        (roughRawCandidateSet n h K) x pivot L sigma density request := by
    intro request
    simpa only [bankPaperCanonicalTangentLowerCard,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget, requestSource, requestTarget,
      edges, source, target, flow, candidates,
      bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using (hcleanData request).1
  have hlower : ∀ request : BankPaperCanonicalTangentSplitRequest
      R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      bankPaperCanonicalTangentLowerCard R certificate fixed
          (roughRawCandidateSet n h K) x pivot L sigma density request ≤
        (tangentSplitCleanMultiplierLists
          (bankPaperCanonicalTangentEdges R certificate fixed
            (roughRawCandidateSet n h K) x pivot)
          (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
          (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
          L sigma
          (bankPaperCanonicalTangentEdgeFlow R certificate fixed
            (roughRawCandidateSet n h K) x pivot)
          n K h (roughHeadModulus W) X0 (yNat n)
          R.tangentPaperDedicatedRows
          (R.tangentPaperNumericalGuardSet
            certificate fixedExceptional) request).card := by
    intro request
    simpa only [bankPaperCanonicalTangentLowerCard,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget,
      tangentSplitCleanMultiplierLists, tangentCleanMultiplierLists,
      requestSource, requestTarget, edges, source, target, flow, candidates,
      bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using (hcleanData request).2.1
  have hlowerScale : ∀ request : BankPaperCanonicalTangentSplitRequest
      R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
      ∀ side,
        density * n ≤
          (bankPaperCanonicalTangentLowerCard R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma density request :
              ℝ) *
            tangentEndpointLabel
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma)
              side request := by
    intro request side
    have hminScale := (hcleanData request).2.2.2
    cases side with
    | source =>
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            (by
              show ((min (requestSource request) (requestTarget request) : ℕ) : ℝ) ≤
                (requestSource request : ℝ)
              exact_mod_cast
                (min_le_left (requestSource request) (requestTarget request)))
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalTangentLowerCard,
          bankPaperCanonicalTangentRequestSource,
          bankPaperCanonicalTangentRequestTarget, tangentEndpointLabel,
          requestSource, requestTarget, edges, source, target, flow,
          candidates, bankPaperCanonicalTangentEdges,
          bankPaperCanonicalTangentEdgeFlow] using hscale
    | target =>
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            (by
              show ((min (requestSource request) (requestTarget request) : ℕ) : ℝ) ≤
                (requestTarget request : ℝ)
              exact_mod_cast
                (min_le_right (requestSource request) (requestTarget request)))
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalTangentLowerCard,
          bankPaperCanonicalTangentRequestSource,
          bankPaperCanonicalTangentRequestTarget, tangentEndpointLabel,
          requestSource, requestTarget, edges, source, target, flow,
          candidates, bankPaperCanonicalTangentEdges,
          bankPaperCanonicalTangentEdgeFlow] using hscale
  have hassembly :=
    R.exists_canonicalSectionNinePostTangentOutput_of_cleanListLower
      certificate fixedExceptional fixed x pivot density L sigma hKh hn
      hyLe hySq hdensity hL hsigma hfixedPositive hchargeDvd hfeasible
      hrowIntegral hbalance hsupport hlowerPos hlower hlowerScale
      hslack hsmall
  obtain ⟨multiplier, hmem, hdistinct, _hdivergence, _hboundary,
      output, houtput⟩ := hassembly
  exact ⟨multiplier, hmem, hdistinct, output, houtput⟩

end BankPaperRealization

namespace BankPaperRealization

/-- Eventual canonical clean-list inputs for every request of the literal
prime-residual star.  Candidate counting, the canonical exceptional bound,
and deterministic deletion counting are all discharged by the imported
clean-list theorem.  Only the request-wise interval and final natural-number
loss comparison remain as premises. -/
theorem eventually_canonicalSectionNineCleanListLower :
    ∀ᶠ n : ℕ in atTop,
      ∀ (c : ℝ) (depth W K h X0 : ℕ)
        (left right : ℕ → ℕ) (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
        (pivot : BankPaperCanonicalTangentPrime n W)
        (L sigma density : ℝ),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      0 < density →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        n /
            min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request) ≤
          tangentBroadUpper n K h /
            max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        tangentEffectiveLowerCard density n
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)) +
            tangentCanonicalExceptionalNatUpper n K h X0 (yNat n)
              (max
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request))
              (min
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma request)) +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K h
            (max
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))
            (min
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request)
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n h K) x pivot L sigma request))) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        0 < bankPaperCanonicalTangentLowerCard R certificate fixed
          (roughRawCandidateSet n h K) x pivot L sigma density request) ∧
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        bankPaperCanonicalTangentLowerCard R certificate fixed
            (roughRawCandidateSet n h K) x pivot L sigma density request ≤
          (tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n h K) x pivot)
            n K h (roughHeadModulus W) X0 (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card) ∧
      ∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed (roughRawCandidateSet n h K) x pivot L sigma,
        ∀ side,
          density * n ≤
            (bankPaperCanonicalTangentLowerCard R certificate fixed
              (roughRawCandidateSet n h K) x pivot L sigma density request :
                ℝ) *
              tangentEndpointLabel
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n h K) x pivot L sigma)
                side request := by
  filter_upwards
    [eventually_tangentPaperCleanCommonMultiplierList_card_lower_canonical]
      with n hclean
  intro c depth W K h X0 left right changed R certificate fixedExceptional
    fixed x pivot L sigma density hfixedTail hTwoW hPrefix hyCutoff
    hdensity hinterval harithmetic
  let candidates := roughRawCandidateSet n h K
  let edges := bankPaperCanonicalTangentEdges
    R certificate fixed candidates x pivot
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let flow := bankPaperCanonicalTangentEdgeFlow
    R certificate fixed candidates x pivot
  let requestSource : TangentSplitRequest edges L sigma flow → ℕ :=
    tangentSplitRequestSource source
  let requestTarget : TangentSplitRequest edges L sigma flow → ℕ :=
    tangentSplitRequestTarget target
  have hrequestPrime : ∀ request : TangentSplitRequest edges L sigma flow,
      (requestSource request).Prime ∧ (requestTarget request).Prime := by
    intro request
    constructor
    · simpa only [requestSource, source, tangentSplitRequestSource,
        tangentSplitRequestEdge, tangentStarEdgeSource] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
    · simpa only [requestTarget, target, tangentSplitRequestTarget,
        tangentSplitRequestEdge, tangentStarEdgeTarget] using
        bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hrequestBand : ∀ request : TangentSplitRequest edges L sigma flow,
      (W < requestSource request ∧ requestSource request ≤ yNat n) ∧
        (W < requestTarget request ∧ requestTarget request ≤ yNat n) := by
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
  have hcleanData : ∀ request : TangentSplitRequest edges L sigma flow,
      0 < tangentEffectiveLowerCard density n
          (min (requestSource request) (requestTarget request)) ∧
        tangentEffectiveLowerCard density n
            (min (requestSource request) (requestTarget request)) ≤
          (tangentCleanCommonMultiplierList n K h (roughHeadModulus W) X0
            (yNat n) (max (requestSource request) (requestTarget request))
            (min (requestSource request) (requestTarget request))
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional)).card ∧
        density * n ≤
          (tangentEffectiveLowerCard density n
              (min (requestSource request) (requestTarget request)) : ℝ) *
            max (requestSource request) (requestTarget request) ∧
        density * n ≤
          (tangentEffectiveLowerCard density n
              (min (requestSource request) (requestTarget request)) : ℝ) *
            min (requestSource request) (requestTarget request) := by
    intro request
    let u := max (requestSource request) (requestTarget request)
    let v := min (requestSource request) (requestTarget request)
    have huPrime : u.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [u, max_eq_right hst] using (hrequestPrime request).2
      · simpa only [u, max_eq_left hts] using (hrequestPrime request).1
    have hvPrime : v.Prime := by
      rcases le_total (requestSource request) (requestTarget request) with
        hst | hts
      · simpa only [v, min_eq_left hst] using (hrequestPrime request).1
      · simpa only [v, min_eq_right hts] using (hrequestPrime request).2
    have hWv : W < v := by
      exact lt_min (hrequestBand request).1.1 (hrequestBand request).2.1
    have huv : v ≤ u := min_le_max
    have huy : u ≤ yNat n := by
      exact max_le (hrequestBand request).1.2 (hrequestBand request).2.2
    have hinterval' : n / v ≤ tangentBroadUpper n K h / u := by
      simpa only [u, v, requestSource, requestTarget, edges, source, target,
        flow, candidates, bankPaperCanonicalTangentEdges,
        bankPaperCanonicalTangentEdgeFlow,
        bankPaperCanonicalTangentRequestSource,
        bankPaperCanonicalTangentRequestTarget] using hinterval request
    have harithmetic' :
        tangentEffectiveLowerCard density n v +
            tangentCanonicalExceptionalNatUpper
              n K h X0 (yNat n) u v +
            4 + 4 * bankPaperSharpMarkerBudget n ≤
          tangentRoughHeadCandidateLower W n K h u v := by
      simpa only [u, v, requestSource, requestTarget, edges, source, target,
        flow, candidates, bankPaperCanonicalTangentEdges,
        bankPaperCanonicalTangentEdgeFlow,
        bankPaperCanonicalTangentRequestSource,
        bankPaperCanonicalTangentRequestTarget] using harithmetic request
    exact hclean c depth (upperEndpoint n (upperTailLength c n)) W K h X0
      u v left right changed R certificate fixedExceptional density
      hfixedTail hTwoW hPrefix hWv huv huy hyCutoff huPrime hvPrime
      hdensity hinterval' harithmetic'
  constructor
  · intro request
    simpa only [bankPaperCanonicalTangentLowerCard,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget, requestSource, requestTarget,
      edges, source, target, flow, candidates,
      bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using (hcleanData request).1
  constructor
  · intro request
    simpa only [bankPaperCanonicalTangentLowerCard,
      bankPaperCanonicalTangentRequestSource,
      bankPaperCanonicalTangentRequestTarget,
      tangentSplitCleanMultiplierLists, tangentCleanMultiplierLists,
      requestSource, requestTarget, edges, source, target, flow, candidates,
      bankPaperCanonicalTangentEdges,
      bankPaperCanonicalTangentEdgeFlow] using (hcleanData request).2.1
  · intro request side
    have hminScale := (hcleanData request).2.2.2
    cases side with
    | source =>
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            (by
              show ((min (requestSource request) (requestTarget request) : ℕ) : ℝ) ≤
                (requestSource request : ℝ)
              exact_mod_cast
                (min_le_left (requestSource request) (requestTarget request)))
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalTangentLowerCard,
          bankPaperCanonicalTangentRequestSource,
          bankPaperCanonicalTangentRequestTarget, tangentEndpointLabel,
          requestSource, requestTarget, edges, source, target, flow,
          candidates, bankPaperCanonicalTangentEdges,
          bankPaperCanonicalTangentEdgeFlow] using hscale
    | target =>
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            (by
              show ((min (requestSource request) (requestTarget request) : ℕ) : ℝ) ≤
                (requestTarget request : ℝ)
              exact_mod_cast
                (min_le_right (requestSource request) (requestTarget request)))
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalTangentLowerCard,
          bankPaperCanonicalTangentRequestSource,
          bankPaperCanonicalTangentRequestTarget, tangentEndpointLabel,
          requestSource, requestTarget, edges, source, target, flow,
          candidates, bankPaperCanonicalTangentEdges,
          bankPaperCanonicalTangentEdgeFlow] using hscale

end BankPaperRealization

namespace BankPaperRealization

/-- Convert the finite post-tangent output into exactly the existential data
requested by `BankPaperCanonicalPostTangentContinuationAtDepth`.  The only
extra premises are the interval, divisibility, and disjointness geometry
which that continuation itself records. -/
theorem canonicalPostTangentContinuationData_of_output
    {c : ℝ} {depth n : ℕ}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (candidates fixed : Finset ℕ)
    (output : BankPaperCanonicalPostTangentOutput
      R certificate candidates fixed)
    (hcandidates : candidates ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hfixed : fixed ⊆
      factorInterval n (upperEndpoint n (upperTailLength c n)))
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (hfixedCandidate : Disjoint fixed candidates)
    (hfixedBank : ∀ slot selected,
      Disjoint fixed (R.exactificationState slot selected))
    (hcandidateBank : ∀ slot selected,
      Disjoint candidates (R.exactificationState slot selected))
    (hanchorsFixed : Disjoint certificate.anchors fixed)
    (hanchorsCandidate : Disjoint certificate.anchors candidates) :
    ∃ candidates' : Finset ℕ, ∃ selector : ℕ → ℝ,
      ∃ fixed' : Finset ℕ,
        candidates' ⊆
            factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        fixed' ⊆
            factorInterval n (upperEndpoint n (upperTailLength c n)) ∧
        (∀ a ∈ candidates', 0 ≤ selector a ∧ selector a ≤ 1) ∧
        (∀ label ∈ completeRoughLabelSet (yNat n) candidates',
          ∃ k : ℤ,
            ∑ a ∈ completeRoughRowFiber
                (yNat n) candidates' label, selector a = (k : ℝ)) ∧
        R.selectorTailCharge fixed' ∣
          certificate.prechargedTailTarget ∧
        (∀ q,
          ∑ a ∈ candidates',
              selector a * (a.factorization q : ℝ) =
            ((certificate.selectorTailTarget R fixed').factorization q :
              ℝ)) ∧
        Disjoint fixed' candidates' ∧
        (∀ slot selected,
          Disjoint fixed' (R.exactificationState slot selected)) ∧
        (∀ slot selected,
          Disjoint candidates'
            (R.exactificationState slot selected)) ∧
        Disjoint certificate.anchors fixed' ∧
        Disjoint certificate.anchors candidates' := by
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have haInterval : a ∈
        Finset.Ioc n (upperEndpoint n (upperTailLength c n)) := by
      simpa only [factorInterval] using hfixed ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp haInterval).1
  have hresidualValuation : ∀ q,
      ∑ a ∈ candidates,
          output.selector a * (a.factorization q : ℝ) =
        ((certificate.selectorTailTarget R fixed).factorization q : ℝ) := by
    apply (certificate.valuationCertificate_iff_selectorTailTarget
      R fixed
        (fun q ↦ ∑ a ∈ candidates,
          output.selector a * (a.factorization q : ℝ))
        hfixedPositive hchargeDvd).1
    exact output.valuationCertificate
  exact ⟨candidates, output.selector, fixed, hcandidates, hfixed,
    output.feasible, output.rowIntegral, hchargeDvd, hresidualValuation,
    hfixedCandidate, hfixedBank, hcandidateBank, hanchorsFixed,
    hanchorsCandidate⟩

end BankPaperRealization

end

end Erdos390.WholePaper
