import Erdos390.WholePaper.TangentPaperCleanListAbsorption
import Erdos390.WholePaper.BankPaperCanonicalSectionNineAssembly

/-!
# Canonical Section 9 assembly with the paper clean-list loss absorbed

This integration layer fixes the literal Section 9 choices

* `h = upperTailLength c n`,
* `X0 = tangentPaperExceptionalCutoff deltaStar n`, and
* `density = tangentPaperCleanListDensity W r0`.

It invokes
`eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed`
directly.  Consequently neither the common-multiplier interval inequality,
the candidate-floor-versus-loss inequality, nor a request-wise list-card
lower bound occurs among the premises of the terminal below.

The remaining inputs are visible and belong to later Section 9 layers:

* geometry/guard placement: the exceptional-tail containment, `W` and guard
  depth inequalities, the central-cutoff inequality, endpoint ratio,
  broad-candidate containment, positivity of `n`, and the two `yNat` scale
  inequalities;
* selector state and balance: positivity of the fixed bank, feasibility,
  integral complete-rough rows, exact band balance, prime-band deficit
  support, tail-charge divisibility, and endpoint slack;
* traffic: exactly the displayed residual-L1 plus the two endpoint
  incident-label census contributions.
-/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-! ## Absorbed clean lists for every canonical star request -/

/-- The request-wise clean-list data needed by the finite Section 9
assembly, now obtained from the absorbed paper terminal.  The sole
request-specific numerical input is the paper geometry `max/min <= r0`;
the interval and every list loss are proved internally. -/
theorem eventually_canonicalSectionNineCleanListLower_absorbed
    (W K : ℕ) {c r0 deltaStar : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (depth : ℕ) (left right : ℕ → ℕ)
        (changed : Finset ℕ),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          left right changed)
        (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
        (pivot : BankPaperCanonicalTangentPrime n W)
        (L sigma : ℝ),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        ((max
            (bankPaperCanonicalTangentRequestSource R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request)
            (bankPaperCanonicalTangentRequestTarget R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request) : ℕ) : ℝ) /
          ((min
            (bankPaperCanonicalTangentRequestSource R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request)
            (bankPaperCanonicalTangentRequestTarget R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request) : ℕ) : ℝ) ≤ r0) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        0 < bankPaperCanonicalTangentLowerCard R certificate fixed
          (roughRawCandidateSet n (upperTailLength c n) K) x pivot
          L sigma (tangentPaperCleanListDensity W r0) request) ∧
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        bankPaperCanonicalTangentLowerCard R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x pivot
            L sigma (tangentPaperCleanListDensity W r0) request ≤
          (tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request).card) ∧
      ∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        ∀ side,
          tangentPaperCleanListDensity W r0 * n ≤
            (bankPaperCanonicalTangentLowerCard R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot
              L sigma (tangentPaperCleanListDensity W r0) request : ℝ) *
              tangentEndpointLabel
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma)
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma)
                side request := by
  have hclean :=
    eventually_tangentPaperCleanCommonMultiplierList_card_lower_absorbed
      W K (tailC := c) (r0 := r0) (deltaStar := deltaStar)
      hc hr0one hr0three hdelta hdeltaUpper hmainSmall
  filter_upwards [hclean] with n hcleanN
  intro depth left right changed R certificate fixedExceptional fixed x
    pivot L sigma hfixedTail hTwoW hPrefix hyCutoff hratio
  let candidates := roughRawCandidateSet n (upperTailLength c n) K
  let edges := bankPaperCanonicalTangentEdges
    R certificate fixed candidates x pivot
  let source := tangentStarEdgeSource
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let target := tangentStarEdgeTarget
    (bankPaperCanonicalTangentPrimeLabel (n := n) (W := W))
  let flow := bankPaperCanonicalTangentEdgeFlow
    R certificate fixed candidates x pivot
  let requestSource :=
    tangentSplitRequestSource
      (edges := edges) (L := L) (sigma := sigma) (flow := flow) source
  let requestTarget :=
    tangentSplitRequestTarget
      (edges := edges) (L := L) (sigma := sigma) (flow := flow) target
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
      0 < tangentEffectiveLowerCard
          (tangentPaperCleanListDensity W r0) n
          (min (requestSource request) (requestTarget request)) ∧
        tangentEffectiveLowerCard (tangentPaperCleanListDensity W r0) n
            (min (requestSource request) (requestTarget request)) ≤
          (tangentCleanCommonMultiplierList n K (upperTailLength c n)
            (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            (max (requestSource request) (requestTarget request))
            (min (requestSource request) (requestTarget request))
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional)).card ∧
        tangentPaperCleanListDensity W r0 * n ≤
          (tangentEffectiveLowerCard (tangentPaperCleanListDensity W r0) n
              (min (requestSource request) (requestTarget request)) : ℝ) *
            max (requestSource request) (requestTarget request) ∧
        tangentPaperCleanListDensity W r0 * n ≤
          (tangentEffectiveLowerCard (tangentPaperCleanListDensity W r0) n
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
    have hvu : v ≤ u := min_le_max
    have huy : u ≤ yNat n :=
      max_le (hrequestBand request).1.2 (hrequestBand request).2.2
    have hratio' : (u : ℝ) / (v : ℝ) ≤ r0 := by
      simpa only [u, v, requestSource, requestTarget, edges, source, target,
        flow, candidates, bankPaperCanonicalTangentEdges,
        bankPaperCanonicalTangentEdgeFlow,
        bankPaperCanonicalTangentRequestSource,
        bankPaperCanonicalTangentRequestTarget] using hratio request
    exact hcleanN c depth (upperEndpoint n (upperTailLength c n)) u v
      left right changed R certificate fixedExceptional hfixedTail hTwoW
      hPrefix hWv hvu huy hyCutoff huPrime hvPrime hratio'
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
        have hminSource :
            ((min (requestSource request) (requestTarget request) : Nat) :
                Real) <= (requestSource request : Real) := by
          exact_mod_cast
            (min_le_left (requestSource request) (requestTarget request))
        have hscale := hminScale.trans
          (mul_le_mul_of_nonneg_left
            hminSource
            (Nat.cast_nonneg _))
        simpa only [bankPaperCanonicalTangentLowerCard,
          bankPaperCanonicalTangentRequestSource,
          bankPaperCanonicalTangentRequestTarget, tangentEndpointLabel,
          requestSource, requestTarget, edges, source, target, flow,
          candidates, bankPaperCanonicalTangentEdges,
          bankPaperCanonicalTangentEdgeFlow] using hscale
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
        simpa only [bankPaperCanonicalTangentLowerCard,
          bankPaperCanonicalTangentRequestSource,
          bankPaperCanonicalTangentRequestTarget, tangentEndpointLabel,
          requestSource, requestTarget, edges, source, target, flow,
          candidates, bankPaperCanonicalTangentEdges,
          bankPaperCanonicalTangentEdgeFlow] using hscale

/-! ## Eventual Section 9 output with clean-list arithmetic removed -/

/-- Canonical post-tangent output at the literal paper clean-list scales.

Compared with
`eventually_exists_canonicalSectionNinePostTangentOutput`, the following
premises have disappeared:

* the request-wise common-multiplier interval inequality;
* the request-wise candidate-floor-versus-loss inequality;
* every positive/list-card/effective-scale clean-list hypothesis.

The proof calls the absorbed clean-list terminal above and then the finite
Section 9 assembly.  What remains is precisely selector state, endpoint
geometry/slack, and the residual-L1/incident-traffic census. -/
theorem eventually_exists_canonicalSectionNinePostTangentOutput_absorbed
    (W K : ℕ) {c r0 deltaStar : ℝ}
    (hc : 0 < c) (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdelta : 0 < deltaStar) (hdeltaUpper : deltaStar < 1 / 18)
    (hmainSmall :
      80 * tangentSelbergCanonicalMainConstant * deltaStar <
        tangentPaperHeadGap W r0) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (depth : ℕ),
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (fixedExceptional fixed : Finset ℕ) (x : ℕ → ℝ)
        (pivot : BankPaperCanonicalTangentPrime n W)
        (L sigma : ℝ),
      fixedExceptional ⊆
          Finset.Ioc (2 * n) (upperEndpoint n (upperTailLength c n)) →
      2 ≤ W → 2 * depth + 1 ≤ W →
      yNat n < centralAnchorCutoff depth n →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        ((max
            (bankPaperCanonicalTangentRequestSource R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request)
            (bankPaperCanonicalTangentRequestTarget R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request) : ℕ) : ℝ) /
          ((min
            (bankPaperCanonicalTangentRequestSource R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request)
            (bankPaperCanonicalTangentRequestTarget R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x
                pivot L sigma request) : ℕ) : ℝ) ≤ r0) →
      K * upperTailLength c n ≤ n → 0 < n →
      (yNat n : ℝ) ≤ n → (yNat n : ℝ) ^ 2 ≤ n →
      0 < L → 0 < sigma →
      (∀ a ∈ fixed, 0 < a) →
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget →
      (∀ a ∈ roughRawCandidateSet n (upperTailLength c n) K,
        0 ≤ x a ∧ x a ≤ 1) →
      BankPaperCanonicalSelectorRowIntegral n
        (roughRawCandidateSet n (upperTailLength c n) K) x →
      BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
        R certificate fixed
          (roughRawCandidateSet n (upperTailLength c n) K) x →
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand (W := W)
        R certificate fixed
          (roughRawCandidateSet n (upperTailLength c n) K) x →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        ∀ multiplier,
          multiplier ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request →
          (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ∧
              x (bankPaperCanonicalTangentRequestSource R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ x
                (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ∧
              x (bankPaperCanonicalTangentRequestTarget R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x
                    pivot L sigma request * multiplier) ≤ 1 - sigma / L)) →
      (∀ request : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma,
        4 * (tangentSplitCensusTotalRequestUpper L sigma
              (tangentStarResidualL1
                (bankPaperCanonicalTangentResidual (W := W)
                  R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x))
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W)) / n) +
          ((bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestSource R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request) / n) +
          ((bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request : ℝ) *
            tangentSplitCensusLabelRequestUpper L sigma
              (tangentStarLabelIncidentTraffic pivot
                (bankPaperCanonicalTangentResidual R certificate fixed
                  (roughRawCandidateSet n (upperTailLength c n) K) x)
                bankPaperCanonicalTangentPrimeLabel)
              (tangentStarSupportCount
                (BankPaperCanonicalTangentPrime n W))
              (bankPaperCanonicalTangentRequestTarget R certificate fixed
                (roughRawCandidateSet n (upperTailLength c n) K) x
                  pivot L sigma request) / n) ≤
            tangentPaperCleanListDensity W r0 ^ 2 / 24) →
      ∃ multiplier : BankPaperCanonicalTangentSplitRequest
          R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma → ℕ,
        (∀ request,
          multiplier request ∈ tangentSplitCleanMultiplierLists
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
            (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            n K (upperTailLength c n) (roughHeadModulus W)
            (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
            R.tangentPaperDedicatedRows
            (R.tangentPaperNumericalGuardSet
              certificate fixedExceptional) request) ∧
        TangentEndpointsDistinct
          (tangentSplitRequests
            (bankPaperCanonicalTangentEdges R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot)
            L sigma
            (bankPaperCanonicalTangentEdgeFlow R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot))
          (bankPaperCanonicalTangentRequestSource R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma)
          (bankPaperCanonicalTangentRequestTarget R certificate fixed
            (roughRawCandidateSet n (upperTailLength c n) K) x
              pivot L sigma)
          multiplier ∧
        ∃ output : BankPaperCanonicalPostTangentOutput R certificate
            (roughRawCandidateSet n (upperTailLength c n) K) fixed,
          output.selector =
            bankPaperCanonicalTangentUpdatedSelector R certificate fixed
              (roughRawCandidateSet n (upperTailLength c n) K) x pivot
                L sigma multiplier := by
  have hcleanEvent :=
    eventually_canonicalSectionNineCleanListLower_absorbed
      W K (c := c) (r0 := r0) (deltaStar := deltaStar)
      hc hr0one hr0three hdelta hdeltaUpper hmainSmall
  filter_upwards [hcleanEvent] with n hcleanN
  intro depth R certificate fixedExceptional fixed x pivot L sigma
    hfixedTail hTwoW hPrefix hyCutoff hratio hKh hn hyLe hySq hL hsigma
    hfixedPositive hchargeDvd hfeasible hrowIntegral hbalance hsupport
    hslack hsmall
  have hclean := hcleanN depth R.anchorGuardLeftCore
    R.anchorGuardRightCore (R.centralChangedMarkers depth) R certificate
    fixedExceptional fixed x pivot L sigma hfixedTail hTwoW hPrefix
    hyCutoff hratio
  have hdensity : 0 < tangentPaperCleanListDensity W r0 :=
    tangentPaperCleanListDensity_pos W (r0 := r0)
      (hr0three.trans (by norm_num))
  have hassembly :=
    R.exists_canonicalSectionNinePostTangentOutput_of_cleanListLower
      (c := c) (depth := depth) (n := n) (W := W) (K := K)
      (h := upperTailLength c n)
      (X0 := tangentPaperExceptionalCutoff deltaStar n)
      certificate fixedExceptional fixed x pivot
      (tangentPaperCleanListDensity W r0) L sigma hKh hn hyLe hySq
      hdensity hL hsigma hfixedPositive hchargeDvd hfeasible hrowIntegral
      hbalance hsupport hclean.1 hclean.2.1 hclean.2.2 hslack hsmall
  obtain ⟨multiplier, hmem, hdistinct, _hdivergence, _hboundary,
      output, houtput⟩ := hassembly
  exact ⟨multiplier, hmem, hdistinct, output, houtput⟩

end BankPaperRealization

end

end Erdos390.WholePaper
