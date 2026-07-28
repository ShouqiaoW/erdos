import Erdos390.WholePaper.BankPaperCanonicalPreTangentSelector
import Erdos390.WholePaper.TangentRatioCellEarthmover
import Erdos390.WholePaper.TangentCanonicalCleanListLower

/-!
# Canonical selector boundary through a distributed tangent flow

This is the star-free replacement for the boundary portion of
`BankPaperCanonicalTangentResidualBridge`.  A distributed earthmover with
the literal canonical residual has the exact factorization boundary needed
by `tangentUpdate_valuation_eq_target`; equal request splitting preserves it.

No clean-list estimate or final collision conclusion occurs in this module.
The only collision-facing asymptotic recorded here is the unconditional
dense-support ceiling `yNat^3 / n -> 0`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Even the deliberately dense distributed support census is at most
`yNat n ^ 2` on the literal canonical prime band.  Consequently its
endpoint-weighted ceiling term is only cubic in `yNat n`. -/
theorem tangentDistributedSupportCount_canonical_le_yNat_sq
    {n W : Nat} :
    tangentDistributedSupportCount
        (BankPaperCanonicalTangentPrime n W) <= yNat n ^ 2 := by
  have hcard : (primeBand n W).card <= yNat n := by
    calc
      (primeBand n W).card <= (Finset.Icc 1 (yNat n)).card := by
        apply Finset.card_le_card
        intro p hp
        exact Finset.mem_Icc.mpr
          ⟨(prime_of_mem_primeBand hp).pos,
            le_yNat_of_mem_primeBand hp⟩
      _ = yNat n := by simp
  unfold tangentDistributedSupportCount
  rw [Fintype.card_coe]
  simpa only [pow_two] using Nat.mul_le_mul hcard hcard

/-- The cubic endpoint ceiling created by the deliberately dense support
still vanishes at the paper cutoff `yNat = floor (n^(2/9))`. -/
theorem tangentDistributed_yNat_cubed_div_self_tendsto_zero :
    Tendsto
      (fun n : Nat => (yNat n : Real) ^ 3 / (n : Real))
      atTop (nhds 0) := by
  have hmodel : Tendsto
      (fun n : Nat => (n : Real) ^ (-(1 / 3 : Real)))
      atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop
      (by norm_num : (0 : Real) < 1 / 3)).comp
        tendsto_natCast_atTop_atTop
  apply squeeze_zero'
  · filter_upwards [] with n
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hyNonneg : 0 <= y n := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have hyFloor : (yNat n : Real) <= y n := Nat.floor_le hyNonneg
    have hyCube : (yNat n : Real) ^ 3 <= y n ^ 3 := by
      exact pow_le_pow_left₀ (by positivity) hyFloor 3
    have hyPow : y n ^ 3 = (n : Real) ^ (2 / 3 : Real) := by
      calc
        y n ^ 3 = ((n : Real) ^ (2 / 9 : Real)) ^ 3 := rfl
        _ = (n : Real) ^ ((2 / 9 : Real) * (3 : Nat)) :=
          (Real.rpow_mul_natCast (Nat.cast_nonneg n)
            (2 / 9 : Real) 3).symm
        _ = (n : Real) ^ (2 / 3 : Real) := by norm_num
    calc
      (yNat n : Real) ^ 3 / (n : Real) <=
          y n ^ 3 / (n : Real) :=
        div_le_div_of_nonneg_right hyCube hnR.le
      _ = (n : Real) ^ ((2 / 3 : Real) - 1) := by
        rw [hyPow, Real.rpow_sub hnR, Real.rpow_one]
      _ = (n : Real) ^ (-(1 / 3 : Real)) := by norm_num
  · exact hmodel

/-- The canonical dense-support ceiling is bounded by the literal cubic
majorant before any limit is taken. -/
theorem tangentDistributedPaperCeilingBudget_canonical_le_yNat_cubic
    (n W : Nat) :
    tangentDistributedPaperCeilingBudget n (yNat n)
        (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W)) <=
      (4 + 2 * (yNat n : Real)) * (yNat n : Real) ^ 2 / (n : Real) := by
  have hsupport :
      (tangentDistributedSupportCount
          (BankPaperCanonicalTangentPrime n W) : Real) <=
        (yNat n : Real) ^ 2 := by
    exact_mod_cast
      (tangentDistributedSupportCount_canonical_le_yNat_sq
        (n := n) (W := W))
  unfold tangentDistributedPaperCeilingBudget
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsupport (by positivity))
    (Nat.cast_nonneg n)

/-- Hence the exact canonical ceiling budget tends to zero for every fixed
head cutoff `W`; no prime-number estimate is used. -/
theorem tangentDistributedPaperCeilingBudget_canonical_tendsto_zero
    (W : Nat) :
    Tendsto
      (fun n : Nat =>
        tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)))
      atTop (nhds 0) := by
  have hsix : Tendsto
      (fun n : Nat => 6 * ((yNat n : Real) ^ 3 / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      tangentDistributed_yNat_cubed_div_self_tendsto_zero.const_mul 6
  apply squeeze_zero'
  · filter_upwards [] with n
    unfold tangentDistributedPaperCeilingBudget
    positivity
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hnR : (0 : Real) < n := by exact_mod_cast hn
    have hyOneNat : 1 <= yNat n := by
      rw [yNat]
      apply Nat.le_floor
      rw [y]
      simpa only [Nat.cast_one] using
        Real.one_le_rpow
          (show (1 : Real) <= (n : Real) by
            exact_mod_cast (show 1 <= n by omega))
          (by norm_num : (0 : Real) <= 2 / 9)
    have hyOne : (1 : Real) <= yNat n := by exact_mod_cast hyOneNat
    have hySqLeCube : (yNat n : Real) ^ 2 <= (yNat n : Real) ^ 3 := by
      have hnonneg : 0 <= (yNat n : Real) ^ 2 := sq_nonneg _
      calc
        (yNat n : Real) ^ 2 = (yNat n : Real) ^ 2 * 1 := by ring
        _ <= (yNat n : Real) ^ 2 * (yNat n : Real) :=
          mul_le_mul_of_nonneg_left hyOne hnonneg
        _ = (yNat n : Real) ^ 3 := by ring
    calc
      tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)) <=
        (4 + 2 * (yNat n : Real)) * (yNat n : Real) ^ 2 /
          (n : Real) :=
        tangentDistributedPaperCeilingBudget_canonical_le_yNat_cubic n W
      _ <= 6 * (yNat n : Real) ^ 3 / (n : Real) := by
        apply div_le_div_of_nonneg_right _ hnR.le
        calc
          (4 + 2 * (yNat n : Real)) * (yNat n : Real) ^ 2 =
              4 * (yNat n : Real) ^ 2 +
                2 * (yNat n : Real) ^ 3 := by ring
          _ <= 4 * (yNat n : Real) ^ 3 +
                2 * (yNat n : Real) ^ 3 := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hySqLeCube (by norm_num))
              (le_refl _)
          _ = 6 * (yNat n : Real) ^ 3 := by ring
      _ = 6 * ((yNat n : Real) ^ 3 / (n : Real)) := by ring
  · exact hsix

/-- The dense canonical support therefore satisfies the paper ceiling
smallness for every fixed positive density. -/
theorem eventually_tangentDistributedPaperCeilingBudget_canonical_le
    (W : Nat) {density : Real} (hdensity : 0 < density) :
    ∀ᶠ n : Nat in atTop,
      tangentDistributedPaperCeilingBudget n (yNat n)
          (tangentDistributedSupportCount
            (BankPaperCanonicalTangentPrime n W)) <=
        density ^ 2 / 96 := by
  exact
    (tangentDistributedPaperCeilingBudget_canonical_tendsto_zero W).eventually
      (eventually_le_nhds (by positivity : (0 : Real) < density ^ 2 / 96))

/-- Canonical-label specialization of the numerical ratio locality theorem.
The only remaining input is the honest geometry statement for the chosen
fixed-ratio cells. -/
theorem bankPaperCanonical_ratioCellEarthmover_positiveEdge_locality
    {n W : Nat} {Band : Type*} [Fintype Band] [DecidableEq Band]
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
        ratioUpper := by
  exact tangentRatioCellEarthmoverFlow_positiveEdge_locality
    lastCell residual bankPaperCanonicalTangentPrimeLabel
      bandOf cellIndex ratioUpper hgeometry hedge

/-! ## Canonical notation for an arbitrary distributed flow -/

abbrev BankPaperCanonicalDistributedTangentSplitRequest
    {n W : Nat}
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (L sigma : Real) :=
  TangentSplitRequest (tangentPositiveFlowEdges flow) L sigma
    (fun edge : BankPaperCanonicalTangentPrime n W ×
        BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2)

def bankPaperCanonicalDistributedTangentRequestSource
    {n W : Nat}
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} :
    BankPaperCanonicalDistributedTangentSplitRequest flow L sigma -> Nat :=
  tangentSplitRequestSource
    (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)

def bankPaperCanonicalDistributedTangentRequestTarget
    {n W : Nat}
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} :
    BankPaperCanonicalDistributedTangentSplitRequest flow L sigma -> Nat :=
  tangentSplitRequestTarget
    (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)

def bankPaperCanonicalDistributedTangentLowerCard
    {n W : Nat}
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma density : Real}
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) : Nat :=
  tangentEffectiveLowerCard density n
    (min
      (bankPaperCanonicalDistributedTangentRequestSource request)
      (bankPaperCanonicalDistributedTangentRequestTarget request))

/-- The selector update for the distributed request family.  The generic
row-preservation and valuation lemmas for `tangentUpdate` apply unchanged. -/
def bankPaperCanonicalDistributedTangentUpdatedSelector
    {n W : Nat}
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (L sigma : Real)
    (multiplier : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma -> Nat)
    (selector : Nat -> Real) : Nat -> Real :=
  tangentUpdate
    (tangentSplitRequests (tangentPositiveFlowEdges flow) L sigma
      (fun edge : BankPaperCanonicalTangentPrime n W ×
          BankPaperCanonicalTangentPrime n W => flow edge.1 edge.2))
    bankPaperCanonicalDistributedTangentRequestSource
    bankPaperCanonicalDistributedTangentRequestTarget
    multiplier tangentSplitRequestWeight selector

/-- Exact canonical request boundary for an arbitrary nonnegative
distributed flow with the literal selector-residual divergence.  This
replaces the star-specific theorem
`bankPaperCanonicalTangentStarSplitRequest_boundary_eq_selectorDeficit` in a
distributed Section 9 assembly. -/
theorem bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
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
            R certificate fixed candidates x q := by
  refine ⟨hdivergence, ?_⟩
  intro q
  calc
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
      ∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
            R certificate fixed candidates x p *
          ((bankPaperCanonicalTangentPrimeLabel p).factorization q : Real) :=
      tangentDistributedSplitRequest_factorizationBoundary_eq_residual
        flow bankPaperCanonicalTangentPrimeLabel
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates x)
        hflow hdivergence L sigma q
    _ = bankPaperCanonicalSelectorValuationDeficit
          R certificate fixed candidates x q :=
      sum_bankPaperCanonicalTangentResidual_mul_factorization_eq_deficit
        R certificate fixed candidates x hsupport q

/-- Selector-facing version of the distributed boundary theorem.  Its
selector input is exactly the upstream rounding predicate; no target traffic
or collision condition is accepted here. -/
theorem bankPaperCanonicalRoundedSelector_distributedBoundary
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) ∧
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
            R certificate fixed candidates selector q := by
  apply bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
    R certificate fixed candidates selector flow hflow hdivergence
  exact
    (bankPaperCanonicalRoundedSelectorTangentInput_selectorState S).2.2.2

/-- Drop-in distributed replacement for
`bankPaperCanonicalSelectorRowIntegral_and_tangentStarBoundary`.  It keeps
the old four-conjunct shape and accepts any nonnegative flow with the exact
residual divergence.  The later ratio-cell specialization supplies the
concrete flow rather than choosing a pivot. -/
theorem bankPaperCanonicalSelectorRowIntegral_and_distributedBoundary
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hrowIntegral : BankPaperCanonicalSelectorRowIntegral
      n candidates selector)
    (hbalance : BankPaperCanonicalPostRoundingPrimeBandBalance (W := W)
      R certificate fixed candidates selector)
    (flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real)
    (hflow : forall source target, 0 <= flow source target)
    (hdivergence : forall p,
      tangentFlowDivergence flow p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates selector)
    (L sigma : Real) :
    BankPaperCanonicalSelectorRowIntegral n candidates selector ∧
      (∑ p : BankPaperCanonicalTangentPrime n W,
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) = 0 ∧
      (forall p : BankPaperCanonicalTangentPrime n W,
        tangentFlowDivergence flow p =
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) ∧
      forall q,
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
            R certificate fixed candidates selector q := by
  have hsum := sum_bankPaperCanonicalTangentResidual_eq_zero
    R certificate fixed candidates selector hbalance
  have hboundary :=
    bankPaperCanonicalDistributedSplitRequest_boundary_eq_selectorDeficit
      R certificate fixed candidates selector flow hflow hdivergence
        hsupport L sigma
  exact ⟨hrowIntegral, hsum, hboundary.1, hboundary.2⟩

/-! ## Selector bounds converted to the literal cell ledgers -/

/-- The prefix ledger already stored in the selector predicate bounds the
canonical cut traffic term by term. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellCutTraffic_le_prefixUpper
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    tangentRatioCellCanonicalCutTraffic lastCell
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex <=
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        prefixUpper band cut := by
  apply tangentRatioCellCanonicalCutTraffic_le_prefixUpper
  exact (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).2.2

/-- More intrinsically, exact band balance and the pointwise residual bound
give the tail-sum cut ledger.  Thus no separate prefix estimate is needed
for this consequence. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellCutTraffic_le_tailPointwiseUpper
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector) :
    tangentRatioCellCanonicalCutTraffic lastCell
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex <=
      ∑ band : Band, ∑ cut ∈ Finset.range (lastCell band),
        tangentRatioCellTailPointwiseUpper
          pointwiseUpper bandOf cellIndex band cut := by
  apply tangentRatioCellCanonicalCutTraffic_le_prefixUpper
  intro band cut
  exact abs_tangentRatioCellPrefixMass_le_tailPointwiseUpper
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    pointwiseUpper bandOf cellIndex
      (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).1
      (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).2.1
      band cut

/-- Canonical label weighting preserves the supplied pointwise residual
bound.  The remaining uniform estimate on the right is the genuine
analytic `C_tan` input. -/
theorem bankPaperCanonicalRoundedSelector_weightedResidual_le_pointwiseUpper
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| <=
      (bankPaperCanonicalTangentPrimeLabel p : Real) * pointwiseUpper p := by
  exact mul_le_mul_of_nonneg_left
    ((bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).2.1 p)
    (Nat.cast_nonneg _)

/-- The weighted literal port load is bounded by the two tail sums divided
by the actual cell cardinality.  No PNT cell lower bound is asserted here. -/
theorem bankPaperCanonicalRoundedSelector_weightedPortLoad_le_pointwisePortUpper
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [DecidableEq Band]
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (p : BankPaperCanonicalTangentPrime n W) :
    (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellUniformPortLoad
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex p <=
      (bankPaperCanonicalTangentPrimeLabel p : Real) *
        tangentRatioCellPointwisePortUpper
          pointwiseUpper bandOf cellIndex p := by
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  exact tangentRatioCellUniformPortLoad_le_pointwisePortUpper
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    pointwiseUpper bandOf cellIndex
      (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).1
      (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).2.1 p

/-! ## The explicit ratio-cell flow, rather than a supplied flow -/

/-- The selector predicate supplies band balance; consecutive occupied cell
geometry supplies the only remaining combinatorial hypotheses.  The flow
itself is the visible formula `tangentRatioCellEarthmoverFlow`. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0) :
    (forall source target,
      0 <= tangentRatioCellEarthmoverFlow lastCell
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex source target) ∧
      (forall p,
        tangentFlowDivergence
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) p =
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) ∧
      TangentFlowRespectsRatioCells bandOf cellIndex
        (tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex) ∧
      tangentFlowTraffic
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) <=
        tangentDistributedTotalTrafficLedger
          (V := BankPaperCanonicalTangentPrime n W)
          (bankPaperCanonicalTangentResidual (W := W)
            R certificate fixed candidates selector)
          (tangentRatioCellCanonicalCutTraffic lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) ∧
      forall p,
        (∑ q, tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex p q) +
          (∑ q, tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex q p) <=
        |bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p| +
          2 * tangentRatioCellUniformPortLoad
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex p := by
  apply tangentRatioCellEarthmoverFlow_spec
    lastCell
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    bandOf cellIndex hindex hoccupied
  exact (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).1

/-- Positive-support incident form used by the split-request census. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellEarthmover_positiveIncident
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (p : BankPaperCanonicalTangentPrime n W) :
    tangentIncidentFlowMass
        (tangentPositiveFlowEdges
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex))
        (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
        (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
        (fun edge => tangentRatioCellEarthmoverFlow lastCell
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex edge.1 edge.2)
        (bankPaperCanonicalTangentPrimeLabel p) <=
      |bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p| +
        2 * tangentRatioCellUniformPortLoad
          (bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector)
          bandOf cellIndex p := by
  apply tangentRatioCellEarthmoverFlow_positiveIncident_le
    lastCell
    (bankPaperCanonicalTangentResidual
      R certificate fixed candidates selector)
    bandOf cellIndex hindex hoccupied
      (bankPaperCanonicalRoundedSelectorTangentInput_residualBounds S).1
    bankPaperCanonicalTangentPrimeLabel
      bankPaperCanonicalTangentPrimeLabel_injective p

/-- The exact factorization boundary now follows with no arbitrary flow
argument: it is furnished by the explicit ratio-cell earthmover above. -/
theorem bankPaperCanonicalRoundedSelector_ratioCellDistributedBoundary
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat)
    {Band : Type*} [Fintype Band] [DecidableEq Band]
    (lastCell : Band -> Nat)
    (bandOf : BankPaperCanonicalTangentPrime n W -> Band)
    (cellIndex : BankPaperCanonicalTangentPrime n W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime n W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (selector : Nat -> Real)
    (S : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates bandOf cellIndex
        pointwiseUpper prefixUpper selector)
    (hindex : forall p, cellIndex p <= lastCell (bandOf p))
    (hoccupied : forall band cell,
      cell <= lastCell band ->
        tangentRatioCellCard bandOf cellIndex band cell ≠ 0)
    (L sigma : Real) :
    (forall p : BankPaperCanonicalTangentPrime n W,
      tangentFlowDivergence
          (tangentRatioCellEarthmoverFlow lastCell
            (bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector)
            bandOf cellIndex) p =
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) ∧
      forall q : Nat,
        (∑ request : TangentSplitRequest
              (tangentPositiveFlowEdges
                (tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex)) L sigma
                (fun edge => tangentRatioCellEarthmoverFlow lastCell
                  (bankPaperCanonicalTangentResidual
                    R certificate fixed candidates selector)
                  bandOf cellIndex edge.1 edge.2),
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
            R certificate fixed candidates selector q := by
  have hspec := bankPaperCanonicalRoundedSelector_ratioCellEarthmover_spec
    R certificate fixed candidates lastCell bandOf cellIndex
      pointwiseUpper prefixUpper selector S hindex hoccupied
  exact bankPaperCanonicalRoundedSelector_distributedBoundary
    R certificate fixed candidates bandOf cellIndex
      pointwiseUpper prefixUpper selector S
      (tangentRatioCellEarthmoverFlow lastCell
        (bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector)
        bandOf cellIndex)
      hspec.1 hspec.2.1 L sigma

end

end Erdos390.WholePaper
