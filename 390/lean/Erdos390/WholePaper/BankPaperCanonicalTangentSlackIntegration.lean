import Erdos390.WholePaper.BankPaperCombinedChargeTerminal
import Erdos390.WholePaper.BankPaperCanonicalGuardedSectionNineContinuation

/-!
# Canonical parameter and endpoint-slack integration for Section 9

This module closes two finite interfaces which occur immediately before the
distributed tangent.

First, it makes one literal choice of `deltaStar` which simultaneously obeys
the complete fixed-factor/precharge budget and the clean-list head-gap
inequality.  Thus the charge terminal and the clean-list theorem no longer
need independently chosen exceptional exponents.

Second, it proves all of the endpoint classification and slack algebra.  A
clean common multiplier puts both endpoints in the guarded broad pool of one
complete rough row, and a nonsmooth such row is active nonexceptional.  On a
nonsmooth row, the displayed absolute bound for the constant correction
density implies the required two-sided selector margin.  On the smooth row,
the protected floor and active ceiling imply the same margin by elementary
addition.

The only construction fact not present in the preceding development is kept
as the explicit proposition
`BankPaperCanonicalGuardedEndpointSlackConstruction`: the actual guarded
selector must agree with the constant broad-row correction off the smooth row,
and its smooth coordinates must have the protected-plus-active decomposition.
No traffic, collision, clean-list cardinality, or final tangent conclusion is
included in that proposition.  The last theorem packages its consequence in
exactly the endpoint-closure and endpoint-slack shape consumed by the
candidate-parametric distributed assembly.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale
open Filter Topology

noncomputable section

/-! ## One exceptional exponent for the charge and tangent arguments -/

/-- The combined admissibility condition used after all fixed choices: the
fixed-factor charge range together with the strict clean-list head-gap
inequality. -/
def IsPaperCombinedTangentDeltaStar
    (c : Real) (W : Nat) (r0 deltaStar : Real) : Prop :=
  IsPaperCombinedChargeDeltaStar c deltaStar ∧
    80 * tangentSelbergCanonicalMainConstant * deltaStar <
      tangentPaperHeadGap W r0

/-- A literal positive exponent small enough for both the combined charge and
the tangent clean-list loss.  The factor `160` leaves half of the fixed head
gap after multiplying by the clean-list constant `80`. -/
def paperCombinedTangentDeltaStar
    (c : Real) (W : Nat) (r0 : Real) : Real :=
  min (paperCombinedChargeDeltaStar c)
    (tangentPaperHeadGap W r0 /
      (160 * tangentSelbergCanonicalMainConstant))

/-- The canonical combined exponent satisfies every charge constraint and
the strict tangent head-gap constraint. -/
theorem paperCombinedTangentDeltaStar_spec
    {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    IsPaperCombinedTangentDeltaStar c W r0
      (paperCombinedTangentDeltaStar c W r0) := by
  have hchargeSpec := paperCombinedChargeDeltaStar_spec hc
  have hmainPos : 0 < tangentSelbergCanonicalMainConstant :=
    tangentSelbergCanonicalMainConstant_pos
  have hgapPos : 0 < tangentPaperHeadGap W r0 :=
    tangentPaperHeadGap_pos W hr0
  have hdenPos :
      0 < 160 * tangentSelbergCanonicalMainConstant := by
    positivity
  have hdeltaPos :
      0 < paperCombinedTangentDeltaStar c W r0 := by
    rw [paperCombinedTangentDeltaStar]
    exact lt_min (paperCombinedChargeDeltaStar_pos hc)
      (div_pos hgapPos hdenPos)
  have hdeltaCharge :
      paperCombinedTangentDeltaStar c W r0 ≤
        paperCombinedChargeDeltaStar c := by
    exact min_le_left _ _
  have hdeltaGap :
      paperCombinedTangentDeltaStar c W r0 ≤
        tangentPaperHeadGap W r0 /
          (160 * tangentSelbergCanonicalMainConstant) := by
    exact min_le_right _ _
  have hdeltaUpper :
      paperCombinedTangentDeltaStar c W r0 < 1 / 18 :=
    hdeltaCharge.trans_lt hchargeSpec.2.1
  have hC0Pos : (0 : Real) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hthetaPos : 0 < paperExceptionalTheta :=
    paperExceptionalTheta_pos
  have hchargePos : 0 < paperExceptionalChargeConstant c :=
    paperExceptionalChargeConstant_pos hcPos
  have hdiv :
      paperCombinedTangentDeltaStar c W r0 / paperExceptionalTheta ≤
        paperCombinedChargeDeltaStar c / paperExceptionalTheta :=
    div_le_div_of_nonneg_right hdeltaCharge hthetaPos.le
  have hchargeBudget :
      paperExceptionalChargeConstant c *
          (paperCombinedTangentDeltaStar c W r0 /
            paperExceptionalTheta) ≤
        (c - C0) / 48 := by
    exact (mul_le_mul_of_nonneg_left hdiv hchargePos.le).trans
      hchargeSpec.2.2
  have hscaled :
      paperCombinedTangentDeltaStar c W r0 *
          (160 * tangentSelbergCanonicalMainConstant) ≤
        tangentPaperHeadGap W r0 :=
    (le_div_iff₀ hdenPos).mp hdeltaGap
  have hmainSmall :
      80 * tangentSelbergCanonicalMainConstant *
          paperCombinedTangentDeltaStar c W r0 <
        tangentPaperHeadGap W r0 := by
    nlinarith
  exact ⟨⟨hdeltaPos, hdeltaUpper, hchargeBudget⟩, hmainSmall⟩

/-- Charge-facing projection of the simultaneous exponent choice. -/
theorem paperCombinedTangentDeltaStar_chargeSpec
    {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    IsPaperCombinedChargeDeltaStar c
      (paperCombinedTangentDeltaStar c W r0) :=
  (paperCombinedTangentDeltaStar_spec W hc hr0).1

/-- Clean-list-facing projection of the simultaneous exponent choice. -/
theorem paperCombinedTangentDeltaStar_cleanListInputs
    {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    0 < paperCombinedTangentDeltaStar c W r0 ∧
      paperCombinedTangentDeltaStar c W r0 < 1 / 18 ∧
      80 * tangentSelbergCanonicalMainConstant *
          paperCombinedTangentDeltaStar c W r0 <
        tangentPaperHeadGap W r0 := by
  have H := paperCombinedTangentDeltaStar_spec W hc hr0
  exact ⟨H.1.1, H.1.2.1, H.2⟩

/-- The combined-charge terminal specialized to the same canonical exponent
which is already small enough for the tangent clean-list head gap. -/
theorem exists_eventually_bankPaperCombinedChargeTerminal_for_tangentChoice
    {c r0 : Real} (W : Nat) (hc : C0 < c) (hr0 : r0 < 2) :
    ∃ depth : Nat, 201 ≤ depth ∧
      ∀ᶠ n : Nat in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          ∃ certificate : GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth),
            centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * bank.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n) ∧
              bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors
                      (paperCombinedTangentDeltaStar c W r0)) ∣
                certificate.prechargedTailTarget ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                      secondOrderScale n +
                    (bank.selectorTailCharge
                      (bank.paperFixedExceptionalFactors
                        (paperCombinedTangentDeltaStar c W r0))).factorization
                          p ≤
                  certificate.prechargedTailTarget.factorization p) ∧
              certificate.selectorTailTarget bank
                    (bank.paperFixedExceptionalFactors
                      (paperCombinedTangentDeltaStar c W r0)) *
                  bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors
                      (paperCombinedTangentDeltaStar c W r0)) =
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) := by
  exact exists_eventually_bankPaperCombinedChargeTerminal_of_deltaStar
    hc (paperCombinedTangentDeltaStar_chargeSpec W hc hr0)

namespace BankPaperRealization

/-! ## The explicit guarded nonsmooth correction -/

/-- Constant correction density on one literal guarded complete-rough row,
with the already proved postcharge quota as target. -/
def roughCanonicalGuardedPostchargeCorrectionDensity
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta L : Real) : Real :=
  bankPaperConstantPoolCorrectionDensity
    (R.roughCanonicalGuardedRow certificate deltaStar K label)
    (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W K label)
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta L)
    (R.roughCanonicalPostchargeRowTarget deltaStar label)

/-- The literal guarded-row constant correction used on a nonsmooth active
row. -/
def roughCanonicalGuardedPostchargeRowCorrectedWeight
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K label : Nat) (alpha beta L : Real)
    (a : Nat) : Real :=
  bankPaperConstantPoolCorrection
    (R.roughCanonicalGuardedRow certificate deltaStar K label)
    (R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
      W K label)
    (roughHeadCompatibleRawWeight W n (upperTailLength c n) K
      alpha beta L)
    (R.roughCanonicalPostchargeRowTarget deltaStar label) a

/-- On the guarded broad pool, the explicit corrected weight is the broad
raw value `beta / L` plus the single rowwise correction density. -/
theorem roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar W K label alpha beta L a =
      beta / L +
        R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
          deltaStar W K label alpha beta L := by
  rw [roughCanonicalGuardedPostchargeRowCorrectedWeight,
    bankPaperConstantPoolCorrection_apply_of_mem ha,
    roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
        certificate deltaStar W K label ha),
    roughCanonicalGuardedPostchargeCorrectionDensity]

/-- The paper's absolute correction-density bounds leave the exact
two-sided tangent margin on every guarded broad coordinate. -/
theorem roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real} {a : Nat}
    (hfloor :
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤
        beta / L)
    (hceiling :
      beta / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤
        1 - sigma / L)
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label) :
    sigma / L ≤
        R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ∧
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
          deltaStar W K label alpha beta L a ≤
        1 - sigma / L := by
  let d := R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
    deltaStar W K label alpha beta L
  have hdLower : -|d| ≤ d := neg_abs_le d
  have hdUpper : d ≤ |d| := le_abs_self d
  rw [R.roughCanonicalGuardedPostchargeRowCorrectedWeight_apply_of_mem ha]
  change sigma / L ≤ beta / L + d ∧
    beta / L + d ≤ 1 - sigma / L
  change sigma / L + |d| ≤ beta / L at hfloor
  change beta / L + |d| ≤ 1 - sigma / L at hceiling
  constructor <;> linarith

/-! ## Clean endpoints lie in the appropriate guarded broad pool -/

/-- Every canonical clean common multiplier puts both numerical endpoints in
the guarded broad correction pool of the multiplier's complete rough row.
If that row is nonsmooth, the integral cutoff test also proves that it is an
active nonexceptional row in the paper's real sense. -/
theorem canonicalDistributedCleanMultiplier_guardedBroadEndpoints
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real}
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) {common : Nat}
    (hcommon : common ∈
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
          (R.paperFixedExceptionalFactors deltaStar)) request) :
    (bankPaperCanonicalDistributedTangentRequestSource request * common ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
            W K (completeRoughLabel (yNat n) common) ∧
      bankPaperCanonicalDistributedTangentRequestTarget request * common ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
            W K (completeRoughLabel (yNat n) common)) ∧
      (completeRoughLabel (yNat n) common ≠ 1 ->
        RoughCanonicalActiveNonexceptionalLabel n deltaStar
          (completeRoughLabel (yNat n) common)) := by
  let s := bankPaperCanonicalDistributedTangentRequestSource request
  let t := bankPaperCanonicalDistributedTangentRequestTarget request
  let label := completeRoughLabel (yNat n) common
  have hsPrime : s.Prime := by
    simpa only [s, bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.1
  have htPrime : t.Prime := by
    simpa only [t, bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      bankPaperCanonicalTangentPrimeLabel_prime request.1.1.2
  have hWs : W < s := by
    simpa only [s, bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      cutoff_lt_of_mem_primeBand request.1.1.1.2
  have hWt : W < t := by
    simpa only [t, bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      cutoff_lt_of_mem_primeBand request.1.1.2.2
  have hsLe : s ≤ yNat n := by
    simpa only [s, bankPaperCanonicalDistributedTangentRequestSource,
      tangentSplitRequestSource, tangentSplitRequestEdge,
      tangentStarEdgeSource] using
      le_yNat_of_mem_primeBand request.1.1.1.2
  have htLe : t ≤ yNat n := by
    simpa only [t, bankPaperCanonicalDistributedTangentRequestTarget,
      tangentSplitRequestTarget, tangentSplitRequestEdge,
      tangentStarEdgeTarget] using
      le_yNat_of_mem_primeBand request.1.1.2.2
  have hclean : common ∈ tangentCleanCommonMultiplierList n K
      (upperTailLength c n) (roughHeadModulus W)
      (tangentPaperExceptionalCutoff deltaStar n) (yNat n)
      (max s t) (min s t) R.tangentPaperDedicatedRows
      (R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar)) := by
    simpa only [tangentSplitCleanMultiplierLists,
      tangentCleanMultiplierLists, s, t] using hcommon
  have hdata := mem_tangentCleanCommonMultiplierList.mp hclean
  have hcommonPos : 0 < common :=
    tangentSplitCleanMultiplier_pos request hcommon
  have hinterval : common ∈ tangentCommonMultiplierInterval n K
      (upperTailLength c n) (max s t) (min s t) :=
    mem_tangentCommonMultiplierInterval.mpr hdata.1
  have hmaxPos : 0 < max s t := hsPrime.pos.trans_le (le_max_left _ _)
  have hminPos : 0 < min s t := lt_min hsPrime.pos htPrime.pos
  have hendpoints := tangentCommonMultiplierInterval_endpoints
    hmaxPos hminPos min_le_max hinterval
  have hsBroad : s * common ∈
      roughBroadLowerBlock n (upperTailLength c n) K := by
    rcases le_total s t with hst | hts
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        min_eq_left hst] using hendpoints.2
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        max_eq_left hts] using hendpoints.1
  have htBroad : t * common ∈
      roughBroadLowerBlock n (upperTailLength c n) K := by
    rcases le_total s t with hst | hts
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        max_eq_right hst] using hendpoints.1
    · simpa only [roughBroadLowerBlock, tangentBroadUpper,
        min_eq_right hts] using hendpoints.2
  have hmaxNot : max s t * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) :=
    hdata.2.2.2.2.1
  have hminNot : min s t * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) :=
    hdata.2.2.2.2.2
  have hsNot : s * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) := by
    rcases le_total s t with hst | hts
    · simpa only [min_eq_left hst] using hminNot
    · simpa only [max_eq_left hts] using hmaxNot
  have htNot : t * common ∉
      R.tangentPaperNumericalGuardSet certificate
        (R.paperFixedExceptionalFactors deltaStar) := by
    rcases le_total s t with hst | hts
    · simpa only [max_eq_right hst] using hmaxNot
    · simpa only [min_eq_right hts] using hminNot
  have hsHead : Nat.Coprime (s * common) (roughHeadModulus W) :=
    (prime_coprime_roughHeadModulus_of_cutoff_lt hsPrime hWs).mul_left
      hdata.2.1
  have htHead : Nat.Coprime (t * common) (roughHeadModulus W) :=
    (prime_coprime_roughHeadModulus_of_cutoff_lt htPrime hWt).mul_left
      hdata.2.1
  have hsLabel : completeRoughLabel (yNat n) (s * common) = label := by
    exact completeRoughLabel_small_left_mul hsPrime.pos hsLe hcommonPos
  have htLabel : completeRoughLabel (yNat n) (t * common) = label := by
    exact completeRoughLabel_small_left_mul htPrime.pos htLe hcommonPos
  have hsPool : s * common ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label := by
    change s * common ∈
      completeRoughRowFiber (yNat n)
          (roughHeadFree W
            (roughBroadLowerBlock n (upperTailLength c n) K)) label \
        R.roughCanonicalGuardSet certificate deltaStar
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_completeRoughRowFiber.mpr
      exact ⟨mem_roughHeadFree.mpr ⟨hsBroad, hsHead⟩, hsLabel⟩
    · simpa only [roughCanonicalGuardSet] using hsNot
  have htPool : t * common ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate deltaStar
        W K label := by
    change t * common ∈
      completeRoughRowFiber (yNat n)
          (roughHeadFree W
            (roughBroadLowerBlock n (upperTailLength c n) K)) label \
        R.roughCanonicalGuardSet certificate deltaStar
    apply Finset.mem_sdiff.mpr
    constructor
    · apply mem_completeRoughRowFiber.mpr
      exact ⟨mem_roughHeadFree.mpr ⟨htBroad, htHead⟩, htLabel⟩
    · simpa only [roughCanonicalGuardSet] using htNot
  have hactive : label ≠ 1 ->
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label := by
    intro hlabel
    exact ⟨hlabel,
      tangentPaperExceptionalCutoff_le_roughScale_implies_real hdata.2.2.1⟩
  simpa only [s, t, label] using ⟨⟨hsPool, htPool⟩, hactive⟩

/-! ## The isolated protected/corrected-selector construction output -/

/-- Exact selector-construction output needed for endpoint slack.

On the smooth broad pool it exposes the frozen protected summand and the
remaining active summand, with their lower floor and upper ceiling.  On every
active nonsmooth row it says that the selector is the explicit constant-pool
correction and records the two numerical density inequalities which leave
`sigma / L` room.  These are precisely the two estimates cited in the paper;
all conversion from them to request-wise tangent slack is proved below. -/
def BankPaperCanonicalGuardedEndpointSlackConstruction
    {c : Real} {depth n : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real) (W K : Nat) (alpha beta L sigma : Real)
    (selector : Nat -> Real) : Prop :=
  (∃ protectedPart active : Nat -> Real,
    ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar W K 1,
      selector a = protectedPart a + active a ∧
        sigma / L ≤ protectedPart a ∧
        0 ≤ active a ∧
        protectedPart a + active a ≤ 1 - sigma / L) ∧
  ∀ label,
    RoughCanonicalActiveNonexceptionalLabel n deltaStar label ->
      sigma / L +
          |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
            deltaStar W K label alpha beta L| ≤ beta / L ∧
        beta / L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar W K label alpha beta L| ≤ 1 - sigma / L ∧
        ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar W K label,
          selector a =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar W K label alpha beta L a

/-- Either branch of the construction proposition gives two-sided slack on
one guarded broad coordinate. -/
theorem guardedEndpointSlackConstruction_twoSidedSlack_of_mem
    {c : Real} {depth n W K label : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar alpha beta L sigma : Real} {selector : Nat -> Real}
    (H : R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar W K alpha beta L sigma selector)
    {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K label)
    (hcase : label = 1 ∨
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label) :
    sigma / L ≤ selector a ∧ selector a ≤ 1 - sigma / L := by
  rcases hcase with hlabel | hactiveLabel
  · subst label
    obtain ⟨protectedPart, active, hsmooth⟩ := H.1
    obtain ⟨hselector, hfloor, hactive, hceiling⟩ := hsmooth a ha
    rw [hselector]
    constructor <;> linarith
  · obtain ⟨hfloor, hceiling, hselector⟩ := H.2 label hactiveLabel
    rw [hselector a ha]
    exact R.roughCanonicalGuardedPostchargeRowCorrectedWeight_twoSidedSlack
      hfloor hceiling ha

/-! ## Adapter to the candidate-parametric distributed tangent -/

/-- The isolated construction output supplies the exact request-wise
two-sided slack premise of the distributed candidate-set assembly. -/
theorem guardedEndpointSlackConstruction_cleanMultiplierSlack
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} (selector : Nat -> Real)
    (H : R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar W K alpha beta L sigma selector)
    (request : BankPaperCanonicalDistributedTangentSplitRequest
      flow L sigma) (common : Nat)
    (hcommon : common ∈
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
          (R.paperFixedExceptionalFactors deltaStar)) request) :
    (sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            common) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestSource request *
            common) ≤ 1 - sigma / L) ∧
      (sigma / L ≤ selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            common) ∧
        selector
          (bankPaperCanonicalDistributedTangentRequestTarget request *
            common) ≤ 1 - sigma / L) := by
  have hendpoints := R.canonicalDistributedCleanMultiplier_guardedBroadEndpoints
    certificate deltaStar request hcommon
  let label := completeRoughLabel (yNat n) common
  have hcase : label = 1 ∨
      RoughCanonicalActiveNonexceptionalLabel n deltaStar label := by
    by_cases hlabel : label = 1
    · exact Or.inl hlabel
    · exact Or.inr (hendpoints.2 (by simpa only [label] using hlabel))
  constructor
  · apply R.guardedEndpointSlackConstruction_twoSidedSlack_of_mem H
      (label := label)
    · simpa only [label] using hendpoints.1.1
    · exact hcase
  · apply R.guardedEndpointSlackConstruction_twoSidedSlack_of_mem H
      (label := label)
    · simpa only [label] using hendpoints.1.2
    · exact hcase

/-- Ready-to-use pair of endpoint inputs for
`exists_canonicalDistributedSectionNinePostTangentOutput_of_paperBudgets_on_candidates`:
clean endpoints remain in the literal guarded candidate set, and every
allowed clean multiplier has the required two-sided selector slack. -/
theorem guardedEndpointSlackConstruction_candidateSetEndpointInputs
    {c : Real} {depth n W K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    {flow : BankPaperCanonicalTangentPrime n W ->
      BankPaperCanonicalTangentPrime n W -> Real}
    {L sigma : Real} (selector : Nat -> Real)
    (hKh : K * upperTailLength c n ≤ n)
    (H : R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar W K alpha beta L sigma selector) :
    (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
        flow L sigma,
      ∀ {common : Nat},
        common ∈
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
                (R.paperFixedExceptionalFactors deltaStar)) request ->
          bankPaperCanonicalDistributedTangentRequestSource request * common ∈
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
            bankPaperCanonicalDistributedTangentRequestTarget request *
                common ∈
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K) ∧
      (∀ request : BankPaperCanonicalDistributedTangentSplitRequest
          flow L sigma,
        ∀ common : Nat,
          common ∈
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
                  (R.paperFixedExceptionalFactors deltaStar)) request ->
            (sigma / L ≤ selector
                  (bankPaperCanonicalDistributedTangentRequestSource request *
                    common) ∧
              selector
                  (bankPaperCanonicalDistributedTangentRequestSource request *
                    common) ≤ 1 - sigma / L) ∧
            (sigma / L ≤ selector
                  (bankPaperCanonicalDistributedTangentRequestTarget request *
                    common) ∧
              selector
                  (bankPaperCanonicalDistributedTangentRequestTarget request *
                    common) ≤ 1 - sigma / L)) := by
  constructor
  · intro request common hcommon
    exact R.roughCanonicalGuardedCandidateSet_cleanEndpoints certificate
      deltaStar hKh request hcommon
  · intro request common hcommon
    exact R.guardedEndpointSlackConstruction_cleanMultiplierSlack
      certificate deltaStar alpha beta selector H request common hcommon

end BankPaperRealization

end

end Erdos390.WholePaper
