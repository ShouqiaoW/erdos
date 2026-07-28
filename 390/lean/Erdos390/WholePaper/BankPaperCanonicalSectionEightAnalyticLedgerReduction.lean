import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic
import Erdos390.WholePaper.BankPaperCanonicalGuardCapacityReduction
import Erdos390.WholePaper.BankPaperAnchorChangeBudget

/-!
# Reduction of the remaining Section 8 analytic ledger

The analytic quota/height bridge deliberately leaves two estimates in
`BankPaperCanonicalSectionEightAnalyticLedger`.  This file separates all
finite and asymptotic algebra around those estimates from the genuinely
missing paper inputs.

For the active mass, the literal intermediate object is the constant
`betaAct / L` layer on the guarded label-one broad pool.  Its difference
from the raw layer is exactly the same constant times the number of deleted
coordinates.  The natural smooth-guard census envelope

`yNat^2 + bankPaperAnchorMarkerBudget`

is already `o(secondOrderScale)`.  Thus only a census bound for the literal
deleted pool and the post-correction identification with the actual
`qTilde` remain.

For the height, the paper first proves the three baseline relations

* `m0 + qTilde = h + O(N/L)`,
* `Lambda0 = m0 L + O(N)`,
* `logY = h L + O(N)`.

Nearest-integer initialization transfers the first relation from `qTilde`
to `q0`; the displayed identity for `A0` then proves `A0 = O(N)`.  Hence the
height half of the old black-box ledger is reduced exactly to those three
named source estimates.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## The literal guarded smooth base -/

/-- The raw label-one base coordinates removed by the exhaustive numerical
guard.  The intersection order agrees with `Finset.card_sdiff`. -/
def bankPaperCanonicalSmoothBaseGuardDeletionPool
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) : Finset Nat :=
  R.roughCanonicalGuardSet certificate deltaStar ∩
    bankPaperCanonicalRawSmoothBasePool W n h K

/-- Exact constant-layer mass on the guarded label-one broad pool. -/
def bankPaperCanonicalGuardedSmoothBaseMass
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real) : Real :=
  betaAct / L n *
    ((R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar W K 1).card : Real)

/-- Fixed exceptional factors and donors are in the upper tail, while every
precharged base or alternate state has a nontrivial marker label.  Therefore
only central anchors can delete a coordinate from the label-one raw pool. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
        deltaStar W K ⊆ certificate.anchors := by
  classical
  intro a ha
  have haData := Finset.mem_inter.mp ha
  have haRawRow : a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) 1 :=
    roughCanonicalBroadCorrectionPool_subset_rawRow
      W n h K (yNat n) 1 haData.2
  have haDeleted : a ∈
      R.roughCanonicalGuardDeletedRow certificate deltaStar K 1 :=
    Finset.mem_inter.mpr ⟨haRawRow, haData.1⟩
  have haSupport :=
    R.roughCanonicalGuardDeletedRow_subset_anchors_union_bankStates
      certificate deltaStar K 1 haDeleted
  rcases Finset.mem_union.mp haSupport with haBefore | haAlternate
  · rcases Finset.mem_union.mp haBefore with haAnchor | haBase
    · exact haAnchor
    · rw [BankPaperRealization.prechargeBaseState, indexedPathState,
        Finset.mem_image] at haBase
      obtain ⟨request, _hrequest, rfl⟩ := haBase
      have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
      rw [R.prechargeBase_completeRoughLabel_eq_marker] at hlabel
      have hhigh := R.yNat_lt_paperMarker request
      have hy := R.six_le_yNat
      omega
  · rw [BankPaperRealization.prechargeAlternateState, indexedPathState,
      Finset.mem_image] at haAlternate
    obtain ⟨request, _hrequest, rfl⟩ := haAlternate
    have hlabel := (mem_completeRoughRowFiber.mp haRawRow).2
    rw [R.prechargeAlternate_completeRoughLabel_eq_marker] at hlabel
    have hhigh := R.yNat_lt_paperMarker request
    have hy := R.six_le_yNat
    omega

/-- Cardinal form of the exact support reduction: the only smooth guard
census still needed is a census of guarded central anchors in the raw
label-one base pool. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchors
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    (bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
      deltaStar W K).card <= certificate.anchors.card :=
  Finset.card_le_card
    (bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
      R certificate deltaStar W K)

/-- Retaining the original raw-pool membership sharpens the preceding
support theorem to the exact smooth-anchor intersection. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchorIntersection
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
        deltaStar W K ⊆
      certificate.anchors ∩
        bankPaperCanonicalRawSmoothBasePool W n h K := by
  intro a ha
  exact Finset.mem_inter.mpr
    ⟨bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchors
        R certificate deltaStar W K ha,
      (Finset.mem_inter.mp ha).2⟩

/-- Hence the missing guard count involves only central anchors which
actually lie in the raw head-free smooth base pool. -/
theorem bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) :
    (bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
      deltaStar W K).card <=
        (certificate.anchors ∩
          bankPaperCanonicalRawSmoothBasePool W n h K).card :=
  Finset.card_le_card
    (bankPaperCanonicalSmoothBaseGuardDeletionPool_subset_anchorIntersection
      R certificate deltaStar W K)

/-! ### The smooth central-anchor census -/

/-- Promoted residual anchors whose base prime is at most the complete-rough
cutoff.  These are the only central anchors which can have label one. -/
def bankPaperCanonicalSmoothResidualAnchorPool
    (n X y : Nat) : Finset Nat :=
  ((residualCentralPrimes n X).filter fun p => p <= y).image
    (promotedCentralFactor n)

/-- Every guarded central anchor in the raw label-one base pool is a promoted
residual anchor whose base prime is at most `yNat`.  Routed large anchors
retain their marker prime in the complete rough label and hence cannot occur
in this row. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_subset_smoothResidual
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (W K : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    certificate.anchors ∩ bankPaperCanonicalRawSmoothBasePool W n h K ⊆
      bankPaperCanonicalSmoothResidualAnchorPool n
        (centralAnchorCutoff depth n) (yNat n) := by
  intro a ha
  have hn : 0 < n :=
    (centralAnchorCutoffThreshold_pos depth).trans_le hnCutoff
  have haRawRow : a ∈ completeRoughRowFiber (yNat n)
      (roughRawCandidateSet n h K) 1 :=
    roughCanonicalBroadCorrectionPool_subset_rawRow
      W n h K (yNat n) 1 (Finset.mem_inter.mp ha).2
  have haLabel : completeRoughLabel (yNat n) a = 1 :=
    (mem_completeRoughRowFiber.mp haRawRow).2
  have haAnchor : a ∈ fullCentralAnchors n
      (centralAnchorCutoff depth n) certificate.q := by
    simpa only [certificate.anchors_eq] using (Finset.mem_inter.mp ha).1
  rw [fullCentralAnchors] at haAnchor
  rcases Finset.mem_union.mp haAnchor with haPromoted | haLarge
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp haPromoted
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_filter.mpr ⟨hp, ?_⟩, rfl⟩
    by_contra hpNotLe
    have hyp : yNat n < p := Nat.lt_of_not_ge hpNotLe
    have hpPrime := residualCentralPrimes_prime hp
    have hpDvdFactor : p ∣ promotedCentralFactor n p := by
      unfold promotedCentralFactor promotedBlock centralPrimeBlock
      exact dvd_mul_of_dvd_right
        (dvd_pow_self p (residualCentralPrimes_exponent_pos hp).ne') _
    have hpDvdLabel : p ∣
        completeRoughLabel (yNat n) (promotedCentralFactor n p) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hpPrime hyp
        (Nat.zero_lt_of_lt (promotedCentralFactor_gt hn)).ne'
        hpDvdFactor
    rw [haLabel] at hpDvdLabel
    exact hpPrime.not_dvd_one hpDvdLabel
  · obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp haLarge
    have hPPrime := largeCentralPrimes_prime hP
    have hPHigh : yNat n < P :=
      hyCutoff.trans (largeCentralPrimes_gt hP)
    have hPPos : 0 < largeCentralAnchor certificate.q P :=
      Nat.zero_lt_of_lt
        (Finset.mem_Ioc.mp
          (largeCentralAnchor_mem_centralInterval
            certificate.isCofactorChoice hP)).1
    have hPDvdLabel : P ∣
        completeRoughLabel (yNat n)
          (largeCentralAnchor certificate.q P) :=
      prime_dvd_completeRoughLabel_of_cutoff_lt hPPrime hPHigh
        hPPos.ne' (dvd_mul_right P (certificate.q P))
    rw [haLabel] at hPDvdLabel
    exact (hPPrime.not_dvd_one hPDvdLabel).elim

/-- The smooth residual-anchor pool has at most `y` elements. -/
theorem bankPaperCanonicalSmoothResidualAnchorPool_card_le
    (n X y : Nat) :
    (bankPaperCanonicalSmoothResidualAnchorPool n X y).card <= y := by
  let primes := (residualCentralPrimes n X).filter fun p => p <= y
  have hsubset : primes ⊆ Finset.Icc 1 y := by
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    exact Finset.mem_Icc.mpr
      ⟨(residualCentralPrimes_prime hpData.1).pos, hpData.2⟩
  calc
    (bankPaperCanonicalSmoothResidualAnchorPool n X y).card <=
        primes.card := by
      exact Finset.card_image_le
    _ <= (Finset.Icc 1 y).card := Finset.card_le_card hsubset
    _ <= y := by
      rw [Nat.card_Icc]
      omega

/-- Pointwise paper-sized bound for the relevant smooth guarded anchors. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (W K : Nat)
    (hnCutoff : centralAnchorCutoffThreshold depth <= n)
    (hyCutoff : yNat n < centralAnchorCutoff depth n) :
    (certificate.anchors ∩
      bankPaperCanonicalRawSmoothBasePool W n h K).card <= yNat n :=
  (Finset.card_le_card
    (guardedCentralAnchors_inter_rawSmoothBasePool_subset_smoothResidual
      certificate W K hnCutoff hyCutoff)).trans
    (bankPaperCanonicalSmoothResidualAnchorPool_card_le n
      (centralAnchorCutoff depth n) (yNat n))

/-- Deleting the numerical guards changes the raw active base mass by
exactly `betaAct / L` times the literal deletion cardinality. -/
theorem bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
    {c : Real} {depth n h : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n (upperEndpoint n h))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (deltaStar : Real) (W K : Nat) (betaAct : Real) :
    bankPaperCanonicalRawSmoothBaseMass W n h K betaAct -
        bankPaperCanonicalGuardedSmoothBaseMass R certificate
          deltaStar W K betaAct =
      betaAct / L n *
        ((bankPaperCanonicalSmoothBaseGuardDeletionPool R certificate
          deltaStar W K).card : Real) := by
  let rawPool : Finset Nat :=
    bankPaperCanonicalRawSmoothBasePool W n h K
  let guardSet : Finset Nat :=
    R.roughCanonicalGuardSet certificate deltaStar
  change
    betaAct / L n * (rawPool.card : Real) -
        betaAct / L n * ((rawPool \ guardSet).card : Real) =
      betaAct / L n * ((guardSet ∩ rawPool).card : Real)
  have hcard :
      (guardSet ∩ rawPool).card <= rawPool.card :=
    Finset.card_le_card Finset.inter_subset_right
  have hcardDiff :
      ((rawPool \ guardSet).card : Real) =
        (rawPool.card : Real) - ((guardSet ∩ rawPool).card : Real) := by
    rw [Finset.card_sdiff, Nat.cast_sub hcard]
  rw [hcardDiff, mul_sub]
  ring

/-! ## Honest tail families and their total asymptotic extensions -/

/-- One realized bank together with its correctly indexed guarded anchor
certificate. -/
def BankPaperCanonicalGuardedTailFiber
    (c : Real) (depth n : Nat) : Type :=
  Σ R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)),
    GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)

set_option maxHeartbeats 800000 in
/-- A coherent choice of realized banks and guarded anchor certificates only
on a genuine tail `N ≤ n`.  Unlike a family indexed by every natural number,
this interface is inhabited by the existing eventual construction and does
not request the impossible realization at `n = 0`. -/
structure BankPaperCanonicalGuardedTailFamily
    (c : Real) (depth N : Nat) where
  fiber : ∀ n, N ≤ n →
    BankPaperCanonicalGuardedTailFiber c depth n

/-- The realized bank in an honest tail-family fiber. -/
def BankPaperCanonicalGuardedTailFamily.realization
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) (hn : N ≤ n) :
    BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)) :=
  (BankPaperCanonicalGuardedTailFamily.fiber F n hn).1

/-- The guarded anchor certificate paired with the realized tail bank. -/
def BankPaperCanonicalGuardedTailFamily.certificate
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) (hn : N ≤ n) :
    let R := BankPaperCanonicalGuardedTailFamily.realization F n hn
    GuardedCentralAnchorCertificate c depth n
      (BankPaperRealization.anchorGuardLeftCore R)
      (BankPaperRealization.anchorGuardRightCore R)
      (BankPaperRealization.centralChangedMarkers R depth) :=
  (BankPaperCanonicalGuardedTailFamily.fiber F n hn).2

/-- Total guarded-base extension of a tail family.  Below the tail threshold
it equals the raw base, so the raw-to-guarded deletion identity remains exact
there with zero deleted coordinates. -/
def BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (W K : Nat) (betaAct deltaStar : Real) (n : Nat) : Real :=
  if hn : N ≤ n then
    bankPaperCanonicalGuardedSmoothBaseMass
      (BankPaperCanonicalGuardedTailFamily.realization F n hn)
      (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
        deltaStar W K betaAct
  else
    bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct

/-- Total deletion-cardinality extension of a tail family, with the missing
finite prefix set to zero. -/
def BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (W K : Nat) (deltaStar : Real) (n : Nat) : Real :=
  if hn : N ≤ n then
    ((bankPaperCanonicalSmoothBaseGuardDeletionPool
      (BankPaperCanonicalGuardedTailFamily.realization F n hn)
      (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
        deltaStar W K).card : Real)
  else
    0

/-- Total relevant-anchor-cardinality extension of a tail family, again with
zero on the finite prefix where no realization is requested. -/
def BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (W K : Nat) (n : Nat) : Real :=
  if hn : N ≤ n then
    (((BankPaperCanonicalGuardedTailFamily.certificate F n hn).anchors ∩
      bankPaperCanonicalRawSmoothBasePool W n
        (upperTailLength c n) K).card : Real)
  else
    0

/-! ## The already-small guard census envelope -/

/-- The paper-sized envelope for smooth guard deletions.  The square allows
both the promoted smooth-anchor census and all precharged bank states to be
absorbed without encoding either family into an asymptotic definition. -/
def bankPaperCanonicalSmoothGuardCensusEnvelope (n : Nat) : Real :=
  (yNat n : Real) ^ 2 + (bankPaperAnchorMarkerBudget n : Real)

/-- The census envelope is pointwise nonnegative. -/
theorem bankPaperCanonicalSmoothGuardCensusEnvelope_nonneg (n : Nat) :
    0 <= bankPaperCanonicalSmoothGuardCensusEnvelope n := by
  unfold bankPaperCanonicalSmoothGuardCensusEnvelope
  positivity

/-- The moving square cutoff is little-o of the central paper scale. -/
theorem bankPaperCanonical_yNat_sq_isLittleO_secondOrderScale :
    (fun n : Nat => (yNat n : Real) ^ 2) =o[atTop]
      secondOrderScale := by
  have hzero : ∀ᶠ n : Nat in atTop,
      secondOrderScale n = 0 -> (yNat n : Real) ^ 2 = 0 := by
    filter_upwards [eventually_secondOrderScale_pos] with n hscale hzero
    exact (hscale.ne' hzero).elim
  apply (isLittleO_iff_tendsto' hzero).mpr
  exact yNat_sq_div_secondOrderScale_tendsto_zero

/-- Consequently the complete smooth-guard census envelope is negligible. -/
theorem bankPaperCanonicalSmoothGuardCensusEnvelope_isLittleO :
    bankPaperCanonicalSmoothGuardCensusEnvelope =o[atTop]
      secondOrderScale := by
  have hsum := bankPaperCanonical_yNat_sq_isLittleO_secondOrderScale.add
    bankPaperAnchorMarkerBudget_isLittleO_secondOrderScale
  exact hsum.congr_left fun n => by
    rfl

/-- Uniformly over every honest tail family of guarded certificates, the
total relevant-anchor extension is `O` of the census envelope.  This closes
the finite guard-deletion census with no new analytic input and no
realization request on the finite prefix. -/
theorem guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
    {c : Real} {N : Nat} (depth W K : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    F.extendedAnchorIntersectionCard W K =O[atTop]
      bankPaperCanonicalSmoothGuardCensusEnvelope := by
  apply IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop N, eventually_ge_atTop
      (centralAnchorCutoffThreshold depth),
    eventually_yNat_lt_centralAnchorCutoff depth,
    eventually_bankBottom_six_le_yNat] with
      n hnTail hnCutoff hyCutoff hySix
  rw [BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard,
    dif_pos hnTail, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    Real.norm_eq_abs,
    abs_of_nonneg (bankPaperCanonicalSmoothGuardCensusEnvelope_nonneg n),
    one_mul]
  have hcard :
      (((BankPaperCanonicalGuardedTailFamily.certificate
          F n hnTail).anchors ∩
        bankPaperCanonicalRawSmoothBasePool W n
          (upperTailLength c n) K).card : Real) <= (yNat n : Real) := by
    exact_mod_cast
      guardedCentralAnchors_inter_rawSmoothBasePool_card_le_yNat
        (BankPaperCanonicalGuardedTailFamily.certificate F n hnTail)
          W K hnCutoff hyCutoff
  have hyOne : (1 : Real) <= yNat n := by
    exact_mod_cast (show 1 <= yNat n by omega)
  have hyNonneg : (0 : Real) <= yNat n := by positivity
  have hySq : (yNat n : Real) <= (yNat n : Real) ^ 2 := by
    calc
      (yNat n : Real) = (yNat n : Real) * 1 := by ring
      _ <= (yNat n : Real) * (yNat n : Real) :=
        mul_le_mul_of_nonneg_left hyOne hyNonneg
      _ = (yNat n : Real) ^ 2 := by ring
  exact hcard.trans <| hySq.trans <|
    le_add_of_nonneg_right (by positivity)

/-- The smallest finite guard-census input still needed for a chosen family
of actual banks and guarded certificates. -/
def BankPaperCanonicalSmoothGuardDeletionCensus
    (deletedCard : Nat -> Real) : Prop :=
  deletedCard =O[atTop] bankPaperCanonicalSmoothGuardCensusEnvelope

/-- Every family satisfying the named finite census is automatically
little-o of the paper scale. -/
theorem bankPaperCanonicalSmoothGuardDeletionCard_isLittleO
    (deletedCard : Nat -> Real)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    deletedCard =o[atTop] secondOrderScale :=
  Hcensus.trans_isLittleO
    bankPaperCanonicalSmoothGuardCensusEnvelope_isLittleO

/-- For fixed `betaAct`, the coefficient `betaAct / L` is uniformly
bounded. -/
theorem bankPaperCanonical_beta_div_L_isBigO_one (betaAct : Real) :
    (fun n : Nat => betaAct / L n) =O[atTop]
      (fun _n : Nat => (1 : Real)) := by
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLone : ∀ᶠ n : Nat in atTop, 1 <= L n :=
    hLTop.eventually (eventually_ge_atTop (1 : Real))
  apply IsBigO.of_bound ‖betaAct‖
  filter_upwards [hLone] with n hn
  have hnormL : 1 <= ‖L n‖ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hn)]
    exact hn
  rw [norm_div, norm_one, mul_one]
  exact div_le_self (norm_nonneg betaAct) hnormL

/-- A census-sized family of deleted coordinates has negligible weighted
mass under the literal `betaAct / L` base layer. -/
theorem bankPaperCanonicalSmoothGuardDeletionMass_isLittleO
    (betaAct : Real) (deletedCard : Nat -> Real)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    (fun n => betaAct / L n * deletedCard n) =o[atTop]
      secondOrderScale := by
  have hweighted :=
    (bankPaperCanonical_beta_div_L_isBigO_one betaAct).mul_isLittleO
      (bankPaperCanonicalSmoothGuardDeletionCard_isLittleO
        deletedCard Hcensus)
  simpa only [one_mul] using hweighted

/-- The post-guard correction estimate which is not present in the current
rough-selector API: after literal guard deletion, all precharge and signed
row-correction changes alter the active label-one mass by `o(N)`. -/
def BankPaperCanonicalGuardedSmoothCorrectionEstimate
    (guardedBase qTilde : Nat -> Real) : Prop :=
  (fun n => guardedBase n - qTilde n) =o[atTop]
    secondOrderScale

/-- Exact identities plus the finite deletion census transfer the raw base
to the explicit guarded base at little-o cost. -/
theorem bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
    (betaAct : Real) (rawBase guardedBase deletedCard : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard) :
    (fun n => rawBase n - guardedBase n) =o[atTop]
      secondOrderScale := by
  exact (bankPaperCanonicalSmoothGuardDeletionMass_isLittleO
    betaAct deletedCard Hcensus).congr_left fun n =>
      (hidentity n).symm

/-- The first field of `BankPaperCanonicalSectionEightAnalyticLedger`
follows from the literal raw-to-guarded identity, the finite census, and the
single named guarded-to-actual correction estimate. -/
theorem bankPaperCanonicalRawSmoothBase_sub_qTilde_isLittleO_of_guardedReduction
    (betaAct : Real)
    (rawBase guardedBase qTilde deletedCard : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hcensus : BankPaperCanonicalSmoothGuardDeletionCensus deletedCard)
    (Hcorrection : BankPaperCanonicalGuardedSmoothCorrectionEstimate
      guardedBase qTilde) :
    (fun n => rawBase n - qTilde n) =o[atTop]
      secondOrderScale := by
  have hguard :=
    bankPaperCanonicalRawSmoothBase_sub_guarded_isLittleO_of_census
      betaAct rawBase guardedBase deletedCard hidentity Hcensus
  exact (hguard.add Hcorrection).congr_left fun n => by ring

/-! ## Reduction of the frozen height defect -/

/-- The three source estimates displayed immediately before the definition
of `A0` in Section 8.  Here `m0` is the total frozen mass, distinct from the
smooth-row frozen mass `mFrozen` used in the nearest-integer quota. -/
def BankPaperCanonicalFrozenBaselineSourceLedger
    (h logY Lambda0 m0 qTilde : Nat -> Real) : Prop :=
  (fun n => m0 n + qTilde n - h n) =O[atTop]
      (fun n => secondOrderScale n / L n) ∧
    (fun n => Lambda0 n - m0 n * L n) =O[atTop]
      secondOrderScale ∧
    (fun n => logY n - h n * L n) =O[atTop]
      secondOrderScale

/-- Constants are `O(N/L)` because the logarithmically smaller scale tends
to infinity. -/
theorem bankPaperCanonical_one_isBigO_secondOrderScale_div_L :
    (fun _n : Nat => (1 : Real)) =O[atTop]
      (fun n => secondOrderScale n / L n) := by
  apply IsBigO.of_bound 1
  have hlarge := secondOrderScale_div_L_tendsto_atTop.eventually
    (eventually_ge_atTop (1 : Real))
  filter_upwards [hlarge] with n hn
  have hnonneg : 0 <= secondOrderScale n / L n :=
    zero_le_one.trans hn
  simpa only [norm_one, one_mul, Real.norm_eq_abs,
    abs_of_nonneg hnonneg] using hn

/-- The nearest-integer change from `qTilde` to `q0` preserves the baseline
mass estimate at the smaller `N/L` scale. -/
theorem bankPaperCanonicalSmoothQ0_baselineMassError_isBigO
    (h m0 mFrozen qTilde : Nat -> Real)
    (Hmass : (fun n => m0 n + qTilde n - h n) =O[atTop]
      (fun n => secondOrderScale n / L n)) :
    (fun n => m0 n +
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - h n)
      =O[atTop] (fun n => secondOrderScale n / L n) := by
  have hroundOne :
      (fun n => bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
        qTilde n) =O[atTop] (fun _n : Nat => (1 : Real)) := by
    apply IsBigO.of_bound (1 / 2)
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs, abs_one, mul_one] using
      bankPaperCanonicalSmoothQ0Family_abs_sub_qTilde_le
        mFrozen qTilde n
  have hround := hroundOne.trans
    bankPaperCanonical_one_isBigO_secondOrderScale_div_L
  exact (Hmass.add hround).congr_left fun n => by ring

/-- Multiplying the baseline mass error `O(N/L)` by `L` gives `O(N)`. -/
theorem bankPaperCanonicalSmoothQ0_baselineMassError_mul_L_isBigO
    (h m0 mFrozen qTilde : Nat -> Real)
    (Hmass : (fun n => m0 n + qTilde n - h n) =O[atTop]
      (fun n => secondOrderScale n / L n)) :
    (fun n => (m0 n +
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n - h n) * L n)
      =O[atTop] secondOrderScale := by
  have hmassQ0 := bankPaperCanonicalSmoothQ0_baselineMassError_isBigO
    h m0 mFrozen qTilde Hmass
  have hraw := hmassQ0.mul (isBigO_refl L atTop)
  apply hraw.congr' EventuallyEq.rfl
  filter_upwards [eventually_gt_atTop 1] with n hn
  exact div_mul_cancel₀ (secondOrderScale n) (L_pos hn).ne'

/-- The paper's three baseline estimates imply the literal frozen height
defect bound, with all signs exposed by the exact algebraic identity. -/
theorem bankPaperCanonicalSmoothA0Family_isBigO_of_baselineSource
    (h logY Lambda0 m0 mFrozen qTilde : Nat -> Real)
    (Hsource : BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde) :
    bankPaperCanonicalSmoothA0Family logY Lambda0 mFrozen qTilde
      =O[atTop] secondOrderScale := by
  have hmassL :=
    bankPaperCanonicalSmoothQ0_baselineMassError_mul_L_isBigO
      h m0 mFrozen qTilde Hsource.1
  have hsum := (Hsource.2.2.sub Hsource.2.1).sub hmassL
  exact hsum.congr_left fun n => by
    unfold bankPaperCanonicalSmoothA0Family
    unfold bankPaperCanonicalSmoothFrozenHeightDefect
    ring

/-! ## The complete reduced source ledger -/

/-- All estimates still absent after the finite and asymptotic reductions
in this file.  The raw-to-guarded identity is deliberately not a field: for
the literal pools it is the unconditional theorem
`bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion`. -/
def BankPaperCanonicalSectionEightAnalyticSourceLedger
    (guardedBase qTilde deletedCard h logY Lambda0 m0 : Nat -> Real) : Prop :=
  BankPaperCanonicalSmoothGuardDeletionCensus deletedCard ∧
    BankPaperCanonicalGuardedSmoothCorrectionEstimate guardedBase qTilde ∧
    BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde

/-- Main reduction theorem: the smaller paper-facing source ledger, together
with the already-proved raw-to-guarded finite identity, constructs the old
two-field Section 8 analytic ledger. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_sourceLedger
    (betaAct : Real)
    (rawBase guardedBase qTilde deletedCard : Nat -> Real)
    (h logY Lambda0 m0 mFrozen : Nat -> Real)
    (hidentity : forall n,
      rawBase n - guardedBase n =
        betaAct / L n * deletedCard n)
    (Hsource : BankPaperCanonicalSectionEightAnalyticSourceLedger
      guardedBase qTilde deletedCard h logY Lambda0 m0) :
    BankPaperCanonicalSectionEightAnalyticLedger rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  constructor
  · exact
      bankPaperCanonicalRawSmoothBase_sub_qTilde_isLittleO_of_guardedReduction
        betaAct rawBase guardedBase qTilde deletedCard hidentity
          Hsource.1 Hsource.2.1
  · exact bankPaperCanonicalSmoothA0Family_isBigO_of_baselineSource
      h logY Lambda0 m0 mFrozen qTilde Hsource.2.2

/-- Literal-bank specialization of the main reduction for an honest tail
family.  The chosen total extensions make the raw-to-guarded identity exact
both on the realized tail and on its synthetic finite prefix, so every field
of `Hsource` is a genuine asymptotic source estimate. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_literalGuardedSource
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (qTilde h logY Lambda0 m0 mFrozen : Nat -> Real)
    (Hsource : BankPaperCanonicalSectionEightAnalyticSourceLedger
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      qTilde
      (F.extendedSmoothBaseGuardDeletionCard W K deltaStar)
      h logY Lambda0 m0) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_sourceLedger
    betaAct
    (fun n => bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct)
    (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
    qTilde
    (F.extendedSmoothBaseGuardDeletionCard W K deltaStar)
    h logY Lambda0 m0 mFrozen
  · intro n
    by_cases hn : N ≤ n
    · simpa only [
          BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
          BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
          dif_pos hn] using
        bankPaperCanonicalRawSmoothBaseMass_sub_guarded_eq_guardDeletion
          (BankPaperCanonicalGuardedTailFamily.realization F n hn)
          (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
            deltaStar W K betaAct
    · simp only [
        BankPaperCanonicalGuardedTailFamily.extendedGuardedSmoothBaseMass,
        BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
        dif_neg hn, sub_self, mul_zero]
  · exact Hsource

/-- Fully reduced tail-family specialization.  The finite support theorem
above turns an `O(yNat^2 + markerBudget)` census for the relevant smooth
anchors into the required deletion census.  Thus no precharge, donor, fixed-
exceptional, or alternate-state cardinality remains in the source data. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_literalAnchorSource
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (qTilde h logY Lambda0 m0 mFrozen : Nat -> Real)
    (Hanchors :
      F.extendedAnchorIntersectionCard W K =O[atTop]
        bankPaperCanonicalSmoothGuardCensusEnvelope)
    (Hcorrection : BankPaperCanonicalGuardedSmoothCorrectionEstimate
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      qTilde)
    (Hbaseline : BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  have hdeletedToAnchors :
      F.extendedSmoothBaseGuardDeletionCard W K deltaStar =O[atTop]
        F.extendedAnchorIntersectionCard W K := by
    apply IsBigO.of_bound 1
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [
      BankPaperCanonicalGuardedTailFamily.extendedSmoothBaseGuardDeletionCard,
      dif_pos hn,
      BankPaperCanonicalGuardedTailFamily.extendedAnchorIntersectionCard,
      dif_pos hn, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      Real.norm_eq_abs, abs_of_nonneg (by positivity), one_mul]
    exact_mod_cast
      bankPaperCanonicalSmoothBaseGuardDeletionPool_card_le_anchorIntersection
        (BankPaperCanonicalGuardedTailFamily.realization F n hn)
        (BankPaperCanonicalGuardedTailFamily.certificate F n hn)
          deltaStar W K
  have Hdeleted : BankPaperCanonicalSmoothGuardDeletionCensus
      (F.extendedSmoothBaseGuardDeletionCard W K deltaStar) :=
    hdeletedToAnchors.trans Hanchors
  apply
    bankPaperCanonicalSectionEightAnalyticLedger_of_literalGuardedSource
      depth W K betaAct deltaStar F qTilde h logY Lambda0 m0 mFrozen
  exact ⟨Hdeleted, Hcorrection, Hbaseline⟩

/-- Final tail-family reduction with the guard census discharged.  The first
old ledger field now requires only the extended guarded-to-`qTilde`
correction estimate; the second requires exactly the paper's three baseline
mass/height estimates. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_of_correctionAndBaseline
    {c : Real} {N : Nat} (depth W K : Nat)
    (betaAct deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (qTilde h logY Lambda0 m0 mFrozen : Nat -> Real)
    (Hcorrection : BankPaperCanonicalGuardedSmoothCorrectionEstimate
      (F.extendedGuardedSmoothBaseMass W K betaAct deltaStar)
      qTilde)
    (Hbaseline : BankPaperCanonicalFrozenBaselineSourceLedger
      h logY Lambda0 m0 qTilde) :
    BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde) := by
  apply bankPaperCanonicalSectionEightAnalyticLedger_of_literalAnchorSource
    depth W K betaAct deltaStar F qTilde h logY Lambda0 m0 mFrozen
  · exact guardedCentralAnchors_inter_rawSmoothBasePool_isBigO_envelope
      depth W K F
  · exact Hcorrection
  · exact Hbaseline

end

end Erdos390.WholePaper
