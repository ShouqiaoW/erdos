import Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement
import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureConstruction

/-!
# Tangent transport for the guarded smooth additive refinement

Changing the guarded smooth broad pool changes a selector's tangent data
only through two literal finite ledgers:

* the unweighted change of the smooth row sum;
* for every natural coordinate `q`, the same change weighted by
  `q`-adic valuation.

This file records those changes exactly.  In particular, it does not infer
the missing active-placement moments from support or pointwise bounds.  The
final connector says that pool feasibility together with zero row and
valuation ledgers transports the complete existing
`BankPaperCanonicalRoundedSelectorTangentInput` to the additive refinement.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Exact valuation moments of the local replacement -/

/-- The change in the selector's `q`-adic valuation caused by replacing the
guarded smooth broad pool by the protected-plus-active refinement. -/
def bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (q : Nat) : Real :=
  ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1,
    (betaProt / B.L +
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed a -
        baseSelector a) * (a.factorization q : Real)

/-- The exact zero-ledger condition which makes the local refinement
invisible both to the smooth row mass and to every prime-valuation
coordinate.  These are placement moment equalities, not consequences of
the pointwise protected/active split. -/
def BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) : Prop :=
  (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1,
      (betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a -
          baseSelector a)) = 0 ∧
    ∀ q : Nat, q.Prime ->
      bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0

/-- Non-prime valuation moments vanish automatically.  Hence the ledger
above only needs to quantify over genuine prime coordinates. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_not_prime
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {q : Nat}
    (hq : ¬q.Prime) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
  simp [bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment,
    Nat.factorization_eq_zero_of_not_prime _ hq]

/-- A replacement supported in the smooth row has no valuation moment
above the smooth cutoff. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_yNat_lt
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {q : Nat}
    (hqPrime : q.Prime) (hqLarge : yNat B.sampleData.n < q) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
      B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
  unfold bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
  apply Finset.sum_eq_zero
  intro a ha
  have haRaw :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K 1 ha
  have haData := mem_completeRoughRowFiber.mp haRaw
  have haHead := mem_roughHeadFree.mp haData.1
  have haInterval : B.sampleData.n < a ∧
      a <= 2 * B.sampleData.n - K * upperTailLength c B.sampleData.n := by
    simpa only [roughBroadLowerBlock, Finset.mem_Ioc] using haHead.1
  have haPos : 0 < a := by omega
  have haSmooth :
      a ∈ Nat.smoothNumbers (yNat B.sampleData.n + 1) :=
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers haPos).mp haData.2
  have hnotDvd : ¬q ∣ a := by
    intro hqa
    have hqSmall :=
      (Nat.mem_smoothNumbers').mp haSmooth q hqPrime hqa
    omega
  rw [Nat.factorization_eq_zero_of_not_dvd hnotDvd]
  simp

/-- At a structured active value where the old selector equals the scaled
seed, the refinement differs from it by exactly the protected constant.
Thus a positive protected split cannot be identified pointwise with the
existing baseline-equality bridge selector. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_sub_base_at_scaledActiveValue
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {T : BarycentricTarget B.sampleData}
    {deltaStar betaProt q : Real} (baseSelector : Nat -> Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (m : B.sampleData.Sample)
    (ha : B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1)
    (hbase : baseSelector (B.sampleData.value m) =
      bankPaperCanonicalScaledActiveSeed T q m) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
          deltaStar betaProt baseSelector
          (bankPaperCanonicalScaledActiveSeed T q)
          (B.sampleData.value m) -
        baseSelector (B.sampleData.value m) = betaProt / B.L := by
  rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector
        (bankPaperCanonicalScaledActiveSeed T q) ha,
    bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      B.sampleData T q hsep m,
    hbase]
  ring

/-- Exact weighted-sum change over the actual guarded candidate set. -/
theorem sum_guardedCandidates_additiveRefinement_factorization_sub_base_eq_moment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (q : Nat) :
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
            deltaStar betaProt baseSelector activeSeed a *
          (a.factorization q : Real)) -
        ∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
          baseSelector a * (a.factorization q : Real) =
      bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q := by
  rw [← Finset.sum_sub_distrib]
  have hpool :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 ⊆
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro a ha
    exact (mem_completeRoughRowFiber.mp
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 ha)).1
  calc
    (∑ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
              B R certificate
              deltaStar betaProt baseSelector activeSeed a *
            (a.factorization q : Real) -
          baseSelector a * (a.factorization q : Real))) =
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
              B R certificate
              deltaStar betaProt baseSelector activeSeed a *
            (a.factorization q : Real) -
          baseSelector a * (a.factorization q : Real)) := by
      symm
      apply Finset.sum_subset hpool
      intro a _haCandidate haNotPool
      rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
        B R certificate baseSelector activeSeed haNotPool]
      ring
    _ = bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q := by
      unfold
        bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
      apply Finset.sum_congr rfl
      intro a ha
      rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
        B R certificate baseSelector activeSeed ha]
      ring

/-- Exact change in the literal selector valuation deficit.  The target
term cancels, leaving the negative of the local valuation moment. -/
theorem bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_sub_moment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (q : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed) q =
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector q -
        bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed q := by
  have hmoment :=
    sum_guardedCandidates_additiveRefinement_factorization_sub_base_eq_moment
      (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
      B R certificate baseSelector activeSeed q
  unfold bankPaperCanonicalSelectorValuationDeficit
  rw [← hmoment]
  ring

/-- Exact pointwise transport formula for the finite-band tangent residual. -/
theorem bankPaperCanonicalTangentResidual_additiveRefinement_eq_sub_moment
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (p : BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W) :
    bankPaperCanonicalTangentResidual R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed) p =
      bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector p -
        bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
          B R certificate deltaStar betaProt baseSelector activeSeed p.1 := by
  unfold bankPaperCanonicalTangentResidual
  exact
    bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_sub_moment
      (K := K) B R certificate fixed baseSelector activeSeed p.1

/-- Exact transport of the signed residual sum in one exponent band. -/
theorem sum_tangentResidual_additiveRefinement_eq_sub_moment
    {Head GeoBand TangentBand : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    [DecidableEq TangentBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (bandOf : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> TangentBand)
    (band : TangentBand) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      if bandOf p = band then
        bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed) p
      else 0) =
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if bandOf p = band then
          bankPaperCanonicalTangentResidual R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            baseSelector p
        else 0) -
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if bandOf p = band then
          bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
            (K := K)
            B R certificate deltaStar betaProt baseSelector activeSeed p.1
        else 0 := by
  calc
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      if bandOf p = band then
        bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed) p
      else 0) =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        ((if bandOf p = band then
            bankPaperCanonicalTangentResidual R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              baseSelector p
          else 0) -
        (if bandOf p = band then
            bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
              (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed p.1
          else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpBand : bandOf p = band
      · simp only [if_pos hpBand]
        exact
          bankPaperCanonicalTangentResidual_additiveRefinement_eq_sub_moment
            (K := K) B R certificate fixed baseSelector activeSeed p
      · simp [hpBand]
    _ = _ := by
      rw [Finset.sum_sub_distrib]

/-- Exact transport of every literal ratio-cell prefix load. -/
theorem tangentRatioCellPrefixMass_additiveRefinement_eq_sub_moment
    {Head GeoBand TangentBand : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    [DecidableEq TangentBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (bandOf : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> TangentBand)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (band : TangentBand) (cut : Nat) :
    tangentRatioCellPrefixMass
        (bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed))
        bandOf cellIndex band cut =
      tangentRatioCellPrefixMass
          (bankPaperCanonicalTangentResidual R certificate fixed
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            baseSelector)
          bandOf cellIndex band cut -
        ∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          if bandOf p = band ∧ cellIndex p <= cut then
            bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
              (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed p.1
          else 0 := by
  unfold tangentRatioCellPrefixMass
  calc
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      if bandOf p = band ∧ cellIndex p <= cut then
        bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed) p
      else 0) =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        ((if bandOf p = band ∧ cellIndex p <= cut then
            bankPaperCanonicalTangentResidual R certificate fixed
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              baseSelector p
          else 0) -
        (if bandOf p = band ∧ cellIndex p <= cut then
            bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment
              (K := K)
              B R certificate deltaStar betaProt baseSelector activeSeed p.1
          else 0)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpCut : bandOf p = band ∧ cellIndex p <= cut
      · simp only [if_pos hpCut]
        exact
          bankPaperCanonicalTangentResidual_additiveRefinement_eq_sub_moment
            (K := K) B R certificate fixed baseSelector activeSeed p
      · simp [hpCut]
    _ = _ := by
      rw [Finset.sum_sub_distrib]

/-! ## Zero-ledger transport -/

/-- Outside the smooth row, every coordinate of the guarded candidate row
is unchanged, not merely the coordinates belonging to another broad pool. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_eq_base_on_guardedRow
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {label a : Nat} (hlabel : label ≠ 1)
    (ha : a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a = baseSelector a := by
  apply bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
  intro haSmooth
  have haOne : a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K 1 haSmooth
  have honeEq := (mem_completeRoughRowFiber.mp haOne).2
  have hlabelEq := (mem_completeRoughRowFiber.mp ha).2
  exact hlabel (hlabelEq.symm.trans honeEq)

/-- Every nonsmooth guarded row has exactly the same total after the local
smooth refinement. -/
theorem sum_guardedRow_additiveRefinement_eq_base_of_label_ne_one
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {label : Nat} (hlabel : label ≠ 1) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed a) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        baseSelector a := by
  apply Finset.sum_congr rfl
  intro a ha
  exact
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_eq_base_on_guardedRow
      (K := K) B R certificate baseSelector activeSeed hlabel ha

/-- A zero unweighted pool ledger makes the refined smooth-row total equal
to the base smooth-row total. -/
theorem sum_guardedSmoothRow_additiveRefinement_eq_base_of_zeroMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed a) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        baseSelector a := by
  apply sub_eq_zero.mp
  exact
    (sum_guardedSmoothRow_additiveRefinement_sub_base_eq_pool
      (K := K) B R certificate baseSelector activeSeed).trans hledger.1

/-- The same named smooth integer quota is preserved by the zero row
ledger. -/
theorem bankPaperCanonicalGuardedSmoothFlexibleQuota_additiveRefinement_of_zeroMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (quota : Int)
    (hbase : BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K baseSelector quota)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota R certificate deltaStar K
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector activeSeed) quota := by
  unfold BankPaperCanonicalGuardedSmoothFlexibleQuota at hbase ⊢
  rw [sum_guardedSmoothRow_additiveRefinement_eq_base_of_zeroMomentLedger
    (K := K) B R certificate baseSelector activeSeed hledger]
  exact hbase

/-- Zero valuation moments make every literal selector deficit identical to
the one of the base selector. -/
theorem bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_base_of_zeroMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed)
    (q : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed) q =
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        baseSelector q := by
  have hmoment :
      bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed q = 0 := by
    by_cases hq : q.Prime
    · exact hledger.2 q hq
    · exact
        bankPaperCanonicalGuardedSmoothAdditiveRefinementValuationMoment_eq_zero_of_not_prime
          (K := K) B R certificate baseSelector activeSeed hq
  rw [
    bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_sub_moment
      (K := K) B R certificate fixed baseSelector activeSeed q,
    hmoment, sub_zero]

/-- Zero valuation moments preserve the finite-band tangent residual
pointwise. -/
theorem bankPaperCanonicalTangentResidual_additiveRefinement_eq_base_of_zeroMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed)
    (p : BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W) :
    bankPaperCanonicalTangentResidual R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed) p =
      bankPaperCanonicalTangentResidual R certificate fixed
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        baseSelector p := by
  unfold bankPaperCanonicalTangentResidual
  exact
    bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_base_of_zeroMomentLedger
      (K := K) B R certificate fixed baseSelector activeSeed hledger p.1

/-- The zero row ledger transports all complete-rough-row integrality from
the base selector to the additive refinement. -/
theorem bankPaperCanonicalSelectorRowIntegral_additiveRefinement_of_zeroMomentLedger
    {Head GeoBand : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hbase : BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      baseSelector)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector activeSeed) := by
  intro label hlabelMem
  obtain ⟨quota, hquota⟩ := hbase label hlabelMem
  refine ⟨quota, ?_⟩
  change
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed a) = (quota : Real)
  change
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
        baseSelector a) = (quota : Real) at hquota
  by_cases hlabel : label = 1
  · subst label
    rw [sum_guardedSmoothRow_additiveRefinement_eq_base_of_zeroMomentLedger
      (K := K) B R certificate baseSelector activeSeed hledger]
    exact hquota
  · calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed a) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K label,
          baseSelector a := by
        exact sum_guardedRow_additiveRefinement_eq_base_of_label_ne_one
          (K := K) B R certificate baseSelector activeSeed hlabel
      _ = (quota : Real) := hquota

/-- Direct connector from an existing rounded selector to the protected
plus active refinement.  The only new inputs are feasibility on the replaced
pool and the explicit zero row/valuation ledger. -/
theorem bankPaperCanonicalRoundedSelectorTangentInput_additiveRefinement_of_zeroMomentLedger
    {Head GeoBand TangentBand : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype GeoBand] [DecidableEq GeoBand]
    [DecidableEq TangentBand]
    (B : BridgeData Head GeoBand)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat)
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (bandOf : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> TangentBand)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : TangentBand -> Nat -> Real)
    (Sbase : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      bandOf cellIndex pointwiseUpper prefixUpper baseSelector)
    (hpoolFeasible : ∀ a ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed a ∧
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed a <= 1)
    (hledger :
      BankPaperCanonicalGuardedSmoothAdditiveRefinementZeroMomentLedger (K := K)
        B R certificate deltaStar betaProt baseSelector activeSeed) :
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      bandOf cellIndex pointwiseUpper prefixUpper
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector activeSeed) := by
  rcases Sbase with
    ⟨hbaseFeasible, hbaseRow, hbaseBalance, hbaseSupport,
      hbaseBand, hbasePointwise, hbasePrefix⟩
  have hdeficit : ∀ q : Nat,
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed) q =
        bankPaperCanonicalSelectorValuationDeficit R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector q := by
    intro q
    exact
      bankPaperCanonicalSelectorValuationDeficit_additiveRefinement_eq_base_of_zeroMomentLedger
        (K := K) B R certificate fixed baseSelector activeSeed hledger q
  have hresidual : ∀ p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed) p =
        bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector p := by
    intro p
    exact
      bankPaperCanonicalTangentResidual_additiveRefinement_eq_base_of_zeroMomentLedger
        (K := K) B R certificate fixed baseSelector activeSeed hledger p
  have hresidualFun :
      bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed) =
        bankPaperCanonicalTangentResidual R certificate fixed
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          baseSelector :=
    funext hresidual
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a haCandidate
    by_cases haPool : a ∈
        R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1
    · exact hpoolFeasible a haPool
    · rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
        (K := K) B R certificate baseSelector activeSeed haPool]
      exact hbaseFeasible a haCandidate
  · exact
      bankPaperCanonicalSelectorRowIntegral_additiveRefinement_of_zeroMomentLedger
        (K := K) B R certificate baseSelector activeSeed hbaseRow hledger
  · unfold BankPaperCanonicalPostRoundingPrimeBandBalance at hbaseBalance ⊢
    simpa only [hdeficit] using hbaseBalance
  · unfold BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand at hbaseSupport ⊢
    intro q hqPrime hqBand
    rw [hdeficit q]
    exact hbaseSupport q hqPrime hqBand
  · intro band
    simpa only [hresidual] using hbaseBand band
  · intro p
    rw [hresidual p]
    exact hbasePointwise p
  · intro band cut
    rw [hresidualFun]
    exact hbasePrefix band cut

end BankPaperRealization

end

end Erdos390.WholePaper
