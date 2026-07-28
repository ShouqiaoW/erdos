import Erdos390.WholePaper.BankPaperCanonicalActualEndpointSlackConnector

/-!
# Additive protected refinement on the guarded smooth broad pool

The literal raw selector already has constant broad weight `beta / L`.
The paper splits `beta = betaProt + betaAct`, freezes the first summand,
and replaces the second by the structured active seed.  The earlier
guarded continuation records only the resulting smooth-row integer quota;
it does not retain this pointwise additive identity.

This file restores that identity by an explicit local refinement.  On the
guarded smooth broad pool it sets

`preSelector = betaProt / L + activeSeedAmbient`,

and away from that pool it leaves an already constructed base selector
unchanged.  Thus nonsmooth corrected rows are untouched, while the actual
frozen remainder is definitionally the protected constant `betaProt / L`.
The existing raw-point theorem proves that this constant is precisely the
protected part of the paper's head-compatible raw broad weight.

This closes the positive-remainder and pre-selector-upper algebra without a
new selector assumption.  It deliberately does not claim that replacing an
arbitrary smooth row preserves its integer quota or prime moments: those are
the separate smooth-ledger/active-measure construction obligations.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The explicit protected layer and additive refinement -/

/-- The frozen protected layer on the literal guarded smooth broad pool. -/
def bankPaperCanonicalGuardedSmoothProtectedLayer
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (a : Nat) : Real :=
  if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 then
    betaProt / B.L
  else 0

@[simp] theorem bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
      deltaStar betaProt a = betaProt / B.L := by
  simp [bankPaperCanonicalGuardedSmoothProtectedLayer, ha]

@[simp] theorem bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} {a : Nat}
    (ha : a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
      deltaStar betaProt a = 0 := by
  simp [bankPaperCanonicalGuardedSmoothProtectedLayer, ha]

/-- A positive protected split constant gives a genuinely positive frozen
weight on every guarded smooth broad coordinate. -/
theorem bankPaperCanonicalGuardedSmoothProtectedLayer_pos_of_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (hbetaProt : 0 < betaProt) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    0 < bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
      deltaStar betaProt a := by
  rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
    B R certificate ha]
  exact div_pos hbetaProt B.L_pos

/-- On the clean smooth broad pool, the explicit protected layer is exactly
the paper's head-compatible raw weight with broad parameter `betaProt`. -/
theorem bankPaperCanonicalGuardedSmoothProtectedLayer_eq_rawWeight_of_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha betaProt : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
        deltaStar betaProt a =
      roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha betaProt B.L a := by
  rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
    B R certificate ha]
  exact (roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool
    (R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K 1 ha)).symm

/-- The protected/active split is an exact additive split of the original
raw broad constant before the active summand is redistributed. -/
theorem roughHeadCompatibleRawWeight_eq_protected_add_active_of_mem_guardedSmoothPool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar alpha betaProt betaAct : Real} {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
        (betaProt + betaAct) B.L a =
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
        B R certificate
          deltaStar betaProt a +
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaAct B.L a := by
  have hraw :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_broadPool
      certificate deltaStar B.sampleData.W K 1 ha
  calc
    roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
        (upperTailLength c B.sampleData.n) K alpha
        (betaProt + betaAct) B.L a =
      (betaProt + betaAct) / B.L :=
        roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool hraw
    _ = betaProt / B.L + betaAct / B.L := by ring
    _ = bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
          B R certificate
          deltaStar betaProt a +
        roughHeadCompatibleRawWeight B.sampleData.W B.sampleData.n
          (upperTailLength c B.sampleData.n) K alpha betaAct B.L a := by
      rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
        B R certificate ha,
        roughHeadCompatibleRawWeight_eq_broad_of_mem_correctionPool hraw]

/-- Replace only the guarded smooth broad coordinates by the literal
protected-plus-active sum; retain the supplied selector everywhere else. -/
def bankPaperCanonicalGuardedSmoothAdditiveRefinement
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (a : Nat) : Real :=
  if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 then
    bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
      B R certificate
        deltaStar betaProt a +
      bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed a
  else baseSelector a

@[simp] theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a =
      betaProt / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData activeSeed a := by
  simp [bankPaperCanonicalGuardedSmoothAdditiveRefinement,
    bankPaperCanonicalGuardedSmoothProtectedLayer, ha]

@[simp] theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a = baseSelector a := by
  simp [bankPaperCanonicalGuardedSmoothAdditiveRefinement, ha]

/-- The refinement's exact pointwise difference from the supplied selector.
This identity is the boundary for transporting a full rounded-selector
input: row sums and prime moments are preserved only after the corresponding
weighted sum of this displayed difference is proved to vanish. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_sub_base
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (a : Nat) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
          deltaStar betaProt baseSelector activeSeed a - baseSelector a =
      if a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 then
        betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a -
          baseSelector a
      else 0 := by
  by_cases ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 <;>
    simp [bankPaperCanonicalGuardedSmoothAdditiveRefinement,
      bankPaperCanonicalGuardedSmoothProtectedLayer, ha]

/-- Exact smooth-row mass change caused by the refinement.  In particular,
preservation of the smooth integer quota is equivalent to controlling this
explicit pool sum; it is not implied by the old quota of `baseSelector`. -/
theorem sum_guardedSmoothRow_additiveRefinement_sub_base_eq_pool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) :
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed a) -
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a =
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a -
          baseSelector a) := by
  rw [← Finset.sum_sub_distrib]
  have hpool :
      R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1 ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K 1
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
            deltaStar betaProt baseSelector activeSeed a -
          baseSelector a)) =
      ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
            deltaStar betaProt baseSelector activeSeed a -
          baseSelector a) := by
      symm
      apply Finset.sum_subset hpool
      intro a _haRow haNotPool
      rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
        B R certificate baseSelector activeSeed haNotPool]
      ring
    _ = ∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a -
          baseSelector a) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
        B R certificate baseSelector activeSeed ha]

/-- Constructive smooth-quota update for the literal additive refinement.
If the replacement pool is chosen to have the signed integer mass change
`targetQuota - baseQuota`, then the refined selector realizes exactly
`targetQuota`.  Thus the desired nearest-integer quota can be installed at
the placement stage rather than inferred from mere row integrality. -/
theorem bankPaperCanonicalGuardedSmoothFlexibleQuota_additiveRefinement_of_rowChange
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (baseQuota targetQuota : Int)
    (hbase : BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K baseSelector baseQuota)
    (hrowChange :
      (∑ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        (betaProt / B.L +
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a -
          baseSelector a)) = ((targetQuota - baseQuota : Int) : Real)) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota R certificate deltaStar K
      (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector activeSeed) targetQuota := by
  unfold BankPaperCanonicalGuardedSmoothFlexibleQuota at hbase ⊢
  have hchange :=
    sum_guardedSmoothRow_additiveRefinement_sub_base_eq_pool
      (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
      B R certificate baseSelector activeSeed
  rw [hrowChange] at hchange
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed a) =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          baseSelector a) + ((targetQuota - baseQuota : Int) : Real) := by
      linarith
    _ = (baseQuota : Real) +
        ((targetQuota - baseQuota : Int) : Real) := by rw [hbase]
    _ = (targetQuota : Real) := by
      push_cast
      ring

/-- Every nonsmooth guarded broad row is pointwise unchanged by the smooth
additive refinement. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_eq_base_on_nonsmoothPool
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
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
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a = baseSelector a := by
  apply bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_not_mem
  intro haSmooth
  have haOne : a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K 1 haSmooth
  have haLabel : a ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K label ha
  have honeEq := (mem_completeRoughRowFiber.mp haOne).2
  have hlabelEq := (mem_completeRoughRowFiber.mp haLabel).2
  exact hlabel (hlabelEq.symm.trans honeEq)

/-! ## Derived active and pre-selector upper bounds -/

/-- Head-pattern separation turns a pointwise active-seed ledger into the
same ledger for its ambient push-forward. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_le_of_headPatternsSeparated
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (activeSeed : B.sampleData.Sample -> Real)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L) :
    forall a : Nat,
      bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData activeSeed a <= Cactive / B.L := by
  intro a
  calc
    bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed a =
        B.ambientActiveWeight 0 a :=
      (Erdos390.WholePaper.BridgeData.ambientActiveWeight_zero_eq_activeSeedAmbient B
        activeSeed hseed a).symm
    _ <= Cactive / B.L := by
      by_cases ha : exists m : B.sampleData.Sample,
          B.sampleData.value m = a
      · obtain ⟨m, rfl⟩ := ha
        rw [B.ambientActiveWeight_eq_of_value hsep,
          Erdos390.WholePaper.BridgeData.activeCoordinateWeight_zero_eq_baseline
            B m,
          hseed m]
        exact hactiveSeed m
      · rw [B.ambientActiveWeight_eq_zero_of_not_value 0 a
          (fun m hm => ha ⟨m, hm⟩)]
        exact div_nonneg hCactive B.L_pos.le

/-- The additive refinement has the expected raw broad upper bound:
protected constant plus the active-coordinate constant. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_le_div_log
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m)
    (Cactive : Real) (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L)
    {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a <=
      (betaProt + Cactive) / B.L := by
  rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
    B R certificate baseSelector activeSeed ha]
  have hactiveAmbient :=
    bankPaperCanonicalActiveSeedAmbientWeight_le_of_headPatternsSeparated
      B hsep activeSeed hseed Cactive hCactive hactiveSeed a
  calc
    betaProt / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData activeSeed a <=
      betaProt / B.L + Cactive / B.L :=
        add_le_add le_rfl hactiveAmbient
    _ = (betaProt + Cactive) / B.L := by ring

/-- Existing cell-mass and cell-cardinality estimates supply the preceding
active constant directly.  This is the exact finite bridge from the paper's
baseline measure-realization bounds to the refined pre-selector upper bound. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_le_of_cellDensity
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m)
    (Cmass density : Real) (hCmass : 0 <= Cmass)
    (hdensity : 0 < density)
    (hmass : forall cell : Cell Head,
      B.baseline.cellMass cell <=
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : forall cell : Cell Head,
      density * (B.sampleData.n : Real) <=
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
      B R certificate
        deltaStar betaProt baseSelector activeSeed a <=
      (betaProt + Cmass / density) / B.L := by
  have hbaseline := B.baseline_baseWeight_le_of_cell_density
    Cmass density hCmass hdensity hmass hcard
  have hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= (Cmass / density) / B.L := by
    intro m
    rw [← hseed m]
    calc
      B.baseline.baseWeight m <= Cmass / (density * B.L) := hbaseline m
      _ = (Cmass / density) / B.L := by
        field_simp [ne_of_gt hdensity, ne_of_gt B.L_pos]
  exact bankPaperCanonicalGuardedSmoothAdditiveRefinement_le_div_log
    B R certificate baseSelector activeSeed hsep hseed
      (Cmass / density) (div_nonneg hCmass hdensity.le)
      hactiveSeed ha

/-- The protected reserve inequality is definitionally built into the
refinement; only the fixed comparison `sigma <= betaProt` remains. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedReserve
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt sigma : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hsigma : sigma <= betaProt) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    sigma / B.L +
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData activeSeed a <=
      bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
        B R certificate
        deltaStar betaProt baseSelector activeSeed a := by
  rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
    B R certificate baseSelector activeSeed ha]
  exact add_le_add
    (div_le_div_of_nonneg_right hsigma B.L_pos.le) le_rfl

/-! ## Exact protected window and actual endpoint -/

/-- The literal frozen push-forward of the refined pre-selector is exactly
the protected broad constant.  This is the strongest finite form of the
previously missing positive-remainder statement. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_frozenAmbientWeight_eq
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) {a : Nat}
    (ha : a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates := R.roughCanonicalGuardedCandidateSet
            certificate deltaStar K))
        (bankPaperCanonicalActualFrozenWeight B.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
            B R certificate
            deltaStar betaProt baseSelector activeSeed)
          activeSeed) a =
      betaProt / B.L := by
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
  have haCandidate : a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K :=
    (mem_completeRoughRowFiber.mp
      (R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
        certificate deltaStar B.sampleData.W K 1 ha)).1
  rw [if_pos haCandidate,
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_apply_of_mem
      B R certificate baseSelector activeSeed ha]
  ring

/-- The actual tagged frozen remainder of the additive refinement is
exactly `betaProt / L` on every guarded smooth broad coordinate. -/
theorem bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedWindow
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    {deltaStar betaProt sigma : Real} (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hsigma : sigma <= betaProt) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed)
        activeSeed)
      sigma betaProt := by
  unfold BankPaperCanonicalGuardedSmoothProtectedWindow
  intro a ha
  rw [bankPaperCanonicalGuardedSmoothAdditiveRefinement_frozenAmbientWeight_eq
    B R certificate baseSelector activeSeed ha]
  constructor
  · exact div_le_div_of_nonneg_right hsigma B.L_pos.le
  · exact le_rfl

/-- Smooth tangent slack for the literal actual endpoint of the additive
refinement.  No protected-reserve or pre-selector-upper premise remains. -/
theorem exists_bankPaperCanonicalGuardedSmoothAdditiveRefinement_endpointSlackLayers
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (baseSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hseed : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m = activeSeed m)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed)
        activeSeed)
      quota path)
    (C sigma Cactive : Real) (hsigma : sigma <= betaProt)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactiveSeed : forall m : B.sampleData.Sample,
      activeSeed m <= Cactive / B.L)
    (hlarge : betaProt +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L) :
    ∃ protectedPart active : Nat -> Real,
      ∀ a ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        bankPaperCanonicalActualP87EndpointSelector B
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
                B R certificate deltaStar betaProt baseSelector activeSeed)
              activeSeed path a =
            protectedPart a + active a ∧
          sigma / B.L <= protectedPart a ∧
          0 <= active a ∧
          protectedPart a + active a <= 1 - sigma / B.L := by
  have hprotected :=
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedWindow
      (K := K) (deltaStar := deltaStar) (betaProt := betaProt)
      (sigma := sigma) B R certificate baseSelector activeSeed hsigma
  have hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L := by
    intro m
    rw [hseed m]
    exact hactiveSeed m
  simpa only [bankPaperCanonicalActualP87EndpointSelector] using
    (exists_bankPaperProposition87EndpointSelector_smoothSlackLayers
      B R certificate deltaStar Delta radius markedTarget N Cpost
      (bankPaperCanonicalActualFrozenValue
        (candidates := R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K))
      (bankPaperCanonicalActualFrozenWeight B.sampleData
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalGuardedSmoothAdditiveRefinement (K := K)
          B R certificate
          deltaStar betaProt baseSelector activeSeed)
        activeSeed)
      quota path Hpath C sigma betaProt Cactive hC hW hhi hsep hCactive
      hactive hprotected hlarge)

end BankPaperRealization

end

end Erdos390.WholePaper
