import Erdos390.Full.CanonicalRegularMeshEndpointFamily
import Erdos390.Full.PaperBaselineSlack
import Erdos390.Full.PaperCanonicalBaseline
import Erdos390.Full.PaperProposition87Assembly
import Erdos390.WholePaper.BankPaperCanonicalGuardedSectionNineContinuation

/-!
# Canonical guarded selector to bridge-fit connector

This module joins the finite objects on the two sides of the Section 8/9
interface without asserting the missing selector theorem.

* `bankPaperCanonicalBridgeData` builds the literal `PaperBridgeFit.BridgeData`
  from an existing guarded structured sample, the canonical barycentric
  baseline, and the canonical regular-mesh partition.
* `BankPaperCanonicalGuardedBridgeSelectorConstructor` is the sole
  existential socket.  Its witness is an actual guarded selector satisfying
  the already defined rounded-selector tangent input and agreeing with the
  bridge baseline on the active structured sample.
* the projection and frozen-layer theorems derive the smooth integer quota,
  feasibility, row integrality, prime-band balance and support, tangent
  balance and pointwise/prefix bounds, the frozen feasibility ledger, and the
  total integer quota.  No one of those conclusions is repeated as a new
  premise.

The active structured sample need only be a subset of the guarded smooth row;
it is not silently identified with the whole row.  All other guarded
coordinates are retained in the frozen layer with their selector weights,
while the fixed exceptional factors have weight one.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open BankPaperRealization

noncomputable section

/-! ## Canonical bridge data -/

/-- The literal bridge data obtained from the canonical barycentric baseline
and the canonical regular-mesh prime partition. -/
def bankPaperCanonicalBridgeData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    BridgeData Head (Fin (M.cellCount + 1)) where
  sampleData := D
  baseline := T.baseline
  partition :=
    Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition
      M hdelta hn hW S
  lowBand := Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M
  referenceHead := referenceHead
  w := delta + eta
  w_pos := hw
  n_gt_one := hn

@[simp] theorem bankPaperCanonicalBridgeData_sampleData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).sampleData = D :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_baseline
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).baseline =
      T.baseline :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_partition
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).partition =
          Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.canonicalPartition
            M hdelta hn hW S :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_lowBand
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).lowBand =
          Erdos390.Full.RegularMeshPrimeCutoffs.Mesh.lowBand M :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_w
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).w =
      delta + eta :=
  rfl

@[simp] theorem bankPaperCanonicalBridgeData_q
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalBridgeData D T M hdelta hn hW S referenceHead hw).q =
      1 := by
  change T.baseline.totalMass = 1
  exact T.baseline_totalMass

/-! ## Active values and integer row quotas -/

/-- The untagged natural-number support of the structured bridge sample. -/
def bankPaperCanonicalBridgeActiveValues
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) : Finset Nat :=
  Finset.univ.image B.sampleData.value

theorem mem_bankPaperCanonicalBridgeActiveValues
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData Head Band} {a : Nat} :
    a ∈ bankPaperCanonicalBridgeActiveValues B ↔
      ∃ m : B.sampleData.Sample, B.sampleData.value m = a := by
  simp [bankPaperCanonicalBridgeActiveValues]

/-- Row integrality alone supplies an integer quota for the smooth row.  If
label `1` is not attained, its fiber is empty and the quota is zero. -/
theorem exists_bankPaperCanonicalSmoothQuota_of_rowIntegral
    {n : Nat} {candidates : Finset Nat} {selector : Nat -> Real}
    (hrow : BankPaperCanonicalSelectorRowIntegral n candidates selector) :
    ∃ smoothQuota : Int,
      (∑ a ∈ completeRoughRowFiber (yNat n) candidates 1,
        selector a) = (smoothQuota : Real) := by
  classical
  by_cases hlabel : 1 ∈ completeRoughLabelSet (yNat n) candidates
  · exact hrow 1 hlabel
  · refine ⟨0, ?_⟩
    have hempty : completeRoughRowFiber (yNat n) candidates 1 = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hlabel (mem_completeRoughLabelSet.mpr
        ⟨a, (mem_completeRoughRowFiber.mp ha).1,
          (mem_completeRoughRowFiber.mp ha).2⟩)
    rw [hempty]
    simp

/-- Integral mass on every attained complete-rough row makes the total
candidate mass integral. -/
theorem exists_bankPaperCanonicalTotalQuota_of_rowIntegral
    {n : Nat} {candidates : Finset Nat} {selector : Nat -> Real}
    (hrow : BankPaperCanonicalSelectorRowIntegral n candidates selector) :
    ∃ candidateQuota : Int,
      (∑ a ∈ candidates, selector a) = (candidateQuota : Real) := by
  classical
  let rowQuota : Nat -> Int := fun label =>
    if hlabel : label ∈ completeRoughLabelSet (yNat n) candidates then
      Classical.choose (hrow label hlabel)
    else 0
  have hrowQuota : forall label
      (hlabel : label ∈ completeRoughLabelSet (yNat n) candidates),
      (∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) = (rowQuota label : Real) := by
    intro label hlabel
    simp only [rowQuota, dif_pos hlabel]
    exact Classical.choose_spec (hrow label hlabel)
  refine ⟨(∑ label ∈ completeRoughLabelSet (yNat n) candidates,
      rowQuota label), ?_⟩
  rw [sum_eq_sum_completeRoughRowFibers]
  calc
    (∑ label ∈ completeRoughLabelSet (yNat n) candidates,
        ∑ a ∈ completeRoughRowFiber (yNat n) candidates label,
          selector a) =
        ∑ label ∈ completeRoughLabelSet (yNat n) candidates,
          (rowQuota label : Real) := by
      apply Finset.sum_congr rfl
      intro label hlabel
      exact hrowQuota label hlabel
    _ = ((∑ label ∈ completeRoughLabelSet (yNat n) candidates,
          rowQuota label : Int) : Real) := by
      push_cast
      rfl

/-! ## The sole missing constructor and all tangent projections -/

/-- The sole missing Section 8/9 constructor.

Its witness is an actual selector on the literal guarded candidate set.  The
first conjunct is the pre-existing rounded-selector tangent input.  The
second says that the coordinates selected for the smooth bridge start at the
canonical barycentric baseline.  It is a selector-construction condition,
not a separately assumed quota, balance, support, tangent, or feasibility
conclusion. -/
def BankPaperCanonicalGuardedBridgeSelectorConstructor
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
    (deltaStar : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real) : Prop :=
  ∃ selector : Nat -> Real,
    BankPaperCanonicalRoundedSelectorTangentInput
      R certificate (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      B.partition.band cellIndex pointwiseUpper prefixUpper selector ∧
    forall m : B.sampleData.Sample,
      selector (B.sampleData.value m) = B.baseline.baseWeight m

/-- The selector constructor exposes every exact outer field consumed before
the tangent: smooth quota, feasibility, row integrality, band balance,
prime-band support, signed band balance, and pointwise/prefix control. -/
theorem bankPaperCanonicalGuardedBridgeSelectorConstructor_exists_fields
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData Head Band}
    {c : Real} {depth K : Nat}
    {R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar : Real}
    {cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat}
    {pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real}
    {prefixUpper : Band -> Nat -> Real}
    (H : BankPaperCanonicalGuardedBridgeSelectorConstructor B R certificate
      deltaStar (K := K) cellIndex pointwiseUpper prefixUpper) :
    ∃ selector : Nat -> Real, ∃ smoothQuota : Int,
      BankPaperCanonicalGuardedSmoothFlexibleQuota R certificate deltaStar K
          selector smoothQuota ∧
      (forall m : B.sampleData.Sample,
        selector (B.sampleData.value m) = B.baseline.baseWeight m) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
        0 <= selector a ∧ selector a <= 1) ∧
      BankPaperCanonicalSelectorRowIntegral B.sampleData.n
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector ∧
      BankPaperCanonicalPostRoundingPrimeBandBalance
        (W := B.sampleData.W)
        R certificate (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector ∧
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
        (W := B.sampleData.W)
        R certificate (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        selector ∧
      (forall band : Band,
        (∑ p : BankPaperCanonicalTangentPrime
            B.sampleData.n B.sampleData.W,
          if B.partition.band p = band then
            bankPaperCanonicalTangentResidual
              R certificate (R.paperFixedExceptionalFactors deltaStar)
              (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
              selector p
          else 0) = 0) ∧
      (forall p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        abs (bankPaperCanonicalTangentResidual
          R certificate (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          selector p) <= pointwiseUpper p) ∧
      forall band : Band, forall cut : Nat,
        abs (tangentRatioCellPrefixMass
          (bankPaperCanonicalTangentResidual
            R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            selector)
          B.partition.band cellIndex band cut) <= prefixUpper band cut := by
  obtain ⟨selector, S, hbaseline⟩ := H
  obtain ⟨smoothQuota, hsmoothQuota⟩ :=
    exists_bankPaperCanonicalSmoothQuota_of_rowIntegral S.2.1
  refine ⟨selector, smoothQuota, ?_, hbaseline, S.1, S.2.1,
    S.2.2.1, S.2.2.2.1, S.2.2.2.2.1, S.2.2.2.2.2.1,
    S.2.2.2.2.2.2⟩
  exact hsmoothQuota

/-! ## Guarded smooth support -/

/-- A structured sample lying in `(n,2n]` whose values avoid the literal
numerical guards is a subset of the guarded smooth row. -/
theorem bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
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
    (deltaStar : Real)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalBridgeActiveValues B ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
  intro a ha
  obtain ⟨m, hvalue⟩ :=
    mem_bankPaperCanonicalBridgeActiveValues.mp ha
  subst a
  apply mem_completeRoughRowFiber.mpr
  constructor
  · rw [BankPaperRealization.roughCanonicalGuardedCandidateSet,
      Finset.mem_sdiff, roughRawCandidateSet_eq_Ioc hKh]
    exact ⟨Finset.mem_Ioc.mpr ⟨hlower m, hupper m⟩,
      hnotGuard m⟩
  · exact (completeRoughLabel_eq_one_iff_mem_smoothNumbers
      (B.sampleData.value_pos m)).mpr
        (B.sampleData.value_mem_smoothNumbers m)

/-- In particular, every active bridge value is an actual guarded
candidate. -/
theorem bankPaperCanonicalBridgeActiveValues_subset_guardedCandidates
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
    (deltaStar : Real)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    bankPaperCanonicalBridgeActiveValues B ⊆
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
  intro a ha
  exact (mem_completeRoughRowFiber.mp
    (bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
      B R certificate deltaStar hKh hlower hupper hnotGuard ha)).1

/-- Fixed exceptional upper-tail factors are disjoint from a bridge sample
supported at or below `2n`. -/
theorem paperFixedExceptionalFactors_disjoint_bridgeActiveValues
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (deltaStar : Real)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      (bankPaperCanonicalBridgeActiveValues B) := by
  rw [Finset.disjoint_left]
  intro a haFixed haActive
  obtain ⟨m, hvalue⟩ :=
    mem_bankPaperCanonicalBridgeActiveValues.mp haActive
  have haTail := R.paperFixedExceptionalFactors_subset_tail deltaStar haFixed
  have haLower : 2 * B.sampleData.n < a := (Finset.mem_Ioc.mp haTail).1
  rw [← hvalue] at haLower
  exact (Nat.not_lt_of_ge (hupper m)) haLower

/-- Fixed exceptional factors belong to the numerical guard set, whereas
guarded candidates are obtained by deleting that set. -/
theorem paperFixedExceptionalFactors_disjoint_guardedCandidates
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
    (deltaStar : Real) :
    Disjoint (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K) := by
  rw [Finset.disjoint_left]
  intro a haFixed haCandidate
  rw [BankPaperRealization.roughCanonicalGuardedCandidateSet,
    Finset.mem_sdiff] at haCandidate
  have haNotGuard := haCandidate.2
  apply haNotGuard
  simp [BankPaperRealization.roughCanonicalGuardSet,
    BankPaperRealization.tangentPaperNumericalGuardSet, haFixed]

/-! ## Frozen layer and quota -/

/-- Finite frozen support: fixed exceptional factors together with all
guarded selector coordinates not handed to the active bridge. -/
def bankPaperCanonicalBridgeFrozenSupport
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat) : Finset Nat :=
  fixed ∪ (candidates \ bankPaperCanonicalBridgeActiveValues B)

/-- The literal finite coordinate type used for the frozen summand in
Proposition 8.7. -/
abbrev BankPaperCanonicalBridgeFrozenIndex
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat) :=
  ↥(bankPaperCanonicalBridgeFrozenSupport B fixed candidates)

/-- Underlying natural-number coordinate of a frozen index. -/
def bankPaperCanonicalBridgeFrozenValue
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData Head Band} {fixed candidates : Finset Nat} :
    BankPaperCanonicalBridgeFrozenIndex B fixed candidates -> Nat :=
  fun f => f.1

/-- Fixed exceptional coordinates have weight one; every other frozen
coordinate retains its guarded selector weight. -/
def bankPaperCanonicalBridgeFrozenCoordinateWeight
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData Head Band} (fixed candidates : Finset Nat)
    (selector : Nat -> Real) :
    BankPaperCanonicalBridgeFrozenIndex B fixed candidates -> Real :=
  fun f => if f.1 ∈ fixed then 1 else selector f.1

/-- Ambient form of the same frozen layer. -/
def bankPaperCanonicalBridgeFrozenWeight
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat)
    (selector : Nat -> Real) (a : Nat) : Real :=
  if a ∈ fixed then 1
  else if a ∈ candidates \ bankPaperCanonicalBridgeActiveValues B then
    selector a
  else 0

/-- The tagged frozen realization has exactly the preceding ambient weight.
The support contains at most one tag over each natural coordinate. -/
theorem frozenAmbientWeight_eq_bankPaperCanonicalBridgeFrozenWeight
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat)
    (selector : Nat -> Real) (a : Nat) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalBridgeFrozenValue
          (B := B) (fixed := fixed) (candidates := candidates))
        (bankPaperCanonicalBridgeFrozenCoordinateWeight
          (B := B) fixed candidates selector) a =
      bankPaperCanonicalBridgeFrozenWeight B fixed candidates selector a := by
  classical
  unfold BridgeData.frozenAmbientWeight
  change (∑ f : ↥(bankPaperCanonicalBridgeFrozenSupport B fixed candidates),
      if f.1 = a then
        (if f.1 ∈ fixed then 1 else selector f.1)
      else 0) = _
  rw [← Finset.sum_subtype
    (bankPaperCanonicalBridgeFrozenSupport B fixed candidates)
    (fun _ => Iff.rfl)
    (fun x => if x = a then
      (if x ∈ fixed then 1 else selector x)
      else 0)]
  by_cases haFixed : a ∈ fixed
  · have haSupport : a ∈
        bankPaperCanonicalBridgeFrozenSupport B fixed candidates :=
      Finset.mem_union_left _ haFixed
    simp [bankPaperCanonicalBridgeFrozenWeight, haFixed, haSupport]
  · by_cases haCandidate :
        a ∈ candidates \ bankPaperCanonicalBridgeActiveValues B
    · have haSupport : a ∈
          bankPaperCanonicalBridgeFrozenSupport B fixed candidates :=
        Finset.mem_union_right _ haCandidate
      simp [bankPaperCanonicalBridgeFrozenWeight, haFixed, haCandidate,
        haSupport]
    · have haSupport : a ∉
          bankPaperCanonicalBridgeFrozenSupport B fixed candidates := by
        simpa [bankPaperCanonicalBridgeFrozenSupport, haFixed] using
          haCandidate
      simp [bankPaperCanonicalBridgeFrozenWeight, haFixed, haCandidate,
        haSupport]

/-- Feasibility of the rounded selector implies feasibility of the entire
frozen ambient layer. -/
theorem bankPaperCanonicalBridgeFrozenWeight_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat)
    (selector : Nat -> Real)
    (hselector : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1) :
    forall a, bankPaperCanonicalBridgeFrozenWeight
      B fixed candidates selector a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  by_cases haFixed : a ∈ fixed
  · simp [bankPaperCanonicalBridgeFrozenWeight, haFixed]
  · by_cases haCandidate :
      a ∈ candidates \ bankPaperCanonicalBridgeActiveValues B
    · simpa [bankPaperCanonicalBridgeFrozenWeight, haFixed, haCandidate]
        using hselector a (Finset.sdiff_subset haCandidate)
    · simp [bankPaperCanonicalBridgeFrozenWeight, haFixed, haCandidate]

/-- If the fixed upper layer is disjoint from the active bridge, the frozen
ambient weight vanishes identically on every active sample coordinate. -/
theorem bankPaperCanonicalBridgeFrozenWeight_eq_zero_on_sample
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat)
    (selector : Nat -> Real)
    (hfixedActive : Disjoint fixed
      (bankPaperCanonicalBridgeActiveValues B)) :
    forall m : B.sampleData.Sample,
      bankPaperCanonicalBridgeFrozenWeight B fixed candidates selector
        (B.sampleData.value m) = 0 := by
  intro m
  have hmActive : B.sampleData.value m ∈
      bankPaperCanonicalBridgeActiveValues B := by
    exact mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩
  have hmFixed : B.sampleData.value m ∉ fixed := by
    intro hm
    exact Finset.disjoint_left.mp hfixedActive hm hmActive
  simp [bankPaperCanonicalBridgeFrozenWeight, hmFixed, hmActive]

/-- Agreement with the baseline makes the selector mass on the active
untagged support exactly the bridge active mass. -/
theorem sum_selector_bridgeActiveValues_eq_q
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (selector : Nat -> Real)
    (hbaseline : forall m : B.sampleData.Sample,
      selector (B.sampleData.value m) = B.baseline.baseWeight m) :
    (∑ a ∈ bankPaperCanonicalBridgeActiveValues B, selector a) = B.q := by
  classical
  unfold bankPaperCanonicalBridgeActiveValues
  rw [Finset.sum_image]
  · simp_rw [hbaseline]
    exact B.baseline.baseWeight_sum
  · intro m _ k _ hvalue
    exact B.sampleData.value_injective_of_headPatternsSeparated hsep hvalue

/-- Sum of the finite frozen coordinates. -/
theorem sum_bankPaperCanonicalBridgeFrozenCoordinateWeight
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (fixed candidates : Finset Nat)
    (selector : Nat -> Real)
    (hfixedCandidates : Disjoint fixed candidates) :
    (∑ f : BankPaperCanonicalBridgeFrozenIndex B fixed candidates,
      bankPaperCanonicalBridgeFrozenCoordinateWeight
        (B := B) fixed candidates selector f) =
      (fixed.card : Real) +
        ∑ a ∈ candidates \ bankPaperCanonicalBridgeActiveValues B,
          selector a := by
  classical
  change (∑ f : ↥(bankPaperCanonicalBridgeFrozenSupport B fixed candidates),
      if f.1 ∈ fixed then 1 else selector f.1) = _
  rw [← Finset.sum_subtype
    (bankPaperCanonicalBridgeFrozenSupport B fixed candidates)
    (fun _ => Iff.rfl)
    (fun a => if a ∈ fixed then 1 else selector a)]
  have hdisjoint : Disjoint fixed
      (candidates \ bankPaperCanonicalBridgeActiveValues B) :=
    by
      rw [Finset.disjoint_left]
      intro a haFixed haCandidate
      exact Finset.disjoint_left.mp hfixedCandidates haFixed
        (Finset.sdiff_subset haCandidate)
  rw [bankPaperCanonicalBridgeFrozenSupport, Finset.sum_union hdisjoint]
  have hfixedSum :
      (∑ a ∈ fixed, if a ∈ fixed then (1 : Real) else selector a) =
        (fixed.card : Real) := by
    calc
      (∑ a ∈ fixed, if a ∈ fixed then (1 : Real) else selector a) =
          ∑ _a ∈ fixed, (1 : Real) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [if_pos ha]
      _ = (fixed.card : Real) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hfixedSum]
  apply congrArg (fun x : Real => (fixed.card : Real) + x)
  apply Finset.sum_congr rfl
  intro a ha
  have haCandidate : a ∈ candidates := Finset.sdiff_subset ha
  have haNotFixed : a ∉ fixed := by
    intro haFixed
    exact Finset.disjoint_left.mp hfixedCandidates haFixed haCandidate
  simp [haNotFixed]

/-- The frozen coordinates plus the active bridge have an integer total
quota.  The integer comes from complete-rough row integrality; it is not a
new quota premise. -/
theorem exists_bankPaperCanonicalBridgeIntegerQuota
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hfixedCandidates : Disjoint fixed candidates)
    (hactiveCandidates : bankPaperCanonicalBridgeActiveValues B ⊆ candidates)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbaseline : forall m : B.sampleData.Sample,
      selector (B.sampleData.value m) = B.baseline.baseWeight m)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates selector) :
    ∃ quota : Int,
      (quota : Real) =
        (∑ f : BankPaperCanonicalBridgeFrozenIndex B fixed candidates,
          bankPaperCanonicalBridgeFrozenCoordinateWeight
            (B := B) fixed candidates selector f) + B.q := by
  obtain ⟨candidateQuota, hcandidateQuota⟩ :=
    exists_bankPaperCanonicalTotalQuota_of_rowIntegral hrow
  refine ⟨(fixed.card : Int) + candidateQuota, ?_⟩
  have hactiveMass :=
    sum_selector_bridgeActiveValues_eq_q B hsep selector hbaseline
  have hsplit :
      (∑ a ∈ candidates, selector a) =
        (∑ a ∈ bankPaperCanonicalBridgeActiveValues B, selector a) +
          ∑ a ∈ candidates \ bankPaperCanonicalBridgeActiveValues B,
            selector a := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff)]
    rw [Finset.union_sdiff_of_subset hactiveCandidates]
  rw [sum_bankPaperCanonicalBridgeFrozenCoordinateWeight B fixed candidates
    selector hfixedCandidates]
  push_cast
  rw [← hcandidateQuota, hsplit, hactiveMass]
  ring

/-! ## Baseline slack and ambient feasibility -/

/-- The frozen ledger is zero on the active sample, so the existing
`C/L` baseline estimate immediately supplies the combined interior slack. -/
theorem bankPaperCanonicalBridge_combinedBaselineSlack
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hfixedActive : Disjoint fixed
      (bankPaperCanonicalBridgeActiveValues B))
    (Cactive Rbound : Real)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Real.exp (2 * Rbound) * Cactive <= B.L) :
    forall m : B.sampleData.Sample,
      bankPaperCanonicalBridgeFrozenWeight B fixed candidates selector
          (B.sampleData.value m) +
        Real.exp (2 * Rbound) * B.baseline.baseWeight m <= 1 := by
  apply B.combinedBaselineSlack_of_div_log_bounds
    (bankPaperCanonicalBridgeFrozenWeight B fixed candidates selector)
    0 Cactive Rbound
  · intro m
    rw [bankPaperCanonicalBridgeFrozenWeight_eq_zero_on_sample
      B fixed candidates selector hfixedActive m]
    exact div_nonneg (le_refl 0) (le_of_lt B.L_pos)
  · exact hactive
  · simpa using hlarge

/-- Complete finite Section 8/9 connector.  The only existential premise is
`H`, the guarded selector constructor.  All displayed outer fields are
derived: the pre-tangent balance/support/bounds, smooth quota, active smooth
support, frozen feasibility and vanishing on the active sample, integer total
quota, and combined baseline slack. -/
theorem exists_bankPaperCanonicalGuardedBridgeConnector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (H : BankPaperCanonicalGuardedBridgeSelectorConstructor B R certificate
      deltaStar (K := K) cellIndex pointwiseUpper prefixUpper)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (Cactive Rbound : Real)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Real.exp (2 * Rbound) * Cactive <= B.L) :
    ∃ selector : Nat -> Real, ∃ smoothQuota quota : Int,
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        B.partition.band cellIndex pointwiseUpper prefixUpper selector ∧
      BankPaperCanonicalGuardedSmoothFlexibleQuota
        R certificate deltaStar K selector smoothQuota ∧
      (forall m : B.sampleData.Sample,
        selector (B.sampleData.value m) = B.baseline.baseWeight m) ∧
      bankPaperCanonicalBridgeActiveValues B ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 ∧
      (forall a : Nat,
        BridgeData.frozenAmbientWeight
          (bankPaperCanonicalBridgeFrozenValue
            (B := B)
            (fixed := R.paperFixedExceptionalFactors deltaStar)
            (candidates := R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K))
          (bankPaperCanonicalBridgeFrozenCoordinateWeight
            (B := B) (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            selector) a ∈ Set.Icc (0 : Real) 1) ∧
      (forall m : B.sampleData.Sample,
        BridgeData.frozenAmbientWeight
          (bankPaperCanonicalBridgeFrozenValue
            (B := B)
            (fixed := R.paperFixedExceptionalFactors deltaStar)
            (candidates := R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K))
          (bankPaperCanonicalBridgeFrozenCoordinateWeight
            (B := B) (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            selector) (B.sampleData.value m) = 0) ∧
      (quota : Real) =
        (∑ f : BankPaperCanonicalBridgeFrozenIndex B
            (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
          bankPaperCanonicalBridgeFrozenCoordinateWeight
            (B := B) (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            selector f) + B.q ∧
      forall m : B.sampleData.Sample,
        BridgeData.frozenAmbientWeight
          (bankPaperCanonicalBridgeFrozenValue
            (B := B)
            (fixed := R.paperFixedExceptionalFactors deltaStar)
            (candidates := R.roughCanonicalGuardedCandidateSet
              certificate deltaStar K))
          (bankPaperCanonicalBridgeFrozenCoordinateWeight
            (B := B) (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            selector) (B.sampleData.value m) +
          Real.exp (2 * Rbound) * B.baseline.baseWeight m <= 1 := by
  obtain ⟨selector, S, hbaseline⟩ := H
  let fixed := R.paperFixedExceptionalFactors deltaStar
  let candidates :=
    R.roughCanonicalGuardedCandidateSet certificate deltaStar K
  have hactiveSmooth : bankPaperCanonicalBridgeActiveValues B ⊆
      R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    bankPaperCanonicalBridgeActiveValues_subset_guardedSmoothRow
      B R certificate deltaStar hKh hlower hupper hnotGuard
  have hactiveCandidates : bankPaperCanonicalBridgeActiveValues B ⊆
      candidates := by
    intro a ha
    exact (mem_completeRoughRowFiber.mp (hactiveSmooth ha)).1
  have hfixedActive : Disjoint fixed
      (bankPaperCanonicalBridgeActiveValues B) :=
    paperFixedExceptionalFactors_disjoint_bridgeActiveValues
      B R deltaStar hupper
  have hfixedCandidates : Disjoint fixed candidates := by
    simpa only [fixed, candidates] using
      paperFixedExceptionalFactors_disjoint_guardedCandidates
        (K := K) B R certificate deltaStar
  obtain ⟨smoothQuota, hsmoothQuota⟩ :=
    exists_bankPaperCanonicalSmoothQuota_of_rowIntegral S.2.1
  obtain ⟨quota, hquota⟩ :=
    exists_bankPaperCanonicalBridgeIntegerQuota B fixed candidates selector
      hfixedCandidates hactiveCandidates hsep hbaseline S.2.1
  have hfrozen : forall a,
      bankPaperCanonicalBridgeFrozenWeight B fixed candidates selector a ∈
        Set.Icc (0 : Real) 1 :=
    bankPaperCanonicalBridgeFrozenWeight_mem_Icc
      B fixed candidates selector S.1
  have hfrozenAmbient : forall a,
      BridgeData.frozenAmbientWeight
        (bankPaperCanonicalBridgeFrozenValue
          (B := B) (fixed := fixed) (candidates := candidates))
        (bankPaperCanonicalBridgeFrozenCoordinateWeight
          (B := B) fixed candidates selector) a ∈ Set.Icc (0 : Real) 1 := by
    intro a
    rw [frozenAmbientWeight_eq_bankPaperCanonicalBridgeFrozenWeight
      B fixed candidates selector a]
    exact hfrozen a
  have hfrozenZero : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
        (bankPaperCanonicalBridgeFrozenValue
          (B := B) (fixed := fixed) (candidates := candidates))
        (bankPaperCanonicalBridgeFrozenCoordinateWeight
          (B := B) fixed candidates selector)
        (B.sampleData.value m) = 0 := by
    intro m
    rw [frozenAmbientWeight_eq_bankPaperCanonicalBridgeFrozenWeight
      B fixed candidates selector]
    exact bankPaperCanonicalBridgeFrozenWeight_eq_zero_on_sample
      B fixed candidates selector hfixedActive m
  have hslackDirect := bankPaperCanonicalBridge_combinedBaselineSlack
    B fixed candidates selector hfixedActive Cactive Rbound
      hactive hlarge
  have hslack : forall m : B.sampleData.Sample,
      BridgeData.frozenAmbientWeight
        (bankPaperCanonicalBridgeFrozenValue
          (B := B) (fixed := fixed) (candidates := candidates))
        (bankPaperCanonicalBridgeFrozenCoordinateWeight
          (B := B) fixed candidates selector)
        (B.sampleData.value m) +
          Real.exp (2 * Rbound) * B.baseline.baseWeight m <= 1 := by
    intro m
    rw [frozenAmbientWeight_eq_bankPaperCanonicalBridgeFrozenWeight
      B fixed candidates selector]
    exact hslackDirect m
  refine ⟨selector, smoothQuota, quota, S, ?_, hbaseline, hactiveSmooth,
    ?_, ?_, ?_, ?_⟩
  · exact hsmoothQuota
  · simpa only [fixed, candidates] using hfrozenAmbient
  · simpa only [fixed, candidates] using hfrozenZero
  · simpa only [fixed, candidates] using hquota
  · simpa only [fixed, candidates] using hslack

/-- Ready-to-use feasibility of the actual frozen-plus-active bridge
coordinates.  It is a direct specialization of the proved baseline-slack
interface. -/
theorem bankPaperCanonicalBridge_ambientCombinedWeight_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hselector : ∀ a ∈ candidates,
      0 <= selector a ∧ selector a <= 1)
    (hfixedActive : Disjoint fixed
      (bankPaperCanonicalBridgeActiveValues B))
    (xi : B.ParamSpace) (radius Cstat Cactive : Real)
    (hxi : norm xi <= radius) (hCstat : 0 <= Cstat)
    (hstat : forall m : B.sampleData.Sample,
      norm (B.statistic m) <= Cstat * B.L)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hlarge : Real.exp (2 * (Cstat * radius)) * Cactive <= B.L) :
    forall a : Nat,
      B.ambientCombinedWeight
          (bankPaperCanonicalBridgeFrozenWeight
            B fixed candidates selector) xi a ∈ Set.Icc (0 : Real) 1 := by
  apply B.ambientCombinedWeight_mem_Icc_of_div_log_bounds
    hsep (bankPaperCanonicalBridgeFrozenWeight B fixed candidates selector)
    (bankPaperCanonicalBridgeFrozenWeight_mem_Icc
      B fixed candidates selector hselector)
    xi radius Cstat 0 Cactive hxi hCstat hstat
  · intro m
    rw [bankPaperCanonicalBridgeFrozenWeight_eq_zero_on_sample
      B fixed candidates selector hfixedActive m]
    exact div_nonneg (le_refl 0) (le_of_lt B.L_pos)
  · exact hactive
  · simpa using hlarge

end

end Erdos390.WholePaper
