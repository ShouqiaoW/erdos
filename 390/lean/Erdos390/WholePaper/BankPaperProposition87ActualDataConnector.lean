import Erdos390.WholePaper.BankPaperProposition87EndpointSelector
import Erdos390.WholePaper.BankPaperCanonicalGuardedBridgeConnector
import Erdos390.WholePaper.BankPaperCanonicalGuardedSectionNineContinuation
import Erdos390.WholePaper.BankPaperCanonicalPrefixAdapter

/-!
# Actual paper data at the Proposition 8.7 / guarded-selector interface

The paper does not use the mass-one normalization of the bridge.  Its
literal active weights are the numbers `z_m^0`, and

`q_n = sum_m z_m^0`.

At a clean numerical coordinate the protected frozen layer may overlap the
active layer.  Consequently `q_n` is not, in general, the sum of the whole
guarded selector on the active support.  This module keeps the two layers
separate.  Every guarded candidate is represented by a frozen tag of weight

`preSelector a - activeSeedAmbient a`,

while Proposition 8.7 evolves the active seed.  Thus the protected overlap
is retained exactly and the combined selector at time zero is the supplied
guarded pre-selector.

The single construction still missing from the finite guarded ledger is
named `BankPaperCanonicalActualActiveMeasureConstructor`.  It asks only for
the paper's active-measure realization: the seed has the canonical
barycentric shape, has eventual paper-scale mass at least one, is supported
on the guarded candidates, and is dominated by the already feasible
pre-selector.  Row integrality, target agreement, band balance, support,
pointwise estimates, and prefix estimates are not repeated in this
constructor; they are derived below from the existing guarded selector and
the Proposition 8.7 path.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The literal active mass and its sole construction socket -/

/-- The paper's literal active mass `q_n = sum_m z_m^0`.  The summation is
over the tagged structured sample, before any protected contribution at the
same natural-number coordinate is adjoined. -/
def bankPaperCanonicalLiteralActiveMass
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real) : Real :=
  ∑ m, activeSeed m

/-- The ambient push-forward of the literal active seed.  Collisions are
summed rather than silently discarded; the paper head-simplex data later
make the value map injective. -/
def bankPaperCanonicalActiveSeedAmbientWeight
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) : Real :=
  ∑ m : D.Sample, if D.value m = a then activeSeed m else 0

/-- The one paper-data constructor not supplied by the guarded row ledger.

It is exactly the baseline active-measure realization of Section 8:

* `q_n` is at least one (the eventual consequence of `q_n asymp n/log n`);
* every `z_m^0` has the scaled canonical barycentric form;
* every active coordinate is an actual guarded candidate; and
* the active seed is dominated by the total pre-selector, leaving a
  nonnegative frozen protected remainder.

No quota, row-integrality, prime-target, band, or prefix conclusion occurs
in this predicate. -/
def BankPaperCanonicalActualActiveMeasureConstructor
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real) : Prop :=
  let q := bankPaperCanonicalLiteralActiveMass D activeSeed
  1 <= q ∧
    (forall m : D.Sample,
      activeSeed m = q * T.baseline.baseWeight m) ∧
    (∀ m : D.Sample, D.value m ∈ candidates) ∧
    ∀ a ∈ candidates,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a <=
        preSelector a

/-- The literal mass extracted from the actual active-measure constructor
is at least one. -/
theorem bankPaperCanonicalLiteralActiveMass_one_le
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    1 <= bankPaperCanonicalLiteralActiveMass D activeSeed := by
  exact H.1

/-- In particular, the literal active mass is positive. -/
theorem bankPaperCanonicalLiteralActiveMass_pos
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    0 < bankPaperCanonicalLiteralActiveMass D activeSeed :=
  zero_lt_one.trans_le (bankPaperCanonicalLiteralActiveMass_one_le H)

/-- Projection of the exact scaled barycentric formula for the active seed. -/
theorem bankPaperCanonicalActiveSeed_eq_mass_mul_baseline
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) :
    activeSeed m =
      bankPaperCanonicalLiteralActiveMass D activeSeed *
        T.baseline.baseWeight m := by
  exact H.2.1 m

/-- Every active sample coordinate lies in the literal guarded candidate
set selected for the prebridge. -/
theorem bankPaperCanonicalActiveSeed_value_mem_candidates
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) : D.value m ∈ candidates := by
  exact H.2.2.1 m

/-- The active seed is nonnegative coordinatewise. -/
theorem bankPaperCanonicalActiveSeed_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (m : D.Sample) : 0 <= activeSeed m := by
  rw [bankPaperCanonicalActiveSeed_eq_mass_mul_baseline H m]
  exact mul_nonneg
    (zero_le_one.trans (bankPaperCanonicalLiteralActiveMass_one_le H))
    (T.baseline.baseWeight_nonneg m)

/-- The ambient seed is dominated by the guarded pre-selector on every
candidate coordinate. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    {a : Nat} (ha : a ∈ candidates) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a <=
      preSelector a := by
  exact H.2.2.2 a ha

/-- The literal `q_n` associated with a family of actual structured active
seeds. -/
def bankPaperCanonicalLiteralQMass
    {Head : Type*} [Fintype Head]
    (D : Nat -> StructuredSampleData Head)
    (activeSeed : forall n, (D n).Sample -> Real) (n : Nat) : Real :=
  bankPaperCanonicalLiteralActiveMass (D n) (activeSeed n)

/-- An eventual family of actual active-measure realizations gives the
precise mass-uniformity input `1 <= q_n` required by the varying-mass
Proposition 8.7 theorem. -/
theorem eventually_one_le_bankPaperCanonicalLiteralQMass
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (H : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n)) :
    ∀ᶠ n : Nat in atTop,
      1 <= bankPaperCanonicalLiteralQMass D activeSeed n := by
  filter_upwards [H] with n hn
  exact bankPaperCanonicalLiteralActiveMass_one_le hn

/-- Direct paper-data instantiation of the reviewed varying-active-mass
Proposition 8.7 package.  The only use of the actual-measure constructor is
to discharge its eventual `1 <= q_n` input. -/
theorem canonical_proposition87_actualPaperData
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : Nat -> StructuredSampleData Head)
    (T : forall n, BarycentricTarget (D n))
    (candidates : Nat -> Finset Nat)
    (preSelector : Nat -> Nat -> Real)
    (activeSeed : forall n, (D n).Sample -> Real)
    (H : ∀ᶠ n : Nat in atTop,
      BankPaperCanonicalActualActiveMeasureConstructor
        (D n) (T n) (candidates n) (preSelector n) (activeSeed n))
    (cMesh : Real) (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) :
    CanonicalProposition87VaryingActiveMassLiteralBalanceStatement
      (bankPaperCanonicalLiteralQMass D activeSeed)
      cMesh I U Cprom Cbank ledger := by
  exact BridgeData.canonical_proposition87_varyingActiveMassLiteralBandBalance
    (bankPaperCanonicalLiteralQMass D activeSeed)
    (eventually_one_le_bankPaperCanonicalLiteralQMass
      D T candidates preSelector activeSeed H)
    cMesh I U Cprom Cbank ledger

/-! ## The actual scaled bridge data -/

/-- Canonical regular-mesh bridge data whose baseline is the paper's actual
active seed and whose total mass is the literal `q_n`. -/
def bankPaperCanonicalActualBridgeData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    BridgeData Head (Fin (M.cellCount + 1)) :=
  bankPaperCanonicalActiveMassBridgeData D T
    (bankPaperCanonicalLiteralActiveMass D activeSeed)
    (bankPaperCanonicalLiteralActiveMass_pos H)
    M hdelta hn hW S referenceHead hw

@[simp] theorem bankPaperCanonicalActualBridgeData_sampleData
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActualBridgeData D T candidates preSelector activeSeed
      H M hdelta hn hW S referenceHead hw).sampleData = D :=
  rfl

@[simp] theorem bankPaperCanonicalActualBridgeData_q
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta) :
    (bankPaperCanonicalActualBridgeData D T candidates preSelector activeSeed
      H M hdelta hn hW S referenceHead hw).q =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  exact bankPaperCanonicalActiveMassBridgeData_q
    D T (bankPaperCanonicalLiteralActiveMass D activeSeed)
      (bankPaperCanonicalLiteralActiveMass_pos H)
    M hdelta hn hW S referenceHead hw

@[simp] theorem bankPaperCanonicalActualBridgeData_baseWeight
    {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
    {delta eta : Real}
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (M : Mesh delta eta) (hdelta : 0 < delta)
    (hn : 1 < D.n) (hW : D.W ≠ 0)
    (S : ScaleSeparation M D.n D.W)
    (referenceHead : Head) (hw : 0 < delta + eta)
    (m : D.Sample) :
    (bankPaperCanonicalActualBridgeData D T candidates preSelector activeSeed
      H M hdelta hn hW S referenceHead hw).baseline.baseWeight m =
        activeSeed m := by
  unfold bankPaperCanonicalActualBridgeData
  rw [bankPaperCanonicalActiveMassBridgeData_baseline,
    T.activeMassBaseline_baseWeight]
  exact (bankPaperCanonicalActiveSeed_eq_mass_mul_baseline H m).symm

/-! ## Tagged frozen remainder and exact push-forward -/

/-- Every guarded candidate is retained as a frozen tag.  On an active
coordinate its weight is the protected remainder; away from the active
support it is the whole pre-selector weight. -/
abbrev BankPaperCanonicalActualFrozenIndex (candidates : Finset Nat) :=
  ↑candidates

/-- Natural-number coordinate of an actual frozen candidate tag. -/
def bankPaperCanonicalActualFrozenValue
    {candidates : Finset Nat} :
    BankPaperCanonicalActualFrozenIndex candidates -> Nat :=
  fun a => a.1

/-- Frozen protected remainder on one tagged candidate. -/
def bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (candidates : Finset Nat)
    (preSelector : Nat -> Real) (activeSeed : D.Sample -> Real)
    (a : BankPaperCanonicalActualFrozenIndex candidates) : Real :=
  preSelector a.1 -
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a.1

/-- The ambient active seed is nonnegative. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_nonneg
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) (a : Nat) :
    0 <= bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_nonneg
  intro m _hm
  split_ifs
  · exact bankPaperCanonicalActiveSeed_nonneg H m
  · exact le_rfl

/-- The ambient active seed vanishes off the candidate set. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_mem
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    {a : Nat} (ha : a ∉ candidates) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg]
  intro hma
  apply ha
  rw [← hma]
  exact bankPaperCanonicalActiveSeed_value_mem_candidates H m

/-- Summing the ambient push-forward over all guarded candidates recovers
the tagged active mass exactly, even before using value-map injectivity. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a ∈ candidates,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
    bankPaperCanonicalLiteralActiveMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (bankPaperCanonicalActiveSeed_value_mem_candidates H m)).elim

/-- The tagged frozen layer pushes forward to the literal protected
remainder `preSelector - activeSeedAmbient` on candidates and to zero
elsewhere. -/
theorem frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (candidates : Finset Nat)
    (preSelector : Nat -> Real) (activeSeed : D.Sample -> Real)
    (a : Nat) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          D candidates preSelector activeSeed) a =
      if a ∈ candidates then
        preSelector a -
          bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a
      else 0 := by
  classical
  unfold BridgeData.frozenAmbientWeight
    bankPaperCanonicalActualFrozenValue
    bankPaperCanonicalActualFrozenWeight
  by_cases ha : a ∈ candidates
  · rw [if_pos ha, Finset.sum_eq_single (⟨a, ha⟩ : ↑candidates)]
    · simp
    · intro b _hb hba
      rw [if_neg]
      intro hvalue
      exact hba (Subtype.ext hvalue)
    · simp
  · rw [if_neg ha]
    apply Finset.sum_eq_zero
    intro b _hb
    rw [if_neg]
    intro hvalue
    apply ha
    rw [← hvalue]
    exact b.2

/-- Feasibility of the guarded pre-selector and dominance of the active
seed imply feasibility of the complete frozen protected remainder. -/
theorem bankPaperCanonicalActualFrozenWeight_mem_Icc
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (hselector : ∀ a ∈ candidates,
      0 <= preSelector a ∧ preSelector a <= 1) :
    forall a,
      BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          D candidates preSelector activeSeed) a ∈ Set.Icc (0 : Real) 1 := by
  intro a
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
  by_cases ha : a ∈ candidates
  · rw [if_pos ha]
    constructor
    · exact sub_nonneg.mpr
        (bankPaperCanonicalActiveSeedAmbientWeight_le_preSelector H ha)
    · exact (sub_le_self _
        (bankPaperCanonicalActiveSeedAmbientWeight_nonneg H a)).trans
          (hselector a ha).2
  · simp [ha]

/-- The total frozen remainder is the pre-selector mass minus the literal
active mass. -/
theorem sum_bankPaperCanonicalActualFrozenWeight
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
        D candidates preSelector activeSeed a) =
      (∑ a ∈ candidates, preSelector a) -
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActualFrozenWeight
  rw [Finset.sum_sub_distrib]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => preSelector a)]
  rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
    (fun a => bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a)]
  rw [sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass H]

/-- Complete-rough-row integrality of the guarded selector supplies the
integer total quota required by Proposition 8.7, with no new quota premise. -/
theorem exists_bankPaperCanonicalActualP87IntegerQuota
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      D.n candidates preSelector) :
    ∃ quota : Int,
      (quota : Real) =
        (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
            D candidates preSelector activeSeed a) +
          bankPaperCanonicalLiteralActiveMass D activeSeed := by
  obtain ⟨quota, hquota⟩ :=
    exists_bankPaperCanonicalTotalQuota_of_rowIntegral hrow
  refine ⟨quota, ?_⟩
  rw [sum_bankPaperCanonicalActualFrozenWeight H]
  linarith

/-! ## The initial combined selector -/

/-- At parameter zero the bridge active weight is exactly its supplied
baseline coordinate weight. -/
theorem BridgeData.activeCoordinateWeight_zero_eq_baseline
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (m : B.sampleData.Sample) :
    B.activeCoordinateWeight 0 m = B.baseline.baseWeight m := by
  unfold Erdos390.Full.PaperBridgeFit.BridgeData.activeCoordinateWeight
    Erdos390.Full.FiniteExponentialFamily.activeWeight
  change B.vectorFamily.baseMass * B.vectorFamily.probabilityMass 0 m =
    B.baseline.baseWeight m
  rw [
    Erdos390.Full.PaperBridgeFit.BridgeData.probabilityMass_zero B m,
    Erdos390.Full.PaperBridgeFit.BridgeData.vectorFamily_baseMass B]
  field_simp [ne_of_gt B.q_pos]

/-- If the bridge baseline is the actual seed, its ambient time-zero active
layer is the ambient push-forward of that seed. -/
theorem BridgeData.ambientActiveWeight_zero_eq_activeSeedAmbient
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (activeSeed : B.sampleData.Sample -> Real)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (a : Nat) :
    B.ambientActiveWeight 0 a =
      bankPaperCanonicalActiveSeedAmbientWeight
        B.sampleData activeSeed a := by
  unfold BridgeData.ambientActiveWeight
    bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_congr rfl
  intro m _hm
  rw [
    Erdos390.WholePaper.BridgeData.activeCoordinateWeight_zero_eq_baseline
      B m,
    hseed m]

/-- With the frozen protected remainder retained, the combined bridge at
time zero is exactly the guarded pre-selector on candidates and zero off
the candidate set. -/
theorem bankPaperCanonicalActualSelectorAt_zero_eq_preSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace) (t : Real) (ht : path t = 0)
    (a : Nat) :
    bankPaperProposition87SelectorAt B
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        path t a =
      if a ∈ candidates then preSelector a else 0 := by
  unfold bankPaperProposition87SelectorAt
    BridgeData.ambientCombinedWeight
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight, ht,
    Erdos390.WholePaper.BridgeData.ambientActiveWeight_zero_eq_activeSeedAmbient
      B activeSeed hseed a]
  by_cases ha : a ∈ candidates
  · rw [if_pos ha]
    simp [ha]
  · rw [if_neg ha,
      bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_mem H ha]
    simp [ha]

/-- The finite support used by the pushed-forward Proposition 8.7 selector
is exactly the literal guarded candidate set. -/
theorem bankPaperCanonicalActualP87SelectorSupport_eq_candidates
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (candidates : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates) :
    bankPaperProposition87SelectorSupport B
      (bankPaperCanonicalActualFrozenValue (candidates := candidates)) =
        candidates := by
  classical
  ext a
  constructor
  · intro ha
    rw [bankPaperProposition87SelectorSupport, Finset.mem_union] at ha
    rcases ha with haFrozen | haActive
    · obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp haFrozen
      exact f.2
    · obtain ⟨m, _hm, hma⟩ := Finset.mem_image.mp haActive
      rw [← hma]
      exact hvalues m
  · intro ha
    apply Finset.mem_union_left
    exact Finset.mem_image.mpr ⟨(⟨a, ha⟩ : ↑candidates),
      Finset.mem_univ _, rfl⟩

/-! ## The literal active marked target and endpoint -/

/-- The active target supplied to Proposition 8.7 is the residual selector
target after subtracting the whole tagged frozen candidate layer. -/
def bankPaperCanonicalActualActiveMarkedTarget
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (p : Nat) : Real :=
  ((certificate.selectorTailTarget R fixed).factorization p : Real) -
    ∑ a : BankPaperCanonicalActualFrozenIndex candidates,
      bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed a *
        valuation p (bankPaperCanonicalActualFrozenValue a)

/-- The actual pushed-forward candidate selector at the Proposition 8.7
endpoint. -/
def bankPaperCanonicalActualP87EndpointSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (path : Real -> B.ParamSpace) : Nat -> Real :=
  bankPaperProposition87EndpointSelector B
    (bankPaperCanonicalActualFrozenValue (candidates := candidates))
    (bankPaperCanonicalActualFrozenWeight
      B.sampleData candidates preSelector activeSeed) path

/-- Adding the tagged frozen target contribution back to the active marked
target recovers the literal residual selector target exactly. -/
theorem bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real) (p : Nat) :
    bankPaperProposition87FullMarkedTarget
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed) p =
      ((certificate.selectorTailTarget R fixed).factorization p : Real) := by
  unfold bankPaperProposition87FullMarkedTarget
    bankPaperCanonicalActualActiveMarkedTarget
  ring

/-- The canonical target-minus-selector deficit of the actual endpoint is
literally the active residual appearing in Proposition 8.7. -/
theorem bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) (p : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) p =
      bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) (path 1) := by
  have hres := bankPaperProposition87FullMarkedResidual_eq_activeResidual
    B
    (bankPaperCanonicalActualFrozenValue (candidates := candidates))
    (bankPaperCanonicalActualFrozenWeight
      B.sampleData candidates preSelector activeSeed)
    (bankPaperCanonicalActualActiveMarkedTarget B R certificate
      fixed candidates preSelector activeSeed) path p
  unfold bankPaperProposition87FullMarkedResidual at hres
  rw [bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget,
    bankPaperCanonicalActualP87SelectorSupport_eq_candidates B candidates
      hvalues] at hres
  simpa only [bankPaperCanonicalSelectorValuationDeficit,
    bankPaperCanonicalActualP87EndpointSelector] using hres

/-- At the initial point, the active residual is exactly the prebridge
canonical selector deficit. -/
theorem bankPaperCanonicalActualInitial_deficit_eq_activeResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (p : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        preSelector p =
      bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) 0 := by
  let path0 : Real -> B.ParamSpace := fun _ => 0
  have hendpoint := bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed
    (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m)
    path0 p
  calc
    bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        preSelector p =
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path0) p := by
        unfold bankPaperCanonicalSelectorValuationDeficit
        apply congrArg (fun x : Real =>
          ((certificate.selectorTailTarget R fixed).factorization p : Real) - x)
        apply Finset.sum_congr rfl
        intro a ha
        rw [bankPaperCanonicalActualP87EndpointSelector,
          bankPaperProposition87EndpointSelector,
          bankPaperCanonicalActualSelectorAt_zero_eq_preSelector
            B candidates preSelector activeSeed H hseed path0 1 rfl a,
          if_pos ha]
    _ = bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) 0 := by
      simpa only [path0] using hendpoint

/-- The pushed-forward endpoint has no support outside the guarded candidate
set. -/
theorem bankPaperCanonicalActualP87EndpointSelector_eq_zero_of_not_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) {a : Nat} (ha : a ∉ candidates) :
    bankPaperCanonicalActualP87EndpointSelector
      B candidates preSelector activeSeed path a = 0 := by
  unfold bankPaperCanonicalActualP87EndpointSelector
    bankPaperProposition87EndpointSelector
  apply bankPaperProposition87SelectorAt_eq_zero_of_not_mem_support
  rw [bankPaperCanonicalActualP87SelectorSupport_eq_candidates
    B candidates hvalues]
  exact ha

/-! ## Smooth active support and unchanged complete-rough rows -/

/-- Every actual structured bridge coordinate lies in complete rough row
`1` of the guarded candidate set. -/
theorem bankPaperCanonicalActualActiveValues_subset_smoothRow
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (candidates : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates) :
    bankPaperCanonicalBridgeActiveValues B ⊆
      completeRoughRowFiber (yNat B.sampleData.n) candidates 1 := by
  intro a ha
  obtain ⟨m, hma⟩ := mem_bankPaperCanonicalBridgeActiveValues.mp ha
  subst a
  apply mem_completeRoughRowFiber.mpr
  exact ⟨hvalues m,
    (completeRoughLabel_eq_one_iff_mem_smoothNumbers
      (B.sampleData.value_pos m)).mpr
        (B.sampleData.value_mem_smoothNumbers m)⟩

/-- A prime above the smooth cutoff has zero valuation on every structured
active coordinate. -/
theorem StructuredSampleData.valuation_eq_zero_of_yNat_lt
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (m : D.Sample)
    {p : Nat} (hp : p.Prime) (hpy : yNat D.n < p) :
    valuation p (D.value m) = 0 := by
  unfold valuation
  have hnotDvd : ¬ p ∣ D.value m := by
    intro hpdvd
    have hpFactors : p ∈ (D.value m).primeFactors :=
      hp.mem_primeFactors hpdvd (Nat.ne_of_gt (D.value_pos m))
    have hpBelow := Nat.primeFactors_subset_of_mem_smoothNumbers
      (D.value_mem_smoothNumbers m) hpFactors
    have hpLt : p < yNat D.n + 1 := (Nat.mem_primesBelow.mp hpBelow).1
    omega
  exact_mod_cast Nat.factorization_eq_zero_of_not_dvd hnotDvd

/-- Hence every active marked moment at such a prime is zero at every bridge
parameter. -/
theorem BridgeData.paperMoment_markedValuation_eq_zero_of_yNat_lt
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (xi : B.ParamSpace)
    {p : Nat} (hp : p.Prime) (hpy : yNat B.sampleData.n < p) :
    B.paperMoment (B.markedValuation p) xi = 0 := by
  unfold BridgeData.paperMoment FiniteExponentialFamily.moment
  apply Finset.sum_eq_zero
  intro m _hm
  rw [show B.markedValuation p m = 0 by
    exact
      Erdos390.WholePaper.StructuredSampleData.valuation_eq_zero_of_yNat_lt
        B.sampleData m hp hpy]
  ring

/-- Push-forward mass over any finite set containing every active sample
value is the total tagged seed mass. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (support : Finset Nat)
    (hvalues : ∀ m : D.Sample, D.value m ∈ support) :
    (∑ a ∈ support,
      bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) =
        bankPaperCanonicalLiteralActiveMass D activeSeed := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
    bankPaperCanonicalLiteralActiveMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (hvalues m)).elim

/-- The active seed push-forward vanishes at a coordinate which is not the
value of any active sample tag. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (activeSeed : D.Sample -> Real)
    (a : Nat) (ha : forall m : D.Sample, D.value m ≠ a) :
    bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a = 0 := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_eq_zero
  intro m _hm
  rw [if_neg (ha m)]

/-- The live bridge layer has total mass `B.q` on any finite set containing
all active sample values. -/
theorem BridgeData.sum_ambientActiveWeight_eq_q_of_values_mem
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band) (xi : B.ParamSpace)
    (support : Finset Nat)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ support) :
    (∑ a ∈ support, B.ambientActiveWeight xi a) = B.q := by
  classical
  unfold BridgeData.ambientActiveWeight
  rw [Finset.sum_comm]
  calc
    (∑ m : B.sampleData.Sample,
      ∑ a ∈ support,
        if B.sampleData.value m = a then
          B.activeCoordinateWeight xi m else 0) =
        ∑ m : B.sampleData.Sample, B.activeCoordinateWeight xi m := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [Finset.sum_eq_single (B.sampleData.value m)]
      · simp
      · intro a _ha hne
        simp [hne.symm]
      · intro hnot
        exact (hnot (hvalues m)).elim
    _ = B.q := B.sum_activeCoordinateWeight xi

/-- Installing the literal seed as the bridge baseline identifies `B.q`
with the paper's literal active mass. -/
theorem BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (activeSeed : B.sampleData.Sample -> Real)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m) :
    B.q = bankPaperCanonicalLiteralActiveMass B.sampleData activeSeed := by
  calc
    B.q = ∑ m : B.sampleData.Sample, B.baseline.baseWeight m := by
      exact B.baseline.baseWeight_sum.symm
    _ = ∑ m : B.sampleData.Sample, activeSeed m := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact hseed m
    _ = bankPaperCanonicalLiteralActiveMass B.sampleData activeSeed := rfl

/-- Pointwise form of the actual endpoint on candidate coordinates: frozen
protected remainder plus the live active layer.  It vanishes outside the
candidate set. -/
theorem bankPaperCanonicalActualP87EndpointSelector_eq
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) (a : Nat) :
    bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path a =
      if a ∈ candidates then
        preSelector a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a +
          B.ambientActiveWeight (path 1) a
      else 0 := by
  unfold bankPaperCanonicalActualP87EndpointSelector
    bankPaperProposition87EndpointSelector
    bankPaperProposition87SelectorAt
    BridgeData.ambientCombinedWeight
  rw [frozenAmbientWeight_eq_bankPaperCanonicalActualFrozenWeight]
  by_cases ha : a ∈ candidates
  · simp [ha]
  ·
    have hnotValue : forall m : B.sampleData.Sample,
        B.sampleData.value m ≠ a := by
      intro m hma
      apply ha
      rw [← hma]
      exact hvalues m
    rw [B.ambientActiveWeight_eq_zero_of_not_value
      (path 1) a hnotValue]
    simp [ha]

/-- Every complete-rough-row mass of the endpoint equals the corresponding
prebridge row mass.  On nonsmooth rows both active terms vanish; on the
smooth row their common total is the fixed literal mass `q_n`. -/
theorem sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace) (label : Nat) :
    (∑ a ∈ completeRoughRowFiber
        (yNat B.sampleData.n) candidates label,
      bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path a) =
      ∑ a ∈ completeRoughRowFiber
        (yNat B.sampleData.n) candidates label,
        preSelector a := by
  classical
  let row := completeRoughRowFiber
    (yNat B.sampleData.n) candidates label
  have hrowCandidates : row ⊆ candidates := by
    intro a ha
    exact (mem_completeRoughRowFiber.mp ha).1
  have hpoint : ∀ a ∈ row,
      bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path a =
        preSelector a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a +
          B.ambientActiveWeight (path 1) a := by
    intro a ha
    rw [bankPaperCanonicalActualP87EndpointSelector_eq
      B candidates preSelector activeSeed
        (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m)
      path a, if_pos (hrowCandidates ha)]
  have hsplit :
      (∑ a ∈ row,
        bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path a) =
        (∑ a ∈ row, preSelector a) -
          (∑ a ∈ row,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData activeSeed a) +
          ∑ a ∈ row, B.ambientActiveWeight (path 1) a := by
    calc
      _ = ∑ a ∈ row,
          (preSelector a -
              bankPaperCanonicalActiveSeedAmbientWeight
                B.sampleData activeSeed a +
            B.ambientActiveWeight (path 1) a) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hpoint a ha
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [hsplit]
  by_cases hlabel : label = 1
  · subst label
    have hactiveValues :=
      bankPaperCanonicalActualActiveValues_subset_smoothRow B candidates
        (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m)
    have hseedMass :=
      sum_bankPaperCanonicalActiveSeedAmbientWeight_eq_activeMass_of_subset
        B.sampleData activeSeed row (fun m => by
          apply hactiveValues
          exact mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩)
    have hactiveMass :=
      Erdos390.WholePaper.BridgeData.sum_ambientActiveWeight_eq_q_of_values_mem
        B (path 1) row (fun m => by
          apply hactiveValues
          exact mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩)
    rw [hseedMass, hactiveMass,
      Erdos390.WholePaper.BridgeData.q_eq_literalActiveMass_of_baseWeight_eq_seed
        B activeSeed hseed]
    ring
  · have hnotRow : forall m : B.sampleData.Sample,
        B.sampleData.value m ∉ row := by
      intro m hm
      have hmLabel := (mem_completeRoughRowFiber.mp hm).2
      have hmOne := (completeRoughLabel_eq_one_iff_mem_smoothNumbers
        (B.sampleData.value_pos m)).mpr
          (B.sampleData.value_mem_smoothNumbers m)
      exact hlabel (hmLabel.symm.trans hmOne)
    have hseedZero :
        (∑ a ∈ row,
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData activeSeed a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      apply hnotRow m
      rw [hma]
      exact ha
    have hactiveZero :
        (∑ a ∈ row, B.ambientActiveWeight (path 1) a) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      apply B.ambientActiveWeight_eq_zero_of_not_value
      intro m hma
      apply hnotRow m
      rw [hma]
      exact ha
    rw [hseedZero, hactiveZero]
    ring

/-- Proposition 8.7 preserves not just smooth-row integrality but the exact
integer quota installed by the prebridge placement.  This is the second
half of the concrete quota-construction bridge: after the additive smooth
placement chooses the nearest-integer quota, the actual endpoint keeps it
unchanged. -/
theorem bankPaperCanonicalGuardedSmoothFlexibleQuota_actualP87Endpoint
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace) (smoothQuota : Int)
    (hquota :
      BankPaperRealization.BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K preSelector smoothQuota) :
    BankPaperRealization.BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
        (bankPaperCanonicalActualP87EndpointSelector B
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          preSelector activeSeed path) smoothQuota := by
  unfold
    BankPaperRealization.BankPaperCanonicalGuardedSmoothFlexibleQuota
      at hquota ⊢
  unfold BankPaperRealization.roughCanonicalGuardedRow at hquota ⊢
  rw [sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector
    B (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      preSelector activeSeed H hseed path 1]
  exact hquota

/-- Therefore complete-rough-row integrality is preserved by the actual
Proposition 8.7 endpoint. -/
theorem bankPaperCanonicalActualP87EndpointSelector_rowIntegral
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {T : BarycentricTarget B.sampleData}
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates preSelector) :
    BankPaperCanonicalSelectorRowIntegral B.sampleData.n candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) := by
  intro label hlabel
  obtain ⟨k, hk⟩ := hrow label hlabel
  refine ⟨k, ?_⟩
  rw [sum_bankPaperCanonicalActualP87EndpointSelector_row_eq_preSelector
    B candidates preSelector activeSeed H hseed path label]
  exact hk

/-! ## Prime support, exact bands, and the derived prefix ledger -/

/-- The literal primewise majorant emitted by Proposition 8.7. -/
def bankPaperCanonicalActualP87PointwiseUpper
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (N Cpost : Real)
    (p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W) : Real :=
  Cpost * N / ((p.1 : Real) * B.L)

/-- Exact target agreement outside `W < p <= y` is preserved by the
Proposition 8.7 endpoint.  Low-prime active moments are explicit P87
invariants; above `y` every active marked valuation is identically zero. -/
theorem bankPaperCanonicalActualP87EndpointSelector_deficitSupportedOnPrimeBand
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hpre : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (hsmall : forall p : Nat, p.Prime -> p <= B.sampleData.W ->
      B.paperMoment (B.markedValuation p) (path 1) =
        B.paperMoment (B.markedValuation p) 0) :
    BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) := by
  intro p hp hnotBand
  have hendpoint := bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed
    (fun m => bankPaperCanonicalActiveSeed_value_mem_candidates H m) path p
  have hinitial := bankPaperCanonicalActualInitial_deficit_eq_activeResidual
    B R certificate fixed candidates preSelector activeSeed H hseed p
  have hpreZero := hpre p hp hnotBand
  by_cases hpW : p <= B.sampleData.W
  · calc
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p =
        bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) (path 1) := hendpoint
      _ = bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) 0 := by rw [hsmall p hp hpW]
      _ = bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates preSelector p := hinitial.symm
      _ = 0 := hpreZero
  · have hWp : B.sampleData.W < p := Nat.lt_of_not_ge hpW
    have hyp : yNat B.sampleData.n < p := by
      by_contra hnotY
      have hpY : p <= yNat B.sampleData.n := Nat.le_of_not_gt hnotY
      exact hnotBand (mem_primeBand.mpr ⟨hp, hWp, hpY⟩)
    have hzeroOne :=
      BridgeData.paperMoment_markedValuation_eq_zero_of_yNat_lt
        B (path 1) hp hyp
    have hzeroZero :=
      BridgeData.paperMoment_markedValuation_eq_zero_of_yNat_lt
        B 0 hp hyp
    calc
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
          (bankPaperCanonicalActualP87EndpointSelector
            B candidates preSelector activeSeed path) p =
        bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) (path 1) := hendpoint
      _ = bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p -
          B.paperMoment (B.markedValuation p) 0 := by
        rw [hzeroOne, hzeroZero]
      _ = bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates preSelector p := hinitial.symm
      _ = 0 := hpreZero

/-- The exact P87 residual cancellation in every arithmetic prime band is
the exact band balance required by the canonical tangent interface. -/
theorem bankPaperCanonicalActualP87EndpointSelector_bandBalance
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace)
    (hbands : forall band : Band,
      B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed) (path 1) band = 0) :
    forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if B.partition.band p = band then
          bankPaperCanonicalTangentResidual R certificate fixed candidates
            (bankPaperCanonicalActualP87EndpointSelector
              B candidates preSelector activeSeed path) p
        else 0) = 0 := by
  intro band
  rw [← Finset.sum_filter]
  change (∑ p ∈ B.partition.data.fiber band,
    bankPaperCanonicalTangentResidual R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) p) = 0
  calc
    _ = ∑ p ∈ B.partition.data.fiber band,
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
            fixed candidates preSelector activeSeed p.1 -
          B.paperMoment (B.markedValuation p.1) (path 1)) := by
      apply Finset.sum_congr rfl
      intro p _hp
      exact bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
        B R certificate fixed candidates preSelector activeSeed hvalues path p.1
    _ = 0 := hbands band

/-- Summing the exact partition-band equations gives the global prime-band
balance field of the rounded-selector tangent input. -/
theorem bankPaperCanonicalActualP87EndpointSelector_primeBandBalance
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (path : Real -> B.ParamSpace)
    (hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if B.partition.band p = band then
          bankPaperCanonicalTangentResidual R certificate fixed candidates
            (bankPaperCanonicalActualP87EndpointSelector
              B candidates preSelector activeSeed path) p
        else 0) = 0) :
    BankPaperCanonicalPostRoundingPrimeBandBalance
      (W := B.sampleData.W) R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) := by
  let residual : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real := fun p =>
    bankPaperCanonicalTangentResidual R certificate fixed candidates
      (bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path) p
  have htotal : (∑ p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W, residual p) = 0 := by
    rw [← Finset.sum_fiberwise Finset.univ B.partition.band residual]
    apply Finset.sum_eq_zero
    intro band _hband
    rw [Finset.sum_filter]
    simpa only [residual] using hbalance band
  unfold BankPaperCanonicalPostRoundingPrimeBandBalance
  calc
    (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
      bankPaperCanonicalSelectorValuationDeficit R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) p) =
      ∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W, residual p := by
        simpa only [Finset.univ_eq_attach, residual,
          bankPaperCanonicalTangentResidual] using
          (Finset.sum_attach (primeBand B.sampleData.n B.sampleData.W)
            (fun p => bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates
                (bankPaperCanonicalActualP87EndpointSelector
                  B candidates preSelector activeSeed path) p)).symm
    _ = 0 := htotal

/-- The P87 primewise rate is exactly the canonical tangent residual rate
for the pushed-forward guarded endpoint. -/
theorem bankPaperCanonicalActualP87EndpointSelector_pointwise
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    (hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates)
    (path : Real -> B.ParamSpace) (N Cpost : Real)
    (hmarked : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed p -
        B.paperMoment (B.markedValuation p) (path 1)) <=
          Cpost * N / ((p : Real) * B.L)) :
    forall p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalTangentResidual R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) p) <=
        bankPaperCanonicalActualP87PointwiseUpper B N Cpost p := by
  intro p
  rw [bankPaperCanonicalTangentResidual,
    bankPaperCanonicalActualEndpoint_deficit_eq_activeResidual
      B R certificate fixed candidates preSelector activeSeed hvalues path p.1]
  exact hmarked p.1 p.2

/-! ## Complete endpoint handoff -/

/-- The actual paper-data endpoint is again a complete guarded
rounded-selector tangent input.

All fields are derived:

* feasibility comes from the P87 path;
* complete-rough-row integrality is preserved by fixed active mass;
* outside-band target agreement combines the low-prime invariants with
  smoothness above `y`;
* exact partition-band balance and the pointwise rate are the literal P87
  residual conclusions; and
* the prefix field is the deterministic pointwise tail sum, obtained by the
  existing prefix adapter rather than postulated independently. -/
theorem exists_bankPaperCanonicalActualP87EndpointSelector
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    {PreBand : Type*} [DecidableEq PreBand]
    (preBandOf : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> PreBand)
    (preCellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (prePointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prePrefixUpper : PreBand -> Nat -> Real)
    (Spre : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates preBandOf preCellIndex
        prePointwiseUpper prePrefixUpper preSelector)
    (Delta : Band -> Real) (radius : NNReal) (N Cpost : Real)
    (quota : Int)
    (Hfit : B.HasPaperProposition87Conclusion Delta radius
      (bankPaperCanonicalActualActiveMarkedTarget B R certificate
        fixed candidates preSelector activeSeed)
      N Cpost
      (bankPaperCanonicalActualFrozenValue (candidates := candidates))
      (bankPaperCanonicalActualFrozenWeight
        B.sampleData candidates preSelector activeSeed)
      quota)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat) :
    ∃ path : Real -> B.ParamSpace, ∃ endpoint : Nat -> Real,
      B.IsPaperProposition87Path Delta radius
        (bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector activeSeed)
        N Cpost
        (bankPaperCanonicalActualFrozenValue (candidates := candidates))
        (bankPaperCanonicalActualFrozenWeight
          B.sampleData candidates preSelector activeSeed)
        quota path ∧
      endpoint = bankPaperCanonicalActualP87EndpointSelector
        B candidates preSelector activeSeed path ∧
      bankPaperProposition87SelectorSupport B
        (bankPaperCanonicalActualFrozenValue (candidates := candidates)) =
          candidates ∧
      (forall p : Nat,
        bankPaperProposition87FullMarkedTarget
            (bankPaperCanonicalActualFrozenValue (candidates := candidates))
            (bankPaperCanonicalActualFrozenWeight
              B.sampleData candidates preSelector activeSeed)
            (bankPaperCanonicalActualActiveMarkedTarget B R certificate
              fixed candidates preSelector activeSeed) p =
          ((certificate.selectorTailTarget R fixed).factorization p : Real)) ∧
      (forall x, x ∉ candidates -> endpoint x = 0) ∧
      BankPaperCanonicalRoundedSelectorTangentInput
        R certificate fixed candidates B.partition.band cellIndex
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
          B.partition.band cellIndex)
        endpoint := by
  obtain ⟨path, hpath, hbands⟩ := Hfit
  let endpoint := bankPaperCanonicalActualP87EndpointSelector
    B candidates preSelector activeSeed path
  have hpathData := hpath
  rcases hpathData with
    ⟨_hzero, _hball, _hsize, _hderiv, _hbandMoments, _hphysical,
      _hlog, _hheads, hsmall, _hprimeLog, hmarked, hfeasible,
      _hfixed, _hmass, _hquota⟩
  have hvalues : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈ candidates :=
    fun m => bankPaperCanonicalActiveSeed_value_mem_candidates Hmeasure m
  have hpreState :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState Spre
  have hselector : ∀ x ∈ candidates,
      0 <= endpoint x ∧ endpoint x <= 1 := by
    intro x _hx
    exact hfeasible 1 (by simp) x
  have hrow : BankPaperCanonicalSelectorRowIntegral
      B.sampleData.n candidates endpoint := by
    exact bankPaperCanonicalActualP87EndpointSelector_rowIntegral
      B candidates preSelector activeSeed Hmeasure hseed path hpreState.2.1
  have hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates endpoint := by
    exact
      bankPaperCanonicalActualP87EndpointSelector_deficitSupportedOnPrimeBand
        B R certificate fixed candidates preSelector activeSeed Hmeasure hseed
        path hpreState.2.2.2 hsmall
  have hbalance : forall band : Band,
      (∑ p : BankPaperCanonicalTangentPrime
          B.sampleData.n B.sampleData.W,
        if B.partition.band p = band then
          bankPaperCanonicalTangentResidual R certificate fixed candidates
            endpoint p
        else 0) = 0 := by
    exact bankPaperCanonicalActualP87EndpointSelector_bandBalance
      B R certificate fixed candidates preSelector activeSeed hvalues path
        hbands
  have hprimeBandBalance : BankPaperCanonicalPostRoundingPrimeBandBalance
      (W := B.sampleData.W) R certificate fixed candidates endpoint := by
    exact bankPaperCanonicalActualP87EndpointSelector_primeBandBalance
      B R certificate fixed candidates preSelector activeSeed path hbalance
  have hpointwise : forall p : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalTangentResidual R certificate fixed candidates
        endpoint p) <= bankPaperCanonicalActualP87PointwiseUpper B N Cpost p := by
    exact bankPaperCanonicalActualP87EndpointSelector_pointwise
      B R certificate fixed candidates preSelector activeSeed hvalues path
        N Cpost hmarked
  have Sendpoint : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
      (tangentRatioCellTailPointwiseUpper
        (bankPaperCanonicalActualP87PointwiseUpper B N Cpost)
        B.partition.band cellIndex)
      endpoint := by
    exact bankPaperCanonicalRoundedSelectorTangentInput_of_balance_pointwise
      R certificate fixed candidates B.partition.band cellIndex
      (bankPaperCanonicalActualP87PointwiseUpper B N Cpost) endpoint
      hselector hrow hprimeBandBalance hsupport hbalance hpointwise
  refine ⟨path, endpoint, hpath, rfl, ?_, ?_, ?_, Sendpoint⟩
  · exact bankPaperCanonicalActualP87SelectorSupport_eq_candidates
      B candidates hvalues
  · intro p
    exact bankPaperCanonicalActualFullMarkedTarget_eq_selectorTailTarget
      B R certificate fixed candidates preSelector activeSeed p
  · intro x hx
    exact bankPaperCanonicalActualP87EndpointSelector_eq_zero_of_not_mem
      B candidates preSelector activeSeed hvalues path hx

/-! ## Direct coupling to the guarded continuation -/

/-- The guarded continuation exposes the exact pre-selector input consumed
by `exists_bankPaperCanonicalActualP87EndpointSelector`, together with its
smooth integer quota, raw-candidate containment, and occupied-cell geometry.
The capacity ledger is retained alongside it.  Thus the continuation and
the actual P87 endpoint theorem compose without renaming a row statement as
an active-measure construction. -/
theorem bankPaperCanonicalGuardedContinuation_with_actualPrebridge
    {c : Real} {depth n W K : Nat}
    {R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n))}
    {certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {deltaStar : Real}
    {Band : Type*} [DecidableEq Band]
    {lastCell : Band -> Nat}
    {bandOf : BankPaperCanonicalTangentPrime n W -> Band}
    {cellIndex : BankPaperCanonicalTangentPrime n W -> Nat}
    {tailLower tailUpper : Band -> Nat -> Nat}
    {scale : Real} {guardBudget poolMinimum : Nat}
    (Hcontinuation :
      BankPaperRealization.BankPaperCanonicalGuardedSectionNineContinuation
      (K := K) R certificate deltaStar lastCell bandOf cellIndex
        tailLower tailUpper scale guardBudget poolMinimum) :
    ((∀ label ∈ completeRoughLabelSet (yNat n)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
      BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel
          n deltaStar label ->
        BankPaperRealization.RoughCanonicalGuardLocalCensusBound
          R certificate deltaStar K label guardBudget) ∧
      (∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel
            n deltaStar label ->
          BankPaperRealization.RoughCanonicalGuardedBroadPoolCapacity
            R certificate deltaStar W K label poolMinimum) ∧
      ∀ label ∈ completeRoughLabelSet (yNat n)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K),
        BankPaperRealization.RoughCanonicalActiveNonexceptionalLabel
            n deltaStar label ->
          BankPaperRealization.RoughCanonicalPostchargeRowCapacity
            R certificate deltaStar K label) ∧
      ∃ smoothFlexibleQuota : Int,
      ∃ preSelector : Nat -> Real,
        BankPaperRealization.BankPaperCanonicalGuardedSmoothFlexibleQuota
            R certificate deltaStar K preSelector smoothFlexibleQuota ∧
          R.roughCanonicalGuardedCandidateSet certificate deltaStar K ⊆
            roughRawCandidateSet n (upperTailLength c n) K ∧
          BankPaperCanonicalRoundedSelectorTangentInput R certificate
            (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
            bandOf cellIndex
            (bankPaperCanonicalHarmonicPointwiseUpper scale)
            (fun band cut => bankPaperCanonicalHarmonicTailMajorant scale
              (tailLower band cut) (tailUpper band cut)) preSelector ∧
          (forall p : BankPaperCanonicalTangentPrime n W,
            cellIndex p <= lastCell (bandOf p)) ∧
          forall band cell, cell <= lastCell band ->
            tangentRatioCellCard bandOf cellIndex band cell ≠ 0 := by
  exact
    ⟨BankPaperRealization.bankPaperCanonicalGuardedSectionNineContinuation_capacityInputs
        Hcontinuation,
      BankPaperRealization.bankPaperCanonicalGuardedSectionNineContinuation_exists_assemblyFrontEnd
        Hcontinuation⟩

end

end Erdos390.WholePaper
