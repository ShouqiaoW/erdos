import Erdos390.WholePaper.BankPaperProposition87ActualDataConnector

/-!
# Constructing the actual active measure and isolating its irreducible fit

The paper's baseline realization has two logically different parts.

* Once a normalized barycentric target and its literal active mass `q_n`
  are fixed, the active coordinates are forced:

  `z_m^0 = q_n * T.baseline.baseWeight m`.

  Their sum is definitionally finite and is proved below to be exactly
  `q_n`.  No analytic or selector input is needed for this part.

* For a *previously fixed* guarded pre-selector, one must still know that
  the pre-selector carries this active mass at every active numerical
  coordinate.  Under the already available head-pattern separation and
  candidate feasibility, this reduces exactly to the coordinatewise
  inequality

  `q_n * T.baseline.baseWeight m <= preSelector (D.value m)`.

The latter is named `BankPaperCanonicalActualCoordinateFit`.  It is the
irreducible coupling absent from `BankPaperCanonicalGuardedSectionNineContinuation`:
that continuation records feasibility, row sums, and prime residuals, but
no pointwise relation between its selector and the later active baseline.

The module also gives a completely unconditional self-selector
construction, proves the guarded-support part from the existing geometry,
and shows that the older guarded bridge selector constructor supplies the
coordinate fit whenever it is instantiated with the literal active-mass
baseline.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## The forced finite active seed -/

/-- The paper's coordinate formula
`z_m^0 = q_n * T.baseline.baseWeight m`. -/
def bankPaperCanonicalScaledActiveSeed
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) (m : D.Sample) : Real :=
  q * T.baseline.baseWeight m

/-- A nonnegative literal mass gives a nonnegative active seed. -/
theorem bankPaperCanonicalScaledActiveSeed_nonneg
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 <= q) (m : D.Sample) :
    0 <= bankPaperCanonicalScaledActiveSeed T q m := by
  exact mul_nonneg hq (T.baseline.baseWeight_nonneg m)

/-- A positive literal mass gives a positive active seed in every
nonempty structured cell. -/
theorem bankPaperCanonicalScaledActiveSeed_pos
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 < q) (m : D.Sample) :
    0 < bankPaperCanonicalScaledActiveSeed T q m := by
  exact mul_pos hq (T.baseline.baseWeight_pos m)

/-- The ambient push-forward of a nonnegative scaled seed is nonnegative,
without assuming an active-measure constructor. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_scaled_nonneg
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 <= q) (a : Nat) :
    0 <= bankPaperCanonicalActiveSeedAmbientWeight D
      (bankPaperCanonicalScaledActiveSeed T q) a := by
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  apply Finset.sum_nonneg
  intro m _hm
  split_ifs
  · exact bankPaperCanonicalScaledActiveSeed_nonneg T hq m
  · exact le_rfl

/-- The canonical scaled seed has total mass exactly `q`; this is the
finite coordinate realization in the paper's baseline-measure lemma. -/
@[simp] theorem bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    (q : Real) :
    bankPaperCanonicalLiteralActiveMass D
        (bankPaperCanonicalScaledActiveSeed T q) = q := by
  unfold bankPaperCanonicalLiteralActiveMass
    bankPaperCanonicalScaledActiveSeed
  rw [← Finset.mul_sum, T.baseline.baseWeight_sum,
    T.baseline_totalMass, mul_one]

/-! ## Canonical finite support and a self-selector witness -/

/-- The finite set of numerical coordinates occupied by the structured
active sample, without choosing bridge-band data. -/
def bankPaperCanonicalStructuredActiveValues
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) : Finset Nat :=
  Finset.univ.image D.value

@[simp] theorem mem_bankPaperCanonicalStructuredActiveValues
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} {a : Nat} :
    a ∈ bankPaperCanonicalStructuredActiveValues D ↔
      ∃ m : D.Sample, D.value m = a := by
  simp [bankPaperCanonicalStructuredActiveValues]

/-- If no pre-selector has yet been fixed, the ambient push-forward of the
scaled seed itself is a canonical finite pre-selector. -/
def bankPaperCanonicalScaledActivePreSelector
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) : Nat -> Real :=
  bankPaperCanonicalActiveSeedAmbientWeight D
    (bankPaperCanonicalScaledActiveSeed T q)

/-- For every `q >= 1`, the canonical active support, scaled seed, and its
own ambient push-forward satisfy the full actual-measure constructor with
no further hypothesis.  The remaining issue in the paper pipeline is
therefore alignment with its already constructed guarded pre-selector, not
existence of an abstract finite active measure. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_self
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 1 <= q) :
    BankPaperCanonicalActualActiveMeasureConstructor D T
      (bankPaperCanonicalStructuredActiveValues D)
      (bankPaperCanonicalScaledActivePreSelector D T q)
      (bankPaperCanonicalScaledActiveSeed T q) := by
  unfold BankPaperCanonicalActualActiveMeasureConstructor
  rw [bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  refine ⟨hq, ?_, ?_, ?_⟩
  · intro m
    rfl
  · intro m
    exact mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩
  · intro a _ha
    exact le_rfl

/-- Existential form of the unconditional finite construction. -/
theorem exists_bankPaperCanonicalActualActiveMeasureConstructor
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hq : 1 <= q) :
    ∃ candidates : Finset Nat,
    ∃ preSelector : Nat -> Real,
    ∃ activeSeed : D.Sample -> Real,
      BankPaperCanonicalActualActiveMeasureConstructor
        D T candidates preSelector activeSeed := by
  exact ⟨bankPaperCanonicalStructuredActiveValues D,
    bankPaperCanonicalScaledActivePreSelector D T q,
    bankPaperCanonicalScaledActiveSeed T q,
    bankPaperCanonicalActualActiveMeasureConstructor_self D T q hq⟩

/-! ## Exact minimization for a fixed guarded pre-selector -/

/-- Structural support plus full ambient domination for the forced scaled
seed.  This is the literal content left after the barycentric seed formula
has been constructed rather than postulated. -/
def BankPaperCanonicalActualActivePlacement
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) : Prop :=
  (∀ m : D.Sample, D.value m ∈ candidates) ∧
    ∀ a ∈ candidates,
      bankPaperCanonicalActiveSeedAmbientWeight D
          (bankPaperCanonicalScaledActiveSeed T q) a <=
        preSelector a

/-- For the canonical scaled seed, the original constructor is equivalent
to `q >= 1` and the finite placement condition.  In particular its seed
equation is not an independent missing input. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_scaled_iff
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
        preSelector (bankPaperCanonicalScaledActiveSeed T q) ↔
      1 <= q ∧
        BankPaperCanonicalActualActivePlacement
          D T candidates preSelector q := by
  unfold BankPaperCanonicalActualActiveMeasureConstructor
    BankPaperCanonicalActualActivePlacement
  rw [bankPaperCanonicalLiteralActiveMass_scaledActiveSeed]
  constructor
  · intro H
    exact ⟨H.1, H.2.2.1, H.2.2.2⟩
  · intro H
    exact ⟨H.1, (fun _m => rfl), H.2.1, H.2.2⟩

/-- With numerical head-pattern separation, the ambient seed at the value
of a sample tag is exactly that tag's scaled weight. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (q : Real) (hsep : D.HeadPatternsSeparated) (m : D.Sample) :
    bankPaperCanonicalActiveSeedAmbientWeight D
        (bankPaperCanonicalScaledActiveSeed T q) (D.value m) =
      bankPaperCanonicalScaledActiveSeed T q m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _hk hkm
    rw [if_neg]
    intro hvalue
    exact hkm (D.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

/-- The irreducible pointwise coupling for an already fixed pre-selector:
each active coordinate must fit under that selector.  No row, target,
band, prefix, or endpoint conclusion is included. -/
def BankPaperCanonicalActualCoordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (preSelector : Nat -> Real) (q : Real) : Prop :=
  forall m : D.Sample,
    bankPaperCanonicalScaledActiveSeed T q m <=
      preSelector (D.value m)

/-- Candidate support, nonnegativity of the pre-selector, and coordinate
fit imply full ambient placement.  Coordinates outside the active image
carry zero active mass; head-pattern separation handles the occupied
coordinates without a collision loss. -/
theorem bankPaperCanonicalActualActivePlacement_of_coordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit D T preSelector q) :
    BankPaperCanonicalActualActivePlacement
      D T candidates preSelector q := by
  refine ⟨hvalues, ?_⟩
  intro a ha
  by_cases hactive : ∃ m : D.Sample, D.value m = a
  · rcases hactive with ⟨m, rfl⟩
    rw [bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      D T q hsep m]
    exact hfit m
  · have hzero : bankPaperCanonicalActiveSeedAmbientWeight D
        (bankPaperCanonicalScaledActiveSeed T q) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive ⟨m, hma⟩
    rw [hzero]
    exact hselectorNonneg a ha

/-- Under the fixed structural/feasibility facts, full placement is
equivalent to coordinate fit. -/
theorem bankPaperCanonicalActualActivePlacement_iff_coordinateFit
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a) :
    BankPaperCanonicalActualActivePlacement D T candidates preSelector q ↔
      BankPaperCanonicalActualCoordinateFit D T preSelector q := by
  constructor
  · intro H m
    rw [← bankPaperCanonicalActiveSeedAmbientWeight_scaled_eq_of_value
      D T q hsep m]
    exact H.2 (D.value m) (H.1 m)
  · exact bankPaperCanonicalActualActivePlacement_of_coordinateFit
      D T candidates preSelector q hsep hvalues hselectorNonneg

/-- Consequently, once guarded support and selector nonnegativity are
available, the original active-measure constructor is *exactly* `q >= 1`
plus the pointwise coordinate fit. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
        preSelector (bankPaperCanonicalScaledActiveSeed T q) ↔
      1 <= q ∧
        BankPaperCanonicalActualCoordinateFit D T preSelector q := by
  rw [bankPaperCanonicalActualActiveMeasureConstructor_scaled_iff]
  constructor
  · intro H
    exact ⟨H.1,
      (bankPaperCanonicalActualActivePlacement_iff_coordinateFit
        D T candidates preSelector q hsep hvalues hselectorNonneg).mp H.2⟩
  · intro H
    exact ⟨H.1,
      (bankPaperCanonicalActualActivePlacement_iff_coordinateFit
        D T candidates preSelector q hsep hvalues hselectorNonneg).mpr H.2⟩

/-- Direct constructor from the irreducible coordinate fit. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (candidates : Finset Nat) (preSelector : Nat -> Real)
    (q : Real) (hq : 1 <= q) (hsep : D.HeadPatternsSeparated)
    (hvalues : ∀ m : D.Sample, D.value m ∈ candidates)
    (hselectorNonneg : ∀ a ∈ candidates, 0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit D T preSelector q) :
    BankPaperCanonicalActualActiveMeasureConstructor D T candidates
      preSelector (bankPaperCanonicalScaledActiveSeed T q) := by
  exact
    (bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
      D T candidates preSelector q hsep hvalues hselectorNonneg).mpr
        ⟨hq, hfit⟩

/-- A zero pre-selector is feasible in `[0,1]` but cannot carry any
positive canonical active coordinate.  Thus selector feasibility alone
cannot imply the missing coordinate fit. -/
theorem bankPaperCanonicalZeroPreSelector_not_coordinateFit
    {Head : Type*} [Fintype Head]
    {D : StructuredSampleData Head} (T : BarycentricTarget D)
    {q : Real} (hq : 0 < q) (m : D.Sample) :
    ¬ BankPaperCanonicalActualCoordinateFit D T (fun _ => 0) q := by
  intro H
  exact (not_le_of_gt
    (bankPaperCanonicalScaledActiveSeed_pos T hq m)) (H m)

/-! ## Guarded geometry and the older bridge-selector constructor -/

/-- Pointwise avoidance of the full numerical guard and interval geometry
already prove the support part of the actual active-measure construction. -/
theorem bankPaperCanonicalStructuredValue_mem_guardedCandidates
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
        R.roughCanonicalGuardSet certificate deltaStar)
    (m : B.sampleData.Sample) :
    B.sampleData.value m ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
  apply bankPaperCanonicalBridgeActiveValues_subset_guardedCandidates
    B R certificate deltaStar hKh hlower hupper hnotGuard
  exact mem_bankPaperCanonicalBridgeActiveValues.mpr ⟨m, rfl⟩

/-- On the literal guarded candidate set, all structural fields are now
derived; only `q >= 1`, candidate nonnegativity, and coordinate fit remain. -/
theorem bankPaperCanonicalActualActiveMeasureConstructor_guarded_of_coordinateFit
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
    (deltaStar : Real) (T : BarycentricTarget B.sampleData)
    (preSelector : Nat -> Real) (q : Real) (hq : 1 <= q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hselectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= preSelector a)
    (hfit : BankPaperCanonicalActualCoordinateFit
      B.sampleData T preSelector q) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      preSelector (bankPaperCanonicalScaledActiveSeed T q) := by
  apply bankPaperCanonicalActualActiveMeasureConstructor_of_coordinateFit
    B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      preSelector q hq hsep
  · intro m
    exact bankPaperCanonicalStructuredValue_mem_guardedCandidates
      B R certificate deltaStar hKh hlower hupper hnotGuard m
  · exact hselectorNonneg
  · exact hfit

/-- The older guarded bridge selector constructor already contains exact
baseline agreement on active coordinates.  If its bridge baseline is the
literal `q`-scaled barycentric baseline, that agreement supplies the
irreducible coordinate fit and hence the full actual-measure constructor.

This theorem is useful but deliberately does not claim that the newer
guarded continuation has this field: it does not. -/
theorem exists_bankPaperCanonicalActualActiveMeasureConstructor_of_guardedBridge
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
    (T : BarycentricTarget B.sampleData)
    (q : Real) (hq : 1 <= q)
    (hbaseline : B.baseline =
      T.activeMassBaseline q (zero_lt_one.trans_le hq))
    (Hbridge : BankPaperCanonicalGuardedBridgeSelectorConstructor
      (K := K) B R certificate deltaStar cellIndex pointwiseUpper prefixUpper)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hlower : forall m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : forall m : B.sampleData.Sample,
      B.sampleData.value m <= 2 * B.sampleData.n)
    (hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar) :
    ∃ preSelector : Nat -> Real,
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          B.partition.band cellIndex pointwiseUpper prefixUpper preSelector ∧
        BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
          (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
          preSelector (bankPaperCanonicalScaledActiveSeed T q) := by
  rcases Hbridge with ⟨preSelector, Spre, hbaselineAt⟩
  refine ⟨preSelector, Spre, ?_⟩
  apply bankPaperCanonicalActualActiveMeasureConstructor_guarded_of_coordinateFit
    B R certificate deltaStar T preSelector q hq hsep
      hKh hlower hupper hnotGuard
  · intro a ha
    exact (Spre.1 a ha).1
  · intro m
    calc
      bankPaperCanonicalScaledActiveSeed T q m =
          (T.activeMassBaseline q (zero_lt_one.trans_le hq)).baseWeight m :=
        (T.activeMassBaseline_baseWeight
          q (zero_lt_one.trans_le hq) m).symm
      _ = B.baseline.baseWeight m :=
        (congrArg
          (fun A : BaselineAllocation B.sampleData => A.baseWeight m)
          hbaseline).symm
      _ = preSelector (B.sampleData.value m) :=
        (hbaselineAt m).symm
      _ <= preSelector (B.sampleData.value m) := le_rfl

/-! ## The literal mass already stored by the paper head simplex -/

/-- Specialization of the forced seed to the repository's explicit paper
head simplex and two-pool physical interpolation data. -/
def bankPaperCanonicalPaperDataActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I) :
    B.sampleData.Sample -> Real :=
  bankPaperCanonicalScaledActiveSeed
    (B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical)
    Rhead.activeMass

/-- The paper-data specialization has literal mass exactly the
`HeadSimplexReserve.activeMass` already present in the repository. -/
@[simp] theorem bankPaperCanonicalLiteralActiveMass_paperDataActiveSeed
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (Rhead : HeadSimplexReserve P)
    (Kphysical : PhysicalInterpolationTarget I) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalPaperDataActiveSeed
          B I hlo hhi Rhead Kphysical) = Rhead.activeMass := by
  exact bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
    (B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical)
    Rhead.activeMass

end

end Erdos390.WholePaper
