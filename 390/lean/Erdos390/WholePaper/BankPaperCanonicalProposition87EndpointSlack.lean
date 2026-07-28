import Erdos390.WholePaper.BankPaperProposition87EndpointSelector
import Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration

/-!
# Proposition 8.7 endpoint slack on the guarded smooth row

The endpoint emitted by Proposition 8.7 is the literal sum of a frozen
ambient layer and an active exponential-family layer.  This file keeps that
overlap visible and proves the quantitative smooth-row part of the tangent
slack argument.

The active upper bound is not an assumption: it follows from the effective
box in `IsPaperProposition87Path`, the baseline `Cactive / L` ledger, and the
proved density-ratio estimate.  The sole construction datum not currently
present in the guarded-selector development is named
`BankPaperCanonicalGuardedSmoothProtectedWindow`: on every guarded smooth
broad coordinate the actual frozen ambient layer contains the protected
floor and is itself `O(1 / L)`.  This is exactly the finite realization of
the protected summand in the paper's smooth additive decomposition and
tangent endpoint-slack argument;
it does not assume endpoint slack or any tangent conclusion.

After that one window is supplied, the endpoint selector has the required
strict upper reserve, the existing nonsmooth constant-pool correction joins
it to form `BankPaperCanonicalGuardedEndpointSlackConstruction`, and the
existing clean-list candidate adapter applies without any further premise.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Filter

noncomputable section

/-! ## The one missing finite protected-layer estimate -/

/-- The precise protected-layer estimate still required from the literal
guarded smooth-row construction.

It concerns the actual frozen ambient layer used by Proposition 8.7, so it
allows protected tags to occupy the same numerical coordinates as active
sample tags.  The lower inequality is the protected floor.  The upper
inequality is the `O(1 / L)` frozen ledger on the whole guarded smooth broad
pool, including coordinates outside the active structured sub-sample. -/
def BankPaperCanonicalGuardedSmoothProtectedWindow
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (sigma Cfixed : Real) : Prop :=
  ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1,
    sigma / B.L <=
        BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∧
      BridgeData.frozenAmbientWeight fixedValue fixedWeight x <=
        Cfixed / B.L

/-- Push-forward through the identity-valued subtype index has exactly one
tag above each member of the finite support.  This is the finite adapter used
by the actual-data connector, whose frozen index is the subtype of guarded
candidates. -/
theorem frozenAmbientWeight_subtype_apply
    (support : Finset Nat) (weight : ↥support -> Real)
    {x : Nat} (hx : x ∈ support) :
    BridgeData.frozenAmbientWeight
        (fun f : ↥support => f.1) weight x = weight ⟨x, hx⟩ := by
  classical
  unfold BridgeData.frozenAmbientWeight
  rw [Finset.sum_eq_single (⟨x, hx⟩ : ↥support)]
  · simp
  · intro f hf hne
    rw [if_neg]
    intro hvalue
    apply hne
    apply Subtype.ext
    exact hvalue
  · intro hnot
    exact (hnot (Finset.mem_univ _)).elim

/-- For the actual frozen remainder, a coordinate carrying no active seed
pushes forward to the original pre-selector weight.  This is the exact
nonsmooth frozen-row adapter. -/
theorem frozenAmbientWeight_subtypeRemainder_eq_preSelector
    (candidates : Finset Nat) (preSelector activeSeedAmbient : Nat -> Real)
    {x : Nat} (hx : x ∈ candidates) (hactive : activeSeedAmbient x = 0) :
    BridgeData.frozenAmbientWeight
        (fun f : ↥candidates => f.1)
        (fun f => preSelector f.1 - activeSeedAmbient f.1) x =
      preSelector x := by
  rw [frozenAmbientWeight_subtype_apply candidates
    (fun f => preSelector f.1 - activeSeedAmbient f.1) hx]
  dsimp
  rw [hactive, sub_zero]

/-- For an identity-valued guarded-candidate frozen layer, it is enough to
verify the protected window directly on its tagged coordinate weights.  No
injectivity or support conclusion remains to be supplied downstream. -/
theorem bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeBounds
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
    (deltaStar : Real) (candidates : Finset Nat)
    (fixedWeight : ↥candidates -> Real) (sigma Cfixed : Real)
    (hpool : R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ⊆ candidates)
    (hweight : forall x
      (hx : x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1),
      sigma / B.L <= fixedWeight ⟨x, hpool hx⟩ ∧
        fixedWeight ⟨x, hpool hx⟩ <= Cfixed / B.L) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar (fun f : ↥candidates => f.1)
        fixedWeight sigma Cfixed := by
  unfold BankPaperCanonicalGuardedSmoothProtectedWindow
  intro x hx
  rw [frozenAmbientWeight_subtype_apply candidates fixedWeight (hpool hx)]
  exact hweight x hx

/-- Concrete subtraction form used by the actual-paper-data connector.  If
`activeSeedAmbient` is nonnegative, the pre-selector has its broad
`Cfixed / L` upper bound, and it dominates the seed by the protected amount
`sigma / L`, then the frozen remainder
`preSelector - activeSeedAmbient` satisfies the exact protected window.

Thus subtraction and finite push-forward introduce no additional gap: the
only lower estimate left to the rough/smooth realization is the displayed
protected reserve before subtraction. -/
theorem bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeRemainder
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
    (deltaStar : Real) (candidates : Finset Nat)
    (preSelector activeSeedAmbient : Nat -> Real)
    (sigma Cfixed : Real)
    (hpool : R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K 1 ⊆ candidates)
    (hactiveNonneg : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      0 <= activeSeedAmbient x)
    (hprotectedReserve : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      sigma / B.L + activeSeedAmbient x <= preSelector x)
    (hpreUpper : ∀ x ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1,
      preSelector x <= Cfixed / B.L) :
    BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar (fun f : ↥candidates => f.1)
        (fun f => preSelector f.1 - activeSeedAmbient f.1)
        sigma Cfixed := by
  apply bankPaperCanonicalGuardedSmoothProtectedWindow_of_subtypeBounds
    B R certificate deltaStar candidates
      (fun f => preSelector f.1 - activeSeedAmbient f.1)
      sigma Cfixed hpool
  intro x hx
  constructor <;> dsimp
  · linarith [hprotectedReserve x hx]
  · linarith [hactiveNonneg x hx, hpreUpper x hx]

/-! ## Quantitative active-coordinate bound at the actual P87 endpoint -/

/-- A pointwise effective-score bound and the baseline coordinate ledger
give an ambient active upper bound at every natural coordinate.  At a sample
coordinate this is the proved P87 density-ratio estimate; away from the
sample support the ambient active weight is exactly zero. -/
theorem bankPaperProposition87AmbientActiveWeight_le_of_effectiveScoreBound
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (xi : B.ParamSpace) (Rbound Cactive : Real)
    (hscore : forall m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| <= Rbound)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L) :
    forall x : Nat,
      B.ambientActiveWeight xi x <=
        Real.exp (2 * Rbound) * Cactive / B.L := by
  intro x
  by_cases hx : exists m : B.sampleData.Sample,
      B.sampleData.value m = x
  · obtain ⟨m, rfl⟩ := hx
    rw [B.ambientActiveWeight_eq_of_value hsep]
    calc
      B.activeCoordinateWeight xi m <=
          Real.exp (2 * Rbound) * B.baseline.baseWeight m :=
        B.activeCoordinateWeight_le_exp_twoEffectiveBound_mul_baseline
          xi Rbound hscore m
      _ <= Real.exp (2 * Rbound) * (Cactive / B.L) :=
        mul_le_mul_of_nonneg_left (hactive m) (Real.exp_pos _).le
      _ = Real.exp (2 * Rbound) * Cactive / B.L := by ring
  · rw [B.ambientActiveWeight_eq_zero_of_not_value xi x
      (fun m hm => hx ⟨m, hm⟩)]
    exact div_nonneg
      (mul_nonneg (Real.exp_pos _).le hCactive) B.L_pos.le

/-- The preceding ambient bound specialized to the literal endpoint of an
`IsPaperProposition87Path`.  Its effective-score radius is obtained from the
path's proved `paperEffectiveSize <= 3 * a` clause; no endpoint estimate is
added as a premise. -/
theorem bankPaperProposition87AmbientActiveWeight_endpoint_le_of_path
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (H : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      fixedValue fixedWeight quota path)
    (C Cactive : Real) (hC : 1 <= C)
    (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L) :
    forall x : Nat,
      B.ambientActiveWeight (path 1) x <=
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive / B.L := by
  have hsize : ∀ t ∈ Set.Icc (0 : Real) 1,
      B.paperEffectiveSize (path t) <= 3 * (radius : Real) :=
    H.2.2.1
  have hsizeOne : B.paperEffectiveSize (path 1) <=
      3 * (radius : Real) := hsize 1 (by constructor <;> norm_num)
  have hscore := B.effectiveScoreBound_of_paperEffectiveSize
    hC hW hhi (path 1) hsizeOne
  exact bankPaperProposition87AmbientActiveWeight_le_of_effectiveScoreBound
    B hsep (path 1)
      ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
          C B.sampleData.W +
        B.nuisanceStatisticCoefficient C) * (3 * (radius : Real)))
      Cactive hscore hCactive hactive

/-- The extra fixed reserve `sigma` costs no new asymptotic input.  After all
constants and the P87 box have been fixed, it is absorbed by the same
`L(n) -> infinity` theorem that supplies ordinary endpoint feasibility. -/
theorem eventually_bankPaperProposition87EndpointSlack_logReserve
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (C : Real) (hC : 1 <= C) (W : Nat) (radius : NNReal)
    (Cfixed Cactive sigma : Real) (hCactive : 0 <= Cactive) :
    ∀ᶠ n : Nat in atTop,
      forall B : BridgeData Head Band,
        B.sampleData.n = n -> B.sampleData.W = W ->
          Cfixed +
              Real.exp (2 *
                ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                    C B.sampleData.W +
                  B.nuisanceStatisticCoefficient C) *
                    (3 * (radius : Real)))) * Cactive + sigma <= B.L := by
  have H := BridgeData.eventually_canonical_exponential_slack_le_L
    (Head := Head) (Band := Band) C hC W radius
      (Cfixed + sigma) Cactive hCactive
  filter_upwards [H] with n hn
  intro B hBn hBW
  have hlarge := hn B hBn hBW
  linarith

/-- If the active structured sample lies in the guarded smooth row, its
ambient active layer vanishes on every guarded nonsmooth broad coordinate.
This is the support fact which lets the frozen nonsmooth selector pass
through the P87 endpoint unchanged. -/
theorem bankPaperProposition87AmbientActiveWeight_eq_zero_on_nonsmoothPool
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
    (deltaStar : Real) (path : Real -> B.ParamSpace)
    (hactiveSmooth : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    {label x : Nat} (hlabel : label ≠ 1)
    (hx : x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar B.sampleData.W K label) :
    B.ambientActiveWeight (path 1) x = 0 := by
  apply B.ambientActiveWeight_eq_zero_of_not_value
  intro m hm
  have hxSmooth : x ∈
      R.roughCanonicalGuardedRow certificate deltaStar K 1 := by
    simpa only [hm] using hactiveSmooth m
  have hxLabel : x ∈
      R.roughCanonicalGuardedRow certificate deltaStar K label :=
    R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
      certificate deltaStar B.sampleData.W K label hx
  have hsmoothEq := (mem_completeRoughRowFiber.mp hxSmooth).2
  have hlabelEq := (mem_completeRoughRowFiber.mp hxLabel).2
  exact hlabel (hlabelEq.symm.trans hsmoothEq)

/-! ## Smooth protected floor and strict upper reserve -/

/-- The actual P87 endpoint selector has the paper's two-sided tangent slack
on every guarded smooth broad coordinate.

The witnesses are not artificial copies: `protected` is the literal frozen
ambient weight and `active` is the literal endpoint active weight.  Thus the
proof remains valid when the two tagged layers overlap at a natural-number
coordinate. -/
theorem exists_bankPaperProposition87EndpointSelector_smoothSlackLayers
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      fixedValue fixedWeight quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hprotected : BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar fixedValue fixedWeight sigma Cfixed)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L) :
    ∃ protectedPart active : Nat -> Real,
      ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
          deltaStar B.sampleData.W K 1,
        bankPaperProposition87EndpointSelector
              B fixedValue fixedWeight path x =
            protectedPart x + active x ∧
          sigma / B.L <= protectedPart x ∧
          0 <= active x ∧
          protectedPart x + active x <= 1 - sigma / B.L := by
  let protectedPart : Nat -> Real :=
    BridgeData.frozenAmbientWeight fixedValue fixedWeight
  let active : Nat -> Real := B.ambientActiveWeight (path 1)
  refine ⟨protectedPart, active, ?_⟩
  intro x hx
  have hprotectedX := hprotected x hx
  have hactiveNonneg : 0 <= active x := by
    exact B.ambientActiveWeight_nonneg (path 1) x
  have hactiveUpper : active x <=
      Real.exp (2 *
        ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
            C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) *
            (3 * (radius : Real)))) * Cactive / B.L := by
    exact bankPaperProposition87AmbientActiveWeight_endpoint_le_of_path
      B Delta radius markedTarget N Cpost fixedValue fixedWeight quota path
        Hpath C Cactive hC hW hhi hsep hCactive hactive x
  have hcoefficient : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive <= B.L - sigma := by
    linarith
  have hsum : protectedPart x + active x <=
      (Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive) / B.L := by
    calc
      protectedPart x + active x <=
          Cfixed / B.L +
            Real.exp (2 *
              ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  C B.sampleData.W +
                B.nuisanceStatisticCoefficient C) *
                  (3 * (radius : Real)))) * Cactive / B.L :=
        add_le_add hprotectedX.2 hactiveUpper
      _ = (Cfixed +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                C B.sampleData.W +
              B.nuisanceStatisticCoefficient C) *
                (3 * (radius : Real)))) * Cactive) / B.L := by ring
  have hreserve : (Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive) / B.L <=
      1 - sigma / B.L := by
    calc
      (Cfixed +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                C B.sampleData.W +
              B.nuisanceStatisticCoefficient C) *
                (3 * (radius : Real)))) * Cactive) / B.L <=
          (B.L - sigma) / B.L :=
        div_le_div_of_nonneg_right hcoefficient B.L_pos.le
      _ = 1 - sigma / B.L := by
        field_simp [ne_of_gt B.L_pos]
  refine ⟨?_, hprotectedX.1, hactiveNonneg, hsum.trans hreserve⟩
  rfl

namespace BankPaperRealization

/-! ## Join to the already proved nonsmooth correction -/

/-- The P87 smooth endpoint layers and the already existing nonsmooth
constant-pool output form the exact guarded endpoint-slack construction.
The active-support premise and frozen-row identity show that P87 changes no
nonsmooth coordinate; the remaining nonsmooth hypotheses are only the two
already isolated correction-density bounds.  The smooth half is proved above
from the protected window and the P87 path. -/
theorem guardedEndpointSlackConstruction_of_proposition87EndpointSelector
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      fixedValue fixedWeight quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hprotected : BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar fixedValue fixedWeight sigma Cfixed)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hactiveSmooth : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L)
    (hfrozenNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          BridgeData.frozenAmbientWeight fixedValue fixedWeight x =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L x) :
    R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
      deltaStar B.sampleData.W K alpha beta B.L sigma
      (bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path) := by
  constructor
  · exact exists_bankPaperProposition87EndpointSelector_smoothSlackLayers
      B R certificate deltaStar Delta radius markedTarget N Cpost
        fixedValue fixedWeight quota path Hpath C sigma Cfixed Cactive
        hC hW hhi hsep hCactive hactive hprotected hlarge
  · intro label hlabel
    obtain ⟨hfloor, hceiling⟩ := hnonsmoothBounds label hlabel
    refine ⟨hfloor, hceiling, ?_⟩
    intro x hx
    change BridgeData.frozenAmbientWeight fixedValue fixedWeight x +
        B.ambientActiveWeight (path 1) x =
      R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
        deltaStar B.sampleData.W K label alpha beta B.L x
    rw [bankPaperProposition87AmbientActiveWeight_eq_zero_on_nonsmoothPool
      B R certificate deltaStar path hactiveSmooth hlabel.1 hx, add_zero]
    exact hfrozenNonsmooth label hlabel x hx

/-- Direct candidate-set handoff for the actual P87 endpoint selector.
Besides the literal clean-list containment it returns the two-sided endpoint
slack consumed by the distributed tangent.  Both conclusions are obtained
by applying the existing candidate adapter to the construction theorem
above. -/
theorem proposition87EndpointSelector_candidateSetEndpointInputs
    {Head Band Fixed : Type*}
    [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Fintype Fixed]
    [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar alpha beta : Real)
    (Delta : Band -> Real) (radius : NNReal)
    (markedTarget : Nat -> Real) (N Cpost : Real)
    (fixedValue : Fixed -> Nat) (fixedWeight : Fixed -> Real)
    (quota : Int) (path : Real -> B.ParamSpace)
    (Hpath : B.IsPaperProposition87Path Delta radius markedTarget N Cpost
      fixedValue fixedWeight quota path)
    (C sigma Cfixed Cactive : Real)
    (hC : 1 <= C) (hW : 1 < B.sampleData.W)
    (hhi : forall sign,
      B.sampleData.hi sign <= physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hCactive : 0 <= Cactive)
    (hactive : forall m : B.sampleData.Sample,
      B.baseline.baseWeight m <= Cactive / B.L)
    (hprotected : BankPaperCanonicalGuardedSmoothProtectedWindow (K := K)
      B R certificate deltaStar fixedValue fixedWeight sigma Cfixed)
    (hlarge : Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              C B.sampleData.W +
            B.nuisanceStatisticCoefficient C) *
              (3 * (radius : Real)))) * Cactive + sigma <= B.L)
    (hactiveSmooth : forall m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hnonsmoothBounds : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        sigma / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          beta / B.L ∧
        beta / B.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar B.sampleData.W K label alpha beta B.L| <=
          1 - sigma / B.L)
    (hfrozenNonsmooth : forall label,
      RoughCanonicalActiveNonexceptionalLabel B.sampleData.n deltaStar label ->
        ∀ x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K label,
          BridgeData.frozenAmbientWeight fixedValue fixedWeight x =
            R.roughCanonicalGuardedPostchargeRowCorrectedWeight certificate
              deltaStar B.sampleData.W K label alpha beta B.L x)
    {flow : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W ->
      BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W -> Real}
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n) :
    (forall request : BankPaperCanonicalDistributedTangentSplitRequest
        flow B.L sigma,
      forall {common : Nat},
        common ∈
            tangentSplitCleanMultiplierLists
              (tangentPositiveFlowEdges flow)
              (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
              (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
              B.L sigma
              (fun edge : BankPaperCanonicalTangentPrime
                    B.sampleData.n B.sampleData.W ×
                  BankPaperCanonicalTangentPrime
                    B.sampleData.n B.sampleData.W =>
                flow edge.1 edge.2)
              B.sampleData.n K
              (upperTailLength c B.sampleData.n)
              (roughHeadModulus B.sampleData.W)
              (tangentPaperExceptionalCutoff deltaStar B.sampleData.n)
              (yNat B.sampleData.n)
              R.tangentPaperDedicatedRows
              (R.tangentPaperNumericalGuardSet certificate
                (R.paperFixedExceptionalFactors deltaStar)) request ->
          bankPaperCanonicalDistributedTangentRequestSource request * common ∈
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K ∧
            bankPaperCanonicalDistributedTangentRequestTarget request *
                common ∈
              R.roughCanonicalGuardedCandidateSet certificate deltaStar K) ∧
      (forall request : BankPaperCanonicalDistributedTangentSplitRequest
          flow B.L sigma,
        forall common : Nat,
          common ∈
              tangentSplitCleanMultiplierLists
                (tangentPositiveFlowEdges flow)
                (tangentStarEdgeSource bankPaperCanonicalTangentPrimeLabel)
                (tangentStarEdgeTarget bankPaperCanonicalTangentPrimeLabel)
                B.L sigma
                (fun edge : BankPaperCanonicalTangentPrime
                      B.sampleData.n B.sampleData.W ×
                    BankPaperCanonicalTangentPrime
                      B.sampleData.n B.sampleData.W =>
                  flow edge.1 edge.2)
                B.sampleData.n K
                (upperTailLength c B.sampleData.n)
                (roughHeadModulus B.sampleData.W)
                (tangentPaperExceptionalCutoff deltaStar B.sampleData.n)
                (yNat B.sampleData.n)
                R.tangentPaperDedicatedRows
                (R.tangentPaperNumericalGuardSet certificate
                  (R.paperFixedExceptionalFactors deltaStar)) request ->
            (sigma / B.L <=
                bankPaperProposition87EndpointSelector
                  B fixedValue fixedWeight path
                    (bankPaperCanonicalDistributedTangentRequestSource
                      request * common) ∧
              bankPaperProposition87EndpointSelector
                  B fixedValue fixedWeight path
                    (bankPaperCanonicalDistributedTangentRequestSource
                      request * common) <= 1 - sigma / B.L) ∧
            (sigma / B.L <=
                bankPaperProposition87EndpointSelector
                  B fixedValue fixedWeight path
                    (bankPaperCanonicalDistributedTangentRequestTarget
                      request * common) ∧
              bankPaperProposition87EndpointSelector
                  B fixedValue fixedWeight path
                    (bankPaperCanonicalDistributedTangentRequestTarget
                      request * common) <= 1 - sigma / B.L)) := by
  have Hconstruction :=
    guardedEndpointSlackConstruction_of_proposition87EndpointSelector
      B R certificate deltaStar alpha beta Delta radius markedTarget N Cpost
        fixedValue fixedWeight quota path Hpath C sigma Cfixed Cactive
        hC hW hhi hsep hCactive hactive hprotected hlarge hactiveSmooth
        hnonsmoothBounds hfrozenNonsmooth
  exact R.guardedEndpointSlackConstruction_candidateSetEndpointInputs
    certificate deltaStar alpha beta
      (bankPaperProposition87EndpointSelector
        B fixedValue fixedWeight path) hKh Hconstruction

end BankPaperRealization

end

end Erdos390.WholePaper
