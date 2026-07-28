import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightBaselineTargetConnector
import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalActualActiveMeasureAdditiveRefinement

/-!
# The post-height baseline under the literal frozen-top placement

The nearest-integer source, the height-changing placement, and the final
barycentric baseline are three different finite objects in the paper.  In
particular, the final baseline has literal mass

`q_n = q0 - d`

and need not equal the two-zero-cell seed used to change the integral row
height.

This file installs the scaled seed of
`bankPaperCanonicalSectionNinePostHeightTarget` directly as the active
layer of the literal frozen-top structured preselector.  The protected
layer then gives pointwise domination, hence the full
`BankPaperCanonicalActualActiveMeasureConstructor` at mass `q0-d`.

The optional feasibility theorem below isolates the remaining upper-bound
issue as the paper's finite geometry: an `O(n / log n)` bound for `q_n`,
a linear lower bound for every structured cell cardinality, and one large
`log n` inequality.  No abstract redistribution contract or equality with
the earlier rounding seed is assumed.
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

namespace BankPaperRealization

/-! ## Literal post-height placed preselector -/

/-- The literal frozen-top source with the final post-height barycentric
seed installed as its structured active layer. -/
def bankPaperCanonicalSectionNinePostHeightPlacedPreSelector
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real) : Nat → Real :=
  bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector (K := K)
    B R certificate Tsource deltaStar betaProt alpha beta qTilde
      (bankPaperCanonicalSectionNinePostHeightActiveSeed
        B I hlo hhi H)

/-- Expanded form of the placed preselector.  This is only definitional
alignment: it does not identify the final active seed with the earlier
nearest-integer or height-changing seed. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector_eq_structuredPlacement
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real) :
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
        B R certificate Tsource I hlo hhi H
          deltaStar betaProt alpha beta qTilde =
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
            B R certificate Tsource deltaStar betaProt
              alpha beta qTilde)
          (bankPaperCanonicalScaledActiveSeed
            (bankPaperCanonicalSectionNinePostHeightTarget
              B I hlo hhi H)
            (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)) :=
  rfl

/-! ## Exact pointwise domination and active measure -/

/-- The final scaled post-height seed is pointwise dominated at every
structured active coordinate by the literal frozen-top placed preselector.
This is the exact coupling required by the actual-measure constructor. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector_coordinateFit
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hbetaProt : 0 ≤ betaProt) :
    BankPaperCanonicalActualCoordinateFit B.sampleData
      (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
        B R certificate Tsource I hlo hhi H
          deltaStar betaProt alpha beta qTilde)
      (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) := by
  simpa only [
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalSectionNinePostHeightActiveSeed] using
    (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
        hsep hbetaProt)

/-- The post-height seed has the paper's exact mass `q_n = q0-d` while
being carried by the literal frozen-top placed preselector. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_actualMeasure
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hqn : 1 ≤ bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n ≤ B.sampleData.n)
    (hlower : ∀ m : B.sampleData.Sample,
      B.sampleData.n < B.sampleData.value m)
    (hupper : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ≤ 2 * B.sampleData.n)
    (hnotGuard : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (hsourceNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 ≤ bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
        B R certificate Tsource deltaStar betaProt
          alpha beta qTilde a) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData
      (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
        B R certificate Tsource I hlo hhi H
          deltaStar betaProt alpha beta qTilde)
      (bankPaperCanonicalSectionNinePostHeightActiveSeed
        B I hlo hhi H) := by
  simpa only [
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalSectionNinePostHeightActiveSeed] using
    (bankPaperCanonicalActualActiveMeasureConstructor_of_structuredAdditivePlacement
      B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
        hqn hsep hKh hlower hupper hnotGuard hbetaProt hsourceNonneg)

/-! ## The finite capacity supplied by post-height geometry -/

/-- An `O(n / log n)` upper bound for the final mass and a linear lower
bound for every structured cell cardinality give the required pointwise
`O(1 / log n)` bound for the redistributed post-height seed.

The normalized target cell masses need no extra hypothesis: positivity and
their exact sum one imply that each is at most one. -/
theorem
    bankPaperCanonicalSectionNinePostHeightActiveSeed_le_of_massAndCellDensity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real)) :
    ∀ m : B.sampleData.Sample,
      bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H m ≤
        (Cmass / density) / B.L := by
  intro m
  let Tpost :=
    bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H
  let qn := bankPaperCanonicalSectionNinePostHeightActiveMass q0 d
  let cell := B.sampleData.cellOf m
  have hcardPos :
      0 < (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos cell
  have hden : 0 < density * B.L :=
    mul_pos hdensity B.L_pos
  have hfactor : 0 ≤ Cmass / (density * B.L) :=
    div_nonneg hCmass hden.le
  have hscaled :
      (Cmass / (density * B.L)) *
          (density * (B.sampleData.n : Real)) ≤
        (Cmass / (density * B.L)) *
          (Fintype.card (B.sampleData.SampleAt cell) : Real) :=
    mul_le_mul_of_nonneg_left (hcard cell) hfactor
  have hcellLeOne : Tpost.baseline.cellMass cell ≤ 1 := by
    calc
      Tpost.baseline.cellMass cell ≤
          ∑ cell' : Cell (PaperHeadSimplex.Tag P),
            Tpost.baseline.cellMass cell' :=
        Finset.single_le_sum
          (fun cell' _ => (Tpost.baseline.cellMass_pos cell').le)
          (Finset.mem_univ cell)
      _ = Tpost.baseline.totalMass := rfl
      _ = 1 := Tpost.baseline_totalMass
  have hcellMass :
      qn * Tpost.baseline.cellMass cell ≤
        Cmass * (B.sampleData.n : Real) / B.L := by
    calc
      qn * Tpost.baseline.cellMass cell ≤ qn * 1 :=
        mul_le_mul_of_nonneg_left hcellLeOne H.activeMass_pos.le
      _ = qn := mul_one qn
      _ ≤ Cmass * (B.sampleData.n : Real) / B.L := hmass
  change qn * Tpost.baseline.baseWeight m ≤
    (Cmass / density) / B.L
  unfold BaselineAllocation.baseWeight
  change
    qn * (Tpost.baseline.cellMass cell /
      (Fintype.card (B.sampleData.SampleAt cell) : Real)) ≤
        (Cmass / density) / B.L
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hcardPos).2
  calc
    qn * Tpost.baseline.cellMass cell ≤
        Cmass * (B.sampleData.n : Real) / B.L := hcellMass
    _ = (Cmass / (density * B.L)) *
          (density * (B.sampleData.n : Real)) := by
      field_simp [ne_of_gt hdensity, ne_of_gt B.L_pos]
    _ ≤ (Cmass / (density * B.L)) *
          (Fintype.card (B.sampleData.SampleAt cell) : Real) := hscaled
    _ = ((Cmass / density) / B.L) *
          (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
      field_simp [ne_of_gt hdensity, ne_of_gt B.L_pos]

/-- The preceding mass/cardinality geometry and one large-`log n`
inequality discharge the exact structured-placement capacity predicate for
the post-height target. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacementCapacity_of_massAndCellDensity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt Cmass density : Real)
    (hbetaProt : 0 ≤ betaProt)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density ≤ B.L) :
    BankPaperCanonicalStructuredAdditivePlacementCapacity (K := K)
      B R certificate deltaStar betaProt
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d) := by
  apply
    bankPaperCanonicalStructuredAdditivePlacementCapacity_of_div_log_bound
      (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
        hbetaProt (Cmass / density)
        (div_nonneg hCmass hdensity.le)
  · exact
      bankPaperCanonicalSectionNinePostHeightActiveSeed_le_of_massAndCellDensity
        B I hlo hhi H Cmass density hCmass hdensity hmass hcard
  · exact hlarge

/-! ## Actual measure and full selector feasibility -/

/-- The complete paper-facing result.  The post-height seed of exact mass
`q0-d` is an actual active measure under the literal frozen-top placed
preselector, and that preselector lies in `[0,1]` throughout the guarded
candidate set.

All upper feasibility is discharged by explicit finite mass and cell
density geometry, rather than by a separate redistribution contract. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlaced_actualMeasure_and_feasible_of_massAndCellDensity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (I : PhysicalIntervals)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperTwo : ∀ sigma, I.upper sigma ≤ 2)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} → Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (deltaStar betaProt alpha beta qTilde : Real)
    (hqn : 1 ≤ bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hKh : K * upperTailLength c B.sampleData.n ≤ B.sampleData.n)
    (hnotGuard : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (hsourceFeasible : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde a ∈ Set.Icc (0 : Real) 1)
    (Cmass density : Real)
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hmass :
      bankPaperCanonicalSectionNinePostHeightActiveMass q0 d ≤
        Cmass * (B.sampleData.n : Real) / B.L)
    (hcard : ∀ cell : Cell (PaperHeadSimplex.Tag P),
      density * (B.sampleData.n : Real) ≤
        (Fintype.card (B.sampleData.SampleAt cell) : Real))
    (hlarge : betaProt + Cmass / density ≤ B.L) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
        (bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
          B R certificate Tsource I hlo hhi H
            deltaStar betaProt alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightActiveSeed
          B I hlo hhi H) ∧
      (∀ a ∈ R.roughCanonicalGuardedCandidateSet
          certificate deltaStar K,
        bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K)
            B R certificate Tsource I hlo hhi H
              deltaStar betaProt alpha beta qTilde a ∈
          Set.Icc (0 : Real) 1) := by
  have hcapacity :=
    bankPaperCanonicalSectionNinePostHeightPlacementCapacity_of_massAndCellDensity
      (K := K) B R certificate I hlo hhi H deltaStar betaProt
        Cmass density hbetaProt hCmass hdensity hmass hcard hlarge
  simpa only [
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    bankPaperCanonicalSectionNinePostHeightActiveSeed] using
    (bankPaperCanonicalActualActiveMeasureConstructor_and_feasible_of_structuredAdditivePlacement_physicalIntervals
      B R certificate deltaStar betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
          B R certificate Tsource deltaStar betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
        (bankPaperCanonicalSectionNinePostHeightActiveMass q0 d)
        hqn hsep I hlowerOne hupperTwo hlo hhi hKh hnotGuard
        hbetaProt hsourceFeasible hcapacity)

end BankPaperRealization

end

end Erdos390.WholePaper
