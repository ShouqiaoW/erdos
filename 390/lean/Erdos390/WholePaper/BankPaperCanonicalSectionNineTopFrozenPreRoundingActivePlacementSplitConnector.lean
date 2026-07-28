import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSourceCoreAlignmentConnector

/-!
# Pre-rounding active measure and post-rounding placement

The nearest-integer correction in the top-frozen source changes only the
two zero-head cells.  In general that correction does not preserve the
product form encoded by `BarycentricTarget`: the physical mixing ratio is
common to every head in a barycentric target, whereas the correction changes
only the zero head.

The Proposition 8.7 interface does not require the placed seed itself to be
barycentric.  Its active measure and its placement seed are separate
arguments.  This file records the honest split:

* the active measure remains the pre-rounding scaled seed
  `bankPaperCanonicalScaledActiveSeed Tsource qTilde`;
* the placement seed carries the symmetric two-zero-cell correction; and
* the protected layer absorbs any negative part of that correction.

Thus no post-rounding `BarycentricTarget` is constructed or assumed.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## Exact projections from the existing source package -/

/-- The source-state, feasibility, and prebridge fields already stored in
the top-frozen finite package assemble to the full verified placement.  This
is an unconditional projection: it neither identifies the placement seed
with the active seed nor asks either seed to be barycentric. -/
theorem
    BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt.verifiedPlacement
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    {B : BridgeData (PaperHeadSimplex.Tag P) Band}
    {c : Real} {depth : Nat}
    {R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {K0 : Nat} {deltaStar : Real}
    (S : BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K0 + 1)
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
        deltaStar S.core.betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
          B R certificate S.Tsource deltaStar S.core.betaProt
            S.alpha S.beta S.qTilde)
        S.placementSeed := by
  exact
    bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
      B R certificate (R.paperFixedExceptionalFactors deltaStar)
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
        B R certificate S.Tsource deltaStar S.core.betaProt
          S.alpha S.beta S.qTilde)
      S.placementSeed S.placedFeasible S.sourceState.rowIntegral
        S.sourceState.deficitSupportedOnPrimeBand S.prebridge

/-! ## A symmetric-placement coordinate-fit lemma -/

/-- On a zero-head cell, an arbitrary symmetric real cell-mass change is
dominated by the protected layer as soon as its negative part fits in that
layer.  This is the general real-mass form needed for the combined
nearest-integer and height correction. -/
theorem
    bankPaperCanonicalScaledActiveSeed_le_protected_add_symmetricRebalance
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
    (deltaStar betaProt : Real)
    (T : BarycentricTarget B.sampleData) (q mass : Real)
    (m : B.sampleData.Sample) (sigma : PhysicalSign)
    (hcell : B.sampleData.cellOf m = (none, sigma))
    (hpool : B.sampleData.value m ∈
      R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1)
    (hloss :
      -mass ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L)) :
    bankPaperCanonicalScaledActiveSeed T q m ≤
      bankPaperCanonicalGuardedSmoothProtectedLayer (K := K)
          B R certificate deltaStar betaProt (B.sampleData.value m) +
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q) mass mass m := by
  have hcard : 0 <
      (Fintype.card
        (B.sampleData.SampleAt (none, sigma)) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos (none, sigma)
  have hpointLoss :
      -mass /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) ≤
        betaProt / B.L := by
    apply (div_le_iff₀ hcard).2
    simpa only [mul_comm] using hloss
  have hpointLoss' :
      -(mass /
          Fintype.card (B.sampleData.SampleAt (none, sigma))) ≤
        betaProt / B.L := by
    simpa only [neg_div] using hpointLoss
  have hold :
      bankPaperCanonicalScaledActiveSeed T q m =
        (q * T.baseline.cellMass (none, sigma)) /
          Fintype.card (B.sampleData.SampleAt (none, sigma)) := by
    unfold bankPaperCanonicalScaledActiveSeed BaselineAllocation.baseWeight
    rw [hcell]
    ring
  rw [
    bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
      B R certificate hpool,
    bankPaperCanonicalSymmetricRebalance_apply_of_zeroHeadCell
      B.sampleData T q mass m sigma hcell,
    hold]
  rw [add_div]
  linarith [hpointLoss']

/-- The pre-rounding scaled barycentric seed has coordinate fit under any
verified symmetric two-zero-cell placement whose negative cell change is
absorbed by the protected layer. -/
theorem
    bankPaperCanonicalActualActiveMeasureConstructor_preRounding_of_symmetricPlacement
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
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (baseSelector : Nat → Real)
    (T : BarycentricTarget B.sampleData) (q mass : Real)
    (hq : 1 ≤ q)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hbetaProt : 0 ≤ betaProt)
    (hminus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) →
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : ∀ m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) →
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hloss : ∀ sigma : PhysicalSign,
      -mass ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (betaProt / B.L))
    (Hplacement :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
        B R certificate fixed deltaStar betaProt baseSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q) mass mass)) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q) mass mass))
      (bankPaperCanonicalScaledActiveSeed T q) := by
  have hvalues : ∀ m : B.sampleData.Sample,
      B.sampleData.value m ∈
        R.roughCanonicalGuardedCandidateSet certificate deltaStar K := by
    intro m
    exact
      (mem_completeRoughRowFiber.mp
        (hactiveSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩))).1
  have hplacement := Hplacement
  unfold BankPaperCanonicalGuardedStructuredAdditivePlacement at hplacement
  have hselectorNonneg : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 ≤
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt baseSelector
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q) mass mass) a :=
    fun a ha => (hplacement.1 a ha).1
  apply
    (bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
      B.sampleData T
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt baseSelector
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed T q) mass mass))
      q hsep hvalues hselectorNonneg).2
  refine ⟨hq, ?_⟩
  intro m
  rw [
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
      (K := K) B R certificate baseSelector
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q) mass mass)
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
    bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
      B.sampleData
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q) mass mass)
        hsep m]
  rcases hcell : B.sampleData.cellOf m with ⟨head, sigma⟩
  cases head with
  | none =>
      apply
        bankPaperCanonicalScaledActiveSeed_le_protected_add_symmetricRebalance
          (K := K) B R certificate deltaStar betaProt T q mass
            m sigma hcell
      · cases sigma with
        | minus => exact hminus m hcell
        | plus => exact hplus m hcell
      · exact hloss sigma
  | some _head =>
      have hunchanged :
          bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q) mass mass m =
            bankPaperCanonicalScaledActiveSeed T q m := by
        simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
          bankPaperCanonicalUniformCellIncrement, hcell]
      rw [hunchanged]
      exact le_add_of_nonneg_left
        (bankPaperCanonicalGuardedSmoothProtectedLayer_nonneg
          (K := K) (deltaStar := deltaStar)
          B R certificate hbetaProt (B.sampleData.value m))

/-! ## Exact top-frozen specialization -/

/-- The literal active and placement masses expose the intended split:
the barycentric active seed has mass `qTilde`, while the combined
nearest-integer and height placement has mass `sourceQ0 - d`. -/
theorem
    bankPaperCanonicalSectionNineTopFrozen_preRoundingActive_postRoundingPlacement_masses
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (K0 : Nat) (deltaStar : Real)
    (core : BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
      B R certificate K0 deltaStar)
    (Tsource : BarycentricTarget B.sampleData)
    (qTilde : Real) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalScaledActiveSeed Tsource qTilde) = qTilde ∧
      bankPaperCanonicalLiteralActiveMass B.sampleData
          (bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
            B R certificate K0 deltaStar core Tsource qTilde) =
        bankPaperCanonicalSectionNineTopFrozenSourceQ0
            B R certificate K0 deltaStar core qTilde -
          (core.d : Real) := by
  exact
    ⟨bankPaperCanonicalLiteralActiveMass_scaledActiveSeed Tsource qTilde,
      bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourcePlacementSeed_eq_q0_sub
        B R certificate K0 deltaStar core Tsource qTilde⟩

/-- The actual-measure constructor for the top-frozen placement keeps the
pre-rounding barycentric active seed.  The only loss premise concerns the
negative part of the *combined* nearest-integer and height cell change.
No post-rounding barycentric target occurs in the statement. -/
theorem
    bankPaperCanonicalActualActiveMeasureConstructor_sectionNineTopFrozen_preRounding
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (K0 : Nat) (deltaStar : Real)
    (core : BankPaperCanonicalSectionNineSymmetricHeightCoreInputsAt
      B R certificate K0 deltaStar)
    (Tsource : BarycentricTarget B.sampleData)
    (qTilde : Real) (hqTilde : 1 ≤ qTilde)
    (hloss : ∀ sigma : PhysicalSign,
      -bankPaperCanonicalSymmetricInitialAndHeightCellMass
          (bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
            B R certificate K0 deltaStar core)
          qTilde core.d ≤
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (core.betaProt / B.L))
    (Hplacement :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K0 + 1)
        B R certificate fixed deltaStar core.betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
            B R certificate Tsource deltaStar core.betaProt
              (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
                B R certificate K0 deltaStar core)
              (bankPaperCanonicalSectionNineTopFrozenSourceBeta
                B R certificate K0 deltaStar core)
              qTilde)
          (bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
            B R certificate K0 deltaStar core Tsource qTilde)) :
    BankPaperCanonicalActualActiveMeasureConstructor B.sampleData Tsource
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K0 + 1) B R certificate Tsource deltaStar
          core.betaProt
          (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
            B R certificate K0 deltaStar core)
          (bankPaperCanonicalSectionNineTopFrozenSourceBeta
            B R certificate K0 deltaStar core)
          qTilde
          (bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
            B R certificate K0 deltaStar core Tsource qTilde))
      (bankPaperCanonicalScaledActiveSeed Tsource qTilde) := by
  let mass : Real :=
    bankPaperCanonicalSymmetricInitialAndHeightCellMass
      (bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
        B R certificate K0 deltaStar core)
      qTilde core.d
  have hseed :
      bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
          B R certificate K0 deltaStar core Tsource qTilde =
        bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed Tsource qTilde)
          mass mass := by
    simpa only [mass] using
      (bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed_eq_combinedRebalance
        B R certificate K0 deltaStar core Tsource qTilde)
  have Hplacement' :
      BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K0 + 1)
        B R certificate fixed deltaStar core.betaProt
          (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
            B R certificate Tsource deltaStar core.betaProt
              (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
                B R certificate K0 deltaStar core)
              (bankPaperCanonicalSectionNineTopFrozenSourceBeta
                B R certificate K0 deltaStar core)
              qTilde)
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            (bankPaperCanonicalScaledActiveSeed Tsource qTilde)
            mass mass) := by
    simpa only [hseed] using Hplacement
  have Hmeasure :=
    bankPaperCanonicalActualActiveMeasureConstructor_preRounding_of_symmetricPlacement
      (K := K0 + 1) B R certificate fixed deltaStar core.betaProt
      (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
        B R certificate Tsource deltaStar core.betaProt
          (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
            B R certificate K0 deltaStar core)
          (bankPaperCanonicalSectionNineTopFrozenSourceBeta
            B R certificate K0 deltaStar core)
          qTilde)
      Tsource qTilde mass hqTilde core.headSeparated core.activeSmooth
        core.betaProt_nonneg core.minusPool core.plusPool
        (by simpa only [mass] using hloss) Hplacement'
  simpa only [
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource,
    hseed] using Hmeasure

end BankPaperRealization

end

end Erdos390.WholePaper
