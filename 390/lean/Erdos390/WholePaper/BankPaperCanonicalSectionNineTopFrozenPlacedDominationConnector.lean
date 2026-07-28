import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSourceCoreAlignmentConnector
import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellMeasureConnector

/-!
# Frozen-top placed domination from the symmetric-height core

The frozen-top source selector and the active bridge measure play different
roles.  The former is based on the literal nearest-integer source, whereas
the latter is the scaled barycentric seed stored in the Section 9 core.

This file isolates the downstream part which does not require identifying
those two seeds.  Once the placement seed is chosen to be the symmetric
height rebalance of the scaled core seed, the already proved protected-loss
bound in `core.fitLoss` gives coordinate fit under the literal frozen-top
Post-Hfit preselector.  Pointwise feasibility of that preselector then gives
the full actual-active-measure constructor.

The final constructor packages these facts into the selector-correct
frozen-top source interface.  Its remaining inputs are exactly the genuine
source-side tasks: the rounded source state, feasibility, and the signed
prebridge ledger for this explicit placement seed.  No source/core seed
equality and no Proposition 8.7 conclusion is included.
-/

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus

noncomputable section

namespace BankPaperRealization

/-! ## The explicit core-height placement seed -/

/-- The placement seed obtained by applying the paper's symmetric height
change to the scaled barycentric seed already stored in the Section 9 core.

This definition deliberately does not identify the core seed with the
literal nearest-integer frozen-top seed. -/
def bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
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
      B R certificate K0 deltaStar) :
    B.sampleData.Sample → Real :=
  bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
    (bankPaperCanonicalScaledActiveSeed core.T core.q0)
    (bankPaperCanonicalSymmetricHeightCellMass core.d)
    (bankPaperCanonicalSymmetricHeightCellMass core.d)

/-- The explicit core-height placement has the exact post-height mass
`core.q0 - core.d`. -/
theorem
    bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenCoreHeightPlacementSeed
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
      B R certificate K0 deltaStar) :
    bankPaperCanonicalLiteralActiveMass B.sampleData
        (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
          B R certificate K0 deltaStar core) =
      core.q0 - (core.d : Real) := by
  simpa only [
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed] using
    (bankPaperCanonicalLiteralActiveMass_symmetricHeightRebalance
      B.sampleData core.T core.q0 core.d)

/-- Unless the height correction vanishes, the post-height placement seed
cannot itself be the pre-height scaled core seed: their literal masses are
`core.q0 - core.d` and `core.q0`, respectively.

This is the exact boundary of the downstream domination theorem below.  It
proves that the protected layer can carry the pre-height seed under the
post-height selector; it does not turn that seed into the paper's
post-height barycentric active measure. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed_ne_scaledCoreSeed_of_d_ne_zero
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
    (hd : core.d ≠ 0) :
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
        B R certificate K0 deltaStar core ≠
      bankPaperCanonicalScaledActiveSeed core.T core.q0 := by
  intro hseed
  have hmass :=
    congrArg (bankPaperCanonicalLiteralActiveMass B.sampleData) hseed
  rw [
    bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenCoreHeightPlacementSeed,
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed] at hmass
  have hdReal : (core.d : Real) = 0 := by
    linarith
  apply hd
  exact_mod_cast hdReal

/-! ## Coordinate domination -/

/-- The scaled core seed fits pointwise below the literal frozen-top
Post-Hfit preselector built from the explicit core-height placement.

Only the geometric and protected-loss fields already present in `core` are
used.  In particular, no feasibility, source-state, prebridge, or target
envelope premise is needed for this coordinate inequality. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacedPreSelector_coordinateFit
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
    (alpha beta qTilde : Real) :
    BankPaperCanonicalActualCoordinateFit B.sampleData core.T
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K0 + 1) B R certificate Tsource deltaStar
          core.betaProt alpha beta qTilde
          (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
            B R certificate K0 deltaStar core))
      core.q0 := by
  simpa only [
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
    (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_coordinateFit_symmetricHeight
      (K := K0 + 1) B R certificate deltaStar core.betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
          B R certificate Tsource deltaStar core.betaProt
            alpha beta qTilde)
        core.T core.q0 core.d core.headSeparated core.betaProt_nonneg
        core.minusPool core.plusPool core.fitLoss)

/-! ## Full actual measure from placed feasibility -/

/-- Feasibility of the explicit frozen-top placed preselector promotes the
preceding coordinate fit to the complete actual-active-measure constructor
for the scaled core seed.

The upper half of the feasibility pair is retained because this theorem is
designed to consume the exact `placedFeasible` field used by the frozen-top
source package; the actual-measure proof itself needs only nonnegativity. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlaced_actualMeasure
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
    (alpha beta qTilde : Real)
    (hplacedFeasible :
      ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1),
        0 ≤
            bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) B R certificate Tsource deltaStar
                core.betaProt alpha beta qTilde
                (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
                  B R certificate K0 deltaStar core) a ∧
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) B R certificate Tsource deltaStar
                core.betaProt alpha beta qTilde
                (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
                  B R certificate K0 deltaStar core) a ≤ 1) :
    BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData core.T
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K0 + 1) B R certificate Tsource deltaStar
          core.betaProt alpha beta qTilde
          (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
            B R certificate K0 deltaStar core))
      (bankPaperCanonicalScaledActiveSeed core.T core.q0) := by
  have hvalues :
      ∀ m : B.sampleData.Sample,
        B.sampleData.value m ∈
          R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1) := by
    intro m
    exact
      (mem_completeRoughRowFiber.mp
        (core.activeSmooth
          (mem_bankPaperCanonicalStructuredActiveValues.mpr
            ⟨m, rfl⟩))).1
  have hselectorNonneg :
      ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1),
        0 ≤
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
            (K := K0 + 1) B R certificate Tsource deltaStar
              core.betaProt alpha beta qTilde
              (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
                B R certificate K0 deltaStar core) a :=
    fun a ha => (hplacedFeasible a ha).1
  apply
    (bankPaperCanonicalActualActiveMeasureConstructor_iff_coordinateFit
      B.sampleData core.T
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      (bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
        (K := K0 + 1) B R certificate Tsource deltaStar
          core.betaProt alpha beta qTilde
          (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
            B R certificate K0 deltaStar core))
      core.q0 core.headSeparated hvalues hselectorNonneg).2
  exact
    ⟨core.q0_one_le,
      bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacedPreSelector_coordinateFit
        B R certificate K0 deltaStar core Tsource alpha beta qTilde⟩

/-! ## Selector-correct source package -/

/-- Build the complete finite frozen-top source package once its three
genuinely source-dependent objects have been proved for the explicit
core-height placement: source state, placed feasibility, and prebridge
ledger.

The active measure and bridge-baseline identity are consequences, not input
fields, of this constructor. -/
def
    bankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt_of_coreHeightPlacement
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
    (alpha beta qTilde : Real)
    (sourceState :
      BankPaperCanonicalSelectorSourceState
        (W := B.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
          B R certificate Tsource deltaStar core.betaProt
            alpha beta qTilde))
    (placedFeasible :
      ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1),
        0 ≤
            bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) B R certificate Tsource deltaStar
                core.betaProt alpha beta qTilde
                (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
                  B R certificate K0 deltaStar core) a ∧
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) B R certificate Tsource deltaStar
                core.betaProt alpha beta qTilde
                (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
                  B R certificate K0 deltaStar core) a ≤ 1)
    (prebridge :
      BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K0 + 1) B R certificate deltaStar core.betaProt
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
          B R certificate Tsource deltaStar core.betaProt
            alpha beta qTilde)
        (bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
          B R certificate K0 deltaStar core)) :
    BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt
      B R certificate K0 deltaStar where
  core := core
  Tsource := Tsource
  alpha := alpha
  beta := beta
  qTilde := qTilde
  placementSeed :=
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlacementSeed
      B R certificate K0 deltaStar core
  activeSeed := bankPaperCanonicalScaledActiveSeed core.T core.q0
  sourceState := sourceState
  placedFeasible := placedFeasible
  prebridge := prebridge
  activeMeasure :=
    bankPaperCanonicalSectionNineTopFrozenCoreHeightPlaced_actualMeasure
      B R certificate K0 deltaStar core Tsource alpha beta qTilde
        placedFeasible
  baseline_seed := by
    intro m
    exact core.baseline_seed m

end BankPaperRealization

end

end Erdos390.WholePaper
