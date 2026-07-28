import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightLocalInputConnector
import Erdos390.WholePaper.BankPaperCanonicalActualBridgeMassUpperConnector
import Erdos390.WholePaper.BankPaperCanonicalRatioCellMomentTraffic
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenMassSynchronizationConnector
import Erdos390.WholePaper.TangentPaperCleanListAbsorption

/-!
# Exact source/core alignment for the top-frozen symmetric-height source

The literal top-frozen source is initialized from `Tsource` at mass
`qTilde`.  Its nearest-integer correction is made only in the two physical
copies of the zero head cell.  The later symmetric height correction is made
in those same two cells.

This file records the part of the Section 8--9 handoff which is already an
exact consequence of the existing definitions:

* the balanced rough parameters are fixed from `core.betaProt` and
  `core.betaAct`;
* the source-side `q0` is the nearest-integer active mass for the literal
  frozen smooth mass;
* the nested initialization and height rebalances equal the single combined
  normalization-and-height rebalance;
* its literal active mass is exactly `q0 - core.d`; and
* both changes preserve every structured head-prime moment.

It also extracts the only active-seed equality already present in
`BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt`:
the stored active seed is the scaled seed of `core.T` and `core.q0`.

What is deliberately not constructed here is the hard missing bridge between
the two sides.  There is currently no theorem constructing a post-rounding
`BarycentricTarget` whose scaled seed is the rounded `Tsource` seed, and no
theorem proving that the scaled core seed is dominated by the literal
top-frozen placed preselector.  Consequently this file does not construct a
`BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt`, does
not assume either missing assertion, and contains no Proposition 8.7 or
Section 9 conclusion.

The last part repairs a separate dependency-order issue at statement level.
The Section 8 ledger gives a positive `Cq` before any bridge family (hence
before any mesh) is selected.  A transparent continuation type then places
`sigma`, `Cpost`, the mesh-uniform tangent constant, and a positive mesh
threshold before the particular mesh, exactly as required in
`reference/paper.tex`, Sections 8.8 and 9.6.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Canonical source-side choices from the common core -/

/-- The literal balanced rough parameter at level `K0 + 1`. -/
def bankPaperCanonicalSectionNineTopFrozenSourceAlpha
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
      B R certificate K0 deltaStar) : Real :=
  bankPaperCanonicalPostHfitBalancedAlpha
    B c K0 core.betaProt core.betaAct

/-- The total broad-row density used by the balanced rough selector. -/
def bankPaperCanonicalSectionNineTopFrozenSourceBeta
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
      B R certificate K0 deltaStar) : Real :=
  core.betaProt + core.betaAct

/-- The literal protected mass of the guarded frozen smooth row. -/
def bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
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
      B R certificate K0 deltaStar) : Real :=
  bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K0 + 1)
    B R certificate deltaStar core.betaProt
      (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
        B R certificate K0 deltaStar core)

/-- The source-side nearest-integer active mass.  This is the value which
the eventual core must identify with `core.q0`; no such identification is
assumed by this definition. -/
def bankPaperCanonicalSectionNineTopFrozenSourceQ0
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
    (qTilde : Real) : Real :=
  bankPaperCanonicalSmoothInitialActiveMass
    (bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
      B R certificate K0 deltaStar core)
    qTilde

/-- The literal nearest-integer source seed, still based on `Tsource` and
`qTilde`. -/
def bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed
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
    (qTilde : Real) : B.sampleData.Sample → Real :=
  bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
    B R certificate Tsource deltaStar core.betaProt
      (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
        B R certificate K0 deltaStar core)
      qTilde

/-- The honest literal placement seed: first perform the nearest-integer
normalization and then the symmetric integer height correction. -/
def bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
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
    (qTilde : Real) : B.sampleData.Sample → Real :=
  bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
    (bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed
      B R certificate K0 deltaStar core Tsource qTilde)
    (bankPaperCanonicalSymmetricHeightCellMass core.d)
    (bankPaperCanonicalSymmetricHeightCellMass core.d)

/-! ## Exact mass and placement identities -/

/-- Pointwise frozen-mass synchronization is exactly what is required to
identify the source-side nearest-integer mass with the analytic `q0`
family.  No target or seed equality is used. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenSourceQ0_eq_smoothQ0Family
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
    (mFrozen qTildeFamily : Nat → Real) (qTilde : Real)
    (hmFrozen :
      mFrozen B.sampleData.n =
        bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
          B R certificate K0 deltaStar core)
    (hqTilde : qTildeFamily B.sampleData.n = qTilde) :
    bankPaperCanonicalSectionNineTopFrozenSourceQ0
        B R certificate K0 deltaStar core qTilde =
      bankPaperCanonicalSmoothQ0Family
        mFrozen qTildeFamily B.sampleData.n := by
  simp only [bankPaperCanonicalSectionNineTopFrozenSourceQ0,
    bankPaperCanonicalSmoothQ0Family, hmFrozen, hqTilde]

/-- The existing row-mass synchronization theorem specializes directly to
the canonical source parameters.  The required value support is one of the
genuine geometric fields of `core`; no source-state package is used. -/
theorem
    bankPaperCanonicalInitialSmoothFrozenMass_eq_sectionNineTopFrozenSourceFrozenMass
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
    (Tsource : BarycentricTarget B.sampleData) (qTilde : Real)
    (hn : 0 < B.sampleData.n)
    (hdeltaUpper : deltaStar ≤ 1) :
    R.bankPaperCanonicalInitialSmoothFrozenMass (K := K0 + 1)
        certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
            (K := K0 + 1) B R certificate deltaStar core.betaProt
              (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
                B R certificate K0 deltaStar core)
              (bankPaperCanonicalSectionNineTopFrozenSourceBeta
                B R certificate K0 deltaStar core)
              (bankPaperCanonicalScaledActiveSeed Tsource qTilde))
          qTilde =
      bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
        B R certificate K0 deltaStar core := by
  simpa only [
    bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass] using
    (bankPaperCanonicalInitialSmoothFrozenMass_eq_topFrozenSmoothFrozenMass_of_scaledSeed
      (K := K0 + 1) B R certificate Tsource deltaStar core.betaProt
        (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
          B R certificate K0 deltaStar core)
        (bankPaperCanonicalSectionNineTopFrozenSourceBeta
          B R certificate K0 deltaStar core)
        qTilde hn hdeltaUpper
        (fun m =>
          core.activeSmooth
            (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)))

/-- Consequently the analytic `q0` family and literal top-frozen `q0`
coincide whenever `mFrozen` is the already-audited Section 8 row-local
frozen-mass definition at this index. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenSourceQ0_eq_smoothQ0Family_of_initialSmoothFrozenMass
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
    (mFrozen qTildeFamily : Nat → Real) (qTilde : Real)
    (hmFrozen :
      mFrozen B.sampleData.n =
        R.bankPaperCanonicalInitialSmoothFrozenMass (K := K0 + 1)
          certificate deltaStar
            (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
              (K := K0 + 1) B R certificate deltaStar core.betaProt
                (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
                  B R certificate K0 deltaStar core)
                (bankPaperCanonicalSectionNineTopFrozenSourceBeta
                  B R certificate K0 deltaStar core)
                (bankPaperCanonicalScaledActiveSeed Tsource qTilde))
            qTilde)
    (hqTilde : qTildeFamily B.sampleData.n = qTilde)
    (hn : 0 < B.sampleData.n)
    (hdeltaUpper : deltaStar ≤ 1) :
    bankPaperCanonicalSectionNineTopFrozenSourceQ0
        B R certificate K0 deltaStar core qTilde =
      bankPaperCanonicalSmoothQ0Family
        mFrozen qTildeFamily B.sampleData.n := by
  apply
    bankPaperCanonicalSectionNineTopFrozenSourceQ0_eq_smoothQ0Family
      B R certificate K0 deltaStar core mFrozen qTildeFamily qTilde
  · exact hmFrozen.trans
      (bankPaperCanonicalInitialSmoothFrozenMass_eq_sectionNineTopFrozenSourceFrozenMass
        B R certificate K0 deltaStar core Tsource qTilde
          hn hdeltaUpper)
  · exact hqTilde

/-- The literal rounded seed has exactly the source-side `q0` mass. -/
theorem
    bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourceRoundedSeed
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
        (bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed
          B R certificate K0 deltaStar core Tsource qTilde) =
      bankPaperCanonicalSectionNineTopFrozenSourceQ0
        B R certificate K0 deltaStar core qTilde := by
  simpa only [bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed,
    bankPaperCanonicalSectionNineTopFrozenSourceQ0,
    bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass,
    bankPaperCanonicalTopFrozenRoundedActiveMass] using
    (bankPaperCanonicalLiteralActiveMass_topFrozenRoundedActiveSeed
      (K := K0 + 1) B R certificate Tsource deltaStar core.betaProt
        (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
          B R certificate K0 deltaStar core)
        qTilde)

/-- Strongest unconditional seed equality presently available: the nested
nearest-integer and height changes are exactly the existing single combined
normalization-and-height rebalance of the original `qTilde`-scaled seed. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed_eq_combinedRebalance
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
    bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
        B R certificate K0 deltaStar core Tsource qTilde =
      bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalScaledActiveSeed Tsource qTilde)
        (bankPaperCanonicalSymmetricInitialAndHeightCellMass
          (bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
            B R certificate K0 deltaStar core)
          qTilde core.d)
        (bankPaperCanonicalSymmetricInitialAndHeightCellMass
          (bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
            B R certificate K0 deltaStar core)
          qTilde core.d) := by
  funext m
  unfold bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
  unfold bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed
  unfold bankPaperCanonicalTopFrozenRoundedActiveSeed
  unfold bankPaperCanonicalTwoZeroHeadCellRebalance
  unfold bankPaperCanonicalUniformCellIncrement
  unfold bankPaperCanonicalTopFrozenNearestIntegerCellMass
  unfold bankPaperCanonicalTopFrozenRoundedActiveMass
  unfold bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
  unfold bankPaperCanonicalSymmetricHeightCellMass
  unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
  unfold bankPaperCanonicalSmoothActiveMassAt
  split_ifs <;> ring

/-- The canonical placement has the paper's exact final active mass. -/
theorem
    bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourcePlacementSeed
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
        (bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
          B R certificate K0 deltaStar core Tsource qTilde) =
      bankPaperCanonicalSmoothActiveMassAt
        (bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
          B R certificate K0 deltaStar core)
        qTilde core.d := by
  rw [
    bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed_eq_combinedRebalance]
  exact
    bankPaperCanonicalLiteralActiveMass_symmetricInitialAndHeightRebalance
      B.sampleData Tsource
        (bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
          B R certificate K0 deltaStar core)
        qTilde core.d

/-- Equivalently, the placement mass is source-side `q0 - d`. -/
theorem
    bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourcePlacementSeed_eq_q0_sub
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
        (bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
          B R certificate K0 deltaStar core Tsource qTilde) =
      bankPaperCanonicalSectionNineTopFrozenSourceQ0
          B R certificate K0 deltaStar core qTilde -
        (core.d : Real) := by
  simpa only [bankPaperCanonicalSectionNineTopFrozenSourceQ0,
    bankPaperCanonicalSmoothActiveMassAt] using
    (bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourcePlacementSeed
      B R certificate K0 deltaStar core Tsource qTilde)

/-- Both zero-cell steps preserve every structured head-prime moment. -/
theorem
    sum_bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed_mul_headValuation_eq_qTilde
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
    (qTilde : Real)
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat)
    (hpattern : B.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime E)
    (p : {p : Nat // p ∈ P}) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
            B R certificate K0 deltaStar core Tsource qTilde m *
          valuation p.1 (B.sampleData.value m)) =
      ∑ m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed Tsource qTilde m *
          valuation p.1 (B.sampleData.value m) := by
  calc
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
            B R certificate K0 deltaStar core Tsource qTilde m *
          valuation p.1 (B.sampleData.value m)) =
        ∑ m : B.sampleData.Sample,
          bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed
              B R certificate K0 deltaStar core Tsource qTilde m *
            valuation p.1 (B.sampleData.value m) := by
      simpa only [
        bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed] using
        (sum_bankPaperCanonicalTwoZeroHeadCellRebalance_mul_valuation_eq
          B.sampleData hprime E hpattern
            (bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed
              B R certificate K0 deltaStar core Tsource qTilde)
            (bankPaperCanonicalSymmetricHeightCellMass core.d)
            (bankPaperCanonicalSymmetricHeightCellMass core.d) p)
    _ = ∑ m : B.sampleData.Sample,
          bankPaperCanonicalScaledActiveSeed Tsource qTilde m *
            valuation p.1 (B.sampleData.value m) := by
      simpa only [
        bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed] using
        (sum_bankPaperCanonicalTopFrozenRoundedActiveSeed_mul_headValuation_eq_qTilde
          (K := K0 + 1) B R certificate Tsource deltaStar
            core.betaProt
            (bankPaperCanonicalSectionNineTopFrozenSourceAlpha
              B R certificate K0 deltaStar core)
            qTilde hprime E hpattern p)

/-! ## What the current source package really aligns -/

/-- The two baseline equalities already stored in the current source
package force its `activeSeed` to be the scaled core seed.  This theorem
does not identify that active seed with the rounded source seed. -/
theorem
    BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt.activeSeed_eq_scaledCoreSeed
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
    S.activeSeed =
      bankPaperCanonicalScaledActiveSeed S.core.T S.core.q0 := by
  funext m
  calc
    S.activeSeed m = B.baseline.baseWeight m :=
      (S.baseline_seed m).symm
    _ = bankPaperCanonicalScaledActiveSeed S.core.T S.core.q0 m :=
      S.core.baseline_seed m

/-- Hence the stored active seed has literal mass `core.q0`. -/
theorem
    BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt.literalActiveMass_activeSeed
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
    bankPaperCanonicalLiteralActiveMass B.sampleData S.activeSeed =
      S.core.q0 := by
  rw [S.activeSeed_eq_scaledCoreSeed]
  exact
    bankPaperCanonicalLiteralActiveMass_scaledActiveSeed
      S.core.T S.core.q0

/-!
## Exact remaining dependency map

The declarations above close only definitional and previously proved
finite identities.  A constructor for
`BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt` still
has to supply the following arrows, none of which is asserted here.

1. Instantiate `core.q0` by
   `bankPaperCanonicalSmoothQ0Family mFrozen qTilde n` and use
   `bankPaperCanonicalSectionNineTopFrozenSourceQ0_eq_smoothQ0Family_of_initialSmoothFrozenMass`
   to identify it with the literal rounded mass.
2. Instantiate `core.d` by
   `bankPaperCanonicalSmoothDIntFamily mu logY Lambda0 mFrozen qTilde n`.
   The existing scalar-capacity and protected-absorption theorems then apply
   to these exact scalar choices.
3. Construct the post-rounding `core.T` and prove that its scaled seed is
   the active measure retained by the bridge.  No such target constructor is
   currently exported.
4. Prove coordinate fit/dominance of that scaled core seed under the
   preselector built from
   `bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed`.  The existing
   `bankPaperCanonicalActualActiveMeasureConstructor_symmetricHeight` starts
   from a scaled seed before the height rebalance and therefore does not
   discharge the top-frozen initialization step by itself.
5. Construct `sourceState` with
   `bankPaperCanonicalTopFrozenRoundedSelectorSourceState_of_qTildeSource`;
   prove placed feasibility; and construct `prebridge` with
   `bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_twoZeroHeadCells_of_active`
   after proving
   `BankPaperCanonicalTopFrozenRoundedPlacementOutsideCompatibility`.

The dependent target envelopes, ledgers, slack, and Proposition 8.7
conclusion belong strictly after these finite source/core steps and are not
part of this alignment connector.
-/

end BankPaperRealization

/-! ## A bridge-mass constant selected before every mesh -/

/-- The analytic ledger chooses a positive upper-bound constant for the
literal `q0` family without mentioning any mesh, head, or bridge family. -/
theorem
    exists_bankPaperCanonical_smoothQ0_upper_before_mesh_of_sectionEightLedger
    (W K : Nat) (c betaAct : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∃ Cq : Real, 0 < Cq ∧
      ∀ᶠ n : Nat in atTop,
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n ≤
          Cq * secondOrderScale n := by
  let rawBase : Nat → Real := fun n =>
    bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct
  have Hraw : rawBase =O[atTop] secondOrderScale := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have HqTilde : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      rawBase qTilde Hraw (by simpa only [rawBase] using Hledger.1)
  have Hq0 :
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
        secondOrderScale :=
    bankPaperCanonicalSmoothQ0Family_isBigO
      mFrozen qTilde HqTilde
  rcases (isBigO_iff').mp Hq0 with ⟨Cq, hCq, hbound⟩
  refine ⟨Cq, hCq, ?_⟩
  filter_upwards [hbound, eventually_secondOrderScale_pos] with
    n hboundN hscaleN
  have habs :
      |bankPaperCanonicalSmoothQ0Family mFrozen qTilde n| ≤
        Cq * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscaleN] using hboundN
  exact
    (le_abs_self
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)).trans habs

/-- Strong paper-order form: one `Cq` is chosen from the ledger before the
types of the later head and bands and before the bridge family.  Every
subsequent scaled-seed bridge family inherits the same eventual bound.
In particular, a mesh-dependent band type may be instantiated only after
`Cq` has already been fixed. -/
theorem
    exists_bankPaperCanonical_actualBridge_q_upper_before_mesh_of_sectionEightLedger_scaledSeed
    (W K : Nat) (c betaAct : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∃ Cq : Real, 0 < Cq ∧
      (∀ᶠ n : Nat in atTop,
        bankPaperCanonicalSmoothQ0Family mFrozen qTilde n ≤
          Cq * secondOrderScale n) ∧
      ∀ {Head Band : Type*}
        [Fintype Head] [DecidableEq Head] [Nonempty Head]
        [Fintype Band] [DecidableEq Band],
        ∀ B : Nat → BridgeData Head Band,
          (∀ᶠ n : Nat in atTop,
            ∃ T : BarycentricTarget (B n).sampleData,
              ∀ m : (B n).sampleData.Sample,
                (B n).baseline.baseWeight m =
                  bankPaperCanonicalScaledActiveSeed T
                    (bankPaperCanonicalSmoothQ0Family
                      mFrozen qTilde n) m) →
          ∀ᶠ n : Nat in atTop,
            (B n).q ≤ Cq * secondOrderScale n := by
  obtain ⟨Cq, hCq, hq0Upper⟩ :=
    exists_bankPaperCanonical_smoothQ0_upper_before_mesh_of_sectionEightLedger
      W K c betaAct logY Lambda0 mFrozen qTilde Hledger
  refine ⟨Cq, hCq, hq0Upper, ?_⟩
  intro Head Band instFintypeHead instDecidableHead instNonemptyHead
    instFintypeBand instDecidableBand B hseed
  filter_upwards [hq0Upper, hseed] with n hq0UpperN hseedN
  obtain ⟨T, hT⟩ := hseedN
  rw [BridgeData.q_eq_of_baseWeight_eq_scaledActiveSeed
    (B n) T
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n) hT]
  exact hq0UpperN

/-! ## Transparent constants-before-mesh continuation -/

/-- The numerical dependency order required by the paper.

`Cq`, `W`, `r0`, and `rho` are fixed outside this definition.  The surviving
slack, Proposition 8.7 constant, mesh-uniform tangent constant, and positive
mesh threshold are then selected.  Only afterward is a particular mesh
quantified.  `localAt` is deliberately abstract: this definition records
only dependency order and does not assert the missing source/core
construction or a local P87 conclusion. -/
def BankPaperCanonicalSectionNineTopFrozenPaperOrderedMeshContinuation
    (r0 rho : Real) (W : Nat) (Cq : Real)
    (localAt :
      ∀ {delta eta : Real},
        RegularRelativeMesh.Mesh delta eta →
          0 < delta → Real → Real → Prop) : Prop :=
  ∃ sigma Cpost tangentConstant meshTol : Real,
    0 < sigma ∧
      0 ≤ Cpost ∧
      0 < tangentConstant ∧
      (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
      0 < meshTol ∧
      meshTol ≤
        bankPaperCanonicalRatioCellPaperWidthChoice
          (tangentPaperCleanListDensity W r0)
          sigma rho tangentConstant ∧
      ∀ {delta eta : Real}
        (M : RegularRelativeMesh.Mesh delta eta)
        (hdelta : 0 < delta),
        delta + M.ratio ≤ meshTol →
          localAt M hdelta sigma Cpost

/-- Specialize a paper-ordered continuation to one later mesh.  The returned
width inequality is the exact one consumed by the Section 9 event step. -/
theorem
    exists_bankPaperCanonicalSectionNineTopFrozen_numericalData_atMesh_of_paperOrdered
    {r0 rho : Real} {W : Nat} {Cq : Real}
    {localAt :
      ∀ {delta eta : Real},
        RegularRelativeMesh.Mesh delta eta →
          0 < delta → Real → Real → Prop}
    (H :
      BankPaperCanonicalSectionNineTopFrozenPaperOrderedMeshContinuation
        r0 rho W Cq localAt)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta) :
    ∃ sigma Cpost tangentConstant meshTol : Real,
      0 < sigma ∧
        0 ≤ Cpost ∧
        0 < tangentConstant ∧
        (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
        0 < meshTol ∧
        meshTol ≤
          bankPaperCanonicalRatioCellPaperWidthChoice
            (tangentPaperCleanListDensity W r0)
            sigma rho tangentConstant ∧
        (delta + M.ratio ≤ meshTol →
          delta + M.ratio ≤
              bankPaperCanonicalRatioCellPaperWidthChoice
                (tangentPaperCleanListDensity W r0)
                sigma rho tangentConstant ∧
            localAt M hdelta sigma Cpost) := by
  obtain ⟨sigma, Cpost, tangentConstant, meshTol,
    hsigma, hCpost, htangent, hcoefficient, hmeshTol,
    hwidth, hlocal⟩ := H
  exact
    ⟨sigma, Cpost, tangentConstant, meshTol, hsigma, hCpost,
      htangent, hcoefficient, hmeshTol, hwidth, fun hmesh =>
        ⟨hmesh.trans hwidth, hlocal M hdelta hmesh⟩⟩

end

end Erdos390.WholePaper
