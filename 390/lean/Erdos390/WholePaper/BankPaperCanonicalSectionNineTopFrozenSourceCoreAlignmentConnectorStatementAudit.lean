import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSourceCoreAlignmentConnector

/-!
# Statement audit for top-frozen source/core alignment

The examples below expose the exact source-side choices, the strongest
unconditional placement equality, and the constants-before-mesh order.
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

/-! ## Expanded finite identities -/

example
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
    bankPaperCanonicalSectionNineTopFrozenSourceAlpha
        B R certificate K0 deltaStar core =
      bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 core.betaProt core.betaAct := by
  rfl

example
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
    bankPaperCanonicalSectionNineTopFrozenSourceBeta
        B R certificate K0 deltaStar core =
      core.betaProt + core.betaAct := by
  rfl

/-- Expanded strongest seed equality.  In particular, its right side still
uses `Tsource` and `qTilde`; it is not silently replaced by the core seed. -/
example
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
          qTilde core.d) :=
  bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed_eq_combinedRebalance
    B R certificate K0 deltaStar core Tsource qTilde

/-- Expanded mass synchronization.  The only geometric inputs beyond the
core are the paper-range inequalities already required by the underlying
audited theorem. -/
example
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
        B R certificate K0 deltaStar core :=
  bankPaperCanonicalInitialSmoothFrozenMass_eq_sectionNineTopFrozenSourceFrozenMass
    B R certificate K0 deltaStar core Tsource qTilde hn hdeltaUpper

/-- Expanded projection from the current source package.  This says only
that `activeSeed` is the scaled core seed; it does not identify the rounded
source seed with it. -/
example
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
      bankPaperCanonicalScaledActiveSeed S.core.T S.core.q0 :=
  S.activeSeed_eq_scaledCoreSeed

end BankPaperRealization

/-! ## Expanded pre-mesh quantifiers -/

/-- The positive bridge-mass constant is outside the later choices of head,
band, and bridge family. -/
example
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
            (B n).q ≤ Cq * secondOrderScale n :=
  exists_bankPaperCanonical_actualBridge_q_upper_before_mesh_of_sectionEightLedger_scaledSeed
    W K c betaAct logY Lambda0 mFrozen qTilde Hledger

/-- Literal unfolding of the paper-order continuation.  Every numerical
witness and `meshTol` precedes the universal particular mesh. -/
example
    (r0 rho : Real) (W : Nat) (Cq : Real)
    (localAt :
      ∀ {delta eta : Real},
        RegularRelativeMesh.Mesh delta eta →
          0 < delta → Real → Real → Prop) :
    BankPaperCanonicalSectionNineTopFrozenPaperOrderedMeshContinuation
        r0 rho W Cq localAt ↔
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
              localAt M hdelta sigma Cpost := by
  rfl

/-! ## Complete declaration census -/

#check BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourceAlpha
#check BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourceBeta
#check
  BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourceFrozenMass
#check BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourceQ0
#check
  BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourceRoundedSeed
#check
  BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed
#check
  BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourceQ0_eq_smoothQ0Family
#check
  BankPaperRealization.bankPaperCanonicalInitialSmoothFrozenMass_eq_sectionNineTopFrozenSourceFrozenMass
#check
  BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourceQ0_eq_smoothQ0Family_of_initialSmoothFrozenMass
#check
  BankPaperRealization.bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourceRoundedSeed
#check
  BankPaperRealization.bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed_eq_combinedRebalance
#check
  BankPaperRealization.bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourcePlacementSeed
#check
  BankPaperRealization.bankPaperCanonicalLiteralActiveMass_sectionNineTopFrozenSourcePlacementSeed_eq_q0_sub
#check
  BankPaperRealization.sum_bankPaperCanonicalSectionNineTopFrozenSourcePlacementSeed_mul_headValuation_eq_qTilde
#check
  BankPaperRealization.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt.activeSeed_eq_scaledCoreSeed
#check
  BankPaperRealization.BankPaperCanonicalSectionNineTopFrozenSymmetricHeightSourceInputsAt.literalActiveMass_activeSeed
#check
  exists_bankPaperCanonical_smoothQ0_upper_before_mesh_of_sectionEightLedger
#check
  exists_bankPaperCanonical_actualBridge_q_upper_before_mesh_of_sectionEightLedger_scaledSeed
#check
  BankPaperCanonicalSectionNineTopFrozenPaperOrderedMeshContinuation
#check
  exists_bankPaperCanonicalSectionNineTopFrozen_numericalData_atMesh_of_paperOrdered

end

end Erdos390.WholePaper
