import Erdos390.WholePaper.BankPaperCanonicalSectionEightPrechargedLogConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightFrozenLogInvarianceConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightOrdinaryLogLedgerConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacementValuationRateConnector
import Erdos390.WholePaper.BankPaperCanonicalP87TargetEnvelopeConnector
import Erdos390.WholePaper.BankPaperCanonicalSmoothProtectedAdditiveRefinement
import Erdos390.WholePaper.BankPaperCanonicalArbitrarySourcePostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenEventStepConnector

/-!
# Paper-faithful finite inputs after the Section 8 height choice

The legacy symmetric-height input fixes a bridge whose baseline has mass
`q0`.  After the integer height `d` is chosen, the paper instead installs a
fresh barycentric target of mass

`qn = q0 - d`.

This file keeps those two stages separate.  A scaffold bridge contributes
only the structured sample needed to define the rounded frozen-top source.
The certificate-dependent logarithmic target is the literal
`log certificate.prechargedTailTarget`; its rounded frozen ledger determines
`A0`.  From the resulting post-height target `Tpost` we construct a new
active-mass bridge `Bpost`, whose baseline is definitionally the scaled
post-height seed and whose partition is the canonical mesh partition.

The source and dependent structures below are finite input packages, not
new analytic assertions.  The source package is discharged by the existing
post-height source-prebridge theorem.  The dependent package lists exactly
the remaining hypotheses consumed by the audited arbitrary-source Post-hfit
producer.  The final adapter packages the result as the public top-frozen
synchronized input for this same `Bpost`, realization, and certificate.
-/

open Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Certificate-dependent post-height scalars -/

/-- The finite-fiber form of the paper's precharged logarithmic target. -/
def bankPaperCanonicalSectionNinePostHeightLogY
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)) : Real :=
  Real.log (certificate.prechargedTailTarget : Real)

/-- The nearest-integer active mass before the height displacement. -/
def bankPaperCanonicalSectionNinePostHeightRoundedQ0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (K : Nat)
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha qTilde : Real) : Real :=
  bankPaperCanonicalTopFrozenRoundedActiveMass (K := K)
    B R certificate deltaStar betaProt alpha qTilde

/-- The complete frozen logarithmic mass of the rounded source, including
the fixed exceptional factors and the state-zero bank. -/
def bankPaperCanonicalSectionNinePostHeightRoundedLambda0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (K : Nat)
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real) : Real :=
  bankPaperCanonicalActualFrozenLogMass B.sampleData
    (R.paperFixedExceptionalFactors deltaStar)
    (baseBankFactors R.exactificationState)
    (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
    (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K)
      B R certificate Tsource deltaStar betaProt alpha beta qTilde)
    (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K)
      B R certificate Tsource deltaStar betaProt alpha qTilde)

/-- The paper's initial post-height physical logarithmic mass:
`A0 = logY - Lambda0 - q0 L`. -/
def bankPaperCanonicalSectionNinePostHeightA0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (K : Nat)
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (Tsource : BarycentricTarget B.sampleData)
    (deltaStar betaProt alpha beta qTilde : Real) : Real :=
  bankPaperCanonicalSectionNinePostHeightLogY B R certificate -
    bankPaperCanonicalSectionNinePostHeightRoundedLambda0
      K B R certificate Tsource deltaStar betaProt alpha beta qTilde -
    bankPaperCanonicalSectionNinePostHeightRoundedQ0
      K B R certificate deltaStar betaProt alpha qTilde * B.L

/-- The active head target left by the same quotient charge. -/
def bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
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
    (deltaStar : Real) :
    {p : Nat // p ∈ P} → Real :=
  fun p =>
    ((certificate.selectorTailTarget R
      (R.paperFixedExceptionalFactors deltaStar)).factorization p.1 : Real)

/-! ## The fresh post-height bridge -/

/-- Data needed before the fresh bridge can be installed.

`Bsource` is only a scaffold carrying the structured sample.  No equality
between its baseline mass and either `q0` or `qn` is requested.  The target
inputs already use the certificate-derived `A0`, so a single realization
and certificate control the source, charge, target, and final bridge. -/
structure BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (deltaStar : Real)
    (hdelta : 0 < delta) where
  Tsource : BarycentricTarget Bsource.sampleData
  betaProt : Real
  betaAct : Real
  qTilde : Real
  d : Int
  exponent : Nat
  hW : Bsource.sampleData.W ≠ 0
  scaleSeparation :
    ScaleSeparation M Bsource.sampleData.n Bsource.sampleData.W
  hlo : ∀ sign, Bsource.sampleData.lo sign =
    physicalBound (I.lower sign) Bsource.sampleData.n
  hhi : ∀ sign, Bsource.sampleData.hi sign =
    physicalBound (I.upper sign) Bsource.sampleData.n
  targetInputs :
    BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      Bsource I
      (bankPaperCanonicalSectionNinePostHeightRoundedQ0
        (K0 + 1) Bsource R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct)
          qTilde)
      (bankPaperCanonicalSectionNinePostHeightA0
        (K0 + 1) Bsource R certificate Tsource deltaStar
          betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            Bsource c K0 betaProt betaAct)
          (betaProt + betaAct) qTilde)
      d exponent
      (bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
        Bsource R certificate deltaStar)

namespace BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}

/-- The balanced smooth-row center used by the actual Post-hfit source. -/
def alpha
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalPostHfitBalancedAlpha
    Bsource c K0 J.betaProt J.betaAct

/-- The total raw-row correction parameter `betaProt + betaAct`. -/
def beta
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  J.betaProt + J.betaAct

/-- The rounded source mass `q0` attached to the bridge inputs. -/
def q0
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightRoundedQ0
    (K0 + 1) Bsource R certificate deltaStar
      J.betaProt J.alpha J.qTilde

/-- The rounded-source frozen logarithmic mass `Lambda0`. -/
def Lambda0
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightRoundedLambda0
    (K0 + 1) Bsource R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.beta J.qTilde

/-- The certificate-dependent initial physical height `A0`. -/
def A0
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightA0
    (K0 + 1) Bsource R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.beta J.qTilde

/-- The active head target attached to the quotient charge. -/
def activeHeadTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    {p : Nat // p ∈ P} → Real :=
  (fun _ =>
    bankPaperCanonicalSectionNinePostHeightActiveHeadTarget
      Bsource R certificate deltaStar) J

/-- The paper's post-height active mass `qn = q0 - d`. -/
def qn
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Real :=
  bankPaperCanonicalSectionNinePostHeightActiveMass J.q0 J.d

/-- The barycentric target constructed before installing the new bridge. -/
def scaffoldTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BarycentricTarget Bsource.sampleData :=
  bankPaperCanonicalSectionNinePostHeightTarget
    Bsource I J.hlo J.hhi J.targetInputs

/-- Positivity of the displayed mesh width follows from the mesh axioms. -/
theorem meshWidth_pos
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    0 < delta + eta := by
  have _hJ : J = J := rfl
  have heta : 0 < eta := M.ratio_pos.trans_le M.ratio_le_eta
  linarith

/-- The fresh bridge with baseline mass exactly `qn` and the canonical
partition selected by the same mesh witness. -/
def postHeightBridge
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M) :=
  bankPaperCanonicalActiveMassBridgeData
    Bsource.sampleData J.scaffoldTarget J.qn
      J.targetInputs.activeMass_pos M hdelta Bsource.n_gt_one
      J.hW J.scaleSeparation none J.meshWidth_pos

@[simp] theorem postHeightBridge_sampleData
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.sampleData = Bsource.sampleData :=
  rfl

@[simp] theorem postHeightBridge_partition
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.partition =
      RegularMeshPrimeCutoffs.Mesh.canonicalPartition
        M hdelta J.postHeightBridge.n_gt_one J.hW J.scaleSeparation :=
  rfl

@[simp] theorem postHeightBridge_q
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.q = J.qn := by
  exact
    bankPaperCanonicalActiveMassBridgeData_q
      Bsource.sampleData J.scaffoldTarget J.qn
        J.targetInputs.activeMass_pos M hdelta Bsource.n_gt_one
        J.hW J.scaleSeparation none J.meshWidth_pos

/-- The physical interval lower endpoints transported to `Bpost`. -/
def postHeightHlo
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    ∀ sign, J.postHeightBridge.sampleData.lo sign =
      physicalBound (I.lower sign) J.postHeightBridge.sampleData.n :=
  J.hlo

/-- The physical interval upper endpoints transported to `Bpost`. -/
def postHeightHhi
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    ∀ sign, J.postHeightBridge.sampleData.hi sign =
      physicalBound (I.upper sign) J.postHeightBridge.sampleData.n :=
  J.hhi

/-- The same numerical post-height target inputs, now indexed by `Bpost`.
Only the bridge's structured sample and logarithmic scale occur in these
fields, and both are unchanged by the active-mass constructor. -/
def postHeightTargetInputs
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      J.postHeightBridge I J.q0 J.A0 J.d J.exponent
        J.activeHeadTarget where
  exponent_pos := J.targetInputs.exponent_pos
  activeMass_pos := J.targetInputs.activeMass_pos
  headMargin := J.targetInputs.headMargin
  headMargin_pos := J.targetInputs.headMargin_pos
  vertex_margin := J.targetInputs.vertex_margin
  zero_margin := J.targetInputs.zero_margin
  physicalEta := J.targetInputs.physicalEta
  physicalEta_pos := J.targetInputs.physicalEta_pos
  minus_below := J.targetInputs.minus_below
  plus_above := J.targetInputs.plus_above

/-- The literal `Tpost` viewed on the fresh bridge. -/
def postHeightTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    BarycentricTarget J.postHeightBridge.sampleData :=
  bankPaperCanonicalSectionNinePostHeightTarget J.postHeightBridge I
    J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs

/-- The fresh bridge target is the target used to construct that bridge. -/
@[simp] theorem postHeightTarget_eq_scaffoldTarget
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightTarget = J.scaffoldTarget :=
  rfl

/-- The scaled seed of mass `qn` installed in the fresh bridge. -/
def postHeightActiveSeed
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.sampleData.Sample → Real :=
  bankPaperCanonicalSectionNinePostHeightActiveSeed
    J.postHeightBridge I J.postHeightHlo J.postHeightHhi
      J.postHeightTargetInputs

/-- The new bridge baseline is exactly the paper-faithful post-height seed. -/
@[simp] theorem postHeightBridge_baseWeight
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightBridge.baseline.baseWeight m =
      J.postHeightActiveSeed m := by
  simpa only [
    postHeightBridge, postHeightActiveSeed,
    bankPaperCanonicalSectionNinePostHeightActiveSeed,
    postHeightTarget_eq_scaffoldTarget] using
    (bankPaperCanonicalActiveMassBridgeData_baseWeight_scaledSeed
      Bsource.sampleData J.scaffoldTarget J.qn
        J.targetInputs.activeMass_pos M hdelta Bsource.n_gt_one
        J.hW J.scaleSeparation none J.meshWidth_pos m)

/-- The rounded `q0` is unchanged when the scaffold baseline is replaced. -/
@[simp] theorem roundedQ0_eq_postHeightBridge
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.q0 =
      bankPaperCanonicalTopFrozenRoundedActiveMass (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt
          J.alpha J.qTilde :=
  rfl

/-- The rounded frozen ledger is likewise independent of the scaffold
baseline and partition. -/
@[simp] theorem roundedLambda0_eq_postHeightBridge
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.Lambda0 =
      bankPaperCanonicalActualFrozenLogMass
        J.postHeightBridge.sampleData
        (R.paperFixedExceptionalFactors deltaStar)
        (baseBankFactors R.exactificationState)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        (bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
          J.postHeightBridge R certificate J.Tsource deltaStar
            J.betaProt J.alpha J.beta J.qTilde)
        (bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
          J.postHeightBridge R certificate J.Tsource deltaStar
            J.betaProt J.alpha J.qTilde) :=
  rfl

end BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

namespace BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}

/-- The nearest-integer active seed of the rounded frozen-top source. -/
def roundedActiveSeed
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) :
    J.postHeightBridge.sampleData.Sample → Real :=
  bankPaperCanonicalTopFrozenRoundedActiveSeed (K := K0 + 1)
    J.postHeightBridge R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.qTilde

/-- The literal rounded frozen-top source on the fresh bridge sample. -/
def roundedSourceSelector
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Nat → Real :=
  bankPaperCanonicalTopFrozenRoundedSourceSelector (K := K0 + 1)
    J.postHeightBridge R certificate J.Tsource deltaStar
      J.betaProt J.alpha J.beta J.qTilde

/-- The source after the complete smooth-row post-height placement. -/
def placedPreSelector
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) : Nat → Real :=
  bankPaperCanonicalSectionNinePostHeightPlacedPreSelector (K := K0 + 1)
    J.postHeightBridge R certificate J.Tsource I
      J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
      deltaStar J.betaProt J.alpha J.beta J.qTilde

end BankPaperCanonicalSectionNinePostHeightBridgeInputsAt

/-! ## Literal source and finite geometry -/

/-- The selector, height, and finite geometry inputs needed to pass from the
rounded source to the fresh post-height active measure.

There is no legacy `SymmetricHeightCoreInputsAt` field.  In particular, no
baseline is pinned to `q0`: every bridge-facing assertion below names
`J.postHeightBridge`, whose mass is `qn`. -/
structure BankPaperCanonicalSectionNinePostHeightSourceInputsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (deltaStar : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta) where
  lowerOne : ∀ sign, 1 ≤ I.lower sign
  upperTwo : ∀ sign, I.upper sign ≤ 2
  upperBroad : ∀ sign,
    physicalBound (I.upper sign) J.postHeightBridge.sampleData.n ≤
      2 * J.postHeightBridge.sampleData.n -
        (K0 + 1) *
          upperTailLength c J.postHeightBridge.sampleData.n
  qn_one_le : 1 ≤ J.qn
  hprime : ∀ p ∈ P, p.Prime
  hpattern :
    J.postHeightBridge.sampleData.pattern =
      PaperHeadSimplex.pattern P hprime J.exponent
  headPrimes : primesUpTo J.postHeightBridge.sampleData.W ⊆ P
  headSeparated : J.postHeightBridge.sampleData.HeadPatternsSeparated
  roughDepth :
    (K0 + 1) *
      upperTailLength c J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.sampleData.n
  outsideGuard : ∀ m : J.postHeightBridge.sampleData.Sample,
    J.postHeightBridge.sampleData.value m ∉
      R.roughCanonicalGuardSet certificate deltaStar
  betaProt_nonneg : 0 ≤ J.betaProt
  sourceState :
    BankPaperCanonicalSelectorSourceState
      (W := J.postHeightBridge.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      J.roundedSourceSelector
  Cmass : Real
  density : Real
  Cmass_nonneg : 0 ≤ Cmass
  density_pos : 0 < density
  massUpper :
    J.qn ≤
      Cmass * (J.postHeightBridge.sampleData.n : Real) /
        J.postHeightBridge.L
  cellDensity : ∀ cell : Cell (PaperHeadSimplex.Tag P),
    density * (J.postHeightBridge.sampleData.n : Real) ≤
      (Fintype.card
        (J.postHeightBridge.sampleData.SampleAt cell) : Real)
  combined_dvd :
    centralAnchorDivisor J.postHeightBridge.sampleData.n
          (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
          certificate.q * R.prechargeBaseStateProduct ∣
      centralTailProduct J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)
  base_dvd :
    (baseBankFactors R.exactificationState).prod id ∣
      certificate.prechargedTailTarget
  charge_dvd :
    R.selectorTailCharge
          (R.paperFixedExceptionalFactors deltaStar) ∣
      certificate.prechargedTailTarget
  target_tail :
    certificate.prechargedTailTarget *
          centralAnchorDivisor J.postHeightBridge.sampleData.n
            (centralAnchorCutoff depth J.postHeightBridge.sampleData.n)
            certificate.q =
      centralTailProduct J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)

namespace BankPaperCanonicalSectionNinePostHeightSourceInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}
    {J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta}

/-- Physical geometry puts every occupied active coordinate in the complete
guarded smooth row. -/
theorem activeSmooth
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) :
    bankPaperCanonicalStructuredActiveValues
        J.postHeightBridge.sampleData ⊆
      R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1 :=
  bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
    J.postHeightBridge R certificate deltaStar I S.lowerOne S.upperTwo
      J.postHeightHlo J.postHeightHhi S.roughDepth S.outsideGuard

/-- The same interval geometry places every occupied active value in the
broad lower block used by arbitrary-seed replacement. -/
theorem activeBroad
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightBridge.sampleData.value m ∈
      roughBroadLowerBlock J.postHeightBridge.sampleData.n
        (upperTailLength c J.postHeightBridge.sampleData.n)
        (K0 + 1) :=
  bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
    J.postHeightBridge I
      (upperTailLength c J.postHeightBridge.sampleData.n)
      (K0 + 1) S.lowerOne S.upperTwo J.postHeightHlo
      J.postHeightHhi S.upperBroad m

/-- Every fixed exceptional factor is positive because it lies in the
literal upper tail. -/
theorem fixedPositive
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) :
    ∀ a ∈ R.paperFixedExceptionalFactors deltaStar, 0 < a := by
  have _hS : S = S := rfl
  intro a ha
  have htail :=
    R.paperFixedExceptionalFactors_subset_tail deltaStar ha
  exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1

/-- The existing one-shot source-prebridge theorem supplies the signed
ledger, actual measure, and full structured placement.  Its only remaining
numerical input is the already-required placement room. -/
theorem sourceToPostHeight
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (hroom : J.betaProt + S.Cmass / S.density ≤
      J.postHeightBridge.L) :
    BankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger
        (K := K0 + 1) J.postHeightBridge R certificate deltaStar
          J.betaProt J.roundedSourceSelector J.postHeightActiveSeed ∧
      BankPaperCanonicalActualActiveMeasureConstructor
        J.postHeightBridge.sampleData J.postHeightTarget
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector J.postHeightActiveSeed ∧
      BankPaperCanonicalGuardedStructuredAdditivePlacement
        (K := K0 + 1) J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar) deltaStar J.betaProt
        J.roundedSourceSelector J.postHeightActiveSeed := by
  exact
    bankPaperCanonicalSectionNinePostHeight_sourcePrebridge_actualMeasure_and_placement_of_sourceState
      (K := K0 + 1) J.postHeightBridge R certificate J.Tsource I
        S.lowerOne S.upperTwo J.postHeightHlo J.postHeightHhi
        S.upperBroad deltaStar J.betaProt J.alpha J.beta J.qTilde
        J.postHeightTargetInputs J.roundedQ0_eq_postHeightBridge
        S.qn_one_le S.hprime S.hpattern S.headPrimes
        (by intro p _hp; rfl) S.headSeparated S.roughDepth
        S.outsideGuard S.betaProt_nonneg S.sourceState
        S.Cmass S.density S.Cmass_nonneg S.density_pos
        S.massUpper S.cellDensity hroom

/-- The finite post-height seed has the pointwise `1/L` capacity supplied by
the mass and cell-density inputs. -/
theorem activeSeedUpper
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightActiveSeed m ≤
      (S.Cmass / S.density) / J.postHeightBridge.L := by
  exact
    bankPaperCanonicalSectionNinePostHeightActiveSeed_le_of_massAndCellDensity
      J.postHeightBridge I J.postHeightHlo J.postHeightHhi
        J.postHeightTargetInputs S.Cmass S.density S.Cmass_nonneg
        S.density_pos S.massUpper S.cellDensity m

end BankPaperCanonicalSectionNinePostHeightSourceInputsAt

/-! ## Remaining Proposition 8.7 and slack inputs -/

/-- The genuinely dependent finite tail after the post-height source has
been constructed.

The target envelopes, placed frozen ledger, active ledger, placement-seed
bound, and protected reserve are deliberately not fields: they follow from
the ordinary-log connector, frozen invariance, mass/cell density, and the
protected-refinement theorem.  The sole remaining prime-rate input is the
final placed-selector deficit bound.  Its future uniform derivation is the
composition of the existing source rates with the new post-height placement
rate; no such composite theorem is assumed here. -/
structure BankPaperCanonicalSectionNinePostHeightDependentInputsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) where
  Cinitial : Real
  Cfixed : Real
  Cinitial_nonneg : 0 ≤ Cinitial
  selectorDeficit :
    ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
        J.postHeightBridge.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector p) ≤
        Cinitial * J.postHeightBridge.q /
          ((p : Real) * J.postHeightBridge.L)
  roundedFrozenLedger :
    ∀ m : J.postHeightBridge.sampleData.Sample,
      BridgeData.frozenAmbientWeight
          (bankPaperCanonicalActualFrozenValue
            (candidates :=
              R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1)))
          (bankPaperCanonicalActualFrozenWeight
            J.postHeightBridge.sampleData
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            J.roundedSourceSelector J.roundedActiveSeed)
          (J.postHeightBridge.sampleData.value m) ≤
        Cfixed / J.postHeightBridge.L
  primeDeviation :
    J.postHeightBridge.primeDeviationL1 ≤
      7 * J.postHeightBridge.w
  radius : NNReal
  localP87 :
    ∀ (Delta : BankPaperCanonicalExponentBand M → Real),
      J.postHeightBridge.HasTargetEnvelopes (7 * Cinitial) Delta →
      ∀ (markedTarget : Nat → Real) (N : Real),
        0 ≤ N →
        J.postHeightBridge.q ≤ (1 : Real) * N →
        (∀ p ∈ primeBand J.postHeightBridge.sampleData.n
            J.postHeightBridge.sampleData.W,
          abs (markedTarget p -
            J.postHeightBridge.paperMoment
              (J.postHeightBridge.markedValuation p) 0) ≤
              Cinitial * N /
                ((p : Real) * J.postHeightBridge.L)) →
        (∀ j, Delta j =
          J.postHeightBridge.markedBandResidual markedTarget 0 j) →
        ∀ {Fixed : Type} [Fintype Fixed],
          ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
            (quota : Int),
            (quota : Real) = (∑ f, fixedWeight f) +
              J.postHeightBridge.q →
            J.postHeightBridge.sampleData.HeadPatternsSeparated →
            (∀ x,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                Icc (0 : Real) 1) →
            (∀ m : J.postHeightBridge.sampleData.Sample,
              BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (J.postHeightBridge.sampleData.value m) ≤
                Cfixed / J.postHeightBridge.L) →
            (∀ m : J.postHeightBridge.sampleData.Sample,
              J.postHeightBridge.baseline.baseWeight m ≤
                (S.Cmass / S.density) / J.postHeightBridge.L) →
            J.postHeightBridge.HasPaperProposition87Conclusion
              Delta radius markedTarget N Cpost
                fixedValue fixedWeight quota
  cellIndex : BankPaperCanonicalTangentPrime
    J.postHeightBridge.sampleData.n
      J.postHeightBridge.sampleData.W → Nat
  fixedRoom :
    J.betaProt + S.Cmass / S.density ≤ Cfixed
  W_large : 1 < J.postHeightBridge.sampleData.W
  sigma_nonneg : 0 ≤ sigma
  sigma_le_betaProt : sigma ≤ J.betaProt
  largeL :
    Cfixed +
        Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                2 J.postHeightBridge.sampleData.W +
            J.postHeightBridge.nuisanceStatisticCoefficient 2) *
              (3 * (radius : Real)))) *
          (S.Cmass / S.density) + sigma ≤
      J.postHeightBridge.L
  nonsmooth :
    ∀ label,
      RoughCanonicalActiveNonexceptionalLabel
          J.postHeightBridge.sampleData.n deltaStar label →
        sigma / J.postHeightBridge.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar J.postHeightBridge.sampleData.W (K0 + 1) label
                J.alpha J.beta J.postHeightBridge.L| ≤
          J.beta / J.postHeightBridge.L ∧
        J.beta / J.postHeightBridge.L +
            |R.roughCanonicalGuardedPostchargeCorrectionDensity certificate
              deltaStar J.postHeightBridge.sampleData.W (K0 + 1) label
                J.alpha J.beta J.postHeightBridge.L| ≤
          1 - sigma / J.postHeightBridge.L

namespace BankPaperCanonicalSectionNinePostHeightDependentInputsAt

variable
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar sigma Cpost : Real}
    {hdelta : 0 < delta}
    {J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta}
    {S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J}

/-- Nonnegativity of the pointwise active capacity. -/
theorem activeCapacity_nonneg
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    0 ≤ S.Cmass / S.density :=
  (fun _ =>
    div_nonneg S.Cmass_nonneg S.density_pos.le) A

/-- The final large-`L` inequality contains the placement-room inequality
needed by the source-to-post-height one-shot theorem. -/
theorem placementRoom
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    J.betaProt + S.Cmass / S.density ≤ J.postHeightBridge.L := by
  have hexp :
      0 ≤ Real.exp (2 *
        ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
              2 J.postHeightBridge.sampleData.W +
          J.postHeightBridge.nuisanceStatisticCoefficient 2) *
            (3 * (A.radius : Real)))) :=
    (Real.exp_pos _).le
  have hproduct :
      0 ≤ Real.exp (2 *
          ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                2 J.postHeightBridge.sampleData.W +
            J.postHeightBridge.nuisanceStatisticCoefficient 2) *
              (3 * (A.radius : Real)))) *
        (S.Cmass / S.density) :=
    mul_nonneg hexp A.activeCapacity_nonneg
  calc
    J.betaProt + S.Cmass / S.density ≤ A.Cfixed := A.fixedRoom
    _ ≤ A.Cfixed +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  2 J.postHeightBridge.sampleData.W +
              J.postHeightBridge.nuisanceStatisticCoefficient 2) *
                (3 * (A.radius : Real)))) *
            (S.Cmass / S.density) + sigma := by
        linarith [hproduct, A.sigma_nonneg]
    _ ≤ J.postHeightBridge.L := A.largeL

/-- Frozen-log invariance identifies the rounded `Lambda0` with the
post-height placed frozen ledger. -/
theorem Lambda0_eq_placedFrozenLogMass
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    J.Lambda0 =
      bankPaperCanonicalActualFrozenLogMass
        J.postHeightBridge.sampleData
        (R.paperFixedExceptionalFactors deltaStar)
        (baseBankFactors R.exactificationState)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector J.postHeightActiveSeed := by
  have _hA : A = A := rfl
  calc
    J.Lambda0 =
        bankPaperCanonicalActualFrozenLogMass
          J.postHeightBridge.sampleData
          (R.paperFixedExceptionalFactors deltaStar)
          (baseBankFactors R.exactificationState)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector J.roundedActiveSeed :=
      J.roundedLambda0_eq_postHeightBridge
    _ =
        bankPaperCanonicalActualFrozenLogMass
          J.postHeightBridge.sampleData
          (R.paperFixedExceptionalFactors deltaStar)
          (baseBankFactors R.exactificationState)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed := by
      symm
      exact
        bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenLogMass_eq_roundedSource
          (K := K0 + 1) J.postHeightBridge R certificate
            (R.paperFixedExceptionalFactors deltaStar)
            (baseBankFactors R.exactificationState) J.Tsource I
            J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
            deltaStar J.betaProt J.alpha J.beta J.qTilde
            S.activeSmooth S.activeBroad

/-- The ordinary logarithmic target is now an output, not an input field. -/
theorem ordinaryLogCompatible
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := J.postHeightBridge.sampleData.W) R certificate
      (R.paperFixedExceptionalFactors deltaStar)
      (R.roughCanonicalGuardedCandidateSet certificate
        deltaStar (K0 + 1))
      J.placedPreSelector := by
  have Hconstruction := S.sourceToPostHeight A.placementRoom
  exact
    bankPaperCanonicalSectionNinePostHeight_initialSelector_ordinaryLogCompatible
      J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector I J.postHeightHlo J.postHeightHhi
        J.postHeightTargetInputs Hconstruction.2.1
        Hconstruction.2.2.2.2 J.Lambda0 (by rfl)
        A.Lambda0_eq_placedFrozenLogMass S.fixedPositive S.charge_dvd

/-- The placed frozen pointwise ledger follows from the rounded one by the
pointwise arbitrary-seed cancellation. -/
theorem placedFrozenLedger
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (m : J.postHeightBridge.sampleData.Sample) :
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed)
        (J.postHeightBridge.sampleData.value m) ≤
      A.Cfixed / J.postHeightBridge.L := by
  calc
    BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed)
        (J.postHeightBridge.sampleData.value m) =
      BridgeData.frozenAmbientWeight
        (bankPaperCanonicalActualFrozenValue
          (candidates :=
            R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1)))
        (bankPaperCanonicalActualFrozenWeight
          J.postHeightBridge.sampleData
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector J.roundedActiveSeed)
        (J.postHeightBridge.sampleData.value m) := by
      classical
      unfold BridgeData.frozenAmbientWeight
      unfold
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightActiveSeed
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedActiveSeed
      apply Finset.sum_congr rfl
      intro a _ha
      rw [
        bankPaperCanonicalSectionNinePostHeightPlaced_actualFrozenWeight_eq_roundedSource
          (K := K0 + 1) J.postHeightBridge R certificate J.Tsource I
            J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
            deltaStar J.betaProt J.alpha J.beta J.qTilde
            S.activeSmooth S.activeBroad a]
    _ ≤ A.Cfixed / J.postHeightBridge.L :=
      A.roundedFrozenLedger m

/-- The fresh active baseline has the same pointwise capacity as its scaled
seed. -/
theorem activeLedger
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (m : J.postHeightBridge.sampleData.Sample) :
    J.postHeightBridge.baseline.baseWeight m ≤
      (S.Cmass / S.density) / J.postHeightBridge.L := by
  have _hA : A = A := rfl
  rw [J.postHeightBridge_baseWeight]
  exact S.activeSeedUpper m

/-- The exact ordinary-log identity and the placed deficit rate produce the
marked-band target envelopes required by Proposition 8.7. -/
theorem targetEnvelopes
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    J.postHeightBridge.HasTargetEnvelopes (7 * A.Cinitial)
      (fun j => J.postHeightBridge.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.placedPreSelector J.postHeightActiveSeed) 0 j) := by
  have Hconstruction := S.sourceToPostHeight A.placementRoom
  exact
    bankPaperCanonicalActualInitialHasTargetEnvelopes_of_selectorDeficit
      J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector J.postHeightActiveSeed
        Hconstruction.2.1 J.postHeightBridge_baseWeight
        A.Cinitial A.Cinitial_nonneg A.selectorDeficit
        A.ordinaryLogCompatible A.primeDeviation

/-- The protected reserve is built into the smooth additive refinement. -/
theorem protectedReserve
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (x : Nat)
    (hx : x ∈ R.roughCanonicalGuardedBroadCorrectionPool certificate
      deltaStar J.postHeightBridge.sampleData.W (K0 + 1) 1) :
    sigma / J.postHeightBridge.L +
        bankPaperCanonicalActiveSeedAmbientWeight
          J.postHeightBridge.sampleData J.postHeightActiveSeed x ≤
      J.placedPreSelector x := by
  have hrefine :=
    bankPaperCanonicalGuardedSmoothAdditiveRefinement_protectedReserve
      (K := K0 + 1) J.postHeightBridge R certificate
        J.roundedSourceSelector J.postHeightActiveSeed
        A.sigma_le_betaProt hx
  rw [←
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_eq_refinement_of_mem_pool
      (K := K0 + 1) J.postHeightBridge R certificate
        J.roundedSourceSelector J.postHeightActiveSeed hx] at hrefine
  simpa only [
    BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector,
    bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
    bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
    bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
    hrefine

/-- The interval cap `I.upper ≤ 2` supplies the producer's physical upper
bound with the fixed value `C = 2`. -/
theorem physicalUpper
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (sign : PhysicalSign) :
    J.postHeightBridge.sampleData.hi sign ≤
      physicalBound 2 J.postHeightBridge.sampleData.n := by
  have _hA : A = A := rfl
  rw [J.postHeightHhi sign]
  unfold physicalBound
  exact Nat.floor_mono
    (mul_le_mul_of_nonneg_right (S.upperTwo sign) (by positivity))

end BankPaperCanonicalSectionNinePostHeightDependentInputsAt

/-! ## Exact placement-rate transport -/

/-- The placed selector deficit is the rounded-source deficit minus the
literal post-height replacement moment.  Expanding that moment here exposes
the exact term controlled by
`exists_uniform_sectionNinePostHeightPlacementValuationMoment_paperRate`.

The remaining uniform analytic composition is therefore only a bound on
this displayed sum; no selector-identification contract is missing. -/
theorem
    bankPaperCanonicalSectionNinePostHeightPlacedSelectorDeficit_eq
    {delta eta : Real} {M : RegularRelativeMesh.Mesh delta eta}
    {P : Finset Nat}
    {Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)}
    {c : Real} {depth K0 : Nat}
    {R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n))}
    {certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth)}
    {I : PhysicalIntervals} {deltaStar : Real} {hdelta : 0 < delta}
    {J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta}
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (p : Nat) :
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector p =
      bankPaperCanonicalSelectorValuationDeficit R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector p -
        (bankPaperCanonicalScaledActiveValuationMoment
              J.postHeightTarget J.qn p -
          (bankPaperCanonicalScaledActiveValuationMoment
                J.Tsource J.qTilde p +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) J.postHeightBridge R certificate deltaStar
                J.betaProt J.alpha J.qTilde p)) := by
  calc
    bankPaperCanonicalSelectorValuationDeficit R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        J.placedPreSelector p =
      bankPaperCanonicalSelectorValuationDeficit R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector p -
        bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) J.postHeightBridge R certificate deltaStar
            J.betaProt J.roundedSourceSelector J.postHeightActiveSeed p := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector,
        bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
        bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
        bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
        (bankPaperCanonicalSelectorValuationDeficit_structuredAdditivePlacement_eq_sub_moment
          (K := K0 + 1) J.postHeightBridge R certificate
            (R.paperFixedExceptionalFactors deltaStar)
            J.roundedSourceSelector J.postHeightActiveSeed
            S.activeSmooth p)
    _ =
      bankPaperCanonicalSelectorValuationDeficit R certificate
          (R.paperFixedExceptionalFactors deltaStar)
          (R.roughCanonicalGuardedCandidateSet certificate
            deltaStar (K0 + 1))
          J.roundedSourceSelector p -
        (bankPaperCanonicalScaledActiveValuationMoment
              J.postHeightTarget J.qn p -
          (bankPaperCanonicalScaledActiveValuationMoment
                J.Tsource J.qTilde p +
            bankPaperCanonicalTopFrozenNearestIntegerValuationMoment
              (K := K0 + 1) J.postHeightBridge R certificate deltaStar
                J.betaProt J.alpha J.qTilde p)) := by
      unfold
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.roundedSourceSelector
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightActiveSeed
      rw [
        bankPaperCanonicalSectionNinePostHeightPlacementValuationMoment_eq
          (K := K0 + 1) J.postHeightBridge R certificate J.Tsource I
            J.postHeightHlo J.postHeightHhi J.postHeightTargetInputs
            deltaStar J.betaProt J.alpha J.beta J.qTilde
            S.activeSmooth S.activeBroad p]
      rfl

/-! ## Finite package producer and synchronized adapter -/

/-- Produce the top-frozen rounded Post-hfit guarded-slack package on the
fresh post-height bridge. -/
theorem
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_postHeightInputs
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S) :
    ∃ quota : Int, ∃ path : Real → J.postHeightBridge.ParamSpace,
      ∃ endpoint : Nat → Real,
        BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
          (K := K0 + 1) J.postHeightBridge R certificate
          (R.paperFixedExceptionalFactors deltaStar) J.Tsource
          deltaStar J.betaProt J.alpha J.beta J.qTilde sigma
          J.postHeightActiveSeed J.postHeightActiveSeed
          A.radius Cpost A.cellIndex quota path endpoint := by
  have Hconstruction := S.sourceToPostHeight A.placementRoom
  have hfeasible :
      ∀ a ∈ R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1),
        0 ≤
            bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) J.postHeightBridge R certificate
                J.Tsource deltaStar J.betaProt J.alpha J.beta
                J.qTilde J.postHeightActiveSeed a ∧
          bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector
              (K := K0 + 1) J.postHeightBridge R certificate
                J.Tsource deltaStar J.betaProt J.alpha J.beta
                J.qTilde J.postHeightActiveSeed a ≤ 1 := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.placedPreSelector,
      bankPaperCanonicalSectionNinePostHeightPlacedPreSelector,
      bankPaperCanonicalTopFrozenRoundedPostHfitStructuredPreSelector,
      bankPaperCanonicalPostHfitStructuredPreSelectorOfSource] using
      Hconstruction.2.2.1
  exact
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_sourceState
      (K := K0 + 1) (T := J.postHeightTarget)
      J.postHeightBridge R certificate
      (R.paperFixedExceptionalFactors deltaStar) J.Tsource
      deltaStar J.betaProt J.alpha J.beta J.qTilde sigma
      J.postHeightActiveSeed J.postHeightActiveSeed S.sourceState
      hfeasible Hconstruction.1 Hconstruction.2.1
      J.postHeightBridge_baseWeight S.headSeparated
      (7 * A.Cinitial) A.Cinitial A.Cfixed
      (S.Cmass / S.density) A.targetEnvelopes A.selectorDeficit
      A.placedFrozenLedger A.activeLedger A.radius Cpost A.localP87
      A.cellIndex (S.Cmass / S.density) A.activeCapacity_nonneg
      S.activeSeedUpper A.fixedRoom 2 (by norm_num) A.W_large
      A.physicalUpper A.activeCapacity_nonneg A.protectedReserve
      A.largeL A.nonsmooth

/-- Package one fixed post-height construction as the public synchronized
top-frozen input.  Every witness is the same witness used to define
`logY`, `Lambda0`, `Tpost`, and `Bpost`. -/
theorem
    bankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt_of_postHeightInputs
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S)
    (hcellIndex :
      A.cellIndex =
        bankPaperCanonicalRatioCellIndex M hdelta
          J.postHeightBridge.n_gt_one J.hW J.scaleSeparation rho) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt
      M J.postHeightBridge c depth K0 deltaStar rho sigma Cpost hdelta := by
  obtain ⟨quota, path, endpoint, Hpost⟩ :=
    exists_bankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage_of_postHeightInputs
      M Bsource R certificate I deltaStar sigma Cpost hdelta J S A
  refine
    ⟨R, certificate, S.combined_dvd, S.base_dvd, S.charge_dvd,
      S.target_tail, J.hW, J.scaleSeparation, J.postHeightBridge_partition,
      J.Tsource, J.betaProt, J.alpha, J.beta, J.qTilde,
      J.postHeightActiveSeed, J.postHeightActiveSeed, A.radius,
      quota, path, endpoint, ?_⟩
  rw [hcellIndex] at Hpost
  exact Hpost

end BankPaperRealization

end

end Erdos390.WholePaper
