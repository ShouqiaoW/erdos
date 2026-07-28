import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshSelectorProvider

/-!
# Expanded statement audit: source-first pre-mesh selector provider

The first example unfolds the complete mesh-uniform callback.  It displays
the eventual index before the universal final mesh, every dependent local
source object and synchronization premise, and the literal prime-band
valuation-deficit estimate.

The second example assigns the provider theorem directly to the same fully
expanded callback under one existentially chosen nonnegative `Cinitial`.
Thus neither the mesh order nor any local premise is hidden behind the
callback abbreviation in the public theorem audit.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Literal expansion of the eventual mesh-uniform callback -/

example
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct mu : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Cinitial : Real) :
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
        Patterns I Cprom Cbank G (c := c) depth W K0
          deltaStar betaProt betaAct mu
          logY Lambda0 mFrozen qTilde Cinitial ↔
      (∀ᶠ n : Nat in atTop,
        ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta)
          (Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M)),
          Bsource.sampleData.n = n →
          Bsource.sampleData.W = W →
          ∀
            (R : BankPaperRealization Bsource.sampleData.n
              (upperEndpoint Bsource.sampleData.n
                (upperTailLength c Bsource.sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              Bsource.sampleData.n R.anchorGuardLeftCore
              R.anchorGuardRightCore (R.centralChangedMarkers depth))
            (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
              (K0 := K0) M Bsource R certificate I deltaStar hdelta)
            (_S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
              M Bsource R certificate I deltaStar hdelta J),
          J.betaProt = betaProt →
          J.betaAct = betaAct →
          ∀
            (hsep :
              physicalBound (I.upper .minus)
                  J.postHeightBridge.sampleData.n <
                physicalBound (I.lower .plus)
                  J.postHeightBridge.sampleData.n)
            (hremaining :
              ∀ cell : Cell (PaperHeadSimplex.Tag P),
                (rawCell Patterns I
                    J.postHeightBridge.sampleData.n cell \
                  (G J.postHeightBridge.sampleData.n).guards).Nonempty),
          J.postHeightBridge.sampleData =
              canonicalSampleData
                (W := J.postHeightBridge.sampleData.W)
                Patterns I (G J.postHeightBridge.sampleData.n)
                  hsep hremaining →
          J.qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass R certificate
                deltaStar J.postHeightBridge.sampleData.W
                  (K0 + 1) J.betaAct →
          (0 ≤ J.alpha ∧ J.alpha ≤ 1) →
          (0 ≤ J.beta / J.postHeightBridge.L ∧
            J.beta / J.postHeightBridge.L ≤ 1) →
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar J.postHeightBridge.sampleData.W
              (K0 + 1) 1).Nonempty →
          (J.d : Real) =
              bankPaperCanonicalSmoothDRealFamily
                mu logY Lambda0 mFrozen qTilde
                  Bsource.sampleData.n →
          J.postHeightBridge.q =
              bankPaperCanonicalSmoothFinalActiveMassFamily
                mu logY Lambda0 mFrozen qTilde
                  Bsource.sampleData.n →
          ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
              J.postHeightBridge.sampleData.W,
            abs
                (bankPaperCanonicalSelectorValuationDeficit
                  R certificate
                  (R.paperFixedExceptionalFactors deltaStar)
                  (R.roughCanonicalGuardedCandidateSet certificate
                    deltaStar (K0 + 1))
                  J.placedPreSelector p) ≤
              Cinitial * J.postHeightBridge.q /
                ((p : Real) * J.postHeightBridge.L)) := by
  rfl

/-! ## Complete expanded provider theorem -/

example
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct mu : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde))
    (hTwoW : 2 ≤ W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W)
    (hc : 0 < c)
    (hdeltaStar : 0 < deltaStar)
    (hdeltaStarUpper : deltaStar < 1 / 18)
    (hbetaAct : 0 < betaAct)
    (hprefix : 2 * depth + 1 ≤ W)
    (hmu : 0 < mu) :
    ∃ Cinitial : Real, 0 ≤ Cinitial ∧
      ∀ᶠ n : Nat in atTop,
        ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta)
          (Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M)),
          Bsource.sampleData.n = n →
          Bsource.sampleData.W = W →
          ∀
            (R : BankPaperRealization Bsource.sampleData.n
              (upperEndpoint Bsource.sampleData.n
                (upperTailLength c Bsource.sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              Bsource.sampleData.n R.anchorGuardLeftCore
              R.anchorGuardRightCore (R.centralChangedMarkers depth))
            (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
              (K0 := K0) M Bsource R certificate I deltaStar hdelta)
            (_S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
              M Bsource R certificate I deltaStar hdelta J),
          J.betaProt = betaProt →
          J.betaAct = betaAct →
          ∀
            (hsep :
              physicalBound (I.upper .minus)
                  J.postHeightBridge.sampleData.n <
                physicalBound (I.lower .plus)
                  J.postHeightBridge.sampleData.n)
            (hremaining :
              ∀ cell : Cell (PaperHeadSimplex.Tag P),
                (rawCell Patterns I
                    J.postHeightBridge.sampleData.n cell \
                  (G J.postHeightBridge.sampleData.n).guards).Nonempty),
          J.postHeightBridge.sampleData =
              canonicalSampleData
                (W := J.postHeightBridge.sampleData.W)
                Patterns I (G J.postHeightBridge.sampleData.n)
                  hsep hremaining →
          J.qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass R certificate
                deltaStar J.postHeightBridge.sampleData.W
                  (K0 + 1) J.betaAct →
          (0 ≤ J.alpha ∧ J.alpha ≤ 1) →
          (0 ≤ J.beta / J.postHeightBridge.L ∧
            J.beta / J.postHeightBridge.L ≤ 1) →
          (R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar J.postHeightBridge.sampleData.W
              (K0 + 1) 1).Nonempty →
          (J.d : Real) =
              bankPaperCanonicalSmoothDRealFamily
                mu logY Lambda0 mFrozen qTilde
                  Bsource.sampleData.n →
          J.postHeightBridge.q =
              bankPaperCanonicalSmoothFinalActiveMassFamily
                mu logY Lambda0 mFrozen qTilde
                  Bsource.sampleData.n →
          ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
              J.postHeightBridge.sampleData.W,
            abs
                (bankPaperCanonicalSelectorValuationDeficit
                  R certificate
                  (R.paperFixedExceptionalFactors deltaStar)
                  (R.roughCanonicalGuardedCandidateSet certificate
                    deltaStar (K0 + 1))
                  J.placedPreSelector p) ≤
              Cinitial * J.postHeightBridge.q /
                ((p : Real) * J.postHeightBridge.L) := by
  exact
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider
      Patterns I Cprom Cbank G (c := c) depth W K0
        deltaStar betaProt betaAct mu
        logY Lambda0 mFrozen qTilde Hledger hTwoW hHeadLe hc
        hdeltaStar hdeltaStarUpper hbetaAct hprefix hmu

/-! ## Public declaration census -/

#check
  BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider

end BankPaperRealization

end

end Erdos390.WholePaper
