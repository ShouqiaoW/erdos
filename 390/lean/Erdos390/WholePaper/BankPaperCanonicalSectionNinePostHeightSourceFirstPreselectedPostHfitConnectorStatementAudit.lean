import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreselectedPostHfitConnector

/-!
# Statement audit for the preselected Post-Hfit connector

This audit expands every callback consumed by the fixed-mesh compositor.
The coherent source obligation, the mesh-uniform placed-selector callback,
and the specialized one-mesh Proposition 8.7 callback are displayed
literally.  The final assignment records the complete production signature:
`Cinitial`, `radius`, and `CP87` are explicit inputs, and the theorem returns
the synchronized Post-Hfit input directly, with no existential choice of
any of those constants.
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

/-! ## Complete coherent source callback expansion -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)) :
    BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
        P Patterns I Cprom Cbank G depth W K0 E Ntail F
          deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
          physicalEtaFloor postMarginFloor Cmass density
          logY Lambda0 mFrozen qTilde M hdelta B ↔
      (∀ᶠ n : Nat in atTop,
        ∃ Bsource : BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
          ∃ hnTail : Ntail ≤ Bsource.sampleData.n,
            let R := F.realization Bsource.sampleData.n hnTail
            let certificate := F.certificate Bsource.sampleData.n hnTail
            ∃ J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                (K0 := K0) M Bsource R certificate I deltaStar hdelta,
              ∃ S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
                  M Bsource R certificate I deltaStar hdelta J,
                ∃ _Hgap :
                    BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
                      M Bsource R certificate I E deltaStar mu
                        sourceMarginFloor headMarginFloor physicalEtaFloor
                        postMarginFloor logY Lambda0 mFrozen qTilde
                        hdelta J S,
                  ∃ hsep :
                      physicalBound (I.upper .minus)
                          J.postHeightBridge.sampleData.n <
                        physicalBound (I.lower .plus)
                          J.postHeightBridge.sampleData.n,
                    ∃ hremaining :
                        ∀ cell : Cell (PaperHeadSimplex.Tag P),
                          (rawCell Patterns I
                              J.postHeightBridge.sampleData.n cell \
                            (G J.postHeightBridge.sampleData.n).guards).Nonempty,
                      B n = J.postHeightBridge ∧
                        Bsource.sampleData.n = n ∧
                        Bsource.sampleData.W = W ∧
                        J.betaProt = betaProt ∧
                        J.betaAct = betaAct ∧
                        J.postHeightBridge.sampleData =
                          canonicalSampleData
                            (W := J.postHeightBridge.sampleData.W)
                            Patterns I
                              (G J.postHeightBridge.sampleData.n)
                              hsep hremaining ∧
                        J.qTilde =
                          bankPaperCanonicalGuardedSmoothBaseMass
                            R certificate deltaStar
                              J.postHeightBridge.sampleData.W
                              (K0 + 1) J.betaAct ∧
                        S.Cmass = Cmass ∧
                        S.density = density) := by
  rfl

/-! ## Complete mesh-uniform placed-selector callback expansion -/

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
                (rawCell Patterns I J.postHeightBridge.sampleData.n cell \
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
                mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n →
          J.postHeightBridge.q =
              bankPaperCanonicalSmoothFinalActiveMassFamily
                mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n →
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

/-! ## Complete specialized one-mesh P87 callback expansion -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct postMarginFloor Cmass density : Real)
    (qMass : Nat → Real)
    (Cinitial : Real) (radius : NNReal) (CP87 : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
        (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar
          betaProt betaAct postMarginFloor Cmass density
          qMass Cinitial radius CP87 hdelta ↔
      (∀ᶠ n : Nat in atTop,
        ∀ (Bsource : BridgeData (PaperHeadSimplex.Tag P)
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
            (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
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
                (rawCell Patterns I J.postHeightBridge.sampleData.n cell \
                  (G J.postHeightBridge.sampleData.n).guards).Nonempty),
          J.postHeightBridge.sampleData =
              canonicalSampleData
                (W := J.postHeightBridge.sampleData.W)
                Patterns I (G J.postHeightBridge.sampleData.n)
                  hsep hremaining →
          postMarginFloor ≤ J.postHeightTarget.cellMassMargin →
          S.Cmass = Cmass →
          S.density = density →
          J.postHeightBridge.q = qMass n →
          ∀ (Delta : BankPaperCanonicalExponentBand M → Real),
            J.postHeightBridge.HasTargetEnvelopes
                (7 * Cinitial) Delta →
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
              (∀ j,
                Delta j =
                  J.postHeightBridge.markedBandResidual
                    markedTarget 0 j) →
              ∀ {Fixed : Type} [Fintype Fixed],
                ∀ (fixedValue : Fixed → Nat)
                  (fixedWeight : Fixed → Real) (quota : Int),
                  (quota : Real) =
                      (∑ f, fixedWeight f) + J.postHeightBridge.q →
                    J.postHeightBridge.sampleData.HeadPatternsSeparated →
                    (∀ x,
                      BridgeData.frozenAmbientWeight
                          fixedValue fixedWeight x ∈
                        Icc (0 : Real) 1) →
                    (∀ m : J.postHeightBridge.sampleData.Sample,
                      BridgeData.frozenAmbientWeight
                          fixedValue fixedWeight
                          (J.postHeightBridge.sampleData.value m) ≤
                        (J.betaProt + S.Cmass / S.density) /
                          J.postHeightBridge.L) →
                    (∀ m : J.postHeightBridge.sampleData.Sample,
                      J.postHeightBridge.baseline.baseWeight m ≤
                        (S.Cmass / S.density) /
                          J.postHeightBridge.L) →
                    J.postHeightBridge.HasPaperProposition87Conclusion
                      Delta radius markedTarget N CP87
                        fixedValue fixedWeight quota) := by
  rfl

/-! ## Complete preselected compositor theorem assignment -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (rho sigma : Real)
    (Cinitial : Real) (radius : NNReal) (CP87 : Real)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (Hsource :
      BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
        P Patterns I Cprom Cbank G depth W K0 E Ntail F
          deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
          physicalEtaFloor postMarginFloor Cmass density
          logY Lambda0 mFrozen qTilde M hdelta B)
    (Hselector :
      BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
        Patterns I Cprom Cbank G (c := c) depth W K0
          deltaStar betaProt betaAct mu
          logY Lambda0 mFrozen qTilde Cinitial)
    (HP87 :
      BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
        (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar
          betaProt betaAct postMarginFloor Cmass density
          (bankPaperCanonicalSmoothFinalActiveMassFamily
            mu logY Lambda0 mFrozen qTilde)
          Cinitial radius CP87 hdelta)
    (hCinitial : 0 ≤ Cinitial)
    (hradius : 0 < (radius : Real))
    (hCP87 : 0 ≤ CP87)
    (hc : 0 < c)
    (hTwoW : 2 ≤ W)
    (hdeltaStar : 0 < deltaStar)
    (hbetaProt : 0 ≤ betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)))
    (hCmass : 0 ≤ Cmass)
    (hdensity : 0 < density)
    (hsigma : 0 < sigma)
    (hsigmaProt : sigma ≤ betaProt)
    (hMoment : canonicalActualMomentCutoff ≤ W) :
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma CP87 hdelta :=
  bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput
    (c := c) M Patterns I Cprom Cbank G depth W K0 E Ntail F
      deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density
      logY Lambda0 mFrozen qTilde rho sigma
      Cinitial radius CP87 hdelta B Hsource Hselector HP87
      hCinitial hradius hCP87 hc hTwoW hdeltaStar
      hbetaProt hbetaAct hbetaUpper hKlarge hCmass hdensity
      hsigma hsigmaProt hMoment

/-! ## Public declaration census -/

#check
  bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput

end BankPaperRealization

end

end Erdos390.WholePaper
