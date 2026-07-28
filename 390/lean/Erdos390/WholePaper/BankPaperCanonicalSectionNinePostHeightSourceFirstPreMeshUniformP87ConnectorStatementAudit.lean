import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Connector

/-!
# Statement audit for the source-first pre-mesh uniform Proposition 8.7 connector

The first example unfolds the production statement, the specialized
eventual callback, and the exact one-index Proposition 8.7 field literally.
The second assigns the production theorem directly to the same complete
expansion.

In particular, the displayed dependency order is
`Cinitial → ∃ radius, ∃ CP87, ∀ M`: both Proposition 8.7 witnesses are
chosen before the final permitted sufficiently fine mesh.  No selector or
Post-Hfit conclusion contract is introduced.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Complete literal definition expansion -/

example
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank) :
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
        I Cprom Cbank G ↔
      ((∀ sign, 1 ≤ I.lower sign) →
        (∀ sign, I.upper sign ≤ (2 : Real)) →
        ∃ meshTol : Real, 0 < meshTol ∧
        ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
          ∀ (qMass : Nat → Real),
            (∀ᶠ n : Nat in atTop, 1 ≤ qMass n) →
          ∀ {P : Finset Nat}
            (Patterns : PaperHeadSimplex.Tag P → Pattern),
            (∀ h : PaperHeadSimplex.Tag P, ∀ p : Nat,
              p ∈ (Patterns h).primes ↔ p.Prime ∧ p ≤ W) →
          ∀ {c : Real} (depth K0 : Nat)
            (deltaStar betaProt betaAct postMarginFloor
              Cmass density : Real),
            0 ≤ betaProt →
            0 ≤ Cmass →
            0 < density →
            0 < postMarginFloor →
          ∀ Cinitial : Real, 0 ≤ Cinitial →
            ∃ radius : NNReal, 0 < (radius : Real) ∧
            ∃ CP87 : Real, 0 ≤ CP87 ∧
              ∀ {delta eta : Real}
                (M : RegularRelativeMesh.Mesh delta eta)
                (hdelta : 0 < delta)
                (_hPermitted : IsPermitted (cMesh := (1 : Real)) M),
                delta + eta ≤ meshTol →
                ∀ᶠ n : Nat in atTop,
                  ∀ (Bsource :
                      BridgeData (PaperHeadSimplex.Tag P)
                        (BankPaperCanonicalExponentBand M)),
                    Bsource.sampleData.n = n →
                    Bsource.sampleData.W = W →
                    ∀
                      (R : BankPaperRealization Bsource.sampleData.n
                        (upperEndpoint Bsource.sampleData.n
                          (upperTailLength c Bsource.sampleData.n)))
                      (certificate :
                        GuardedCentralAnchorCertificate c depth
                          Bsource.sampleData.n R.anchorGuardLeftCore
                          R.anchorGuardRightCore
                          (R.centralChangedMarkers depth))
                      (J :
                        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                          (K0 := K0) M Bsource R certificate I
                            deltaStar hdelta)
                      (S :
                        BankPaperCanonicalSectionNinePostHeightSourceInputsAt
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
                              Patterns I
                                (G J.postHeightBridge.sampleData.n)
                                hsep hremaining →
                        postMarginFloor ≤
                          J.postHeightTarget.cellMassMargin →
                        S.Cmass = Cmass →
                        S.density = density →
                        J.postHeightBridge.q = qMass n →
                        ∀ (Delta :
                            BankPaperCanonicalExponentBand M → Real),
                          J.postHeightBridge.HasTargetEnvelopes
                              (7 * Cinitial) Delta →
                          ∀ (markedTarget : Nat → Real) (N : Real),
                            0 ≤ N →
                            J.postHeightBridge.q ≤ (1 : Real) * N →
                            (∀ p ∈
                                primeBand
                                  J.postHeightBridge.sampleData.n
                                  J.postHeightBridge.sampleData.W,
                              abs (markedTarget p -
                                J.postHeightBridge.paperMoment
                                  (J.postHeightBridge.markedValuation p)
                                  0) ≤
                                Cinitial * N /
                                  ((p : Real) *
                                    J.postHeightBridge.L)) →
                            (∀ j,
                              Delta j =
                                J.postHeightBridge.markedBandResidual
                                  markedTarget 0 j) →
                            ∀ {Fixed : Type} [Fintype Fixed],
                              ∀ (fixedValue : Fixed → Nat)
                                (fixedWeight : Fixed → Real)
                                (quota : Int),
                                (quota : Real) =
                                    (∑ f, fixedWeight f) +
                                      J.postHeightBridge.q →
                                J.postHeightBridge.sampleData.HeadPatternsSeparated →
                                (∀ x,
                                  BridgeData.frozenAmbientWeight
                                      fixedValue fixedWeight x ∈
                                    Icc (0 : Real) 1) →
                                (∀ m :
                                    J.postHeightBridge.sampleData.Sample,
                                  BridgeData.frozenAmbientWeight
                                      fixedValue fixedWeight
                                      (J.postHeightBridge.sampleData.value
                                        m) ≤
                                    (J.betaProt +
                                        S.Cmass / S.density) /
                                      J.postHeightBridge.L) →
                                (∀ m :
                                    J.postHeightBridge.sampleData.Sample,
                                  J.postHeightBridge.baseline.baseWeight m ≤
                                    (S.Cmass / S.density) /
                                      J.postHeightBridge.L) →
                                J.postHeightBridge.HasPaperProposition87Conclusion
                                  Delta radius markedTarget N CP87
                                    fixedValue fixedWeight quota) := by
  rfl

/-! ## Complete expanded theorem assignment -/

example
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank) :
    (∀ sign, 1 ≤ I.lower sign) →
    (∀ sign, I.upper sign ≤ (2 : Real)) →
    ∃ meshTol : Real, 0 < meshTol ∧
    ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
      ∀ (qMass : Nat → Real),
        (∀ᶠ n : Nat in atTop, 1 ≤ qMass n) →
      ∀ {P : Finset Nat}
        (Patterns : PaperHeadSimplex.Tag P → Pattern),
        (∀ h : PaperHeadSimplex.Tag P, ∀ p : Nat,
          p ∈ (Patterns h).primes ↔ p.Prime ∧ p ≤ W) →
      ∀ {c : Real} (depth K0 : Nat)
        (deltaStar betaProt betaAct postMarginFloor
          Cmass density : Real),
        0 ≤ betaProt →
        0 ≤ Cmass →
        0 < density →
        0 < postMarginFloor →
      ∀ Cinitial : Real, 0 ≤ Cinitial →
        ∃ radius : NNReal, 0 < (radius : Real) ∧
        ∃ CP87 : Real, 0 ≤ CP87 ∧
          ∀ {delta eta : Real}
            (M : RegularRelativeMesh.Mesh delta eta)
            (hdelta : 0 < delta)
            (_hPermitted : IsPermitted (cMesh := (1 : Real)) M),
            delta + eta ≤ meshTol →
            ∀ᶠ n : Nat in atTop,
              ∀ (Bsource :
                  BridgeData (PaperHeadSimplex.Tag P)
                    (BankPaperCanonicalExponentBand M)),
                Bsource.sampleData.n = n →
                Bsource.sampleData.W = W →
                ∀
                  (R : BankPaperRealization Bsource.sampleData.n
                    (upperEndpoint Bsource.sampleData.n
                      (upperTailLength c Bsource.sampleData.n)))
                  (certificate :
                    GuardedCentralAnchorCertificate c depth
                      Bsource.sampleData.n R.anchorGuardLeftCore
                      R.anchorGuardRightCore
                      (R.centralChangedMarkers depth))
                  (J :
                    BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                      (K0 := K0) M Bsource R certificate I deltaStar
                        hdelta)
                  (S :
                    BankPaperCanonicalSectionNinePostHeightSourceInputsAt
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
                          Patterns I
                            (G J.postHeightBridge.sampleData.n)
                            hsep hremaining →
                    postMarginFloor ≤
                      J.postHeightTarget.cellMassMargin →
                    S.Cmass = Cmass →
                    S.density = density →
                    J.postHeightBridge.q = qMass n →
                    ∀ (Delta :
                        BankPaperCanonicalExponentBand M → Real),
                      J.postHeightBridge.HasTargetEnvelopes
                          (7 * Cinitial) Delta →
                      ∀ (markedTarget : Nat → Real) (N : Real),
                        0 ≤ N →
                        J.postHeightBridge.q ≤ (1 : Real) * N →
                        (∀ p ∈
                            primeBand J.postHeightBridge.sampleData.n
                              J.postHeightBridge.sampleData.W,
                          abs (markedTarget p -
                            J.postHeightBridge.paperMoment
                              (J.postHeightBridge.markedValuation p)
                              0) ≤
                            Cinitial * N /
                              ((p : Real) * J.postHeightBridge.L)) →
                        (∀ j,
                          Delta j =
                            J.postHeightBridge.markedBandResidual
                              markedTarget 0 j) →
                        ∀ {Fixed : Type} [Fintype Fixed],
                          ∀ (fixedValue : Fixed → Nat)
                            (fixedWeight : Fixed → Real)
                            (quota : Int),
                            (quota : Real) =
                                (∑ f, fixedWeight f) +
                                  J.postHeightBridge.q →
                            J.postHeightBridge.sampleData.HeadPatternsSeparated →
                            (∀ x,
                              BridgeData.frozenAmbientWeight
                                  fixedValue fixedWeight x ∈
                                Icc (0 : Real) 1) →
                            (∀ m :
                                J.postHeightBridge.sampleData.Sample,
                              BridgeData.frozenAmbientWeight
                                  fixedValue fixedWeight
                                  (J.postHeightBridge.sampleData.value m) ≤
                                (J.betaProt + S.Cmass / S.density) /
                                  J.postHeightBridge.L) →
                            (∀ m :
                                J.postHeightBridge.sampleData.Sample,
                              J.postHeightBridge.baseline.baseWeight m ≤
                                (S.Cmass / S.density) /
                                  J.postHeightBridge.L) →
                            J.postHeightBridge.HasPaperProposition87Conclusion
                              Delta radius markedTarget N CP87
                                fixedValue fixedWeight quota := by
  exact
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87
      I Cprom Cbank G

/-! ## Complete public declaration census -/

#check
  BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87

end BankPaperRealization

end

end Erdos390.WholePaper
