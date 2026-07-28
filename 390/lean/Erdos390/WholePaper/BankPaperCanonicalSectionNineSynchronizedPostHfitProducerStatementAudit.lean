import Erdos390.WholePaper.BankPaperCanonicalSectionNineSynchronizedPostHfitProducer

/-!
# Statement audit for the same-witness synchronized Post-Hfit producer

The audit checks both the legacy and source-state local analytic inputs,
the old-to-weak adapter, literally expands both eventual suppliers'
quantifier order, and records both finite and eventual same-witness producer
signatures.
-/

open Filter Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Exact local analytic input -/

example
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar sigma Cpost : Real) :
    BankPaperCanonicalSectionNinePostHfitLocalInputsAt
        (K0 := K0) B R certificate deltaStar sigma Cpost ↔
      ∃ betaProt betaAct : Real,
        ∃ oldSeed activeSeed : B.sampleData.Sample → Real,
          ∃ minusMass plusMass : Real,
            ∃ rowChange : Int,
              ∃ sourceCellIndex : BankPaperCanonicalTangentPrime
                  B.sampleData.n B.sampleData.W → Nat,
                ∃ sourcePointwiseUpper : BankPaperCanonicalTangentPrime
                    B.sampleData.n B.sampleData.W → Real,
                  ∃ sourcePrefixUpper : Band → Nat → Real,
                    ∃ T : BarycentricTarget B.sampleData,
                      ∃ Ctarget Cinitial Cfixed Cactive : Real,
                        ∃ radius : NNReal,
                          ∃ Cplacement C : Real,
                            0 ≤ betaProt ∧
                            BankPaperCanonicalRoundedSelectorTangentInput
                              R certificate
                              (R.paperFixedExceptionalFactors deltaStar)
                              (R.roughCanonicalGuardedCandidateSet certificate
                                deltaStar (K0 + 1))
                              B.partition.band sourceCellIndex
                              sourcePointwiseUpper sourcePrefixUpper
                              (bankPaperCanonicalPostHfitGlobalSourceSelector
                                B K0 R certificate deltaStar betaProt betaAct
                                  oldSeed) ∧
                            B.sampleData.HeadPatternsSeparated ∧
                            bankPaperCanonicalStructuredActiveValues
                                  B.sampleData ⊆
                                R.roughCanonicalGuardedRow certificate deltaStar
                                  (K0 + 1) 1 ∧
                            (∀ m : B.sampleData.Sample,
                              B.sampleData.cellOf m = (none, .minus) →
                                B.sampleData.value m ∈
                                  R.roughCanonicalGuardedBroadCorrectionPool
                                    certificate deltaStar B.sampleData.W
                                      (K0 + 1) 1) ∧
                            (∀ m : B.sampleData.Sample,
                              B.sampleData.cellOf m = (none, .plus) →
                                B.sampleData.value m ∈
                                  R.roughCanonicalGuardedBroadCorrectionPool
                                    certificate deltaStar B.sampleData.W
                                      (K0 + 1) 1) ∧
                            (∀ m : B.sampleData.Sample,
                              B.sampleData.cellOf m = (none, .minus) →
                                0 ≤
                                    bankPaperCanonicalTwoZeroHeadCellRebalance
                                      B.sampleData oldSeed minusMass plusMass m ∧
                                  betaProt / B.L +
                                      bankPaperCanonicalTwoZeroHeadCellRebalance
                                        B.sampleData oldSeed minusMass plusMass
                                          m ≤
                                    1) ∧
                            (∀ m : B.sampleData.Sample,
                              B.sampleData.cellOf m = (none, .plus) →
                                0 ≤
                                    bankPaperCanonicalTwoZeroHeadCellRebalance
                                      B.sampleData oldSeed minusMass plusMass m ∧
                                  betaProt / B.L +
                                      bankPaperCanonicalTwoZeroHeadCellRebalance
                                        B.sampleData oldSeed minusMass plusMass
                                          m ≤
                                    1) ∧
                            minusMass + plusMass = (rowChange : Real) ∧
                            BankPaperCanonicalActualActiveMeasureConstructor
                              B.sampleData T
                              (R.roughCanonicalGuardedCandidateSet certificate
                                deltaStar (K0 + 1))
                              (bankPaperCanonicalPostHfitStructuredPreSelector
                                B K0 R certificate deltaStar betaProt betaAct
                                  oldSeed minusMass plusMass)
                              activeSeed ∧
                            (∀ m, B.baseline.baseWeight m = activeSeed m) ∧
                            B.HasTargetEnvelopes Ctarget
                              (fun j => B.markedBandResidual
                                (bankPaperCanonicalActualActiveMarkedTarget
                                  B R certificate
                                  (R.paperFixedExceptionalFactors deltaStar)
                                  (R.roughCanonicalGuardedCandidateSet
                                    certificate deltaStar (K0 + 1))
                                  (bankPaperCanonicalPostHfitStructuredPreSelector
                                    B K0 R certificate deltaStar betaProt
                                      betaAct oldSeed minusMass plusMass)
                                  activeSeed) 0 j) ∧
                            (∀ p ∈ primeBand
                                B.sampleData.n B.sampleData.W,
                              abs (bankPaperCanonicalSelectorValuationDeficit
                                R certificate
                                  (R.paperFixedExceptionalFactors deltaStar)
                                  (R.roughCanonicalGuardedCandidateSet
                                    certificate deltaStar (K0 + 1))
                                  (bankPaperCanonicalPostHfitStructuredPreSelector
                                    B K0 R certificate deltaStar betaProt
                                      betaAct oldSeed minusMass plusMass) p) ≤
                                Cinitial * B.q / ((p : Real) * B.L)) ∧
                            (∀ m : B.sampleData.Sample,
                              BridgeData.frozenAmbientWeight
                                  (bankPaperCanonicalActualFrozenValue
                                    (candidates :=
                                      R.roughCanonicalGuardedCandidateSet
                                        certificate deltaStar (K0 + 1)))
                                  (bankPaperCanonicalActualFrozenWeight
                                    B.sampleData
                                    (R.roughCanonicalGuardedCandidateSet
                                      certificate deltaStar (K0 + 1))
                                    (bankPaperCanonicalPostHfitStructuredPreSelector
                                      B K0 R certificate deltaStar betaProt
                                        betaAct oldSeed minusMass plusMass)
                                    activeSeed)
                                  (B.sampleData.value m) ≤
                                Cfixed / B.L) ∧
                            (∀ m : B.sampleData.Sample,
                              B.baseline.baseWeight m ≤ Cactive / B.L) ∧
                            (∀ (Delta : Band → Real),
                              B.HasTargetEnvelopes Ctarget Delta →
                              ∀ (markedTarget : Nat → Real) (N : Real),
                                0 ≤ N →
                                B.q ≤ (1 : Real) * N →
                                (∀ p ∈ primeBand
                                    B.sampleData.n B.sampleData.W,
                                  abs (markedTarget p -
                                    B.paperMoment
                                      (B.markedValuation p) 0) ≤
                                    Cinitial * N / ((p : Real) * B.L)) →
                                (∀ j,
                                  Delta j =
                                    B.markedBandResidual markedTarget 0 j) →
                                ∀ {Fixed : Type} [Fintype Fixed],
                                  ∀ (fixedValue : Fixed → Nat)
                                    (fixedWeight : Fixed → Real) (quota : Int),
                                    (quota : Real) =
                                        (∑ f, fixedWeight f) + B.q →
                                    B.sampleData.HeadPatternsSeparated →
                                    (∀ x,
                                      BridgeData.frozenAmbientWeight
                                        fixedValue fixedWeight x ∈
                                          Icc (0 : Real) 1) →
                                    (∀ m : B.sampleData.Sample,
                                      BridgeData.frozenAmbientWeight
                                          fixedValue fixedWeight
                                            (B.sampleData.value m) ≤
                                        Cfixed / B.L) →
                                    (∀ m : B.sampleData.Sample,
                                      B.baseline.baseWeight m ≤
                                        Cactive / B.L) →
                                    B.HasPaperProposition87Conclusion
                                      Delta radius markedTarget N Cpost
                                        fixedValue fixedWeight quota) ∧
                            0 ≤ Cplacement ∧
                            (∀ m : B.sampleData.Sample,
                              bankPaperCanonicalTwoZeroHeadCellRebalance
                                  B.sampleData oldSeed minusMass plusMass m ≤
                                Cplacement / B.L) ∧
                            betaProt + Cplacement ≤ Cfixed ∧
                            1 ≤ C ∧
                            1 < B.sampleData.W ∧
                            (∀ sign,
                              B.sampleData.hi sign ≤
                                physicalBound C B.sampleData.n) ∧
                            0 ≤ Cactive ∧
                            (∀ x ∈
                              R.roughCanonicalGuardedBroadCorrectionPool
                                certificate deltaStar B.sampleData.W
                                  (K0 + 1) 1,
                              sigma / B.L +
                                  bankPaperCanonicalActiveSeedAmbientWeight
                                    B.sampleData activeSeed x ≤
                                bankPaperCanonicalPostHfitStructuredPreSelector
                                  B K0 R certificate deltaStar betaProt betaAct
                                    oldSeed minusMass plusMass x) ∧
                            Cfixed +
                                Real.exp (2 *
                                  ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                                        C B.sampleData.W +
                                    B.nuisanceStatisticCoefficient C) *
                                      (3 * (radius : Real)))) *
                                  Cactive + sigma ≤
                              B.L ∧
                            RoughCanonicalBalancedNonsmoothBounds
                              R certificate deltaStar B.sampleData.W K0
                                betaProt betaAct sigma := by
  rfl

/-! ## Supplier quantifier order -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNinePostHfitLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta ↔
      ∀ᶠ n : Nat in atTop,
        ∃ hW : (B n).sampleData.W ≠ 0,
          ∃ S : ScaleSeparation M
              (B n).sampleData.n (B n).sampleData.W,
            (B n).partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta (B n).n_gt_one hW S ∧
              ∀ (R : BankPaperRealization (B n).sampleData.n
                    (upperEndpoint (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n)))
                (certificate : GuardedCentralAnchorCertificate c depth
                  (B n).sampleData.n R.anchorGuardLeftCore
                  R.anchorGuardRightCore
                  (R.centralChangedMarkers depth)),
                centralAnchorDivisor (B n).sampleData.n
                      (centralAnchorCutoff depth (B n).sampleData.n)
                      certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                (baseBankFactors R.exactificationState).prod id ∣
                    certificate.prechargedTailTarget →
                R.selectorTailCharge
                      (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                certificate.prechargedTailTarget *
                      centralAnchorDivisor (B n).sampleData.n
                        (centralAnchorCutoff depth (B n).sampleData.n)
                        certificate.q =
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                BankPaperCanonicalSectionNinePostHfitLocalInputsAt
                  (K0 := K0) (B n) R certificate
                    deltaStar sigma Cpost := by
  rfl

/-! ## Source-state supplier quantifier order -/

/-- The weak supplier is still tail-only: the canonical partition witness is
chosen at each sufficiently large index before the exact capacity
realization and certificate, and the four capacity facts precede the local
SourceState input. -/
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar sigma Cpost : Real)
    (hdelta : 0 < delta) :
    BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta ↔
      ∀ᶠ n : Nat in atTop,
        ∃ hW : (B n).sampleData.W ≠ 0,
          ∃ S : ScaleSeparation M
              (B n).sampleData.n (B n).sampleData.W,
            (B n).partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta (B n).n_gt_one hW S ∧
              ∀ (R : BankPaperRealization (B n).sampleData.n
                    (upperEndpoint (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n)))
                (certificate : GuardedCentralAnchorCertificate c depth
                  (B n).sampleData.n R.anchorGuardLeftCore
                  R.anchorGuardRightCore
                  (R.centralChangedMarkers depth)),
                centralAnchorDivisor (B n).sampleData.n
                      (centralAnchorCutoff depth (B n).sampleData.n)
                      certificate.q * R.prechargeBaseStateProduct ∣
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                (baseBankFactors R.exactificationState).prod id ∣
                    certificate.prechargedTailTarget →
                R.selectorTailCharge
                      (R.paperFixedExceptionalFactors deltaStar) ∣
                    certificate.prechargedTailTarget →
                certificate.prechargedTailTarget *
                      centralAnchorDivisor (B n).sampleData.n
                        (centralAnchorCutoff depth (B n).sampleData.n)
                        certificate.q =
                    centralTailProduct (B n).sampleData.n
                      (upperTailLength c (B n).sampleData.n) →
                BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
                  (K0 := K0) (B n) R certificate
                    deltaStar sigma Cpost := by
  rfl

/-! ## One-index same-witness assembly -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hcombined :
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hbaseDvd :
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget)
    (hchargeDvd :
      R.selectorTailCharge
            (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (htargetTail :
      certificate.prechargedTailTarget *
            centralAnchorDivisor B.sampleData.n
              (centralAnchorCutoff depth B.sampleData.n)
              certificate.q =
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hW : B.sampleData.W ≠ 0)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition :
      B.partition =
        RegularMeshPrimeCutoffs.Mesh.canonicalPartition
          M hdelta B.n_gt_one hW S)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitLocalInputsAt
        (K0 := K0) B R certificate deltaStar sigma Cpost) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
      M B c depth K0 deltaStar rho sigma Cpost hdelta :=
  bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_localInputs
    M B R certificate deltaStar rho sigma Cpost hdelta hcombined
      hbaseDvd hchargeDvd htargetTail hW S hpartition Hlocal

/-! ## One-index source-state same-witness assembly -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hcombined :
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hbaseDvd :
      (baseBankFactors R.exactificationState).prod id ∣
        certificate.prechargedTailTarget)
    (hchargeDvd :
      R.selectorTailCharge
            (R.paperFixedExceptionalFactors deltaStar) ∣
        certificate.prechargedTailTarget)
    (htargetTail :
      certificate.prechargedTailTarget *
            centralAnchorDivisor B.sampleData.n
              (centralAnchorCutoff depth B.sampleData.n)
              certificate.q =
        centralTailProduct B.sampleData.n
          (upperTailLength c B.sampleData.n))
    (hW : B.sampleData.W ≠ 0)
    (S : ScaleSeparation M B.sampleData.n B.sampleData.W)
    (hpartition :
      B.partition =
        RegularMeshPrimeCutoffs.Mesh.canonicalPartition
          M hdelta B.n_gt_one hW S)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
        (K0 := K0) B R certificate deltaStar sigma Cpost) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
      M B c depth K0 deltaStar rho sigma Cpost hdelta :=
  bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_sourceStateLocalInputs
    M B R certificate deltaStar rho sigma Cpost hdelta hcombined
      hbaseDvd hchargeDvd htargetTail hW S hpartition Hlocal

/-! ## Eventual same-witness handoff -/

example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n)
    (Hcapacity :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma Cpost hdelta :=
  bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal
    M B deltaStar rho sigma Cpost hdelta hBn Hcapacity Hlocal

/-! ## Eventual source-state same-witness handoff -/

/-- The eventual weak producer receives tail synchronization first, then the
combined-charge terminal, then the local SourceState supplier for those same
capacity witnesses. -/
example
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (hBn :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n)
    (Hcapacity :
      BankPaperCombinedChargeTerminalAtDepth c deltaStar depth)
    (Hlocal :
      BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
        M B c depth K0 deltaStar sigma Cpost hdelta) :
    BankPaperCanonicalSectionNineSynchronizedPostHfitInput
      M B c depth K0 deltaStar rho sigma Cpost hdelta :=
  bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal_sourceStateLocalSupplier
    M B deltaStar rho sigma Cpost hdelta hBn Hcapacity Hlocal

/-! ## Complete public declaration census -/

#check BankPaperCanonicalSectionNinePostHfitLocalInputsAt
#check BankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt
#check
  bankPaperCanonicalSectionNinePostHfitSourceStateLocalInputsAt_of_localInputs
#check BankPaperCanonicalSectionNinePostHfitLocalSupplier
#check BankPaperCanonicalSectionNinePostHfitSourceStateLocalSupplier
#check
  bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_sourceStateLocalInputs
#check
  bankPaperCanonicalSectionNineSynchronizedPostHfitInputAt_of_localInputs
#check
  bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal
#check
  bankPaperCanonicalSectionNineSynchronizedPostHfitInput_of_combinedChargeTerminal_sourceStateLocalSupplier

end BankPaperRealization

end

end Erdos390.WholePaper
