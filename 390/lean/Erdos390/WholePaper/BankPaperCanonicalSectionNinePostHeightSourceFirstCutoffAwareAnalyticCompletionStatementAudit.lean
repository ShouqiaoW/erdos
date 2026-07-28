import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCutoffAwareAnalyticCompletion

/-!
# Expanded statement audit: cutoff-aware source-first analytic completion

This audit assigns the production theorem directly to its complete public
output expansion.  In particular, the Proposition 8.7 cutoff `W0` is chosen
before the universally quantified final width `W`.

The concluding
`BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion` is not
left behind an alias.  Its synchronized eventual Post-Hfit input is also
expanded pointwise, displaying the realization, certificate, canonical mesh
partition, source target, rounded source parameters, and guarded slack
package for the same bridge family.
-/

open Filter Topology Set Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 4000000 in
example
    {c : Real} (hc : C0 < c) :
    ∀ depth : Nat, 201 ≤ depth →
      ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
        2 ≤ W →
        2 * depth + 1 ≤ W →
        fullReciprocalSumUniformCutoff ≤ W →
        canonicalActualMomentCutoff ≤ W →
        ∀ r0 deltaStar : Real,
          1 < r0 →
          r0 < 3 / 2 →
          IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
          BankPaperCombinedChargeTerminalAtDepth c deltaStar depth →
          ∃ delta eta : Real,
            ∃ M : RegularRelativeMesh.Mesh delta eta,
              ∃ P : Finset Nat,
                ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
                    (BankPaperCanonicalExponentBand M),
                  ∃ K0 : Nat,
                    ∃ tangentConstant sigma Cpost Cq : Real,
                      ∃ hdelta : 0 < delta,
                        0 < tangentConstant ∧
                          0 < sigma ∧
                          delta + M.ratio ≤
                            bankPaperCanonicalRatioCellPaperWidthChoice
                              (tangentPaperCleanListDensity W r0)
                              sigma (21 / 20 : Real) tangentConstant ∧
                          0 ≤ Cpost ∧
                          (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant ∧
                          (∀ᶠ n : Nat in atTop,
                            (B n).sampleData.n = n ∧
                              (B n).sampleData.W = W) ∧
                          (∀ᶠ n : Nat in atTop,
                            (B n).q ≤ Cq * secondOrderScale n) ∧
                          ∀ᶠ n : Nat in atTop,
                            ∃ R : BankPaperRealization
                                (B n).sampleData.n
                                (upperEndpoint (B n).sampleData.n
                                  (upperTailLength c
                                    (B n).sampleData.n)),
                              ∃ certificate :
                                  GuardedCentralAnchorCertificate c depth
                                    (B n).sampleData.n
                                    R.anchorGuardLeftCore
                                    R.anchorGuardRightCore
                                    (R.centralChangedMarkers depth),
                                centralAnchorDivisor
                                      (B n).sampleData.n
                                      (centralAnchorCutoff depth
                                        (B n).sampleData.n)
                                      certificate.q *
                                      R.prechargeBaseStateProduct ∣
                                    centralTailProduct
                                      (B n).sampleData.n
                                      (upperTailLength c
                                        (B n).sampleData.n) ∧
                                  (baseBankFactors
                                      R.exactificationState).prod id ∣
                                    certificate.prechargedTailTarget ∧
                                  R.selectorTailCharge
                                        (R.paperFixedExceptionalFactors
                                          deltaStar) ∣
                                    certificate.prechargedTailTarget ∧
                                  certificate.prechargedTailTarget *
                                        centralAnchorDivisor
                                          (B n).sampleData.n
                                          (centralAnchorCutoff depth
                                            (B n).sampleData.n)
                                          certificate.q =
                                      centralTailProduct
                                        (B n).sampleData.n
                                        (upperTailLength c
                                          (B n).sampleData.n) ∧
                                  ∃ hW : (B n).sampleData.W ≠ 0,
                                    ∃ S : ScaleSeparation M
                                        (B n).sampleData.n
                                        (B n).sampleData.W,
                                      (B n).partition =
                                          RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                                            M hdelta (B n).n_gt_one hW S ∧
                                        ∃ Tsource :
                                            BarycentricTarget
                                              (B n).sampleData,
                                          ∃ betaProt alpha beta
                                              qTilde : Real,
                                            ∃ placementSeed activeSeed :
                                                (B n).sampleData.Sample →
                                                  Real,
                                              ∃ radius : NNReal,
                                                ∃ quota : Int,
                                                  ∃ path :
                                                      Real →
                                                        (B n).ParamSpace,
                                                    ∃ endpoint :
                                                        Nat → Real,
                                                      BankPaperRealization.BankPaperCanonicalTopFrozenRoundedPostHfitGuardedSlackPackage
                                                        (K := K0 + 1)
                                                        (B n) R certificate
                                                        (R.paperFixedExceptionalFactors
                                                          deltaStar)
                                                        Tsource deltaStar
                                                        betaProt alpha beta
                                                        qTilde sigma
                                                        placementSeed
                                                        activeSeed radius
                                                        Cpost
                                                        (bankPaperCanonicalRatioCellIndex
                                                          M hdelta
                                                          (B n).n_gt_one
                                                          hW S
                                                          (21 / 20 :
                                                            Real))
                                                        quota path
                                                        endpoint := by
  simpa only [
    BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion,
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInput,
    BankPaperCanonicalSectionNineTopFrozenSynchronizedPostHfitInputAt] using
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion
      hc

/-! ## Public declaration census -/

#check
  exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion

end BankPaperRealization

end

end Erdos390.WholePaper
