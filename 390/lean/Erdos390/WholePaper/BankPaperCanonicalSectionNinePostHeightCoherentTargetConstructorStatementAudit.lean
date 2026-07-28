import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor

/-!
# Statement audit for the coherent post-height target constructor

The first expanded statement records that one tail family retains all six
literal conclusions of the depth-first combined-charge terminal on the same
fiber.  The second records the paper-order choice boundary: the exponent and
positive head margin are fixed before the mesh, while the eventual conclusion
exposes the exact source target, post-height ledger values, head inclusion,
selector factorization, and terminal divisibilities used by the residual
connector.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

/-! ## Exact six-conjunct guarded-tail selection -/

example
    {c deltaStar : Real} {depth : Nat}
    (H : BankPaperCombinedChargeTerminalAtDepth c deltaStar depth) :
    ∃ N : Nat, ∃ F : BankPaperCanonicalGuardedTailFamily c depth N,
      ∀ n (hn : N ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n) :=
  exists_bankPaperCanonicalGuardedTailFamily_of_combinedChargeTerminalAtDepth H

/-! ## Fixed-before-mesh choice order and residual-facing output -/

namespace BankPaperRealization

example
    {c deltaStar betaProt betaAct : Real}
    {depth Ntail W K0 : Nat}
    (hc : C0 < c)
    (hdeltaStar : IsPaperCombinedChargeDeltaStar c deltaStar)
    (hW : 0 < W) (hbetaAct : 0 < betaAct)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (hterminal :
      ∀ n (hn : Ntail ≤ n),
        let R := F.realization n hn
        let certificate := F.certificate n hn
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
            certificate.prechargedTailTarget ∧
          (∀ p ∈ primesUpTo (2 * depth + 1),
            (c - C0) / (24 * (((p - 1 : Nat) : Real))) *
                  secondOrderScale n +
                (R.selectorTailCharge
                  (R.paperFixedExceptionalFactors deltaStar)).factorization p ≤
              certificate.prechargedTailTarget.factorization p) ∧
          certificate.selectorTailTarget R
                (R.paperFixedExceptionalFactors deltaStar) *
              R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) =
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
              centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q =
            centralTailProduct n (upperTailLength c n))
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n => bankPaperCanonicalRawSmoothBaseMass W n
          (upperTailLength c n) (K0 + 1) betaAct)
        (F.extendedGuardedSmoothBaseMass
          W (K0 + 1) betaAct deltaStar)
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen
          (F.extendedGuardedSmoothBaseMass
            W (K0 + 1) betaAct deltaStar))) :
    ∃ E : Nat, ∃ margin : Real,
      0 < E ∧ 0 < margin ∧
        0 <
          bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2 ∧
        ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta),
          ∀ᶠ n : Nat in atTop,
            ∀ (hdelta : 0 < delta)
              (D : StructuredSampleData
                (PaperHeadSimplex.Tag (primesUpTo W))),
              D.n = n →
              D.W = W →
              ∃ hnD : 1 < D.n,
              ∃ hWD : D.W ≠ 0,
              ∃ hw : 0 < delta + eta,
              ∀ (S : ScaleSeparation M D.n D.W)
                (_hpattern :
                  D.pattern =
                    PaperHeadSimplex.pattern (primesUpTo W)
                      (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                        W) E)
                (hlo : ∀ sigma, D.lo sigma =
                  physicalBound
                    (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.lower
                      sigma) D.n)
                (hhi : ∀ sigma, D.hi sigma =
                  physicalBound
                    (bankPaperCanonicalSectionNinePostHeightPhysicalIntervals.upper
                      sigma) D.n),
                ∃ hnTail : Ntail ≤ D.n,
                  let R := F.realization D.n hnTail
                  let certificate := F.certificate D.n hnTail
                  let qSource :=
                    F.extendedGuardedSmoothBaseMass
                      W (K0 + 1) betaAct deltaStar D.n
                  let target : {p : Nat // p ∈ primesUpTo W} → Real :=
                    fun p =>
                      ((certificate.selectorTailTarget R
                        (R.paperFixedExceptionalFactors
                          deltaStar)).factorization p.1 : Real)
                  ∃ Rhead : HeadSimplexReserve (primesUpTo W),
                    Rhead.exponent = E ∧
                      Rhead.activeMass = qSource ∧
                      Rhead.margin = margin ∧
                      (∀ p, Rhead.target p = target p) ∧
                      (let Kphysical :=
                        bankPaperCanonicalSectionNinePostHeightFixedPhysicalTarget
                       let Tsource :=
                        bankPaperCanonicalSectionNineCoherentSourceTarget
                          M D
                            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                            hlo hhi Rhead Kphysical hdelta
                            hnD hWD S hw
                       let Bsource :=
                        bankPaperCanonicalSectionNineCoherentSourceBridge
                          M D
                            bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                            hlo hhi Rhead Kphysical hdelta
                            hnD hWD S hw
                       let alpha :=
                        bankPaperCanonicalPostHfitBalancedAlpha
                          Bsource c K0 betaProt betaAct
                       mFrozen D.n =
                            bankPaperCanonicalTopFrozenSmoothFrozenMass
                              (K := K0 + 1) Bsource R certificate
                                deltaStar betaProt alpha →
                         logY D.n =
                            bankPaperCanonicalSectionNinePostHeightLogY
                              Bsource R certificate →
                         Lambda0 D.n =
                            bankPaperCanonicalSectionNinePostHeightRoundedLambda0
                              (K0 + 1) Bsource R certificate Tsource
                                deltaStar betaProt alpha
                                (betaProt + betaAct) qSource →
                         ∃ J :
                            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
                              (K0 := K0) M Bsource R certificate
                                bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                deltaStar hdelta,
                           J.Tsource =
                                J.postHeightBridge.barycentricTargetOfPaperData
                                  bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
                                  J.postHeightHlo J.postHeightHhi
                                  Rhead Kphysical ∧
                             J.qTilde = Rhead.activeMass ∧
                             J.qTilde =
                                bankPaperCanonicalGuardedSmoothBaseMass
                                  R certificate deltaStar W
                                    (K0 + 1) betaAct ∧
                             J.exponent = E ∧
                             J.d =
                                bankPaperCanonicalSmoothDIntFamily
                                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                                  logY Lambda0 mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.betaProt = betaProt ∧
                             J.betaAct = betaAct ∧
                             J.q0 =
                                bankPaperCanonicalSmoothQ0Family
                                  mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.A0 =
                                bankPaperCanonicalSmoothA0Family
                                  logY Lambda0 mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.qn =
                                bankPaperCanonicalSmoothFinalActiveMassFamily
                                  bankPaperCanonicalSectionNinePostHeightPhysicalMu
                                  logY Lambda0 mFrozen
                                  (F.extendedGuardedSmoothBaseMass
                                    W (K0 + 1) betaAct deltaStar) D.n ∧
                             J.targetInputs.headMargin = margin ∧
                             J.targetInputs.physicalEta =
                                bankPaperCanonicalSectionNinePostHeightPhysicalEta /
                                  2 ∧
                             J.postHeightBridge.sampleData.pattern =
                                PaperHeadSimplex.pattern (primesUpTo W)
                                  (bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime
                                    W) Rhead.exponent ∧
                             primesUpTo J.postHeightBridge.sampleData.W ⊆
                                primesUpTo W ∧
                             (∀ p : {p : Nat // p ∈ primesUpTo W},
                                p.1 ≤ J.postHeightBridge.sampleData.W →
                                  Rhead.target p =
                                    ((certificate.selectorTailTarget R
                                      (R.paperFixedExceptionalFactors
                                        deltaStar)).factorization p.1 :
                                      Real)) ∧
                             centralAnchorDivisor D.n
                                    (centralAnchorCutoff depth D.n)
                                    certificate.q *
                                  R.prechargeBaseStateProduct ∣
                                centralTailProduct D.n
                                  (upperTailLength c D.n) ∧
                             R.selectorTailCharge
                                  (R.paperFixedExceptionalFactors deltaStar) ∣
                                certificate.prechargedTailTarget) :=
  exists_eventually_bankPaperCanonicalSectionNinePostHeightCoherentTarget_of_guardedTailFamily
    hc hdeltaStar hW hbetaAct F hterminal logY Lambda0 mFrozen Hledger

/-! ## Complete public declaration census -/

#check
  exists_bankPaperCanonicalSectionNinePostHeightBridgeInputsAt_of_coherentMargins
#check
  exists_eventually_bankPaperCanonicalSectionNinePostHeightCoherentTarget_of_guardedTailFamily

end BankPaperRealization

#check
  exists_bankPaperCanonicalGuardedTailFamily_of_combinedChargeTerminalAtDepth
#check bankPaperCanonicalSectionNinePostHeightHeadLinearFloor
#check bankPaperCanonicalSectionNinePostHeightHeadLinearFloor_pos
#check bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
#check
  eventually_upperTailValuation_le_postHeightHeadUpperCoefficient_on_finset
#check
  eventually_bankPaperCanonicalSectionNinePostHeight_selectorTarget_headBounds
#check bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
#check
  exists_eventually_bankPaperCanonicalSectionNinePostHeight_sourceAndFinalMass_linearBounds
#check
  bankPaperCanonicalSectionNinePostHeightPhysicalMean_eq_smoothFamilyRatio
#check bankPaperCanonicalSectionNineTargetScaffoldBaseline
#check bankPaperCanonicalSectionNineTargetScaffoldBridge
#check bankPaperCanonicalSectionNineTargetScaffoldBridge_sampleData
#check bankPaperCanonicalSectionNineCoherentSourceHeadReserve
#check bankPaperCanonicalSectionNineCoherentSourceHeadReserve_exponent
#check bankPaperCanonicalSectionNineCoherentSourceHeadReserve_activeMass
#check bankPaperCanonicalSectionNineCoherentSourceHeadReserve_target
#check bankPaperCanonicalSectionNineCoherentSourceTarget
#check bankPaperCanonicalSectionNineCoherentSourceBridge
#check bankPaperCanonicalSectionNineCoherentSourceBridge_sampleData
#check bankPaperCanonicalSectionNineCoherentSourceTarget_eq_bridgeTarget
#check bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime

end

end Erdos390.WholePaper
