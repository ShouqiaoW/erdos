import Erdos390.WholePaper.BankPaperCanonicalDistributedSectionNineTerminal
import Erdos390.WholePaper.BankPaperCanonicalRatioCellGeometryTrafficConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineBudgetClosure
import Erdos390.WholePaper.BankPaperCanonicalSectionNineFixedComponentCollision

/-!
# Synchronized eventual Section 9 final-payload connector

This file joins the finite final-geometry theorem to the eventual budget,
moment, collision, and capacity interfaces.

The important quantifier choice is existential.  At each sufficiently large
ambient index, one capacity bank and guarded anchor certificate are augmented
by one actual Post-Hfit endpoint for that same pair.  We do not require a
Post-Hfit endpoint for every bank/certificate satisfying the capacity facts.

All estimates after the Post-Hfit endpoint are automatic here:

* the actual moment structure and the lower scale-point bound;
* the clean-list, main, error, ceiling, and actual-`q` scale budgets;
* the fixed-component collision statement; and
* the fixed-rough-depth tail-length comparison.

The remaining input is named
`BankPaperCanonicalSectionNineSynchronizedPostHfitInput`.  It contains no
clean multiplier, tangent flow, post-tangent output, final geometry, or final
payload.  Its only non-capacity mathematical content is an actual Post-Hfit
slack package and the equality identifying the bridge partition with the
literal canonical partition.  Thus it records exactly the still-unavoidable
compatibility gap: the Section 8/Post-Hfit data must be constructed for the
same existential bank and certificate selected at the capacity stage.
-/

open Filter

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PrimeBandQuadrature
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-! ## The exact remaining synchronized input -/

/-- One finite capacity witness augmented by one actual Post-Hfit endpoint.

The four capacity fields are the three fields retained by
`BankPaperCanonicalDistributedSectionNineTerminalAtDepth` and the
tail-charge divisibility consumed by the finite final-payload theorem.  The
remaining existential data are precisely the parameters of
`BankPaperCanonicalPostHfitGuardedSlackPackage`.

In particular, this proposition does not contain a budget closure, a
collision conclusion, a clean-list conclusion, a tangent multiplier, a
post-tangent output, or a final payload. -/
def BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∃ R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)),
    ∃ certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
        R.anchorGuardLeftCore R.anchorGuardRightCore
        (R.centralChangedMarkers depth),
      centralAnchorDivisor B.sampleData.n
            (centralAnchorCutoff depth B.sampleData.n)
            certificate.q * R.prechargeBaseStateProduct ∣
          centralTailProduct B.sampleData.n
            (upperTailLength c B.sampleData.n) ∧
        (baseBankFactors R.exactificationState).prod id ∣
          certificate.prechargedTailTarget ∧
        R.selectorTailCharge
              (R.paperFixedExceptionalFactors deltaStar) ∣
          certificate.prechargedTailTarget ∧
        certificate.prechargedTailTarget *
              centralAnchorDivisor B.sampleData.n
                (centralAnchorCutoff depth B.sampleData.n)
                certificate.q =
            centralTailProduct B.sampleData.n
              (upperTailLength c B.sampleData.n) ∧
        ∃ hW : B.sampleData.W ≠ 0,
          ∃ S : ScaleSeparation M B.sampleData.n B.sampleData.W,
            B.partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hW S ∧
              ∃ betaProt betaAct : Real,
                ∃ oldSeed activeSeed : B.sampleData.Sample → Real,
                  ∃ minusMass plusMass : Real,
                    ∃ radius : NNReal,
                      ∃ quota : Int,
                        ∃ path : Real → B.ParamSpace,
                          ∃ endpoint : Nat → Real,
                            BankPaperRealization.BankPaperCanonicalPostHfitGuardedSlackPackage
                              B K0 R certificate
                              (R.paperFixedExceptionalFactors deltaStar)
                              deltaStar betaProt betaAct sigma
                              oldSeed activeSeed minusMass plusMass
                              radius Cpost
                              (bankPaperCanonicalRatioCellIndex
                                M hdelta B.n_gt_one hW S
                                rho)
                              quota path endpoint

/-- Eventual existential form of the synchronized Post-Hfit input.

The bridge family is fixed before the asymptotic index.  Its exact ambient
index and width equalities are kept outside this definition because they are
also consumed independently by the budget closure. -/
def BankPaperCanonicalSectionNineSynchronizedPostHfitInput
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (c : Real) (depth K0 : Nat)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta) : Prop :=
  ∀ᶠ n : Nat in atTop,
    BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
      M (B n) c depth K0 deltaStar rho sigma Cpost hdelta

/-! ## One-index assembly -/

set_option maxHeartbeats 2000000 in
private theorem bankPaperCanonicalSectionNineFinalPayload_eventStep
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c r0 deltaStar sigma rho tangentConstant Cpost : Real}
    {depth K0 n W : Nat}
    (hdelta : 0 < delta)
    (hBn : B.sampleData.n = n) (hBW : B.sampleData.W = W)
    (hWtwo : 2 ≤ W)
    (hr0three : r0 < 3 / 2)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hprime : TangentFixedRatioPrimeIntervalOccupied W rho)
    (Hinput :
      BankPaperCanonicalSectionNineSynchronizedPostHfitInputAt
        M B c depth K0 deltaStar rho sigma Cpost hdelta)
    (Hbudget :
      ∀ (hn : 1 < n) (hW : W ≠ 0)
        (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth))
        (S : ScaleSeparation M n W)
        (endpoint : Nat → Real),
        BankPaperCanonicalSectionNineBudgetClosure
          (K0 := K0) M B R certificate deltaStar sigma
          hdelta hn hW S r0 rho tangentConstant Cpost endpoint)
    (Hmoment :
      ∃ hWne : W ≠ 0, ∃ hn : 1 < n,
        (∀ k : Fin M.cellCount,
          (2 : Real) ≤ scalePoint n (M.lower k)) ∧
        ∀ S : ScaleSeparation M n W,
          RegularMeshPrimeCutoffs.Mesh.MomentReady M
            (RegularMeshPrimeCutoffs.Mesh.canonicalPartition
              M hdelta hn hWne S))
    (Hcollision :
      ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n)))
        (deltaStar : Real),
        R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
          deltaStar)
    (hKh : (K0 + 1) * upperTailLength c n ≤ n) :
    ∃ R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n)),
      ∃ certificate : GuardedCentralAnchorCertificate c depth n
          R.anchorGuardLeftCore R.anchorGuardRightCore
          (R.centralChangedMarkers depth),
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * R.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors R.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
          certificate.prechargedTailTarget *
                centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q =
              centralTailProduct n (upperTailLength c n) ∧
          ∃ W' K : Nat,
            ∃ selector : Nat → Real,
              ∃ flow : BankPaperCanonicalTangentPrime n W' →
                  BankPaperCanonicalTangentPrime n W' → Real,
                ∃ L sigma' : Real,
                  R.BankPaperCanonicalSectionNineFinalPayload (K := K)
                    certificate deltaStar selector flow L sigma' := by
  subst n
  subst W
  obtain ⟨R, certificate, hcombined, hbaseDvd, hchargeDvd,
    htargetTail, hWne, S, hpartition, betaProt, betaAct,
    oldSeed, activeSeed, minusMass, plusMass, radius, quota, path,
    endpoint, Hpost⟩ := Hinput
  obtain ⟨hWmoment, hn, hTwo, HmomentReady⟩ := Hmoment
  have Hbudget' :
      BankPaperCanonicalSectionNineBudgetClosure
        (K0 := K0) M B R certificate deltaStar sigma
          hdelta hn hWmoment S r0 rho tangentConstant Cpost endpoint :=
    Hbudget hn hWmoment R certificate S endpoint
  unfold BankPaperCanonicalSectionNineBudgetClosure at Hbudget'
  obtain ⟨_hBnBudget, _hBWBudget, hlowerPos, hlower, hlowerScale,
    hmain, herror, hceiling, hscaleDom, hscale⟩ := Hbudget'
  have hdensity :
      0 < tangentPaperCleanListDensity B.sampleData.W r0 :=
    tangentPaperCleanListDensity_pos B.sampleData.W
      (hr0three.trans (by norm_num))
  have hN : 0 < secondOrderScale B.sampleData.n :=
    secondOrderScale_pos (by omega)
  have hfixedComponents :
      R.BankPaperCanonicalSectionNineFixedComponentCollisionFree
        deltaStar :=
    Hcollision R deltaStar
  let flow :
      BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W →
        BankPaperCanonicalTangentPrime B.sampleData.n B.sampleData.W → Real :=
    R.bankPaperCanonicalSectionNineRatioCellFlow
      M certificate deltaStar (K0 + 1) hdelta B.n_gt_one
        hWne S rho endpoint
  have Hpost' := Hpost
  unfold BankPaperRealization.BankPaperCanonicalPostHfitGuardedSlackPackage
    at Hpost'
  have HselectorPartition :
      BankPaperCanonicalRoundedSelectorTangentInput R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet certificate
          deltaStar (K0 + 1))
        B.partition.band
        (bankPaperCanonicalRatioCellIndex
          M hdelta B.n_gt_one (by omega) S rho)
        (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
        (tangentRatioCellTailPointwiseUpper
          (bankPaperCanonicalActualP87PointwiseUpper B B.q Cpost)
          B.partition.band
          (bankPaperCanonicalRatioCellIndex
            M hdelta B.n_gt_one (by omega) S rho))
        endpoint := by
    exact Hpost'.2.2.2.2.1
  have Hslack :
      R.BankPaperCanonicalGuardedEndpointSlackConstruction certificate
        deltaStar B.sampleData.W (K0 + 1)
        (BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) B.L sigma endpoint := by
    exact Hpost'.2.2.2.2.2
  have hpayload :
      R.BankPaperCanonicalSectionNineFinalPayload (K := K0 + 1)
        certificate deltaStar endpoint flow B.L sigma := by
    exact
      (BankPaperRealization.bankPaperCanonicalSectionNineFinalPayload_of_roundedSelector_guardedSlack
        (c := c) (depth := depth) (K0 := K0)
        M B R certificate deltaStar
        (BankPaperRealization.bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) sigma radius Cpost endpoint
        hdelta hWtwo S hpartition r0 rho tangentConstant
        (secondOrderScale B.sampleData.n)
        (tangentPaperCleanListDensity B.sampleData.W r0)
        hrho hratio htangent.le hN hscaleDom hMertens hPNT hprime
        hTwo (HmomentReady S) HselectorPartition Hslack
        hKh hdensity hsigma hscale
        hchargeDvd hfixedComponents hmain herror hceiling
        hlowerPos hlower hlowerScale).1
  exact ⟨R, certificate, hcombined, hbaseDvd, htargetTail,
    B.sampleData.W, K0 + 1, endpoint, flow, B.L, sigma, hpayload⟩

/-! ## Eventual final-payload assembly -/

/-- Assemble a synchronized distributed Section 9 terminal.

Only the actual active-mass upper bound and the synchronized Post-Hfit input
remain asymptotic premises.  Moment readiness, all clean-list and scalar
budgets, fixed-component collision-freedom, and the rough-depth tail
comparison are invoked internally.

The fixed ratio is chosen before the asymptotic index and is required to lie
strictly between `1` and the cubic threshold imposed by `r0`. -/
theorem
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_synchronizedPostHfit
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (W K0 depth : Nat)
    {c r0 deltaStar rho tangentConstant sigma Cpost Cq : Real}
    (hdelta : 0 < delta) (hc : 0 < c)
    (hr0one : 1 < r0) (hr0three : r0 < 3 / 2)
    (hdeltaStar :
      IsPaperCombinedTangentDeltaStar c W r0 deltaStar)
    (hWtwo : 2 ≤ W) (hprefix : 2 * depth + 1 ≤ W)
    (hMoment : canonicalActualMomentCutoff ≤ W)
    (hMertens : fullReciprocalSumUniformCutoff ≤ W)
    (hrho : 1 < rho) (hratio : rho ^ 3 < r0)
    (htangent : 0 < tangentConstant) (hsigma : 0 < sigma)
    (hwidth :
      delta + M.ratio ≤
        bankPaperCanonicalRatioCellPaperWidthChoice
          (tangentPaperCleanListDensity W r0)
          sigma rho tangentConstant)
    (hCpost : 0 ≤ Cpost)
    (hcoefficient :
      (2 / 9 : Real) * Cpost * Cq ≤ tangentConstant)
    (hPNT : TangentFixedRatioPrimeCountLower W rho)
    (hprime :
      TangentFixedRatioPrimeIntervalOccupied W rho)
    (hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W)
    (hqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q ≤ Cq * secondOrderScale n)
    (Hinput :
      BankPaperCanonicalSectionNineSynchronizedPostHfitInput
        M B c depth K0 deltaStar rho sigma Cpost hdelta) :
    BankPaperCanonicalDistributedSectionNineTerminalAtDepth
      c deltaStar depth := by
  have Hbudget :=
    eventually_bankPaperCanonicalSectionNineBudgetClosure
      M B W K0 depth hdelta hc hr0one hr0three
      hdeltaStar.1.1 hdeltaStar.1.2.1 hdeltaStar.2
      hWtwo hprefix hrho hratio htangent hsigma hwidth
      hCpost hcoefficient hsync hqUpper
  have HmomentReady :=
    eventually_bankPaperCanonical_actualMomentReady
      M hdelta W hMoment
  have Hcollision :=
    eventually_bankPaperCanonicalSectionNineFixedComponentCollisionFree hc
  have HKh :=
    BankPaperRealization.eventually_mul_upperTailLength_le_self
      (K0 + 1) hc
  simp only [BankPaperCanonicalSectionNineSynchronizedPostHfitInput]
    at Hinput
  simp only [BankPaperCanonicalDistributedSectionNineTerminalAtDepth]
  filter_upwards [Hinput, hsync, Hbudget, HmomentReady, Hcollision, HKh] with
    n HinputN hsyncN HbudgetN HmomentN HcollisionN hKhN
  exact
    bankPaperCanonicalSectionNineFinalPayload_eventStep
      M (B n) hdelta hsyncN.1 hsyncN.2 hWtwo hr0three
      hrho hratio htangent hsigma hMertens hPNT hprime
      HinputN HbudgetN HmomentN HcollisionN hKhN

/-! ## Parameter-synchronized residual interface -/

/-- The analytic data which still have to augment the synchronized capacity
terminal chosen by `exists_bankPaperCanonicalSectionNineParameterSynchronization`.

This package contains no final-payload conclusion.  Its two genuinely
external parts are:

* the active-mass estimate `q ≤ Cq * secondOrderScale`; and
* the synchronized Post-Hfit input for the same existential capacity
  witnesses.

The mesh-width data remain visible.  The fixed-ratio PNT and occupancy
cutoffs are not fields of this package: the theorem below enlarges `W` after
the capacity depth is selected and proves both cutoff predicates itself. -/
def BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion
    (c : Real) (depth W : Nat) (r0 deltaStar : Real) : Prop :=
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
                BankPaperCanonicalSectionNineSynchronizedPostHfitInput
                  M B c depth K0 deltaStar (21 / 20 : Real)
                    sigma Cpost hdelta

/-- Choose the capacity depth first, then its width, tangent exponent, and
one complete synchronized finite-payload terminal.

The hypothesis is intentionally a capacity-augmentation interface: it
receives the already proved combined-charge terminal and must return the
named analytic completion, rather than a final payload or a post-tangent
continuation.

Unlike the earlier core parameter projection, this theorem also chooses the
quantitative PNT and interval-occupancy cutoffs before fixing `W`.  The common
width is taken only after the capacity depth is known, so the depth/width
order remains the one required by the paper. -/
theorem
    exists_bankPaperCanonicalSectionNineParameterSynchronizedFinalPayload
    {c : Real} (hc : C0 < c)
    (Hcompletion :
      ∀ (depth W : Nat) (r0 deltaStar : Real),
        201 ≤ depth →
        2 ≤ W →
        2 * depth + 1 ≤ W →
        fullReciprocalSumUniformCutoff ≤ W →
        canonicalActualMomentCutoff ≤ W →
        1 < r0 →
        r0 < 3 / 2 →
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar →
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth →
          BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion
            c depth W r0 deltaStar) :
    ∃ depth W : Nat, ∃ r0 deltaStar : Real,
      201 ≤ depth ∧
        2 ≤ W ∧
        2 * depth + 1 ≤ W ∧
        fullReciprocalSumUniformCutoff ≤ W ∧
        canonicalActualMomentCutoff ≤ W ∧
        1 < r0 ∧
        r0 < 3 / 2 ∧
        IsPaperCombinedTangentDeltaStar c W r0 deltaStar ∧
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth ∧
        BankPaperCanonicalDistributedSectionNineTerminalAtDepth
          c deltaStar depth := by
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice hc
  let r0 : Real := 5 / 4
  let rho : Real := 21 / 20
  have hr0one : 1 < r0 := by norm_num [r0]
  have hr0three : r0 < 3 / 2 := by norm_num [r0]
  have hr0two : r0 < 2 := by norm_num [r0]
  have hrho : 1 < rho := by norm_num [rho]
  have hratio : rho ^ 3 < r0 := by norm_num [rho, r0]
  obtain ⟨WPNT, _hWPNTtwo, _hWPNTMertens, hWPNT⟩ :=
    exists_fixedRatioPrimeCountLower_and_Mertens_cutoff hrho
  obtain ⟨Woccupancy, _hWoccupancyTwo, hWoccupancy⟩ :=
    exists_fixedRatioPrimeIntervalOccupancy_cutoff hrho
  let W : Nat :=
    max (2 * depth + 1)
      (max tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy)))
  have hprefix : 2 * depth + 1 ≤ W := by
    dsimp only [W]
    exact le_max_left _ _
  have hMertensBase : tangentSelbergMertensBase ≤ W := by
    dsimp only [W]
    exact
      (le_max_left tangentSelbergMertensBase
        (max canonicalActualMomentCutoff (max WPNT Woccupancy))).trans
          (le_max_right _ _)
  have hWtwo : 2 ≤ W :=
    tangentSelbergMertensBase_ge_two.trans hMertensBase
  have hMertens : fullReciprocalSumUniformCutoff ≤ W :=
    tangentSelbergMertensBase_ge_cutoff.trans hMertensBase
  have hMoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W]
    exact
      ((le_max_left canonicalActualMomentCutoff
        (max WPNT Woccupancy)).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWPNTW : WPNT ≤ W := by
    dsimp only [W]
    exact
      (((le_max_left WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hWoccupancyW : Woccupancy ≤ W := by
    dsimp only [W]
    exact
      (((le_max_right WPNT Woccupancy).trans
        (le_max_right canonicalActualMomentCutoff
          (max WPNT Woccupancy))).trans
          (le_max_right tangentSelbergMertensBase
            (max canonicalActualMomentCutoff (max WPNT Woccupancy)))).trans
        (le_max_right _ _)
  have hPNT : TangentFixedRatioPrimeCountLower W rho :=
    tangentFixedRatioPrimeCountLower_mono_cutoff hWPNTW hWPNT
  have hprime : TangentFixedRatioPrimeIntervalOccupied W rho :=
    tangentFixedRatioPrimeIntervalOccupied_mono_cutoff
      hWoccupancyW hWoccupancy
  let deltaStar := paperCombinedTangentDeltaStar c W r0
  obtain ⟨hdeltaStar', Hcharge'⟩ :=
    huniform W r0 hr0two
  have Hanalytic :=
    Hcompletion depth W r0 deltaStar hdepth hWtwo hprefix
      hMertens hMoment hr0one hr0three hdeltaStar' Hcharge'
  unfold BankPaperCanonicalSectionNineSynchronizedAnalyticCompletion
    at Hanalytic
  obtain ⟨delta, eta, M, P, B, K0, tangentConstant, sigma,
    Cpost, Cq, hdelta, htangent, hsigma, hwidth, hCpost,
    hcoefficient, hsync, hqUpper, Hinput⟩ :=
    Hanalytic
  have hcPos : 0 < c := by
    have hC0Pos : (0 : Real) < C0 := by norm_num [C0]
    exact hC0Pos.trans hc
  have Hterminal :=
    bankPaperCanonicalDistributedSectionNineTerminalAtDepth_of_synchronizedPostHfit
      M B W K0 depth hdelta hcPos hr0one hr0three hdeltaStar'
      hWtwo hprefix hMoment hMertens hrho hratio htangent hsigma hwidth
      hCpost hcoefficient hPNT hprime hsync hqUpper Hinput
  exact ⟨depth, W, r0, deltaStar, hdepth, hWtwo, hprefix,
    hMertens, hMoment, hr0one, hr0three, hdeltaStar',
    Hcharge', Hterminal⟩

end

end Erdos390.WholePaper
