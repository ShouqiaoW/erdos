import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightEventualSupplierConnector

/-!
# A placed-selector provider chosen before the final mesh

The placed-selector paper-rate theorem already chooses its uniform constant
before the regular relative mesh.  In the fixed-mesh Post-Hfit compositor,
however, its analytic `d`-bound and final-active-mass lower bound were
specialized only after a mesh had been supplied.

This file packages the same argument in the source-first parameter order.
The Section 8 ledger first selects one nonnegative `Cinitial`.  On one
common tail, and uniformly for every later mesh, the callback consumes only
the literal local source synchronizations, the alpha and beta boxes, the
nonempty correction pool, and exact synchronization of `d` and the fresh
bridge mass with their Section 8 families.  Its conclusion is exactly the
placed-selector deficit estimate; no Post-Hfit or terminal conclusion is
included.
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

set_option maxHeartbeats 2400000

/-! ## The literal mesh-uniform callback -/

/-- The exact placed-selector field supplied after `Cinitial` has been
chosen.

The mesh occurs only inside the eventual callback.  The two analytic
premises are equalities with the displayed Section 8 families, rather than
already-proved norm bounds.  The remaining premises are literal local
source, canonical-sample, box, and correction-pool data consumed by the
placed-selector theorem. -/
def
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 : Nat)
    (deltaStar betaProt betaAct mu : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (Cinitial : Real) : Prop :=
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
            ((p : Real) * J.postHeightBridge.L)

/-! ## Selection from the Section 8 ledger -/

/-- Select one placed-selector constant from the exact Section 8 ledger,
strictly before any final regular mesh is introduced.

The proof intersects the uniform placed-selector event with the ledger's
`d = O(secondOrderScale / L)` estimate and positive paper-scale lower bound
for the final active mass.  Exact local family synchronization then supplies
the two numerical inequalities required by the underlying theorem. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider
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
      BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
        Patterns I Cprom Cbank G (c := c) depth W K0
          deltaStar betaProt betaAct mu
          logY Lambda0 mFrozen qTilde Cinitial := by
  have hWone : 1 < W := by omega
  obtain ⟨Azero, hAzero, Nzero, Hzero⟩ :=
    exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate
      Patterns I Cprom Cbank G W hWone hHeadLe
  have HdBigO :=
    bankPaperCanonicalSectionEight_d_isBigO
      W (K0 + 1) c betaAct hmu
        logY Lambda0 mFrozen qTilde Hledger
  obtain ⟨Cd, hCd, Hd⟩ := (isBigO_iff').mp HdBigO
  rcases
      bankPaperCanonicalSectionEight_finalActiveMass_paperScaleLower
        W (K0 + 1) hc hbetaAct hmu
          logY Lambda0 mFrozen qTilde Hledger with
    ⟨cFinal, hcFinal, HfinalMass⟩
  obtain ⟨Cinitial, hCinitial, Hselector⟩ :=
    exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate
      (betaProt := betaProt) (betaAct := betaAct)
      P Patterns I Cprom Cbank G W K0 depth hTwoW hHeadLe
        hc hdeltaStar hdeltaStarUpper (by norm_num : (0 : Real) < 1)
        hcFinal hAzero.le hCd.le hprefix
  refine ⟨Cinitial, hCinitial, ?_⟩
  unfold
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshPlacedSelectorCallback
  filter_upwards [
      Hselector, Hd, HfinalMass, eventually_ge_atTop Nzero]
      with n hselectorN hdN hfinalMassN hNzero
  intro delta eta M hmesh Bsource hBn hBW R certificate J S
    hbetaProtSync hbetaActSync hsep hremaining hcanonical hqTilde
    halpha hbetaBox hpool hdFamily hqFamily
  subst n
  have hscaleDiv :
      0 < secondOrderScale Bsource.sampleData.n /
        L Bsource.sampleData.n := by
    have hnOne : 1 < Bsource.sampleData.n := by
      simpa only [
        BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
        using J.postHeightBridge.n_gt_one
    exact div_pos (secondOrderScale_pos hnOne) (L_pos hnOne)
  have hdBound :
      |(J.d : Real)| ≤
        Cd *
          (secondOrderScale J.postHeightBridge.sampleData.n /
            J.postHeightBridge.L) := by
    have hdBoundN :
        |bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n| ≤
          Cd * (secondOrderScale Bsource.sampleData.n /
            L Bsource.sampleData.n) := by
      simpa only [Real.norm_eq_abs, abs_of_pos hscaleDiv] using hdN
    simpa only [
      hdFamily,
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData,
      BridgeData.L] using hdBoundN
  have hmass :
      cFinal *
          secondOrderScale J.postHeightBridge.sampleData.n ≤
        J.postHeightBridge.q := by
    rw [hqFamily]
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hfinalMassN
  have hzero :
      ∀ p : BandPrime J.postHeightBridge.sampleData.n
            J.postHeightBridge.sampleData.W,
        ∀ sign : PhysicalSign,
          (J.postHeightBridge.guardedCellProbability
              (none, sign)).expect
              (fun m ↦ valuation p.1 (m : Nat)) ≤
            Azero / (p.1 : Real) := by
    intro p sign
    exact
      Hzero J.postHeightBridge
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hNzero)
        (by
          simpa only [
            BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
            using hBW)
        hsep hremaining hcanonical p sign
  exact
    hselectorN M hmesh Bsource rfl hBW R certificate J S
      hbetaProtSync hbetaActSync hsep hremaining hcanonical hqTilde
      halpha hbetaBox hpool hdBound hmass hzero

end BankPaperRealization

end

end Erdos390.WholePaper
