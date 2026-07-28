import Erdos390.Full.SelectedDyadicRegularMesh
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Connector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshSelectorProvider
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshEventualCoherentBridgeSourceObligation
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstPreselectedPostHfitConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceObligationPublicSyncConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletionConnector

/-!
# Cutoff-aware source-first analytic completion

This module performs the remaining source-first choices in the dependency
order used by the paper.  At a fixed capacity depth, Proposition 8.7 first
selects a mesh tolerance and a width cutoff.  Only after the final width is
given do we choose the guarded tail family, the positive protected/active
split, the common Section 8 ledger, the selector and Proposition 8.7
constants, and the tangent budget.  The final dyadic regular mesh is selected
last, fine enough simultaneously for Proposition 8.7 and the Section 9
tangent width.

The conclusion is the public synchronized analytic completion, not a
distributed terminal.  Thus the depth-first combined-charge terminal remains
an explicit input to this construction.
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
/-- At each already selected capacity depth, choose one Proposition 8.7
width cutoff.  Every later width satisfying that cutoff and the public
Section 9 cutoffs admits the complete frozen-top synchronized analytic
completion for the same combined tangent exponent and capacity terminal.

The mesh tolerance is chosen before `W`; all numerical, ledger, selector,
and P87 constants are chosen before the final explicit dyadic mesh. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareAnalyticCompletion
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
          BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
            c depth W r0 deltaStar := by
  intro depth _hdepth
  let I :=
    bankPaperCanonicalSectionNinePostHeightPhysicalIntervals
  let G : ∀ n, Ledger n 2 0 :=
    roughCanonicalBridgeRelevantLedgerFamily depth
  have hlowerOne : ∀ sign, 1 ≤ I.lower sign := by
    intro sign
    simpa only [I] using
      bankPaperCanonicalSectionNinePostHeightPhysicalIntervals_lower_one sign
  have hupperTwo : ∀ sign, I.upper sign ≤ (2 : Real) := by
    intro sign
    cases sign <;>
      norm_num [I,
        bankPaperCanonicalSectionNinePostHeightPhysicalIntervals]
  have HP87uniform :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87
      I 2 0 G
  unfold
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
    at HP87uniform
  obtain ⟨meshTol, hmeshTol, W0, HP87width⟩ :=
    HP87uniform hlowerOne hupperTwo
  refine ⟨W0, ?_⟩
  intro W hW0 hTwoW hprefix _hMertens hMoment
    r0 deltaStar _hr0one hr0three hdeltaStar Hcharge
  have hcPos : 0 < c :=
    (show (0 : Real) < C0 by norm_num [C0]).trans hc
  have hWpos : 0 < W := by omega
  obtain ⟨Ntail, F, hterminal⟩ :=
    exists_bankPaperCanonicalGuardedTailFamily_of_combinedChargeTerminalAtDepth
      Hcharge

  /- The protected and active pieces are a fixed positive half-budget split.
  The multiplicity is then selected by the Archimedean property. -/
  let betaPiece : Real :=
    (c / roughHeadDensity W) / 4
  let betaProt : Real := betaPiece
  let betaAct : Real := betaPiece
  have hHeadDensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hBetaScale : 0 < c / roughHeadDensity W :=
    div_pos hcPos hHeadDensity
  have hbetaPiece : 0 < betaPiece := by
    dsimp only [betaPiece]
    positivity
  have hbetaProt : 0 < betaProt := by
    simpa only [betaProt] using hbetaPiece
  have hbetaAct : 0 < betaAct := by
    simpa only [betaAct] using hbetaPiece
  have hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W := by
    dsimp only [betaProt, betaAct, betaPiece]
    linarith
  obtain ⟨K0, hK0⟩ :=
    exists_nat_gt (1 / roughHeadDensity W)
  have hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real)) := by
    calc
      1 / roughHeadDensity W ≤ (K0 : Real) := hK0.le
      _ ≤ (((K0 + 1 : Nat) : Real)) := by norm_num

  have HpreMeshSource :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshEventualCoherentBridgeSourceObligation
      hc hdeltaStar.1 hWpos hbetaProt.le hbetaAct hbetaUpper hKlarge
        hprefix F hterminal
  dsimp only at HpreMeshSource
  obtain
      ⟨E, sourceCellMargin, postMargin, Cmass, sourceDensity,
        logY, Lambda0, mFrozen, hE, hsourceCellMargin,
        hpostMargin, hphysicalEtaFloor, hpostCellMargin,
        hCmass, hsourceDensity, hlogY, HledgerRaw, HsourceRaw⟩ :=
    HpreMeshSource

  let P := primesUpTo W
  let hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    simpa only [P] using
      bankPaperCanonicalSectionNinePostHeight_primesUpTo_prime W p hp
  let Patterns : PaperHeadSimplex.Tag P → Pattern :=
    PaperHeadSimplex.pattern P hprime E
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass
      W (K0 + 1) betaAct deltaStar
  let physicalEtaFloor : Real :=
    bankPaperCanonicalSectionNinePostHeightPhysicalEta / 2
  let postCellMargin : Real :=
    postMargin *
      (physicalEtaFloor /
        PhysicalInterpolationTarget.physicalSpan I)
  let qMass : Nat → Real :=
    bankPaperCanonicalSmoothFinalActiveMassFamily
      bankPaperCanonicalSectionNinePostHeightPhysicalMu
      logY Lambda0 mFrozen qTilde
  have Hledger :
      BankPaperCanonicalSectionEightAnalyticLedger
        (fun n =>
          bankPaperCanonicalRawSmoothBaseMass W n
            (upperTailLength c n) (K0 + 1) betaAct)
        qTilde
        (bankPaperCanonicalSmoothA0Family
          logY Lambda0 mFrozen qTilde) := by
    simpa only [qTilde] using HledgerRaw
  have Hsource :
      ∀ {delta eta : Real}
          (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta),
        ∃ B : Nat → BridgeData (PaperHeadSimplex.Tag P)
            (BankPaperCanonicalExponentBand M),
          BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
            P Patterns I 2 0 G (c := c) depth W K0 E Ntail F
            deltaStar betaProt betaAct
            bankPaperCanonicalSectionNinePostHeightPhysicalMu
            sourceCellMargin postMargin physicalEtaFloor postCellMargin
            Cmass sourceDensity logY Lambda0 mFrozen qTilde
            M hdelta B := by
    intro delta eta M hdelta
    obtain ⟨B, HsourceM⟩ := HsourceRaw M hdelta
    refine ⟨B, ?_⟩
    simpa only [
      P, hprime, Patterns, I, G, qTilde, physicalEtaFloor, postCellMargin]
      using HsourceM
  have hqMassOne :
      ∀ᶠ n : Nat in atTop, 1 ≤ qMass n := by
    simpa only [qMass] using
      eventually_one_le_bankPaperCanonicalSectionEight_finalActiveMass
        W (K0 + 1) hcPos hbetaAct
          bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
          logY Lambda0 mFrozen qTilde Hledger
  have hPatterns :
      ∀ h : PaperHeadSimplex.Tag P, ∀ p : Nat,
        p ∈ (Patterns h).primes ↔ p.Prime ∧ p ≤ W := by
    intro h p
    change p ∈ P ↔ p.Prime ∧ p ≤ W
    simpa only [P] using (mem_primesUpTo (B := W) (p := p))
  have hHeadLe :
      ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W := by
    intro h q hq
    exact ((hPatterns h q).mp hq).2

  /- The common ledger selects the public bridge-mass coefficient and the
  mesh-uniform selector before the P87 constants and before the mesh. -/
  have HqMassBigO : qMass =O[atTop] secondOrderScale := by
    simpa only [qMass] using
      bankPaperCanonicalSectionNinePostHeight_finalActiveMass_isBigO
        W (K0 + 1) c betaAct
          bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
          logY Lambda0 mFrozen qTilde Hledger
  obtain ⟨Cq, hCq, HqMassNorm⟩ := HqMassBigO.exists_pos
  have HqMassUpper :
      ∀ᶠ n : Nat in atTop,
        qMass n ≤ Cq * secondOrderScale n := by
    filter_upwards [
      HqMassNorm.bound, eventually_secondOrderScale_pos] with
        n hnorm hscale
    calc
      qMass n ≤ |qMass n| := le_abs_self _
      _ = ‖qMass n‖ := (Real.norm_eq_abs _).symm
      _ ≤ Cq * ‖secondOrderScale n‖ := hnorm
      _ = Cq * secondOrderScale n := by
        rw [Real.norm_eq_abs, abs_of_pos hscale]
  obtain ⟨Cinitial, hCinitial, Hselector⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshPlacedSelectorProvider
      Patterns I 2 0 G (c := c) depth W K0
        deltaStar betaProt betaAct
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        logY Lambda0 mFrozen qTilde Hledger
        hTwoW hHeadLe hcPos hdeltaStar.1.1 hdeltaStar.1.2.1
        hbetaAct hprefix
        bankPaperCanonicalSectionNinePostHeightPhysicalMu_pos
  obtain ⟨radius, hradius, CP87, hCP87, HP87mesh⟩ :=
    HP87width W hW0 qMass hqMassOne Patterns hPatterns
      (c := c) depth K0 deltaStar betaProt betaAct
        postCellMargin Cmass sourceDensity
        hbetaProt.le hCmass.le hsourceDensity hpostCellMargin
        Cinitial hCinitial

  let rho : Real := 21 / 20
  let sigma : Real := betaProt / 2
  let tangentConstant : Real :=
    max 1 ((2 / 9 : Real) * CP87 * Cq)
  have hrho : 1 < rho := by norm_num [rho]
  have hsigma : 0 < sigma := by
    dsimp only [sigma]
    positivity
  have hsigmaProt : sigma ≤ betaProt := by
    dsimp only [sigma]
    linarith
  have htangent : 0 < tangentConstant :=
    zero_lt_one.trans_le (by
      dsimp only [tangentConstant]
      exact le_max_left _ _)
  have hcoefficient :
      (2 / 9 : Real) * CP87 * Cq ≤ tangentConstant := by
    dsimp only [tangentConstant]
    exact le_max_right _ _
  have hCleanDensity :
      0 < tangentPaperCleanListDensity W r0 :=
    tangentPaperCleanListDensity_pos W
      (hr0three.trans (by norm_num))
  let widthChoice : Real :=
    bankPaperCanonicalRatioCellPaperWidthChoice
      (tangentPaperCleanListDensity W r0)
      sigma rho tangentConstant
  have hwidthChoice : 0 < widthChoice := by
    simpa only [widthChoice] using
      bankPaperCanonical_ratioCellPaperWidthChoice_pos
        hCleanDensity hsigma hrho htangent
  let meshChoiceTol : Real :=
    min meshTol widthChoice / 2
  have hmeshChoiceTol : 0 < meshChoiceTol := by
    dsimp only [meshChoiceTol]
    exact div_pos (lt_min hmeshTol hwidthChoice) (by norm_num)
  obtain ⟨Kmesh, Nmesh, hKmesh, hNmesh,
      hdeltaFine, hratioFine, _hcellFine⟩ :=
    SelectedDyadicRegularMesh.exists_fine_mesh
      meshChoiceTol hmeshChoiceTol
  let delta : Real := SelectedDyadicRegularMesh.delta Kmesh
  let eta : Real := SelectedDyadicRegularMesh.ratio Nmesh
  let M : RegularRelativeMesh.Mesh delta eta :=
    SelectedDyadicRegularMesh.mesh Kmesh Nmesh (by omega) hNmesh
  have hdelta : 0 < delta := by
    dsimp only [delta, SelectedDyadicRegularMesh.delta]
    positivity
  have hfine : delta + eta ≤ meshTol := by
    have hsum : delta + eta < 2 * meshChoiceTol := by
      dsimp only [delta, eta]
      linarith
    have hmin : min meshTol widthChoice ≤ meshTol :=
      min_le_left _ _
    dsimp only [meshChoiceTol] at hsum
    linarith
  have hwidth : delta + M.ratio ≤ widthChoice := by
    have hsum : delta + eta < 2 * meshChoiceTol := by
      dsimp only [delta, eta]
      linarith
    have hmin : min meshTol widthChoice ≤ widthChoice :=
      min_le_right _ _
    have hratioM : M.ratio = eta := rfl
    rw [hratioM]
    dsimp only [meshChoiceTol] at hsum
    linarith
  have hPermitted :
      IsPermitted (cMesh := (1 : Real)) M := by
    unfold IsPermitted
    change (1 : Real) * eta ≤ eta
    norm_num
  obtain ⟨B, HsourceM⟩ := Hsource M hdelta
  have HP87M :=
    HP87mesh M hdelta hPermitted hfine
  have Hinput :=
    bankPaperCanonicalSectionNinePostHeight_sourceFirstPreselectedPostHfitInput
      M Patterns I 2 0 G (c := c) depth W K0 E Ntail F
        deltaStar betaProt betaAct
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        sourceCellMargin postMargin physicalEtaFloor postCellMargin
        Cmass sourceDensity logY Lambda0 mFrozen qTilde
        rho sigma Cinitial radius CP87 hdelta B HsourceM
        Hselector HP87M hCinitial hradius hCP87 hcPos hTwoW
        hdeltaStar.1.1 hbetaProt.le hbetaAct hbetaUpper hKlarge
        hCmass.le hsourceDensity hsigma hsigmaProt hMoment
  have Hpublic :=
    eventually_bankPaperCanonicalSectionNinePostHeight_coherentBridgeSourceObligation_publicSync
      P Patterns I 2 0 G (c := c) depth W K0 E Ntail F
        deltaStar betaProt betaAct
        bankPaperCanonicalSectionNinePostHeightPhysicalMu
        sourceCellMargin postMargin physicalEtaFloor postCellMargin
        Cmass sourceDensity logY Lambda0 mFrozen qTilde
        M hdelta B HsourceM
  have Hsync :
      ∀ᶠ n : Nat in atTop,
        (B n).sampleData.n = n ∧
          (B n).sampleData.W = W :=
    Hpublic.mono fun _ hn => ⟨hn.1, hn.2.1⟩
  have HBqUpper :
      ∀ᶠ n : Nat in atTop,
        (B n).q ≤ Cq * secondOrderScale n := by
    filter_upwards [Hpublic, HqMassUpper] with n hpublic hupper
    calc
      (B n).q = qMass n := by
        simpa only [qMass] using hpublic.2.2
      _ ≤ Cq * secondOrderScale n := hupper

  unfold
    BankPaperCanonicalSectionNineTopFrozenSynchronizedAnalyticCompletion
  refine
    ⟨delta, eta, M, P, B, K0, tangentConstant, sigma,
      CP87, Cq, hdelta, htangent, hsigma, ?_, hCP87,
      hcoefficient, Hsync, HBqUpper, ?_⟩
  · simpa only [widthChoice, rho] using hwidth
  · simpa only [rho] using Hinput

end BankPaperRealization

end

end Erdos390.WholePaper
