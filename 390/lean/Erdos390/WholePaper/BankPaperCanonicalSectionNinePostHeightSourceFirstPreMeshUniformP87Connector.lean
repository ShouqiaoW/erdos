import Erdos390.WholePaper.BankPaperCanonicalP87VaryingMassUniformOrderConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstEventualPostHfitConnector

/-!
# Pre-mesh uniform Proposition 8.7 callback

The fixed-mesh Proposition 8.7 factory records its choices only after a
particular regular mesh has been introduced.  The underlying uniform theorem
is stronger: after the width, varying active-mass family, source constants,
and selector constant have been fixed, it chooses one radius and one
post-adjustment constant which work for every sufficiently fine permitted
mesh.

This file exposes that dependency order directly.  Its conclusion is the
same specialized eventual callback consumed by the source-first post-height
compositor; it introduces no selector or Post-Hfit conclusion.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

namespace BankPaperRealization

/-! ## Pre-mesh uniform adapter -/

/-- Proposition 8.7 in the dependency order required by the final
source-first orchestration.

The tolerance and prime cutoff precede the final width and varying mass
family.  For fixed patterns, source constants, and `Cinitial`, the radius and
`CP87` are then chosen before the eventual callback is specialized to any
particular permitted sufficiently fine mesh. -/
def
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank) : Prop :=
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
      (deltaStar betaProt betaAct postMarginFloor Cmass density : Real),
      0 ≤ betaProt →
      0 ≤ Cmass →
      0 < density →
      0 < postMarginFloor →
    ∀ Cinitial : Real, 0 ≤ Cinitial →
      ∃ radius : NNReal, 0 < (radius : Real) ∧
      ∃ CP87 : Real, 0 ≤ CP87 ∧
        ∀ {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
          (hdelta : 0 < delta)
          (_hPermitted : IsPermitted (cMesh := (1 : Real)) M),
          delta + eta ≤ meshTol →
          BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
            (c := c) M Patterns I Cprom Cbank G depth W K0 deltaStar
              betaProt betaAct postMarginFloor Cmass density qMass
              Cinitial radius CP87 hdelta

set_option maxHeartbeats 4000000 in
/-- Construct the pre-mesh specialized eventual Proposition 8.7 callback
from the uniform-order varying-active-mass theorem. -/
theorem
    exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstPreMeshUniformP87
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank) :
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
      I Cprom Cbank G := by
  unfold
    BankPaperCanonicalSectionNinePostHeightSourceFirstPreMeshUniformP87Statement
  intro hlowerOne hupperTwo
  have hUniform :=
    bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder
      (1 : Real) I (2 : Real) Cprom Cbank G
  unfold BankPaperCanonicalP87VaryingMassUniformOrderStatement at hUniform
  obtain ⟨meshTol, hmeshTol, W0, hUniformW⟩ :=
    hUniform (by norm_num) (by norm_num) hlowerOne hupperTwo
  refine ⟨meshTol, hmeshTol, W0, ?_⟩
  intro W hW qMass hqMassOne P Patterns hPatterns c depth K0
    deltaStar betaProt betaAct postMarginFloor Cmass density
    hbetaProt hCmass hdensity hpostMargin Cinitial hCinitial
  have hCtarget : 0 ≤ 7 * Cinitial :=
    mul_nonneg (by norm_num) hCinitial
  have hCfixed : 0 ≤ betaProt + Cmass / density :=
    add_nonneg hbetaProt (div_nonneg hCmass hdensity.le)
  have hCactive : 0 ≤ Cmass / density :=
    div_nonneg hCmass hdensity.le
  obtain ⟨radius, hradius, CP87, hCP87, hP87⟩ :=
    hUniformW W hW qMass hqMassOne Patterns hPatterns
      (7 * Cinitial) Cinitial (1 : Real)
      (betaProt + Cmass / density) (Cmass / density) postMarginFloor
      hCtarget hCinitial (by norm_num) hCfixed hCactive hpostMargin
  refine ⟨radius, hradius, CP87, hCP87, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  unfold
    BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedEventualLocalP87Callback
  have hP87N := hP87 M hdelta hPermitted hfine
  filter_upwards [hP87N] with n hn
  intro Bsource hBsourceN hBsourceW R certificate J S
    hbetaProtSync hbetaActSync hsep hremaining hcanonical
    hmargin hCmassSync hdensitySync hqSync
  have hJn : J.postHeightBridge.sampleData.n = n := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hBsourceN
  have hJW : J.postHeightBridge.sampleData.W = W := by
    simpa only [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightBridge_sampleData]
      using hBsourceW
  have hqn :
      J.qn = qMass J.postHeightBridge.sampleData.n := by
    calc
      J.qn = J.postHeightBridge.q := J.postHeightBridge_q.symm
      _ = qMass n := hqSync
      _ = qMass J.postHeightBridge.sampleData.n := by rw [hJn]
  have hq : 0 < qMass J.postHeightBridge.sampleData.n := by
    rw [← hqn]
    exact lt_of_lt_of_le zero_lt_one S.qn_one_le
  have hbaseline :
      J.postHeightBridge.baseline =
        J.postHeightTarget.activeMassBaseline
          (qMass J.postHeightBridge.sampleData.n) hq := by
    rw [
      BankPaperCanonicalSectionNinePostHeightBridgeInputsAt.postHeightTarget_eq_scaffoldTarget]
    change
      J.scaffoldTarget.activeMassBaseline J.qn
          J.targetInputs.activeMass_pos =
        J.scaffoldTarget.activeMassBaseline
          (qMass J.postHeightBridge.sampleData.n) hq
    simp only [hqn]
  have hpartition :
      ∃ (hWne : J.postHeightBridge.sampleData.W ≠ 0)
        (Sscale : ScaleSeparation M J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W),
        J.postHeightBridge.partition =
          RegularMeshPrimeCutoffs.Mesh.canonicalPartition
            M hdelta J.postHeightBridge.n_gt_one hWne Sscale := by
    exact
      ⟨J.hW, J.scaleSeparation,
        J.postHeightBridge_partition⟩
  unfold
    BankPaperCanonicalSectionNinePostHeightSourceFirstSpecializedLocalP87At
  intro Delta henv markedTarget N hN hMass hinitial hDelta
    Fixed instFixed fixedValue fixedWeight quota hquota
    hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  exact
    hn J.postHeightBridge hJn hJW hsep hremaining hcanonical
      hpartition (by rfl) J.postHeightTarget hq hmargin hbaseline
      Delta henv markedTarget N hN hMass hinitial hDelta
      fixedValue fixedWeight quota hquota hheadSeparated hfrozenFeasible
      (by
        simpa only [hbetaProtSync, hCmassSync, hdensitySync] using
          hfrozenLedger)
      (by
        simpa only [hCmassSync, hdensitySync] using hactiveLedger)

end BankPaperRealization

end

end Erdos390.WholePaper
