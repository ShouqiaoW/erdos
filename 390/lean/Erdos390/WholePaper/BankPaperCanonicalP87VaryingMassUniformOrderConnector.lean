import Erdos390.Full.PaperProposition87ActiveMassTransport

/-!
# Uniform paper order for varying-mass canonical Proposition 8.7

The varying-active-mass Proposition 8.7 theorem is uniform in the mass
family once that family is eventually at least one.  Its original public
statement, however, takes the family before exposing the mesh threshold and
the prime cutoff, so that logical statement does not record the uniform
dependency order.

This connector exposes `meshTol` and `W0` first.  Only after a width
`W ≥ W0` has been selected is the varying family `qMass` introduced.  The
proof uses the mass-one literal theorem to select the two uniform cutoffs,
then repeats the normalized-law transport used by
`canonical_proposition87_varyingActiveMassLiteralBandBalance`.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperBridgeFit.BridgeData
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperPermittedRegularMesh
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh

noncomputable section

/-- Quantifier-uniform form of the varying-active-mass literal Proposition
8.7 statement.  The mesh tolerance and prime cutoff are selected before
both the final width and the varying active-mass family. -/
def BankPaperCanonicalP87VaryingMassUniformOrderStatement
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : ∀ n, Ledger n Cprom Cbank) : Prop :=
  0 < cMesh →
  1 ≤ U →
  (∀ sigma, 1 ≤ I.lower sigma) →
  (∀ sigma, I.upper sigma ≤ U) →
  ∃ meshTol : Real, 0 < meshTol ∧
  ∃ W0 : Nat, ∀ W : Nat, W0 ≤ W →
    ∀ (qMass : Nat → Real),
      (∀ᶠ n : Nat in atTop, 1 ≤ qMass n) →
    ∀ {Head : Type*} [Fintype Head] [DecidableEq Head] [Nonempty Head]
      (Phead : Head → HeadPattern.Pattern),
    (∀ h : Head, ∀ p : Nat,
      p ∈ (Phead h).primes ↔ p.Prime ∧ p ≤ W) →
    ∀ (Ctarget Cinitial Cmass Cfixed Cactive marginFloor : Real),
      0 ≤ Ctarget → 0 ≤ Cinitial → 0 ≤ Cmass →
      0 ≤ Cfixed → 0 ≤ Cactive → 0 < marginFloor →
    ∃ radius : NNReal, 0 < (radius : Real) ∧
    ∃ Cpost : Real, 0 ≤ Cpost ∧
    ∀ {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
      (hdelta : 0 < delta)
      (_hPermitted : IsPermitted (cMesh := cMesh) M),
      delta + eta ≤ meshTol →
      ∀ᶠ n : Nat in atTop,
        ∀ (B : BridgeData Head (Fin (M.cellCount + 1))),
          B.sampleData.n = n → B.sampleData.W = W →
          ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
            (hremaining : ∀ c : Cell Head,
              (rawCell Phead I B.sampleData.n c \
                (ledger B.sampleData.n).guards).Nonempty),
            (hcanonical : B.sampleData = canonicalSampleData
              (W := B.sampleData.W) Phead I (ledger B.sampleData.n)
                hsep hremaining) →
            (hpartition : ∃ (hWne : B.sampleData.W ≠ 0)
                (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition =
                RegularMeshPrimeCutoffs.Mesh.canonicalPartition
                  M hdelta B.n_gt_one hWne S) →
            (hscale : B.w = delta + eta) →
            ∀ (T : BarycentricTarget B.sampleData)
              (hq : 0 < qMass B.sampleData.n),
              marginFloor ≤ T.cellMassMargin →
              B.baseline =
                T.activeMassBaseline (qMass B.sampleData.n) hq →
            ∀ (Delta : Fin (M.cellCount + 1) → Real),
              B.HasTargetEnvelopes Ctarget Delta →
            ∀ (markedTarget : Nat → Real) (N : Real),
              0 ≤ N →
              B.q ≤ Cmass * N →
              (∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
                abs (markedTarget p -
                  B.paperMoment (B.markedValuation p) 0) ≤
                    Cinitial * N / ((p : Real) * B.L)) →
              (∀ j,
                Delta j = B.markedBandResidual markedTarget 0 j) →
            ∀ {Fixed : Type*} [Fintype Fixed]
              (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
              (quota : Int),
              (quota : Real) = (∑ f, fixedWeight f) + B.q →
              B.sampleData.HeadPatternsSeparated →
              (∀ x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Set.Icc (0 : Real) 1) →
              (∀ m : B.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                  (B.sampleData.value m) ≤ Cfixed / B.L) →
              (∀ m : B.sampleData.Sample,
                B.baseline.baseWeight m ≤ Cactive / B.L) →
              B.HasPaperProposition87Conclusion
                Delta radius markedTarget N Cpost
                  fixedValue fixedWeight quota

set_option maxHeartbeats 4000000 in
/-- Varying-active-mass canonical Proposition 8.7 with its mesh tolerance
and prime cutoff selected uniformly before the final width and mass family.
-/
theorem
    bankPaperCanonicalP87VaryingActiveMassLiteralBandBalance_uniformOrder
    (cMesh : Real)
    (I : PhysicalIntervals) (U : Real)
    (Cprom Cbank : Nat) (ledger : ∀ n, Ledger n Cprom Cbank) :
    BankPaperCanonicalP87VaryingMassUniformOrderStatement
      cMesh I U Cprom Cbank ledger := by
  have hold := canonical_proposition87_literalBandBalance
    cMesh I U Cprom Cbank ledger
  unfold CanonicalProposition87LiteralBalanceStatement at hold
  unfold BankPaperCanonicalP87VaryingMassUniformOrderStatement
  intro hcMesh hU hlowerOne hupperU
  obtain ⟨meshTol, hmeshTol, Wold, hWold⟩ :=
    hold hcMesh hU hlowerOne hupperU
  let W0 : Nat := max Wold 2
  refine ⟨meshTol, hmeshTol, W0, ?_⟩
  intro W hW qMass hqOne Head _instHeadFintype _instHeadDecidable
    _instHeadNonempty Phead hPhead
    Ctarget Cinitial Cmass Cfixed Cactive marginFloor
    hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  have hWoldLe : Wold ≤ W := (le_max_left Wold 2).trans hW
  have hWtwo : 2 ≤ W := (le_max_right Wold 2).trans hW
  obtain ⟨radius, hradius, Cpost, hCpost, hMeshOld⟩ :=
    hWold W hWoldLe Phead hPhead
      Ctarget Cinitial Cmass Cfixed Cactive marginFloor
      hCtarget hCinitial hCmass hCfixed hCactive hmarginFloor
  refine ⟨radius, hradius, Cpost, hCpost, ?_⟩
  intro delta eta M hdelta hPermitted hfine
  have hOldN := hMeshOld M hdelta hPermitted hfine
  have hSlackN := eventually_canonical_exponential_slack_le_L
    (Head := Head) (Band := Fin (M.cellCount + 1))
    U hU W radius Cfixed Cactive hCactive
  filter_upwards [hOldN, hSlackN, hqOne] with n hnOld hslack hqOneN
  intro B hBn hBW hsep hremaining hcanonical hpartition hscale
    T hq hTmargin hbaseline Delta henv markedTarget N hN hMassBound
    hinitial hDelta Fixed _instFixedFintype fixedValue fixedWeight
    quota hquota hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
  let q : Real := qMass B.sampleData.n
  let B0 := B.normalizedLawCompanion T
  have hqOneB : 1 ≤ q := by
    dsimp only [q]
    rw [hBn]
    exact hqOneN
  have hqPos : 0 < q := lt_of_lt_of_le zero_lt_one hqOneB
  have hqProof : hq = hqPos := Subsingleton.elim _ _
  have hbaseline' : B.baseline = T.activeMassBaseline q hqPos := by
    simpa only [q, hqProof] using hbaseline
  have hBWlarge : 1 < B.sampleData.W := by
    rw [hBW]
    omega
  have hhiIntervals : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhiU : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound U B.sampleData.n := by
    intro sigma
    rw [hhiIntervals]
    exact FixedFiniteMixtureFullUniform.physicalBound_mono
      (hupperU sigma) B.sampleData.n
  have henv0 := B.hasTargetEnvelopes_normalizedLawCompanion
    T q hqPos hbaseline' Delta henv
  have hN0 : 0 ≤ N / q := div_nonneg hN hqPos.le
  have hqRaw : q ≤ Cmass * N := by
    rw [← B.q_eq_of_baseline_eq_activeMassBaseline
      T q hqPos hbaseline']
    exact hMassBound
  have hqMass0 : B0.q ≤ Cmass * (N / q) := by
    exact B.normalizedLawCompanion_q_le_of_activeMass_bound
      T q hqPos hqRaw
  have hinitial0 := B.normalizedLawCompanion_initialMarkedRate
    T q hqPos hbaseline' markedTarget N Cinitial
      (primeBand B.sampleData.n B.sampleData.W) hinitial
  have hDelta0 : ∀ j,
      Delta j / q = B0.markedBandResidual
        (fun p => markedTarget p / q) 0 j := by
    intro j
    have hres :=
      B.markedBandResidual_eq_activeMass_mul_normalizedLawCompanion
        T q hqPos hbaseline' markedTarget 0 j
    rw [hDelta j, hres]
    field_simp [ne_of_gt hqPos]
    ring
  have hactive0Raw := B.normalizedLawCompanion_baseWeight_le_div_log
    T q hqPos hbaseline' hactiveLedger
  have hCdiv : Cactive / q ≤ Cactive :=
    div_le_self hCactive hqOneB
  have hactive0 : ∀ m : B0.sampleData.Sample,
      B0.baseline.baseWeight m ≤ Cactive / B0.L := by
    intro m
    exact (hactive0Raw m).trans
      (div_le_div_of_nonneg_right hCdiv B.L_pos.le)
  have hfrozen0 : ∀ x : Nat,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) x ∈ Set.Icc (0 : Real) 1 := by
    intro x
    simp [frozenAmbientWeight]
  have hfrozenLedger0 : ∀ m : B0.sampleData.Sample,
      frozenAmbientWeight (fun e : Fin 0 => Fin.elim0 e)
        (fun e : Fin 0 => Fin.elim0 e) (B0.sampleData.value m) ≤
          Cfixed / B0.L := by
    intro m
    simp only [frozenAmbientWeight, Finset.univ_eq_empty,
      Finset.sum_empty]
    exact div_nonneg hCfixed B0.L_pos.le
  have hquota0 : ((1 : Int) : Real) =
      (∑ e : Fin 0, (Fin.elim0 e : Real)) + B0.q := by
    simp [B0, normalizedLawCompanion_q]
  have Hnormalized : B0.HasPaperProposition87Conclusion
      (fun j => Delta j / q) radius (fun p => markedTarget p / q)
      (N / q) Cpost (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 := by
    exact hnOld B0 hBn hBW hsep hremaining
      (by simpa only [B0, normalizedLawCompanion] using hcanonical)
      (by simpa only [B0, normalizedLawCompanion] using hpartition)
      (by simpa only [B0, normalizedLawCompanion] using hscale)
      T hTmargin rfl (fun j => Delta j / q) henv0
      (fun p => markedTarget p / q) (N / q) hN0 hqMass0
      (by simpa only [B0, normalizedLawCompanion] using hinitial0)
      hDelta0 (fun e : Fin 0 => Fin.elim0 e)
      (fun e : Fin 0 => Fin.elim0 e) 1 hquota0
      (by simpa only [B0, normalizedLawCompanion] using hheadSeparated)
      hfrozen0 hfrozenLedger0 hactive0
  exact B.canonical_activeMass_proposition87_of_normalizedLawCompanion
    T q hqPos hbaseline' Delta radius markedTarget N Cpost
    (fun e : Fin 0 => Fin.elim0 e) (fun e : Fin 0 => Fin.elim0 e) 1
    Hnormalized fixedValue fixedWeight quota hquota hU hBWlarge hhiU
    hheadSeparated hfrozenFeasible hfrozenLedger hactiveLedger
    (hslack B hBn hBW)

end

end Erdos390.WholePaper
