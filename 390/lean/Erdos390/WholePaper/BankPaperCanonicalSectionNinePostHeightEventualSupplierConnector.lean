import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacedSelectorDeficitRateConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightAnalyticLedgerReduction
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenRoundedSourceStateEventualConnector
import Erdos390.WholePaper.BankPaperCanonicalActualMomentReadyEventually
import Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure
import Erdos390.WholePaper.BankPaperCanonicalPostHfitBalancedAlphaEventually
import Erdos390.Full.PaperProposition87ActiveMassTransport

/-!
# Honest reduction boundary for the fresh Section 9 post-height bridge

This file deliberately stops before the synchronized analytic completion.
It exports three narrower layers:

* the uniform guarded zero-cell valuation estimate which was previously
  buried inside the placement proof;
* the genuinely missing post-height target/source producer obligation; and
* a finite local-input reduction which packages already-produced analytic
  fields without calling that package a completed eventual supplier.

The selector constant is chosen by
`exists_eventually_bankPaperCanonicalSectionNinePostHeightPlacedSelector_deficit_paperRate`
before Proposition 8.7 chooses its radius and `Cpost`.  In particular, no
supplier is asked to work for every possible later `Cinitial`.

Every family-level definition below uses one
`BankPaperCanonicalGuardedTailFamily`, hence one realization and guarded
certificate at a given index.  The public bridge is always the literal
fresh bridge `J.postHeightBridge`; no legacy symmetric-height equality
`q = q0` occurs.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.DickmanBasic
open Erdos390.Full.FiniteProbability
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperPrimePowerChamberError
open Erdos390.Full.PaperRawTiltedValuationMeanRows
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.RegularRelativeMesh
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Uniform zero-cell valuation means -/

/-- Uniform paper-rate upper bound for both guarded zero-cell valuation
means.  This is the direct one-sided consequence of the canonical guarded
cell profile estimate used by the Section 9 placed-selector theorem. -/
theorem
    exists_uniform_bridge_guardedZeroCell_valuation_mean_paperRate
    {P : Finset Nat}
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    (W : Nat) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (Patterns h).primes, q ≤ W) :
    ∃ Azero : Real, 0 < Azero ∧ ∃ N₀ : Nat,
      ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
        (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        N₀ ≤ B.sampleData.n → B.sampleData.W = W →
        (hsep : physicalBound (I.upper .minus) B.sampleData.n <
          physicalBound (I.lower .plus) B.sampleData.n) →
        (hremaining : ∀ cell : Cell (PaperHeadSimplex.Tag P),
          (rawCell Patterns I B.sampleData.n cell \
            (G B.sampleData.n).guards).Nonempty) →
        B.sampleData =
          canonicalSampleData
            (W := B.sampleData.W) Patterns I
              (G B.sampleData.n) hsep hremaining →
        ∀ p : BandPrime B.sampleData.n B.sampleData.W,
          ∀ sigma : PhysicalSign,
            (B.guardedCellProbability (none, sigma)).expect
                (fun m ↦ valuation p.1 (m : Nat)) ≤
              Azero / (p.1 : Real) := by
  obtain ⟨Ccell, hCcell, Ncell, hcellProfile⟩ :=
    exists_uniform_bridge_guardedCell_valuation_mean_profiles_paperRate
      Patterns I Cprom Cbank G W hW hHeadLe
  let Amain : Real := 6 / rho DickmanBasic.U
  let Azero : Real := Amain + Ccell
  have hAmain : 0 < Amain := by
    dsimp only [Amain]
    exact div_pos (by norm_num) DickmanBasic.rho_U_pos
  have hAzero : 0 < Azero := by
    dsimp only [Azero]
    exact add_pos hAmain hCcell
  have hLtendsto : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogEvent : ∀ᶠ n : Nat in atTop, 1 ≤ L n :=
    hLtendsto.eventually (eventually_ge_atTop 1)
  obtain ⟨Nlog, hNlog⟩ := Filter.eventually_atTop.mp hlogEvent
  refine ⟨Azero, hAzero, max 2 (max Ncell Nlog), ?_⟩
  intro Band _instBand _instBandDec B hN hBW hsep hremaining
    hcanonical p sigma
  have hn : 1 < B.sampleData.n := by omega
  have hNcell : Ncell ≤ B.sampleData.n := by omega
  have hNlogBound : Nlog ≤ B.sampleData.n := by omega
  have hp := prime_of_mem_primeBand p.2
  have hpR : 0 < (p.1 : Real) := by exact_mod_cast hp.pos
  have hLone : 1 ≤ B.L := by
    simpa only [BridgeData.L] using
      hNlog B.sampleData.n hNlogBound
  have hcellRaw :=
    hcellProfile B hNcell hBW hsep hremaining hcanonical p
  let Kcut := Nat.log p.1 (yNat B.sampleData.n ^ 4)
  let mainSum := ∑ k ∈ positiveExponents Kcut,
    paperDivisibilityMain B.sampleData.n (p.1 ^ k)
  have hpY : p.1 ≤ yNat B.sampleData.n :=
    le_yNat_of_mem_primeBand p.2
  have hY4pos : 0 < yNat B.sampleData.n ^ 4 :=
    pow_pos (hp.pos.trans_le hpY) 4
  have hpK : p.1 ^ Kcut ≤ yNat B.sampleData.n ^ 4 := by
    dsimp only [Kcut]
    exact Nat.pow_log_le_self p.1 hY4pos.ne'
  have hmainTerm (k : Nat) (hk : k ∈ positiveExponents Kcut) :
      0 ≤ paperDivisibilityMain B.sampleData.n (p.1 ^ k) ∧
        paperDivisibilityMain B.sampleData.n (p.1 ^ k) ≤
          (1 / rho DickmanBasic.U) * singleWeight p.1 k := by
    have hkLe : k ≤ Kcut := (mem_positiveExponents.mp hk).2
    have hpk :
        p.1 ^ k ≤ yNat B.sampleData.n ^ 4 :=
      (Nat.pow_le_pow_right hp.pos hkLe).trans hpK
    have hraw :=
      paperDivisibilityMain_nonneg_le hn (pow_pos hp.pos k) hpk
    refine ⟨hraw.1, ?_⟩
    have habs :=
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp hpk
    simpa only [abs_of_nonneg hraw.1] using habs
  have hweight :
      (∑ k ∈ positiveExponents Kcut, singleWeight p.1 k) ≤
        6 / (p.1 : Real) :=
    sum_singleWeight_positiveExponents_le hp.two_le
  have hmainUpper : mainSum ≤ Amain / (p.1 : Real) := by
    calc
      mainSum ≤
          ∑ k ∈ positiveExponents Kcut,
            (1 / rho DickmanBasic.U) * singleWeight p.1 k := by
        dsimp only [mainSum]
        exact Finset.sum_le_sum fun k hk => (hmainTerm k hk).2
      _ = (1 / rho DickmanBasic.U) *
          ∑ k ∈ positiveExponents Kcut, singleWeight p.1 k := by
        rw [Finset.mul_sum]
      _ ≤ (1 / rho DickmanBasic.U) * (6 / (p.1 : Real)) := by
        exact mul_le_mul_of_nonneg_left hweight
          (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
      _ = Amain / (p.1 : Real) := by
        dsimp only [Amain]
        field_simp [hpR.ne', DickmanBasic.rho_U_pos.ne']
  let mean :=
    (B.guardedCellProbability (none, sigma)).expect
      (fun m ↦ valuation p.1 (m : Nat))
  have hprofile :
      |mean - mainSum| ≤ Ccell / ((p.1 : Real) * B.L) := by
    simpa only [mean, Kcut, mainSum] using
      hcellRaw (none, sigma)
  have herror :
      Ccell / ((p.1 : Real) * B.L) ≤
        Ccell / (p.1 : Real) := by
    apply div_le_div_of_nonneg_left hCcell.le hpR
    calc
      (p.1 : Real) = (p.1 : Real) * 1 := by ring
      _ ≤ (p.1 : Real) * B.L :=
        mul_le_mul_of_nonneg_left hLone hpR.le
  have hmeanLe :
      mean ≤ mainSum + Ccell / ((p.1 : Real) * B.L) := by
    have hself : mean - mainSum ≤ |mean - mainSum| :=
      le_abs_self _
    linarith
  calc
    mean ≤ mainSum + Ccell / ((p.1 : Real) * B.L) := hmeanLe
    _ ≤ Amain / (p.1 : Real) + Ccell / (p.1 : Real) :=
      add_le_add hmainUpper herror
    _ = Azero / (p.1 : Real) := by
      dsimp only [Azero]
      ring

/-! ## The genuine producer obligation -/

/-- Primitive paper inputs still missing after all currently exported
eventual estimates are accounted for.

The first group is the uniform target/source construction:

* fixed positive margins for the pre-height source target and the fresh
  post-height target;
* one fixed positive head-simplex exponent;
* synchronization of the literal frozen mass, `qTilde`, and final active
  mass with the Section 8 analytic families; and
* the three primitive rounded-source residual facts.

The balanced-alpha box is not a field: it is supplied by
`eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc`.  There is no
dependent-input, Post-Hfit-input, final-event, or implementation-rate field
in this record. -/
structure BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (E : Nat)
    (deltaStar mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) where
  exponent_pos : 0 < E
  exponent_sync : J.exponent = E
  sourceMarginFloor_pos : 0 < sourceMarginFloor
  headMarginFloor_pos : 0 < headMarginFloor
  physicalEtaFloor_pos : 0 < physicalEtaFloor
  postMarginFloor_pos : 0 < postMarginFloor
  sourceTarget_margin :
    sourceMarginFloor ≤ J.Tsource.cellMassMargin
  headMargin_uniform :
    headMarginFloor ≤ J.targetInputs.headMargin
  physicalEta_uniform :
    physicalEtaFloor ≤ J.targetInputs.physicalEta
  postHeightTarget_margin :
    postMarginFloor ≤ J.postHeightTarget.cellMassMargin
  qTilde_family :
    J.qTilde = qTilde Bsource.sampleData.n
  mFrozen_family :
    mFrozen Bsource.sampleData.n =
      bankPaperCanonicalTopFrozenSmoothFrozenMass (K := K0 + 1)
        J.postHeightBridge R certificate deltaStar J.betaProt J.alpha
  finalActiveMass_family :
    J.qn =
      bankPaperCanonicalSmoothFinalActiveMassFamily
        mu logY Lambda0 mFrozen qTilde Bsource.sampleData.n
  sourceResidual :
    BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
      (K := K0 + 1) J.postHeightBridge R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        J.Tsource deltaStar J.betaProt J.alpha J.beta J.qTilde

/-- The explicit family-level obligation to construct the fresh bridge and
its source package from one guarded-tail family and the corresponding
capacity witnesses.

This is intentionally named an obligation, not a supplier theorem.  The
existential `J` contains the primitive
`BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs`; the
existential `S` contains the source state obtained after applying the
conditional rounded-source theorem to `Hgap.sourceResidual`.  Their
existence has not yet been proved in the repository.

All already-exported alpha, rate, moment, frozen-ledger, P87, large-`L`,
and nonsmooth conclusions are absent. -/
def BankPaperCanonicalSectionNinePostHeightEventualCoherentBridgeSourceObligation
    (P : Finset Nat)
    (Patterns : PaperHeadSimplex.Tag P → Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : ∀ n, Ledger n Cprom Cbank)
    {c : Real} (depth W K0 E Ntail : Nat)
    (F : BankPaperCanonicalGuardedTailFamily c depth Ntail)
    (deltaStar betaProt betaAct mu sourceMarginFloor headMarginFloor
      physicalEtaFloor postMarginFloor Cmass density : Real)
    (logY Lambda0 mFrozen qTilde : Nat → Real)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    (hdelta : 0 < delta)
    (B : Nat → BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M)) : Prop :=
  ∀ᶠ n : Nat in atTop,
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
                    S.density = density

/-!
## Exact dependent-field census

For `BankPaperCanonicalSectionNinePostHeightDependentInputsAt`, the current
producer map is:

* the physical part of the fresh target interior:
  `bankPaperCanonicalSectionEight_physicalMeanError_isBigO` after the
  Section 8 family identities are synchronized; the unproved part of the
  coherent target constructor is the fixed head-simplex reserve and its
  assembly with that physical interval;
* `Cinitial`, its nonnegativity, and `selectorDeficit`: the uniform placed
  selector theorem, using the zero-cell theorem exported above together
  with the Section 8 `d` and final-mass rates;
* the balanced-alpha box: the standalone eventual balanced-alpha theorem;
* `Cfixed`, `roundedFrozenLedger`, and `fixedRoom`: choose
  `Cfixed = betaProt + Cactive`; additive-placement frozen invariance and
  post-height rounded-source invariance give the pointwise ledger;
* `primeDeviation`: eventual canonical `MomentReady` followed by
  `actual_L1_bound_of_ready`;
* `radius` and `localP87`: varying-active-mass canonical Proposition 8.7,
  with `Ctarget = 7 * Cinitial`, `Cmass = 1`, and
  `Cactive = S.Cmass / S.density`;
* `cellIndex`: the literal `bankPaperCanonicalRatioCellIndex`;
* `W_large`: the fixed choice `2 ≤ W`;
* `sigma_nonneg` and `sigma_le_betaProt`: the fixed parameter choice;
* `largeL`: `eventually_canonical_exponential_slack_le_L`, with `sigma`
  absorbed into the fixed term; and
* `nonsmooth`: `eventually_roughCanonicalBalancedNonsmoothBounds`.

The target envelope, placed frozen ledger, active ledger, active-seed bound,
and protected reserve are not fields of the dependent record: the existing
post-height local connector constructs them after the above data are
installed.

Thus the only producer gap is the uniform coherent target/source
construction recorded in
`BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt`.
-/

/-! ## Non-final finite local-input reduction -/

/-- What the present file is allowed to conclude at one index: the
balanced-alpha box and a dependent local-input package whose cell index is
the literal ratio-cell index from the same mesh witness.

This is strictly below the public Post-Hfit input and below every eventual
or completion proposition. -/
def BankPaperCanonicalSectionNinePostHeightLocalInputReductionAt
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    {c : Real} {depth K0 : Nat}
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (deltaStar rho sigma Cpost : Real)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J) : Prop :=
  (0 ≤ J.alpha ∧ J.alpha ≤ 1) ∧
    ∃ A : BankPaperCanonicalSectionNinePostHeightDependentInputsAt
        M Bsource R certificate I deltaStar sigma Cpost hdelta J S,
      A.cellIndex =
        bankPaperCanonicalRatioCellIndex M hdelta
          J.postHeightBridge.n_gt_one J.hW J.scaleSeparation rho

/-- Package the outputs of the already-exported finite/eventual chains into
the non-final local reduction.

The hypotheses after `Hgap` are not genuine gap fields:

* `hselector` is the selected output of the placed-selector rate theorem;
* `hroundedFrozenLedger` is the additive-placement frozen invariance chain;
* `hprimeDeviation` is `actualMomentReady` plus
  `MomentReady.actual_L1_bound_of_ready`;
* `hlocalP87` is the varying-active-mass canonical P87 output chosen after
  `Cinitial`;
* `hlargeL` and `hnonsmooth` are the exported exponential-slack and
  balanced-nonsmooth events.

They remain separate arguments here because eventual intersection is a
family-level operation, while the primitive producer obligation above
is still open.  The signature fixes `Cinitial`, then `radius` and `Cpost`,
before the later mesh, matching the canonical varying-mass P87 order. -/
theorem
    bankPaperCanonicalSectionNinePostHeightLocalInputReduction_of_exportedFields
    {c : Real} {depth K0 E : Nat}
    {mu sourceMarginFloor headMarginFloor physicalEtaFloor
      postMarginFloor : Real}
    {logY Lambda0 mFrozen qTilde : Nat → Real}
    (deltaStar rho sigma Cinitial : Real)
    (hCinitial : 0 ≤ Cinitial)
    (radius : NNReal)
    (Cpost : Real)
    {delta eta : Real} (M : RegularRelativeMesh.Mesh delta eta)
    {P : Finset Nat}
    (Bsource : BridgeData (PaperHeadSimplex.Tag P)
      (BankPaperCanonicalExponentBand M))
    (R : BankPaperRealization Bsource.sampleData.n
      (upperEndpoint Bsource.sampleData.n
        (upperTailLength c Bsource.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth
      Bsource.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (I : PhysicalIntervals)
    (hdelta : 0 < delta)
    (J : BankPaperCanonicalSectionNinePostHeightBridgeInputsAt
      (K0 := K0) M Bsource R certificate I deltaStar hdelta)
    (S : BankPaperCanonicalSectionNinePostHeightSourceInputsAt
      M Bsource R certificate I deltaStar hdelta J)
    (_Hgap : BankPaperCanonicalSectionNinePostHeightPrimitiveGapsAt
      M Bsource R certificate I E deltaStar mu sourceMarginFloor
        headMarginFloor physicalEtaFloor postMarginFloor
        logY Lambda0 mFrozen qTilde hdelta J S)
    (halpha : 0 ≤ J.alpha ∧ J.alpha ≤ 1)
    (hselector :
      ∀ p ∈ primeBand J.postHeightBridge.sampleData.n
          J.postHeightBridge.sampleData.W,
        abs (bankPaperCanonicalSelectorValuationDeficit
          R certificate (R.paperFixedExceptionalFactors deltaStar)
            (R.roughCanonicalGuardedCandidateSet certificate
              deltaStar (K0 + 1))
            J.placedPreSelector p) ≤
          Cinitial * J.postHeightBridge.q /
            ((p : Real) * J.postHeightBridge.L))
    (hroundedFrozenLedger :
      ∀ m : J.postHeightBridge.sampleData.Sample,
        BridgeData.frozenAmbientWeight
            (bankPaperCanonicalActualFrozenValue
              (candidates :=
                R.roughCanonicalGuardedCandidateSet certificate
                  deltaStar (K0 + 1)))
            (bankPaperCanonicalActualFrozenWeight
              J.postHeightBridge.sampleData
              (R.roughCanonicalGuardedCandidateSet certificate
                deltaStar (K0 + 1))
              J.roundedSourceSelector J.roundedActiveSeed)
            (J.postHeightBridge.sampleData.value m) ≤
          (J.betaProt + S.Cmass / S.density) /
            J.postHeightBridge.L)
    (hprimeDeviation :
      J.postHeightBridge.primeDeviationL1 ≤
        7 * J.postHeightBridge.w)
    (hlocalP87 :
      ∀ (Delta : BankPaperCanonicalExponentBand M → Real),
        J.postHeightBridge.HasTargetEnvelopes (7 * Cinitial) Delta →
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
          (∀ j, Delta j =
            J.postHeightBridge.markedBandResidual markedTarget 0 j) →
          ∀ {Fixed : Type} [Fintype Fixed],
            ∀ (fixedValue : Fixed → Nat) (fixedWeight : Fixed → Real)
              (quota : Int),
              (quota : Real) = (∑ f, fixedWeight f) +
                J.postHeightBridge.q →
              J.postHeightBridge.sampleData.HeadPatternsSeparated →
              (∀ x,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight x ∈
                  Icc (0 : Real) 1) →
              (∀ m : J.postHeightBridge.sampleData.Sample,
                BridgeData.frozenAmbientWeight fixedValue fixedWeight
                    (J.postHeightBridge.sampleData.value m) ≤
                  (J.betaProt + S.Cmass / S.density) /
                    J.postHeightBridge.L) →
              (∀ m : J.postHeightBridge.sampleData.Sample,
                J.postHeightBridge.baseline.baseWeight m ≤
                  (S.Cmass / S.density) / J.postHeightBridge.L) →
              J.postHeightBridge.HasPaperProposition87Conclusion
                Delta radius markedTarget N Cpost
                  fixedValue fixedWeight quota)
    (hTwoW : 2 ≤ J.postHeightBridge.sampleData.W)
    (hsigma : 0 < sigma)
    (hsigmaProt : sigma ≤ J.betaProt)
    (hlargeL :
      (J.betaProt + S.Cmass / S.density) +
          Real.exp (2 *
            ((Erdos390.Full.PaperStatisticNorm.valuationLogCoefficient
                  2 J.postHeightBridge.sampleData.W +
              J.postHeightBridge.nuisanceStatisticCoefficient 2) *
                (3 * (radius : Real)))) *
            (S.Cmass / S.density) + sigma ≤
        J.postHeightBridge.L)
    (hnonsmooth :
      ∀ label,
        RoughCanonicalActiveNonexceptionalLabel
            J.postHeightBridge.sampleData.n deltaStar label →
          sigma / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            J.beta / J.postHeightBridge.L ∧
          J.beta / J.postHeightBridge.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar
                J.postHeightBridge.sampleData.W (K0 + 1) label
                  J.alpha J.beta J.postHeightBridge.L| ≤
            1 - sigma / J.postHeightBridge.L) :
    BankPaperCanonicalSectionNinePostHeightLocalInputReductionAt
      M Bsource R certificate I deltaStar rho sigma Cpost hdelta J S := by
  let A :
      BankPaperCanonicalSectionNinePostHeightDependentInputsAt
        M Bsource R certificate I deltaStar sigma Cpost hdelta J S :=
    { Cinitial := Cinitial
      Cfixed := J.betaProt + S.Cmass / S.density
      Cinitial_nonneg := hCinitial
      selectorDeficit := hselector
      roundedFrozenLedger := by
        exact hroundedFrozenLedger
      primeDeviation := hprimeDeviation
      radius := radius
      localP87 := by
        exact hlocalP87
      cellIndex :=
        bankPaperCanonicalRatioCellIndex M hdelta
          J.postHeightBridge.n_gt_one J.hW J.scaleSeparation rho
      fixedRoom := le_rfl
      W_large := by omega
      sigma_nonneg := hsigma.le
      sigma_le_betaProt := hsigmaProt
      largeL := by
        exact hlargeL
      nonsmooth := hnonsmooth }
  exact ⟨halpha, ⟨A, rfl⟩⟩

end BankPaperRealization

end

end Erdos390.WholePaper
