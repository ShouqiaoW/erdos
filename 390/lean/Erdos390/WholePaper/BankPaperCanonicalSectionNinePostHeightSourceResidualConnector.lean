import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightLocalInputConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionNineActiveLedgerConnector
import Erdos390.WholePaper.BankPaperCanonicalPostHfitBalancedAlphaEventually
import Erdos390.WholePaper.BankPaperCanonicalNonsmoothSlackClosure
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenSmoothFeasibilityConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenChargedRowsConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenSelectorTailSupportReductionConnector
import Erdos390.WholePaper.BankPaperCanonicalSmoothSourceGuardedSharpRoundedValuationRateConnector

/-!
# The coherent post-height source residual

This file closes the three primitive residual fields for the literal
pre-rounding frozen-top source, once the source target has been honestly
constructed from paper head and physical data.

The target interface is deliberately transparent.  It asks for the exact
equalities

* `Tsource = B.barycentricTargetOfPaperData ... Rhead Kphysical`, and
* `qTilde = Rhead.activeMass`,

together with the certificate-derived head-target compatibility.  It does
not store feasibility, charged rows, selector support, a source state, or
the residual conclusion in an input structure.

All remaining inputs are primitive geometry and synchronization facts.
The coordinate capacity is derived from the guarded canonical cell-density
theorem and the literal guarded smooth-mass estimate.  Nonsmooth endpoint
slack, charged-row realization, and postcharge row capacity are supplied by
their existing assumption-free eventual theorems.
-/

open Filter Topology Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.HeadPattern
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.RegularMeshPrimeCutoffs
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

set_option maxHeartbeats 2400000

/-! ## Two reusable capacity facts -/

/-- A paper-scale mass bound and a linear lower bound for every sample cell
give the exact `Cactive / L` bound for the scaled source seed itself.

Unlike the active-ledger wrapper, this statement does not identify the
scaled seed with the bridge baseline; the post-height bridge has a different
active mass, so that identification would be false for `Tsource,qTilde`. -/
theorem bankPaperCanonical_scaledActiveSeed_le_divLog_of_cellDensity
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (T : BarycentricTarget B.sampleData)
    (q Cq density : Real)
    (hCq : 0 <= Cq) (hdensity : 0 < density)
    (hq : |q| <= Cq * secondOrderScale B.sampleData.n)
    (hcard : forall cell : Cell Head,
      density * (B.sampleData.n : Real) <=
        (Fintype.card (B.sampleData.SampleAt cell) : Real)) :
    forall m : B.sampleData.Sample,
      bankPaperCanonicalScaledActiveSeed T q m <=
        (Cq / density) / B.L := by
  intro m
  let cell := B.sampleData.cellOf m
  have hcardPos :
      0 < (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    exact_mod_cast B.sampleData.sampleAt_card_pos cell
  have hcellPos : 0 < T.baseline.cellMass cell :=
    T.baseline.cellMass_pos cell
  have hcellOne : T.baseline.cellMass cell <= 1 :=
    bankPaperCanonical_baseline_cellMass_le_one T cell
  have hscaled :
      bankPaperCanonicalScaledActiveSeed T q m =
        (q * T.baseline.cellMass cell) /
          Fintype.card (B.sampleData.SampleAt cell) := by
    unfold bankPaperCanonicalScaledActiveSeed BaselineAllocation.baseWeight
    change
      q * (T.baseline.cellMass cell /
          Fintype.card (B.sampleData.SampleAt cell)) =
        (q * T.baseline.cellMass cell) /
          Fintype.card (B.sampleData.SampleAt cell)
    ring
  have hscaledUpper :
      bankPaperCanonicalScaledActiveSeed T q m <=
        |q| / Fintype.card (B.sampleData.SampleAt cell) := by
    rw [hscaled]
    calc
      (q * T.baseline.cellMass cell) /
            Fintype.card (B.sampleData.SampleAt cell) <=
          (|q| * T.baseline.cellMass cell) /
            Fintype.card (B.sampleData.SampleAt cell) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_abs_self q) hcellPos.le)
          hcardPos.le
      _ <= (|q| * 1) /
            Fintype.card (B.sampleData.SampleAt cell) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hcellOne (abs_nonneg q))
          hcardPos.le
      _ = |q| / Fintype.card (B.sampleData.SampleAt cell) := by
        ring
  have hmassUpper :
      |q| / Fintype.card (B.sampleData.SampleAt cell) <=
        (Cq * secondOrderScale B.sampleData.n) /
          Fintype.card (B.sampleData.SampleAt cell) :=
    div_le_div_of_nonneg_right hq hcardPos.le
  have hfactorNonneg : 0 <= (Cq / density) / B.L :=
    div_nonneg (div_nonneg hCq hdensity.le) B.L_pos.le
  have hcardScaled :=
    mul_le_mul_of_nonneg_left (hcard cell) hfactorNonneg
  have hscaleIdentity :
      Cq * secondOrderScale B.sampleData.n =
        ((Cq / density) / B.L) *
          (density * (B.sampleData.n : Real)) := by
    change
      Cq * ((B.sampleData.n : Real) / B.L) =
        ((Cq / density) / B.L) *
          (density * (B.sampleData.n : Real))
    field_simp [hdensity.ne', B.L_pos.ne']
  have hcapacity :
      (Cq * secondOrderScale B.sampleData.n) /
            Fintype.card (B.sampleData.SampleAt cell) <=
        (Cq / density) / B.L := by
    apply (div_le_iff₀ hcardPos).2
    calc
      Cq * secondOrderScale B.sampleData.n =
          ((Cq / density) / B.L) *
            (density * (B.sampleData.n : Real)) :=
        hscaleIdentity
      _ <= ((Cq / density) / B.L) *
            (Fintype.card (B.sampleData.SampleAt cell) : Real) :=
        hcardScaled
  exact hscaledUpper.trans (hmassUpper.trans hcapacity)

/-- Eventual linear cell capacity for every bridge whose structured sample
is literally the canonical guard-deleted sample.  This is the cardinality
part of the active-ledger theorem, exposed independently because the source
seed is not the post-height bridge baseline. -/
theorem eventually_bankPaperCanonical_canonicalSample_cellDensityFloor
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (Phead : Head -> Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData Head Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell : Cell Head,
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
            forall cell : Cell Head,
              bankPaperCanonicalGuardedCellDensityFloor Phead I *
                  (B.sampleData.n : Real) <=
                (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
  have hguardedDensity :=
    eventually_guarded_rawCell_density Phead I Cprom Cbank ledger
  filter_upwards [hguardedDensity, eventually_gt_atTop 0] with
      n hguardedDensityN hn
  intro B hBn hsep hremaining hcanonical cell
  have hnReal : 0 < (n : Real) := by
    exact_mod_cast hn
  have hcellFinset :
      B.sampleData.cellFinset cell =
        rawCell Phead I n cell \ (ledger n).guards := by
    calc
      B.sampleData.cellFinset cell =
          (canonicalSampleData (W := B.sampleData.W)
            Phead I (ledger B.sampleData.n)
              hsep hremaining).cellFinset cell :=
        congrArg
          (fun D : StructuredSampleData Head => D.cellFinset cell)
          hcanonical
      _ = rawCell Phead I B.sampleData.n cell \
          (ledger B.sampleData.n).guards :=
        canonicalSampleData_cellFinset
          Phead I (ledger B.sampleData.n) hsep hremaining cell
      _ = rawCell Phead I n cell \ (ledger n).guards := by
        rw [hBn]
  have hcardEq :
      (Fintype.card (B.sampleData.SampleAt cell) : Real) =
        ((rawCell Phead I n cell \ (ledger n).guards).card : Real) := by
    rw [Fintype.card_coe, hcellFinset]
  have hdensityLe :
      bankPaperCanonicalGuardedCellDensityFloor Phead I <=
        paperCellDensity (Phead cell.1)
          (I.lower cell.2) (I.upper cell.2) / 4 :=
    bankPaperCanonicalGuardedCellDensityFloor_le Phead I cell
  calc
    bankPaperCanonicalGuardedCellDensityFloor Phead I *
          (B.sampleData.n : Real) =
        bankPaperCanonicalGuardedCellDensityFloor Phead I *
          (n : Real) := by rw [hBn]
    _ <=
        (paperCellDensity (Phead cell.1)
          (I.lower cell.2) (I.upper cell.2) / 4) * (n : Real) :=
      mul_le_mul_of_nonneg_right hdensityLe hnReal.le
    _ = paperCellDensity (Phead cell.1)
          (I.lower cell.2) (I.upper cell.2) * (n : Real) / 4 := by
      ring
    _ <= ((rawCell Phead I n cell \
        (ledger n).guards).card : Real) :=
      hguardedDensityN cell
    _ = (Fintype.card
        (B.sampleData.SampleAt cell) : Real) :=
      hcardEq.symm

/-! ## Eventual residual construction -/

/-- The strongest noncircular eventual constructor for the literal
frozen-top source residual.

The paper target is supplied by its actual constructors and exact
equalities, rather than by an unconstrained target contract.  Feasibility,
charged rows, and full prime-band support are conclusions.  The source
target `T`, mass `qTilde`, realization, certificate, fixed exceptional set,
and rough level `K0 + 1` are unchanged in the result. -/
theorem
    eventually_bankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt_of_coherentTarget
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Patterns : PaperHeadSimplex.Tag P -> Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (G : forall n, Ledger n Cprom Cbank)
    (depth W K0 : Nat)
    {c deltaStar betaProt betaAct sigma : Real}
    (hc : 0 < c) (hdeltaStar : 0 < deltaStar)
    (hbetaProt : 0 <= betaProt) (hbetaAct : 0 < betaAct)
    (hsigmaNonneg : 0 <= sigma) (hsigmaProt : sigma <= betaProt)
    (hbetaUpper :
      betaProt + betaAct <= c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W <= (((K0 + 1 : Nat) : Real)))
    (hprefix : 2 * depth + 1 <= W) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (hcanonicalSep :
            physicalBound (I.upper .minus) B.sampleData.n <
              physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell : Cell (PaperHeadSimplex.Tag P),
            (rawCell Patterns I B.sampleData.n cell \
              (G B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Patterns I (G B.sampleData.n)
                  hcanonicalSep hremaining ->
        forall
          (R : BankPaperRealization B.sampleData.n
            (upperEndpoint B.sampleData.n
              (upperTailLength c B.sampleData.n)))
          (certificate : GuardedCentralAnchorCertificate c depth
            B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
            (R.centralChangedMarkers depth))
          (T : BarycentricTarget B.sampleData)
          (qTilde : Real),
          qTilde =
              bankPaperCanonicalGuardedSmoothBaseMass R certificate
                deltaStar B.sampleData.W (K0 + 1) betaAct ->
        forall
          (hprime : ∀ p ∈ P, p.Prime)
          (Rhead : HeadSimplexReserve P)
          (Kphysical : PhysicalInterpolationTarget I)
          (hlo : forall sign, B.sampleData.lo sign =
            physicalBound (I.lower sign) B.sampleData.n)
          (hhi : forall sign, B.sampleData.hi sign =
            physicalBound (I.upper sign) B.sampleData.n),
          T =
              B.barycentricTargetOfPaperData
                I hlo hhi Rhead Kphysical ->
          qTilde = Rhead.activeMass ->
          B.sampleData.pattern =
              PaperHeadSimplex.pattern P hprime Rhead.exponent ->
          primesUpTo B.sampleData.W ⊆ P ->
          B.sampleData.HeadPatternsSeparated ->
          (forall sign, 1 <= I.lower sign) ->
          (forall sign, I.upper sign <= 2) ->
          (forall sign,
            physicalBound (I.upper sign) B.sampleData.n <=
              2 * B.sampleData.n -
                (K0 + 1) * upperTailLength c B.sampleData.n) ->
          (K0 + 1) * upperTailLength c B.sampleData.n <=
              B.sampleData.n ->
          (forall m : B.sampleData.Sample,
            B.sampleData.value m ∉
              R.roughCanonicalGuardSet certificate deltaStar) ->
          (forall p : {p : Nat // p ∈ P},
            p.1 <= B.sampleData.W ->
              Rhead.target p =
                ((certificate.selectorTailTarget R
                  (R.paperFixedExceptionalFactors deltaStar)).factorization
                    p.1 : Real)) ->
          R.selectorTailCharge
                (R.paperFixedExceptionalFactors deltaStar) ∣
              certificate.prechargedTailTarget ->
          BankPaperCanonicalTopFrozenRoundedSourceResidualInputsAt
            (K := K0 + 1) B R certificate
              (R.paperFixedExceptionalFactors deltaStar)
              T deltaStar betaProt
                (bankPaperCanonicalPostHfitBalancedAlpha
                  B c K0 betaProt betaAct)
                (betaProt + betaAct) qTilde := by
  let density :=
    bankPaperCanonicalGuardedCellDensityFloor Patterns I
  let Cactive := |betaAct| / density
  have hdensity : 0 < density := by
    simpa only [density] using
      bankPaperCanonicalGuardedCellDensityFloor_pos Patterns I
  have hCactive : 0 <= Cactive := by
    dsimp only [Cactive]
    exact div_nonneg (abs_nonneg betaAct) hdensity.le
  have hbetaNonneg : 0 <= betaProt + betaAct :=
    add_nonneg hbetaProt hbetaAct.le
  have Halpha :=
    eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
      (Head := PaperHeadSimplex.Tag P) (Band := Band)
      W K0 hc hbetaNonneg hbetaUpper hKlarge
  have Hnonsmooth :=
    eventually_roughCanonicalBalancedNonsmoothBounds
      W K0 hc hdeltaStar hbetaAct hsigmaProt
  have Hrows :=
    eventually_bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_chargedNonsmoothRows
      (P := P) (Band := Band) depth W (K0 + 1) hc hdeltaStar
  have Hcapacity :=
    BankPaperRealization.eventually_roughCanonical_active_intrinsic_guard_capacity_inputs
      W (K0 + 1) 1 hc hdeltaStar
  have HcellDensity :=
    eventually_bankPaperCanonical_canonicalSample_cellDensityFloor
      (Band := Band) Patterns I Cprom Cbank G
  have hLTop : Tendsto L atTop atTop := by
    simpa only [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have HsourceRoom :
      ∀ᶠ n : Nat in atTop, betaProt + Cactive <= L n :=
    hLTop.eventually (eventually_ge_atTop (betaProt + Cactive))
  have HbetaRoom :
      ∀ᶠ n : Nat in atTop, betaProt + betaAct <= L n :=
    hLTop.eventually (eventually_ge_atTop (betaProt + betaAct))
  filter_upwards [
      Halpha, Hnonsmooth, Hrows, Hcapacity, HcellDensity,
      HsourceRoom, HbetaRoom,
      eventually_ge_atTop (centralAnchorCutoffThreshold depth),
      eventually_yNat_lt_centralAnchorCutoff depth]
      with n halphaN hnonsmoothN hrowsN hcapacityN hcellDensityN
        hsourceRoomN hbetaRoomN hnCutoff hyCutoff
  intro B hBn hBW hcanonicalSep hremaining hcanonical
    R certificate T qTilde hmass
    hprime Rhead Kphysical hlo hhi hT hqTarget hpattern hhead
    hheadSeparated hlowerOne hupperTwo hupperBroad hroughDepth
    houtsideGuard hcompatibility hchargeDvd
  subst n
  have halpha :
      bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct ∈ Set.Icc (0 : Real) 1 :=
    halphaN B rfl hBW
  have hactiveBroad :
      forall m : B.sampleData.Sample,
        B.sampleData.value m ∈
          roughBroadLowerBlock B.sampleData.n
            (upperTailLength c B.sampleData.n) (K0 + 1) := by
    intro m
    exact
      bankPaperCanonicalStructuredValue_mem_roughBroadLowerBlock_of_physicalIntervals
        B I (upperTailLength c B.sampleData.n) (K0 + 1)
          hlowerOne hupperTwo hlo hhi hupperBroad m
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow
          certificate deltaStar (K0 + 1) 1 :=
    bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
      B R certificate deltaStar I hlowerOne hupperTwo hlo hhi
        hroughDepth houtsideGuard
  have hqBound :
      |qTilde| <= |betaAct| * secondOrderScale B.sampleData.n := by
    calc
      |qTilde| =
          |bankPaperCanonicalGuardedSmoothBaseMass R certificate
            deltaStar B.sampleData.W (K0 + 1) betaAct| :=
        congrArg abs hmass
      _ <= |betaAct| * secondOrderScale B.sampleData.n :=
        abs_bankPaperCanonicalGuardedSmoothBaseMass_le_abs_mul_secondOrderScale
          R certificate deltaStar B.sampleData.W (K0 + 1)
            betaAct B.n_gt_one
  have hcard :
      forall cell : Cell (PaperHeadSimplex.Tag P),
        density * (B.sampleData.n : Real) <=
          (Fintype.card (B.sampleData.SampleAt cell) : Real) := by
    simpa only [density] using
      hcellDensityN B rfl hcanonicalSep hremaining hcanonical
  have hseedUpper :
      forall m : B.sampleData.Sample,
        bankPaperCanonicalScaledActiveSeed T qTilde m <=
          Cactive / B.L := by
    simpa only [Cactive] using
      bankPaperCanonical_scaledActiveSeed_le_divLog_of_cellDensity
        B T qTilde |betaAct| density (abs_nonneg betaAct)
          hdensity hqBound hcard
  have hsourceRoom : betaProt + Cactive <= B.L := by
    simpa only [BridgeData.L] using hsourceRoomN
  have hbetaRoom : betaProt + betaAct <= B.L := by
    simpa only [BridgeData.L] using hbetaRoomN
  have hbetaBox :
      0 <= (betaProt + betaAct) / B.L ∧
        (betaProt + betaAct) / B.L <= 1 := by
    constructor
    · exact div_nonneg hbetaNonneg B.L_pos.le
    · apply (div_le_iff₀ B.L_pos).2
      simpa only [one_mul] using hbetaRoom
  have hsigmaBox : 0 <= sigma / B.L :=
    div_nonneg hsigmaNonneg B.L_pos.le
  have hnonsmooth :=
    hnonsmoothN depth R certificate hnCutoff hyCutoff
  have hfloor :
      forall label,
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          sigma / B.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar B.sampleData.W (K0 + 1) label
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  (betaProt + betaAct) B.L| <=
            (betaProt + betaAct) / B.L := by
    intro label hlabel
    simpa only [
      bankPaperCanonicalPostHfitBalancedAlpha, BridgeData.L, hBW] using
      (hnonsmooth label hlabel).1
  have hceiling :
      forall label,
        RoughCanonicalActiveNonexceptionalLabel
            B.sampleData.n deltaStar label ->
          (betaProt + betaAct) / B.L +
              |R.roughCanonicalGuardedPostchargeCorrectionDensity
                certificate deltaStar B.sampleData.W (K0 + 1) label
                  (bankPaperCanonicalPostHfitBalancedAlpha
                    B c K0 betaProt betaAct)
                  (betaProt + betaAct) B.L| <=
            1 - sigma / B.L := by
    intro label hlabel
    simpa only [
      bankPaperCanonicalPostHfitBalancedAlpha, BridgeData.L, hBW] using
      (hnonsmooth label hlabel).2
  have hqNonneg : 0 <= qTilde := by
    rw [hqTarget]
    exact Rhead.activeMass_pos.le
  have hfeasible :=
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_feasible_of_scaledSeedDivLog_of_twoSidedSlack
      (K := K0 + 1) B R certificate T deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) qTilde sigma Cactive
        hqNonneg halpha hbetaProt hbetaBox hsigmaBox
        hheadSeparated hactiveBroad hCactive hseedUpper
        hsourceRoom hfloor hceiling
  have hrows :=
    hrowsN B rfl hBW R certificate T betaProt
      (bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct)
      (betaProt + betaAct) qTilde
  have hpostchargeCapacity :
      forall label,
        IsCompleteRoughLabel (yNat B.sampleData.n) label ->
          RoughCanonicalActiveNonexceptionalLabel
              B.sampleData.n deltaStar label ->
            RoughCanonicalPostchargeRowCapacity
              R certificate deltaStar (K0 + 1) label := by
    intro label hcomplete hactive
    exact
      (hcapacityN depth R.anchorGuardLeftCore R.anchorGuardRightCore
        (R.centralChangedMarkers depth) R certificate hnCutoff hyCutoff
          label hcomplete hactive).2.2
  have hrowsTarget :
      let Tpaper :=
        B.barycentricTargetOfPaperData I hlo hhi Rhead Kphysical
      BankPaperCanonicalChargedNonsmoothRowRealization
        (K := K0 + 1) R certificate deltaStar
          (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
            (K := K0 + 1) B R certificate deltaStar betaProt
              (bankPaperCanonicalPostHfitBalancedAlpha
                B c K0 betaProt betaAct)
              (betaProt + betaAct)
              (bankPaperCanonicalScaledActiveSeed
                Tpaper Rhead.activeMass)) := by
    dsimp only
    rw [← hT, ← hqTarget]
    exact hrows
  have hprefixB : 2 * depth + 1 <= B.sampleData.W := by
    simpa only [hBW] using hprefix
  have hsupportTarget :=
    bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop_deficitSupportedOnPrimeBand
      (K := K0 + 1) B hprime Rhead I hlo hhi Kphysical hpattern
        R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) hactiveSmooth hhead hcompatibility
          hprefixB hchargeDvd hrowsTarget hpostchargeCapacity
  have hsupport :
      BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
        (W := B.sampleData.W) R certificate
        (R.paperFixedExceptionalFactors deltaStar)
        (R.roughCanonicalGuardedCandidateSet
          certificate deltaStar (K0 + 1))
        (bankPaperCanonicalGlobalCorrectedSourceSelectorWithTop
          (K := K0 + 1) B R certificate deltaStar betaProt
            (bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct)
            (betaProt + betaAct)
            (bankPaperCanonicalScaledActiveSeed T qTilde)) := by
    rw [hT, hqTarget]
    exact hsupportTarget
  exact ⟨hfeasible, hrows, hsupport⟩

end BankPaperRealization

end

end Erdos390.WholePaper
