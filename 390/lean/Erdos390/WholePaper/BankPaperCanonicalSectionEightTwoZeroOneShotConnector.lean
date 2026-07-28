import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellOuterCapacityConnector
import Erdos390.WholePaper.BankPaperCanonicalBridgeRelevantGuardLedger

/-!
# One-shot Section 8 orchestration for the two zero-head cells

This file joins the three already audited layers of the literal Section 8
construction:

* the analytic ledger gives the `q0` and integer-height asymptotics;
* the two-zero-cell producer realizes the height change by `-d / 2` in
  each physical copy of the zero head cell; and
* the structured prebridge ledger transports the resulting integral row
  change and the exact head-prime moments.

The source selector is not postulated through a new interface.  It is the
canonical protected-plus-ambient selector, and its finite selector state is
read directly from the existing
`BankPaperCanonicalRoundedSelectorTangentInput`.  Consequently the only
new feasibility work is at the two coordinates that actually change.

The terminal eventual theorem uses the same `hcanonical` and
`cellMassMargin` arguments as the canonical Proposition 8.7 statement.  It
only assumes that the ledger and rough guard agree on the positive, smooth,
at-most-`2n` structured universe.  Together with the canonical sample guards,
this yields pointwise exclusion from the full rough guard without any global
Finset equality.  To invoke the existing actual P87 endpoint consumer after
the structured placement, one must additionally identify
the rebalanced seed with a bridge baseline (`Hmeasure` and `hseed`) and
supply the existing analytic `Hfit`; those are retained under their
existing names rather than hidden in a new assumption package.
-/

open Filter Topology Asymptotics Set
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.GuardSquarefreeErrorRate
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperScaleMarkedCell
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## A reusable two-cell scalar capacity lemma -/

/-- Any active-mass family of paper scale, perturbed by a little-o cell
change, fits in either canonical zero-head cell.  This is the common
asymptotic argument behind the `qTilde` normalization stage and the
height-only `q0` stage. -/
theorem eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (activeMass cellChange : Nat -> Real)
    (HmassLower : BankPaperCanonicalActiveMassPaperScaleLower activeMass)
    (HmassUpper : activeMass =O[atTop] secondOrderScale)
    (Hchange : cellChange =o[atTop] secondOrderScale)
    {marginFloor : Real} (hmarginFloor : 0 < marginFloor)
    (betaProt : Real) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall sigma : PhysicalSign,
              0 <= activeMass n *
                    T.baseline.cellMass (none, sigma) +
                  cellChange n ∧
              activeMass n * T.baseline.cellMass (none, sigma) +
                  cellChange n <=
                (Fintype.card
                    (B.sampleData.SampleAt (none, sigma)) : Real) *
                  (1 - betaProt / B.L) := by
  rcases HmassLower with ⟨Clower, hClower, hmassLower⟩
  rcases (isBigO_iff').mp HmassUpper with
    ⟨Cupper, hCupper, hmassUpper⟩
  have hremoveChange :=
    Hchange.bound
      (half_pos (mul_pos hClower hmarginFloor))
  have haddChange := Hchange.bound (by norm_num : (0 : Real) < 1)
  let rho := bankPaperCanonicalZeroHeadCellDensityFloor Phead I
  have hrho : 0 < rho := by
    simpa only [rho] using
      bankPaperCanonicalZeroHeadCellDensityFloor_pos Phead I
  have hscaleSmall :=
    (secondOrderScale_isLittleO_natCast.const_mul_left
      (Cupper + 1)).bound (half_pos hrho)
  have hdensity :=
    eventually_guarded_rawCell_density Phead I Cprom Cbank ledger
  have hLTop : Tendsto L atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLlarge : ∀ᶠ n : Nat in atTop,
      2 * betaProt <= L n :=
    hLTop.eventually (eventually_ge_atTop (2 * betaProt))
  filter_upwards [hmassLower, hmassUpper, hremoveChange, haddChange,
      hscaleSmall, hdensity, hLlarge, eventually_gt_atTop 1] with
      n hmassLowerN hmassUpperN hremoveN haddN hscaleSmallN
        hdensityN hLlargeN hn
  intro B hBn hsep hremaining hcanonical T hTmargin sigma
  have hscalePos : 0 < secondOrderScale n :=
    secondOrderScale_pos (by omega)
  have hnReal : 0 < (n : Real) := by
    exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hcellPos :
      0 < T.baseline.cellMass (none, sigma) :=
    T.baseline.cellMass_pos (none, sigma)
  have hcellFloor :
      marginFloor <= T.baseline.cellMass (none, sigma) :=
    bankPaperCanonical_marginFloor_le_baseline_cellMass
      T hTmargin (none, sigma)
  have hcellOne :
      T.baseline.cellMass (none, sigma) <= 1 :=
    bankPaperCanonical_baseline_cellMass_le_one T (none, sigma)
  have hmassPos : 0 < activeMass n := by
    exact (mul_pos hClower hscalePos).trans_le hmassLowerN
  have hremoveAbs :
      |cellChange n| <=
        (Clower * marginFloor / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscalePos] using hremoveN
  have hbaseLower :
      Clower * marginFloor * secondOrderScale n <=
        activeMass n * T.baseline.cellMass (none, sigma) := by
    calc
      Clower * marginFloor * secondOrderScale n =
          (Clower * secondOrderScale n) * marginFloor := by ring
      _ <= activeMass n * marginFloor :=
        mul_le_mul_of_nonneg_right hmassLowerN hmarginFloor.le
      _ <= activeMass n * T.baseline.cellMass (none, sigma) :=
        mul_le_mul_of_nonneg_left hcellFloor hmassPos.le
  have hremove :
      0 <= activeMass n * T.baseline.cellMass (none, sigma) +
        cellChange n := by
    have hchangeLower :
        -(Clower * marginFloor / 2 * secondOrderScale n) <=
          cellChange n :=
      neg_le_of_abs_le hremoveAbs
    have hmainScaleNonneg :
        0 <= Clower * marginFloor * secondOrderScale n := by
      positivity
    nlinarith
  have hmassUpperAbs :
      |activeMass n| <= Cupper * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscalePos] using hmassUpperN
  have haddAbs :
      |cellChange n| <= secondOrderScale n := by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_pos hscalePos] using haddN
  have hmassCellUpper :
      activeMass n * T.baseline.cellMass (none, sigma) <=
        Cupper * secondOrderScale n := by
    calc
      activeMass n * T.baseline.cellMass (none, sigma) <=
          |activeMass n| * T.baseline.cellMass (none, sigma) :=
        mul_le_mul_of_nonneg_right
          (le_abs_self (activeMass n)) hcellPos.le
      _ <= |activeMass n| * 1 :=
        mul_le_mul_of_nonneg_left hcellOne (abs_nonneg _)
      _ = |activeMass n| := by ring
      _ <= Cupper * secondOrderScale n := hmassUpperAbs
  have htotalUpper :
      activeMass n * T.baseline.cellMass (none, sigma) +
          cellChange n <=
        (Cupper + 1) * secondOrderScale n := by
    have hchangeUpper : cellChange n <= secondOrderScale n :=
      (le_abs_self (cellChange n)).trans haddAbs
    nlinarith
  have hscaleSmall' :
      (Cupper + 1) * secondOrderScale n <=
        rho / 2 * (n : Real) := by
    have hCtotal : 0 < Cupper + 1 := by linarith
    simpa only [Real.norm_eq_abs,
      abs_of_pos (mul_pos hCtotal hscalePos),
      abs_of_pos hnReal] using hscaleSmallN
  have hcellFinset :
      B.sampleData.cellFinset (none, sigma) =
        rawCell Phead I n (none, sigma) \
          (ledger n).guards := by
    calc
      B.sampleData.cellFinset (none, sigma) =
          (canonicalSampleData (W := B.sampleData.W)
            Phead I (ledger B.sampleData.n)
              hsep hremaining).cellFinset (none, sigma) :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.cellFinset (none, sigma))
          hcanonical
      _ = rawCell Phead I B.sampleData.n (none, sigma) \
          (ledger B.sampleData.n).guards :=
        canonicalSampleData_cellFinset
          Phead I (ledger B.sampleData.n)
            hsep hremaining (none, sigma)
      _ = rawCell Phead I n (none, sigma) \
          (ledger n).guards := by rw [hBn]
  have hcardEq :
      (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) =
        ((rawCell Phead I n (none, sigma) \
          (ledger n).guards).card : Real) := by
    rw [Fintype.card_coe, hcellFinset]
  have hcardDensity :
      rho * (n : Real) <=
        (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) := by
    have hrhoLe :
        rho <= paperCellDensity (Phead none)
            (I.lower sigma) (I.upper sigma) / 4 := by
      simpa only [rho] using
        bankPaperCanonicalZeroHeadCellDensityFloor_le
          Phead I sigma
    calc
      rho * (n : Real) <=
          (paperCellDensity (Phead none)
            (I.lower sigma) (I.upper sigma) / 4) * (n : Real) :=
        mul_le_mul_of_nonneg_right hrhoLe hnReal.le
      _ = paperCellDensity (Phead none)
          (I.lower sigma) (I.upper sigma) * (n : Real) / 4 := by
        ring
      _ <= ((rawCell Phead I n (none, sigma) \
          (ledger n).guards).card : Real) :=
        hdensityN (none, sigma)
      _ = (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) :=
        hcardEq.symm
  have hLpos : 0 < L n := L_pos hn
  have hprotectedHalfN :
      (1 : Real) / 2 <= 1 - betaProt / L n := by
    have hdiv : betaProt / L n <= (1 : Real) / 2 := by
      apply (div_le_iff₀ hLpos).2
      nlinarith
    linarith
  have hBL : B.L = L n := by
    unfold BridgeData.L L
    rw [hBn]
  have hprotectedHalf :
      (1 : Real) / 2 <= 1 - betaProt / B.L := by
    simpa only [hBL] using hprotectedHalfN
  have hadd :
      activeMass n * T.baseline.cellMass (none, sigma) +
          cellChange n <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (1 - betaProt / B.L) := by
    calc
      activeMass n * T.baseline.cellMass (none, sigma) +
          cellChange n <=
          rho / 2 * (n : Real) :=
        htotalUpper.trans hscaleSmall'
      _ = (rho * (n : Real)) * ((1 : Real) / 2) := by ring
      _ <= (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) *
            ((1 : Real) / 2) :=
        mul_le_mul_of_nonneg_right hcardDensity (by norm_num)
      _ <= (Fintype.card
          (B.sampleData.SampleAt (none, sigma)) : Real) *
            (1 - betaProt / B.L) :=
        mul_le_mul_of_nonneg_left hprotectedHalf (by positivity)
  exact And.intro hremove hadd

/-! ## Height-only capacity from the Section 8 ledger -/

/-- The literal signed mass `-d(n)/2` placed in either zero-head cell. -/
def bankPaperCanonicalSymmetricHeightCellMassFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSymmetricHeightCellMass
    (bankPaperCanonicalSmoothDIntFamily
      mu logY Lambda0 mFrozen qTilde n)

/-- The height-only cell change is little-o of the paper scale. -/
theorem bankPaperCanonicalSymmetricHeightCellMassFamily_isLittleO
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSymmetricHeightCellMassFamily
        mu logY Lambda0 mFrozen qTilde =o[atTop]
      secondOrderScale := by
  have hdBigO :=
    bankPaperCanonicalSectionEight_d_isBigO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hd :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =o[atTop]
        secondOrderScale :=
    hdBigO.trans_isLittleO
      secondOrderScale_div_L_isLittleO_secondOrderScale
  have hhalf := hd.const_mul_left (-(1 : Real) / 2)
  exact hhalf.congr_left fun n => by
    unfold bankPaperCanonicalSymmetricHeightCellMassFamily
    unfold bankPaperCanonicalSymmetricHeightCellMass
    unfold bankPaperCanonicalSmoothDRealFamily
    ring

/-- Both zero-head cells have exact scalar capacity for the integer
height-only rebalance that starts from the initialized `q0` seed. -/
theorem
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_scalarCapacity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct mu marginFloor : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (hmarginFloor : 0 < marginFloor)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde))
    (betaProt : Real) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall sigma : PhysicalSign,
              0 <=
                  bankPaperCanonicalSmoothQ0Family mFrozen qTilde n *
                    T.baseline.cellMass (none, sigma) -
                  (bankPaperCanonicalSmoothDIntFamily
                    mu logY Lambda0 mFrozen qTilde n : Real) / 2 ∧
              bankPaperCanonicalSmoothQ0Family mFrozen qTilde n *
                    T.baseline.cellMass (none, sigma) -
                  (bankPaperCanonicalSmoothDIntFamily
                    mu logY Lambda0 mFrozen qTilde n : Real) / 2 <=
                (Fintype.card
                    (B.sampleData.SampleAt (none, sigma)) : Real) *
                  (1 - betaProt / B.L) := by
  let rawBase : Nat -> Real := fun n =>
    bankPaperCanonicalRawSmoothBaseMass W n
      (upperTailLength c n) K betaAct
  have HrawLower :
      BankPaperCanonicalActiveMassPaperScaleLower rawBase := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_paperScaleLower
        W K hc hbeta
  have HqTildeLower :
      BankPaperCanonicalActiveMassPaperScaleLower qTilde :=
    bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
      rawBase qTilde HrawLower Hledger.1
  have Hq0Lower :
      BankPaperCanonicalActiveMassPaperScaleLower
        (bankPaperCanonicalSmoothQ0Family mFrozen qTilde) :=
    bankPaperCanonicalSmoothQ0Family_paperScaleLower
      mFrozen qTilde HqTildeLower
  have HrawBigO : rawBase =O[atTop] secondOrderScale := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have HqTildeBigO : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      rawBase qTilde HrawBigO Hledger.1
  have Hq0BigO :
      bankPaperCanonicalSmoothQ0Family mFrozen qTilde =O[atTop]
        secondOrderScale :=
    bankPaperCanonicalSmoothQ0Family_isBigO
      mFrozen qTilde HqTildeBigO
  have Hheight :
      bankPaperCanonicalSymmetricHeightCellMassFamily
          mu logY Lambda0 mFrozen qTilde =o[atTop]
        secondOrderScale :=
    bankPaperCanonicalSymmetricHeightCellMassFamily_isLittleO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hcapacity :=
    eventually_bankPaperCanonicalTwoZeroHeadCell_scalarCapacity_of_asymptoticMass
      (P := P) (Band := Band)
      Phead I Cprom Cbank ledger
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde)
      (bankPaperCanonicalSymmetricHeightCellMassFamily
        mu logY Lambda0 mFrozen qTilde)
      Hq0Lower Hq0BigO Hheight hmarginFloor betaProt
  filter_upwards [hcapacity] with n hcapacityN
  intro B hBn hsep hremaining hcanonical T hTmargin sigma
  have hscalar :=
    hcapacityN B hBn hsep hremaining hcanonical T hTmargin sigma
  unfold bankPaperCanonicalSymmetricHeightCellMassFamily
    bankPaperCanonicalSymmetricHeightCellMass at hscalar
  constructor <;> nlinarith [hscalar.1, hscalar.2]

/-- Pointwise `[0,1]` capacity on either changed zero-head cell. -/
theorem
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_rebalance_capacity
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (W K : Nat) {c betaAct mu marginFloor : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (hmarginFloor : 0 < marginFloor)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde))
    (betaProt : Real) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell Phead I B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                Phead I (ledger B.sampleData.n) hsep hremaining ->
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall (sigma : PhysicalSign)
              (m : B.sampleData.Sample),
              B.sampleData.cellOf m = (none, sigma) ->
              0 <=
                  bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n)) m ∧
              betaProt / B.L +
                  bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n)) m <= 1 := by
  have hcapacity :=
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_scalarCapacity
      (P := P) (Band := Band)
      Phead I Cprom Cbank ledger W K hc hbeta hmu hmarginFloor
        logY Lambda0 mFrozen qTilde Hledger betaProt
  filter_upwards [hcapacity] with n hcapacityN
  intro B hBn hsep hremaining hcanonical T hTmargin sigma m hcell
  have hscalar :=
    hcapacityN B hBn hsep hremaining hcanonical T hTmargin sigma
  exact
    ⟨bankPaperCanonicalSymmetricHeightRebalance_nonneg_of_cellMass
        B.sampleData T
          (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
          (bankPaperCanonicalSmoothDIntFamily
            mu logY Lambda0 mFrozen qTilde n)
          m sigma hcell (by linarith [hscalar.1]),
      bankPaperCanonicalSymmetricHeightRebalance_protected_le_one_of_cellMass
        B T
          (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
          (bankPaperCanonicalSmoothDIntFamily
            mu logY Lambda0 mFrozen qTilde n)
          betaProt m sigma hcell hscalar.2⟩

/-! ## Reusing the rounded source selector -/

/-- For an injective structured value map, the ambient push-forward of an
arbitrary tagged seed at an occupied value is exactly the corresponding
tagged weight. -/
theorem bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
    {Head : Type*} [Fintype Head]
    (D : StructuredSampleData Head) (seed : D.Sample -> Real)
    (hsep : D.HeadPatternsSeparated) (m : D.Sample) :
    bankPaperCanonicalActiveSeedAmbientWeight D seed (D.value m) =
      seed m := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  rw [Finset.sum_eq_single m]
  · simp
  · intro k _hk hkm
    rw [if_neg]
    intro hvalue
    exact hkm (D.value_injective_of_headPatternsSeparated hsep hvalue)
  · simp

/-- A feasible canonical ambient source remains feasible after a
two-zero-cell rebalance as soon as the two changed tagged cells satisfy
their literal pointwise capacities.  Every other active coordinate is
unchanged, while every non-active coordinate is equal to the source
selector by the ambient difference identity. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_feasible_of_source
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real) (hbetaProt : 0 <= betaProt)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hsource : ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <= bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed a ∧
        bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed a <= 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1)
    (hplusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m <= 1) :
    ∀ a ∈
      R.roughCanonicalGuardedCandidateSet certificate deltaStar K,
      0 <=
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a ∧
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a <= 1 := by
  intro a haCandidate
  by_cases hactive :
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData
  · obtain ⟨m, rfl⟩ :=
      mem_bankPaperCanonicalStructuredActiveValues.mp hactive
    have hnewAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass)
            (B.sampleData.value m) =
          bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
        B.sampleData
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass)
          hsep m
    have holdAmbient :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData oldSeed
            (B.sampleData.value m) = oldSeed m :=
      bankPaperCanonicalActiveSeedAmbientWeight_eq_of_value
        B.sampleData oldSeed hsep m
    by_cases hmMinus :
        B.sampleData.cellOf m = (none, .minus)
    · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
          (K := K)
          B R certificate
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass)
            (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
        hnewAmbient,
        bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
          B R certificate (hminus m hmMinus)]
      have hcap := hminusCapacity m hmMinus
      exact
        ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
          hcap.2⟩
    · by_cases hmPlus :
          B.sampleData.cellOf m = (none, .plus)
      · rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
            (K := K)
            B R certificate
              (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed)
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass)
              (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩),
          hnewAmbient,
          bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
            B R certificate (hplus m hmPlus)]
        have hcap := hplusCapacity m hmPlus
        exact
          ⟨add_nonneg (div_nonneg hbetaProt B.L_pos.le) hcap.1,
            hcap.2⟩
      · have hsame :
          bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass m =
            oldSeed m := by
          simp [bankPaperCanonicalTwoZeroHeadCellRebalance,
            bankPaperCanonicalUniformCellIncrement, hmMinus, hmPlus]
        have hplacedEq :
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                B R certificate deltaStar betaProt
                (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                  B R certificate deltaStar betaProt oldSeed)
                (bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass)
                (B.sampleData.value m) =
              bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed
                  (B.sampleData.value m) := by
          rw [bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_apply_of_mem
                (K := K)
                B R certificate
                  (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                    B R certificate deltaStar betaProt oldSeed)
                  (bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData oldSeed minusMass plusMass)
                  (mem_bankPaperCanonicalStructuredActiveValues.mpr
                    ⟨m, rfl⟩),
              hnewAmbient, hsame]
          by_cases hpool :
              B.sampleData.value m ∈
                R.roughCanonicalGuardedBroadCorrectionPool certificate
                  deltaStar B.sampleData.W K 1
          · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_mem
                B R certificate hpool,
              bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_mem
                (K := K)
                B R certificate oldSeed hpool,
              holdAmbient]
          · rw [bankPaperCanonicalGuardedSmoothProtectedLayer_apply_of_not_mem
                B R certificate hpool,
              bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector_apply_of_not_mem
                (K := K)
                B R certificate oldSeed hpool,
              holdAmbient, zero_add]
        rw [hplacedEq]
        exact hsource (B.sampleData.value m) haCandidate
  · have hnewZero :
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have holdZero :
        bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a = 0 := by
      apply bankPaperCanonicalActiveSeedAmbientWeight_eq_zero_of_not_value
      intro m hma
      exact hactive
        (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, hma⟩)
    have hdiff :=
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source
        (K := K) B R certificate deltaStar betaProt oldSeed
          minusMass plusMass a
    rw [hnewZero, holdZero] at hdiff
    have hplacedEq :
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a =
          bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed a := by
      linarith
    rw [hplacedEq]
    exact hsource a haCandidate

/-- The prior rounded source state, the exact signed prebridge ledger, and
the two changed-cell capacities produce the full structured additive
placement consumed by the actual Proposition 8.7 endpoint theorem. -/
theorem
    bankPaperCanonicalGuardedStructuredAdditivePlacement_symmetricHeight_of_roundedSource
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt : Real)
    (hbetaProt : 0 <= betaProt)
    (T : BarycentricTarget B.sampleData) (q0 : Real) (d : Int)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (Ssource : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      B.partition.band cellIndex pointwiseUpper prefixUpper
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt
          (bankPaperCanonicalScaledActiveSeed T q0)))
    (hsep : B.sampleData.HeadPatternsSeparated)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hminusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d) m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q0)
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d) m <= 1)
    (hplusCapacity : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        0 <= bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
          (bankPaperCanonicalScaledActiveSeed T q0)
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d) m ∧
        betaProt / B.L +
            bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              (bankPaperCanonicalScaledActiveSeed T q0)
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d) m <= 1) :
    BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
      B R certificate fixed deltaStar betaProt
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt
          (bankPaperCanonicalScaledActiveSeed T q0))
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalScaledActiveSeed T q0)
        (bankPaperCanonicalSymmetricHeightCellMass d)
        (bankPaperCanonicalSymmetricHeightCellMass d)) := by
  have Sstate :=
    bankPaperCanonicalRoundedSelectorTangentInput_selectorState Ssource
  have hfeasible :=
    bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_feasible_of_source
      (K := K) B R certificate deltaStar betaProt hbetaProt
      (bankPaperCanonicalScaledActiveSeed T q0)
      (bankPaperCanonicalSymmetricHeightCellMass d)
      (bankPaperCanonicalSymmetricHeightCellMass d)
      hsep Sstate.1 hminus hplus hminusCapacity hplusCapacity
  have hledger :=
    bankPaperCanonicalGuardedStructuredAdditivePrebridgeMomentLedger_symmetricHeight
      B R certificate deltaStar betaProt
      (bankPaperCanonicalScaledActiveSeed T q0) d
      hactiveSmooth hminus hplus
  exact
    bankPaperCanonicalGuardedStructuredAdditivePlacement_of_prebridgeMomentLedger
      B R certificate fixed
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt
          (bankPaperCanonicalScaledActiveSeed T q0))
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
        (bankPaperCanonicalScaledActiveSeed T q0)
        (bankPaperCanonicalSymmetricHeightCellMass d)
        (bankPaperCanonicalSymmetricHeightCellMass d))
      hfeasible Sstate.2.1 Sstate.2.2.2 hledger

/-! ## Exact quota transport -/

/-- The same symmetric height placement transports an explicitly known
source smooth-row quota by the literal integer `-d`.  Thus the remaining
quota socket is only the exact quota of the already rounded source
selector, not a new integrality or moment package. -/
theorem
    bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_source
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real) (d baseQuota : Int)
    (hbase : BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt oldSeed) baseQuota)
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (baseQuota - d) := by
  unfold BankPaperCanonicalGuardedSmoothFlexibleQuota at hbase ⊢
  have hchange :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed)
              (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                oldSeed
                (bankPaperCanonicalSymmetricHeightCellMass d)
                (bankPaperCanonicalSymmetricHeightCellMass d)) a -
          bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed a)) =
        ((-d : Int) : Real) := by
    calc
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                B R certificate deltaStar betaProt oldSeed)
              (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                oldSeed
                (bankPaperCanonicalSymmetricHeightCellMass d)
                (bankPaperCanonicalSymmetricHeightCellMass d)) a -
          bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed a)) =
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                oldSeed
                (bankPaperCanonicalSymmetricHeightCellMass d)
                (bankPaperCanonicalSymmetricHeightCellMass d)) a -
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a) := by
          apply Finset.sum_congr rfl
          intro a _ha
          exact
            bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source
              (K := K) B R certificate deltaStar betaProt oldSeed
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d) a
      _ = bankPaperCanonicalSymmetricHeightCellMass d +
          bankPaperCanonicalSymmetricHeightCellMass d := by
        apply sum_bankPaperCanonicalTwoZeroHeadCellRebalance_ambient_sub
        · intro m hm
          exact
            R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K 1 (hminus m hm)
        · intro m hm
          exact
            R.roughCanonicalGuardedBroadCorrectionPool_subset_guardedRow
              certificate deltaStar B.sampleData.W K 1 (hplus m hm)
      _ = ((-d : Int) : Real) :=
        bankPaperCanonicalSymmetricHeightCellMass_add_self d
  have hsumChange :
      (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
              B R certificate deltaStar betaProt oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
              oldSeed
              (bankPaperCanonicalSymmetricHeightCellMass d)
              (bankPaperCanonicalSymmetricHeightCellMass d)) a) -
        ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
          bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed a =
        ((-d : Int) : Real) := by
    rw [← Finset.sum_sub_distrib]
    exact hchange
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
          B R certificate deltaStar betaProt
          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
            oldSeed
            (bankPaperCanonicalSymmetricHeightCellMass d)
            (bankPaperCanonicalSymmetricHeightCellMass d)) a) =
      (baseQuota : Real) + ((-d : Int) : Real) := by
        rw [← hbase]
        linarith
    _ = ((baseQuota - d : Int) : Real) := by
      push_cast
      ring

/-- Section 8 specialization of the preceding transport.  Identifying the
canonical source with the displayed `d = 0` flexible quota gives the exact
displayed quota at the constructed integer height `d`. -/
theorem
    bankPaperCanonicalGuardedSmoothFlexibleQuota_initialSource_of_rowIntegral
    {c : Real} {depth n K : Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar qTilde : Real) (selector : Nat -> Real)
    (hrow : BankPaperCanonicalSelectorRowIntegral n
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      selector) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K selector
      (bankPaperCanonicalSmoothFlexibleQuotaAt
        (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
          certificate deltaStar selector qTilde)
        qTilde
        (Int.ofNat
          (completeLabelMultiplicity (yNat n)
              (R.paperFixedExceptionalFactors deltaStar) 1 +
            completeLabelMultiplicity (yNat n)
              R.prechargeBaseState 1))
        0) := by
  obtain ⟨sourceQuota, hsourceQuota⟩ :=
    exists_bankPaperCanonicalSmoothQuota_of_rowIntegral hrow
  have hsourceQuota' :
      (∑ a ∈ R.roughCanonicalGuardedRow
          certificate deltaStar K 1, selector a) =
        (sourceQuota : Real) := by
    simpa only [BankPaperRealization.roughCanonicalGuardedRow] using
      hsourceQuota
  have htotal :
      R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
            certificate deltaStar selector qTilde +
          qTilde =
        ((Int.ofNat
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) 1 +
              completeLabelMultiplicity (yNat n)
                R.prechargeBaseState 1) +
            sourceQuota : Int) : Real) := by
    unfold BankPaperRealization.bankPaperCanonicalInitialSmoothFrozenMass
    rw [hsourceQuota']
    simp only [Int.ofNat_eq_natCast, Nat.cast_add, Int.cast_add,
      Int.cast_natCast]
    ring
  have hinitial :
      bankPaperCanonicalSmoothInitialQuota
          (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
            certificate deltaStar selector qTilde)
          qTilde =
        Int.ofNat
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) 1 +
              completeLabelMultiplicity (yNat n)
                R.prechargeBaseState 1) +
          sourceQuota :=
    bankPaperCanonicalSmoothInitialQuota_eq_of_total_eq_intCast htotal
  have hflexibleQuota :
      bankPaperCanonicalSmoothFlexibleQuotaAt
          (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
            certificate deltaStar selector qTilde)
          qTilde
          (Int.ofNat
            (completeLabelMultiplicity (yNat n)
                (R.paperFixedExceptionalFactors deltaStar) 1 +
              completeLabelMultiplicity (yNat n)
                R.prechargeBaseState 1))
          0 =
        sourceQuota := by
    unfold bankPaperCanonicalSmoothFlexibleQuotaAt
      bankPaperCanonicalSmoothQuotaAt
    rw [hinitial]
    omega
  unfold BankPaperCanonicalGuardedSmoothFlexibleQuota
  rw [hflexibleQuota]
  exact hsourceQuota'

/-- The already rounded canonical ambient source supplies the row-integrality
input in the preceding exact initialization theorem.  Thus its displayed
`d = 0` quota is a theorem once `mFrozen` is the literal row-local frozen
mass, rather than an additional selector premise. -/
theorem
    bankPaperCanonicalGuardedSmoothFlexibleQuota_ambientSource_initial
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt qTilde : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (Ssource : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      B.partition.band cellIndex pointwiseUpper prefixUpper
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt oldSeed)) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt oldSeed)
      (bankPaperCanonicalSmoothFlexibleQuotaAt
        (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
          certificate deltaStar
          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed)
          qTilde)
        qTilde
        (Int.ofNat
          (completeLabelMultiplicity (yNat B.sampleData.n)
              (R.paperFixedExceptionalFactors deltaStar) 1 +
            completeLabelMultiplicity (yNat B.sampleData.n)
              R.prechargeBaseState 1))
        0) := by
  apply
    bankPaperCanonicalGuardedSmoothFlexibleQuota_initialSource_of_rowIntegral
      (K := K) R certificate deltaStar qTilde
  exact
    (bankPaperCanonicalRoundedSelectorTangentInput_selectorState Ssource).2.1

theorem
    bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_initialQuota
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (mFrozen qTilde : Real) (mFix d : Int)
    (hbase : BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt oldSeed)
      (bankPaperCanonicalSmoothFlexibleQuotaAt
        mFrozen qTilde mFix 0))
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalSmoothFlexibleQuotaAt
        mFrozen qTilde mFix d) := by
  have hquota :=
    bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_source
      (K := K) B R certificate deltaStar betaProt oldSeed d
      (bankPaperCanonicalSmoothFlexibleQuotaAt
        mFrozen qTilde mFix 0)
      hbase hminus hplus
  convert hquota using 1
  unfold bankPaperCanonicalSmoothFlexibleQuotaAt
    bankPaperCanonicalSmoothQuotaAt
  omega

/-- Combining literal initialization with the symmetric height transport
closes the constructed smooth quota for the two-cell placement. -/
theorem
    bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_roundedSource
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed : Finset Nat) (deltaStar betaProt qTilde : Real)
    (oldSeed : B.sampleData.Sample -> Real) (d : Int)
    (cellIndex : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Nat)
    (pointwiseUpper : BankPaperCanonicalTangentPrime
      B.sampleData.n B.sampleData.W -> Real)
    (prefixUpper : Band -> Nat -> Real)
    (Ssource : BankPaperCanonicalRoundedSelectorTangentInput
      R certificate fixed
      (R.roughCanonicalGuardedCandidateSet certificate deltaStar K)
      B.partition.band cellIndex pointwiseUpper prefixUpper
      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
        B R certificate deltaStar betaProt oldSeed))
    (hminus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .minus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1)
    (hplus : forall m : B.sampleData.Sample,
      B.sampleData.cellOf m = (none, .plus) ->
        B.sampleData.value m ∈
          R.roughCanonicalGuardedBroadCorrectionPool certificate
            deltaStar B.sampleData.W K 1) :
    BankPaperCanonicalGuardedSmoothFlexibleQuota
      R certificate deltaStar K
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
        B R certificate deltaStar betaProt
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
      (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData oldSeed
          (bankPaperCanonicalSymmetricHeightCellMass d)
          (bankPaperCanonicalSymmetricHeightCellMass d)))
      (bankPaperCanonicalSmoothFlexibleQuotaAt
        (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
          certificate deltaStar
          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
            B R certificate deltaStar betaProt oldSeed)
          qTilde)
        qTilde
        (Int.ofNat
          (completeLabelMultiplicity (yNat B.sampleData.n)
              (R.paperFixedExceptionalFactors deltaStar) 1 +
            completeLabelMultiplicity (yNat B.sampleData.n)
              R.prechargeBaseState 1))
        d) := by
  apply
    bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_initialQuota
      (K := K) B R certificate deltaStar betaProt oldSeed
      (R.bankPaperCanonicalInitialSmoothFrozenMass (K := K)
        certificate deltaStar
        (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
          B R certificate deltaStar betaProt oldSeed)
        qTilde)
      qTilde
      (Int.ofNat
        (completeLabelMultiplicity (yNat B.sampleData.n)
            (R.paperFixedExceptionalFactors deltaStar) 1 +
          completeLabelMultiplicity (yNat B.sampleData.n)
            R.prechargeBaseState 1))
      d
  · exact
      bankPaperCanonicalGuardedSmoothFlexibleQuota_ambientSource_initial
        (K := K) B R certificate fixed deltaStar betaProt qTilde oldSeed
        cellIndex pointwiseUpper prefixUpper Ssource
  · exact hminus
  · exact hplus

/-! ## Canonical P87-local one-shot orchestration -/

/-- A fixed multiple of the upper-tail length is eventually at most the
ambient sample size. -/
theorem eventually_mul_upperTailLength_le_self
    (K : Nat) {c : Real} (hc : 0 < c) :
    ∀ᶠ n : Nat in atTop,
      K * upperTailLength c n <= n := by
  have hT : Tendsto
      (fun n : Nat => (K : Real) *
        ((upperTailLength c n : Real) / (n : Real)))
      atTop (nhds 0) := by
    simpa only [mul_zero] using
      (upperTailLength_ratio_tendsto_zero hc).const_mul (K : Real)
  have hsmall := hT.eventually
    (eventually_lt_nhds (by norm_num : (0 : Real) < 1))
  filter_upwards [hsmall, eventually_gt_atTop 0] with n hn hnPos
  have hn' :
      (K : Real) *
          ((upperTailLength c n : Real) / (n : Real)) < 1 := hn
  have hnReal : 0 < (n : Real) := by exact_mod_cast hnPos
  have hnDiv :
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) < 1 := by
    calc
      ((K : Real) * (upperTailLength c n : Real)) / (n : Real) =
          (K : Real) *
            ((upperTailLength c n : Real) / (n : Real)) := by ring
      _ < 1 := hn'
  have hcross :
      (K : Real) * (upperTailLength c n : Real) < (n : Real) := by
    simpa only [one_mul] using (div_lt_iff₀ hnReal).mp hnDiv
  have hcast :
      ((K * upperTailLength c n : Nat) : Real) < (n : Real) := by
    push_cast
    exact hcross
  exact_mod_cast hcast.le

/-- The canonical-sample and local guard-agreement data expose exactly the
four finite geometry inputs later consumed by the actual active-measure
constructor: head-pattern separation, support in the guarded smooth row,
and guarded broad-pool membership of the two changed zero-head cells.

These facts were previously proved only inside the one-shot terminal.  This
projection has no selector, capacity, asymptotic, or choice input. -/
theorem bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperTwo : forall sigma, I.upper sigma <= 2)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    {c : Real} {depth K : Nat}
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (hhead : primesUpTo B.sampleData.W ⊆ P)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : forall cell : Cell (PaperHeadSimplex.Tag P),
      (rawCell (PaperHeadSimplex.pattern P hprime E) I B.sampleData.n cell \
        (ledger B.sampleData.n).guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W)
        (PaperHeadSimplex.pattern P hprime E) I
        (ledger B.sampleData.n) hsep hremaining)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar : Real)
    (hguardAgreement : BankPaperCanonicalBridgeGuardAgreement
      (ledger B.sampleData.n) R certificate deltaStar)
    (hKh : K * upperTailLength c B.sampleData.n <= B.sampleData.n)
    (hupperBroad : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n) :
    B.sampleData.HeadPatternsSeparated ∧
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 ∧
      (forall m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .minus) ->
          B.sampleData.value m ∈
            R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1) ∧
      forall m : B.sampleData.Sample,
        B.sampleData.cellOf m = (none, .plus) ->
          B.sampleData.value m ∈
            R.roughCanonicalGuardedBroadCorrectionPool certificate
              deltaStar B.sampleData.W K 1 := by
  have hpattern :
      B.sampleData.pattern =
        PaperHeadSimplex.pattern P hprime E := by
    calc
      B.sampleData.pattern =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).pattern :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.pattern)
          hcanonical
      _ = PaperHeadSimplex.pattern P hprime E :=
        canonicalSampleData_pattern
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining
  have hlo : forall sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    calc
      B.sampleData.lo sigma =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).lo sigma :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.lo sigma)
          hcanonical
      _ = physicalBound (I.lower sigma) B.sampleData.n :=
        canonicalSampleData_lo
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining sigma
  have hhi : forall sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    calc
      B.sampleData.hi sigma =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).hi sigma :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.hi sigma)
          hcanonical
      _ = physicalBound (I.upper sigma) B.sampleData.n :=
        canonicalSampleData_hi
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining sigma
  have hsampleGuards :
      B.sampleData.guards =
        (ledger B.sampleData.n).guards := by
    calc
      B.sampleData.guards =
          (canonicalSampleData (W := B.sampleData.W)
            (PaperHeadSimplex.pattern P hprime E) I
            (ledger B.sampleData.n) hsep hremaining).guards :=
        congrArg
          (fun D : StructuredSampleData (PaperHeadSimplex.Tag P) =>
            D.guards)
          hcanonical
      _ = (ledger B.sampleData.n).guards :=
        canonicalSampleData_guards
          (PaperHeadSimplex.pattern P hprime E) I
          (ledger B.sampleData.n) hsep hremaining
  have hbounds :=
    bankPaperCanonicalStructuredValue_bounds_of_physicalIntervals
      B I hlowerOne hupperTwo hlo hhi
  have hnotGuard : forall m : B.sampleData.Sample,
      B.sampleData.value m ∉
        R.roughCanonicalGuardSet certificate deltaStar := by
    intro m hfull
    apply B.sampleData.value_not_guard m
    rw [hsampleGuards]
    exact
      (hguardAgreement (B.sampleData.value m)
        (B.sampleData.value_pos m) (hbounds.2 m)
        (B.sampleData.value_mem_smoothNumbers m)).mpr hfull
  have hheadSep : B.sampleData.HeadPatternsSeparated :=
    Erdos390.Full.PaperBridgeFit.StructuredSampleData.headPatternsSeparated_of_paperHeadSimplex
      P hprime E hE B.sampleData hpattern
  have hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    bankPaperCanonicalStructuredActiveValues_subset_guardedSmoothRow_of_physicalIntervals
      (K := K) B R certificate deltaStar
      I hlowerOne hupperTwo hlo hhi hKh hnotGuard
  have hzeroCells :=
    bankPaperCanonicalTwoZeroHeadCells_subset_guardedBroadCorrectionPool_of_physicalIntervals
      (K := K) B R certificate deltaStar
      hprime E hpattern hhead I hlowerOne hupperTwo hlo hhi
      hupperBroad hnotGuard
  exact ⟨hheadSep, hactiveSmooth, hzeroCells.1, hzeroCells.2⟩

/-- One-shot terminal in the literal local shape of canonical Proposition
8.7.  The Section 8 ledger supplies height-only capacity; `hcanonical`
supplies the physical endpoints and simplex pattern; local ledger/rough-guard
agreement supplies broad-pool membership; and the already rounded
canonical source supplies every unchanged selector invariant.

The conclusion retains the reusable transport from any identified source
quota.  For the literal rounded source used here, the preceding
`bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_roundedSource`
closes that source value directly from its existing row-integrality field. -/
theorem
    eventually_bankPaperCanonicalSectionEight_twoZeroHeadCell_oneShot
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperStrict : forall sigma, I.upper sigma < 2)
    (Cprom Cbank : Nat) (ledger : forall n, Ledger n Cprom Cbank)
    (depth W K : Nat)
    {c betaAct mu marginFloor deltaStar betaProt : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (hmarginFloor : 0 < marginFloor)
    (hbetaProt : 0 <= betaProt)
    (hhead : primesUpTo W ⊆ P)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell (PaperHeadSimplex.pattern P hprime E) I
                B.sampleData.n cell \
              (ledger B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                (PaperHeadSimplex.pattern P hprime E) I
                (ledger B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
              (R.centralChangedMarkers depth))
            (_hguardAgreement : BankPaperCanonicalBridgeGuardAgreement
              (ledger B.sampleData.n) R certificate deltaStar),
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall (fixed : Finset Nat)
              (cellIndex : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W -> Nat)
              (pointwiseUpper : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W -> Real)
              (prefixUpper : Band -> Nat -> Real),
              BankPaperCanonicalRoundedSelectorTangentInput
                R certificate fixed
                (R.roughCanonicalGuardedCandidateSet
                  certificate deltaStar K)
                B.partition.band cellIndex pointwiseUpper prefixUpper
                (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                  B R certificate
                    deltaStar betaProt
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))) ->
              BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
                  B R certificate
                  fixed deltaStar betaProt
                  (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                    B R certificate
                      deltaStar betaProt
                      (bankPaperCanonicalScaledActiveSeed T
                        (bankPaperCanonicalSmoothQ0Family
                          mFrozen qTilde n)))
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) ∧
                forall baseQuota : Int,
                  BankPaperCanonicalGuardedSmoothFlexibleQuota
                      R certificate
                      deltaStar K
                      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                        B R certificate
                          deltaStar betaProt
                          (bankPaperCanonicalScaledActiveSeed T
                            (bankPaperCanonicalSmoothQ0Family
                              mFrozen qTilde n)))
                      baseQuota ->
                    BankPaperCanonicalGuardedSmoothFlexibleQuota
                      R certificate
                      deltaStar K
                      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                        B R certificate
                          deltaStar betaProt
                          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                            B R certificate
                              deltaStar betaProt
                              (bankPaperCanonicalScaledActiveSeed T
                                (bankPaperCanonicalSmoothQ0Family
                                  mFrozen qTilde n)))
                          (bankPaperCanonicalTwoZeroHeadCellRebalance
                            B.sampleData
                            (bankPaperCanonicalScaledActiveSeed T
                              (bankPaperCanonicalSmoothQ0Family
                                mFrozen qTilde n))
                            (bankPaperCanonicalSymmetricHeightCellMass
                              (bankPaperCanonicalSmoothDIntFamily
                                mu logY Lambda0 mFrozen qTilde n))
                            (bankPaperCanonicalSymmetricHeightCellMass
                              (bankPaperCanonicalSmoothDIntFamily
                                mu logY Lambda0 mFrozen qTilde n))))
                      (baseQuota -
                        bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n) := by
  have hcapacity :=
    eventually_bankPaperCanonicalSymmetricHeight_twoZeroHeadCell_rebalance_capacity
      (P := P) (Band := Band)
      (PaperHeadSimplex.pattern P hprime E)
      I Cprom Cbank ledger W K hc hbeta hmu hmarginFloor
        logY Lambda0 mFrozen qTilde Hledger betaProt
  have hupperBroad :=
    eventually_physicalIntervals_upperBound_le_two_mul_sub_upperTailLength
      I K hc hupperStrict
  have hKh := eventually_mul_upperTailLength_le_self K hc
  filter_upwards [hcapacity, hupperBroad, hKh] with
    n hcapacityN hupperBroadN hKhN
  intro B hBn hBW hsep hremaining hcanonical
    R certificate hguardAgreement T hTmargin
    fixed cellIndex pointwiseUpper prefixUpper Ssource
  have hheadB : primesUpTo B.sampleData.W ⊆ P := by
    simpa only [hBW] using hhead
  have hKhB :
      K * upperTailLength c B.sampleData.n <= B.sampleData.n := by
    simpa only [hBn] using hKhN
  have hupperBroadB : forall sigma,
      physicalBound (I.upper sigma) B.sampleData.n <=
        2 * B.sampleData.n -
          K * upperTailLength c B.sampleData.n := by
    intro sigma
    simpa only [hBn] using hupperBroadN sigma
  have hupperTwo : forall sigma, I.upper sigma <= 2 :=
    fun sigma => (hupperStrict sigma).le
  have hgeometry :=
    bankPaperCanonicalSectionEight_twoZeroHeadCell_geometryInputs
      (P := P) (Band := Band) (c := c) (depth := depth) (K := K)
      hprime E hE I hlowerOne hupperTwo Cprom Cbank ledger
      B hheadB hsep hremaining hcanonical R certificate deltaStar
      hguardAgreement hKhB hupperBroadB
  have hheadSep := hgeometry.1
  have hactiveSmooth := hgeometry.2.1
  have hminus := hgeometry.2.2.1
  have hplus := hgeometry.2.2.2
  have hchangedCapacity : forall sigma
      (m : B.sampleData.Sample),
      B.sampleData.cellOf m = (none, sigma) ->
        0 <=
            bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData
              (bankPaperCanonicalScaledActiveSeed T
                (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n))
              (bankPaperCanonicalSymmetricHeightCellMass
                (bankPaperCanonicalSmoothDIntFamily
                  mu logY Lambda0 mFrozen qTilde n))
              (bankPaperCanonicalSymmetricHeightCellMass
                (bankPaperCanonicalSmoothDIntFamily
                  mu logY Lambda0 mFrozen qTilde n)) m ∧
          betaProt / B.L +
              bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData
                (bankPaperCanonicalScaledActiveSeed T
                  (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n))
                (bankPaperCanonicalSymmetricHeightCellMass
                  (bankPaperCanonicalSmoothDIntFamily
                    mu logY Lambda0 mFrozen qTilde n))
                (bankPaperCanonicalSymmetricHeightCellMass
                  (bankPaperCanonicalSmoothDIntFamily
                    mu logY Lambda0 mFrozen qTilde n)) m <= 1 :=
    hcapacityN B hBn hsep hremaining hcanonical T hTmargin
  have Hplacement :=
    bankPaperCanonicalGuardedStructuredAdditivePlacement_symmetricHeight_of_roundedSource
      B R certificate
      fixed deltaStar betaProt hbetaProt T
      (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n)
      (bankPaperCanonicalSmoothDIntFamily
        mu logY Lambda0 mFrozen qTilde n)
      cellIndex pointwiseUpper prefixUpper Ssource
      hheadSep hactiveSmooth hminus hplus
      (hchangedCapacity .minus) (hchangedCapacity .plus)
  refine ⟨Hplacement, ?_⟩
  intro baseQuota hbaseQuota
  exact
    bankPaperCanonicalGuardedSmoothFlexibleQuota_symmetricHeight_of_source
      (K := K) B R certificate
      deltaStar betaProt
      (bankPaperCanonicalScaledActiveSeed T
        (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n))
      (bankPaperCanonicalSmoothDIntFamily
        mu logY Lambda0 mFrozen qTilde n)
      baseQuota hbaseQuota hminus hplus

/-- The literal bridge specialization fixes the ledger family before the
asymptotic index and before any realization or certificate.  The eventual
bridge-relevant agreement theorem then discharges the local agreement
argument of the generic one-shot terminal. -/
theorem
    eventually_bankPaperCanonicalSectionEight_twoZeroHeadCell_oneShot_relevantLedgerFamily
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (hprime : ∀ p ∈ P, p.Prime) (E : Nat) (hE : 0 < E)
    (I : PhysicalIntervals)
    (hlowerOne : forall sigma, 1 <= I.lower sigma)
    (hupperStrict : forall sigma, I.upper sigma < 2)
    (depth W K : Nat)
    {c betaAct mu marginFloor deltaStar betaProt : Real}
    (hc : 0 < c) (hbeta : 0 < betaAct) (hmu : 0 < mu)
    (hmarginFloor : 0 < marginFloor)
    (hbetaProt : 0 <= betaProt)
    (hhead : primesUpTo W ⊆ P)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      forall (B : BridgeData (PaperHeadSimplex.Tag P) Band),
        B.sampleData.n = n ->
        B.sampleData.W = W ->
        forall
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : forall cell :
              Cell (PaperHeadSimplex.Tag P),
            (rawCell (PaperHeadSimplex.pattern P hprime E) I
                B.sampleData.n cell \
              (roughCanonicalBridgeRelevantLedgerFamily
                depth B.sampleData.n).guards).Nonempty),
          B.sampleData =
              canonicalSampleData (W := B.sampleData.W)
                (PaperHeadSimplex.pattern P hprime E) I
                (roughCanonicalBridgeRelevantLedgerFamily
                  depth B.sampleData.n) hsep hremaining ->
          forall
            (R : BankPaperRealization B.sampleData.n
              (upperEndpoint B.sampleData.n
                (upperTailLength c B.sampleData.n)))
            (certificate : GuardedCentralAnchorCertificate c depth
              B.sampleData.n R.anchorGuardLeftCore R.anchorGuardRightCore
              (R.centralChangedMarkers depth)),
          forall (T : BarycentricTarget B.sampleData),
            marginFloor <= T.cellMassMargin ->
            forall (fixed : Finset Nat)
              (cellIndex : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W -> Nat)
              (pointwiseUpper : BankPaperCanonicalTangentPrime
                B.sampleData.n B.sampleData.W -> Real)
              (prefixUpper : Band -> Nat -> Real),
              BankPaperCanonicalRoundedSelectorTangentInput
                R certificate fixed
                (R.roughCanonicalGuardedCandidateSet
                  certificate deltaStar K)
                B.partition.band cellIndex pointwiseUpper prefixUpper
                (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                  B R certificate
                    deltaStar betaProt
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))) ->
              BankPaperCanonicalGuardedStructuredAdditivePlacement (K := K)
                  B R certificate
                  fixed deltaStar betaProt
                  (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                    B R certificate
                      deltaStar betaProt
                      (bankPaperCanonicalScaledActiveSeed T
                        (bankPaperCanonicalSmoothQ0Family
                          mFrozen qTilde n)))
                  (bankPaperCanonicalTwoZeroHeadCellRebalance B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T
                      (bankPaperCanonicalSmoothQ0Family
                        mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricHeightCellMass
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))) ∧
                forall baseQuota : Int,
                  BankPaperCanonicalGuardedSmoothFlexibleQuota
                      R certificate
                      deltaStar K
                      (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                        B R certificate
                          deltaStar betaProt
                          (bankPaperCanonicalScaledActiveSeed T
                            (bankPaperCanonicalSmoothQ0Family
                              mFrozen qTilde n)))
                      baseQuota ->
                    BankPaperCanonicalGuardedSmoothFlexibleQuota
                      R certificate
                      deltaStar K
                      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
                        B R certificate
                          deltaStar betaProt
                          (bankPaperCanonicalTwoZeroHeadCellAmbientSourceSelector (K := K)
                            B R certificate
                              deltaStar betaProt
                              (bankPaperCanonicalScaledActiveSeed T
                                (bankPaperCanonicalSmoothQ0Family
                                  mFrozen qTilde n)))
                          (bankPaperCanonicalTwoZeroHeadCellRebalance
                            B.sampleData
                            (bankPaperCanonicalScaledActiveSeed T
                              (bankPaperCanonicalSmoothQ0Family
                                mFrozen qTilde n))
                            (bankPaperCanonicalSymmetricHeightCellMass
                              (bankPaperCanonicalSmoothDIntFamily
                                mu logY Lambda0 mFrozen qTilde n))
                            (bankPaperCanonicalSymmetricHeightCellMass
                              (bankPaperCanonicalSmoothDIntFamily
                                mu logY Lambda0 mFrozen qTilde n))))
                      (baseQuota -
                        bankPaperCanonicalSmoothDIntFamily
                          mu logY Lambda0 mFrozen qTilde n) := by
  have honeShot :=
    eventually_bankPaperCanonicalSectionEight_twoZeroHeadCell_oneShot
      (P := P) (Band := Band) (c := c) (betaAct := betaAct)
      (mu := mu) (marginFloor := marginFloor)
      (deltaStar := deltaStar) (betaProt := betaProt)
      hprime E hE I hlowerOne hupperStrict
      2 0 (roughCanonicalBridgeRelevantLedgerFamily depth)
      depth W K hc hbeta hmu hmarginFloor hbetaProt hhead
      logY Lambda0 mFrozen qTilde Hledger
  have hagreement :=
    eventually_roughCanonicalBridgeRelevantLedgerFamily_agreement
      (c := c) depth deltaStar
  filter_upwards [honeShot, hagreement] with
    n honeShotN hagreementN
  intro B hBn
  subst n
  intro hBW hsep hremaining hcanonical R certificate
  exact
    honeShotN B rfl hBW hsep hremaining hcanonical R certificate
      (hagreementN R certificate)

end BankPaperRealization

end

end Erdos390.WholePaper
