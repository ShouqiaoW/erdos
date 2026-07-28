import Erdos390.WholePaper.BankPaperCanonicalTwoZeroHeadCellProducerConnector
import Erdos390.Full.GuardSquarefreeErrorRate

/-!
# Outer asymptotic capacity for the two zero-head cells

The finite two-cell producer reduces feasibility to one lower and one upper
scalar inequality in each physical sign.  This file supplies those
inequalities from the already constructed paper-scale inputs.

The actual post-guard mass is bounded below and above on the
`secondOrderScale` scale.  The combined nearest-integer and height change is
little-o of that scale.  A uniform positive cell-mass margin therefore
absorbs every removal.  On the other side, `secondOrderScale = o(n)` and the
canonical guard-deleted cell-density theorem leave enough room below the
protected ceiling.

The terminal statements use the same local canonical-data equality and
cell-mass-margin argument as Proposition 8.7.  No new asymptotic predicate or
family-identification assumption is introduced.
-/

open Filter Topology Asymptotics
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

/-! ## Scale and cell-mass preliminaries -/

/-- The paper scale `n / log n` is little-o of the ambient cardinality
scale `n`. -/
theorem secondOrderScale_isLittleO_natCast :
    secondOrderScale =o[atTop] (fun n : Nat => (n : Real)) := by
  have hzero : ∀ᶠ n : Nat in atTop,
      (n : Real) = 0 -> secondOrderScale n = 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn hcast
    have hn0 : (n : Real) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hn)
    exact (hn0 hcast).elim
  exact (isLittleO_iff_tendsto' hzero).mpr
    secondOrderScale_ratio_tendsto_zero

/-- A uniform lower bound for `cellMassMargin` is also a lower bound for
each literal baseline cell mass, because the canonical baseline has total
mass one. -/
theorem bankPaperCanonical_marginFloor_le_baseline_cellMass
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) {marginFloor : Real}
    (hTmargin : marginFloor <= T.cellMassMargin)
    (cell : Cell Head) :
    marginFloor <= T.baseline.cellMass cell := by
  calc
    marginFloor <= T.cellMassMargin := hTmargin
    _ <= T.baseline.normalizedCellMass cell :=
      T.cellMassMargin_le cell
    _ = T.baseline.cellMass cell := by
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]

/-- Every literal canonical baseline cell mass is at most one. -/
theorem bankPaperCanonical_baseline_cellMass_le_one
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head}
    (T : BarycentricTarget D) (cell : Cell Head) :
    T.baseline.cellMass cell <= 1 := by
  calc
    T.baseline.cellMass cell =
        T.baseline.normalizedCellMass cell := by
      symm
      unfold BaselineAllocation.normalizedCellMass
      rw [T.baseline_totalMass, div_one]
    _ <= 1 := by
      rw [← T.baseline.normalizedCellMass_sum]
      exact Finset.single_le_sum
        (fun d _hd => (T.baseline.normalizedCellMass_pos d).le)
        (Finset.mem_univ cell)

/-! ## The combined cell change is negligible -/

/-- The actual symmetric cell change from the post-guard mass `qTilde`
through nearest-integer initialization and the integer height adjustment. -/
def bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
    (mu : Real) (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (n : Nat) : Real :=
  bankPaperCanonicalSymmetricInitialAndHeightCellMass
    (mFrozen n) (qTilde n)
    (bankPaperCanonicalSmoothDIntFamily
      mu logY Lambda0 mFrozen qTilde n)

/-- The combined change in one zero-head cell is `o(n / log n)`: the
nearest-integer part is already little-o, and half of the height change is
`O(n / log^2 n)`. -/
theorem
    bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily_isLittleO
    (W K : Nat) (c betaAct : Real) {mu : Real} (hmu : 0 < mu)
    (logY Lambda0 mFrozen qTilde : Nat -> Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
        mu logY Lambda0 mFrozen qTilde =o[atTop]
      secondOrderScale := by
  have hround :=
    bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
      mFrozen qTilde
  have hdBigO :=
    bankPaperCanonicalSectionEight_d_isBigO
      W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hd :
      bankPaperCanonicalSmoothDRealFamily
          mu logY Lambda0 mFrozen qTilde =o[atTop]
        secondOrderScale :=
    hdBigO.trans_isLittleO
      secondOrderScale_div_L_isLittleO_secondOrderScale
  have hcombined :
      (fun n =>
        (bankPaperCanonicalSmoothQ0Family mFrozen qTilde n -
            qTilde n) -
          bankPaperCanonicalSmoothDRealFamily
            mu logY Lambda0 mFrozen qTilde n) =o[atTop]
        secondOrderScale :=
    hround.sub hd
  have hhalf := hcombined.const_mul_left ((1 : Real) / 2)
  exact hhalf.congr_left fun n => by
    unfold bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
    unfold bankPaperCanonicalSymmetricInitialAndHeightCellMass
    unfold bankPaperCanonicalSmoothActiveMassAt
    unfold bankPaperCanonicalSmoothQ0Family
    unfold bankPaperCanonicalSmoothDRealFamily
    ring

/-! ## A common positive density for the two zero-head cells -/

/-- A fixed density valid simultaneously for the two physical signs of the
zero-head cell. -/
def bankPaperCanonicalZeroHeadCellDensityFloor
    {P : Finset Nat}
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals) : Real :=
  min
      (paperCellDensity (Phead none)
        (I.lower .minus) (I.upper .minus))
      (paperCellDensity (Phead none)
        (I.lower .plus) (I.upper .plus)) / 4

theorem bankPaperCanonicalZeroHeadCellDensityFloor_pos
    {P : Finset Nat}
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals) :
    0 < bankPaperCanonicalZeroHeadCellDensityFloor Phead I := by
  unfold bankPaperCanonicalZeroHeadCellDensityFloor
  have hminus :
      0 < paperCellDensity (Phead none)
        (I.lower .minus) (I.upper .minus) :=
    paperCellDensity_pos (Phead none) (I.lower_lt_upper .minus)
  have hplus :
      0 < paperCellDensity (Phead none)
        (I.lower .plus) (I.upper .plus) :=
    paperCellDensity_pos (Phead none) (I.lower_lt_upper .plus)
  exact div_pos (lt_min hminus hplus) (by norm_num)

theorem bankPaperCanonicalZeroHeadCellDensityFloor_le
    {P : Finset Nat}
    (Phead : PaperHeadSimplex.Tag P -> HeadPattern.Pattern)
    (I : PhysicalIntervals) (sigma : PhysicalSign) :
    bankPaperCanonicalZeroHeadCellDensityFloor Phead I <=
      paperCellDensity (Phead none)
        (I.lower sigma) (I.upper sigma) / 4 := by
  cases sigma with
  | minus =>
      unfold bankPaperCanonicalZeroHeadCellDensityFloor
      have h := min_le_left
        (paperCellDensity (Phead none)
          (I.lower .minus) (I.upper .minus))
        (paperCellDensity (Phead none)
          (I.lower .plus) (I.upper .plus))
      nlinarith
  | plus =>
      unfold bankPaperCanonicalZeroHeadCellDensityFloor
      have h := min_le_right
        (paperCellDensity (Phead none)
          (I.lower .minus) (I.upper .minus))
        (paperCellDensity (Phead none)
          (I.lower .plus) (I.upper .plus))
      nlinarith

/-! ## Outer scalar capacity -/

/-- For every sufficiently large canonical P87 sample, both zero-head
physical cells satisfy the exact scalar removal and protected-addition
inequalities required by the finite producer. -/
theorem
    eventually_bankPaperCanonicalSymmetricInitialAndHeight_twoZeroHeadCell_scalarCapacity
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
              0 <= qTilde n * T.baseline.cellMass (none, sigma) +
                bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
                  mu logY Lambda0 mFrozen qTilde n ∧
              qTilde n * T.baseline.cellMass (none, sigma) +
                  bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
                    mu logY Lambda0 mFrozen qTilde n <=
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
  have HqLower :
      BankPaperCanonicalActiveMassPaperScaleLower qTilde :=
    bankPaperCanonicalPostGuardSmoothMass_paperScaleLower
      rawBase qTilde HrawLower Hledger.1
  rcases HqLower with ⟨Clower, hClower, hqLower⟩
  have HrawBigO : rawBase =O[atTop] secondOrderScale := by
    simpa only [rawBase] using
      bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct
  have HqBigO : qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      rawBase qTilde HrawBigO Hledger.1
  rcases (isBigO_iff').mp HqBigO with
    ⟨Cupper, hCupper, hqUpper⟩
  let cellChange : Nat -> Real :=
    bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
      mu logY Lambda0 mFrozen qTilde
  have hcellChange : cellChange =o[atTop] secondOrderScale := by
    simpa only [cellChange] using
      bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily_isLittleO
        W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hremoveChange :=
    hcellChange.bound
      (half_pos (mul_pos hClower hmarginFloor))
  have haddChange := hcellChange.bound (by norm_num : (0 : Real) < 1)
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
  filter_upwards [hqLower, hqUpper, hremoveChange, haddChange,
      hscaleSmall, hdensity, hLlarge, eventually_gt_atTop 1] with
      n hqLowerN hqUpperN hremoveN haddN hscaleSmallN
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
  have hqPos : 0 < qTilde n := by
    exact (mul_pos hClower hscalePos).trans_le hqLowerN
  have hremoveAbs :
      |cellChange n| <=
        (Clower * marginFloor / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscalePos] using hremoveN
  have hbaseLower :
      Clower * marginFloor * secondOrderScale n <=
        qTilde n * T.baseline.cellMass (none, sigma) := by
    calc
      Clower * marginFloor * secondOrderScale n =
          (Clower * secondOrderScale n) * marginFloor := by ring
      _ <= qTilde n * marginFloor :=
        mul_le_mul_of_nonneg_right hqLowerN hmarginFloor.le
      _ <= qTilde n * T.baseline.cellMass (none, sigma) :=
        mul_le_mul_of_nonneg_left hcellFloor hqPos.le
  have hremove :
      0 <= qTilde n * T.baseline.cellMass (none, sigma) +
        cellChange n := by
    have hchangeLower :
        -(Clower * marginFloor / 2 * secondOrderScale n) <=
          cellChange n :=
      (neg_le_of_abs_le hremoveAbs)
    have hmainScaleNonneg :
        0 <= Clower * marginFloor * secondOrderScale n := by
      positivity
    nlinarith
  have hqUpperAbs :
      |qTilde n| <= Cupper * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscalePos] using hqUpperN
  have haddAbs :
      |cellChange n| <= secondOrderScale n := by
    simpa only [Real.norm_eq_abs, one_mul, abs_of_pos hscalePos] using haddN
  have hqCellUpper :
      qTilde n * T.baseline.cellMass (none, sigma) <=
        Cupper * secondOrderScale n := by
    calc
      qTilde n * T.baseline.cellMass (none, sigma) <=
          |qTilde n| * T.baseline.cellMass (none, sigma) :=
        mul_le_mul_of_nonneg_right
          (le_abs_self (qTilde n)) hcellPos.le
      _ <= |qTilde n| * 1 :=
        mul_le_mul_of_nonneg_left hcellOne (abs_nonneg _)
      _ = |qTilde n| := by ring
      _ <= Cupper * secondOrderScale n := hqUpperAbs
  have htotalUpper :
      qTilde n * T.baseline.cellMass (none, sigma) +
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
          (W := B.sampleData.W)
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
      qTilde n * T.baseline.cellMass (none, sigma) +
          cellChange n <=
        (Fintype.card
            (B.sampleData.SampleAt (none, sigma)) : Real) *
          (1 - betaProt / B.L) := by
    calc
      qTilde n * T.baseline.cellMass (none, sigma) +
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
  simpa only [cellChange] using And.intro hremove hadd

/-! ## Feeding the finite producer -/

/-- The outer scalar theorem closes the literal coordinate inequalities of
the two-zero-cell producer for every sample in either zero-head cell. -/
theorem
    eventually_bankPaperCanonicalSymmetricInitialAndHeight_twoZeroHeadCell_rebalance_capacity
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
                    (bankPaperCanonicalScaledActiveSeed T (qTilde n))
                    (bankPaperCanonicalSymmetricInitialAndHeightCellMass
                      (mFrozen n) (qTilde n)
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricInitialAndHeightCellMass
                      (mFrozen n) (qTilde n)
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n)) m ∧
              betaProt / B.L +
                  bankPaperCanonicalTwoZeroHeadCellRebalance
                    B.sampleData
                    (bankPaperCanonicalScaledActiveSeed T (qTilde n))
                    (bankPaperCanonicalSymmetricInitialAndHeightCellMass
                      (mFrozen n) (qTilde n)
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n))
                    (bankPaperCanonicalSymmetricInitialAndHeightCellMass
                      (mFrozen n) (qTilde n)
                      (bankPaperCanonicalSmoothDIntFamily
                        mu logY Lambda0 mFrozen qTilde n)) m <= 1 := by
  have hcapacity :=
    eventually_bankPaperCanonicalSymmetricInitialAndHeight_twoZeroHeadCell_scalarCapacity
      (P := P) (Band := Band)
      Phead I Cprom Cbank ledger W K hc hbeta hmu hmarginFloor
        logY Lambda0 mFrozen qTilde Hledger betaProt
  filter_upwards [hcapacity] with n hcapacityN
  intro B hBn hsep hremaining hcanonical T hTmargin sigma m hcell
  have hscalar :=
    hcapacityN B hBn hsep hremaining hcanonical T hTmargin sigma
  have hmass :
      bankPaperCanonicalSymmetricInitialAndHeightCellMassFamily
          mu logY Lambda0 mFrozen qTilde n =
        bankPaperCanonicalSymmetricInitialAndHeightCellMass
          (mFrozen n) (qTilde n)
          (bankPaperCanonicalSmoothDIntFamily
            mu logY Lambda0 mFrozen qTilde n) :=
    rfl
  rw [hmass] at hscalar
  exact
    ⟨bankPaperCanonicalSymmetricInitialAndHeightRebalance_nonneg_of_cellMass
        B.sampleData T (mFrozen n) (qTilde n)
          (bankPaperCanonicalSmoothDIntFamily
            mu logY Lambda0 mFrozen qTilde n)
          m sigma hcell hscalar.1,
      bankPaperCanonicalSymmetricInitialAndHeightRebalance_protected_le_one_of_cellMass
        B T (mFrozen n) (qTilde n)
          (bankPaperCanonicalSmoothDIntFamily
            mu logY Lambda0 mFrozen qTilde n)
          betaProt m sigma hcell hscalar.2⟩

end BankPaperRealization

end

end Erdos390.WholePaper
