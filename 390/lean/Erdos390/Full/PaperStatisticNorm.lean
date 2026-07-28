import Erdos390.Full.PaperBridgeFitFeasibility
import Erdos390.Full.ValuationTiltCell
import Erdos390.Full.PaperPrimePowerRow

/-!
# An actual `O(log n)` bound for the paper bridge statistic

This file discharges the pointwise statistic-norm hypothesis used by the
finite feasibility layer of Proposition 8.7.  The proof uses the genuine
valuation statistic on the actual prime band, the physical interval bound,
and fixed mesh/head constants.  No covariance or ODE conclusion is assumed.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperStatisticNorm

open ArithmeticModel Scale ValuationTiltCell
open PaperBridgeFit

noncomputable section

/-- Converts the fixed physical ceiling `C n` to a multiple of `log n`. -/
def physicalLogCoefficient (C : ℝ) : ℝ :=
  1 + Real.log C / Real.log 2

/-- Converts the total band valuation to a multiple of `log n`. -/
def valuationLogCoefficient (C : ℝ) (W : ℕ) : ℝ :=
  physicalLogCoefficient C / Real.log (W : ℝ)

/-- One coordinate envelope, before taking the Euclidean norm. -/
def statisticCoordinateCoefficient (C R : ℝ) (W : ℕ) (w : ℝ) : ℝ :=
  max ((1 + R) * valuationLogCoefficient C W)
    (max (physicalLogCoefficient C)
      (max (3 / Real.log 2) (valuationLogCoefficient C W / w)))

/-- The explicit pointwise statistic-norm constant. -/
def statisticNormConstant
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (C R : ℝ) : ℝ :=
  Real.sqrt (Fintype.card B.Coord : ℝ) *
    statisticCoordinateCoefficient C R B.sampleData.W B.w

lemma physicalLogCoefficient_nonneg {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ physicalLogCoefficient C := by
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold physicalLogCoefficient
  positivity

lemma valuationLogCoefficient_nonneg {C : ℝ} {W : ℕ}
    (hC : 1 ≤ C) (hW : 1 < W) :
    0 ≤ valuationLogCoefficient C W := by
  unfold valuationLogCoefficient
  exact div_nonneg (physicalLogCoefficient_nonneg hC)
    (Real.log_pos (by exact_mod_cast hW)).le

lemma statisticCoordinateCoefficient_nonneg {C R w : ℝ} {W : ℕ}
    (hC : 1 ≤ C) :
    0 ≤ statisticCoordinateCoefficient C R W w := by
  unfold statisticCoordinateCoefficient
  exact (physicalLogCoefficient_nonneg hC).trans
    (le_max_of_le_right (le_max_left _ _))

lemma statisticNormConstant_nonneg
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {C R : ℝ}
    (hC : 1 ≤ C) :
    0 ≤ statisticNormConstant B C R := by
  unfold statisticNormConstant
  exact mul_nonneg (Real.sqrt_nonneg _)
    (statisticCoordinateCoefficient_nonneg hC)

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

lemma log_two_le_L : Real.log 2 ≤ B.L := by
  unfold PaperBridgeFit.BridgeData.L
  apply Real.log_le_log (by norm_num)
  exact_mod_cast B.n_gt_one

/-- The actual physical endpoint has logarithm at most the displayed fixed
multiple of `L=log n`. -/
theorem log_physicalBound_le
    {C : ℝ} (hC : 1 ≤ C) :
    Real.log (physicalBound C B.sampleData.n : ℝ) ≤
      physicalLogCoefficient C * B.L := by
  have hn0 : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hnR : (0 : ℝ) < (B.sampleData.n : ℝ) := by exact_mod_cast hn0
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hphysical : B.sampleData.n ≤ physicalBound C B.sampleData.n := by
    unfold physicalBound
    apply Nat.le_floor
    exact_mod_cast (show (B.sampleData.n : ℝ) ≤
      C * (B.sampleData.n : ℝ) by
        nlinarith [show (0 : ℝ) ≤ (B.sampleData.n : ℝ) by positivity])
  have hMpos : (0 : ℝ) < (physicalBound C B.sampleData.n : ℝ) := by
    exact_mod_cast hn0.trans_le hphysical
  have hMcast : (physicalBound C B.sampleData.n : ℝ) ≤
      C * (B.sampleData.n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hlogM : Real.log (physicalBound C B.sampleData.n : ℝ) ≤
      Real.log C + B.L := by
    calc
      Real.log (physicalBound C B.sampleData.n : ℝ) ≤
          Real.log (C * (B.sampleData.n : ℝ)) :=
        Real.log_le_log hMpos hMcast
      _ = Real.log C + Real.log (B.sampleData.n : ℝ) := by
        rw [Real.log_mul hCpos.ne' hnR.ne']
      _ = Real.log C + B.L := by rfl
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCL : Real.log C ≤ (Real.log C / Real.log 2) * B.L := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog2).2
      (mul_le_mul_of_nonneg_left (log_two_le_L B) hlogC0)
  calc
    Real.log (physicalBound C B.sampleData.n : ℝ) ≤
        Real.log C + B.L := hlogM
    _ ≤ physicalLogCoefficient C * B.L := by
      unfold physicalLogCoefficient
      nlinarith

/-- Total valuation on the genuine prime band is `O(L)` with an explicit
fixed-cutoff coefficient. -/
theorem totalBandValuation_le
    {C : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) :
    (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        valuation p (B.sampleData.value m)) ≤
      valuationLogCoefficient C B.sampleData.W * B.L := by
  have hm := B.sampleData.value_pos m
  have hmM : B.sampleData.value m ≤ physicalBound C B.sampleData.n :=
    (B.sampleData.value_le_hi m).trans (hhi (B.sampleData.cellOf m).2)
  have hpW : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      B.sampleData.W ≤ p := by
    intro p hp
    exact (cutoff_lt_of_mem_primeBand hp).le
  have hraw := sum_valuation_le_log_ratio
    (primeBand B.sampleData.n B.sampleData.W) hm hmM hW hpW
  have hlogW : 0 < Real.log (B.sampleData.W : ℝ) :=
    Real.log_pos (by exact_mod_cast hW)
  calc
    _ ≤ Real.log (physicalBound C B.sampleData.n : ℝ) /
        Real.log (B.sampleData.W : ℝ) := hraw
    _ ≤ (physicalLogCoefficient C * B.L) /
        Real.log (B.sampleData.W : ℝ) :=
      div_le_div_of_nonneg_right (log_physicalBound_le B hC) hlogW.le
    _ = valuationLogCoefficient C B.sampleData.W * B.L := by
      unfold valuationLogCoefficient
      ring

theorem bandCenter_le_one (j : Band) : B.bandCenter j ≤ 1 := by
  change (∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
      B.partition.data.mass j ≤ 1
  have hnum : (∑ p ∈ B.partition.data.fiber j,
      (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) ≤
      B.partition.data.mass j := by
    unfold Erdos390.Lemma84.WeightedBandData.mass
    apply Finset.sum_le_sum
    intro p hp
    have ht := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
    have hp0 : 0 ≤ 1 / (p.1 : ℝ) := by positivity
    calc
      (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 ≤
          (1 / (p.1 : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left ht hp0
      _ = 1 / (p.1 : ℝ) := mul_one _
  exact (div_le_one (B.partition.data.mass_pos j)).2 hnum

theorem abs_primeDeviation_le_one
    (p : ArithmeticBandGeometry.BandPrime
      B.sampleData.n B.sampleData.W) :
    |B.primeDeviation p| ≤ 1 := by
  have hc0 := (B.bandCenter_pos (B.partition.band p)).le
  have hc1 := bandCenter_le_one B (B.partition.band p)
  have ht0 := (B.bandPrime_tPrime_pos p).le
  have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
    B.n_gt_one p.2
  unfold PaperBridgeFit.BridgeData.primeDeviation
  rw [abs_le]
  constructor <;> linarith

theorem bandScore_nonneg (j : Band) (m : B.sampleData.Sample) :
    0 ≤ B.bandScore j m := by
  unfold PaperBridgeFit.BridgeData.bandScore
  exact Finset.sum_nonneg fun p hp ↦ valuation_nonneg p.1 _

theorem bandScore_le_totalBandValuation (j : Band)
    (m : B.sampleData.Sample) :
    B.bandScore j m ≤
      ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        valuation p (B.sampleData.value m) := by
  unfold PaperBridgeFit.BridgeData.bandScore
  calc
    (∑ p ∈ B.partition.data.fiber j,
        valuation p.1 (B.sampleData.value m)) ≤
        ∑ p : ArithmeticBandGeometry.BandPrime
            B.sampleData.n B.sampleData.W,
          valuation p.1 (B.sampleData.value m) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun p hp hnot ↦ valuation_nonneg p.1 _)
    _ = ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
          valuation p (B.sampleData.value m) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach
          (primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ valuation p (B.sampleData.value m)))

theorem abs_slowScore_le_totalBandValuation (m : B.sampleData.Sample) :
    |B.slowScore m| ≤
      ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        valuation p (B.sampleData.value m) := by
  unfold PaperBridgeFit.BridgeData.slowScore
  calc
    |∑ p : ArithmeticBandGeometry.BandPrime
        B.sampleData.n B.sampleData.W,
        B.primeDeviation p * valuation p.1 (B.sampleData.value m)| ≤
      ∑ p : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        |B.primeDeviation p * valuation p.1 (B.sampleData.value m)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : ArithmeticBandGeometry.BandPrime
          B.sampleData.n B.sampleData.W,
        valuation p.1 (B.sampleData.value m) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (valuation_nonneg p.1 _)]
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (abs_primeDeviation_le_one B p)
          (valuation_nonneg p.1 _)
    _ = ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        valuation p (B.sampleData.value m) := by
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach
          (primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ valuation p (B.sampleData.value m)))

theorem log_C_le_physicalLogCoefficient_mul_L
    {C : ℝ} (hC : 1 ≤ C) :
    Real.log C ≤ physicalLogCoefficient C * B.L := by
  have hlogC0 : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hCL : Real.log C ≤ (Real.log C / Real.log 2) * B.L := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ hlog2).2
      (mul_le_mul_of_nonneg_left (log_two_le_L B) hlogC0)
  unfold physicalLogCoefficient
  nlinarith [B.L_pos]

/-- The physical logarithm is uniformly `O(L)` on the two actual physical
pools. -/
theorem abs_physicalScore_le
    {C : ℝ} (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) :
    |B.physicalScore m| ≤ physicalLogCoefficient C * B.L := by
  have hn0 : 0 < B.sampleData.n := Nat.zero_lt_of_lt B.n_gt_one
  have hnR : (0 : ℝ) < (B.sampleData.n : ℝ) := by exact_mod_cast hn0
  have hm0 := B.sampleData.value_pos m
  have hmR : (0 : ℝ) < (B.sampleData.value m : ℝ) := by exact_mod_cast hm0
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have hmM : B.sampleData.value m ≤ physicalBound C B.sampleData.n :=
    (B.sampleData.value_le_hi m).trans (hhi (B.sampleData.cellOf m).2)
  have hMcast : (physicalBound C B.sampleData.n : ℝ) ≤
      C * (B.sampleData.n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg hCpos.le hnR.le)
  have hmUpper : (B.sampleData.value m : ℝ) ≤
      C * (B.sampleData.n : ℝ) :=
    (by exact_mod_cast hmM : (B.sampleData.value m : ℝ) ≤
      (physicalBound C B.sampleData.n : ℝ)).trans hMcast
  have hratioPos : 0 < (B.sampleData.value m : ℝ) /
      (B.sampleData.n : ℝ) := div_pos hmR hnR
  have hratioUpper : (B.sampleData.value m : ℝ) /
      (B.sampleData.n : ℝ) ≤ C := (div_le_iff₀ hnR).2 (by
        simpa only [mul_comm] using hmUpper)
  have hratioLower : 1 / (B.sampleData.n : ℝ) ≤
      (B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ) := by
    exact div_le_div_of_nonneg_right
      (by exact_mod_cast hm0 : (1 : ℝ) ≤ B.sampleData.value m) hnR.le
  have hlogUpper : B.physicalScore m ≤ Real.log C := by
    unfold PaperBridgeFit.BridgeData.physicalScore
    exact Real.log_le_log hratioPos hratioUpper
  have hlogLower : -B.L ≤ B.physicalScore m := by
    have hlog := Real.log_le_log (one_div_pos.mpr hnR) hratioLower
    unfold PaperBridgeFit.BridgeData.physicalScore
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hnR.ne',
      Real.log_one, zero_sub] at hlog
    exact hlog
  have hPL : B.L ≤ physicalLogCoefficient C * B.L := by
    have hPone : 1 ≤ physicalLogCoefficient C := by
      unfold physicalLogCoefficient
      have : 0 ≤ Real.log C / Real.log 2 :=
        div_nonneg (Real.log_nonneg hC)
          (Real.log_pos (by norm_num)).le
      linarith
    simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right hPone B.L_pos.le)
  rw [abs_le]
  constructor
  · linarith
  · exact hlogUpper.trans (log_C_le_physicalLogCoefficient_mul_L B hC)

theorem normalizedCellMass_le_one [Nonempty Head]
    (c : Cell Head) : B.baseline.normalizedCellMass c ≤ 1 := by
  rw [← B.baseline.normalizedCellMass_sum]
  exact Finset.single_le_sum
    (fun d hd ↦ (B.baseline.normalizedCellMass_pos d).le)
    (Finset.mem_univ c)

theorem headBaselineMass_nonneg [Nonempty Head] (h : Head) :
    0 ≤ B.headBaselineMass h := by
  unfold PaperBridgeFit.BridgeData.headBaselineMass
  exact Finset.sum_nonneg fun sigma hsigma ↦
    (B.baseline.normalizedCellMass_pos (h, sigma)).le

theorem headBaselineMass_le_two [Nonempty Head] (h : Head) :
    B.headBaselineMass h ≤ 2 := by
  unfold PaperBridgeFit.BridgeData.headBaselineMass
  calc
    (∑ sigma : PhysicalSign,
        B.baseline.normalizedCellMass (h, sigma)) ≤
        ∑ _sigma : PhysicalSign, (1 : ℝ) := by
      exact Finset.sum_le_sum fun sigma hsigma ↦
        normalizedCellMass_le_one B (h, sigma)
    _ = 2 := by
      have hcard : Fintype.card PhysicalSign = 2 := by rfl
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact_mod_cast hcard

theorem abs_centeredHeadScore_le_three [Nonempty Head]
    (h : B.HeadIndex) (m : B.sampleData.Sample) :
    |B.centeredHeadScore h m| ≤ 3 := by
  have hI0 : 0 ≤ B.headIndicator h.1 m := by
    unfold PaperBridgeFit.BridgeData.headIndicator
    split <;> norm_num
  have hI1 : B.headIndicator h.1 m ≤ 1 := by
    unfold PaperBridgeFit.BridgeData.headIndicator
    split <;> norm_num
  have hH0 := headBaselineMass_nonneg B h.1
  have hH2 := headBaselineMass_le_two B h.1
  unfold PaperBridgeFit.BridgeData.centeredHeadScore
  rw [abs_le]
  constructor <;> linarith

theorem abs_gaugeScore_le
    {C R : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hR : 0 ≤ R)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hratio : ∀ j : B.GaugeIndex, |B.lowRatio j| ≤ R)
    (j : B.GaugeIndex) (m : B.sampleData.Sample) :
    |B.gaugeScore j m| ≤
      ((1 + R) * valuationLogCoefficient C B.sampleData.W) * B.L := by
  let T : ℝ := valuationLogCoefficient C B.sampleData.W * B.L
  have hV0 := valuationLogCoefficient_nonneg hC hW
  have hT0 : 0 ≤ T := mul_nonneg hV0 B.L_pos.le
  have hj0 := bandScore_nonneg B j.1 m
  have hl0 := bandScore_nonneg B B.lowBand m
  have hjT : B.bandScore j.1 m ≤ T :=
    (bandScore_le_totalBandValuation B j.1 m).trans
      (totalBandValuation_le B hC hW hhi m)
  have hlT : B.bandScore B.lowBand m ≤ T :=
    (bandScore_le_totalBandValuation B B.lowBand m).trans
      (totalBandValuation_le B hC hW hhi m)
  unfold PaperBridgeFit.BridgeData.gaugeScore
  calc
    |B.bandScore j.1 m - B.lowRatio j * B.bandScore B.lowBand m| ≤
        |B.bandScore j.1 m| +
          |B.lowRatio j * B.bandScore B.lowBand m| := abs_sub _ _
    _ = B.bandScore j.1 m +
        |B.lowRatio j| * B.bandScore B.lowBand m := by
      rw [abs_of_nonneg hj0, abs_mul, abs_of_nonneg hl0]
    _ ≤ T + R * T := by
      apply add_le_add hjT
      calc
        |B.lowRatio j| * B.bandScore B.lowBand m ≤
            R * B.bandScore B.lowBand m :=
          mul_le_mul_of_nonneg_right (hratio j) hl0
        _ ≤ R * T := mul_le_mul_of_nonneg_left hlT hR
    _ = ((1 + R) * valuationLogCoefficient C B.sampleData.W) * B.L := by
      dsimp only [T]
      ring

theorem abs_slowStatisticCoordinate_le
    {C : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) :
    |B.slowScore m / B.w| ≤
      (valuationLogCoefficient C B.sampleData.W / B.w) * B.L := by
  rw [abs_div, abs_of_pos B.w_pos]
  calc
    |B.slowScore m| / B.w ≤
        (valuationLogCoefficient C B.sampleData.W * B.L) / B.w :=
      div_le_div_of_nonneg_right
        ((abs_slowScore_le_totalBandValuation B m).trans
          (totalBandValuation_le B hC hW hhi m)) B.w_pos.le
    _ = (valuationLogCoefficient C B.sampleData.W / B.w) * B.L := by
      ring

theorem three_le_headCoefficient_mul_L :
    (3 : ℝ) ≤ (3 / Real.log 2) * B.L := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    (3 : ℝ) = (3 / Real.log 2) * Real.log 2 := by field_simp
    _ ≤ (3 / Real.log 2) * B.L :=
      mul_le_mul_of_nonneg_left (log_two_le_L B) (by positivity)

/-- Every literal coordinate of the actual paper statistic has the same
explicit `O(L)` envelope. -/
theorem abs_statistic_apply_le
    [Nonempty Head] {C R : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W) (hR : 0 ≤ R)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hratio : ∀ j : B.GaugeIndex, |B.lowRatio j| ≤ R)
    (m : B.sampleData.Sample) (c : B.Coord) :
    |B.statistic m c| ≤
      statisticCoordinateCoefficient C R B.sampleData.W B.w * B.L := by
  rw [B.statistic_apply]
  cases c with
  | gauge j =>
      simp only [PaperBridgeFit.BridgeData.rawStatistic,
        PaperBridgeFit.BridgeData.coordScale, div_one]
      exact (abs_gaugeScore_le B hC hW hR hhi hratio j m).trans
        (mul_le_mul_of_nonneg_right
          (le_max_left _ _) B.L_pos.le)
  | physical =>
      simp only [PaperBridgeFit.BridgeData.rawStatistic,
        PaperBridgeFit.BridgeData.coordScale, div_one]
      exact (abs_physicalScore_le B hC hhi m).trans
        (mul_le_mul_of_nonneg_right
          (le_max_of_le_right (le_max_left _ _)) B.L_pos.le)
  | head h =>
      simp only [PaperBridgeFit.BridgeData.rawStatistic,
        PaperBridgeFit.BridgeData.coordScale, div_one]
      exact (abs_centeredHeadScore_le_three B h m).trans
        ((three_le_headCoefficient_mul_L B).trans
          (mul_le_mul_of_nonneg_right
            (le_max_of_le_right (le_max_of_le_right (le_max_left _ _)))
            B.L_pos.le))
  | slow =>
      simp only [PaperBridgeFit.BridgeData.rawStatistic,
        PaperBridgeFit.BridgeData.coordScale]
      exact (abs_slowStatisticCoordinate_le B hC hW hhi m).trans
        (mul_le_mul_of_nonneg_right
          (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))
          B.L_pos.le)

/-- The desired unconditional pointwise `O(L)` norm bound for the actual
statistic vector. -/
theorem statistic_norm_le
    [Nonempty Head] {C R : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W) (hR : 0 ≤ R)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hratio : ∀ j : B.GaugeIndex, |B.lowRatio j| ≤ R)
    (m : B.sampleData.Sample) :
    ‖B.statistic m‖ ≤ statisticNormConstant B C R * B.L := by
  let K : ℝ := statisticCoordinateCoefficient C R B.sampleData.W B.w
  have hK0 : 0 ≤ K := statisticCoordinateCoefficient_nonneg hC
  have hKL0 : 0 ≤ K * B.L := mul_nonneg hK0 B.L_pos.le
  have hsum : ‖B.statistic m‖ ^ 2 ≤
      ∑ _c : B.Coord, (K * B.L) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    apply Finset.sum_le_sum
    intro c hc
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (B.statistic m c))
        (by simpa only [K] using
          abs_statistic_apply_le B hC hW hR hhi hratio m c) 2
  have hcard0 : 0 ≤ (Fintype.card B.Coord : ℝ) := by positivity
  have hsqrt : (Real.sqrt (Fintype.card B.Coord : ℝ)) ^ 2 =
      (Fintype.card B.Coord : ℝ) := Real.sq_sqrt hcard0
  have hsumEq : (∑ _c : B.Coord, (K * B.L) ^ 2) =
      (Fintype.card B.Coord : ℝ) * (K * B.L) ^ 2 := by simp
  have htargetSq : (statisticNormConstant B C R * B.L) ^ 2 =
      (Fintype.card B.Coord : ℝ) * (K * B.L) ^ 2 := by
    unfold statisticNormConstant
    dsimp only [K]
    rw [mul_assoc]
    nlinarith
  have htarget0 : 0 ≤ statisticNormConstant B C R * B.L :=
    mul_nonneg (statisticNormConstant_nonneg B hC) B.L_pos.le
  rw [hsumEq] at hsum
  have hsq : ‖B.statistic m‖ ^ 2 ≤
      (statisticNormConstant B C R * B.L) ^ 2 := by
    rw [htargetSq]
    exact hsum
  nlinarith [norm_nonneg (B.statistic m)]

/-- The compact effective-score estimate needed by the ODE layer, now with
the statistic-norm premise discharged by the literal paper statistics. -/
theorem effectiveScoreBound_of_actualStatisticNorm
    [Nonempty Head] {C R : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W) (hR : 0 ≤ R)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hratio : ∀ j : B.GaugeIndex, |B.lowRatio j| ≤ R)
    (xi : B.ParamSpace) (radius : ℝ) (hxi : ‖xi‖ ≤ radius) :
    ∀ m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| ≤
        statisticNormConstant B C R * radius := by
  exact B.effectiveScoreBound_of_statistic_norm
    xi radius (statisticNormConstant B C R) hxi
    (statisticNormConstant_nonneg B hC)
    (statistic_norm_le B hC hW hR hhi hratio)

/-- Literal `[0,1]` feasibility on the preselected parameter ball, with the
former abstract `hstat` premise replaced by the actual valuation, physical,
head, and compensated-score ledger proved above. -/
theorem ambientCombinedWeight_mem_Icc_of_actualStatisticNorm
    [Nonempty Head] {C R : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W) (hR : 0 ≤ R)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hratio : ∀ j : B.GaugeIndex, |B.lowRatio j| ≤ R)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : ℕ → ℝ)
    (hfrozen : ∀ a, frozenWeight a ∈ Set.Icc (0 : ℝ) 1)
    (xi : B.ParamSpace) (radius : ℝ) (hxi : ‖xi‖ ≤ radius)
    (hslack : ∀ m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) +
        Real.exp (2 * (statisticNormConstant B C R * radius)) *
          B.baseline.baseWeight m ≤ 1) :
    ∀ a : ℕ,
      B.ambientCombinedWeight frozenWeight xi a ∈ Set.Icc (0 : ℝ) 1 := by
  exact B.ambientCombinedWeight_mem_Icc_of_statisticNormBound
    hsep frozenWeight hfrozen xi radius (statisticNormConstant B C R)
    hxi (statisticNormConstant_nonneg B hC)
    (statistic_norm_le B hC hW hR hhi hratio) hslack

end BridgeData

end

end Erdos390.Full.PaperStatisticNorm
