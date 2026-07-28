import Erdos390.Full.PaperGuardedStructuredSample
import Erdos390.Full.PaperUniformNuisanceGap
import Erdos390.Full.PaperStatisticNorm

/-!
# Uniform nuisance geometry from the fixed physical intervals

The paper fixes two scaled intervals `(a_sigma n, b_sigma n]`.  This file
connects their literal floored natural endpoints to the physical logarithm
used by `BridgeData`.  It produces the fixed separation and fixed bound
required by `PaperUniformNuisanceGap`; neither constant depends on `n`.
-/

namespace Erdos390.Full.PaperBridgeFit

open ArithmeticModel PaperGuardCensus

noncomputable section

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- A sample in a floored scaled physical cell lies below the corresponding
fixed real upper endpoint after division by `n`. -/
theorem physicalScore_le_log_upper
    (I : PaperGuardCensus.PhysicalIntervals)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (m : B.sampleData.Sample) :
    B.physicalScore m ≤ Real.log (I.upper (B.sampleData.cellOf m).2) := by
  let sigma := (B.sampleData.cellOf m).2
  have hn : (0 : ℝ) < B.sampleData.n := by
    exact_mod_cast (Nat.zero_lt_of_lt B.n_gt_one)
  have hv : (0 : ℝ) < B.sampleData.value m := by
    exact_mod_cast B.sampleData.value_pos m
  have hmleNat : B.sampleData.value m ≤
      physicalBound (I.upper sigma) B.sampleData.n := by
    simpa only [sigma, hhi] using B.sampleData.value_le_hi m
  have hmle : (B.sampleData.value m : ℝ) ≤
      (physicalBound (I.upper sigma) B.sampleData.n : ℝ) := by
    exact_mod_cast hmleNat
  have hfloor : (physicalBound (I.upper sigma) B.sampleData.n : ℝ) ≤
      I.upper sigma * (B.sampleData.n : ℝ) := by
    unfold physicalBound
    exact Nat.floor_le (mul_nonneg
      (le_of_lt ((I.lower_pos sigma).trans (I.lower_lt_upper sigma)))
      (Nat.cast_nonneg _))
  have hratio :
      (B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ) ≤
        I.upper sigma := by
    apply (div_le_iff₀ hn).2
    exact hmle.trans hfloor
  unfold physicalScore
  exact Real.log_le_log (div_pos hv hn) hratio

/-- The strict lower endpoint survives the natural floor because the sample
coordinate is an integer strictly above that floor. -/
theorem log_lower_lt_physicalScore
    (I : PaperGuardCensus.PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (m : B.sampleData.Sample) :
    Real.log (I.lower (B.sampleData.cellOf m).2) < B.physicalScore m := by
  let sigma := (B.sampleData.cellOf m).2
  have hn : (0 : ℝ) < B.sampleData.n := by
    exact_mod_cast (Nat.zero_lt_of_lt B.n_gt_one)
  have hmgtNat : physicalBound (I.lower sigma) B.sampleData.n <
      B.sampleData.value m := by
    simpa only [sigma, hlo] using B.sampleData.lo_lt_value m
  have hfloorlt : I.lower sigma * (B.sampleData.n : ℝ) <
      (physicalBound (I.lower sigma) B.sampleData.n : ℝ) + 1 := by
    unfold physicalBound
    exact Nat.lt_floor_add_one _
  have hsuccNat : physicalBound (I.lower sigma) B.sampleData.n + 1 ≤
      B.sampleData.value m := by omega
  have hsucc :
      (physicalBound (I.lower sigma) B.sampleData.n : ℝ) + 1 ≤
        (B.sampleData.value m : ℝ) := by
    exact_mod_cast hsuccNat
  have hscaled : I.lower sigma * (B.sampleData.n : ℝ) <
      (B.sampleData.value m : ℝ) := hfloorlt.trans_le hsucc
  have hratio : I.lower sigma <
      (B.sampleData.value m : ℝ) / (B.sampleData.n : ℝ) := by
    apply (lt_div_iff₀ hn).2
    simpa only [mul_comm] using hscaled
  unfold physicalScore
  exact Real.log_lt_log (I.lower_pos sigma) hratio

/-- If all fixed lower endpoints exceed one and all upper endpoints are at
most `U`, every physical logarithm is nonnegative and at most `log U`. -/
theorem abs_physicalScore_le_log_upperBound
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (m : B.sampleData.Sample) :
    |B.physicalScore m| ≤ Real.log U := by
  have hlower := B.log_lower_lt_physicalScore I hlo m
  have hlowerLog : 0 ≤
      Real.log (I.lower (B.sampleData.cellOf m).2) :=
    Real.log_nonneg (hlowerOne _)
  have hscore0 : 0 ≤ B.physicalScore m :=
    hlowerLog.trans hlower.le
  rw [abs_of_nonneg hscore0]
  exact (B.physicalScore_le_log_upper I hhi m).trans
    (Real.log_le_log
      ((I.lower_pos _).trans (I.lower_lt_upper _))
      (hupperU _))

/-- The two fixed physical pools give a quantitative gap between their
conditional means. -/
theorem fixedInterval_cellPhysicalMean_separation [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (h : Head) :
    Real.log (I.lower .plus) - Real.log (I.upper .minus) ≤
      B.cellPhysicalMean (h, .plus) -
        B.cellPhysicalMean (h, .minus) := by
  apply B.cellPhysicalMean_sub_ge_of_cellwise h
    (Real.log (I.upper .minus)) (Real.log (I.lower .plus))
  · intro m hm
    exact (B.physicalScore_le_log_upper I hhi m).trans_eq (by
      congr 1
      exact congrArg I.upper (congrArg Prod.snd hm))
  · intro m hm
    exact (B.log_lower_lt_physicalScore I hlo m).le.trans_eq' (by
      congr 1
      exact congrArg I.lower (congrArg Prod.snd hm))

/-- Uniform absolute bound for every conditional physical mean. -/
theorem fixedInterval_abs_cellPhysicalMean_le [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (c : Cell Head) :
    |B.cellPhysicalMean c| ≤ Real.log U := by
  apply B.abs_cellPhysicalMean_le_of_cellwise c (Real.log U)
  intro m hm
  exact B.abs_physicalScore_le_log_upperBound I
    hlowerOne hupperU hlo hhi m

/-- Fixed, `n`-independent radius for the nuisance statistic vector. -/
def fixedIntervalNuisanceRadius [Nonempty Head] (U : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
    max (Real.log U) 3

theorem fixedIntervalNuisanceRadius_nonneg [Nonempty Head] (U : ℝ) :
    0 ≤ B.fixedIntervalNuisanceRadius U := by
  unfold fixedIntervalNuisanceRadius
  positivity

theorem nuisanceStatistic_norm_le_fixedIntervals [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (m : B.sampleData.Sample) :
    ‖B.nuisanceStatistic m‖ ≤ B.fixedIntervalNuisanceRadius U := by
  let K : ℝ := max (Real.log U) 3
  have hK : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 3).trans (le_max_right _ _)
  have hcoord : ∀ c : NuisanceCoord B.HeadIndex,
      |B.nuisanceStatistic m c| ≤ K := by
    intro c
    cases c with
    | physical =>
        rw [B.nuisanceStatistic_physical]
        exact (B.abs_physicalScore_le_log_upperBound I
          hlowerOne hupperU hlo hhi m).trans (le_max_left _ _)
    | head h =>
        rw [B.nuisanceStatistic_head]
        exact (PaperStatisticNorm.BridgeData.abs_centeredHeadScore_le_three
          B h m).trans
          (le_max_right _ _)
  have hsq : ‖B.nuisanceStatistic m‖ ^ 2 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs]
    calc
      (∑ c : NuisanceCoord B.HeadIndex,
          |B.nuisanceStatistic m c| ^ 2) ≤
          ∑ _c : NuisanceCoord B.HeadIndex, K ^ 2 := by
        apply Finset.sum_le_sum
        intro c _
        exact pow_le_pow_left₀ (abs_nonneg _) (hcoord c) 2
      _ = (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
        simp
  have hcard : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
  have hsqrt :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sq_sqrt hcard
  have hradiusSq : (B.fixedIntervalNuisanceRadius U) ^ 2 =
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) * K ^ 2 := by
    unfold fixedIntervalNuisanceRadius
    dsimp only [K]
    rw [mul_pow, hsqrt]
  have hnorm0 := norm_nonneg (B.nuisanceStatistic m)
  have hradius0 := B.fixedIntervalNuisanceRadius_nonneg U
  rw [← hradiusSq] at hsq
  nlinarith

/-- A fixed diameter for all actual nuisance patterns in the two physical
pools. -/
def fixedIntervalNuisanceDiameter [Nonempty Head] (U : ℝ) : ℝ :=
  2 * B.fixedIntervalNuisanceRadius U

theorem nuisanceStatistic_distance_le_fixedIntervals [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals) {U : ℝ}
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (i j : B.sampleData.Sample) :
    ‖B.nuisanceStatistic i - B.nuisanceStatistic j‖ ≤
      B.fixedIntervalNuisanceDiameter U := by
  calc
    ‖B.nuisanceStatistic i - B.nuisanceStatistic j‖ ≤
        ‖B.nuisanceStatistic i‖ + ‖B.nuisanceStatistic j‖ := norm_sub_le _ _
    _ ≤ B.fixedIntervalNuisanceRadius U +
        B.fixedIntervalNuisanceRadius U := add_le_add
      (B.nuisanceStatistic_norm_le_fixedIntervals I
        hlowerOne hupperU hlo hhi i)
      (B.nuisanceStatistic_norm_le_fixedIntervals I
        hlowerOne hupperU hlo hhi j)
    _ = B.fixedIntervalNuisanceDiameter U := by
      unfold fixedIntervalNuisanceDiameter
      ring

theorem fixedInterval_separation_pos
    (I : PaperGuardCensus.PhysicalIntervals) :
    0 < Real.log (I.lower .plus) - Real.log (I.upper .minus) := by
  have hminus : I.upper .minus ∈ Set.Ioi (0 : ℝ) :=
    (I.lower_pos .minus).trans (I.lower_lt_upper .minus)
  have hplus : I.lower .plus ∈ Set.Ioi (0 : ℝ) := I.lower_pos .plus
  exact sub_pos.mpr (Real.strictMonoOn_log hminus hplus I.separated)

/-- The uniform baseline nuisance gap specialized to the literal fixed
physical intervals.  Once the common normalized cell-mass margin `lambda`
is supplied by the barycentric active-measure construction, the conclusion
contains no `n`-dependent gap and no limiting covariance. -/
theorem nuisanceCovarianceOperator_zero_fixedIntervals
    [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals) {U lambda : ℝ}
    (hlambda : 0 < lambda)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (x : B.NuisanceSpace) :
    B.uniformNuisanceGap lambda
        (Real.log (I.lower .plus) - Real.log (I.upper .minus))
        (Real.log U) * ‖x‖ ^ 2 ≤
      inner ℝ x (B.nuisanceCovarianceOperator 0 x) := by
  apply B.nuisanceCovarianceOperator_zero_uniform_gap
    hlambda (fixedInterval_separation_pos I) hweight
  · exact B.fixedInterval_cellPhysicalMean_separation I hlo hhi
      B.referenceHead
  · exact B.fixedInterval_abs_cellPhysicalMean_le I
      hlowerOne hupperU hlo hhi

/-- A small `l1` change of the actual finite law preserves half of the
explicit fixed-interval nuisance gap.  The diameter in this theorem is fixed
with the physical constants; unlike the older all-pairs sum, it does not grow
with the number of smooth samples. -/
theorem nuisanceCovarianceOperator_fixedIntervals_half_gap_of_l1
    [Nonempty Head]
    (I : PaperGuardCensus.PhysicalIntervals) {U lambda epsilon : ℝ}
    (hlambda : 0 < lambda)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    (hweight : ∀ c : Cell Head,
      lambda ≤ B.baseline.normalizedCellMass c)
    (xi : B.ParamSpace)
    (hl1 : B.nuisanceFineBaseline.weightL1Distance
      (B.vectorFamily.probabilityMass xi) ≤ epsilon)
    (hsmall : epsilon * B.fixedIntervalNuisanceDiameter U ^ 2 ≤
      B.uniformNuisanceGap lambda
        (Real.log (I.lower .plus) - Real.log (I.upper .minus))
        (Real.log U) / 2)
    (x : B.NuisanceSpace) :
    (B.uniformNuisanceGap lambda
        (Real.log (I.lower .plus) - Real.log (I.upper .minus))
        (Real.log U) / 2) * ‖x‖ ^ 2 ≤
      inner ℝ x (B.nuisanceCovarianceOperator xi x) := by
  let gamma := B.uniformNuisanceGap lambda
    (Real.log (I.lower .plus) - Real.log (I.upper .minus))
    (Real.log U)
  have hbase : gamma * ‖x‖ ^ 2 ≤
      B.nuisanceFineBaseline.covarianceForm x := by
    exact B.nuisanceFineBaseline_uniform_gap hlambda
      (fixedInterval_separation_pos I) hweight
      (B.fixedInterval_cellPhysicalMean_separation I hlo hhi
        B.referenceHead)
      (B.fixedInterval_abs_cellPhysicalMean_le I
        hlowerOne hupperU hlo hhi) x
  have hperturb := B.nuisanceFineBaseline.abs_covarianceForm_reweight_sub_le
    (B.vectorFamily.probabilityMass xi)
    (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi)
    (B.vectorFamily.scalarFamily.probabilityMass_sum xi)
    (B.fixedIntervalNuisanceDiameter U) epsilon
    (B.nuisanceStatistic_distance_le_fixedIntervals I
      hlowerOne hupperU hlo hhi) hl1 x
  have hlower : B.nuisanceFineBaseline.covarianceForm x -
      epsilon * B.fixedIntervalNuisanceDiameter U ^ 2 * ‖x‖ ^ 2 ≤
      (B.nuisanceFineBaseline.reweight
        (B.vectorFamily.probabilityMass xi)
        (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi)
        (B.vectorFamily.scalarFamily.probabilityMass_sum xi)).covarianceForm x := by
    have := neg_le_of_abs_le hperturb
    linarith
  rw [B.nuisanceCovarianceOperator_quadratic]
  have hreweight :
      (B.nuisanceFineBaseline.reweight
        (B.vectorFamily.probabilityMass xi)
        (B.vectorFamily.scalarFamily.probabilityMass_nonneg xi)
        (B.vectorFamily.scalarFamily.probabilityMass_sum xi)).covarianceForm x =
      (B.nuisanceFineAt xi).covarianceForm x := by
    rfl
  rw [← hreweight]
  have herror : epsilon * B.fixedIntervalNuisanceDiameter U ^ 2 *
      ‖x‖ ^ 2 ≤ (gamma / 2) * ‖x‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hsmall (sq_nonneg _)
  linarith

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
