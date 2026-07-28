import Erdos390.Full.PaperEffectiveNorm
import Erdos390.Full.PaperStatisticNorm
import Erdos390.Full.PaperBaselineSlack

/-!
# Dimension-free score control in the paper's effective parameter norm

The Euclidean parameter norm has one coordinate per prime band and is not the
norm used in the non-circular argument of Proposition 8.7.  This file proves
the exact re-expansion of the finite exponential-family score into the
effective prime fugacities and the fixed nuisance block.  It then obtains a
pointwise score bound whose constant is independent of the number of bands.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit
namespace BridgeData

open ArithmeticModel ArithmeticBandGeometry
open Erdos390.Full.PaperStatisticNorm
open Erdos390.Full.PaperStatisticNorm.BridgeData

noncomputable section

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Reconstructing all band coefficients from the quotient gauge gives
exactly the gauge part of the exponential score. -/
theorem sum_bandParameter_mul_bandScore_eq_gauge
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    (∑ j : Band, B.bandParameter xi j * B.bandScore j m) =
      ∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) * B.gaugeScore k m := by
  rw [Fintype.sum_eq_add_sum_subtype_ne
    (fun j : Band => B.bandParameter xi j * B.bandScore j m) B.lowBand]
  simp only [B.bandParameter_low, B.bandParameter_gauge]
  unfold gaugeScore
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hfactor :
      (∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) *
          (B.lowRatio k * B.bandScore B.lowBand m)) =
        (∑ k : B.GaugeIndex,
          B.lowRatio k * xi (MomentCoord.gauge k)) *
            B.bandScore B.lowBand m := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  rw [hfactor]
  ring

/-- Fiberwise expansion of a band-linear valuation statistic into its
individual prime coefficients. -/
theorem sum_bandParameter_mul_bandScore_eq_primeSum
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    (∑ j : Band, B.bandParameter xi j * B.bandScore j m) =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.bandParameter xi (B.partition.band p) *
          valuation p.1 (B.sampleData.value m) := by
  unfold bandScore
  rw [← Finset.sum_fiberwise Finset.univ B.partition.band
    (fun p => B.bandParameter xi (B.partition.band p) *
      valuation p.1 (B.sampleData.value m))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hpj : B.partition.band p = j := (Finset.mem_filter.mp hp).2
  rw [hpj]

/-- Exact main-score identity: quotient-gauge plus compensated slow score is
the valuation sum with the literal effective prime fugacity. -/
theorem gaugeSlowScore_eq_effectivePrimeSum
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    (∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) * B.gaugeScore k m) +
        xi MomentCoord.slow * (B.slowScore m / B.w) =
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m) := by
  rw [← B.sum_bandParameter_mul_bandScore_eq_gauge xi m,
    B.sum_bandParameter_mul_bandScore_eq_primeSum xi m]
  unfold effectivePrimeCoefficient slowScore
  simp_rw [add_mul]
  rw [Finset.sum_add_distrib]
  apply congrArg₂ (· + ·)
  · rfl
  · have hdiv :
        xi MomentCoord.slow *
            ((∑ p : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation p *
                valuation p.1 (B.sampleData.value m)) / B.w) =
          (xi MomentCoord.slow / B.w) *
            (∑ p : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation p *
                valuation p.1 (B.sampleData.value m)) := by
        field_simp [ne_of_gt B.w_pos]
    rw [hdiv, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    ring

/-- Canonical splitting of the quotient/slow coordinate sum. -/
private def mainCoordEquiv (Gauge : Type*) :
    MainCoord Gauge ≃ Gauge ⊕ Unit where
  toFun
    | .gauge j => Sum.inl j
    | .slow => Sum.inr ()
  invFun
    | Sum.inl j => .gauge j
    | Sum.inr _ => .slow
  left_inv c := by cases c <;> rfl
  right_inv
    | Sum.inl j => rfl
    | Sum.inr () => rfl

private theorem sum_mainCoord {Gauge : Type*} [Fintype Gauge]
    (f : MainCoord Gauge → ℝ) :
    (∑ c : MainCoord Gauge, f c) =
      (∑ j : Gauge, f (.gauge j)) + f .slow := by
  calc
    (∑ c : MainCoord Gauge, f c) =
        ∑ s : Gauge ⊕ Unit, f ((mainCoordEquiv Gauge).symm s) := by
      exact Fintype.sum_equiv (mainCoordEquiv Gauge) f
        (fun s => f ((mainCoordEquiv Gauge).symm s)) (fun c => by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [mainCoordEquiv]

/-- The actual exponential score decomposes into its effective-prime and
fixed-dimensional nuisance parts. -/
theorem vectorScore_eq_effectivePrime_add_nuisance [Nonempty Head]
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    B.vectorFamily.scalarFamily.score m xi =
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)) +
      inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) := by
  simp only [VectorExponentialFamily.scalarFamily, innerSL_apply_apply]
  rw [PiLp.inner_apply]
  change (∑ c : B.Coord, xi c * B.statistic m c) = _
  rw [B.sum_coord_split]
  have hmain :
      (∑ c : MainCoord B.GaugeIndex,
        xi (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow) *
        B.statistic m (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow)) =
      (∑ k : B.GaugeIndex,
        xi (MomentCoord.gauge k) * B.gaugeScore k m) +
        xi MomentCoord.slow * (B.slowScore m / B.w) := by
    rw [sum_mainCoord]
    simp [rawStatistic, coordScale]
  have hnuisance :
      (∑ c : NuisanceCoord B.HeadIndex,
        xi (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h) *
        B.statistic m (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h)) =
      inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) := by
    rw [PiLp.inner_apply]
    change _ = ∑ c : NuisanceCoord B.HeadIndex,
      B.nuisanceStatistic m c * B.nuisanceParameter xi c
    apply Finset.sum_congr rfl
    intro c hc
    cases c <;> simp [rawStatistic, coordScale] <;> ring
  calc
    (∑ c : MainCoord B.GaugeIndex,
        xi (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow) *
        B.statistic m (match c with
          | .gauge j => MomentCoord.gauge j
          | .slow => MomentCoord.slow)) +
      ∑ c : NuisanceCoord B.HeadIndex,
        xi (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h) *
        B.statistic m (match c with
          | .physical => MomentCoord.physical
          | .head h => MomentCoord.head h) =
        ((∑ k : B.GaugeIndex,
          xi (MomentCoord.gauge k) * B.gaugeScore k m) +
          xi MomentCoord.slow * (B.slowScore m / B.w)) +
          inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m) :=
      congrArg₂ (· + ·) hmain hnuisance
    _ = _ := by rw [B.gaugeSlowScore_eq_effectivePrimeSum]

/-! ## Dimension-free pointwise bounds -/

/-- Fixed-dimensional normalized envelope for the physical/head nuisance
statistic.  It depends on the fixed head set, but not on the prime mesh. -/
def nuisanceStatisticCoefficient (C : ℝ) : ℝ :=
  Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
    max (physicalLogCoefficient C) (3 / Real.log 2)

theorem nuisanceStatisticCoefficient_nonneg {C : ℝ} (hC : 1 ≤ C) :
    0 ≤ B.nuisanceStatisticCoefficient C := by
  unfold nuisanceStatisticCoefficient
  exact mul_nonneg (Real.sqrt_nonneg _)
    (le_max_left _ _ |>.trans' (physicalLogCoefficient_nonneg hC))

theorem abs_nuisanceStatistic_apply_le [Nonempty Head]
    {C : ℝ} (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) (c : NuisanceCoord B.HeadIndex) :
    |B.nuisanceStatistic m c| ≤
      max (physicalLogCoefficient C) (3 / Real.log 2) * B.L := by
  cases c with
  | physical =>
      exact (abs_physicalScore_le B hC hhi m).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) B.L_pos.le)
  | head h =>
      exact (abs_centeredHeadScore_le_three B h m).trans
        ((three_le_headCoefficient_mul_L B).trans
          (mul_le_mul_of_nonneg_right (le_max_right _ _) B.L_pos.le))

/-- Euclidean norm bound for the nuisance statistic; its dimension is fixed
by the head simplex and does not grow with the prime mesh. -/
theorem nuisanceStatistic_norm_le [Nonempty Head]
    {C : ℝ} (hC : 1 ≤ C)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (m : B.sampleData.Sample) :
    ‖B.nuisanceStatistic m‖ ≤
      B.nuisanceStatisticCoefficient C * B.L := by
  let K : ℝ := max (physicalLogCoefficient C) (3 / Real.log 2)
  have hK0 : 0 ≤ K :=
    (physicalLogCoefficient_nonneg hC).trans (le_max_left _ _)
  have hKL0 : 0 ≤ K * B.L := mul_nonneg hK0 B.L_pos.le
  have hsum : ‖B.nuisanceStatistic m‖ ^ 2 ≤
      ∑ _c : NuisanceCoord B.HeadIndex, (K * B.L) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
    apply Finset.sum_le_sum
    intro c hc
    simpa only [sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (B.nuisanceStatistic m c))
        (by simpa only [K] using B.abs_nuisanceStatistic_apply_le hC hhi m c) 2
  have hcard0 : 0 ≤
      (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) := by positivity
  have hsqrt :
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) :=
    Real.sq_sqrt hcard0
  have hsumEq :
      (∑ _c : NuisanceCoord B.HeadIndex, (K * B.L) ^ 2) =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (K * B.L) ^ 2 := by simp
  have htargetSq :
      (B.nuisanceStatisticCoefficient C * B.L) ^ 2 =
        (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
          (K * B.L) ^ 2 := by
    unfold nuisanceStatisticCoefficient
    dsimp only [K]
    rw [mul_assoc]
    nlinarith
  have htarget0 : 0 ≤ B.nuisanceStatisticCoefficient C * B.L :=
    mul_nonneg (B.nuisanceStatisticCoefficient_nonneg hC) B.L_pos.le
  rw [hsumEq] at hsum
  have hsq : ‖B.nuisanceStatistic m‖ ^ 2 ≤
      (B.nuisanceStatisticCoefficient C * B.L) ^ 2 := by
    rw [htargetSq]
    exact hsum
  nlinarith [norm_nonneg (B.nuisanceStatistic m)]

/-- The prime part of the literal score is controlled by the largest
effective fugacity times the actual total band valuation. -/
theorem abs_effectivePrimeSum_le
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)| ≤
      ‖fun p => B.effectivePrimeCoefficient xi p‖ *
        (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
          valuation p (B.sampleData.value m)) := by
  calc
    |∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)| ≤
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        |B.effectivePrimeCoefficient xi p *
          valuation p.1 (B.sampleData.value m)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        ‖fun q => B.effectivePrimeCoefficient xi q‖ *
          valuation p.1 (B.sampleData.value m) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [abs_mul, abs_of_nonneg (valuation_nonneg p.1 _)]
      exact mul_le_mul_of_nonneg_right
        (by
          simpa only [Real.norm_eq_abs] using
            (norm_le_pi_norm
              (fun q : BandPrime B.sampleData.n B.sampleData.W =>
                B.effectivePrimeCoefficient xi q) p))
        (valuation_nonneg p.1 _)
    _ = ‖fun q => B.effectivePrimeCoefficient xi q‖ *
        (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
          valuation p (B.sampleData.value m)) := by
      rw [← Finset.mul_sum]
      congr 1
      simpa only [Finset.univ_eq_attach] using
        (Finset.sum_attach
          (primeBand B.sampleData.n B.sampleData.W)
          (fun p ↦ valuation p (B.sampleData.value m)))

/-- The actual score is bounded in the effective paper norm with no loss
depending on the number of prime bands. -/
theorem abs_vectorScore_div_L_le_paperEffectiveSize [Nonempty Head]
    {C : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (xi : B.ParamSpace) (m : B.sampleData.Sample) :
    |B.vectorFamily.scalarFamily.score m xi / B.L| ≤
      (valuationLogCoefficient C B.sampleData.W +
        B.nuisanceStatisticCoefficient C) * B.paperEffectiveSize xi := by
  let E : ℝ := ‖fun p => B.effectivePrimeCoefficient xi p‖
  let Z : ℝ := ‖B.nuisanceParameter xi‖
  let Kp : ℝ := valuationLogCoefficient C B.sampleData.W
  let Kz : ℝ := B.nuisanceStatisticCoefficient C
  have hE0 : 0 ≤ E := norm_nonneg _
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hKp0 : 0 ≤ Kp := valuationLogCoefficient_nonneg hC hW
  have hKz0 : 0 ≤ Kz := B.nuisanceStatisticCoefficient_nonneg hC
  have hprime :
      |∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.effectivePrimeCoefficient xi p *
            valuation p.1 (B.sampleData.value m)| ≤ E * Kp * B.L := by
    calc
      |∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.effectivePrimeCoefficient xi p *
            valuation p.1 (B.sampleData.value m)| ≤
          ‖fun p => B.effectivePrimeCoefficient xi p‖ *
            (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
              valuation p (B.sampleData.value m)) :=
        B.abs_effectivePrimeSum_le xi m
      _ ≤ E * (Kp * B.L) := by
        simpa only [E, Kp] using
          (mul_le_mul_of_nonneg_left
            (totalBandValuation_le B hC hW hhi m) hE0)
      _ = E * Kp * B.L := by ring
  have hnuisance :
      |inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m)| ≤
        Z * Kz * B.L := by
    calc
      |inner ℝ (B.nuisanceParameter xi) (B.nuisanceStatistic m)| ≤
          ‖B.nuisanceParameter xi‖ * ‖B.nuisanceStatistic m‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ Z * (Kz * B.L) :=
        mul_le_mul_of_nonneg_left
          (B.nuisanceStatistic_norm_le hC hhi m) hZ0
      _ = Z * Kz * B.L := by ring
  have hscore :
      |B.vectorFamily.scalarFamily.score m xi| ≤
        (Kp + Kz) * B.paperEffectiveSize xi * B.L := by
    rw [B.vectorScore_eq_effectivePrime_add_nuisance xi m]
    calc
      |_ + _| ≤ |_| + |_| := abs_add_le _ _
      _ ≤ E * Kp * B.L + Z * Kz * B.L := add_le_add hprime hnuisance
      _ ≤ (Kp + Kz) * B.paperEffectiveSize xi * B.L := by
        have hEle : E ≤ B.paperEffectiveSize xi := by
          unfold E paperEffectiveSize
          linarith [norm_nonneg (B.nuisanceParameter xi),
            abs_nonneg (xi MomentCoord.slow)]
        have hZle : Z ≤ B.paperEffectiveSize xi := by
          unfold Z paperEffectiveSize
          linarith [norm_nonneg
            (fun p => B.effectivePrimeCoefficient xi p),
            abs_nonneg (xi MomentCoord.slow)]
        have hL0 := B.L_pos.le
        have hcoeff : E * Kp + Z * Kz ≤
            B.paperEffectiveSize xi * (Kp + Kz) := by
          calc
            E * Kp + Z * Kz ≤
                B.paperEffectiveSize xi * Kp +
                  B.paperEffectiveSize xi * Kz :=
              add_le_add
                (mul_le_mul_of_nonneg_right hEle hKp0)
                (mul_le_mul_of_nonneg_right hZle hKz0)
            _ = B.paperEffectiveSize xi * (Kp + Kz) := by ring
        calc
          E * Kp * B.L + Z * Kz * B.L =
              (E * Kp + Z * Kz) * B.L := by ring
          _ ≤ (B.paperEffectiveSize xi * (Kp + Kz)) * B.L :=
            mul_le_mul_of_nonneg_right hcoeff hL0
          _ = (Kp + Kz) * B.paperEffectiveSize xi * B.L := by ring
  rw [abs_div, abs_of_pos B.L_pos]
  apply (div_le_iff₀ B.L_pos).2
  simpa only [Kp, Kz, E, Z, mul_assoc] using hscore

/-- Effective-ball form consumed by the feasibility and baseline-slack
layers of Proposition 8.7. -/
theorem effectiveScoreBound_of_paperEffectiveSize [Nonempty Head]
    {C a : ℝ} (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a) :
    ∀ m : B.sampleData.Sample,
      |B.vectorFamily.scalarFamily.score m xi / B.L| ≤
        (valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * a := by
  intro m
  exact (B.abs_vectorScore_div_L_le_paperEffectiveSize hC hW hhi xi m).trans
    (mul_le_mul_of_nonneg_left hxi
      (add_nonneg (valuationLogCoefficient_nonneg hC hW)
        (B.nuisanceStatisticCoefficient_nonneg hC)))

/-- Literal natural-coordinate feasibility from the paper effective box and
the two proved `O(1/L)` ledgers.  Unlike the earlier Euclidean corollary, its
constant does not grow with the number of prime bands. -/
theorem ambientCombinedWeight_mem_Icc_of_paperEffectiveSize
    [Nonempty Head]
    {C a Cfixed Cactive : ℝ}
    (hC : 1 ≤ C) (hW : 1 < B.sampleData.W)
    (hhi : ∀ sigma, B.sampleData.hi sigma ≤
      physicalBound C B.sampleData.n)
    (hsep : B.sampleData.HeadPatternsSeparated)
    (frozenWeight : ℕ → ℝ)
    (hfrozenFeasible : ∀ x, frozenWeight x ∈ Set.Icc (0 : ℝ) 1)
    (xi : B.ParamSpace) (hxi : B.paperEffectiveSize xi ≤ a)
    (hfrozen : ∀ m : B.sampleData.Sample,
      frozenWeight (B.sampleData.value m) ≤ Cfixed / B.L)
    (hactive : ∀ m : B.sampleData.Sample,
      B.baseline.baseWeight m ≤ Cactive / B.L)
    (hlarge : Cfixed +
      Real.exp (2 *
        ((valuationLogCoefficient C B.sampleData.W +
          B.nuisanceStatisticCoefficient C) * a)) * Cactive ≤ B.L) :
    ∀ x : ℕ,
      B.ambientCombinedWeight frozenWeight xi x ∈ Set.Icc (0 : ℝ) 1 := by
  let R := (valuationLogCoefficient C B.sampleData.W +
    B.nuisanceStatisticCoefficient C) * a
  apply B.ambientCombinedWeight_mem_Icc_of_effectiveScoreBound
    hsep frozenWeight hfrozenFeasible xi R
      (B.effectiveScoreBound_of_paperEffectiveSize hC hW hhi xi hxi)
  exact B.combinedBaselineSlack_of_div_log_bounds frozenWeight
    Cfixed Cactive R hfrozen hactive (by simpa only [R] using hlarge)

end

end BridgeData
end Erdos390.Full.PaperBridgeFit
