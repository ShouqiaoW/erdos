import Erdos390.Full.PaperExactSchurTwoStageQuadratic

/-!
# Concrete main-coordinate bound for the fast/slow Schur split

This file discharges the finite coordinate comparison left explicit by
`exactSchurGap_of_fastSlow`.  The constant is literal and finite; it may
depend on the fixed arithmetic partition, but it is chosen before the ODE
and no continuum or asymptotic assertion enters its proof.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticBandGeometry PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Sum of the squared actual arithmetic centres over the concrete gauge
coordinates (the low row is recovered from the gauge relation and is not a
coordinate of `MainSpace`). -/
def gaugeCenterSquareSum : ℝ :=
  ∑ j : B.GaugeIndex, B.bandCenter j.1 ^ 2

theorem gaugeCenterSquareSum_nonneg : 0 ≤ B.gaugeCenterSquareSum := by
  unfold gaugeCenterSquareSum
  exact Finset.sum_nonneg fun j hj ↦ sq_nonneg _

/-- Exact Euclidean norm identity for the concrete main coordinates. -/
theorem main_norm_sq_eq_gauge_add_slow (u : B.MainSpace) :
    ‖u‖ ^ 2 =
      (∑ j : B.GaugeIndex, |u (MainCoord.gauge j)| ^ 2) +
        |u MainCoord.slow| ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs]
  let E : MainCoord B.GaugeIndex ≃ B.GaugeIndex ⊕ Unit :=
    { toFun := fun c ↦ match c with
        | .gauge j => Sum.inl j
        | .slow => Sum.inr ()
      invFun := fun s ↦ match s with
        | Sum.inl j => .gauge j
        | Sum.inr _ => .slow
      left_inv := by intro c; cases c <;> rfl
      right_inv := by intro s; cases s with
        | inl j => rfl
        | inr z => cases z; rfl }
  calc
    (∑ c : MainCoord B.GaugeIndex, |u c| ^ 2) =
        ∑ s : B.GaugeIndex ⊕ Unit, |u (E.symm s)| ^ 2 := by
      exact Fintype.sum_equiv E _ _ (fun c ↦ by simp)
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp [E]

/-- Every concrete gauge-coordinate square sum is controlled by the paper
sharp norm and the literal centre-square sum. -/
theorem gauge_coordinate_sum_le_sharp
    (q : B.RawBandGauge) :
    (∑ j : B.GaugeIndex, |q.1 j.1| ^ 2) ≤
      B.gaugeCenterSquareSum *
        paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q ^ 2 := by
  unfold gaugeCenterSquareSum
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hcoord := abs_raw_coordinate_le_paperSharpNorm
    B.harmonicMass B.bandCenter
    (B.partition.center_ne_zero B.n_gt_one) q j.1
  have hcenter : |B.bandCenter j.1| = B.bandCenter j.1 :=
    abs_of_pos (B.bandCenter_pos j.1)
  rw [hcenter] at hcoord
  have hleft0 : 0 ≤ |q.1 j.1| := abs_nonneg _
  have hright0 : 0 ≤ B.bandCenter j.1 *
      paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one) q :=
    mul_nonneg (B.bandCenter_pos j.1).le (norm_nonneg _)
  have hsquare := (sq_le_sq₀ hleft0 hright0).2 hcoord
  nlinarith

/-- A raw-gauge subtraction has the expected triangle bound in the exact
paper sharp norm. -/
theorem paperSharpNorm_sub_smul_le
    (q r : B.RawBandGauge) (lambda : ℝ) :
    paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one) (q - lambda • r) ≤
      paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) q +
        |lambda| * paperSharpNorm B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one) r := by
  unfold paperSharpNorm
  rw [map_sub, map_smul]
  calc
    ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)).symm q -
        lambda •
          (scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one)).symm r‖ ≤
        ‖(scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
          (B.partition.center_ne_zero B.n_gt_one)).symm q‖ +
        ‖lambda •
          (scaleGaugeLinearEquiv B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one)).symm r‖ :=
      norm_sub_le _ _
    _ = _ := by rw [norm_smul, Real.norm_eq_abs]

/-- Explicit coordinate comparison used by the fast/slow coercivity
assembly.  If the first-stage regression has sharp norm at most
`Creg * w`, then the concrete main norm is controlled by the fast sharp
coordinate and the stored slow coordinate with the displayed finite
constant. -/
theorem main_norm_sq_le_fastSharp_add_storedSlow
    (u : B.MainSpace) (qFast qReg : B.RawBandGauge) (lambda Creg : ℝ)
    (hCreg : 0 ≤ Creg)
    (hreg : paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one) qReg ≤ Creg * B.w)
    (hq : B.rawGaugeOfMain u = qFast - lambda • qReg)
    (hslow : u MainCoord.slow = B.w * lambda) :
    ‖u‖ ^ 2 ≤
      (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2)) *
        (paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 +
          (B.w * lambda) ^ 2) := by
  let S : B.RawBandGauge → ℝ := fun q ↦
    paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q
  let A : ℝ := B.gaugeCenterSquareSum
  have hA : 0 ≤ A := B.gaugeCenterSquareSum_nonneg
  have hS (q : B.RawBandGauge) : 0 ≤ S q := norm_nonneg _
  have hw : 0 ≤ B.w := B.w_pos.le
  have hreg' : S qReg ≤ Creg * B.w := hreg
  have hlambdaReg : |lambda| * S qReg ≤
      Creg * |B.w * lambda| := by
    calc
      |lambda| * S qReg ≤ |lambda| * (Creg * B.w) :=
        mul_le_mul_of_nonneg_left hreg' (abs_nonneg _)
      _ = Creg * |B.w * lambda| := by
        rw [abs_mul, abs_of_pos B.w_pos]
        ring
  have hraw : S (B.rawGaugeOfMain u) ≤
      S qFast + Creg * |B.w * lambda| := by
    rw [hq]
    exact (B.paperSharpNorm_sub_smul_le qFast qReg lambda).trans
      (by
        dsimp only [S]
        linarith)
  have hrawSq : S (B.rawGaugeOfMain u) ^ 2 ≤
      2 * S qFast ^ 2 + 2 * Creg ^ 2 * (B.w * lambda) ^ 2 := by
    have hright : 0 ≤ S qFast + Creg * |B.w * lambda| :=
      add_nonneg (hS qFast)
        (mul_nonneg hCreg (abs_nonneg _))
    have hsquare := (sq_le_sq₀ (hS (B.rawGaugeOfMain u)) hright).2 hraw
    calc
      S (B.rawGaugeOfMain u) ^ 2 ≤
          (S qFast + Creg * |B.w * lambda|) ^ 2 := hsquare
      _ ≤ 2 * S qFast ^ 2 +
          2 * (Creg * |B.w * lambda|) ^ 2 := by
        nlinarith [sq_nonneg (S qFast - Creg * |B.w * lambda|)]
      _ = 2 * S qFast ^ 2 +
          2 * Creg ^ 2 * (B.w * lambda) ^ 2 := by
        rw [mul_pow, sq_abs]
        ring
  have hgauge := B.gauge_coordinate_sum_le_sharp (B.rawGaugeOfMain u)
  have hgauge' :
      (∑ j : B.GaugeIndex, |u (MainCoord.gauge j)| ^ 2) ≤
        A * (2 * S qFast ^ 2 +
          2 * Creg ^ 2 * (B.w * lambda) ^ 2) := by
    have hmul := mul_le_mul_of_nonneg_left hrawSq hA
    rw [show (∑ j : B.GaugeIndex,
        |u (MainCoord.gauge j)| ^ 2) =
      ∑ j : B.GaugeIndex, |(B.rawGaugeOfMain u).1 j.1| ^ 2 by
        apply Finset.sum_congr rfl
        intro j hj
        rw [B.rawGaugeOfMain_positive]]
    exact hgauge.trans hmul
  rw [B.main_norm_sq_eq_gauge_add_slow, hslow]
  rw [sq_abs]
  dsimp only [A, S] at hgauge' ⊢
  have hs0 : 0 ≤
      paperSharpNorm B.harmonicMass B.bandCenter
        (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 := sq_nonneg _
  have hwlambda0 : 0 ≤ (B.w * lambda) ^ 2 := sq_nonneg _
  calc
    (∑ j : B.GaugeIndex, |u (MainCoord.gauge j)| ^ 2) +
        (B.w * lambda) ^ 2 ≤
      B.gaugeCenterSquareSum *
          (2 * paperSharpNorm B.harmonicMass B.bandCenter
              (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 +
            2 * Creg ^ 2 * (B.w * lambda) ^ 2) +
          (B.w * lambda) ^ 2 := by
      simpa only [add_comm] using
        add_le_add_right hgauge' ((B.w * lambda) ^ 2)
    _ ≤ (1 + 2 * B.gaugeCenterSquareSum * (1 + Creg ^ 2)) *
        (paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 +
          (B.w * lambda) ^ 2) := by
      have hC2 : 0 ≤ Creg ^ 2 := sq_nonneg _
      have hAx : 0 ≤ B.gaugeCenterSquareSum *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 :=
        mul_nonneg B.gaugeCenterSquareSum_nonneg hs0
      have hAy : 0 ≤ B.gaugeCenterSquareSum * (B.w * lambda) ^ 2 :=
        mul_nonneg B.gaugeCenterSquareSum_nonneg hwlambda0
      have hACx : 0 ≤ B.gaugeCenterSquareSum * Creg ^ 2 *
          paperSharpNorm B.harmonicMass B.bandCenter
            (B.partition.center_ne_zero B.n_gt_one) qFast ^ 2 :=
        mul_nonneg (mul_nonneg B.gaugeCenterSquareSum_nonneg hC2) hs0
      nlinarith

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
