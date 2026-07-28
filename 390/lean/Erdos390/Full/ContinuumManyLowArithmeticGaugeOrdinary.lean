import Erdos390.Full.ContinuumManyLowProjectedRawInverse

/-!
# Ordinary continuum inverse on a varying arithmetic gauge

The continuum graph is reversible for the continuum weight, whereas the
literal prime partition is projected with the arithmetic mass and centre.
This file performs that change of gauge without dividing by the least cell
centre.  The defect is measured in the raw weights `H * alpha`, and the
input gauge is represented exactly by the mixed weight
`H_a * alpha_a * alpha_c`.
-/

open scoped BigOperators
open Set

noncomputable section

set_option maxHeartbeats 800000

namespace Erdos390.Full.ContinuumCellGraph
namespace ArithmeticGaugeOrdinary

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteReversibleGraph
open FiniteRawLowDiagonal
open MovingLowGaugeTransfer
open PaperWeightedInverseExport

variable {Band Low High : Type*} [Fintype Band]
  [Fintype Low] [Fintype High]

/-- A raw weighted projection is bounded in ordinary norm by a scaled
first-moment/centre-energy ratio.  The scale `alphaMax` is explicit; in the
paper all centres are at most one. -/
theorem weightedGaugeProjection_norm_le_of_scaled_moment_ratio
    [Nonempty Band]
    (H alpha x : Band → ℝ) {alphaMax C R : ℝ}
    (hH : ∀ i, 0 ≤ H i)
    (hAlpha : ∀ i, 0 ≤ alpha i)
    (hAlphaUpper : ∀ i, alpha i ≤ alphaMax)
    (hTotal : 0 < sharpWeightTotal H alpha)
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hx : ∀ i, |x i| ≤ C)
    (hRatio : alphaMax * (∑ i : Band, H i * alpha i) ≤
      R * sharpWeightTotal H alpha) :
    ‖weightedGaugeProjection H alpha x‖ ≤ (1 + R) * C := by
  let total : ℝ := sharpWeightTotal H alpha
  let numerator : ℝ := ∑ i : Band, H i * alpha i * x i
  have hMoment : 0 ≤ ∑ i : Band, H i * alpha i :=
    Finset.sum_nonneg fun i _ ↦ mul_nonneg (hH i) (hAlpha i)
  have hAlphaMax : 0 ≤ alphaMax :=
    (hAlpha (Classical.choice (inferInstance : Nonempty Band))).trans
      (hAlphaUpper (Classical.choice (inferInstance : Nonempty Band)))
  have hnum : |numerator| ≤ C * (∑ i : Band, H i * alpha i) := by
    dsimp only [numerator]
    calc
      |∑ i : Band, H i * alpha i * x i| ≤
          ∑ i : Band, |H i * alpha i * x i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Band, C * (H i * alpha i) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul, abs_mul, abs_of_nonneg (hH i),
          abs_of_nonneg (hAlpha i)]
        calc
          H i * alpha i * |x i| ≤ (H i * alpha i) * C :=
            mul_le_mul_of_nonneg_left (hx i)
              (mul_nonneg (hH i) (hAlpha i))
          _ = C * (H i * alpha i) := by ring
      _ = C * (∑ i : Band, H i * alpha i) := by
        rw [Finset.mul_sum]
  have hmeanScaled : alphaMax * |numerator / total| ≤ R * C := by
    have ht : 0 < total := hTotal
    rw [abs_div, abs_of_pos ht]
    calc
      alphaMax * (|numerator| / total) ≤
          alphaMax * ((C * (∑ i : Band, H i * alpha i)) / total) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right hnum ht.le) hAlphaMax
      _ = C * (alphaMax * (∑ i : Band, H i * alpha i)) / total := by
        ring
      _ ≤ C * (R * total) / total := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hC) ht.le
      _ = R * C := by
        field_simp [ht.ne']
  have hbound : 0 ≤ (1 + R) * C := by positivity
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro i
  rw [Real.norm_eq_abs]
  unfold weightedGaugeProjection
  change |x i - alpha i * (numerator / total)| ≤ _
  calc
    |x i - alpha i * (numerator / total)| ≤
        |x i| + alpha i * |numerator / total| := by
      calc
        |x i - alpha i * (numerator / total)| ≤
            |x i| + |alpha i * (numerator / total)| := abs_sub _ _
        _ = |x i| + alpha i * |numerator / total| := by
          rw [abs_mul, abs_of_nonneg (hAlpha i)]
    _ ≤ C + alphaMax * |numerator / total| :=
      add_le_add (hx i)
        (mul_le_mul_of_nonneg_right (hAlphaUpper i) (abs_nonneg _))
    _ ≤ C + R * C := add_le_add le_rfl hmeanScaled
    _ = (1 + R) * C := by ring

/-- If a vector has zero continuum raw moment, changing to the arithmetic
raw projection moves it by at most the displayed raw-weight defect.  This
is the exact place where the two varying gauges are compared. -/
theorem weightedGaugeProjection_sub_self_norm_le_of_rawWeightDefect
    [Nonempty Band]
    (H alpha Hc alphac g : Band → ℝ)
    {alphaMax rho : ℝ}
    (hAlpha : ∀ i, 0 ≤ alpha i)
    (hAlphaUpper : ∀ i, alpha i ≤ alphaMax)
    (hTotal : 0 < sharpWeightTotal H alpha)
    (hContinuumMoment : ∑ i : Band, Hc i * alphac i * g i = 0)
    (hDefect : alphaMax *
        (∑ i : Band, |H i * alpha i - Hc i * alphac i|) ≤
      rho * sharpWeightTotal H alpha) :
    ‖weightedGaugeProjection H alpha g - g‖ ≤ rho * ‖g‖ := by
  let total : ℝ := sharpWeightTotal H alpha
  let numerator : ℝ := ∑ i : Band, H i * alpha i * g i
  let defect : ℝ :=
    ∑ i : Band, |H i * alpha i - Hc i * alphac i|
  have hAlphaMax : 0 ≤ alphaMax :=
    (hAlpha (Classical.choice (inferInstance : Nonempty Band))).trans
      (hAlphaUpper (Classical.choice (inferInstance : Nonempty Band)))
  have hDefectNonneg : 0 ≤ defect := by
    dsimp only [defect]
    exact Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  have hNumIdentity : numerator =
      ∑ i : Band, (H i * alpha i - Hc i * alphac i) * g i := by
    dsimp only [numerator]
    rw [show (∑ i : Band, H i * alpha i * g i) =
        (∑ i : Band, (H i * alpha i - Hc i * alphac i) * g i) +
          ∑ i : Band, Hc i * alphac i * g i by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring]
    rw [hContinuumMoment, add_zero]
  have hNum : |numerator| ≤ defect * ‖g‖ := by
    rw [hNumIdentity]
    calc
      |∑ i : Band, (H i * alpha i - Hc i * alphac i) * g i| ≤
          ∑ i : Band, |(H i * alpha i - Hc i * alphac i) * g i| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Band,
          |H i * alpha i - Hc i * alphac i| * ‖g‖ := by
        apply Finset.sum_le_sum
        intro i hi
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left
          (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm g i)
          (abs_nonneg _)
      _ = defect * ‖g‖ := by
        dsimp only [defect]
        rw [Finset.sum_mul]
  have hRhoNonneg : 0 ≤ rho := by
    have hleft : 0 ≤ alphaMax * defect :=
      mul_nonneg hAlphaMax hDefectNonneg
    have hright : 0 ≤ rho * total := hleft.trans (by
      simpa only [defect, total] using hDefect)
    nlinarith [hTotal]
  have hbound : 0 ≤ rho * ‖g‖ := mul_nonneg hRhoNonneg (norm_nonneg _)
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro i
  rw [Real.norm_eq_abs]
  unfold weightedGaugeProjection
  change |g i - alpha i * (numerator / total) - g i| ≤ _
  rw [sub_sub_cancel_left, abs_neg, abs_mul,
    abs_of_nonneg (hAlpha i), abs_div, abs_of_pos hTotal]
  calc
    alpha i * (|numerator| / total) ≤
        alphaMax * ((defect * ‖g‖) / total) := by
      exact mul_le_mul (hAlphaUpper i)
        (div_le_div_of_nonneg_right hNum hTotal.le)
        (by positivity) hAlphaMax
    _ = (alphaMax * defect / total) * ‖g‖ := by ring
    _ ≤ rho * ‖g‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (div_le_iff₀ hTotal).2
      simpa only [total, defect] using hDefect

namespace IntervalMesh

variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Deterministic many-low inverse for an endpoint arithmetic raw operator.
The input and output live on the literal arithmetic gauge.  The continuum
graph enters only through explicit row, residual, and raw-weight errors;
neither the number of low cells nor their least centre occurs. -/
theorem ordinary_split_arithmetic_projected_raw_bound
    [DecidableEq Band] [Nonempty Band] [Nonempty High]
    (e : Sum Low High ≃ Band)
    (diagonalA : Band → ℝ) (kernelA : Band → Band → ℝ)
    (H alphaA : Band → ℝ)
    {C kappa amin amax alphaAMax lowCenter lowLength totalLength
      gaugeRatio d residual rowError R rho : ℝ}
    (hC : 0 ≤ C)
    (hKernel : ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      |covarianceKernel s t| ≤ C * s * t)
    (hkappa : 0 < kappa)
    (hgap : ∀ s ∈ Icc (0 : ℝ) 1,
      ∀ t ∈ Icc epsilon (1 - epsilon),
        kappa ≤ -covarianceKernelQuotient t s)
    (hAnchorMassPos : 0 < ∑ i : High, M.splitHighAnchor e i)
    (hAmin : 0 < amin)
    (hHighCenterLower : ∀ i : High, amin ≤ M.center (e (.inr i)))
    (hHighCenterUpper : ∀ i : High, M.center (e (.inr i)) ≤ amax)
    (hAmax : 0 ≤ amax)
    (hLowCenterNonneg : 0 ≤ lowCenter)
    (hLowCenter : ∀ l : Low, M.center (e (.inl l)) ≤ lowCenter)
    (hLowLengthNonneg : 0 ≤ lowLength)
    (hLowLength : ∑ l : Low, M.length (e (.inl l)) ≤ lowLength)
    (hTotalLengthNonneg : 0 ≤ totalLength)
    (hTotalLength : ∑ i : Band, M.length i ≤ totalLength)
    (hH : ∀ i, 0 < H i) (hAlphaA : ∀ i, 0 < alphaA i)
    (hAlphaAUpper : ∀ i, alphaA i ≤ alphaAMax)
    (hMixedGaugeRatio :
      (∑ l : Low, H (e (.inl l)) * alphaA (e (.inl l))) ≤
        gaugeRatio *
          (∑ i : High, H (e (.inr i)) * alphaA (e (.inr i)) *
            M.center (e (.inr i))))
    (hdOne : d < 1)
    (hDiagonalLow : ∀ l : Low,
      |M.normalizedDiagonalCell (e (.inl l)) - 1| ≤ d)
    (hResidualNonneg : 0 ≤ residual)
    (hResidual : ∀ i : Band, |M.rowResidual i| ≤ residual)
    (hRowErrorNonneg : 0 ≤ rowError)
    (hRowError : ∀ b : RawGaugeSpace H alphaA, ∀ i : Band,
      |rawOperator diagonalA kernelA b.1 i -
          rawOperator M.normalizedDiagonalCell M.normalizedKernelCell
            b.1 i| ≤ rowError * ‖b‖)
    (hR : 0 ≤ R)
    (hMomentRatio : alphaAMax * (∑ i : Band, H i * alphaA i) ≤
      R * sharpWeightTotal H alphaA)
    (hRhoHalf : rho ≤ 1 / 2)
    (hRawWeightDefect : alphaAMax *
        (∑ i : Band,
          |H i * alphaA i - M.harmonicMass i * M.center i|) ≤
      rho * sharpWeightTotal H alphaA)
    (hAbsorbLow :
      let epsLow :=
        (residual + C * lowCenter * totalLength) / (1 - d)
      max epsLow
        (amax *
          (2 * (1 / (kappa *
              ∑ i : High, M.splitHighAnchor e i)) *
              ((C * lowCenter * lowLength) / amin +
                (C * lowLength) * epsLow) +
            gaugeRatio * epsLow)) ≤ 1 / 2)
    (hAbsorbArithmetic :
      let Clow := 1 / (1 - d)
      let Cmain :=
        max Clow
          (amax *
            (2 * (1 / (kappa *
                ∑ i : High, M.splitHighAnchor e i)) *
                (1 / amin + (C * lowLength) * Clow) +
              gaugeRatio * Clow))
      4 * Cmain * ((1 + R) * (rowError + residual)) ≤ 1 / 2)
    (b : RawGaugeSpace H alphaA) :
    ‖b‖ ≤
      (8 *
        max (1 / (1 - d))
          (amax *
            (2 * (1 / (kappa *
                ∑ i : High, M.splitHighAnchor e i)) *
                (1 / amin +
                  (C * lowLength) * (1 / (1 - d))) +
              gaugeRatio * (1 / (1 - d))))) *
        ‖projectedRawLinearMap diagonalA kernelA H alphaA
          (ne_of_gt (by
            unfold sharpWeightTotal sharpWeight
            apply Finset.sum_pos
            · intro i _hi
              exact mul_pos (hH i) (sq_pos_of_pos (hAlphaA i))
            · exact Finset.univ_nonempty)) b‖ := by
  let totalA : ℝ := sharpWeightTotal H alphaA
  have hTotalA : 0 < totalA := by
    dsimp only [totalA, sharpWeightTotal, sharpWeight]
    apply Finset.sum_pos
    · intro i hi
      exact mul_pos (hH i) (sq_pos_of_pos (hAlphaA i))
    · exact Finset.univ_nonempty
  let qBand : Band → ℝ := fun i ↦ b.1 i / M.center i
  let q : Sum Low High → ℝ := fun x ↦ qBand (e x)
  let graph : Band → ℝ := fun i ↦
    M.center i * graphOperator M.sharpKernelEdge qBand i
  let continuumRaw : Band → ℝ :=
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b.1
  let arithmeticRaw : Band → ℝ := rawOperator diagonalA kernelA b.1
  let projected : Band → ℝ :=
    weightedGaugeProjection H alphaA arithmeticRaw
  let B : ℝ := ‖b‖
  let G : ℝ := ‖projected‖
  let E : ℝ := rowError + residual
  let Ggraph : ℝ := 2 * G + 2 * ((1 + R) * E) * B
  let Clow : ℝ := 1 / (1 - d)
  let epsLow : ℝ :=
    (residual + C * lowCenter * totalLength) / (1 - d)
  let Cmain : ℝ :=
    max Clow
      (amax *
        (2 * (1 / (kappa *
            ∑ i : High, M.splitHighAnchor e i)) *
            (1 / amin + (C * lowLength) * Clow) +
          gaugeRatio * Clow))
  have hB : 0 ≤ B := norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
  have hE : 0 ≤ E := add_nonneg hRowErrorNonneg hResidualNonneg
  have hGgraph : 0 ≤ Ggraph := by dsimp only [Ggraph]; positivity
  have hClow : 0 ≤ Clow := by
    dsimp only [Clow]
    exact one_div_nonneg.mpr (sub_pos.mpr hdOne).le
  have hepsLow : 0 ≤ epsLow := by
    dsimp only [epsLow]
    exact div_nonneg
      (add_nonneg hResidualNonneg
        (mul_nonneg (mul_nonneg hC hLowCenterNonneg)
          hTotalLengthNonneg))
      (sub_pos.mpr hdOne).le
  have hCmain : 0 ≤ Cmain :=
    hClow.trans (by dsimp only [Cmain]; exact le_max_left _ _)
  have hbPoint (i : Band) : |b.1 i| ≤ B := by
    dsimp only [B]
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm b.1 i
  have hqScale (i : Band) : M.center i * qBand i = b.1 i := by
    dsimp only [qBand]
    field_simp [ne_of_gt (M.center_pos i)]
  have hContinuumDecomp : continuumRaw = graph +
      fun i ↦ M.rowResidual i * b.1 i := by
    funext i
    have h := M.rawOperator_eq_scaledGraph_add_residual b.1 i
    simpa only [continuumRaw, graph, qBand] using h
  have hGraphContinuumMoment :
      ∑ i : Band, M.harmonicMass i * M.center i * graph i = 0 := by
    dsimp only [graph]
    calc
      (∑ i : Band, M.harmonicMass i * M.center i *
          (M.center i * graphOperator M.sharpKernelEdge qBand i)) =
        ∑ i : Band, (M.harmonicMass i * M.center i ^ 2) *
          graphOperator M.sharpKernelEdge qBand i := by
            apply Finset.sum_congr rfl
            intro i _hi
            ring
      _ = 0 := weighted_sum_graphOperator_eq_zero M.sharpKernelEdge
        (fun i ↦ M.harmonicMass i * M.center i ^ 2) qBand
        M.sharpKernelEdge_detailedBalance
  have hProjectionDefect :
      ‖weightedGaugeProjection H alphaA graph - graph‖ ≤ rho * ‖graph‖ := by
    exact weightedGaugeProjection_sub_self_norm_le_of_rawWeightDefect
      H alphaA M.harmonicMass M.center graph
      (fun i ↦ (hAlphaA i).le) hAlphaAUpper hTotalA
      hGraphContinuumMoment hRawWeightDefect
  let z : Band → ℝ := arithmeticRaw - graph
  have hzPoint (i : Band) : |z i| ≤ E * B := by
    have hrow := hRowError b i
    have hres := hResidual i
    have hdecomp := congrFun hContinuumDecomp i
    simp only [Pi.add_apply] at hdecomp
    dsimp only [z, arithmeticRaw, Pi.sub_apply]
    have hid : arithmeticRaw i - graph i =
        (arithmeticRaw i - continuumRaw i) + M.rowResidual i * b.1 i := by
      rw [hdecomp]
      ring
    rw [hid]
    calc
      |arithmeticRaw i - continuumRaw i + M.rowResidual i * b.1 i| ≤
          |arithmeticRaw i - continuumRaw i| +
            |M.rowResidual i * b.1 i| := abs_add_le _ _
      _ ≤ rowError * B + residual * B := by
        rw [abs_mul]
        exact add_le_add (by simpa only [arithmeticRaw, continuumRaw, B]
          using hrow)
          (mul_le_mul hres (hbPoint i) (abs_nonneg _)
            hResidualNonneg)
      _ = E * B := by dsimp only [E]; ring
  have hzProjected :
      ‖weightedGaugeProjection H alphaA z‖ ≤ (1 + R) * (E * B) := by
    exact weightedGaugeProjection_norm_le_of_scaled_moment_ratio
      H alphaA z (fun i ↦ (hH i).le) (fun i ↦ (hAlphaA i).le)
      hAlphaAUpper hTotalA (mul_nonneg hE hB) hR hzPoint hMomentRatio
  have hProjectedDecomp : projected =
      weightedGaugeProjection H alphaA graph +
        weightedGaugeProjection H alphaA z := by
    have harith : arithmeticRaw = graph + z := by
      funext i
      dsimp only [z]
      simp
    dsimp only [projected]
    rw [harith, weightedGaugeProjection_add]
  have hProjectedGraph :
      ‖weightedGaugeProjection H alphaA graph‖ ≤
        G + (1 + R) * (E * B) := by
    have hid : weightedGaugeProjection H alphaA graph =
        projected - weightedGaugeProjection H alphaA z := by
      rw [hProjectedDecomp]
      abel
    rw [hid]
    exact (norm_sub_le _ _).trans
      (add_le_add (by simpa only [G] using le_rfl) hzProjected)
  have hGraphNorm : ‖graph‖ ≤ Ggraph := by
    have htri : ‖graph‖ ≤
        ‖weightedGaugeProjection H alphaA graph‖ +
          ‖weightedGaugeProjection H alphaA graph - graph‖ := by
      have hid : graph = weightedGaugeProjection H alphaA graph -
          (weightedGaugeProjection H alphaA graph - graph) := by abel
      calc
        ‖graph‖ = ‖weightedGaugeProjection H alphaA graph -
            (weightedGaugeProjection H alphaA graph - graph)‖ :=
          congrArg norm hid
        _ ≤ _ := norm_sub_le _ _
    have hraw : ‖graph‖ ≤
        G + (1 + R) * (E * B) + rho * ‖graph‖ :=
      htri.trans (add_le_add hProjectedGraph hProjectionDefect)
    have hscaled : rho * ‖graph‖ ≤ (1 / 2) * ‖graph‖ :=
      mul_le_mul_of_nonneg_right hRhoHalf (norm_nonneg _)
    dsimp only [Ggraph]
    nlinarith
  have hGraphOutput (x : Sum Low High) :
      |M.center (e x) *
          graphOperator (M.splitSharpEdge e) q x| ≤ Ggraph := by
    have hrelabel := M.graphOperator_split_eq e q x
    rw [hrelabel]
    have hqRelabel : (fun i ↦ q (e.symm i)) = qBand := by
      funext i
      dsimp only [q]
      rw [e.apply_symm_apply]
    rw [hqRelabel]
    change |graph (e x)| ≤ Ggraph
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm graph (e x)).trans hGraphNorm
  have hLowDirect (l : Low) :
      |M.center (e (.inl l)) * q (.inl l)| ≤
        Clow * Ggraph + epsLow * B := by
    let i : Band := e (.inl l)
    have hrawOutput : |continuumRaw i| ≤ Ggraph + residual * B := by
      have hdecomp := congrFun hContinuumDecomp i
      simp only [Pi.add_apply] at hdecomp
      calc
        |continuumRaw i| = |graph i + M.rowResidual i * b.1 i| := by
          rw [hdecomp]
        _ ≤ |graph i| + |M.rowResidual i * b.1 i| := abs_add_le _ _
        _ ≤ Ggraph + residual * B := by
          exact add_le_add
            (by simpa only [Real.norm_eq_abs] using
              (norm_le_pi_norm graph i).trans hGraphNorm)
            (by rw [abs_mul]
                exact mul_le_mul (hResidual i) (hbPoint i)
                  (abs_nonneg _) hResidualNonneg)
    have hkernel :
        ∑ j : Band, |M.normalizedKernelCell i j| ≤
          C * lowCenter * totalLength := by
      have hrow := M.sum_abs_normalizedKernelCell_le hC hKernel hTotalLength i
      have hci : M.center i ≤ lowCenter := hLowCenter l
      exact hrow.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hci hC) hTotalLengthNonneg)
    have hdirect := FiniteRawLowDiagonal.abs_coordinate_le
      M.normalizedDiagonalCell M.normalizedKernelCell b.1 i
      (hDiagonalLow l) hdOne hkernel hrawOutput
    have hnum :
        Ggraph + residual * B +
            (C * lowCenter * totalLength) * ‖b.1‖ ≤
          Ggraph + (residual + C * lowCenter * totalLength) * B := by
      have hnorm : ‖b.1‖ = B := rfl
      rw [hnorm]
      ring_nf
      exact le_refl
        (Ggraph + residual * B + B * C * lowCenter * totalLength)
    have hden : 0 < 1 - d := sub_pos.mpr hdOne
    have hbq : b.1 i = M.center i * q (.inl l) := by
      dsimp only [i, q]
      rw [hqScale]
    rw [hbq] at hdirect
    calc
      |M.center i * q (.inl l)| ≤
          (Ggraph + residual * B +
            (C * lowCenter * totalLength) * ‖b.1‖) / (1 - d) :=
        hdirect
      _ ≤ (Ggraph +
          (residual + C * lowCenter * totalLength) * B) / (1 - d) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = Clow * Ggraph + epsLow * B := by
        dsimp only [Clow, epsLow]
        ring
  let omega : Sum Low High → ℝ := fun x ↦
    H (e x) * alphaA (e x) * M.center (e x)
  have hGauge : ∑ x : Sum Low High, omega x * q x = 0 := by
    calc
      (∑ x : Sum Low High, omega x * q x) =
          ∑ i : Band, H i * alphaA i * b.1 i := by
        apply Fintype.sum_equiv e
        intro x
        dsimp only [omega, q, qBand]
        field_simp [ne_of_gt (M.center_pos (e x))]
      _ = 0 := by
        have hbGauge := b.2
        change ∑ i : Band, H i * alphaA i * b.1 i = 0 at hbGauge
        exact hbGauge
  have hOmegaHigh (i : High) : 0 ≤ omega (.inr i) := by
    dsimp only [omega]
    exact mul_nonneg
      (mul_nonneg (hH _).le (hAlphaA _).le) (M.center_pos _).le
  have hOmegaHighTotal : 0 < ∑ i : High, omega (.inr i) := by
    apply Finset.sum_pos
    · intro i hi
      dsimp only [omega]
      exact mul_pos (mul_pos (hH _) (hAlphaA _)) (M.center_pos _)
    · exact Finset.univ_nonempty
  have hGaugeLow :
      |∑ l : Low, omega (.inl l) * q (.inl l)| ≤
        gaugeRatio * (∑ i : High, omega (.inr i)) *
          (Clow * Ggraph + epsLow * B) := by
    calc
      |∑ l : Low, omega (.inl l) * q (.inl l)| ≤
          ∑ l : Low, (H (e (.inl l)) * alphaA (e (.inl l))) *
            (Clow * Ggraph + epsLow * B) := by
        calc
          |∑ l : Low, omega (.inl l) * q (.inl l)| ≤
              ∑ l : Low, |omega (.inl l) * q (.inl l)| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ l : Low,
                (H (e (.inl l)) * alphaA (e (.inl l))) *
                (Clow * Ggraph + epsLow * B) := by
            apply Finset.sum_le_sum
            intro l hl
            have hterm : |omega (.inl l) * q (.inl l)| =
                (H (e (.inl l)) * alphaA (e (.inl l))) *
                  |M.center (e (.inl l)) * q (.inl l)| := by
              dsimp only [omega]
              rw [abs_mul, abs_mul,
                abs_of_pos (mul_pos (hH _) (hAlphaA _)),
                abs_of_pos (M.center_pos _), abs_mul,
                abs_of_pos (M.center_pos _)]
              ring
            rw [hterm]
            exact mul_le_mul_of_nonneg_left (hLowDirect l)
              (mul_nonneg (hH _).le (hAlphaA _).le)
      _ = (∑ l : Low, H (e (.inl l)) * alphaA (e (.inl l))) *
          (Clow * Ggraph + epsLow * B) := by rw [Finset.sum_mul]
      _ ≤ gaugeRatio * (∑ i : High, omega (.inr i)) *
          (Clow * Ggraph + epsLow * B) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        simpa only [omega] using hMixedGaugeRatio
  have hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤
        C * M.center i * M.length j :=
    M.abs_normalizedKernelCell_le_center_mul_length hKernel
  have hCrossRows (i : High) :
      |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
          (q (.inr i) - q (.inl l))| ≤
        (C * lowCenter * lowLength) * B / amin +
          (C * lowLength) * (Clow * Ggraph + epsLow * B) := by
    exact M.abs_splitSharpEdge_cross_low_le e hC hLowCenterNonneg hB
      (by positivity) hCell hLowCenter hLowLength hAmin
      hHighCenterLower q (by
        intro x
        have hx : M.center (e x) * q x = b.1 (e x) := by
          dsimp only [q]
          rw [hqScale]
        rw [hx]
        exact hbPoint (e x)) hLowDirect i
  have hSplitNorm :
      ‖fun x ↦ M.center (e x) * q x‖ = B := by
    apply le_antisymm
    · rw [pi_norm_le_iff_of_nonneg hB]
      intro x
      rw [Real.norm_eq_abs]
      have hx : M.center (e x) * q x = b.1 (e x) := by
        dsimp only [q]
        rw [hqScale]
      rw [hx]
      exact hbPoint (e x)
    · change ‖b.1‖ ≤ _
      rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
      intro i
      rw [Real.norm_eq_abs]
      let x := e.symm i
      have hx : M.center (e x) * q x = b.1 i := by
        dsimp only [x, q]
        rw [e.apply_symm_apply, hqScale]
      rw [← hx]
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (fun x ↦ M.center (e x) * q x) x
  have hBase := FiniteManyLowRawGraphInverse.ordinary_raw_bound
    (M.splitSharpEdge e) (M.splitHighAnchor e) omega
    (fun x ↦ M.center (e x)) q hGgraph hkappa rfl hAnchorMassPos
    (M.gap_mul_splitHighAnchor_le_highEdge e hgap)
    hHighCenterLower hAmin hHighCenterUpper
    (fun i ↦ (M.center_pos _).le) hAmax
    (mul_nonneg (mul_nonneg hC hLowCenterNonneg) hLowLengthNonneg)
    (mul_nonneg hC hLowLengthNonneg) hClow hepsLow hOmegaHigh
    hOmegaHighTotal hGauge hGraphOutput (by
      intro l
      rw [hSplitNorm]
      exact hLowDirect l) (by
      intro i
      rw [hSplitNorm]
      exact hCrossRows i) (by
      rw [hSplitNorm]
      exact hGaugeLow)
    (by simpa only [epsLow] using hAbsorbLow)
  have hBNorm : B ≤ 2 * Cmain * Ggraph := by
    have hnonneg : 0 ≤ 2 * Cmain * Ggraph := by positivity
    change ‖b.1‖ ≤ _
    rw [pi_norm_le_iff_of_nonneg hnonneg]
    intro i
    rw [Real.norm_eq_abs]
    let x := e.symm i
    have hx := hBase x
    have hid : M.center (e x) * q x = b.1 i := by
      dsimp only [x, q]
      rw [e.apply_symm_apply, hqScale]
    rw [hid] at hx
    simpa only [Cmain, Clow] using hx
  have hSmall : 4 * Cmain * ((1 + R) * E) ≤ 1 / 2 := by
    simpa only [Cmain, Clow, E] using hAbsorbArithmetic
  have hFinal : B ≤ 8 * Cmain * G := by
    have hraw : B ≤ 4 * Cmain * G +
        (4 * Cmain * ((1 + R) * E)) * B := by
      calc
        B ≤ 2 * Cmain * Ggraph := hBNorm
        _ = 4 * Cmain * G +
            (4 * Cmain * ((1 + R) * E)) * B := by
          dsimp only [Ggraph]
          ring
    have habsorb : (4 * Cmain * ((1 + R) * E)) * B ≤
        (1 / 2) * B := mul_le_mul_of_nonneg_right hSmall hB
    have hhalf : B ≤ 4 * Cmain * G + (1 / 2) * B :=
      hraw.trans (add_le_add le_rfl habsorb)
    linarith
  simpa only [B, G, projected, Cmain, Clow] using hFinal

end IntervalMesh
end ArithmeticGaugeOrdinary
end Erdos390.Full.ContinuumCellGraph
