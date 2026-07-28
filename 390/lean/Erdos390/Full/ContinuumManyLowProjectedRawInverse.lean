import Erdos390.Full.ContinuumProjectedRawOrdinary

/-!
# Uniform ordinary inverse for the projected continuum cell operator

The unprojected continuum row is a reversible graph row plus the explicit
piecewise-centre residual.  This file projects that identity, proves the
direct low-row bound, invokes the many-low maximum principle, and performs
the final residual absorption.  Every smallness inequality appears in the
statement.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteRawLowDiagonal
open MovingLowGaugeTransfer
open PaperWeightedInverseExport

variable {Band Low High : Type*} [Fintype Band]
  [Fintype Low] [Fintype High]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Relabelling by a finite equivalence commutes exactly with the graph
operator. -/
theorem graphOperator_split_eq
    (e : Sum Low High ≃ Band) (q : Sum Low High → ℝ)
    (x : Sum Low High) :
    graphOperator (M.splitSharpEdge e) q x =
      graphOperator M.sharpKernelEdge (fun i ↦ q (e.symm i)) (e x) := by
  unfold graphOperator splitSharpEdge
  exact Fintype.sum_equiv e _ _ (fun j ↦ by simp)

/-- Exact projected continuum ordinary inverse.  The constant contains only
the fixed high geometry.  Dependence on the moving low region occurs in the
two displayed absorption inequalities and not through its least centre or
number of cells. -/
theorem ordinary_split_projected_raw_bound
    [DecidableEq Band] [Nonempty High]
    (e : Sum Low High ≃ Band)
    {C kappa amin amax lowCenter lowLength totalLength gaugeRatio
      d residual R : ℝ}
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
    (hGaugeRatio : 0 ≤ gaugeRatio)
    (hGaugeRatioGeometry : lowLength ≤ gaugeRatio *
      (amin * ∑ i : High, M.splitHighAnchor e i))
    (hdOne : d < 1)
    (hDiagonalLow : ∀ l : Low,
      |M.normalizedDiagonalCell (e (.inl l)) - 1| ≤ d)
    (hResidualNonneg : 0 ≤ residual)
    (hResidual : ∀ i : Band, |M.rowResidual i| ≤ residual)
    (hR : 0 ≤ R)
    (hMomentRatio : (∑ i : Band,
        M.harmonicMass i * M.center i) ≤
      R * sharpWeightTotal M.harmonicMass M.center)
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
    (hAbsorbResidual :
      let Clow := 1 / (1 - d)
      let Cmain :=
        max Clow
          (amax *
            (2 * (1 / (kappa *
                ∑ i : High, M.splitHighAnchor e i)) *
                (1 / amin + (C * lowLength) * Clow) +
              gaugeRatio * Clow))
      2 * Cmain * ((1 + R) * residual) ≤ 1 / 2)
    (q : Sum Low High → ℝ)
    (hGauge : ∑ x : Sum Low High,
      M.splitSharpWeight e x * q x = 0) :
    ∀ x : Sum Low High,
      |M.center (e x) * q x| ≤
        (4 *
          max (1 / (1 - d))
            (amax *
              (2 * (1 / (kappa *
                  ∑ i : High, M.splitHighAnchor e i)) *
                  (1 / amin +
                    (C * lowLength) * (1 / (1 - d))) +
                gaugeRatio * (1 / (1 - d))))) *
          ‖weightedGaugeProjection M.harmonicMass M.center
            (rawOperator M.normalizedDiagonalCell
              M.normalizedKernelCell
              (fun i ↦ M.center i * q (e.symm i)))‖ := by
  letI : Nonempty Band :=
    ⟨e (.inr (Classical.choice (inferInstance : Nonempty High)))⟩
  let qBand : Band → ℝ := fun i ↦ q (e.symm i)
  let b : Band → ℝ := fun i ↦ M.center i * qBand i
  let raw : Band → ℝ :=
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b
  let projected : Band → ℝ :=
    weightedGaugeProjection M.harmonicMass M.center raw
  let residualVector : Band → ℝ := fun i ↦ M.rowResidual i * b i
  let graphVector : Band → ℝ := fun i ↦
    M.center i * graphOperator M.sharpKernelEdge qBand i
  let B : ℝ := ‖fun x ↦ M.center (e x) * q x‖
  let G : ℝ := ‖projected‖
  let Clow : ℝ := 1 / (1 - d)
  let epsLow : ℝ :=
    (residual + C * lowCenter * totalLength) / (1 - d)
  let epsGraph : ℝ := (1 + R) * residual
  let Ggraph : ℝ := G + epsGraph * B
  let Cmain : ℝ :=
    max Clow
      (amax *
        (2 * (1 / (kappa *
            ∑ i : High, M.splitHighAnchor e i)) *
            (1 / amin + (C * lowLength) * Clow) +
          gaugeRatio * Clow))
  have hB : 0 ≤ B := norm_nonneg _
  have hG : 0 ≤ G := norm_nonneg _
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
  have hepsGraph : 0 ≤ epsGraph := by
    dsimp only [epsGraph]
    positivity
  have hGgraph : 0 ≤ Ggraph := by
    dsimp only [Ggraph]
    positivity
  have hCmain : 0 ≤ Cmain :=
    hClow.trans (by dsimp only [Cmain]; exact le_max_left _ _)
  have hqBand (x : Sum Low High) : qBand (e x) = q x := by
    dsimp only [qBand]
    rw [e.symm_apply_apply]
  have hbCoord (x : Sum Low High) : b (e x) = M.center (e x) * q x := by
    dsimp only [b]
    rw [hqBand]
  have hbBound (i : Band) : |b i| ≤ B := by
    let x := e.symm i
    have hx : |M.center (e x) * q x| ≤ B := by
      dsimp only [B]
      simpa only [Real.norm_eq_abs] using
        norm_le_pi_norm (fun y ↦ M.center (e y) * q y) x
    simpa only [x, e.apply_symm_apply] using hx
  have hbNorm : ‖b‖ ≤ B := by
    rw [pi_norm_le_iff_of_nonneg hB]
    intro i
    rw [Real.norm_eq_abs]
    exact hbBound i
  have hResidualVector (i : Band) :
      |residualVector i| ≤ residual * B := by
    dsimp only [residualVector]
    rw [abs_mul]
    exact mul_le_mul (hResidual i) (hbBound i)
      (abs_nonneg _) hResidualNonneg
  have hProjectedResidual :
      ‖weightedGaugeProjection M.harmonicMass M.center residualVector‖ ≤
        (1 + R) * (residual * B) :=
    M.weightedGaugeProjection_norm_le_of_moment_ratio residualVector
      (mul_nonneg hResidualNonneg hB) hR hResidualVector hMomentRatio
  have hRawDecomp : raw = graphVector + residualVector := by
    funext i
    have h := M.rawOperator_eq_scaledGraph_add_residual b i
    have hdivide : (fun j ↦ b j / M.center j) = qBand := by
      funext j
      dsimp only [b]
      field_simp [ne_of_gt (M.center_pos j)]
    rw [hdivide] at h
    simpa only [raw, graphVector, residualVector, Pi.add_apply] using h
  have hProjectedDecomp : projected = graphVector +
      weightedGaugeProjection M.harmonicMass M.center residualVector := by
    dsimp only [projected]
    rw [hRawDecomp, weightedGaugeProjection_add]
    apply congrArg₂ (fun u v : Band → ℝ ↦ u + v) _ rfl
    funext i
    exact M.weightedGaugeProjection_scaledGraph_eq qBand i
  have hGraphOutput (x : Sum Low High) :
      |M.center (e x) *
        graphOperator (M.splitSharpEdge e) q x| ≤ Ggraph := by
    have hgraphRelabel := M.graphOperator_split_eq e q x
    have hcoord : |projected (e x)| ≤ G := by
      dsimp only [G]
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm projected (e x)
    have hresCoord :
        |weightedGaugeProjection M.harmonicMass M.center
            residualVector (e x)| ≤
          (1 + R) * (residual * B) := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm
          (weightedGaugeProjection M.harmonicMass M.center residualVector)
          (e x)).trans hProjectedResidual
    have hidentity :
        M.center (e x) *
            graphOperator (M.splitSharpEdge e) q x =
          projected (e x) -
            weightedGaugeProjection M.harmonicMass M.center
              residualVector (e x) := by
      have hfun := congrFun hProjectedDecomp (e x)
      dsimp only [Pi.add_apply, graphVector] at hfun
      rw [hgraphRelabel]
      change M.center (e x) * graphOperator M.sharpKernelEdge qBand (e x) = _
      linarith [hfun]
    rw [hidentity]
    calc
      |projected (e x) -
          weightedGaugeProjection M.harmonicMass M.center
            residualVector (e x)| ≤
        |projected (e x)| +
          |weightedGaugeProjection M.harmonicMass M.center
            residualVector (e x)| := abs_sub _ _
      _ ≤ G + (1 + R) * (residual * B) :=
        add_le_add hcoord hresCoord
      _ = Ggraph := by dsimp only [Ggraph, epsGraph]; ring
  have hLowDirect (l : Low) :
      |M.center (e (.inl l)) * q (.inl l)| ≤
        Clow * Ggraph + epsLow * B := by
    let i : Band := e (.inl l)
    have hrawOutput : |raw i| ≤ Ggraph + residual * B := by
      have hgraph := hGraphOutput (.inl l)
      have hres := hResidualVector i
      have hidentity := congrFun hRawDecomp i
      dsimp only [graphVector] at hidentity
      have hrelabel := M.graphOperator_split_eq e q (.inl l)
      rw [hrelabel] at hgraph
      calc
        |raw i| = |graphVector i + residualVector i| := by
          simpa only [Pi.add_apply] using congrArg abs hidentity
        _ ≤ |graphVector i| + |residualVector i| := abs_add_le _ _
        _ ≤ Ggraph + residual * B := add_le_add hgraph hres
    have hkernel :
        ∑ j : Band, |M.normalizedKernelCell i j| ≤
          C * lowCenter * totalLength := by
      have hrow := M.sum_abs_normalizedKernelCell_le hC hKernel hTotalLength i
      have hci : M.center i ≤ lowCenter := hLowCenter l
      exact hrow.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hci hC) hTotalLengthNonneg)
    have hdiag : |M.normalizedDiagonalCell i - 1| ≤ d :=
      hDiagonalLow l
    have hdirect := FiniteRawLowDiagonal.abs_coordinate_le
      M.normalizedDiagonalCell M.normalizedKernelCell b i hdiag hdOne
      hkernel hrawOutput
    have hnum :
        Ggraph + residual * B +
            (C * lowCenter * totalLength) * ‖b‖ ≤
          Ggraph +
            (residual + C * lowCenter * totalLength) * B := by
      calc
        Ggraph + residual * B +
            (C * lowCenter * totalLength) * ‖b‖ ≤
          Ggraph + residual * B +
            (C * lowCenter * totalLength) * B :=
          add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hbNorm
              (mul_nonneg (mul_nonneg hC hLowCenterNonneg)
                hTotalLengthNonneg))
        _ = Ggraph +
            (residual + C * lowCenter * totalLength) * B := by ring
    have hden : 0 < 1 - d := sub_pos.mpr hdOne
    rw [hbCoord (.inl l)] at hdirect
    calc
      |M.center (e (.inl l)) * q (.inl l)| ≤
          (Ggraph + residual * B +
            (C * lowCenter * totalLength) * ‖b‖) / (1 - d) := hdirect
      _ ≤ (Ggraph +
            (residual + C * lowCenter * totalLength) * B) / (1 - d) :=
        div_le_div_of_nonneg_right hnum hden.le
      _ = Clow * Ggraph + epsLow * B := by
        dsimp only [Clow, epsLow]
        ring
  have hBase := M.ordinary_split_raw_bound e hC hKernel hkappa hgap
    hAnchorMassPos hAmin hHighCenterLower hHighCenterUpper hAmax
    hLowCenterNonneg hLowCenter hLowLengthNonneg hLowLength
    hGaugeRatio hGaugeRatioGeometry hClow hepsLow hGgraph q hGauge
    hGraphOutput hLowDirect (by simpa only [epsLow] using hAbsorbLow)
  have hcoord : ∀ x : Sum Low High,
      |M.center (e x) * q x| ≤ 2 * Cmain * Ggraph := by
    intro x
    simpa only [Cmain, Clow] using hBase x
  have hBNorm : B ≤ 2 * Cmain * Ggraph := by
    have hnonneg : 0 ≤ 2 * Cmain * Ggraph := by positivity
    dsimp only [B]
    rw [pi_norm_le_iff_of_nonneg hnonneg]
    intro x
    rw [Real.norm_eq_abs]
    exact hcoord x
  have hResidualSmall : 2 * Cmain * epsGraph ≤ 1 / 2 := by
    simpa only [Cmain, Clow, epsGraph] using hAbsorbResidual
  have hBfinal : B ≤ 4 * Cmain * G := by
    have hscaled : (2 * Cmain * epsGraph) * B ≤ (1 / 2) * B :=
      mul_le_mul_of_nonneg_right hResidualSmall hB
    have hraw : B ≤ 2 * Cmain * G +
        (2 * Cmain * epsGraph) * B := by
      calc
        B ≤ 2 * Cmain * Ggraph := hBNorm
        _ = 2 * Cmain * G + (2 * Cmain * epsGraph) * B := by
          dsimp only [Ggraph]
          ring
    nlinarith
  intro x
  have hx : |M.center (e x) * q x| ≤ B := by
    dsimp only [B]
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun y ↦ M.center (e y) * q y) x
  exact hx.trans (by
    simpa only [Cmain, Clow, G, projected, raw, b, qBand] using hBfinal)

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
