import Erdos390.Full.ContinuumManyLowHighGeometry
import Erdos390.Full.FiniteManyLowRawGraphInverse

/-!
# Ordinary raw estimate for a low--high continuum cell graph

This file attaches the exact continuum product-cell estimates to the finite
many-low maximum principle.  The only remaining analytic inputs are the
scaled graph-output bound and the direct diagonal estimate on the low rows.
In particular, neither the number of low cells nor their least endpoint
occurs in the conclusion.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteManyLowRawGraphInverse

variable {Band Low High : Type*} [Fintype Band] [DecidableEq Band]
  [Fintype Low] [Fintype High]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- The continuum low/high geometry discharges every finite-graph side
condition in `FiniteManyLowRawGraphInverse.ordinary_raw_bound`.  The two
hypotheses `hOutput` and `hLow` are deliberately kept separate: in the
projected application they acquire different, explicitly vanishing,
residual errors. -/
theorem ordinary_split_raw_bound
    [Nonempty High]
    (e : Sum Low High ≃ Band)
    {C kappa amin amax lowCenter lowLength gaugeRatio
      Clow epsLow G : ℝ}
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
    (hGaugeRatio : 0 ≤ gaugeRatio)
    (hGaugeRatioGeometry : lowLength ≤ gaugeRatio *
      (amin * ∑ i : High, M.splitHighAnchor e i))
    (hClow : 0 ≤ Clow) (hEpsLow : 0 ≤ epsLow) (hG : 0 ≤ G)
    (q : Sum Low High → ℝ)
    (hGauge : ∑ x : Sum Low High,
      M.splitSharpWeight e x * q x = 0)
    (hOutput : ∀ x : Sum Low High,
      |M.center (e x) *
        graphOperator (M.splitSharpEdge e) q x| ≤ G)
    (hLow : ∀ l : Low,
      |M.center (e (.inl l)) * q (.inl l)| ≤
        Clow * G + epsLow *
          ‖fun x ↦ M.center (e x) * q x‖)
    (hAbsorb :
      max epsLow
        (amax *
          (2 * (1 / (kappa *
              ∑ i : High, M.splitHighAnchor e i)) *
              ((C * lowCenter * lowLength) / amin +
                (C * lowLength) * epsLow) +
            gaugeRatio * epsLow)) ≤ 1 / 2) :
    ∀ x : Sum Low High,
      |M.center (e x) * q x| ≤
        2 *
          max Clow
            (amax *
              (2 * (1 / (kappa *
                  ∑ i : High, M.splitHighAnchor e i)) *
                  (1 / amin + (C * lowLength) * Clow) +
                gaugeRatio * Clow)) * G := by
  let B : ℝ := ‖fun x ↦ M.center (e x) * q x‖
  let lowBudget : ℝ := Clow * G + epsLow * B
  have hB : 0 ≤ B := norm_nonneg _
  have hLowBudget : 0 ≤ lowBudget := by
    dsimp only [lowBudget]
    positivity
  have hCell : ∀ i j,
      |M.normalizedKernelCell i j| ≤
        C * M.center i * M.length j :=
    M.abs_normalizedKernelCell_le_center_mul_length hKernel
  have hNormPoint (x : Sum Low High) :
      |M.center (e x) * q x| ≤ B := by
    dsimp only [B]
    simpa only [Real.norm_eq_abs] using
      norm_le_pi_norm (fun y ↦ M.center (e y) * q y) x
  have hCrossRows (i : High) :
      |∑ l : Low, M.splitSharpEdge e (.inr i) (.inl l) *
          (q (.inr i) - q (.inl l))| ≤
        (C * lowCenter * lowLength) * B / amin +
          (C * lowLength) * lowBudget := by
    exact M.abs_splitSharpEdge_cross_low_le e hC hLowCenterNonneg hB
      hLowBudget hCell hLowCenter hLowLength hAmin
      hHighCenterLower q hNormPoint (by
        intro l
        simpa only [lowBudget, B] using hLow l) i
  have hGaugeLow :
      |∑ l : Low, M.splitSharpWeight e (.inl l) * q (.inl l)| ≤
        gaugeRatio *
          (∑ i : High, M.splitSharpWeight e (.inr i)) * lowBudget := by
    exact M.abs_lowSharpGaugeSum_le e hAmin hGaugeRatio hLowBudget
      hHighCenterLower le_rfl hLowLength hGaugeRatioGeometry q (by
        intro l
        simpa only [lowBudget, B] using hLow l)
  apply ordinary_raw_bound
    (M.splitSharpEdge e) (M.splitHighAnchor e)
    (M.splitSharpWeight e) (fun x ↦ M.center (e x)) q
    hG hkappa rfl hAnchorMassPos
    (M.gap_mul_splitHighAnchor_le_highEdge e hgap)
    hHighCenterLower hAmin hHighCenterUpper
    (fun i ↦ (M.center_pos _).le) hAmax
    (mul_nonneg (mul_nonneg hC hLowCenterNonneg) hLowLengthNonneg)
    (mul_nonneg hC hLowLengthNonneg)
    hClow hEpsLow
    (fun i ↦ by
      unfold splitSharpWeight
      exact mul_nonneg (M.harmonicMass_pos _).le (sq_nonneg _))
    (by
      apply Finset.sum_pos
      · intro i hi
        unfold splitSharpWeight
        exact mul_pos (M.harmonicMass_pos _)
          (sq_pos_of_pos (M.center_pos _))
      · exact Finset.univ_nonempty)
    hGauge hOutput hLow (by
      intro i
      simpa only [B, lowBudget] using hCrossRows i)
    (by simpa only [lowBudget, B] using hGaugeLow)
    hAbsorb

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
