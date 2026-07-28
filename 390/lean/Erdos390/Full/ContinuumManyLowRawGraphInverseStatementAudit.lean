import Erdos390.Full.ContinuumManyLowRawGraphInverse

/-!
Independent expanded statement audit for the ordinary moving-low continuum
estimate.  The restatement exposes every constant and, in particular, shows
that neither the cardinality of `Low` nor a least low endpoint occurs in the
bound.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumManyLowRawGraphInverseStatementAudit

open ConditionedPoissonLimit
open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open FiniteGraphQuotientInverse

variable {Band Low High : Type*} [Fintype Band] [DecidableEq Band]
  [Fintype Low] [Fintype High]
variable {epsilon : ℝ}

theorem ordinary_bound_uniform_over_finitely_many_moving_low_cells
    [Nonempty High]
    (M : IntervalMesh epsilon Band)
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
  exact M.ordinary_split_raw_bound e hC hKernel hkappa hgap
    hAnchorMassPos hAmin hHighCenterLower hHighCenterUpper hAmax
    hLowCenterNonneg hLowCenter hLowLengthNonneg hLowLength
    hGaugeRatio hGaugeRatioGeometry hClow hEpsLow hG q hGauge
    hOutput hLow hAbsorb

end Erdos390.Full.ContinuumManyLowRawGraphInverseStatementAudit
