import Erdos390.Full.ContinuumManyLowRawGraphInverse
import Erdos390.Full.FiniteGraphStableInverse

/-!
# Projected continuum rows in the ordinary moving-low norm

The continuum compression is the reversible graph row plus the explicit
cell-centering residual.  This file controls the part of that residual which
is reintroduced by gauge projection.  The estimate uses only a first/sharp
moment ratio; it never divides by the least cell centre.

These lemmas are stated on an arbitrary finite interval mesh and are intended
to be reused both by the continuum inverse in Lemma 8.4 and by the ordinary
fast solve in Proposition 8.7.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open FiniteGraphQuotientInverse
open FiniteGraphStableInverse

variable {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Exact continuum sharp-gauge weight. -/
def continuumSharpWeight (i : Band) : ℝ :=
  M.harmonicMass i * M.center i ^ 2

/-- First moment which controls projection in the ordinary raw norm. -/
def continuumFirstWeight (i : Band) : ℝ :=
  M.harmonicMass i * M.center i

/-- The explicit piecewise-centre residual score. -/
def continuumResidualScore (q : Band → ℝ) (i : Band) : ℝ :=
  M.rowResidual i * q i

omit [DecidableEq Band] in
theorem continuumSharpWeight_nonneg (i : Band) :
    0 ≤ M.continuumSharpWeight i := by
  exact mul_nonneg (M.harmonicMass_pos i).le (sq_nonneg _)

omit [DecidableEq Band] in
theorem continuumFirstWeight_nonneg (i : Band) :
    0 ≤ M.continuumFirstWeight i := by
  exact mul_nonneg (M.harmonicMass_pos i).le (M.center_pos i).le

omit [DecidableEq Band] in
/-- Projection of the continuum row is exactly the graph row plus the
projected explicit residual. -/
theorem meanProjection_continuumSharp_eq_graph_add_residual
    (q : Band → ℝ) :
    meanProjection M.continuumSharpWeight
        (M.continuumSharpOperator q) =
      graphOperator M.sharpKernelEdge q +
        meanProjection M.continuumSharpWeight
          (M.continuumResidualScore q) := by
  have hdecomp : M.continuumSharpOperator q =
      graphOperator M.sharpKernelEdge q + M.continuumResidualScore q := by
    funext i
    rw [M.continuumSharpOperator_eq_graph_add_residual]
    rfl
  rw [hdecomp]
  funext i
  rw [meanProjection_add]
  have hgraph := M.meanProjection_sharpGraph_eq q
  change meanProjection M.continuumSharpWeight
      (graphOperator M.sharpKernelEdge q) =
        graphOperator M.sharpKernelEdge q at hgraph
  rw [hgraph]
  rfl

omit [DecidableEq Band] in
/-- The weighted mean of the continuum row is entirely due to the explicit
residual; the reversible graph contributes zero exactly. -/
theorem weightedMean_continuumSharp_eq_residual
    (q : Band → ℝ) :
    weightedMean M.continuumSharpWeight (M.continuumSharpOperator q) =
      weightedMean M.continuumSharpWeight
        (M.continuumResidualScore q) := by
  have hdecomp : M.continuumSharpOperator q =
      graphOperator M.sharpKernelEdge q + M.continuumResidualScore q := by
    funext i
    rw [M.continuumSharpOperator_eq_graph_add_residual]
    rfl
  rw [hdecomp, weightedMean_add]
  have hgraph := M.weightedMean_sharpGraph_eq_zero q
  change weightedMean M.continuumSharpWeight
      (graphOperator M.sharpKernelEdge q) = 0 at hgraph
  rw [hgraph, zero_add]

omit [DecidableEq Band] in
/-- Moment-ratio estimate for the scalar removed by continuum gauge
projection.  The hypotheses and conclusion are uniform in the number and
least endpoint of the cells. -/
theorem abs_center_mul_weightedMean_residual_le
    {rho R B : ℝ}
    (hRho : 0 ≤ rho) (hB : 0 ≤ B)
    (hTotal : 0 < ∑ j : Band, M.continuumSharpWeight j)
    (hMomentRatio : ∀ i : Band,
      M.center i * (∑ j : Band, M.continuumFirstWeight j) ≤
        R * (∑ j : Band, M.continuumSharpWeight j))
    (q : Band → ℝ)
    (hResidual : ∀ j : Band, |M.rowResidual j| ≤ rho)
    (hPoint : ∀ j : Band, |M.center j * q j| ≤ B)
    (i : Band) :
    |M.center i * weightedMean M.continuumSharpWeight
        (M.continuumResidualScore q)| ≤ rho * R * B := by
  have hNumerator :
      |∑ j : Band, M.continuumSharpWeight j *
          M.continuumResidualScore q j| ≤
        (rho * B) * ∑ j : Band, M.continuumFirstWeight j := by
    calc
      |∑ j : Band, M.continuumSharpWeight j *
          M.continuumResidualScore q j| ≤
          ∑ j : Band, |M.continuumSharpWeight j *
            M.continuumResidualScore q j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band, (rho * B) * M.continuumFirstWeight j := by
        apply Finset.sum_le_sum
        intro j hj
        have hH : 0 < M.harmonicMass j := M.harmonicMass_pos j
        have hc : 0 < M.center j := M.center_pos j
        rw [continuumSharpWeight, continuumResidualScore,
          continuumFirstWeight, abs_mul, abs_mul, abs_mul,
          abs_of_pos hH, abs_of_nonneg (sq_nonneg (M.center j))]
        calc
          M.harmonicMass j * M.center j ^ 2 *
              (|M.rowResidual j| * |q j|) =
              (M.harmonicMass j * M.center j) *
                |M.rowResidual j| * |M.center j * q j| := by
            rw [abs_mul, abs_of_pos hc]
            ring
          _ ≤ (M.harmonicMass j * M.center j) * rho * B := by
            gcongr
            · exact hResidual j
            · exact hPoint j
          _ = (rho * B) * (M.harmonicMass j * M.center j) := by ring
      _ = (rho * B) * ∑ j : Band, M.continuumFirstWeight j := by
        rw [Finset.mul_sum]
  have hMean :
      |weightedMean M.continuumSharpWeight
          (M.continuumResidualScore q)| ≤
        ((rho * B) * ∑ j : Band, M.continuumFirstWeight j) /
          (∑ j : Band, M.continuumSharpWeight j) := by
    unfold weightedMean weightTotal
    rw [abs_div, abs_of_pos hTotal]
    exact div_le_div_of_nonneg_right hNumerator hTotal.le
  have hc : 0 < M.center i := M.center_pos i
  rw [abs_mul, abs_of_pos hc]
  calc
    M.center i *
        |weightedMean M.continuumSharpWeight
          (M.continuumResidualScore q)| ≤
      M.center i *
        (((rho * B) * ∑ j : Band, M.continuumFirstWeight j) /
          (∑ j : Band, M.continuumSharpWeight j)) :=
      mul_le_mul_of_nonneg_left hMean hc.le
    _ = (rho * B) *
        (M.center i * ∑ j : Band, M.continuumFirstWeight j) /
          (∑ j : Band, M.continuumSharpWeight j) := by ring
    _ ≤ (rho * B) *
        (R * ∑ j : Band, M.continuumSharpWeight j) /
          (∑ j : Band, M.continuumSharpWeight j) := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hMomentRatio i)
          (mul_nonneg hRho hB)) hTotal.le
    _ = rho * R * B := by
      field_simp [ne_of_gt hTotal]

omit [DecidableEq Band] in
/-- Projected residual in the ordinary raw norm. -/
theorem abs_center_mul_projectedResidual_le
    {rho R B : ℝ}
    (hRho : 0 ≤ rho) (hB : 0 ≤ B)
    (hTotal : 0 < ∑ j : Band, M.continuumSharpWeight j)
    (hMomentRatio : ∀ i : Band,
      M.center i * (∑ j : Band, M.continuumFirstWeight j) ≤
        R * (∑ j : Band, M.continuumSharpWeight j))
    (q : Band → ℝ)
    (hResidual : ∀ j : Band, |M.rowResidual j| ≤ rho)
    (hPoint : ∀ j : Band, |M.center j * q j| ≤ B)
    (i : Band) :
    |M.center i * meanProjection M.continuumSharpWeight
        (M.continuumResidualScore q) i| ≤ rho * (1 + R) * B := by
  have hmean := M.abs_center_mul_weightedMean_residual_le hRho hB
    hTotal hMomentRatio q hResidual hPoint i
  unfold meanProjection continuumResidualScore
  calc
    |M.center i *
        (M.rowResidual i * q i -
          weightedMean M.continuumSharpWeight
            (fun j ↦ M.rowResidual j * q j))| ≤
      |M.center i * (M.rowResidual i * q i)| +
        |M.center i * weightedMean M.continuumSharpWeight
          (fun j ↦ M.rowResidual j * q j)| := by
      rw [mul_sub]
      exact abs_sub _ _
    _ ≤ rho * B + rho * R * B := by
      apply add_le_add
      · rw [show M.center i * (M.rowResidual i * q i) =
            M.rowResidual i * (M.center i * q i) by ring,
          abs_mul]
        exact mul_le_mul (hResidual i) (hPoint i)
          (abs_nonneg _) hRho
      · simpa only [continuumResidualScore] using hmean
    _ = rho * (1 + R) * B := by ring

omit [DecidableEq Band] in
/-- A bound for the projected continuum row gives a graph-output bound with
only the moment-ratio residual loss. -/
theorem abs_center_mul_graph_le_of_projectedContinuum
    {rho R B G : ℝ}
    (hRho : 0 ≤ rho) (hB : 0 ≤ B)
    (hTotal : 0 < ∑ j : Band, M.continuumSharpWeight j)
    (hMomentRatio : ∀ i : Band,
      M.center i * (∑ j : Band, M.continuumFirstWeight j) ≤
        R * (∑ j : Band, M.continuumSharpWeight j))
    (q : Band → ℝ)
    (hResidual : ∀ j : Band, |M.rowResidual j| ≤ rho)
    (hPoint : ∀ j : Band, |M.center j * q j| ≤ B)
    (hProjected : ∀ i : Band,
      |M.center i * meanProjection M.continuumSharpWeight
        (M.continuumSharpOperator q) i| ≤ G)
    (i : Band) :
    |M.center i * graphOperator M.sharpKernelEdge q i| ≤
      G + rho * (1 + R) * B := by
  have hid := congrFun
    (M.meanProjection_continuumSharp_eq_graph_add_residual q) i
  have hres := M.abs_center_mul_projectedResidual_le hRho hB
    hTotal hMomentRatio q hResidual hPoint i
  rw [Pi.add_apply] at hid
  have hproj := hProjected i
  rw [hid] at hproj
  calc
    |M.center i * graphOperator M.sharpKernelEdge q i| =
      |M.center i *
        ((graphOperator M.sharpKernelEdge q i +
            meanProjection M.continuumSharpWeight
              (M.continuumResidualScore q) i) -
          meanProjection M.continuumSharpWeight
            (M.continuumResidualScore q) i)| := by ring_nf
    _ ≤ |M.center i *
          (graphOperator M.sharpKernelEdge q i +
            meanProjection M.continuumSharpWeight
              (M.continuumResidualScore q) i)| +
        |M.center i * meanProjection M.continuumSharpWeight
          (M.continuumResidualScore q) i| := by
      rw [mul_sub]
      exact abs_sub _ _
    _ ≤ G + rho * (1 + R) * B := add_le_add hproj hres

omit [DecidableEq Band] in
/-- The corresponding unprojected raw continuum row is even cheaper: its
only lost scalar is the weighted mean of the explicit residual. -/
theorem abs_center_mul_continuumSharp_le_of_projected
    {rho R B G : ℝ}
    (hRho : 0 ≤ rho) (hB : 0 ≤ B)
    (hTotal : 0 < ∑ j : Band, M.continuumSharpWeight j)
    (hMomentRatio : ∀ i : Band,
      M.center i * (∑ j : Band, M.continuumFirstWeight j) ≤
        R * (∑ j : Band, M.continuumSharpWeight j))
    (q : Band → ℝ)
    (hResidual : ∀ j : Band, |M.rowResidual j| ≤ rho)
    (hPoint : ∀ j : Band, |M.center j * q j| ≤ B)
    (hProjected : ∀ i : Band,
      |M.center i * meanProjection M.continuumSharpWeight
        (M.continuumSharpOperator q) i| ≤ G)
    (i : Band) :
    |M.center i * M.continuumSharpOperator q i| ≤
      G + rho * R * B := by
  have hmean := M.abs_center_mul_weightedMean_residual_le hRho hB
    hTotal hMomentRatio q hResidual hPoint i
  have hmeanEq := M.weightedMean_continuumSharp_eq_residual q
  unfold meanProjection at hProjected
  calc
    |M.center i * M.continuumSharpOperator q i| =
      |M.center i *
        ((M.continuumSharpOperator q i -
            weightedMean M.continuumSharpWeight
              (M.continuumSharpOperator q)) +
          weightedMean M.continuumSharpWeight
            (M.continuumSharpOperator q))| := by ring_nf
    _ ≤ |M.center i *
          (M.continuumSharpOperator q i -
            weightedMean M.continuumSharpWeight
              (M.continuumSharpOperator q))| +
        |M.center i * weightedMean M.continuumSharpWeight
          (M.continuumSharpOperator q)| := by
      rw [mul_add]
      exact abs_add_le _ _
    _ ≤ G + rho * R * B := by
      apply add_le_add (hProjected i)
      rw [hmeanEq]
      exact hmean

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
