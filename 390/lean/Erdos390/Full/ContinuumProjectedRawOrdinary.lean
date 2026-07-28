import Erdos390.Full.ContinuumManyLowRawGraphInverse

/-!
# Ordinary bounds for the projected continuum raw operator

The continuum graph row is exactly gauge preserving.  The piecewise-centre
residual is not, so this file estimates its literal raw-gauge projection in
the ordinary supremum norm.  The estimate uses only the first-moment to
centre-energy ratio and therefore has no least-centre divisor.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open FiniteGraphQuotientInverse
open MovingLowGaugeTransfer
open PaperWeightedInverseExport

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

/-- Ordinary norm of the exact weighted raw projection. -/
theorem weightedGaugeProjection_norm_le_of_moment_ratio
    [Nonempty Band]
    (x : Band → ℝ) {C R : ℝ}
    (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hx : ∀ j, |x j| ≤ C)
    (hRatio : (∑ j : Band, M.harmonicMass j * M.center j) ≤
      R * sharpWeightTotal M.harmonicMass M.center) :
    ‖weightedGaugeProjection M.harmonicMass M.center x‖ ≤
      (1 + R) * C := by
  let total : ℝ := sharpWeightTotal M.harmonicMass M.center
  let numerator : ℝ :=
    ∑ j : Band, M.harmonicMass j * M.center j * x j
  have htotal : 0 < total := by
    dsimp only [total, sharpWeightTotal, sharpWeight]
    apply Finset.sum_pos
    · intro j hj
      exact mul_pos (M.harmonicMass_pos j)
        (sq_pos_of_pos (M.center_pos j))
    · exact Finset.univ_nonempty
  have hmoment : 0 ≤
      ∑ j : Band, M.harmonicMass j * M.center j :=
    Finset.sum_nonneg fun j hj ↦
      mul_nonneg (M.harmonicMass_pos j).le (M.center_pos j).le
  have hnum : |numerator| ≤
      C * ∑ j : Band, M.harmonicMass j * M.center j := by
    dsimp only [numerator]
    calc
      |∑ j : Band, M.harmonicMass j * M.center j * x j| ≤
          ∑ j : Band,
            |M.harmonicMass j * M.center j * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Band,
          C * (M.harmonicMass j * M.center j) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [abs_mul, abs_mul, abs_of_pos (M.harmonicMass_pos j),
          abs_of_pos (M.center_pos j)]
        calc
          M.harmonicMass j * M.center j * |x j| ≤
              (M.harmonicMass j * M.center j) * C :=
            mul_le_mul_of_nonneg_left (hx j)
              (mul_nonneg (M.harmonicMass_pos j).le
                (M.center_pos j).le)
          _ = C * (M.harmonicMass j * M.center j) := by ring
      _ = C * ∑ j : Band,
          M.harmonicMass j * M.center j := by rw [Finset.mul_sum]
  have hmean : |numerator / total| ≤ C * R := by
    rw [abs_div, abs_of_pos htotal]
    calc
      |numerator| / total ≤
          (C * ∑ j : Band,
            M.harmonicMass j * M.center j) / total :=
        div_le_div_of_nonneg_right hnum htotal.le
      _ ≤ (C * (R * total)) / total :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hRatio hC) htotal.le
      _ = C * R := by field_simp [htotal.ne']
  have hbound : 0 ≤ (1 + R) * C :=
    mul_nonneg (by linarith) hC
  rw [pi_norm_le_iff_of_nonneg hbound]
  intro j
  rw [Real.norm_eq_abs]
  unfold weightedGaugeProjection
  change |x j - M.center j * (numerator / total)| ≤ _
  calc
    |x j - M.center j * (numerator / total)| ≤
        |x j| + |M.center j| * |numerator / total| := by
      simpa only [abs_mul] using
        abs_sub (x j) (M.center j * (numerator / total))
    _ ≤ C + 1 * (C * R) := by
      have hcenter : M.center j ≤ 1 := by
        unfold center
        apply (div_le_iff₀ (M.harmonicMass_pos j)).2
        change M.length j ≤ 1 * M.harmonicMass j
        have hlog : M.harmonicMass j =
            Real.log (M.upper j / M.lower j) := by
          unfold harmonicMass
          rw [integral_one_div_of_pos (M.lower_pos j)
            ((M.lower_pos j).trans (M.lower_lt_upper j))]
        rw [one_mul, hlog]
        unfold length
        have ha : 0 < M.lower j := M.lower_pos j
        have hb : M.lower j < M.upper j := M.lower_lt_upper j
        have hupper : M.upper j ≤ 1 := M.upper_le_one j
        have hlogLower : M.upper j - M.lower j ≤
            Real.log (M.upper j / M.lower j) := by
          have hx : 0 < M.upper j / M.lower j := div_pos (ha.trans hb) ha
          have hone : 1 ≤ M.upper j / M.lower j :=
            (one_le_div ha).2 hb.le
          have hbasic := Real.one_sub_inv_le_log_of_pos hx
          have hfactor : 0 ≤ 1 - (M.upper j / M.lower j)⁻¹ := by
            have hinvLe : (M.upper j / M.lower j)⁻¹ ≤ 1 := by
              exact inv_le_one_of_one_le₀ hone
            linarith
          calc
            M.upper j - M.lower j =
                M.upper j * (1 - (M.upper j / M.lower j)⁻¹) := by
              field_simp [ha.ne', (ha.trans hb).ne']
            _ ≤ 1 * (1 - (M.upper j / M.lower j)⁻¹) :=
              mul_le_mul_of_nonneg_right hupper hfactor
            _ ≤ Real.log (M.upper j / M.lower j) := by
              simpa only [one_mul] using hbasic
        exact hlogLower
      rw [abs_of_pos (M.center_pos j)]
      exact add_le_add (hx j)
        (mul_le_mul hcenter hmean (abs_nonneg _) (by positivity))
    _ = (1 + R) * C := by ring

/-- Scaling the reversible graph row back to raw coordinates and applying
the exact raw projection changes nothing. -/
theorem weightedGaugeProjection_scaledGraph_eq
    [Nonempty Band]
    (q : Band → ℝ) (i : Band) :
    weightedGaugeProjection M.harmonicMass M.center
        (fun j ↦ M.center j * graphOperator M.sharpKernelEdge q j) i =
      M.center i * graphOperator M.sharpKernelEdge q i := by
  have hAlpha : ∀ j, M.center j ≠ 0 := fun j ↦ ne_of_gt (M.center_pos j)
  have hTotal : sharpWeightTotal M.harmonicMass M.center ≠ 0 := by
    apply ne_of_gt
    unfold sharpWeightTotal sharpWeight
    apply Finset.sum_pos
    · intro j hj
      exact mul_pos (M.harmonicMass_pos j)
        (sq_pos_of_pos (M.center_pos j))
    · exact Finset.univ_nonempty
  rw [show (fun j ↦ M.center j * graphOperator M.sharpKernelEdge q j) =
      scaleByCenter M.center (graphOperator M.sharpKernelEdge q) by rfl]
  rw [weightedGaugeProjection_scale_eq M.harmonicMass M.center
    (graphOperator M.sharpKernelEdge q) hAlpha hTotal]
  change M.center i *
      meanProjection
        (fun j ↦ M.harmonicMass j * M.center j ^ 2)
          (graphOperator M.sharpKernelEdge q) i = _
  rw [M.meanProjection_sharpGraph_eq q]

/-- Exact raw-coordinate form of
`continuumSharpOperator_eq_graph_add_residual`. -/
theorem rawOperator_eq_scaledGraph_add_residual
    (b : Band → ℝ) (i : Band) :
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b i =
      M.center i * graphOperator M.sharpKernelEdge
          (fun j ↦ b j / M.center j) i + M.rowResidual i * b i := by
  let q : Band → ℝ := fun j ↦ b j / M.center j
  have hAlpha : ∀ j, M.center j ≠ 0 := fun j ↦ ne_of_gt (M.center_pos j)
  have hb : b = scaleByCenter M.center q := by
    funext j
    dsimp only [q, scaleByCenter]
    field_simp [hAlpha j]
  calc
    rawOperator M.normalizedDiagonalCell M.normalizedKernelCell b i =
        rawOperator M.normalizedDiagonalCell M.normalizedKernelCell
          (scaleByCenter M.center q) i := by rw [← hb]
    _ = M.center i *
        CompressedArithmeticOperator.sharpOperator
          M.normalizedDiagonalCell M.normalizedKernelCell M.center q i :=
      rawOperator_scale_eq M.normalizedDiagonalCell M.normalizedKernelCell
        M.center q hAlpha i
    _ = M.center i * M.continuumSharpOperator q i := rfl
    _ = M.center i *
          (graphOperator M.sharpKernelEdge q i + M.rowResidual i * q i) := by
      rw [M.continuumSharpOperator_eq_graph_add_residual q i]
    _ = M.center i * graphOperator M.sharpKernelEdge
          (fun j ↦ b j / M.center j) i + M.rowResidual i * b i := by
      dsimp only [q]
      have hi : M.center i * (b i / M.center i) = b i := by
        field_simp [hAlpha i]
      calc
        M.center i *
            (graphOperator M.sharpKernelEdge
                (fun j ↦ b j / M.center j) i +
              M.rowResidual i * (b i / M.center i)) =
            M.center i * graphOperator M.sharpKernelEdge
                (fun j ↦ b j / M.center j) i +
              M.rowResidual i *
                (M.center i * (b i / M.center i)) := by ring
        _ = _ := by rw [hi]

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
