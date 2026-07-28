import Erdos390.Full.ContinuumCellGraph

/-!
# Endpoint bounds for the logarithmic mean

The continuum cell centre is the logarithmic mean of its endpoints.  These
elementary endpoint bounds are used by the moving-prefix ordinary inverse.
-/

open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

variable {epsilon : ℝ} {Band : Type*} [Fintype Band]
  (M : IntervalMesh epsilon Band)

theorem harmonicMass_eq_log_div (i : Band) :
    M.harmonicMass i = Real.log (M.upper i / M.lower i) := by
  unfold harmonicMass
  rw [integral_one_div_of_pos (M.lower_pos i)
    ((M.lower_pos i).trans (M.lower_lt_upper i))]

/-- The logarithmic mean lies between the two cell endpoints. -/
theorem lower_le_center (i : Band) : M.lower i ≤ M.center i := by
  have ha : 0 < M.lower i := M.lower_pos i
  have hb : 0 < M.upper i := ha.trans (M.lower_lt_upper i)
  have hratio : 0 < M.upper i / M.lower i := div_pos hb ha
  have hlog := Real.log_le_sub_one_of_pos hratio
  have hmass : M.harmonicMass i ≤ M.length i / M.lower i := by
    rw [M.harmonicMass_eq_log_div]
    calc
      Real.log (M.upper i / M.lower i) ≤
          M.upper i / M.lower i - 1 := hlog
      _ = M.length i / M.lower i := by
        unfold length
        field_simp [ne_of_gt ha]
  have hmul : M.lower i * M.harmonicMass i ≤ M.length i := by
    calc
      M.lower i * M.harmonicMass i ≤
          M.lower i * (M.length i / M.lower i) :=
        mul_le_mul_of_nonneg_left hmass ha.le
      _ = M.length i := by field_simp [ne_of_gt ha]
  rw [center]
  exact (le_div_iff₀ (M.harmonicMass_pos i)).2 (by
    simpa only [mul_comm] using hmul)

theorem center_le_upper (i : Band) : M.center i ≤ M.upper i := by
  have ha : 0 < M.lower i := M.lower_pos i
  have hb : 0 < M.upper i := ha.trans (M.lower_lt_upper i)
  have hratio : 0 < M.upper i / M.lower i := div_pos hb ha
  have hlog := Real.one_sub_inv_le_log_of_pos hratio
  have hmass : M.length i / M.upper i ≤ M.harmonicMass i := by
    rw [M.harmonicMass_eq_log_div]
    have hid : 1 - (M.upper i / M.lower i)⁻¹ =
        M.length i / M.upper i := by
      unfold length
      field_simp [ne_of_gt ha, ne_of_gt hb]
    simpa only [hid] using hlog
  rw [center]
  exact (div_le_iff₀ (M.harmonicMass_pos i)).2 (by
    have hmul := mul_le_mul_of_nonneg_left hmass hb.le
    have hcancel :
        M.upper i * (M.length i / M.upper i) = M.length i := by
      field_simp [ne_of_gt hb]
    nlinarith)

/-- Harmonic mass times the logarithmic mean is exactly the ordinary cell
length.  This identity is the arithmetic/continuum raw-gauge comparison;
it does not replace an arithmetic centre by a continuum centre. -/
theorem harmonicMass_mul_center_eq_length (i : Band) :
    M.harmonicMass i * M.center i = M.length i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
