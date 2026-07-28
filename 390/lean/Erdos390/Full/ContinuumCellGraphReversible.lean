import Erdos390.Full.ContinuumCellGraph
import Erdos390.Full.FiniteReversibleGraph

/-!
# Reversibility of the continuum cell graph

After the centre conjugation, the cell edge is reversible for the exact
sharp gauge weight `H_i alpha_i^2`.  The proof below keeps the moving low
cell: all divisions occur on its positive interval `[t₀,δ]`, and no lower
bound independent of `t₀` is used.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full.ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open FiniteGraphQuotientInverse
open FiniteReversibleGraph

variable {Band : Type*} [Fintype Band] [DecidableEq Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

omit [DecidableEq Band] in
private theorem sharpEdgeIntegrand_comm
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (hs0 : s ≠ 0) (ht0 : t ≠ 0) :
    (-covarianceKernelQuotient t s) / t =
      (-covarianceKernelQuotient s t) / s := by
  rw [covarianceKernelQuotient_eq_div ht hs hs0,
    covarianceKernelQuotient_eq_div hs ht ht0,
    covarianceKernel_comm t s]
  field_simp [hs0, ht0]

omit [DecidableEq Band] in
private theorem doubleSharpIntegral_comm (i j : Band) :
    (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
    ∫ s in M.lower j..M.upper j,
      ∫ t in M.lower i..M.upper i,
        (-covarianceKernelQuotient t s) / t := by
  let g : ℝ → ℝ → ℝ := fun s t ↦
    (-covarianceKernelQuotient t s) / t
  let R : Set (ℝ × ℝ) :=
    Icc (M.lower i) (M.upper i) ×ˢ Icc (M.lower j) (M.upper j)
  have hg : ContinuousOn (Function.uncurry g) R := by
    intro z hz
    have htz : z.2 ≠ 0 :=
      ne_of_gt ((M.lower_pos j).trans_le hz.2.1)
    exact (((continuous_uncurry_covarianceKernelQuotient.comp
      (continuous_snd.prodMk continuous_fst)).neg).continuousAt.div
        continuousAt_snd htz).continuousWithinAt
  have hIntegrableOn : IntegrableOn (Function.uncurry g)
      (Ioc (M.lower i) (M.upper i) ×ˢ
        Ioc (M.lower j) (M.upper j)) := by
    apply (hg.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hIntegrable : Integrable (Function.uncurry g)
      ((volume.restrict (Ioc (M.lower i) (M.upper i))).prod
        (volume.restrict (Ioc (M.lower j) (M.upper j)))) := by
    rw [Measure.prod_restrict]
    exact hIntegrableOn
  have hswap :
      (∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j, g s t) =
      ∫ t in M.lower j..M.upper j,
        ∫ s in M.lower i..M.upper i, g s t := by
    simp_rw [intervalIntegral.integral_of_le
      (le_of_lt (M.lower_lt_upper i)),
      intervalIntegral.integral_of_le
        (le_of_lt (M.lower_lt_upper j))]
    exact integral_integral_swap hIntegrable
  rw [show (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        (-covarianceKernelQuotient t s) / t) =
      ∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j, g s t by rfl,
    hswap]
  apply intervalIntegral.integral_congr
  intro s _hs
  apply intervalIntegral.integral_congr
  intro t _ht
  dsimp only [g]
  have hscc : s ∈ Icc (M.lower j) (M.upper j) := by
    simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using _hs
  have htcc : t ∈ Icc (M.lower i) (M.upper i) := by
    simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using _ht
  exact sharpEdgeIntegrand_comm
    (M.cell_mem_unit htcc) (M.cell_mem_unit hscc)
    (ne_of_gt ((M.lower_pos i).trans_le htcc.1))
    (ne_of_gt ((M.lower_pos j).trans_le hscc.1))

omit [DecidableEq Band] in
/-- The exact harmonic-centre gauge weight equals `length * center`. -/
theorem harmonicMass_mul_center_sq_eq (i : Band) :
    M.harmonicMass i * M.center i ^ 2 = M.length i * M.center i := by
  unfold center
  field_simp [ne_of_gt (M.harmonicMass_pos i)]

omit [DecidableEq Band] in
/-- Exact detailed balance for the continuum sharp edge. -/
theorem sharpKernelEdge_detailedBalance (i j : Band) :
    (M.harmonicMass i * M.center i ^ 2) * M.sharpKernelEdge i j =
      (M.harmonicMass j * M.center j ^ 2) * M.sharpKernelEdge j i := by
  rw [M.harmonicMass_mul_center_sq_eq i,
    M.harmonicMass_mul_center_sq_eq j]
  unfold sharpKernelEdge
  rw [M.doubleSharpIntegral_comm i j]
  field_simp [ne_of_gt (M.length_pos i), ne_of_gt (M.length_pos j)]

omit [DecidableEq Band] in
/-- The weighted mean of the continuum graph row is identically zero. -/
theorem weightedMean_sharpGraph_eq_zero (q : Band → ℝ) :
    weightedMean (fun i ↦ M.harmonicMass i * M.center i ^ 2)
      (graphOperator M.sharpKernelEdge q) = 0 := by
  exact weightedMean_graphOperator_eq_zero M.sharpKernelEdge
    (fun i ↦ M.harmonicMass i * M.center i ^ 2) q
    M.sharpKernelEdge_detailedBalance

omit [DecidableEq Band] in
/-- Hence the projected and unprojected reference rows coincide exactly. -/
theorem meanProjection_sharpGraph_eq (q : Band → ℝ) :
    meanProjection (fun i ↦ M.harmonicMass i * M.center i ^ 2)
        (graphOperator M.sharpKernelEdge q) =
      graphOperator M.sharpKernelEdge q := by
  exact meanProjection_graphOperator_eq M.sharpKernelEdge
    (fun i ↦ M.harmonicMass i * M.center i ^ 2) q
    M.sharpKernelEdge_detailedBalance

end IntervalMesh
end Erdos390.Full.ContinuumCellGraph
