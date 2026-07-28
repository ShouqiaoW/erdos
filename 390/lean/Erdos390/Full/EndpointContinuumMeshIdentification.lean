import Erdos390.Full.ContinuumRowResidualBound

/-!
# Exact identification of endpoint continuum cells with an interval mesh

The prime-quadrature modules use natural endpoints and logarithmic
coordinates, whereas the continuum graph is phrased directly in physical
intervals.  This file proves that the two diagonal and double-kernel
matrices are literally the same after identifying endpoints.  The kernel
proof includes the required Fubini swap on positive rectangles.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.Full
namespace ContinuumCellGraph
namespace IntervalMesh

open MeasureTheory
open ConditionedPoissonLimit
open KernelPrimeQuadrature
open DoubleKernelPrimeQuadrature
open DiagonalPrimeQuadrature
open CompressedArithmeticOperator

variable {Band : Type*} [Fintype Band]
variable {epsilon : ℝ} (M : IntervalMesh epsilon Band)

private theorem double_intervalIntegral_swap_of_continuous
    {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    {g : ℝ → ℝ → ℝ} (hg : Continuous (Function.uncurry g)) :
    (∫ s in a..b, ∫ t in c..d, g s t) =
      ∫ t in c..d, ∫ s in a..b, g s t := by
  have hIntegrableOn : IntegrableOn (Function.uncurry g)
      (Ioc a b ×ˢ Ioc c d) := by
    apply (hg.continuousOn.integrableOn_compact
      (isCompact_Icc.prod isCompact_Icc)).mono_set
    exact prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self
  have hIntegrable : Integrable (Function.uncurry g)
      ((volume.restrict (Ioc a b)).prod
        (volume.restrict (Ioc c d))) := by
    rw [Measure.prod_restrict]
    exact hIntegrableOn
  simp_rw [intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_of_le hcd]
  exact integral_integral_swap hIntegrable

theorem harmonicMass_eq_continuumCellMass
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i : Band) :
    M.harmonicMass i = continuumCellMass z (lower i) (upper i) := by
  have hlo : 0 < realLogCoordinate z (lower i : ℝ) := by
    rw [← hLower]
    exact M.lower_pos i
  have hup : 0 < realLogCoordinate z (upper i : ℝ) := by
    rw [← hUpper]
    exact (M.lower_pos i).trans (M.lower_lt_upper i)
  unfold harmonicMass continuumCellMass
  rw [hLower, hUpper, integral_one_div_of_pos hlo hup,
    Real.log_div hup.ne' hlo.ne']

theorem normalizedDiagonalCell_eq_endpointContinuum
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i : Band) :
    M.normalizedDiagonalCell i = continuumDiagonal z lower upper i := by
  unfold normalizedDiagonalCell continuumDiagonal
  unfold normalizedDiagonalContinuumCell diagonalContinuumCell
    continuumCellOperator
  rw [hLower, hUpper, M.harmonicMass_eq_continuumCellMass
    z lower upper hLower hUpper i]

private theorem doubleKernelNumerator_eq_endpointContinuum
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i j : Band) :
    (∫ s in M.lower i..M.upper i,
      ∫ t in M.lower j..M.upper j,
        covarianceKernelQuotient t s / t) =
      doubleContinuumKernelCell z
        (lower i) (upper i) (lower j) (upper j) := by
  let di : ℝ → ℝ := fun s => max s (M.lower i / 2)
  let dj : ℝ → ℝ := fun t => max t (M.lower j / 2)
  let g : ℝ → ℝ → ℝ := fun s t =>
    covarianceKernel t s / di s / dj t
  have hdiCont : Continuous di :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower i / 2)
  have hdjCont : Continuous dj :=
    continuous_id.max
      (continuous_const : Continuous fun _ : ℝ => M.lower j / 2)
  have hdi0 (s : ℝ) : di s ≠ 0 := by
    apply ne_of_gt
    exact (half_pos (M.lower_pos i)).trans_le (le_max_right _ _)
  have hdj0 (t : ℝ) : dj t ≠ 0 := by
    apply ne_of_gt
    exact (half_pos (M.lower_pos j)).trans_le (le_max_right _ _)
  have hg : Continuous (Function.uncurry g) := by
    dsimp only [g, Function.uncurry]
    exact (continuous_covarianceKernel.comp
      (continuous_snd.prodMk continuous_fst)).div
        (hdiCont.comp continuous_fst) (fun x => hdi0 x.1) |>.div
        (hdjCont.comp continuous_snd) (fun x => hdj0 x.2)
  have hdiCell {s : ℝ} (hs : s ∈ Icc (M.lower i) (M.upper i)) :
      di s = s := by
    have hhalf : M.lower i / 2 ≤ s := by
      linarith [M.lower_pos i, hs.1]
    simp [di, max_eq_left hhalf]
  have hdjCell {t : ℝ} (ht : t ∈ Icc (M.lower j) (M.upper j)) :
      dj t = t := by
    have hhalf : M.lower j / 2 ≤ t := by
      linarith [M.lower_pos j, ht.1]
    simp [dj, max_eq_left hhalf]
  have hleft :
      (∫ s in M.lower i..M.upper i,
        ∫ t in M.lower j..M.upper j,
          covarianceKernelQuotient t s / t) =
        ∫ s in M.lower i..M.upper i,
          ∫ t in M.lower j..M.upper j, g s t := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    have hsUnit := M.cell_mem_unit hscc
    have htUnit := M.cell_mem_unit htcc
    have hs0 : s ≠ 0 := ne_of_gt ((M.lower_pos i).trans_le hscc.1)
    unfold g
    rw [hdiCell hscc, hdjCell htcc]
    change covarianceKernelQuotient t s / t =
      covarianceKernel t s / s / t
    rw [covarianceKernelQuotient_eq_div htUnit hsUnit hs0]
  have hright :
      (∫ t in M.lower j..M.upper j,
        ∫ s in M.lower i..M.upper i, g s t) =
      doubleContinuumKernelCell z
        (lower i) (upper i) (lower j) (upper j) := by
    unfold doubleContinuumKernelCell continuumCellOperator
    rw [← hLower i, ← hUpper i, ← hLower j, ← hUpper j]
    apply intervalIntegral.integral_congr
    intro t ht
    have htcc : t ∈ Icc (M.lower j) (M.upper j) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper j))] using ht
    change (∫ s in M.lower i..M.upper i, g s t) =
      (∫ s in M.lower i..M.upper i,
        covarianceKernel t s / s) / t
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro s hs
    have hscc : s ∈ Icc (M.lower i) (M.upper i) := by
      simpa [uIcc_of_le (le_of_lt (M.lower_lt_upper i))] using hs
    unfold g
    change covarianceKernel t s / di s / dj t =
      covarianceKernel t s / s / t
    rw [hdiCell hscc, hdjCell htcc]
  rw [hleft,
    double_intervalIntegral_swap_of_continuous
      (le_of_lt (M.lower_lt_upper i))
      (le_of_lt (M.lower_lt_upper j)) hg,
    hright]

theorem normalizedKernelCell_eq_endpointContinuum
    (z : ℝ) (lower upper : Band → ℕ)
    (hLower : ∀ i, M.lower i = realLogCoordinate z (lower i : ℝ))
    (hUpper : ∀ i, M.upper i = realLogCoordinate z (upper i : ℝ))
    (i j : Band) :
    M.normalizedKernelCell i j = continuumKernel z lower upper i j := by
  unfold normalizedKernelCell continuumKernel
  unfold normalizedDoubleContinuumKernelCell
  rw [M.doubleKernelNumerator_eq_endpointContinuum
      z lower upper hLower hUpper i j,
    M.harmonicMass_eq_continuumCellMass
      z lower upper hLower hUpper i]

end IntervalMesh
end ContinuumCellGraph
end Erdos390.Full
