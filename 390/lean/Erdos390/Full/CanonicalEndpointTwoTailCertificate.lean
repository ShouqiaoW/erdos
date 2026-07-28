import Erdos390.Full.CanonicalEndpointIntervalMesh
import Erdos390.Full.ContinuumTwoTailResidualBound

/-!
# Exact two-tail coverage of the canonical endpoint mesh

Consecutive natural cutoffs telescope exactly.  The first endpoint is the
fixed cutoff coordinate and the last is the `floor y` coordinate, so this
produces the two-tail certificate required by the honest residual theorem.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.RegularMeshPrimeCutoffs

open ArithmeticModel RegularRelativeMesh
open KernelPrimeQuadrature
open ConditionedPoissonLimit
open ContinuumCellGraph
open ContinuumCellGraph.IntervalMesh
open MeasureTheory

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

private theorem continuous_inner_endpointKernel
    (a b : ℝ) :
    Continuous (fun s : ℝ =>
      ∫ t in a..b, covarianceKernelQuotient t s) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (a₀ := a) (b₀ := b)
  exact continuous_uncurry_covarianceKernelQuotient.comp
    (continuous_snd.prodMk continuous_fst)

/-- The canonical interval mesh covers exactly from the coordinate of `W`
to the coordinate of `floor y`. -/
def canonicalTwoTailCertificate
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≠ 0) (hWTwo : 2 ≤ W)
    (S : ScaleSeparation M n W)
    (epsilon : ℝ) (anchorCell : Fin M.cellCount)
    (hInteriorLower hInteriorUpper) :
    let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S
      epsilon anchorCell hInteriorLower hInteriorUpper
    IM.TwoTailPartitionCertificate := by
  let E := canonicalCertificate M hdelta hn hW S
  let IM := canonicalIntervalMesh M hdelta hn hW hWTwo S
    epsilon anchorCell hInteriorLower hInteriorUpper
  let a : ℕ → ℝ := fun k =>
    realLogCoordinate (y n) (fullCutoff M n W k : ℝ)
  have hylog : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (Real.log_pos (by exact_mod_cast hn))
  have hbasePos : 0 < a 0 := by
    dsimp only [a, fullCutoff]
    unfold realLogCoordinate
    exact div_pos (Real.log_pos (by exact_mod_cast (show 1 < W by omega))) hylog
  have hmono : Monotone (fullCutoff M n W) :=
    fullCutoff_monotone M hdelta hn (W_le_first_fullCutoff M S)
  have haMono : Monotone a := by
    intro r s hrs
    dsimp only [a]
    have hrTwo : 2 ≤ fullCutoff M n W r :=
      hWTwo.trans (hmono (Nat.zero_le r))
    exact DoubleKernelPrimeQuadrature.realLogCoordinate_mono_nat
      (by
        exact (Real.log_pos_iff (Scale.y_pos
          (Nat.zero_lt_of_lt hn)).le).mp hylog)
      hrTwo (hmono hrs)
  have htopOne : a (M.cellCount + 1) ≤ 1 := by
    dsimp only [a]
    rw [fullCutoff_last M (Nat.zero_lt_of_lt hn)]
    have hypos := Scale.y_pos (Nat.zero_lt_of_lt hn)
    have hfloorPos : (0 : ℝ) < (yNat n : ℝ) := by
      have : 2 ≤ yNat n := by
        rw [← fullCutoff_last M (Nat.zero_lt_of_lt hn)]
        exact hWTwo.trans (hmono (Nat.zero_le _))
      positivity
    unfold realLogCoordinate
    apply (div_le_iff₀ hylog).2
    simpa only [one_mul] using Real.log_le_log hfloorPos
      (Nat.floor_le hypos.le)
  refine {
    base := a 0
    upperEnd := a (M.cellCount + 1)
    base_nonneg := hbasePos.le
    base_le_upperEnd := haMono (Nat.zero_le _)
    upperEnd_le_one := htopOne
    totalLength := ?_
    kernelDoubleIntegral_split := ?_
  }
  · change (∑ j : Fin (M.cellCount + 1),
        (a (j.1 + 1) - a j.1)) =
      a (M.cellCount + 1) - a 0
    calc
      (∑ j : Fin (M.cellCount + 1), (a (j.1 + 1) - a j.1)) =
          ∑ k ∈ Finset.range (M.cellCount + 1),
            (a (k + 1) - a k) := by
        simpa only using Fin.sum_univ_eq_sum_range
          (fun k : ℕ => a (k + 1) - a k) (M.cellCount + 1)
      _ = a (M.cellCount + 1) - a 0 := by
        rw [Finset.sum_range_sub]
  · intro i
    change (∑ j : Fin (M.cellCount + 1),
      ∫ s in a i.1..a (i.1 + 1),
        ∫ t in a j.1..a (j.1 + 1),
          covarianceKernelQuotient t s) =
      ∫ s in a i.1..a (i.1 + 1),
        ∫ t in a 0..a (M.cellCount + 1),
          covarianceKernelQuotient t s
    rw [← intervalIntegral.integral_finset_sum]
    · apply intervalIntegral.integral_congr
      intro s hs
      change (∑ j : Fin (M.cellCount + 1),
          ∫ t in a j.1..a (j.1 + 1),
            covarianceKernelQuotient t s) =
        ∫ t in a 0..a (M.cellCount + 1),
          covarianceKernelQuotient t s
      calc
        (∑ j : Fin (M.cellCount + 1),
            ∫ t in a j.1..a (j.1 + 1),
              covarianceKernelQuotient t s) =
            ∑ k ∈ Finset.range (M.cellCount + 1),
              ∫ t in a k..a (k + 1),
                covarianceKernelQuotient t s := by
          simpa only using Fin.sum_univ_eq_sum_range
            (fun k : ℕ =>
              ∫ t in a k..a (k + 1), covarianceKernelQuotient t s)
            (M.cellCount + 1)
        _ = _ := intervalIntegral.sum_integral_adjacent_intervals
          (fun k hk =>
            (continuous_uncurry_covarianceKernelQuotient.comp
              (continuous_id.prodMk continuous_const)).intervalIntegrable _ _)
    · intro j hj
      exact (continuous_inner_endpointKernel (a j.1) (a (j.1 + 1))).intervalIntegrable _ _

end Mesh
end Erdos390.Full.RegularMeshPrimeCutoffs
