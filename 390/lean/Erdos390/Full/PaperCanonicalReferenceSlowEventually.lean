import Erdos390.Full.PaperNonstepReferenceSlowDirect
import Erdos390.Full.PaperCanonicalActualMomentBoundsEventually

/-!
# Canonical direct reference slow-row bound

The identity part of the Dickman diagonal is cancelled exactly on each
arithmetic prime fibre.  The remaining diagonal and kernel terms both carry
the literal first moment of that fibre.  Consequently the constant below is
universal: it is chosen before `W`, `delta`, `eta`, and the mesh, and no
factor such as `1 / delta` occurs.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PaperActualSlowRightRowFinite
open ConditionedPoissonLimit DickmanBasic
open RegularMeshPrimeCutoffs

namespace BridgeData

/-- Global-order canonical reference-row terminal.  The constants are
universal and `W₀` is selected before the paper scale and mesh. -/
theorem exists_global_cutoff_eventually_canonical_referenceSlowRow_le :
    ∃ CF Cprod : ℝ, 0 ≤ CF ∧ 0 ≤ Cprod ∧
      ∃ W₀ : ℕ, ∀ W : ℕ, W₀ ≤ W →
      ∀ {delta eta : ℝ} (hdelta : 0 < delta)
        (M : RegularRelativeMesh.Mesh delta eta),
        ∀ᶠ n : ℕ in atTop,
          ∀ {Head : Type*} [Fintype Head] [DecidableEq Head]
            (B : BridgeData Head (Fin (M.cellCount + 1))),
            B.sampleData.n = n → B.sampleData.W = W →
            (∃ (hWne : B.sampleData.W ≠ 0)
              (S : ScaleSeparation M B.sampleData.n B.sampleData.W),
              B.partition = Mesh.canonicalPartition
                M hdelta B.n_gt_one hWne S) →
            B.w = delta + eta →
            ∀ i : Fin (M.cellCount + 1),
              |B.referenceSlowRow i| ≤
                (CF + 7 * Cprod) *
                  B.w * B.bandCenter i := by
  obtain ⟨CF, hCFpos, hFLipschitz⟩ := exists_F_lipschitz_unit
  obtain ⟨Cprod, hCprod, hProduct⟩ := kernel_product_bound
  let W₀ : ℕ := canonicalActualMomentCutoff
  refine ⟨CF, Cprod, hCFpos.le, hCprod.le, W₀, ?_⟩
  intro W hW delta eta hdelta M
  have hWmoment : canonicalActualMomentCutoff ≤ W := by
    dsimp only [W₀] at hW
    exact hW
  have hMoment :=
    Mesh.canonicalActualFirstMomentCutoff_eventually M hdelta W hWmoment
  filter_upwards [hMoment] with n hMomentN
  intro Head _instFintype _instDecidable B hBn hBW hpartition hscale i
  subst n
  subst W
  obtain ⟨_hWneMoment, _hnMoment, hMomentAll⟩ := hMomentN
  obtain ⟨hWne, S, hpartitionUser⟩ := hpartition
  let Pcanonical := Mesh.canonicalPartition M hdelta B.n_gt_one hWne S
  have hpartitionCanonical : B.partition = Pcanonical := by
    exact hpartitionUser.trans (by rfl)
  obtain ⟨hdevSupRaw, hdevL1Raw⟩ := hMomentAll S
  have hactualScale : delta + M.ratio ≤ B.w := by
    rw [hscale]
    linarith [M.ratio_le_eta]
  have hw : 0 < B.w :=
    (add_pos hdelta M.ratio_pos).trans_le hactualScale
  have hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ B.w := by
    intro p
    change |B.partition.deviation p| ≤ B.w
    rw [hpartitionCanonical]
    exact (hdevSupRaw p).trans hactualScale
  have hdevL1 : B.primeDeviationL1 ≤ 7 * B.w := by
    change B.partition.totalL1 ≤ 7 * B.w
    rw [hpartitionCanonical]
    exact hdevL1Raw.trans
      (mul_le_mul_of_nonneg_left hactualScale (by norm_num))
  have hFone : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) - 1| ≤
        CF * tPrime B.sampleData.n p.1 := by
    intro p
    have ht : tPrime B.sampleData.n p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos p).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one p.2⟩
    have h := hFLipschitz _ ht 0 (by norm_num)
    simpa only [F_zero, sub_zero, abs_of_nonneg ht.1] using h
  have hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        Cprod * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1 := by
    intro p q
    have hp : tPrime B.sampleData.n p.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos p).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one p.2⟩
    have hq : tPrime B.sampleData.n q.1 ∈ Icc (0 : ℝ) 1 :=
      ⟨(B.bandPrime_tPrime_pos q).le,
        PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
          B.n_gt_one q.2⟩
    simpa only [covarianceKernel] using hProduct _ hp _ hq
  exact B.abs_referenceSlowRow_le_of_harmonicCentering
    hw.le hCprod.le hFone hKernelProduct hdevSup hdevL1 i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
