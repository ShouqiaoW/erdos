import Erdos390.Full.PaperCanonicalActualFullQuotientNullIdentification
import Erdos390.Full.PaperPrimeDeviationGeometry
import Erdos390.Full.SquarefreeReferenceOperatorIdentification

/-!
# Exact finite reference estimate for the slow right row

This file isolates the moving-low-cell estimate which is easy to lose if
one bounds the Dickman diagonal by an absolute constant.  The arithmetic
deviation is centred on every actual prime fiber.  We therefore subtract
`F (alpha_i)` in the diagonal term before estimating it.  The resulting
bound retains the factor `alpha_i`, including on the low cell where
`alpha_i` tends to zero.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeSharpBandTransfer SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open PrimeSquarefreeDirichletGeometry
open FiniteAnchoredDirichletQuadratic
open ConditionedPoissonLimit DickmanBasic

namespace PaperActualSlowRightRowFinite

/-- A uniform Lipschitz constant for the Dickman diagonal profile on the
closed unit interval.  This is extracted from the already proved
differentiability and continuity of `F`; it is independent of every mesh,
cutoff, ambient integer, and tilt box. -/
theorem exists_F_lipschitz_unit :
    ∃ CF : ℝ, 0 < CF ∧ ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |F s - F t| ≤ CF * |s - t| := by
  have hcontinuous : ContinuousOn (fun x : ℝ => ‖deriv F x‖)
      (Set.Icc (0 : ℝ) 1) := by
    exact (continuousOn_deriv_F.mono (Set.Icc_subset_Icc_right
      (by norm_num : (1 : ℝ) ≤ 2))).norm
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1)) hcontinuous
  let CF : ℝ := 1 + ‖deriv F x‖
  have hCF : 0 < CF := by
    dsimp only [CF]
    positivity
  refine ⟨CF, hCF, ?_⟩
  intro s hs t ht
  have hderiv (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      ‖deriv F u‖ ≤ CF := by
    dsimp only [CF]
    exact (hmax hu).trans (le_add_of_nonneg_left (by norm_num))
  have hbound := Convex.norm_image_sub_le_of_norm_deriv_le
    (f := F) (C := CF)
    (fun u hu => differentiableAt_F
      ⟨hu.1, hu.2.trans (by norm_num)⟩)
    hderiv (convex_Icc (0 : ℝ) 1) ht hs
  simpa only [Real.norm_eq_abs] using hbound

end PaperActualSlowRightRowFinite

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The signed Dickman reference row at the literal arithmetic band-centre
coefficient is relatively `O(w)` in every band, including the moving low
band.  The three contributions are visible in the conclusion:

* `rowError` is the finite prime row-sum defect on the exact logarithmic
  direction;
* `2 * CF * w` is the centred diagonal contribution;
* `7 * CKernel * w` is the product-kernel contribution.

The hypotheses are finite inequalities on the actual prime set.  In
particular, no continuum centre and no minimum-band-centre estimate occurs.
-/
theorem referenceBandRow_bandCenter_le_of_rowResidual
    {rowError w CF CKernel : ℝ}
    (hw : 0 ≤ w)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hrowResidual : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p| ≤
        rowError * tPrime B.sampleData.n p.1)
    (hFdiff : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) -
          F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |referenceBandRow B.partition B.bandCenter i| ≤
      (rowError + (2 * CF + 7 * CKernel) * w) * B.bandCenter i := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let base : ℝ := (1 / H) *
    ∑ p ∈ B.partition.data.fiber i,
      (1 / (p.1 : ℝ)) *
        rowResidual
          (primeWeight B.sampleData.n)
          (primeDiagonal B.sampleData.n)
          (primeKernel B.sampleData.n) p
  let diagonal : ℝ := (1 / H) *
    ∑ p ∈ B.partition.data.fiber i,
      (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
        B.primeDeviation p
  let kernel : ℝ := (1 / H) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q *
          covarianceKernel
            (tPrime B.sampleData.n p.1)
            (tPrime B.sampleData.n q.1) /
              ((p.1 : ℝ) * (q.1 : ℝ))
  have hH : 0 < H := by
    simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by
    simpa only [alpha] using B.bandCenter_pos i
  have htNonneg (p : BandPrime B.sampleData.n B.sampleData.W) :
      0 ≤ tPrime B.sampleData.n p.1 :=
    (B.bandPrime_tPrime_pos p).le
  have htOne (p : BandPrime B.sampleData.n B.sampleData.W) :
      tPrime B.sampleData.n p.1 ≤ 1 :=
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
      B.n_gt_one p.2
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hcenterDecomp (p : BandPrime B.sampleData.n B.sampleData.W) :
      B.bandCenter (B.partition.band p) =
        tPrime B.sampleData.n p.1 + B.primeDeviation p := by
    unfold primeDeviation
    ring
  have hfirstMoment :
      (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
        H * alpha := by
    change (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.harmonicMass i * B.bandCenter i
    unfold harmonicMass bandCenter
    change (∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
      B.partition.data.mass i *
        ((∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
            B.partition.data.mass i)
    field_simp [ne_of_gt (B.partition.data.mass_pos i)]
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band q) *
            squarefreeReferenceEntry B.sampleData.n p.1 q.1) =
        (1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p +
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p +
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
    have hdiag :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band q) *
            (if p.1 = q.1 then
              F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
            else 0)) =
          B.bandCenter (B.partition.band p) *
            (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q hq hqp
        have hpqVal : p.1 ≠ q.1 := by
          intro hpq
          exact hqp (Subtype.ext hpq.symm)
        simp [hpqVal]
      · simp
    have hkernelT :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n q.1 *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          (1 / (p.1 : ℝ)) *
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (tPrime B.sampleData.n q.1 / (q.1 : ℝ)) *
                covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      unfold squarefreeKernelEntry
      ring
    have hkernelG :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
      apply Finset.sum_congr rfl
      intro q hq
      unfold squarefreeKernelEntry
      ring
    simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal,
      mul_add]
    rw [Finset.sum_add_distrib, hdiag]
    simp_rw [hcenterDecomp, add_mul]
    rw [Finset.sum_add_distrib, hkernelT, hkernelG]
    unfold rowResidual primeWeight primeDiagonal primeKernel
    rw [mul_add, Finset.mul_sum]
    ring
  have href :
      referenceBandRow B.partition B.bandCenter i =
        base + diagonal + kernel := by
    unfold referenceBandRow base diagonal kernel H harmonicMass
    simp_rw [hinner]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    ring
  have hbase : |base| ≤ rowError * alpha := by
    unfold base
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / H : ℝ))]
    calc
      (1 / H) *
          |∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ)) *
              rowResidual
                (primeWeight B.sampleData.n)
                (primeDiagonal B.sampleData.n)
                (primeKernel B.sampleData.n) p| ≤
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            |(1 / (p.1 : ℝ)) *
              rowResidual
                (primeWeight B.sampleData.n)
                (primeDiagonal B.sampleData.n)
                (primeKernel B.sampleData.n) p| :=
          mul_le_mul_of_nonneg_left
            (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ)) *
              (rowError * tPrime B.sampleData.n p.1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p hp
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / (p.1 : ℝ)))]
        exact mul_le_mul_of_nonneg_left (hrowResidual p) (by positivity)
      _ = rowError * alpha := by
        rw [show (∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ)) *
              (rowError * tPrime B.sampleData.n p.1)) =
            rowError *
              (∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ)) *
                  tPrime B.sampleData.n p.1) by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          ring,
          hfirstMoment]
        field_simp [ne_of_gt hH]
  have hdiagonal : |diagonal| ≤ (2 * CF * w) * alpha := by
    have hcentered :
        (∑ p ∈ B.partition.data.fiber i,
          (F (alpha) / (p.1 : ℝ)) * B.primeDeviation p) = 0 := by
      rw [show (∑ p ∈ B.partition.data.fiber i,
          (F alpha / (p.1 : ℝ)) * B.primeDeviation p) =
          F alpha *
            (∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ)) * B.primeDeviation p) by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring,
        B.primeDeviation_fiber_sum]
      ring
    have hdiagRewrite : diagonal = (1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          ((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p := by
      unfold diagonal
      rw [show (∑ p ∈ B.partition.data.fiber i,
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) *
            B.primeDeviation p) =
        (∑ p ∈ B.partition.data.fiber i,
          ((F (tPrime B.sampleData.n p.1) - F alpha) /
              (p.1 : ℝ)) * B.primeDeviation p) +
        ∑ p ∈ B.partition.data.fiber i,
          (F alpha / (p.1 : ℝ)) * B.primeDeviation p by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro p hp
          ring,
        hcentered, add_zero]
    rw [hdiagRewrite, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ (1 / H : ℝ))]
    calc
      (1 / H) *
          |∑ p ∈ B.partition.data.fiber i,
            ((F (tPrime B.sampleData.n p.1) - F alpha) /
                (p.1 : ℝ)) * B.primeDeviation p| ≤
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            |((F (tPrime B.sampleData.n p.1) - F alpha) /
                (p.1 : ℝ)) * B.primeDeviation p| :=
          mul_le_mul_of_nonneg_left
            (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (CF * w) * ((1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p hp
        have hpBand : B.partition.band p = i :=
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
            B.partition.data).mp hp
        have hF :
            |F (tPrime B.sampleData.n p.1) - F alpha| ≤
              CF * |B.primeDeviation p| := by
          simpa only [alpha, hpBand] using hFdiff p
        rw [abs_mul, abs_div, abs_of_pos (hpPos p)]
        calc
          (|F (tPrime B.sampleData.n p.1) - F alpha| /
              (p.1 : ℝ)) * |B.primeDeviation p| ≤
            ((CF * |B.primeDeviation p|) / (p.1 : ℝ)) *
              |B.primeDeviation p| :=
                mul_le_mul_of_nonneg_right
                  (div_le_div_of_nonneg_right hF (hpPos p).le)
                  (abs_nonneg _)
          _ ≤ ((CF * w) / (p.1 : ℝ)) *
              |B.primeDeviation p| := by
                apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
                apply div_le_div_of_nonneg_right _ (hpPos p).le
                exact mul_le_mul_of_nonneg_left (hdevSup p) hCF
          _ = (CF * w) *
              ((1 / (p.1 : ℝ)) * |B.primeDeviation p|) := by ring
      _ ≤ (1 / H) *
          ((CF * w) * (2 * H * alpha)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Finset.mul_sum]
        exact mul_le_mul_of_nonneg_left
          (B.bandDeviationL1_le_two_mul_mass_mul_center i)
          (mul_nonneg hCF hw)
      _ = (2 * CF * w) * alpha := by
        field_simp [ne_of_gt hH]
  have hkernel : |kernel| ≤ (7 * CKernel * w) * alpha := by
    unfold kernel
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / H : ℝ))]
    calc
      (1 / H) *
          |∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) /
                    ((p.1 : ℝ) * (q.1 : ℝ))| ≤
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q *
                covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) /
                    ((p.1 : ℝ) * (q.1 : ℝ))| := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p hp ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
              (CKernel * B.primeDeviationL1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p hp
        calc
          (∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q *
              covarianceKernel
                (tPrime B.sampleData.n p.1)
                (tPrime B.sampleData.n q.1) /
                  ((p.1 : ℝ) * (q.1 : ℝ))|) ≤
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
                (CKernel *
                  ((1 / (q.1 : ℝ)) * |B.primeDeviation q|)) := by
            apply Finset.sum_le_sum
            intro q hq
            rw [abs_div,
              abs_of_pos (mul_pos (hpPos p) (hpPos q)), abs_mul]
            have hK := hKernelProduct p q
            calc
              (|B.primeDeviation q| *
                    |covarianceKernel
                      (tPrime B.sampleData.n p.1)
                      (tPrime B.sampleData.n q.1)|) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) ≤
                (|B.primeDeviation q| *
                    (CKernel * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1)) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
                    apply div_le_div_of_nonneg_right _ (by positivity)
                    exact mul_le_mul_of_nonneg_left hK (abs_nonneg _)
              _ ≤
                (|B.primeDeviation q| *
                    (CKernel * tPrime B.sampleData.n p.1 * 1)) /
                  ((p.1 : ℝ) * (q.1 : ℝ)) := by
                    apply div_le_div_of_nonneg_right _ (by positivity)
                    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
                    exact mul_le_mul_of_nonneg_left (htOne q)
                      (mul_nonneg hCKernel (htNonneg p))
              _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
                  (CKernel *
                    ((1 / (q.1 : ℝ)) * |B.primeDeviation q|)) := by
                    ring
          _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
              (CKernel * B.primeDeviationL1) := by
            unfold primeDeviationL1
            rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 / H) *
          ((H * alpha) * (CKernel * (7 * w))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hcoefNonneg : 0 ≤
            ∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 / (p.1 : ℝ) :=
          Finset.sum_nonneg fun p hp ↦ div_nonneg (htNonneg p) (hpPos p).le
        have hfirstDiv :
            (∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = H * alpha := by
          calc
            (∑ p ∈ B.partition.data.fiber i,
                tPrime B.sampleData.n p.1 / (p.1 : ℝ)) =
              ∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 := by
                  apply Finset.sum_congr rfl
                  intro p hp
                  ring
            _ = H * alpha := hfirstMoment
        rw [← Finset.sum_mul]
        rw [hfirstDiv]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hdevL1 hCKernel)
          (mul_nonneg hH.le halpha.le)
      _ = (7 * CKernel * w) * alpha := by
        field_simp [ne_of_gt hH]
  rw [href]
  calc
    |base + diagonal + kernel| ≤ |base| + |diagonal| + |kernel| := by
      exact (abs_add_le (base + diagonal) kernel).trans
        (add_le_add (abs_add_le base diagonal) le_rfl)
    _ ≤ rowError * alpha + (2 * CF * w) * alpha +
          (7 * CKernel * w) * alpha :=
      add_le_add (add_le_add hbase hdiagonal) hkernel
    _ = (rowError + (2 * CF + 7 * CKernel) * w) *
          B.bandCenter i := by
      dsimp only [alpha]
      ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
