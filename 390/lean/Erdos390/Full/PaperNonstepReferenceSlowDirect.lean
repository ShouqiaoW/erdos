import Erdos390.Full.PaperNonstepSquarefreeSlowLedger
import Erdos390.Full.PaperActualSlowRightRowFinite

/-!
# Direct harmonic-centering bound for the non-step reference slow row

This finite lemma avoids a prime-row residual altogether.  The diagonal
identity term cancels exactly because `sum_{p in P_i} g_p/p = 0`.  What
remains is bounded by the local product moment `sum t_p |g_p|/p`; the kernel
term factors into the output first moment and the corresponding global
product moment.  Thus every contribution contains `w * alpha_i` with a
universal constant.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open SquarefreeCovarianceReference
open SquarefreeReferenceOperatorIdentification
open ConditionedPoissonLimit DickmanBasic

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Direct universal reference bound for the literal non-step coefficient.
No row-residual, least-centre, mesh, or asymptotic hypothesis occurs. -/
theorem abs_referenceSlowRow_le_of_harmonicCentering
    {w CF CKernel : ℝ}
    (hw : 0 ≤ w) (hCKernel : 0 ≤ CKernel)
    (hFone : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |F (tPrime B.sampleData.n p.1) - 1| ≤
        CF * tPrime B.sampleData.n p.1)
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
    |B.referenceSlowRow i| ≤
      (CF + 7 * CKernel) * w * B.bandCenter i := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let diagonal : ℝ := (1 / H) *
    ∑ p ∈ B.partition.data.fiber i,
      B.primeDeviation p *
        (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ))
  let kernel : ℝ := (1 / H) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q *
          covarianceKernel
            (tPrime B.sampleData.n p.1)
            (tPrime B.sampleData.n q.1) /
              ((p.1 : ℝ) * (q.1 : ℝ))
  let globalProduct : ℝ :=
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
        (1 / (q.1 : ℝ))
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by simpa only [alpha] using B.bandCenter_pos i
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have ht0 (p : BandPrime B.sampleData.n B.sampleData.W) :
      0 ≤ tPrime B.sampleData.n p.1 :=
    (B.bandPrime_tPrime_pos p).le
  have ht1 (p : BandPrime B.sampleData.n B.sampleData.W) :
      tPrime B.sampleData.n p.1 ≤ 1 :=
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one p.2
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
  have hdiagInner (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q *
          (if p.1 = q.1 then
            F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
          else 0)) =
        B.primeDeviation p *
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
    rw [Finset.sum_eq_single p]
    · simp
    · intro q _hq hqp
      have hpqVal : p.1 ≠ q.1 := by
        intro hpq
        exact hqp (Subtype.ext hpq.symm)
      simp [hpqVal]
    · simp
  have href : B.referenceSlowRow i = diagonal + kernel := by
    unfold referenceSlowRow diagonal kernel H
    simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal, mul_add]
    rw [show
      (∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (B.primeDeviation q * squarefreeKernelEntry
              B.sampleData.n p.1 q.1 +
            B.primeDeviation q *
              (if p.1 = q.1 then
                F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
              else 0))) =
      (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ))) +
      ∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q * squarefreeKernelEntry
            B.sampleData.n p.1 q.1 by
        simp_rw [Finset.sum_add_distrib, hdiagInner]
        ring]
    unfold squarefreeKernelEntry
    ring
  have hcentered :
      (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p * (1 / (p.1 : ℝ))) = 0 := by
    rw [show (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p * (1 / (p.1 : ℝ))) =
      ∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) * B.primeDeviation p by
        apply Finset.sum_congr rfl
        intro p _hp
        ring]
    exact B.primeDeviation_fiber_sum i
  have hdiagRewrite : diagonal = (1 / H) *
      ∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          ((F (tPrime B.sampleData.n p.1) - 1) / (p.1 : ℝ)) := by
    unfold diagonal
    rw [show (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          (F (tPrime B.sampleData.n p.1) / (p.1 : ℝ))) =
      (∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p *
          ((F (tPrime B.sampleData.n p.1) - 1) / (p.1 : ℝ))) +
      ∑ p ∈ B.partition.data.fiber i,
        B.primeDeviation p * (1 / (p.1 : ℝ)) by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p _hp
        ring,
      hcentered, add_zero]
  have hdiagonal : |diagonal| ≤ (CF * w) * alpha := by
    rw [hdiagRewrite, abs_mul,
      abs_of_nonneg (one_div_nonneg.mpr hH.le)]
    calc
      (1 / H) *
          |∑ p ∈ B.partition.data.fiber i,
            B.primeDeviation p *
              ((F (tPrime B.sampleData.n p.1) - 1) /
                (p.1 : ℝ))| ≤
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            |B.primeDeviation p *
              ((F (tPrime B.sampleData.n p.1) - 1) /
                (p.1 : ℝ))| :=
        mul_le_mul_of_nonneg_left
          (Finset.abs_sum_le_sum_abs _ _) (by positivity)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (CF * w) *
              ((1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        rw [abs_mul, abs_div, abs_of_pos (hpPos p)]
        calc
          |B.primeDeviation p| *
              (|F (tPrime B.sampleData.n p.1) - 1| / (p.1 : ℝ)) ≤
            w * ((CF * tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
              calc
                |B.primeDeviation p| *
                    (|F (tPrime B.sampleData.n p.1) - 1| / (p.1 : ℝ)) ≤
                  w * (|F (tPrime B.sampleData.n p.1) - 1| / (p.1 : ℝ)) :=
                    mul_le_mul_of_nonneg_right (hdevSup p)
                      (div_nonneg (abs_nonneg _) (hpPos p).le)
                _ ≤ w * ((CF * tPrime B.sampleData.n p.1) / (p.1 : ℝ)) :=
                    mul_le_mul_of_nonneg_left
                      (div_le_div_of_nonneg_right (hFone p) (hpPos p).le) hw
          _ = (CF * w) *
              ((1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) := by ring
      _ = (CF * w) * alpha := by
        rw [← Finset.mul_sum, hfirstMoment]
        field_simp [hH.ne']
  have hglobal0 : 0 ≤ globalProduct := by
    dsimp only [globalProduct]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (mul_nonneg (ht0 q) (abs_nonneg _))
        (one_div_nonneg.mpr (hpPos q).le)
  have hglobal : globalProduct ≤ 7 * w := by
    have htoL1 : globalProduct ≤ B.primeDeviationL1 := by
      dsimp only [globalProduct]
      unfold primeDeviationL1
      apply Finset.sum_le_sum
      intro q _hq
      have hfac : 0 ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) :=
        mul_nonneg (abs_nonneg _) (one_div_nonneg.mpr (hpPos q).le)
      calc
        tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
            (1 / (q.1 : ℝ)) =
          tPrime B.sampleData.n q.1 *
            (|B.primeDeviation q| * (1 / (q.1 : ℝ))) := by ring
        _ ≤ 1 * (|B.primeDeviation q| * (1 / (q.1 : ℝ))) :=
          mul_le_mul_of_nonneg_right (ht1 q) hfac
        _ = (1 / (q.1 : ℝ)) * |B.primeDeviation q| := by ring
    exact htoL1.trans hdevL1
  have hkernel : |kernel| ≤ (7 * CKernel * w) * alpha := by
    unfold kernel
    rw [abs_mul, abs_of_nonneg (one_div_nonneg.mpr hH.le)]
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
          (Finset.sum_le_sum fun p _hp ↦ Finset.abs_sum_le_sum_abs _ _)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
              (CKernel * globalProduct) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
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
                  (tPrime B.sampleData.n q.1 *
                    |B.primeDeviation q| *
                      (1 / (q.1 : ℝ)))) := by
            apply Finset.sum_le_sum
            intro q _hq
            rw [abs_div,
              abs_of_pos (mul_pos (hpPos p) (hpPos q)), abs_mul]
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
                exact mul_le_mul_of_nonneg_left
                  (hKernelProduct p q) (abs_nonneg _)
              _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
                  (CKernel *
                    (tPrime B.sampleData.n q.1 *
                      |B.primeDeviation q| *
                        (1 / (q.1 : ℝ)))) := by ring
          _ = (tPrime B.sampleData.n p.1 / (p.1 : ℝ)) *
              (CKernel * globalProduct) := by
            dsimp only [globalProduct]
            rw [Finset.mul_sum, Finset.mul_sum]
      _ ≤ (1 / H) *
          ((H * alpha) * (CKernel * (7 * w))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have hfirstDiv :
            (∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 / (p.1 : ℝ)) = H * alpha := by
          calc
            _ = ∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 := by
              apply Finset.sum_congr rfl
              intro p _hp
              ring
            _ = H * alpha := hfirstMoment
        rw [← Finset.sum_mul, hfirstDiv]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left hglobal hCKernel)
          (mul_nonneg hH.le halpha.le)
      _ = (7 * CKernel * w) * alpha := by
        field_simp [hH.ne']
  rw [href]
  calc
    |diagonal + kernel| ≤ |diagonal| + |kernel| := abs_add_le _ _
    _ ≤ (CF * w) * alpha + (7 * CKernel * w) * alpha :=
      add_le_add hdiagonal hkernel
    _ = (CF + 7 * CKernel) * w * B.bandCenter i := by
      dsimp only [alpha]
      ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
