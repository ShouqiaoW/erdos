import Erdos390.Full.PaperNonstepSlowRightLedger
import Erdos390.Full.PaperActualSlowRightRowFinite

/-!
# Exact non-step squarefree slow-row ledger

This file keeps the primewise coefficient
`g_p = alpha_{j(p)} - t_p` throughout the signed squarefree comparison.
Consequently the off-diagonal profile error is charged to the global
weighted `L¹` deviation, and the `p^{-2}` diagonal is exactly the local
quantity handled by `PaperCanonicalNonstepLocalDiagonalEventually`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open SquarefreeCovarianceReference SquarefreeSharpBandTransfer
open PrimeSquarefreeDirichletGeometry FiniteAnchoredDirichletQuadratic
open PaperActualSlowRightRowFinite
open SquarefreeReferenceOperatorIdentification

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Signed Dickman reference row with the literal non-step slow
coefficient. -/
def referenceSlowRow (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1

/-- The reference row of the exact logarithmic prime coefficient. -/
def referenceLogRow (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n q.1 *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1

set_option maxHeartbeats 2000000 in
/-- Exact entrywise-to-row aggregation for the literal non-step coefficient.
No least-centre divisor and no number-of-bands factor occurs. -/
theorem abs_squarefreeSlowRow_sub_referenceSlowRow_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    {epsilonOff epsilonDiag Cdiag w : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hepsilonDiag : 0 ≤ epsilonDiag)
    (hentry : ∀ p q : BandPrime B.sampleData.n B.sampleData.W,
      |(B.actualValuationLaw xi).covII p.1 q.1 -
          squarefreeReferenceEntry B.sampleData.n p.1 q.1| ≤
        epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
          (if p = q then
            epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
          else 0))
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.normalizedSquarefreeBandCovarianceRow xi B.slowSquarefreeScore i -
        B.referenceSlowRow i| ≤
      7 * epsilonOff * w +
        2 * epsilonDiag * B.bandCenter i +
        Cdiag * B.bandDeviationReciprocalSquare i := by
  let H : ℝ := B.harmonicMass i
  let alpha : ℝ := B.bandCenter i
  let L1 : ℝ := B.primeDeviationL1
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q *
            ((B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1)| ≤
        epsilonOff / (p.1 : ℝ) * L1 +
          epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
          Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by
    calc
      |∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q *
            ((B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1)| ≤
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q *
              ((B.actualValuationLaw xi).covII p.1 q.1 -
                squarefreeReferenceEntry B.sampleData.n p.1 q.1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q| *
            |(B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1| := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [abs_mul]
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |B.primeDeviation q| *
            (epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)) +
              (if p = q then
                epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
              else 0)) := by
        apply Finset.sum_le_sum
        intro q _hq
        exact mul_le_mul_of_nonneg_left (hentry p q) (abs_nonneg _)
      _ = epsilonOff / (p.1 : ℝ) * L1 +
          epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
          Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by
        have hoff :
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q| *
                (epsilonOff / ((p.1 : ℝ) * (q.1 : ℝ)))) =
              epsilonOff / (p.1 : ℝ) * L1 := by
          dsimp only [L1]
          unfold primeDeviationL1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _hq
          field_simp [ne_of_gt (hpPos p), ne_of_gt (hpPos q)]
        have hdiag :
            (∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q| *
                (if p = q then
                  epsilonDiag / (p.1 : ℝ) + Cdiag / (p.1 : ℝ) ^ 2
                else 0)) =
              epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
                Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by
          calc
            _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                if q = p then
                  |B.primeDeviation q| *
                    (epsilonDiag / (p.1 : ℝ) +
                      Cdiag / (p.1 : ℝ) ^ 2)
                else 0 := by
              apply Finset.sum_congr rfl
              intro q _hq
              by_cases hpq : p = q
              · subst q
                simp
              · have hqp : q ≠ p := fun h ↦ hpq h.symm
                simp [hpq, hqp]
            _ = |B.primeDeviation p| *
                (epsilonDiag / (p.1 : ℝ) +
                  Cdiag / (p.1 : ℝ) ^ 2) := by simp
            _ = epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
                Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2 := by ring
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, hoff, hdiag]
        ring
  let A : ℝ := ∑ p ∈ B.partition.data.fiber i,
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      B.primeDeviation q * (B.actualValuationLaw xi).covII p.1 q.1
  let R : ℝ := ∑ p ∈ B.partition.data.fiber i,
    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
      B.primeDeviation q *
        squarefreeReferenceEntry B.sampleData.n p.1 q.1
  have hdiff : A - R =
      ∑ p ∈ B.partition.data.fiber i,
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation q *
            ((B.actualValuationLaw xi).covII p.1 q.1 -
              squarefreeReferenceEntry B.sampleData.n p.1 q.1) := by
    dsimp only [A, R]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  have hsum : |A - R| ≤
      epsilonOff * L1 * H +
        epsilonDiag * (2 * H * alpha) +
        Cdiag *
          (∑ p ∈ B.partition.data.fiber i,
            |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
    rw [hdiff]
    calc
      |∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q *
              ((B.actualValuationLaw xi).covII p.1 q.1 -
                squarefreeReferenceEntry B.sampleData.n p.1 q.1)| ≤
          ∑ p ∈ B.partition.data.fiber i,
            |∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                ((B.actualValuationLaw xi).covII p.1 q.1 -
                  squarefreeReferenceEntry B.sampleData.n p.1 q.1)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ B.partition.data.fiber i,
          (epsilonOff / (p.1 : ℝ) * L1 +
            epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ) +
            Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2) :=
        Finset.sum_le_sum fun p _hp ↦ hinner p
      _ = epsilonOff * L1 * H +
          epsilonDiag *
            (∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ)) * |B.primeDeviation p|) +
          Cdiag *
            (∑ p ∈ B.partition.data.fiber i,
              |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
        dsimp only [H, harmonicMass]
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        have hoffsum :
            (∑ p ∈ B.partition.data.fiber i,
              epsilonOff / (p.1 : ℝ) * L1) =
              epsilonOff * L1 *
                ∑ p ∈ B.partition.data.fiber i, 1 / (p.1 : ℝ) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        have hepssum :
            (∑ p ∈ B.partition.data.fiber i,
              epsilonDiag * |B.primeDeviation p| / (p.1 : ℝ)) =
              epsilonDiag *
                ∑ p ∈ B.partition.data.fiber i,
                  (1 / (p.1 : ℝ)) * |B.primeDeviation p| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        have hCsum :
            (∑ p ∈ B.partition.data.fiber i,
              Cdiag * |B.primeDeviation p| / (p.1 : ℝ) ^ 2) =
              Cdiag *
                ∑ p ∈ B.partition.data.fiber i,
                  |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring
        rw [hoffsum, hepssum, hCsum]
        simp only [Erdos390.Lemma84.WeightedBandData.mass,
          ArithmeticBandGeometry.Partition.data]
      _ ≤ epsilonOff * L1 * H +
          epsilonDiag * (2 * H * alpha) +
          Cdiag *
            (∑ p ∈ B.partition.data.fiber i,
              |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2) := by
        have hmid :
            epsilonDiag *
                (∑ p ∈ B.partition.data.fiber i,
                  (1 / (p.1 : ℝ)) * |B.primeDeviation p|) ≤
              epsilonDiag * (2 * H * alpha) := by
          simpa only [bandDeviationL1, H, alpha] using
            mul_le_mul_of_nonneg_left
              (B.bandDeviationL1_le_two_mul_mass_mul_center i)
              hepsilonDiag
        exact add_le_add (add_le_add le_rfl hmid) le_rfl
  have hactual :=
    (B.normalizedSlowRows_eq_fullSquarefreeCoefficientRows xi i).2
  have hscaled :
      |(1 / H) * A - (1 / H) * R| ≤
        epsilonOff * L1 + 2 * epsilonDiag * alpha +
          Cdiag * B.bandDeviationReciprocalSquare i := by
    rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hH)]
    have hscaled0 :=
      mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hH.le)
    unfold bandDeviationReciprocalSquare
    dsimp only [H, alpha, harmonicMass] at hH hscaled0 ⊢
    convert hscaled0 using 1
    all_goals field_simp [hH.ne']
  have hL1 : epsilonOff * L1 ≤ 7 * epsilonOff * w := by
    calc
      epsilonOff * L1 ≤ epsilonOff * (7 * w) :=
        mul_le_mul_of_nonneg_left hdevL1 hepsilonOff
      _ = 7 * epsilonOff * w := by ring
  rw [hactual]
  change |(1 / H) * A - (1 / H) * R| ≤ _
  exact hscaled.trans (add_le_add (add_le_add hL1 le_rfl) le_rfl)

/-- The reference logarithmic row is exactly the band average of the finite
prime row-sum residual. -/
theorem referenceLogRow_eq_residual (i : Band) :
    B.referenceLogRow i =
      (1 / B.harmonicMass i) *
        ∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) *
            rowResidual
              (primeWeight B.sampleData.n)
              (primeDiagonal B.sampleData.n)
              (primeKernel B.sampleData.n) p := by
  have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n q.1 *
          squarefreeReferenceEntry B.sampleData.n p.1 q.1) =
        (1 / (p.1 : ℝ)) *
          rowResidual
            (primeWeight B.sampleData.n)
            (primeDiagonal B.sampleData.n)
            (primeKernel B.sampleData.n) p := by
    have hdiag :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n q.1 *
            (if p.1 = q.1 then
              DickmanBasic.F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)
            else 0)) =
          tPrime B.sampleData.n p.1 *
            (DickmanBasic.F (tPrime B.sampleData.n p.1) / (p.1 : ℝ)) := by
      rw [Finset.sum_eq_single p]
      · simp
      · intro q _hq hqp
        have hpq : p.1 ≠ q.1 := by
          intro h
          exact hqp (Subtype.ext h.symm)
        simp [hpq]
      · simp
    have hkernel :
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n q.1 *
            squarefreeKernelEntry B.sampleData.n p.1 q.1) =
          (1 / (p.1 : ℝ)) *
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              (tPrime B.sampleData.n q.1 / (q.1 : ℝ)) *
                ConditionedPoissonLimit.covarianceKernel
                  (tPrime B.sampleData.n p.1)
                  (tPrime B.sampleData.n q.1) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _hq
      unfold squarefreeKernelEntry
      ring
    simp_rw [squarefreeReferenceEntry_eq_kernel_add_diagonal, mul_add]
    rw [Finset.sum_add_distrib, hdiag, hkernel]
    unfold rowResidual primeWeight primeDiagonal primeKernel
    ring
  unfold referenceLogRow
  simp_rw [hinner]

/-- The reference non-step row is exactly the band-centre reference row
minus the logarithmic residual row. -/
theorem referenceSlowRow_eq_bandCenter_sub_log (i : Band) :
    B.referenceSlowRow i =
      referenceBandRow B.partition B.bandCenter i - B.referenceLogRow i := by
  unfold referenceSlowRow referenceLogRow referenceBandRow
  change (1 / B.partition.mass i) * _ =
    (1 / B.partition.mass i) * _ -
      (1 / B.partition.mass i) * _
  rw [← mul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p _hp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _hq
  unfold primeDeviation bandCenter
  ring

/-- Fully finite reference bound for the literal non-step slow row. -/
theorem abs_referenceSlowRow_le_of_rowResidual
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
      |DickmanBasic.F (tPrime B.sampleData.n p.1) -
          DickmanBasic.F (B.bandCenter (B.partition.band p))| ≤
        CF * |B.primeDeviation p|)
    (hKernelProduct : ∀
      p q : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p.1)
          (tPrime B.sampleData.n q.1)| ≤
        CKernel * tPrime B.sampleData.n p.1 *
          tPrime B.sampleData.n q.1)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.primeDeviation p| ≤ w)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.referenceSlowRow i| ≤
      (2 * rowError + (2 * CF + 7 * CKernel) * w) *
        B.bandCenter i := by
  have hcenter := B.referenceBandRow_bandCenter_le_of_rowResidual
    hw hCF hCKernel hrowResidual hFdiff hKernelProduct hdevSup hdevL1 i
  have hlog : |B.referenceLogRow i| ≤
      rowError * B.bandCenter i := by
    rw [B.referenceLogRow_eq_residual]
    let H := B.harmonicMass i
    have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
    rw [abs_mul, abs_of_pos (one_div_pos.mpr hH)]
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
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _)
          (by positivity)
      _ ≤ (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ)) *
              (rowError * tPrime B.sampleData.n p.1) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        rw [abs_mul, abs_of_nonneg (by positivity :
          0 ≤ (1 / (p.1 : ℝ)))]
        exact mul_le_mul_of_nonneg_left (hrowResidual p) (by positivity)
      _ = rowError * B.bandCenter i := by
        have hfirst :
            (∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ)) *
                tPrime B.sampleData.n p.1) =
              B.harmonicMass i * B.bandCenter i := by
          unfold harmonicMass bandCenter
          change (∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) =
            B.partition.data.mass i *
              ((∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
                  B.partition.data.mass i)
          field_simp [ne_of_gt (B.partition.data.mass_pos i)]
        change (1 / H) *
            (∑ p ∈ B.partition.data.fiber i,
              (1 / (p.1 : ℝ)) *
                (rowError * tPrime B.sampleData.n p.1)) = _
        rw [show (∑ p ∈ B.partition.data.fiber i,
            (1 / (p.1 : ℝ)) *
              (rowError * tPrime B.sampleData.n p.1)) =
            rowError *
              ∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ)) *
                  tPrime B.sampleData.n p.1 by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p _hp
          ring, hfirst]
        dsimp only [H]
        field_simp [ne_of_gt (B.harmonicMass_pos i)]
  rw [B.referenceSlowRow_eq_bandCenter_sub_log]
  calc
    |referenceBandRow B.partition B.bandCenter i - B.referenceLogRow i| ≤
        |referenceBandRow B.partition B.bandCenter i| +
          |B.referenceLogRow i| := abs_sub _ _
    _ ≤ (rowError + (2 * CF + 7 * CKernel) * w) *
          B.bandCenter i + rowError * B.bandCenter i :=
      add_le_add hcenter hlog
    _ = (2 * rowError + (2 * CF + 7 * CKernel) * w) *
          B.bandCenter i := by ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
