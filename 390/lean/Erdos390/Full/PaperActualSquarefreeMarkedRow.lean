import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.PaperActualPrimePowerRelative
import Erdos390.Full.PaperCompensatedCoefficientBounds

/-!
# The squarefree marked row at the paper's relative scale

This file records the finite row calculation used in Lemma 8.6 and
Proposition 8.7.  A signed product-reciprocal comparison with the
Poisson--Dickman reference matrix is summed against the literal compensated
coefficient.  The result is pointwise in the marked prime and therefore does
not follow from a band-averaged operator estimate.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Exact finite expansion of the actual squarefree marked row. -/
theorem actualSquarefreeMarkedRow_eq_sum [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q) =
      ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          (B.actualValuationLaw xi).covII p r := by
  have hmarked := (B.actualMarkedRows_eq_covariances xi q p).2
  rw [← hmarked]
  unfold squarefreeMarkedRow covII
  rw [(B.actualValuationLaw xi).probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro r hr
  rw [(B.actualValuationLaw xi).probability.covariance_smul_right]

/-- A product-reciprocal signed entry error gives a reciprocal marked-row
error.  This is the row analogue of the quadratic-form transfer, with the
diagonal first- and second-reciprocal terms kept separate. -/
theorem actualSquarefreeMarkedRow_sub_reference_le [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond CL1 w : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          CL1 * w)
    (hentry : ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2
          else 0)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q) -
      ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          squarefreeReferenceEntry B.sampleData.n p r| ≤
      (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
  rw [B.actualSquarefreeMarkedRow_eq_sum xi q p]
  rw [← Finset.sum_sub_distrib]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  calc
    |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        (B.actualCompensatedNatCoefficient q r *
            (B.actualValuationLaw xi).covII p r -
          B.actualCompensatedNatCoefficient q r *
            squarefreeReferenceEntry B.sampleData.n p r)| =
      |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          ((B.actualValuationLaw xi).covII p r -
            squarefreeReferenceEntry B.sampleData.n p r)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          |(B.actualValuationLaw xi).covII p r -
            squarefreeReferenceEntry B.sampleData.n p r| := by
      calc
        _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r *
              ((B.actualValuationLaw xi).covII p r -
                squarefreeReferenceEntry B.sampleData.n p r)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          rw [abs_mul]
    _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          (epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
            if p = r then
              epsilonDiag * (1 / (p : ℝ)) +
                epsilonSecond * (1 / (p : ℝ)) ^ 2
            else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hentry p r hp hr) (abs_nonneg _)
    _ = epsilonOff * (1 / (p : ℝ)) *
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hoff :
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| *
              (epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)))) =
          epsilonOff * (1 / (p : ℝ)) *
            (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
              |B.actualCompensatedNatCoefficient q r| *
                (1 / (r : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hoff]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp
        ring
      · intro r hr hne
        simp [Ne.symm hne]
      · exact fun hnot ↦ (hnot hp).elim
    _ ≤ epsilonOff * (1 / (p : ℝ)) * (CL1 * w) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hcoeffL1
          (mul_nonneg hepsilonOff (one_div_nonneg.mpr hpR.le))) _
    _ = (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
        |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by ring

/-- The Poisson--Dickman reference marked row is controlled by the same
pointwise and reciprocal-`L¹` ledgers as the literal compensated vector. -/
theorem referenceMarkedRow_le
    (q : B.RawBandGauge) {CF CKernel Csup CL1 w : ℝ}
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hcoeffSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ Csup * w)
    (hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          CL1 * w)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          squarefreeReferenceEntry B.sampleData.n p r| ≤
      (CKernel * CL1 + CF * Csup) * w * (1 / (p : ℝ)) := by
  let pp : BandPrime B.sampleData.n B.sampleData.W := ⟨p, hp⟩
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hentry : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |squarefreeReferenceEntry B.sampleData.n p r| ≤
        CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then CF * (1 / (p : ℝ)) else 0 := by
    intro r hr
    let rr : BandPrime B.sampleData.n B.sampleData.W := ⟨r, hr⟩
    have hrR : (0 : ℝ) < r := by
      exact_mod_cast (prime_of_mem_primeBand hr).pos
    by_cases hpr : p = r
    · subst r
      unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_pos rfl, if_pos rfl]
      calc
        |DickmanBasic.F (tPrime B.sampleData.n p) / (p : ℝ) +
            ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n p) (tPrime B.sampleData.n p) /
                ((p : ℝ) * (p : ℝ))| ≤
          |DickmanBasic.F (tPrime B.sampleData.n p) / (p : ℝ)| +
            |ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n p) (tPrime B.sampleData.n p) /
                ((p : ℝ) * (p : ℝ))| := abs_add_le _ _
        _ ≤ CF * (1 / (p : ℝ)) +
            CKernel * (1 / (p : ℝ)) * (1 / (p : ℝ)) := by
          rw [abs_div, abs_of_pos hpR, abs_div,
            abs_of_pos (mul_pos hpR hpR)]
          have hFp : |DickmanBasic.F (tPrime B.sampleData.n p)| ≤ CF :=
            hF pp
          have hKp : |ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤
              CKernel := hKernel pp pp
          calc
            _ ≤ CF / (p : ℝ) + CKernel / ((p : ℝ) * (p : ℝ)) :=
              add_le_add
                (div_le_div_of_nonneg_right hFp hpR.le)
                (div_le_div_of_nonneg_right hKp
                  (mul_nonneg hpR.le hpR.le))
            _ = _ := by field_simp [hpR.ne']
        _ = CKernel * (1 / (p : ℝ)) * (1 / (p : ℝ)) +
            CF * (1 / (p : ℝ)) := by ring
    · unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_neg hpr, if_neg hpr, abs_div,
        abs_of_pos (mul_pos hpR hrR)]
      have hKr : |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n r)| ≤ CKernel :=
        hKernel pp rr
      calc
        _ ≤ CKernel / ((p : ℝ) * (r : ℝ)) :=
          div_le_div_of_nonneg_right hKr (mul_nonneg hpR.le hrR.le)
        _ = CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)) + 0 := by
          field_simp [hpR.ne', hrR.ne']
          ring
  calc
    |∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q r *
          squarefreeReferenceEntry B.sampleData.n p r| ≤
      ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          |squarefreeReferenceEntry B.sampleData.n p r| := by
        calc
          _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
              |B.actualCompensatedNatCoefficient q r *
                squarefreeReferenceEntry B.sampleData.n p r| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by
            apply Finset.sum_congr rfl
            intro r hr
            rw [abs_mul]
    _ ≤ ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| *
          (CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
            if p = r then CF * (1 / (p : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_left (hentry r hr) (abs_nonneg _)
    _ = CKernel * (1 / (p : ℝ)) *
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) +
        CF * (1 / (p : ℝ)) *
          |B.actualCompensatedNatCoefficient q p| := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      have hk :
          (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
            |B.actualCompensatedNatCoefficient q r| *
              (CKernel * (1 / (p : ℝ)) * (1 / (r : ℝ)))) =
          CKernel * (1 / (p : ℝ)) *
            (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
              |B.actualCompensatedNatCoefficient q r| *
                (1 / (r : ℝ))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        ring
      rw [hk]
      congr 1
      rw [Finset.sum_eq_single p]
      · simp
        ring
      · intro r hr hne
        simp [Ne.symm hne]
      · exact fun hnot ↦ (hnot hp).elim
    _ ≤ CKernel * (1 / (p : ℝ)) * (CL1 * w) +
        CF * (1 / (p : ℝ)) * (Csup * w) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hcoeffL1
          (mul_nonneg hCKernel (one_div_nonneg.mpr hpR.le)))
        (mul_le_mul_of_nonneg_left (hcoeffSup p hp)
          (mul_nonneg hCF (one_div_nonneg.mpr hpR.le)))
    _ = (CKernel * CL1 + CF * Csup) * w * (1 / (p : ℝ)) := by ring

/-- Complete squarefree marked-row estimate from signed entry comparison.
The second-reciprocal diagonal term is paid with one explicit `1/W`. -/
theorem actualSquarefreeMarkedRow_le_of_entrywise [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond CF CKernel Csup CL1 w : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hepsilonDiag : 0 ≤ epsilonDiag)
    (hepsilonSecond : 0 ≤ epsilonSecond)
    (hCF : 0 ≤ CF) (hCKernel : 0 ≤ CKernel)
    (hCsup : 0 ≤ Csup) (hw : 0 ≤ w)
    (hW : 0 < B.sampleData.W)
    (hcoeffSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ Csup * w)
    (hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          CL1 * w)
    (hentry : ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        epsilonOff * (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2
          else 0)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
      ((CKernel * CL1 + CF * Csup) +
          (epsilonOff * CL1 + epsilonDiag * Csup +
            epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ)))) *
        w * (1 / (p : ℝ)) := by
  let reference : ℝ :=
    ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
      B.actualCompensatedNatCoefficient q r *
        squarefreeReferenceEntry B.sampleData.n p r
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hWR : (0 : ℝ) < B.sampleData.W := by exact_mod_cast hW
  have hWp : (B.sampleData.W : ℝ) ≤ p := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le
  have hinv : 1 / (p : ℝ) ≤ 1 / (B.sampleData.W : ℝ) :=
    one_div_le_one_div_of_le hWR hWp
  have hdiff := B.actualSquarefreeMarkedRow_sub_reference_le xi q
    hepsilonOff hcoeffL1 hentry hp
  have href := B.referenceMarkedRow_le q hCF hCKernel
    hcoeffSup hcoeffL1 hF hKernel hp
  have hcp := hcoeffSup p hp
  have hdiagSecond :
      |B.actualCompensatedNatCoefficient q p| *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) ≤
        (epsilonDiag * Csup +
            epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
          w * (1 / (p : ℝ)) := by
    have hdiagNonneg : 0 ≤ epsilonDiag * (1 / (p : ℝ)) +
        epsilonSecond * (1 / (p : ℝ)) ^ 2 := by positivity
    calc
      _ ≤ (Csup * w) *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) :=
        mul_le_mul_of_nonneg_right hcp hdiagNonneg
      _ ≤ (Csup * w) *
          (epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond *
              ((1 / (B.sampleData.W : ℝ)) * (1 / (p : ℝ)))) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg hCsup hw)
        exact add_le_add_right
          (mul_le_mul_of_nonneg_left
            (by
              rw [pow_two]
              exact mul_le_mul_of_nonneg_right hinv
                (one_div_nonneg.mpr hpR.le))
            hepsilonSecond) _
      _ = _ := by ring
  have hdiff' :
      |(B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q) - reference| ≤
        (epsilonOff * CL1 + epsilonDiag * Csup +
            epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
          w * (1 / (p : ℝ)) := by
    calc
      _ ≤ (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
          |B.actualCompensatedNatCoefficient q p| *
            (epsilonDiag * (1 / (p : ℝ)) +
              epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
        simpa only [reference] using hdiff
      _ ≤ (epsilonOff * CL1 * w) * (1 / (p : ℝ)) +
          (epsilonDiag * Csup +
              epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
            w * (1 / (p : ℝ)) := add_le_add_right hdiagSecond _
      _ = _ := by ring
  calc
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| =
      |((B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q) - reference) + reference| := by ring_nf
    _ ≤ |(B.tiltedLaw xi).covariance
          (fun m ↦ divInd p (B.sampleData.value m))
          (B.postBandSquarefreeScore q) - reference| + |reference| :=
      abs_add_le _ _
    _ ≤ (epsilonOff * CL1 + epsilonDiag * Csup +
          epsilonSecond * Csup * (1 / (B.sampleData.W : ℝ))) *
          w * (1 / (p : ℝ)) +
        (CKernel * CL1 + CF * Csup) * w * (1 / (p : ℝ)) :=
      add_le_add hdiff' (by simpa only [reference] using href)
    _ = _ := by ring

/-- The canonical signed one- and two-divisor profiles give the literal
actual-law entry comparison.  The equality between the sigma mixture and the
global guarded tilted law keeps all between-cell covariance terms. -/
theorem actualSquarefreeEntry_bound_of_profiles [Nonempty Head]
    (xi : B.ParamSpace) {Eprofile CKernel : ℝ}
    (hEprofile : 0 ≤ Eprofile)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hKernelDiag : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n p) (tPrime B.sampleData.n p)| ≤ CKernel) :
    ∀ p r,
      p ∈ primeBand B.sampleData.n B.sampleData.W →
      r ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualValuationLaw xi).covII p r -
          squarefreeReferenceEntry B.sampleData.n p r| ≤
        (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            (1 / (p : ℝ)) * (1 / (r : ℝ)) +
          if p = r then
            (2 * Eprofile) * (1 / (p : ℝ)) +
              ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * (1 / (p : ℝ)) ^ 2
          else 0 := by
  let weight := tiltedSigmaWeight B.baselineCellProbability
    B.guardedCellProbability (B.scaledBridgeScore xi)
  have hraw :=
    SquarefreeCovarianceReference.sigmaMixture_squarefree_reference_entry_bound_of_squarefree_profiles
      hEprofile weight (B.actualComponentValuationLaw xi) B.n_gt_one
      hpair hsingle hKernelDiag
  have hlaw := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hlaw
  rw [hlaw] at hraw
  intro p r hp hr
  have h := hraw ⟨p, hp⟩ ⟨r, hr⟩
  have hp0 : (p : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hp).ne_zero
  have hr0 : (r : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hr).ne_zero
  by_cases hpr : p = r
  · subst r
    convert h using 1
    field_simp [hp0]
  · have hsub : (⟨p, hp⟩ : BandPrime B.sampleData.n B.sampleData.W) ≠
        ⟨r, hr⟩ := by
      intro heq
      exact hpr (congrArg Subtype.val heq)
    simp only [if_neg hsub] at h
    convert h using 1
    simp only [if_neg hpr]
    field_simp [hp0, hr0]

/-- Paper-facing squarefree marked row with no abstract row hypothesis.  Its
inputs are exactly the signed local profiles, the two uniform kernel bounds,
and the coefficient estimates already used in the slow quadratic argument. -/
theorem actualSquarefreeMarkedRow_le_of_profiles [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Eprofile CF CKernel : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hEprofile : 0 ≤ Eprofile) (hCF : 0 ≤ CF)
    (hCKernel : 0 ≤ CKernel)
    (hW : 0 < B.sampleData.W)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hpair : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      ∀ r, r ∈ (primeBand B.sampleData.n B.sampleData.W).erase p →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd (OmittedTiltPairChamber.pairPower p r 1 1)
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n
          (OmittedTiltPairChamber.pairPower p r 1 1)| ≤
        Eprofile * PaperPrimePowerChamberError.pairWeight p r 1 1)
    (hsingle : ∀ c p, p ∈ primeBand B.sampleData.n B.sampleData.W →
      |(B.actualComponentValuationLaw xi c).probability.expect
          (fun omega ↦ divInd p
            ((B.actualComponentValuationLaw xi c).value omega)) -
        PaperScaleMarkedCell.paperDivisibilityMain B.sampleData.n p| ≤
          Eprofile * PaperPrimePowerChamberError.singleWeight p 1)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤ CKernel)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
      ((CKernel * (7 + C * K) + CF * (1 + C)) +
          ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
              (7 + C * K) +
            (2 * Eprofile) * (1 + C) +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
                CKernel) * (1 + C) *
              (1 / (B.sampleData.W : ℝ)))) *
        w * (1 / (p : ℝ)) := by
  have hcoeff := B.partition.compensatedCoefficient_three_bounds
    B.n_gt_one q hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  have hcoeffSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ (1 + C) * w := by
    intro r hr
    rw [B.actualCompensatedNatCoefficient_of_mem q hr]
    simpa only [B.partition_compensatedCoefficient_eq q ⟨r, hr⟩] using
      hcoeff.1 ⟨r, hr⟩
  have hcoeffL1 :
      (∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q r| * (1 / (r : ℝ))) ≤
          (7 + C * K) * w := by
    rw [B.compensatedNatL1_eq_partition q]
    exact hcoeff.2.1
  have hentry := B.actualSquarefreeEntry_bound_of_profiles xi hEprofile
    hpair hsingle (fun r hr ↦ hKernel ⟨r, hr⟩ ⟨r, hr⟩)
  have hCsup : 0 ≤ 1 + C := by positivity
  have hoff : 0 ≤
      4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile :=
    mul_nonneg (by norm_num)
      (PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile)
  have hsecond : 0 ≤
      (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + CKernel :=
    add_nonneg (sq_nonneg _) hCKernel
  exact B.actualSquarefreeMarkedRow_le_of_entrywise xi q
    hoff (mul_nonneg (by norm_num) hEprofile) hsecond hCF hCKernel
    hCsup hw hW hcoeffSup hcoeffL1 hentry hF hKernel hp

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
