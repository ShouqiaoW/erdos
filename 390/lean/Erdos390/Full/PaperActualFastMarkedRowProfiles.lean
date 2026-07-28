import Erdos390.Full.PaperActualSquarefreeMarkedRow
import Erdos390.Full.PaperActualPrimePowerRowTransfer
import Erdos390.Full.PaperExactTwoStageOrdinaryFast

/-!
# Ordinary-fast marked rows from the literal analytic inputs

The fast solve is bounded in the ordinary raw-band norm.  Its reference
kernel row is nevertheless `O(1/p)`: the product bound for the Dickman
kernel supplies the missing factor `t_r`, whose prime sum is bounded.  Only
the signed profile error pays the full harmonic mass, exactly as in the
paper's `epsilon(n) log L -> 0` bookkeeping.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PaperWeightedInverseExport
open SquarefreeCovarianceReference

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- Squarefree companion of a literal raw-band regression score. -/
def bandSquarefreeRegressionScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ r : BandPrime B.sampleData.n B.sampleData.W,
    q.1 (B.partition.band r) * divInd r.1 (B.sampleData.value m)

theorem bandRegression_markedRows_eq_sums [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.bandRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covVV p r.1 ∧
    (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q) =
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          (B.actualValuationLaw xi).covII p r.1 := by
  constructor
  · have hscore : B.bandRegressionScore q =
        fun m ↦ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          q.1 (B.partition.band r) *
            valuation r.1 (B.sampleData.value m) := by
      funext m
      exact B.bandRegressionScore_eq_primeSum q m
    rw [hscore]
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl
  · unfold bandSquarefreeRegressionScore
    rw [(B.tiltedLaw xi).covariance_sum_right]
    apply Finset.sum_congr rfl
    intro r hr
    rw [(B.tiltedLaw xi).covariance_smul_right]
    rfl

/-- The full-versus-squarefree weighted row applies to an ordinary raw-band
coefficient without any moving-centre loss. -/
theorem bandRegression_full_sub_squarefree_marked_le_of_weightedRow
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) {R : ℝ}
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.bandRegressionScore q) -
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.bandSquarefreeRegressionScore q)| ≤
      ‖q‖ * R * (1 / (p : ℝ)) := by
  rw [(B.bandRegression_markedRows_eq_sums xi q p).1,
    (B.bandRegression_markedRows_eq_sums xi q p).2]
  rw [← Finset.sum_sub_distrib]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hrowp := hrow ⟨p, hp⟩
  calc
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        (q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covVV p r.1 -
          q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covII p r.1)| =
      |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          ((B.actualValuationLaw xi).covVV p r.1 -
            (B.actualValuationLaw xi).covII p r.1)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |q.1 (B.partition.band r)| *
          |(B.actualValuationLaw xi).covVV p r.1 -
            (B.actualValuationLaw xi).covII p r.1| := by
      calc
        _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |q.1 (B.partition.band r) *
              ((B.actualValuationLaw xi).covVV p r.1 -
                (B.actualValuationLaw xi).covII p r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul]
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        ‖q‖ * |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1| := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul_of_nonneg_right
        (by simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm q.1 (B.partition.band r))) (abs_nonneg _)
    _ = ‖q‖ * ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1| := by rw [Finset.mul_sum]
    _ ≤ ‖q‖ * (R / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      exact (le_div_iff₀ hpR).2 (by simpa only [mul_comm] using hrowp)
    _ = ‖q‖ * R * (1 / (p : ℝ)) := by ring

/-- Signed profile transfer for an ordinary raw-band coefficient.  The
off-diagonal error pays the exact total harmonic mass. -/
theorem bandSquarefreeRegression_sub_reference_marked_le
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {epsilonOff epsilonDiag epsilonSecond H : ℝ}
    (hepsilonOff : 0 ≤ epsilonOff)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
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
        (B.bandSquarefreeRegressionScore q) -
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p r.1| ≤
      ‖q‖ *
        (epsilonOff * H + epsilonDiag +
          epsilonSecond * (1 / (p : ℝ))) * (1 / (p : ℝ)) := by
  rw [(B.bandRegression_markedRows_eq_sums xi q p).2]
  rw [← Finset.sum_sub_distrib]
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hmassEq :
      (∑ r : BandPrime B.sampleData.n B.sampleData.W,
        (1 / (r.1 : ℝ))) = ∑ j : Band, B.harmonicMass j := by
    rw [B.sum_harmonicMass_eq_bandReciprocalSum]
    unfold PrimeSums.bandReciprocalSum
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W) (fun r ↦ 1 / (r : ℝ))
    simpa only [Finset.univ_eq_attach] using hattach
  have hq (r : BandPrime B.sampleData.n B.sampleData.W) :
      |q.1 (B.partition.band r)| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1
      (B.partition.band r)
  calc
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        (q.1 (B.partition.band r) *
            (B.actualValuationLaw xi).covII p r.1 -
          q.1 (B.partition.band r) *
            squarefreeReferenceEntry B.sampleData.n p r.1)| =
      |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          ((B.actualValuationLaw xi).covII p r.1 -
            squarefreeReferenceEntry B.sampleData.n p r.1)| := by
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        ring
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |q.1 (B.partition.band r)| *
          |(B.actualValuationLaw xi).covII p r.1 -
            squarefreeReferenceEntry B.sampleData.n p r.1| := by
      calc
        _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
            |q.1 (B.partition.band r) *
              ((B.actualValuationLaw xi).covII p r.1 -
                squarefreeReferenceEntry B.sampleData.n p r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = _ := by simp only [abs_mul]
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        ‖q‖ *
          (epsilonOff * (1 / (p : ℝ)) * (1 / (r.1 : ℝ)) +
            if p = r.1 then
              epsilonDiag * (1 / (p : ℝ)) +
                epsilonSecond * (1 / (p : ℝ)) ^ 2
            else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul (hq r) (hentry p r.1 hp r.2)
        (abs_nonneg _) (norm_nonneg q)
    _ = ‖q‖ *
        (epsilonOff * (1 / (p : ℝ)) *
            (∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (1 / (r.1 : ℝ))) +
          epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      have hoff :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            epsilonOff * (1 / (p : ℝ)) * (1 / (r.1 : ℝ))) =
          epsilonOff * (1 / (p : ℝ)) *
            (∑ r : BandPrime B.sampleData.n B.sampleData.W,
              (1 / (r.1 : ℝ))) := by rw [Finset.mul_sum]
      have hdiag :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            if p = r.1 then
              epsilonDiag * (1 / (p : ℝ)) +
                epsilonSecond * (1 / (p : ℝ)) ^ 2
            else 0) =
          epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2 := by
        rw [Finset.sum_eq_single ⟨p, hp⟩]
        · simp
        · intro r hr hne
          have hval : p ≠ r.1 := by
            intro heq
            exact hne (Subtype.ext heq.symm)
          simp only [if_neg hval]
        · exact fun hnot ↦ (hnot (Finset.mem_univ _)).elim
      rw [hoff, hdiag]
      ring
    _ ≤ ‖q‖ *
        (epsilonOff * (1 / (p : ℝ)) * H +
          epsilonDiag * (1 / (p : ℝ)) +
            epsilonSecond * (1 / (p : ℝ)) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      gcongr
      exact hmassEq.trans_le hH
    _ = ‖q‖ *
        (epsilonOff * H + epsilonDiag +
          epsilonSecond * (1 / (p : ℝ))) * (1 / (p : ℝ)) := by ring

/-- The product Dickman-kernel bound gives an `O(1/p)` reference row even
for an ordinary, rather than sharp, raw-band coefficient. -/
theorem bandReferenceMarkedRow_le_product
    (q : B.RawBandGauge) {CF Cprod K : ℝ}
    (hCprod : 0 ≤ Cprod)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hF : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |DickmanBasic.F (tPrime B.sampleData.n r.1)| ≤ CF)
    (hKernel : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
        Cprod * tPrime B.sampleData.n r.1 * tPrime B.sampleData.n s.1)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p r.1| ≤
      ‖q‖ * (Cprod * K + CF) * (1 / (p : ℝ)) := by
  let pp : BandPrime B.sampleData.n B.sampleData.W := ⟨p, hp⟩
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have htp : 0 ≤ tPrime B.sampleData.n p :=
    PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one hp
  have htp1 : tPrime B.sampleData.n p ≤ 1 :=
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one hp
  have hq (r : BandPrime B.sampleData.n B.sampleData.W) :
      |q.1 (B.partition.band r)| ≤ ‖q‖ := by
    simpa only [Real.norm_eq_abs] using norm_le_pi_norm q.1
      (B.partition.band r)
  have hentry (r : BandPrime B.sampleData.n B.sampleData.W) :
      |squarefreeReferenceEntry B.sampleData.n p r.1| ≤
        Cprod * (1 / (p : ℝ)) *
            (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) +
          if p = r.1 then CF * (1 / (p : ℝ)) else 0 := by
    have hrR : (0 : ℝ) < r.1 := by
      exact_mod_cast (prime_of_mem_primeBand r.2).pos
    by_cases hpr : p = r.1
    · subst p
      unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_pos rfl, if_pos rfl]
      calc
        |DickmanBasic.F (tPrime B.sampleData.n r.1) / (r.1 : ℝ) +
            ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n r.1) (tPrime B.sampleData.n r.1) /
                ((r.1 : ℝ) * (r.1 : ℝ))| ≤
          |DickmanBasic.F (tPrime B.sampleData.n r.1) / (r.1 : ℝ)| +
            |ConditionedPoissonLimit.covarianceKernel
              (tPrime B.sampleData.n r.1) (tPrime B.sampleData.n r.1) /
                ((r.1 : ℝ) * (r.1 : ℝ))| := abs_add_le _ _
        _ ≤ CF * (1 / (r.1 : ℝ)) +
            Cprod * (1 / (r.1 : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) := by
          rw [abs_div, abs_of_pos hrR, abs_div,
            abs_of_pos (mul_pos hrR hrR)]
          have hK := hKernel r r
          calc
            _ ≤ CF / (r.1 : ℝ) +
                (Cprod * tPrime B.sampleData.n r.1 *
                  tPrime B.sampleData.n r.1) /
                    ((r.1 : ℝ) * (r.1 : ℝ)) :=
              add_le_add
                (div_le_div_of_nonneg_right (hF r) hrR.le)
                (div_le_div_of_nonneg_right hK
                  (mul_nonneg hrR.le hrR.le))
            _ ≤ CF * (1 / (r.1 : ℝ)) +
                Cprod * (1 / (r.1 : ℝ)) *
                  (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) := by
              have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
                B.n_gt_one r.2
              have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
                B.n_gt_one r.2
              field_simp [hrR.ne']
              nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1)]
        _ = Cprod * (1 / (r.1 : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) +
            CF * (1 / (r.1 : ℝ)) := by ring
    · unfold squarefreeReferenceEntry squarefreeKernelEntry
      rw [if_neg hpr, if_neg hpr, abs_div,
        abs_of_pos (mul_pos hpR hrR)]
      have hK := hKernel pp r
      calc
        _ ≤ (Cprod * tPrime B.sampleData.n p *
              tPrime B.sampleData.n r.1) / ((p : ℝ) * (r.1 : ℝ)) :=
          div_le_div_of_nonneg_right hK (mul_nonneg hpR.le hrR.le)
        _ ≤ Cprod * (1 / (p : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) := by
          field_simp [hpR.ne', hrR.ne']
          exact mul_le_mul_of_nonneg_right
            (by simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left htp1 hCprod))
            (PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
              B.n_gt_one r.2)
        _ = _ := by ring
  calc
    |∑ r : BandPrime B.sampleData.n B.sampleData.W,
        q.1 (B.partition.band r) *
          squarefreeReferenceEntry B.sampleData.n p r.1| ≤
      ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        |q.1 (B.partition.band r)| *
          |squarefreeReferenceEntry B.sampleData.n p r.1| := by
        calc
          _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
              |q.1 (B.partition.band r) *
                squarefreeReferenceEntry B.sampleData.n p r.1| :=
            Finset.abs_sum_le_sum_abs _ _
          _ = _ := by simp only [abs_mul]
    _ ≤ ∑ r : BandPrime B.sampleData.n B.sampleData.W,
        ‖q‖ * (Cprod * (1 / (p : ℝ)) *
            (tPrime B.sampleData.n r.1 / (r.1 : ℝ)) +
          if p = r.1 then CF * (1 / (p : ℝ)) else 0) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul (hq r) (hentry r) (abs_nonneg _) (norm_nonneg q)
    _ = ‖q‖ * (Cprod * (1 / (p : ℝ)) *
          PrimeSums.bandTReciprocalSum B.sampleData.n B.sampleData.W +
        CF * (1 / (p : ℝ))) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib]
      have hk :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            Cprod * (1 / (p : ℝ)) *
              (tPrime B.sampleData.n r.1 / (r.1 : ℝ))) =
          Cprod * (1 / (p : ℝ)) *
            PrimeSums.bandTReciprocalSum
              B.sampleData.n B.sampleData.W := by
        rw [← Finset.mul_sum]
        unfold PrimeSums.bandTReciprocalSum
        congr 1
        exact (Finset.sum_subtype
          (primeBand B.sampleData.n B.sampleData.W)
          (fun _ ↦ Iff.rfl)
          (fun r ↦ tPrime B.sampleData.n r / (r : ℝ))).symm
      have hdiag :
          (∑ r : BandPrime B.sampleData.n B.sampleData.W,
            if p = r.1 then CF * (1 / (p : ℝ)) else 0) =
          CF * (1 / (p : ℝ)) := by
        rw [Finset.sum_eq_single ⟨p, hp⟩]
        · simp
        · intro r hr hne
          have hval : p ≠ r.1 := by
            intro heq
            exact hne (Subtype.ext heq.symm)
          simp only [if_neg hval]
        · exact fun hnot ↦ (hnot (Finset.mem_univ _)).elim
      rw [hk, hdiag]
    _ ≤ ‖q‖ * (Cprod * (1 / (p : ℝ)) * K +
        CF * (1 / (p : ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg q)
      exact add_le_add_left
        (mul_le_mul_of_nonneg_left hbandT
          (mul_nonneg hCprod (one_div_nonneg.mpr hpR.le))) _
    _ = ‖q‖ * (Cprod * K + CF) * (1 / (p : ℝ)) := by ring

/-- Full nuisance-residual fast marked row.  Every term on the right is a
literal finite conclusion; there is no assumed fast or vector-field row. -/
theorem nuisanceResidual_bandRegression_markedRow_le_of_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) {gamma : ℝ} (hgamma : 0 < gamma)
    (hgap : ∀ z, gamma * ‖z‖ ^ 2 ≤
      inner ℝ z (B.nuisanceCovarianceOperator xi z))
    (q : B.RawBandGauge)
    {H K Eprofile CF Cprod R Cmarked : ℝ}
    (hH0 : 0 ≤ H) (hCmarked : 0 ≤ Cmarked)
    (hEprofile : 0 ≤ Eprofile)
    (hCprod : 0 ≤ Cprod)
    (hW : 0 < B.sampleData.W)
    (hH : (∑ j : Band, B.harmonicMass j) ≤ H)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
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
    (hKernelProduct : ∀ r s : BandPrime B.sampleData.n B.sampleData.W,
      |ConditionedPoissonLimit.covarianceKernel
          (tPrime B.sampleData.n r.1)
          (tPrime B.sampleData.n s.1)| ≤
        Cprod * tPrime B.sampleData.n r.1 * tPrime B.sampleData.n s.1)
    (hrow : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      (r.1 : ℝ) *
        ∑ s : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV r.1 s.1 -
            (B.actualValuationLaw xi).covII r.1 s.1| ≤ R)
    (hmarked : ∀ (c : NuisanceCoord B.HeadIndex)
      (r : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation r.1 (B.sampleData.value m))| ≤
          Cmarked * (1 / (r.1 : ℝ)))
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.nuisanceResidualScore xi hgamma hgap
          (B.bandRegressionScore q))| ≤
      ((Cprod * K + CF) +
          ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
              H + 2 * Eprofile +
            ((1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 +
              Cprod) * (1 / (B.sampleData.W : ℝ))) + R +
          (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
                (Cmarked * H)) / gamma) *
            (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              Cmarked))) * ‖q‖ * (1 / (p : ℝ)) := by
  have hentry := B.actualSquarefreeEntry_bound_of_profiles xi hEprofile
    hpair hsingle (fun r hr ↦ by
      have ht0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand
        B.n_gt_one hr
      have ht1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand
        B.n_gt_one hr
      have hk := hKernelProduct ⟨r, hr⟩ ⟨r, hr⟩
      calc
        _ ≤ Cprod * tPrime B.sampleData.n r * tPrime B.sampleData.n r := hk
        _ ≤ Cprod := by
          nlinarith [mul_nonneg ht0 (sub_nonneg.mpr ht1), hCprod])
  have hsfDiff := B.bandSquarefreeRegression_sub_reference_marked_le
    xi q
    (mul_nonneg (by norm_num)
      (PaperPrimePowerChamberError.pairCovarianceScale_nonneg hEprofile))
    hH hentry hp
  have href := B.bandReferenceMarkedRow_le_product q hCprod
    hbandT hF hKernelProduct hp
  have hpow := B.bandRegression_full_sub_squarefree_marked_le_of_weightedRow
    xi q hrow hp
  let full := (B.tiltedLaw xi).covariance
    (fun m ↦ valuation p (B.sampleData.value m))
    (B.bandRegressionScore q)
  let squarefree := (B.tiltedLaw xi).covariance
    (fun m ↦ divInd p (B.sampleData.value m))
    (B.bandSquarefreeRegressionScore q)
  let reference := ∑ r : BandPrime B.sampleData.n B.sampleData.W,
    q.1 (B.partition.band r) *
      squarefreeReferenceEntry B.sampleData.n p r.1
  have hpR : (0 : ℝ) < p := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hWR : (0 : ℝ) < B.sampleData.W := by exact_mod_cast hW
  have hWp : (B.sampleData.W : ℝ) ≤ p := by
    exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le
  have hinv : 1 / (p : ℝ) ≤ 1 / (B.sampleData.W : ℝ) :=
    one_div_le_one_div_of_le hWR hWp
  let second :=
    (1 / DickmanBasic.rho DickmanBasic.U + 2 * Eprofile) ^ 2 + Cprod
  have hsecond : 0 ≤ second := by
    dsimp only [second]
    exact add_nonneg (sq_nonneg _) hCprod
  have hsfDiff' : |squarefree - reference| ≤
      ‖q‖ * ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
          H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) *
        (1 / (p : ℝ)) := by
    have hraw : |squarefree - reference| ≤
        ‖q‖ * ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            H + 2 * Eprofile + second * (1 / (p : ℝ))) *
          (1 / (p : ℝ)) := by
      simpa only [squarefree, reference, second] using hsfDiff
    have hinside :
        (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * H +
            2 * Eprofile + second * (1 / (p : ℝ)) ≤
          (4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) * H +
            2 * Eprofile + second * (1 / (B.sampleData.W : ℝ)) := by
      gcongr
    exact hraw.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hinside (norm_nonneg q))
      (one_div_nonneg.mpr hpR.le))
  have hfull : |full| ≤
      ‖q‖ * ((Cprod * K + CF) +
        ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) + R) *
          (1 / (p : ℝ)) := by
    have htriangle : |full| ≤
        |full - squarefree| + |squarefree - reference| + |reference| := by
      calc
        |full| = |(full - squarefree) + (squarefree - reference) + reference| :=
          by ring_nf
        _ ≤ |full - squarefree| + |squarefree - reference| + |reference| :=
          (abs_add_three _ _ _)
    calc
      _ ≤ |full - squarefree| + |squarefree - reference| + |reference| :=
        htriangle
      _ ≤ ‖q‖ * R * (1 / (p : ℝ)) +
          ‖q‖ * ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
            H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) *
              (1 / (p : ℝ)) +
          ‖q‖ * (Cprod * K + CF) * (1 / (p : ℝ)) :=
        add_le_add (add_le_add (by simpa only [full, squarefree] using hpow)
          hsfDiff') (by simpa only [reference] using href)
      _ = _ := by ring
  have hsource := B.nuisanceCovarianceVector_rawBandRegression_norm_le_of_marked
    xi hCmarked hmarked q
  have hmarkedCoord : ∀ c : NuisanceCoord B.HeadIndex,
      |(B.tiltedLaw xi).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p (B.sampleData.value m))| ≤
          Cmarked * (1 / (p : ℝ)) := fun c ↦ hmarked c ⟨p, hp⟩
  have hmarkedZ : ‖B.nuisanceCovarianceVector xi
      (fun m ↦ valuation p (B.sampleData.value m))‖ ≤
      (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
        Cmarked) * (1 / (p : ℝ)) := by
    have hraw := B.nuisanceCovarianceVector_norm_le_sqrt_card_mul
      xi (fun m ↦ valuation p (B.sampleData.value m))
      (mul_nonneg hCmarked (one_div_nonneg.mpr hpR.le)) hmarkedCoord
    simpa only [mul_assoc] using hraw
  let d : ℝ := Real.sqrt
    (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ)
  let Cz : ℝ := d * (Cmarked * H)
  let Crow : ℝ := d * Cmarked
  have hsourceH : ‖B.nuisanceCovarianceVector xi
      (B.bandRegressionScore q)‖ ≤ Cz * ‖q‖ := by
    calc
      _ ≤ d * ((Cmarked * ∑ j : Band, B.harmonicMass j) * ‖q‖) := by
        simpa only [d] using hsource
      _ ≤ d * ((Cmarked * H) * ‖q‖) := by
        apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg q)
        exact mul_le_mul_of_nonneg_left hH hCmarked
      _ = Cz * ‖q‖ := by simp only [Cz]; ring
  have hCz : 0 ≤ Cz := by
    dsimp only [Cz, d]
    positivity
  let a := B.nuisanceCoefficientOfScore xi hgamma hgap
    (B.bandRegressionScore q)
  have ha : ‖a‖ ≤ (Cz / gamma) * ‖q‖ := by
    calc
      ‖a‖ ≤ ‖B.nuisanceCovarianceVector xi
          (B.bandRegressionScore q)‖ / gamma :=
        B.nuisanceCoefficientOfScore_norm_le xi hgamma hgap _
      _ ≤ (Cz * ‖q‖) / gamma :=
        div_le_div_of_nonneg_right hsourceH hgamma.le
      _ = (Cz / gamma) * ‖q‖ := by ring
  have hnuisance :
      |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (fun m ↦ inner ℝ a (B.nuisanceStatistic m))| ≤
      ((Cz / gamma) * Crow) * ‖q‖ * (1 / (p : ℝ)) := by
    rw [B.covariance_marked_nuisanceScore_eq_inner]
    calc
      |inner ℝ a (B.nuisanceCovarianceVector xi
          (fun m ↦ valuation p (B.sampleData.value m)))| ≤
        ‖a‖ * ‖B.nuisanceCovarianceVector xi
          (fun m ↦ valuation p (B.sampleData.value m))‖ :=
        abs_real_inner_le_norm _ _
      _ ≤ ((Cz / gamma) * ‖q‖) *
          (Crow * (1 / (p : ℝ))) := by
        exact mul_le_mul ha (by simpa only [Crow, d] using hmarkedZ)
          (norm_nonneg _) (mul_nonneg (div_nonneg hCz hgamma.le)
            (norm_nonneg q))
      _ = _ := by ring
  have hdecomp :
      (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (B.nuisanceResidualScore xi hgamma hgap
            (B.bandRegressionScore q)) = full -
        (B.tiltedLaw xi).covariance
          (fun m ↦ valuation p (B.sampleData.value m))
          (fun m ↦ inner ℝ
            (B.nuisanceCoefficientOfScore xi hgamma hgap
              (B.bandRegressionScore q))
            (B.nuisanceStatistic m)) := by
    unfold nuisanceResidualScore
    have hfun :
        (fun m ↦ B.bandRegressionScore q m -
          inner ℝ a (B.nuisanceStatistic m)) =
        fun m ↦ B.bandRegressionScore q m + (-1 : ℝ) *
          inner ℝ a (B.nuisanceStatistic m) := by
      funext m
      ring
    rw [hfun, (B.tiltedLaw xi).covariance_add_right,
      (B.tiltedLaw xi).covariance_smul_right]
    dsimp only [a]
    ring
  rw [hdecomp]
  calc
    |full - (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceStatistic m))| ≤
      |full| + |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (fun m ↦ inner ℝ
          (B.nuisanceCoefficientOfScore xi hgamma hgap
            (B.bandRegressionScore q))
          (B.nuisanceStatistic m))| := abs_sub _ _
    _ ≤ ‖q‖ * ((Cprod * K + CF) +
          ((4 * PaperPrimePowerChamberError.pairCovarianceScale Eprofile) *
              H + 2 * Eprofile + second * (1 / (B.sampleData.W : ℝ))) + R) *
            (1 / (p : ℝ)) +
        (((Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
              (Cmarked * H)) / gamma) *
          (Real.sqrt (Fintype.card (NuisanceCoord B.HeadIndex) : ℝ) *
            Cmarked)) * ‖q‖ * (1 / (p : ℝ)) :=
      add_le_add hfull hnuisance
    _ = _ := by dsimp only [second, Cz, Crow, d]; ring

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
