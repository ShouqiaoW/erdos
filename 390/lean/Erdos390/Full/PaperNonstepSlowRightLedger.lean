import Erdos390.Full.PaperActualPrimePowerRowTransfer
import Erdos390.Full.PrimePowerSharpBandTransfer
import Erdos390.Full.PaperPrimeDeviationGeometry
import Erdos390.Full.PaperActualTwoStageRegression

/-!
# Exact non-step prime-power ledger for the slow right row

The slow coefficient is the literal arithmetic deviation
`g_p = alpha_{j(p)} - t_p`; it is not replaced by a step function.  This
file keeps the `t_p` factors in the three `JI/IJ/JJ` orientations until
after the output-band average.  The resulting finite estimate has exactly
three kinds of terms:

* a structural `Cpow / W` multiple of `w * alpha_i`;
* an analytic remainder `epsilon / W` times `w` (to be divided by the
  actual arithmetic centre only in the eventual specialization); and
* the literal local reciprocal-square deviation ledger.

No mesh, continuum centre, asymptotic profile, or ODE box occurs in the
theorem below.  It is therefore reusable in both Lemma 8.6 and Proposition
8.7.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

namespace BridgeData

private theorem normalized_double_sum_factor
    {P Q : Type*} [Fintype Q]
    (H : ℝ) (s : Finset P) (f : P → ℝ) (g : Q → ℝ) :
    (1 / H) * ∑ p ∈ s, ∑ q : Q, f p * g q =
      ((1 / H) * ∑ p ∈ s, f p) * ∑ q : Q, g q := by
  have hinner (p : P) :
      (∑ q : Q, f p * g q) = f p * ∑ q : Q, g q := by
    rw [Finset.mul_sum]
  simp_rw [hinner]
  rw [← Finset.sum_mul]
  ring

private theorem normalized_double_sum_factor_const
    {P Q : Type*} [Fintype Q]
    (H : ℝ) (s : Finset P) (c : ℝ) (f : P → ℝ) (g : Q → ℝ) :
    (1 / H) * ∑ p ∈ s, ∑ q : Q, c * f p * g q =
      c * ((1 / H) * ∑ p ∈ s, f p) * ∑ q : Q, g q := by
  have hinner (p : P) :
      (∑ q : Q, c * f p * g q) =
        c * ∑ q : Q, f p * g q := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  simp_rw [hinner]
  rw [← Finset.mul_sum]
  calc
    (1 / H) * (c * ∑ p ∈ s, ∑ q : Q, f p * g q) =
        c * ((1 / H) * ∑ p ∈ s, ∑ q : Q, f p * g q) := by ring
    _ = c * ((1 / H) * ∑ p ∈ s, f p) * ∑ q : Q, g q := by
      rw [normalized_double_sum_factor H s f g]
      ring

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The squarefree analogue of the literal slow score. -/
def slowSquarefreeScore (m : B.sampleData.Sample) : ℝ :=
  ∑ p : BandPrime B.sampleData.n B.sampleData.W,
    B.primeDeviation p * divInd p.1 (B.sampleData.value m)

/-- The squarefree output statistic on one actual arithmetic band. -/
def squarefreeBandScore (i : Band) (m : B.sampleData.Sample) : ℝ :=
  ∑ p ∈ B.partition.data.fiber i,
    divInd p.1 (B.sampleData.value m)

/-- Squarefree-output analogue of `normalizedBandCovarianceRow`. -/
def normalizedSquarefreeBandCovarianceRow
    [Nonempty Head] (xi : B.ParamSpace)
    (F : B.sampleData.Sample → ℝ) (i : Band) : ℝ :=
  (B.tiltedLaw xi).covariance (B.squarefreeBandScore i) F /
    B.harmonicMass i

/-- The local `p^{-2}` deviation term which is deliberately retained in the
non-step prime-power calculation. -/
def bandDeviationReciprocalSquare (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2

/-- Named exact budget for the non-step prime-power row.  The first summand
is structural, the second is the analytic four-mark remainder, and the
third is the diagonal prime-power term. -/
def nonstepPrimePowerRowBudget
    (Cpow epsilon w W alpha localDiagonal : ℝ) : ℝ :=
  (21 * Cpow * (1 / W)) * (w * alpha) +
    (21 * epsilon * (1 / W)) * w +
  3 * (Cpow + epsilon) * localDiagonal

/-- Literal full-valuation row with the primewise non-step coefficient.
This formulation is law-generic, so the canonical raw reference law and
the final actual law can be compared without changing coefficients. -/
def nonstepFullCoefficientRow
    {Omega : Type*} [Fintype Omega] {Mlaw : ℕ}
    (law : BoundedValuationLaw Omega Mlaw) (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q * law.covVV p.1 q.1

/-- Literal squarefree row with the same primewise non-step coefficient. -/
def nonstepSquarefreeCoefficientRow
    {Omega : Type*} [Fintype Omega] {Mlaw : ℕ}
    (law : BoundedValuationLaw Omega Mlaw) (i : Band) : ℝ :=
  (1 / B.harmonicMass i) *
    ∑ p ∈ B.partition.data.fiber i,
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation q * law.covII p.1 q.1

/-- Exact identification of the full and squarefree raw slow rows with the
literal covariance rows on the actual tilted sample. -/
theorem normalizedSlowRows_eq_fullSquarefreeCoefficientRows
    [Nonempty Head] (xi : B.ParamSpace) (i : Band) :
    B.normalizedBandCovarianceRow xi B.slowScore i =
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                (B.actualValuationLaw xi).covVV p.1 q.1 ∧
      B.normalizedSquarefreeBandCovarianceRow xi B.slowSquarefreeScore i =
        (1 / B.harmonicMass i) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                (B.actualValuationLaw xi).covII p.1 q.1 := by
  constructor
  · unfold normalizedBandCovarianceRow bandScore slowScore
      actualValuationLaw BoundedValuationLaw.covVV BoundedValuationLaw.V
    rw [FiniteProbability.covariance_sum_left]
    simp_rw [FiniteProbability.covariance_sum_right,
      FiniteProbability.covariance_smul_right]
    ring
  · unfold normalizedSquarefreeBandCovarianceRow squarefreeBandScore
      slowSquarefreeScore
      actualValuationLaw BoundedValuationLaw.covII BoundedValuationLaw.I
    rw [FiniteProbability.covariance_sum_left]
    simp_rw [FiniteProbability.covariance_sum_right,
      FiniteProbability.covariance_smul_right]
    ring

set_option maxHeartbeats 3000000 in
/-- **Exact non-step slow-row ledger.**

The constant `21` is the sum of the three orientation constants `7`; no
factor depending on a mesh, a low centre, or a tilt box is hidden in it.
The only term not already proportional to the actual output centre is the
explicit `epsilon / W` remainder.  The diagonal is not bounded crudely by
`1/W`: its literal local value is exported for the moving-low-cell
specialization. -/
theorem abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
    {Omega : Type*} [Fintype Omega] {Mlaw : ℕ}
    (law : BoundedValuationLaw Omega Mlaw)
    {Cpow epsilon w : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon) (hw : 0 ≤ w)
    (hW : 1 < B.sampleData.W)
    (h75 : PrimePowerTransferBounds law
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.nonstepFullCoefficientRow law i -
        B.nonstepSquarefreeCoefficientRow law i| ≤
      nonstepPrimePowerRowBudget Cpow epsilon w
        (B.sampleData.W : ℝ) (B.bandCenter i)
        (B.bandDeviationReciprocalSquare i) := by
  let H := B.harmonicMass i
  let alpha := B.bandCenter i
  let invW : ℝ := 1 / (B.sampleData.W : ℝ)
  have hH : 0 < H := by simpa only [H] using B.harmonicMass_pos i
  have halpha : 0 < alpha := by simpa only [alpha] using B.bandCenter_pos i
  have hWreal : (0 : ℝ) < B.sampleData.W := by
    exact_mod_cast Nat.zero_lt_of_lt hW
  have hinvW0 : 0 ≤ invW := by dsimp only [invW]; positivity
  have hinvW1 : invW ≤ 1 := by
    dsimp only [invW]
    have hOne : (1 : ℝ) ≤ B.sampleData.W := by exact_mod_cast hW.le
    simpa only [one_div_one] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hOne
  have hpPos (p : BandPrime B.sampleData.n B.sampleData.W) :
      (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hpInv0 (p : BandPrime B.sampleData.n B.sampleData.W) :
      0 ≤ (1 / (p.1 : ℝ)) := by positivity
  have hpInvW (p : BandPrime B.sampleData.n B.sampleData.W) :
      (1 / (p.1 : ℝ)) ≤ invW := by
    exact one_div_le_one_div_of_le hWreal
      (by exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le)
  have ht0 (p : BandPrime B.sampleData.n B.sampleData.W) :
      0 ≤ tPrime B.sampleData.n p.1 :=
    PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand B.n_gt_one p.2
  have ht1 (p : BandPrime B.sampleData.n B.sampleData.W) :
      tPrime B.sampleData.n p.1 ≤ 1 :=
    PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand B.n_gt_one p.2
  let B1 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    |B.primeDeviation q| * (1 / (q.1 : ℝ))
  let G1 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
      (1 / (q.1 : ℝ))
  let B2 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2
  let G2 : ℝ := ∑ q : BandPrime B.sampleData.n B.sampleData.W,
    tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
      (1 / (q.1 : ℝ)) ^ 2
  have hB1 : B1 ≤ 7 * w := by
    simpa only [B1, primeDeviationL1, mul_comm] using hdevL1
  have hB10 : 0 ≤ B1 := by
    dsimp only [B1]
    exact Finset.sum_nonneg fun q _hq ↦ mul_nonneg (abs_nonneg _) (hpInv0 q)
  have hG10 : 0 ≤ G1 := by
    dsimp only [G1]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (mul_nonneg (ht0 q) (abs_nonneg _)) (hpInv0 q)
  have hB20 : 0 ≤ B2 := by
    dsimp only [B2]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (abs_nonneg _) (sq_nonneg _)
  have hG20 : 0 ≤ G2 := by
    dsimp only [G2]
    exact Finset.sum_nonneg fun q _hq ↦
      mul_nonneg (mul_nonneg (ht0 q) (abs_nonneg _)) (sq_nonneg _)
  have hG1 : G1 ≤ B1 := by
    dsimp only [G1, B1]
    apply Finset.sum_le_sum
    intro q _hq
    have hfac : 0 ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) :=
      mul_nonneg (abs_nonneg _) (hpInv0 q)
    nlinarith [mul_le_mul_of_nonneg_right (ht1 q) hfac]
  have hB2 : B2 ≤ invW * B1 := by
    dsimp only [B2, B1]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro q _hq
    have hmul := mul_le_mul_of_nonneg_left (hpInvW q) (abs_nonneg (B.primeDeviation q))
    calc
      |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2 =
          |B.primeDeviation q| * (1 / (q.1 : ℝ)) *
            (1 / (q.1 : ℝ)) := by ring
      _ ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) * invW :=
        mul_le_mul_of_nonneg_left (hpInvW q)
          (mul_nonneg (abs_nonneg _) (hpInv0 q))
      _ = invW * (|B.primeDeviation q| * (1 / (q.1 : ℝ))) := by ring
  have hG2 : G2 ≤ B2 := by
    dsimp only [G2, B2]
    apply Finset.sum_le_sum
    intro q _hq
    have hfac : 0 ≤ |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2 :=
      mul_nonneg (abs_nonneg _) (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right (ht1 q) hfac]
  have hG1w : G1 ≤ 7 * w := hG1.trans hB1
  have hB2w : B2 ≤ 7 * invW * w := by
    calc
      B2 ≤ invW * B1 := hB2
      _ ≤ invW * (7 * w) := mul_le_mul_of_nonneg_left hB1 hinvW0
      _ = 7 * invW * w := by ring
  have hG2w : G2 ≤ 7 * invW * w := hG2.trans hB2w
  have hfirst :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) = alpha := by
    change (1 / B.partition.data.mass i) *
        (∑ p ∈ B.partition.data.fiber i,
          tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) =
      (∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1) /
        B.partition.data.mass i
    rw [show (∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) =
        ∑ p ∈ B.partition.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime B.sampleData.n p.1 by
      apply Finset.sum_congr rfl
      intro p _hp
      ring]
    ring
  have hmass :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) = 1 := by
    change (1 / H) * H = 1
    field_simp [ne_of_gt hH]
  have hfirst2 :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2 ≤
          invW * alpha := by
    calc
      _ ≤ (1 / H) * ∑ p ∈ B.partition.data.fiber i,
          invW * (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        calc
          tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2 =
              (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) *
                (1 / (p.1 : ℝ)) := by ring
          _ ≤ (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) * invW :=
            mul_le_mul_of_nonneg_left (hpInvW p)
              (mul_nonneg (ht0 p) (hpInv0 p))
          _ = _ := by ring
      _ = invW * alpha := by
        rw [← Finset.mul_sum]
        calc
          (1 / H) *
              (invW * ∑ p ∈ B.partition.data.fiber i,
                tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) =
              invW * ((1 / H) *
                ∑ p ∈ B.partition.data.fiber i,
                  tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) := by ring
          _ = invW * alpha := by rw [hfirst]
  have hmass2 :
      (1 / H) * ∑ p ∈ B.partition.data.fiber i,
        (1 / (p.1 : ℝ)) ^ 2 ≤ invW := by
    calc
      _ ≤ (1 / H) * ∑ p ∈ B.partition.data.fiber i,
          invW * (1 / (p.1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum
        intro p _hp
        simpa only [pow_two] using
          mul_le_mul_of_nonneg_right (hpInvW p) (hpInv0 p)
      _ = invW := by
        rw [← Finset.mul_sum]
        calc
          (1 / H) *
              (invW * ∑ p ∈ B.partition.data.fiber i,
                (1 / (p.1 : ℝ))) =
              invW * ((1 / H) *
                ∑ p ∈ B.partition.data.fiber i,
                  (1 / (p.1 : ℝ))) := by ring
          _ = invW := by rw [hmass, mul_one]
  -- Build the entry display on the diagonal, where the public
  -- off-diagonal theorem intentionally requires `p ≠ q`.
  have hentry' (p q : BandPrime B.sampleData.n B.sampleData.W) :
      |law.covVV p.1 q.1 - law.covII p.1 q.1| ≤
        (Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n q.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
        (Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n q.1 + epsilon) *
            (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
        (Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n q.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
        (if p = q then
          3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0) := by
    by_cases hpq : p = q
    · subst q
      rw [if_pos rfl]
      have hd :=
        PrimePowerSharpBandTransfer.abs_covVV_sub_covII_le_of_transferBounds_diagonal
          law h75 p
      have hoff : 0 ≤
          (Cpow * tPrime B.sampleData.n p.1 *
                tPrime B.sampleData.n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) +
          (Cpow * tPrime B.sampleData.n p.1 *
                tPrime B.sampleData.n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) ^ 2 +
          (Cpow * tPrime B.sampleData.n p.1 *
                tPrime B.sampleData.n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) ^ 2 := by
        have hc : 0 ≤ Cpow * tPrime B.sampleData.n p.1 *
              tPrime B.sampleData.n p.1 + epsilon :=
          add_nonneg
            (mul_nonneg (mul_nonneg hCpow (ht0 p)) (ht0 p)) hepsilon
        positivity
      linarith
    · rw [if_neg hpq]
      simpa only [add_zero] using
        PrimePowerSharpBandTransfer.abs_covVV_sub_covII_le_of_transferBounds_of_ne
          law h75 p q hpq
  unfold nonstepFullCoefficientRow nonstepSquarefreeCoefficientRow
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  have hdiff :
      (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law.covVV p.1 q.1) -
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                B.primeDeviation q * law.covII p.1 q.1) =
        (1 / H) *
          ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              B.primeDeviation q *
                (law.covVV p.1 q.1 - law.covII p.1 q.1) := by
    congr 1
    apply Finset.sum_congr rfl
    intro p _hp
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro q _hq
    ring
  rw [hdiff]
  calc
    |(1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation q * (law.covVV p.1 q.1 - law.covII p.1 q.1)| ≤
      (1 / H) *
        ∑ p ∈ B.partition.data.fiber i,
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |B.primeDeviation q| *
              |law.covVV p.1 q.1 - law.covII p.1 q.1| := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (1 / H : ℝ))]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum fun p _hp ↦
            (Finset.abs_sum_le_sum_abs _ _).trans
              (Finset.sum_le_sum fun q _hq ↦ by rw [abs_mul]))
    _ ≤ (21 * Cpow * invW) * (w * alpha) +
          (21 * epsilon * invW) * w +
          3 * (Cpow + epsilon) * B.bandDeviationReciprocalSquare i := by
      -- Each of `JI`, `IJ`, and `JJ` is contracted separately; the
      -- diagonal remains literal.  `ring_nf` after distributivity leaves
      -- precisely the four moment products proved above.
      have hpoint (p : BandPrime B.sampleData.n B.sampleData.W)
          (q : BandPrime B.sampleData.n B.sampleData.W) :
          |B.primeDeviation q| *
              |law.covVV p.1 q.1 - law.covII p.1 q.1| ≤
            |B.primeDeviation q| *
              ((Cpow * tPrime B.sampleData.n p.1 *
                    tPrime B.sampleData.n q.1 + epsilon) *
                  (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
               (Cpow * tPrime B.sampleData.n p.1 *
                    tPrime B.sampleData.n q.1 + epsilon) *
                  (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
               (Cpow * tPrime B.sampleData.n p.1 *
                    tPrime B.sampleData.n q.1 + epsilon) *
                  (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
               (if p = q then
                  3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0)) :=
        mul_le_mul_of_nonneg_left (hentry' p q) (abs_nonneg _)
      calc
        _ ≤ (1 / H) * ∑ p ∈ B.partition.data.fiber i,
            ∑ q : BandPrime B.sampleData.n B.sampleData.W,
              |B.primeDeviation q| *
                ((Cpow * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
                 (Cpow * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
                 (Cpow * tPrime B.sampleData.n p.1 *
                      tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
                 (if p = q then
                    3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact Finset.sum_le_sum fun p _hp ↦
            Finset.sum_le_sum fun q _hq ↦ hpoint p q
        _ ≤ _ := by
          let OT1 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))
          let O1 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i, (1 / (p.1 : ℝ))
          let OT2 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2
          let O2 : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i, (1 / (p.1 : ℝ)) ^ 2
          let JI : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  ((Cpow * tPrime B.sampleData.n p.1 *
                        tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)))
          let IJ : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  ((Cpow * tPrime B.sampleData.n p.1 *
                        tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2)
          let JJ : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  ((Cpow * tPrime B.sampleData.n p.1 *
                        tPrime B.sampleData.n q.1 + epsilon) *
                    (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2)
          let D : ℝ := (1 / H) *
            ∑ p ∈ B.partition.data.fiber i,
              ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                |B.primeDeviation q| *
                  (if p = q then
                    3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0)
          have hsplit :
              (1 / H) * ∑ p ∈ B.partition.data.fiber i,
                ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                  |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
                     (Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                        (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
                     (Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 +
                     (if p = q then 3 * (Cpow + epsilon) *
                        (1 / (p.1 : ℝ)) ^ 2 else 0)) =
                JI + IJ + JJ + D := by
            dsimp only [JI, IJ, JJ, D]
            simp_rw [mul_add, Finset.sum_add_distrib]
            ring
          have hJIeq : JI = Cpow * OT2 * G1 + epsilon * O2 * B1 := by
            have hpointEq (p : BandPrime B.sampleData.n B.sampleData.W)
                (q : BandPrime B.sampleData.n B.sampleData.W) :
                |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                      (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ))) =
                  Cpow *
                    (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2) *
                    (tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
                      (1 / (q.1 : ℝ))) +
                  epsilon * (1 / (p.1 : ℝ)) ^ 2 *
                    (|B.primeDeviation q| * (1 / (q.1 : ℝ))) := by ring
            dsimp only [JI]
            simp_rw [hpointEq, Finset.sum_add_distrib]
            rw [mul_add,
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) Cpow
                (fun p ↦ tPrime B.sampleData.n p.1 *
                  (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ tPrime B.sampleData.n q.1 *
                  |B.primeDeviation q| * (1 / (q.1 : ℝ))),
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) epsilon
                (fun p ↦ (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ |B.primeDeviation q| * (1 / (q.1 : ℝ)))]
          have hIJeq : IJ = Cpow * OT1 * G2 + epsilon * O1 * B2 := by
            have hpointEq (p : BandPrime B.sampleData.n B.sampleData.W)
                (q : BandPrime B.sampleData.n B.sampleData.W) :
                |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                      (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2) =
                  Cpow *
                    (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ))) *
                    (tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
                      (1 / (q.1 : ℝ)) ^ 2) +
                  epsilon * (1 / (p.1 : ℝ)) *
                    (|B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2) := by ring
            dsimp only [IJ]
            simp_rw [hpointEq, Finset.sum_add_distrib]
            rw [mul_add,
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) Cpow
                (fun p ↦ tPrime B.sampleData.n p.1 *
                  (1 / (p.1 : ℝ)))
                (fun q ↦ tPrime B.sampleData.n q.1 *
                  |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2),
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) epsilon
                (fun p ↦ (1 / (p.1 : ℝ)))
                (fun q ↦ |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2)]
          have hJJeq : JJ = Cpow * OT2 * G2 + epsilon * O2 * B2 := by
            have hpointEq (p : BandPrime B.sampleData.n B.sampleData.W)
                (q : BandPrime B.sampleData.n B.sampleData.W) :
                |B.primeDeviation q| *
                    ((Cpow * tPrime B.sampleData.n p.1 *
                          tPrime B.sampleData.n q.1 + epsilon) *
                      (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2) =
                  Cpow *
                    (tPrime B.sampleData.n p.1 * (1 / (p.1 : ℝ)) ^ 2) *
                    (tPrime B.sampleData.n q.1 * |B.primeDeviation q| *
                      (1 / (q.1 : ℝ)) ^ 2) +
                  epsilon * (1 / (p.1 : ℝ)) ^ 2 *
                    (|B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2) := by ring
            dsimp only [JJ]
            simp_rw [hpointEq, Finset.sum_add_distrib]
            rw [mul_add,
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) Cpow
                (fun p ↦ tPrime B.sampleData.n p.1 *
                  (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ tPrime B.sampleData.n q.1 *
                  |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2),
              normalized_double_sum_factor_const H
                (B.partition.data.fiber i) epsilon
                (fun p ↦ (1 / (p.1 : ℝ)) ^ 2)
                (fun q ↦ |B.primeDeviation q| * (1 / (q.1 : ℝ)) ^ 2)]
          have hDeq : D =
              3 * (Cpow + epsilon) * B.bandDeviationReciprocalSquare i := by
            have hinner (p : BandPrime B.sampleData.n B.sampleData.W) :
                (∑ q : BandPrime B.sampleData.n B.sampleData.W,
                  |B.primeDeviation q| *
                    (if p = q then 3 * (Cpow + epsilon) *
                      (1 / (p.1 : ℝ)) ^ 2 else 0)) =
                  |B.primeDeviation p| *
                    (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2) := by
              calc
                _ = ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                    if q = p then
                      |B.primeDeviation q| *
                        (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2)
                    else 0 := by
                      apply Finset.sum_congr rfl
                      intro q _hq
                      by_cases hpq : p = q
                      · subst q; simp
                      · have hqp : q ≠ p := fun h ↦ hpq h.symm
                        simp [hpq, hqp]
                _ = _ := by simp
            dsimp only [D]
            simp_rw [hinner]
            rw [show (∑ p ∈ B.partition.data.fiber i,
                |B.primeDeviation p| *
                  (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2)) =
                3 * (Cpow + epsilon) *
                  ∑ p ∈ B.partition.data.fiber i,
                    |B.primeDeviation p| * (1 / (p.1 : ℝ)) ^ 2 by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro p _hp
              ring]
            unfold bandDeviationReciprocalSquare
            ring
          have hJI : JI ≤
              7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w := by
            rw [hJIeq]
            have hOT2 : OT2 ≤ invW * alpha := by simpa only [OT2] using hfirst2
            have hO2 : O2 ≤ invW := by simpa only [O2] using hmass2
            calc
              Cpow * OT2 * G1 + epsilon * O2 * B1 ≤
                  Cpow * (invW * alpha) * (7 * w) +
                    epsilon * invW * (7 * w) := by gcongr
              _ = _ := by ring
          have hIJ : IJ ≤
              7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w := by
            rw [hIJeq]
            have hOT1 : OT1 = alpha := by simpa only [OT1] using hfirst
            have hO1 : O1 = 1 := by simpa only [O1] using hmass
            rw [hOT1, hO1]
            simp only [mul_one]
            calc
              Cpow * alpha * G2 + epsilon * B2 ≤
                  Cpow * alpha * (7 * invW * w) +
                    epsilon * (7 * invW * w) := by gcongr
              _ = _ := by ring
          have hJJ : JJ ≤
              7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w := by
            rw [hJJeq]
            have hOT2 : OT2 ≤ invW * alpha := by simpa only [OT2] using hfirst2
            have hO2 : O2 ≤ invW := by simpa only [O2] using hmass2
            have hinvSq : invW * invW ≤ invW := by nlinarith
            calc
              Cpow * OT2 * G2 + epsilon * O2 * B2 ≤
                  Cpow * (invW * alpha) * (7 * invW * w) +
                    epsilon * invW * (7 * invW * w) := by gcongr
              _ ≤ 7 * Cpow * invW * w * alpha +
                    7 * epsilon * invW * w := by
                have hca : 0 ≤ 7 * Cpow * w * alpha := by positivity
                have hew : 0 ≤ 7 * epsilon * w := by positivity
                nlinarith [mul_le_mul_of_nonneg_left hinvSq hca,
                  mul_le_mul_of_nonneg_left hinvSq hew]
          rw [hsplit]
          calc
            JI + IJ + JJ + D ≤
                (7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w) +
                (7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w) +
                (7 * Cpow * invW * w * alpha + 7 * epsilon * invW * w) +
                3 * (Cpow + epsilon) *
                  B.bandDeviationReciprocalSquare i :=
              add_le_add (add_le_add (add_le_add hJI hIJ) hJJ) hDeq.le
            _ = (21 * Cpow * invW) * (w * alpha) +
                  (21 * epsilon * invW) * w +
                  3 * (Cpow + epsilon) *
                    B.bandDeviationReciprocalSquare i := by ring
    _ = nonstepPrimePowerRowBudget Cpow epsilon w
          (B.sampleData.W : ℝ) (B.bandCenter i)
          (B.bandDeviationReciprocalSquare i) := by
      simp only [nonstepPrimePowerRowBudget, invW, alpha]

/-- Actual-law specialization of the law-generic exact non-step ledger. -/
theorem abs_normalizedSlowRow_sub_squarefree_le_nonstepBudget
    [Nonempty Head]
    (xi : B.ParamSpace)
    {Cpow epsilon w : ℝ}
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon) (hw : 0 ≤ w)
    (hW : 1 < B.sampleData.W)
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hdevL1 : B.primeDeviationL1 ≤ 7 * w)
    (i : Band) :
    |B.normalizedBandCovarianceRow xi B.slowScore i -
        B.normalizedSquarefreeBandCovarianceRow xi B.slowSquarefreeScore i| ≤
      nonstepPrimePowerRowBudget Cpow epsilon w
        (B.sampleData.W : ℝ) (B.bandCenter i)
        (B.bandDeviationReciprocalSquare i) := by
  have hrows := B.normalizedSlowRows_eq_fullSquarefreeCoefficientRows xi i
  rw [hrows.1, hrows.2]
  exact B.abs_nonstepFullCoefficientRow_sub_squarefree_le_nonstepBudget
    (B.actualValuationLaw xi) hCpow hepsilon hw hW h75 hdevL1 i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
