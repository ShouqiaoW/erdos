import Erdos390.Full.FiniteLogStieltjes
import Erdos390.Full.PaperBridgePhysicalValuationRow
import Erdos390.Full.PaperNuisancePrimeLogRows
import Erdos390.Full.PrimePowerLcmGeometry

/-!
# Exact reductions for the two medium-law nuisance inputs

The nuisance Schur row in paper Lemma 8.6 uses two arithmetic facts about
the literal medium-prime component laws:

* a Stieltjes bound for `Cov(v_p, log (m / n))` inside one cell; and
* agreement, to reciprocal-logarithmic precision, of `E v_p` in two cells.

This file proves all finite probability, Abel summation, prime-power
summation, and physical-log identifications surrounding those two facts.
It intentionally does **not** replace the remaining arithmetic estimates by
a bundled certificate.  The hypotheses in the two terminal reductions are
the literal moving-prefix estimate and the literal prime-power/tail
estimates which still have to be obtained from the marked-cell theorem.
-/

open scoped BigOperators Interval

namespace Erdos390.Full

noncomputable section

open ArithmeticModel FiniteProbability ValuationScoreDomination
open DivisibilityMomentBounds

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Subtracting a deterministic constant from the right statistic does not
change covariance.  This is used to pass exactly from `log m` to
`log (m / n)`. -/
theorem covariance_sub_const_right
    (mu : FiniteProbability Omega) (F G : Omega → ℝ) (a : ℝ) :
    mu.covariance F (fun omega ↦ G omega - a) = mu.covariance F G := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (G omega - a)) =
      (∑ omega, mu.mass omega * G omega) -
        a * (∑ omega, mu.mass omega) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * (F omega * (G omega - a))) =
      (∑ omega, mu.mass omega * (F omega * G omega)) -
        a * (∑ omega, mu.mass omega * F omega) by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [mu.mass_sum]
  ring

/-- The first derivative at zero of `Cov(F,G)` under exponential tilting by
`S`, written in the centered form used in the paper's Stieltjes argument. -/
def covarianceThirdCentered
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ) : ℝ :=
  mu.covariance (fun omega ↦ F omega * G omega) S -
    mu.covariance F S * mu.expect G -
    mu.expect F * mu.covariance G S

theorem covarianceThirdCentered_add_score
    (mu : FiniteProbability Omega) (F G S T : Omega → ℝ) :
    mu.covarianceThirdCentered F G (fun omega ↦ S omega + T omega) =
      mu.covarianceThirdCentered F G S +
        mu.covarianceThirdCentered F G T := by
  unfold covarianceThirdCentered
  rw [mu.covariance_add_right, mu.covariance_add_right,
    mu.covariance_add_right]
  ring_nf

theorem covarianceThirdCentered_smul_score
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ) (a : ℝ) :
    mu.covarianceThirdCentered F G (fun omega ↦ a * S omega) =
      a * mu.covarianceThirdCentered F G S := by
  unfold covarianceThirdCentered
  rw [mu.covariance_smul_right, mu.covariance_smul_right,
    mu.covariance_smul_right]
  ring_nf

theorem covarianceThirdCentered_sum_score
    {Iota : Type*} [DecidableEq Iota]
    (mu : FiniteProbability Omega) (F G : Omega → ℝ)
    (s : Finset Iota) (S : Iota → Omega → ℝ) :
    mu.covarianceThirdCentered F G (fun omega ↦ ∑ i ∈ s, S i omega) =
      ∑ i ∈ s, mu.covarianceThirdCentered F G (S i) := by
  induction s using Finset.induction_on with
  | empty => simp [covarianceThirdCentered, covariance, expect]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covarianceThirdCentered_add_score, ih]

theorem covarianceThirdCentered_add_left
    (mu : FiniteProbability Omega) (F T G S : Omega → ℝ) :
    mu.covarianceThirdCentered (fun omega ↦ F omega + T omega) G S =
      mu.covarianceThirdCentered F G S +
        mu.covarianceThirdCentered T G S := by
  unfold covarianceThirdCentered
  rw [show (fun omega ↦ (F omega + T omega) * G omega) =
      fun omega ↦ F omega * G omega + T omega * G omega by
    funext omega
    ring]
  rw [mu.covariance_add_left, mu.covariance_add_left,
    mu.expect_add]
  ring_nf

theorem covarianceThirdCentered_sum_left
    {Iota : Type*} [DecidableEq Iota]
    (mu : FiniteProbability Omega) (G S : Omega → ℝ)
    (s : Finset Iota) (F : Iota → Omega → ℝ) :
    mu.covarianceThirdCentered (fun omega ↦ ∑ i ∈ s, F i omega) G S =
      ∑ i ∈ s, mu.covarianceThirdCentered (F i) G S := by
  induction s using Finset.induction_on with
  | empty => simp [covarianceThirdCentered, covariance, expect]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covarianceThirdCentered_add_left, ih]

/-- Symmetric third-cumulant identity.  For divisibility indicators the
product `F*H` becomes the indicator of the lcm, reducing the whole
first-order tilted physical calculation to three centered prefix rows. -/
theorem covarianceThirdCentered_eq_covariance_mul
    (mu : FiniteProbability Omega) (F G H : Omega → ℝ) :
    mu.covarianceThirdCentered F G H =
      mu.covariance (fun omega ↦ F omega * H omega) G -
        mu.expect H * mu.covariance F G -
        mu.expect F * mu.covariance H G := by
  have hHG : mu.expect (fun omega ↦ H omega * G omega) =
      mu.expect (fun omega ↦ G omega * H omega) := by
    unfold expect
    apply Finset.sum_congr rfl
    intro omega _
    ring
  have hFHG : mu.expect (fun omega ↦ F omega * G omega * H omega) =
      mu.expect (fun omega ↦ F omega * H omega * G omega) := by
    unfold expect
    apply Finset.sum_congr rfl
    intro omega _
    ring
  unfold covarianceThirdCentered covariance
  rw [hHG, hFHG]
  ring_nf

/-- Three literal centered divisor/prefix rows control the first-order
third cumulant.  Coprimality turns the lcm scale into the product `D*E`;
no independence statement is used. -/
theorem abs_covarianceThirdCentered_divInd_prefix_divInd_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) {D E : ℕ} {K A L : ℝ}
    (hD : 0 < D) (hE : 0 < E) (hcop : Nat.Coprime D E)
    (hK : 0 ≤ K) (hA : 0 ≤ A) (hL : 0 < L)
    (hcovD : |mu.covariance (fun omega ↦ divInd D (value omega)) pref| ≤
      K / ((D : ℝ) * L))
    (hcovE : |mu.covariance (fun omega ↦ divInd E (value omega)) pref| ≤
      K / ((E : ℝ) * L))
    (hcovDE : |mu.covariance
        (fun omega ↦ divInd (D * E) (value omega)) pref| ≤
      K / (((D : ℝ) * (E : ℝ)) * L))
    (hexpectD : mu.expect (fun omega ↦ divInd D (value omega)) ≤
      A / (D : ℝ))
    (hexpectE : mu.expect (fun omega ↦ divInd E (value omega)) ≤
      A / (E : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ divInd D (value omega)) pref
        (fun omega ↦ divInd E (value omega))| ≤
      (K * (1 + 2 * A)) /
        (((D : ℝ) * (E : ℝ)) * L) := by
  have hDEpoint :
      (fun omega ↦ divInd D (value omega) * divInd E (value omega)) =
        fun omega ↦ divInd (D * E) (value omega) := by
    funext omega
    rw [DivisibilityMomentBounds.divInd_mul_eq_lcm, hcop.lcm_eq_mul]
  rw [mu.covarianceThirdCentered_eq_covariance_mul, hDEpoint]
  have hED0 : 0 ≤ mu.expect (fun omega ↦ divInd D (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg _ _)
  have hEE0 : 0 ≤ mu.expect (fun omega ↦ divInd E (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg _ _)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  have hscaleD : 0 ≤ K / ((D : ℝ) * L) := by positivity
  have hscaleE : 0 ≤ K / ((E : ℝ) * L) := by positivity
  calc
    |mu.covariance (fun omega ↦ divInd (D * E) (value omega)) pref -
        mu.expect (fun omega ↦ divInd E (value omega)) *
          mu.covariance (fun omega ↦ divInd D (value omega)) pref -
        mu.expect (fun omega ↦ divInd D (value omega)) *
          mu.covariance (fun omega ↦ divInd E (value omega)) pref| ≤
      |mu.covariance (fun omega ↦ divInd (D * E) (value omega)) pref| +
        mu.expect (fun omega ↦ divInd E (value omega)) *
          |mu.covariance (fun omega ↦ divInd D (value omega)) pref| +
        mu.expect (fun omega ↦ divInd D (value omega)) *
          |mu.covariance (fun omega ↦ divInd E (value omega)) pref| := by
      calc
        _ ≤ |mu.covariance
              (fun omega ↦ divInd (D * E) (value omega)) pref -
            mu.expect (fun omega ↦ divInd E (value omega)) *
              mu.covariance (fun omega ↦ divInd D (value omega)) pref| +
            |mu.expect (fun omega ↦ divInd D (value omega)) *
              mu.covariance (fun omega ↦ divInd E (value omega)) pref| :=
          abs_sub _ _
        _ ≤ (|mu.covariance
              (fun omega ↦ divInd (D * E) (value omega)) pref| +
            |mu.expect (fun omega ↦ divInd E (value omega)) *
              mu.covariance (fun omega ↦ divInd D (value omega)) pref|) +
            |mu.expect (fun omega ↦ divInd D (value omega)) *
              mu.covariance (fun omega ↦ divInd E (value omega)) pref| :=
          add_le_add (abs_sub _ _) le_rfl
        _ = _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg hEE0, abs_of_nonneg hED0]
    _ ≤ K / (((D : ℝ) * (E : ℝ)) * L) +
        (A / (E : ℝ)) * (K / ((D : ℝ) * L)) +
        (A / (D : ℝ)) * (K / ((E : ℝ) * L)) := by
      exact add_le_add
        (add_le_add hcovDE
          (mul_le_mul hexpectE hcovD (abs_nonneg _) (div_nonneg hA hER.le)))
        (mul_le_mul hexpectD hcovE (abs_nonneg _) (div_nonneg hA hDR.le))
    _ = (K * (1 + 2 * A)) /
        (((D : ℝ) * (E : ℝ)) * L) := by
      field_simp [hDR.ne', hER.ne', hL.ne']
      ring

/-- Non-coprime version of the three-row cumulant estimate.  The joint row
is charged at the literal lcm scale; this is the local-prime input used when
the forced valuation prime is restored into the compact tilt. -/
theorem abs_covarianceThirdCentered_divInd_prefix_divInd_lcm_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) {D E : ℕ} {K A L : ℝ}
    (hD : 0 < D) (hE : 0 < E)
    (hA : 0 ≤ A)
    (hcovD : |mu.covariance (fun omega ↦ divInd D (value omega)) pref| ≤
      K / ((D : ℝ) * L))
    (hcovE : |mu.covariance (fun omega ↦ divInd E (value omega)) pref| ≤
      K / ((E : ℝ) * L))
    (hcovLcm : |mu.covariance
        (fun omega ↦ divInd (Nat.lcm D E) (value omega)) pref| ≤
      K / ((Nat.lcm D E : ℝ) * L))
    (hexpectD : mu.expect (fun omega ↦ divInd D (value omega)) ≤
      A / (D : ℝ))
    (hexpectE : mu.expect (fun omega ↦ divInd E (value omega)) ≤
      A / (E : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ divInd D (value omega)) pref
        (fun omega ↦ divInd E (value omega))| ≤
      K / ((Nat.lcm D E : ℝ) * L) +
        (A / (E : ℝ)) * (K / ((D : ℝ) * L)) +
        (A / (D : ℝ)) * (K / ((E : ℝ) * L)) := by
  have hDEpoint :
      (fun omega ↦ divInd D (value omega) * divInd E (value omega)) =
        fun omega ↦ divInd (Nat.lcm D E) (value omega) := by
    funext omega
    rw [DivisibilityMomentBounds.divInd_mul_eq_lcm]
  rw [mu.covarianceThirdCentered_eq_covariance_mul, hDEpoint]
  have hED0 : 0 ≤ mu.expect (fun omega ↦ divInd D (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg _ _)
  have hEE0 : 0 ≤ mu.expect (fun omega ↦ divInd E (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg _ _)
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hER : (0 : ℝ) < E := by exact_mod_cast hE
  calc
    |mu.covariance
          (fun omega ↦ divInd (Nat.lcm D E) (value omega)) pref -
        mu.expect (fun omega ↦ divInd E (value omega)) *
          mu.covariance (fun omega ↦ divInd D (value omega)) pref -
        mu.expect (fun omega ↦ divInd D (value omega)) *
          mu.covariance (fun omega ↦ divInd E (value omega)) pref| ≤
      |mu.covariance
          (fun omega ↦ divInd (Nat.lcm D E) (value omega)) pref| +
        mu.expect (fun omega ↦ divInd E (value omega)) *
          |mu.covariance (fun omega ↦ divInd D (value omega)) pref| +
        mu.expect (fun omega ↦ divInd D (value omega)) *
          |mu.covariance (fun omega ↦ divInd E (value omega)) pref| := by
      calc
        _ ≤ |mu.covariance
              (fun omega ↦ divInd (Nat.lcm D E) (value omega)) pref -
            mu.expect (fun omega ↦ divInd E (value omega)) *
              mu.covariance (fun omega ↦ divInd D (value omega)) pref| +
            |mu.expect (fun omega ↦ divInd D (value omega)) *
              mu.covariance (fun omega ↦ divInd E (value omega)) pref| :=
          abs_sub _ _
        _ ≤ (|mu.covariance
              (fun omega ↦ divInd (Nat.lcm D E) (value omega)) pref| +
            |mu.expect (fun omega ↦ divInd E (value omega)) *
              mu.covariance (fun omega ↦ divInd D (value omega)) pref|) +
            |mu.expect (fun omega ↦ divInd D (value omega)) *
              mu.covariance (fun omega ↦ divInd E (value omega)) pref| :=
          add_le_add (abs_sub _ _) le_rfl
        _ = _ := by
          rw [abs_mul, abs_mul, abs_of_nonneg hEE0, abs_of_nonneg hED0]
    _ ≤ K / ((Nat.lcm D E : ℝ) * L) +
        (A / (E : ℝ)) * (K / ((D : ℝ) * L)) +
        (A / (D : ℝ)) * (K / ((E : ℝ) * L)) := by
      exact add_le_add
        (add_le_add hcovLcm
          (mul_le_mul hexpectE hcovD (abs_nonneg _)
            (div_nonneg hA hER.le)))
        (mul_le_mul hexpectD hcovE (abs_nonneg _)
          (div_nonneg hA hDR.le))

/-- A finite omitted-local divisor score inherits the third-cumulant bound
term by term.  This is an exact finite identity followed only by the triangle
inequality; in particular it introduces no cardinality or harmonic-loss
factor beyond the explicitly displayed weighted sum. -/
theorem abs_covarianceThirdCentered_weighted_divInd_sum_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (F G : Omega → ℝ) (R : Finset ℕ)
    (coeff bound : ℕ → ℝ)
    (hbound : ∀ E ∈ R,
      |mu.covarianceThirdCentered F G
          (fun omega ↦ divInd E (value omega))| ≤ bound E) :
    |mu.covarianceThirdCentered F G
        (fun omega ↦ ∑ E ∈ R, coeff E * divInd E (value omega))| ≤
      ∑ E ∈ R, |coeff E| * bound E := by
  rw [mu.covarianceThirdCentered_sum_score]
  calc
    |∑ E ∈ R,
        mu.covarianceThirdCentered F G
          (fun omega ↦ coeff E * divInd E (value omega))| =
        |∑ E ∈ R, coeff E *
          mu.covarianceThirdCentered F G
            (fun omega ↦ divInd E (value omega))| := by
      congr 1
      apply Finset.sum_congr rfl
      intro E hE
      rw [mu.covarianceThirdCentered_smul_score]
    _ ≤ ∑ E ∈ R,
        |coeff E * mu.covarianceThirdCentered F G
          (fun omega ↦ divInd E (value omega))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ E ∈ R, |coeff E| *
        |mu.covarianceThirdCentered F G
          (fun omega ↦ divInd E (value omega))| := by
      apply Finset.sum_congr rfl
      intro E hE
      rw [abs_mul]
    _ ≤ ∑ E ∈ R, |coeff E| * bound E := by
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_left (hbound E hE) (abs_nonneg _)

/-- Box-bounded coefficients and reciprocal-scale component estimates give
the exact reciprocal-mass bound needed for the first Taylor coefficient.
The coefficient `B` is outside the reciprocal sum and hence is independent
of the number of prime-power score terms. -/
theorem abs_covarianceThirdCentered_weighted_divInd_sum_reciprocal_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (F G : Omega → ℝ) (R : Finset ℕ)
    (coeff : ℕ → ℝ) {B C D L : ℝ}
    (hC : 0 ≤ C) (hD : 0 < D) (hL : 0 < L)
    (hRpos : ∀ E ∈ R, 0 < E)
    (hcoeff : ∀ E ∈ R, |coeff E| ≤ B)
    (hcomponent : ∀ E ∈ R,
      |mu.covarianceThirdCentered F G
          (fun omega ↦ divInd E (value omega))| ≤
        C / (D * (E : ℝ) * L)) :
    |mu.covarianceThirdCentered F G
        (fun omega ↦ ∑ E ∈ R, coeff E * divInd E (value omega))| ≤
      (B * C / (D * L)) * ∑ E ∈ R, 1 / (E : ℝ) := by
  have hraw := mu.abs_covarianceThirdCentered_weighted_divInd_sum_le
    value F G R coeff (fun E ↦ C / (D * (E : ℝ) * L)) hcomponent
  refine hraw.trans ?_
  calc
    ∑ E ∈ R, |coeff E| * (C / (D * (E : ℝ) * L)) ≤
        ∑ E ∈ R, B * (C / (D * (E : ℝ) * L)) := by
      apply Finset.sum_le_sum
      intro E hE
      exact mul_le_mul_of_nonneg_right (hcoeff E hE) (by positivity)
    _ = (B * C / (D * L)) * ∑ E ∈ R, 1 / (E : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro E hE
      have hEpos : (0 : ℝ) < E := by exact_mod_cast hRpos E hE
      field_simp [hD.ne', hL.ne', hEpos.ne']

/-- The genuine valuation tilt has a first Taylor coefficient of size
`L⁻²` times the literal prime-power reciprocal mass.  One factor `L⁻¹`
comes from the un-tilted centered prefix row and the other from the score
coefficient.  This is the precise cancellation that a total-variation
argument would lose. -/
theorem abs_covarianceThirdCentered_valuationScore_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (F G : Omega → ℝ) (P : Finset ℕ) (eta : ℕ → ℝ)
    (M : ℕ) {B C D L : ℝ}
    (hB : 0 ≤ B) (hD : 0 < D) (hL : 0 < L)
    (hprime : ∀ p ∈ P, p.Prime)
    (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (heta : ∀ p ∈ P, |eta p| ≤ B)
    (hcomponent : ∀ p ∈ P, ∀ k ∈ positiveExponents M,
      |mu.covarianceThirdCentered F G
          (fun omega ↦ divInd (p ^ k) (value omega))| ≤
        C / (D * ((p ^ k : ℕ) : ℝ) * L)) :
    |mu.covarianceThirdCentered F G
        (fun omega ↦ valuationScore P eta L (value omega))| ≤
      (B * C / (D * L ^ 2)) *
        ∑ p ∈ P, ∑ k ∈ positiveExponents M,
          1 / ((p ^ k : ℕ) : ℝ) := by
  have hscoreEq :
      (fun omega ↦ valuationScore P eta L (value omega)) =
        fun omega ↦ ∑ p ∈ P, ∑ k ∈ positiveExponents M,
          (eta p / L) * divInd (p ^ k) (value omega) := by
    funext omega
    exact valuationScore_eq_indicator_sum_of_le P eta L hprime
      (hvaluePos omega) (hvalueLe omega)
  rw [hscoreEq, mu.covarianceThirdCentered_sum_score]
  simp_rw [mu.covarianceThirdCentered_sum_score,
    mu.covarianceThirdCentered_smul_score]
  calc
    |∑ p ∈ P, ∑ k ∈ positiveExponents M,
        eta p / L * mu.covarianceThirdCentered F G
          (fun omega ↦ divInd (p ^ k) (value omega))| ≤
      ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        |eta p / L * mu.covarianceThirdCentered F G
          (fun omega ↦ divInd (p ^ k) (value omega))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun p hp ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (|eta p| / L) *
          |mu.covarianceThirdCentered F G
            (fun omega ↦ divInd (p ^ k) (value omega))| := by
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul, abs_div, abs_of_pos hL]
    _ ≤ ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        (B / L) * (C / (D * ((p ^ k : ℕ) : ℝ) * L)) := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul
        (div_le_div_of_nonneg_right (heta p hp) hL.le)
        (hcomponent p hp k hk) (abs_nonneg _)
        (div_nonneg hB hL.le)
    _ = (B * C / (D * L ^ 2)) *
        ∑ p ∈ P, ∑ k ∈ positiveExponents M,
          1 / ((p ^ k : ℕ) : ℝ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      have hpkNat : 0 < p ^ k := pow_pos (hprime p hp).pos k
      have hpkpos : (0 : ℝ) < (p ^ k : ℕ) := by exact_mod_cast hpkNat
      field_simp [hD.ne', hL.ne', hpkpos.ne']

/-- Concrete omitted-local specialization of the preceding summation.  The
only first-order inputs are exactly the three literal moving-prefix rows at
`D`, `p^k`, and `D p^k`, together with reciprocal one-point bounds. -/
theorem abs_covarianceThirdCentered_divInd_prefix_valuationScore_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) (P : Finset ℕ) (eta : ℕ → ℝ)
    (M D : ℕ) {B K A L : ℝ}
    (hD : 0 < D) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hL : 0 < L)
    (hprime : ∀ p ∈ P, p.Prime)
    (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (heta : ∀ p ∈ P, |eta p| ≤ B)
    (hcop : ∀ p ∈ P, Nat.Coprime D p)
    (hcovD : |mu.covariance
        (fun omega ↦ divInd D (value omega)) pref| ≤
      K / ((D : ℝ) * L))
    (hexpectD : mu.expect (fun omega ↦ divInd D (value omega)) ≤
      A / (D : ℝ))
    (hcovPow : ∀ p ∈ P, ∀ k ∈ positiveExponents M,
      |mu.covariance
          (fun omega ↦ divInd (p ^ k) (value omega)) pref| ≤
        K / (((p ^ k : ℕ) : ℝ) * L))
    (hcovProduct : ∀ p ∈ P, ∀ k ∈ positiveExponents M,
      |mu.covariance
          (fun omega ↦ divInd (D * p ^ k) (value omega)) pref| ≤
        K / (((D : ℝ) * ((p ^ k : ℕ) : ℝ)) * L))
    (hexpectPow : ∀ p ∈ P, ∀ k ∈ positiveExponents M,
      mu.expect (fun omega ↦ divInd (p ^ k) (value omega)) ≤
        A / ((p ^ k : ℕ) : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ divInd D (value omega)) pref
        (fun omega ↦ valuationScore P eta L (value omega))| ≤
      (B * (K * (1 + 2 * A)) / ((D : ℝ) * L ^ 2)) *
        ∑ p ∈ P, ∑ k ∈ positiveExponents M,
          1 / ((p ^ k : ℕ) : ℝ) := by
  apply mu.abs_covarianceThirdCentered_valuationScore_le value
    (fun omega ↦ divInd D (value omega)) pref P eta M
    hB (by exact_mod_cast hD) hL
    hprime hvaluePos hvalueLe heta
  intro p hp k hk
  have hpk : 0 < p ^ k := pow_pos (hprime p hp).pos k
  exact mu.abs_covarianceThirdCentered_divInd_prefix_divInd_le
    value pref hD hpk ((hcop p hp).pow_right k) hK hA hL hcovD
      (hcovPow p hp k hk) (hcovProduct p hp k hk) hexpectD
      (hexpectPow p hp k hk)

/-- First Taylor coefficient of the restored local-prime score.  Unlike the
omitted-prime estimate, the joint row is charged at `p^max(r,k)`.  The
display keeps this exact same-prime ledger visible for the subsequent
`O(1/p)` summation. -/
theorem abs_covarianceThirdCentered_valuation_localScore_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) (p M : ℕ) (eta : ℕ → ℝ)
    {B K A L : ℝ}
    (hp : p.Prime) (hB : 0 ≤ B)
    (hA : 0 ≤ A) (hL : 0 < L)
    (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (heta : |eta p| ≤ B)
    (hcovPow : ∀ r ∈ positiveExponents M,
      |mu.covariance
          (fun omega ↦ divInd (p ^ r) (value omega)) pref| ≤
        K / (((p ^ r : ℕ) : ℝ) * L))
    (hexpectPow : ∀ r ∈ positiveExponents M,
      mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) ≤
        A / ((p ^ r : ℕ) : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ valuation p (value omega)) pref
        (fun omega ↦ valuationScore {p} eta L (value omega))| ≤
      ∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
        (B / L) *
          (K / (((p ^ max r k : ℕ) : ℝ) * L) +
            (A / ((p ^ k : ℕ) : ℝ)) *
              (K / (((p ^ r : ℕ) : ℝ) * L)) +
            (A / ((p ^ r : ℕ) : ℝ)) *
              (K / (((p ^ k : ℕ) : ℝ) * L))) := by
  have hF : (fun omega ↦ valuation p (value omega)) =
      fun omega ↦ ∑ r ∈ positiveExponents M,
        divInd (p ^ r) (value omega) := by
    funext omega
    exact valuation_eq_sum_divInd_of_le hp (hvaluePos omega) (hvalueLe omega)
  have hS : (fun omega ↦ valuationScore {p} eta L (value omega)) =
      fun omega ↦ ∑ k ∈ positiveExponents M,
        (eta p / L) * divInd (p ^ k) (value omega) := by
    funext omega
    have hraw := valuationScore_eq_indicator_sum_of_le
      ({p} : Finset ℕ) eta L (fun q hq ↦ by
        have hqp : q = p := by simpa using hq
        simpa only [hqp] using hp)
        (hvaluePos omega) (hvalueLe omega)
    simpa using hraw
  rw [hF, hS, mu.covarianceThirdCentered_sum_left]
  simp_rw [mu.covarianceThirdCentered_sum_score,
    mu.covarianceThirdCentered_smul_score]
  have hcomponent (r : ℕ) (hr : r ∈ positiveExponents M)
      (k : ℕ) (hk : k ∈ positiveExponents M) :
      |mu.covarianceThirdCentered
          (fun omega ↦ divInd (p ^ r) (value omega)) pref
          (fun omega ↦ divInd (p ^ k) (value omega))| ≤
        K / (((p ^ max r k : ℕ) : ℝ) * L) +
          (A / ((p ^ k : ℕ) : ℝ)) *
            (K / (((p ^ r : ℕ) : ℝ) * L)) +
          (A / ((p ^ r : ℕ) : ℝ)) *
            (K / (((p ^ k : ℕ) : ℝ) * L)) := by
    have hrpos : 0 < p ^ r := pow_pos hp.pos r
    have hkpos : 0 < p ^ k := pow_pos hp.pos k
    have hmaxMem : max r k ∈ positiveExponents M := by
      rw [mem_positiveExponents] at hr hk ⊢
      omega
    have hraw := mu.abs_covarianceThirdCentered_divInd_prefix_divInd_lcm_le
      value pref hrpos hkpos hA (hcovPow r hr) (hcovPow k hk)
        (by simpa only [PrimePowerLcmGeometry.lcm_pow_pow_eq_pow_max] using
          hcovPow (max r k) hmaxMem)
        (hexpectPow r hr) (hexpectPow k hk)
    simpa only [PrimePowerLcmGeometry.lcm_pow_pow_eq_pow_max] using hraw
  calc
    |∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
        eta p / L * mu.covarianceThirdCentered
          (fun omega ↦ divInd (p ^ r) (value omega)) pref
          (fun omega ↦ divInd (p ^ k) (value omega))| ≤
      ∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
        |eta p / L * mu.covarianceThirdCentered
          (fun omega ↦ divInd (p ^ r) (value omega)) pref
          (fun omega ↦ divInd (p ^ k) (value omega))| := by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun r hr ↦ Finset.abs_sum_le_sum_abs _ _)
    _ = ∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
        (|eta p| / L) *
          |mu.covarianceThirdCentered
            (fun omega ↦ divInd (p ^ r) (value omega)) pref
            (fun omega ↦ divInd (p ^ k) (value omega))| := by
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro k hk
      rw [abs_mul, abs_div, abs_of_pos hL]
    _ ≤ ∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
        (B / L) *
          (K / (((p ^ max r k : ℕ) : ℝ) * L) +
            (A / ((p ^ k : ℕ) : ℝ)) *
              (K / (((p ^ r : ℕ) : ℝ) * L)) +
            (A / ((p ^ r : ℕ) : ℝ)) *
              (K / (((p ^ k : ℕ) : ℝ) * L))) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul
        (div_le_div_of_nonneg_right heta hL.le) (hcomponent r hr k hk)
        (abs_nonneg _) (div_nonneg hB hL.le)

/-- Absolute expectation is bounded by expectation of the pointwise
absolute value. -/
theorem abs_expect_le_expect_abs
    (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    |mu.expect F| ≤ mu.expect (fun omega ↦ |F omega|) := by
  unfold expect
  calc
    |∑ omega, mu.mass omega * F omega| ≤
        ∑ omega, |mu.mass omega * F omega| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ omega, mu.mass omega * |F omega| := by
      apply Finset.sum_congr rfl
      intro omega homega
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg omega)]

/-- The pointwise second-order exponential remainder may be integrated
against an arbitrary signed mark. -/
theorem abs_expect_exp_sub_one_sub_score_le
    (mu : FiniteProbability Omega) (H S : Omega → ℝ)
    (hscore : ∀ omega, |S omega| ≤ 1) :
    |mu.expect (fun omega ↦
        H omega * (Real.exp (S omega) - 1 - S omega))| ≤
      mu.expect (fun omega ↦ |H omega| * S omega ^ 2) := by
  calc
    |mu.expect (fun omega ↦
        H omega * (Real.exp (S omega) - 1 - S omega))| ≤
      mu.expect (fun omega ↦
        |H omega * (Real.exp (S omega) - 1 - S omega)|) :=
      mu.abs_expect_le_expect_abs _
    _ ≤ mu.expect (fun omega ↦ |H omega| * S omega ^ 2) := by
      apply mu.expect_mono
      intro omega
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        (Real.abs_exp_sub_one_sub_id_le (hscore omega)) (abs_nonneg _)

/-- A normalized exponential tilt has the expected first-order expansion,
with a completely explicit second-order remainder.  The hypotheses are
literal moments rather than a total-variation estimate, so a marked
`1/d` scale is preserved. -/
theorem abs_exponentialTilt_expect_sub_linearized_le
    (mu : FiniteProbability Omega) (H S : Omega → ℝ)
    {a Rone KH RH CH : ℝ}
    (ha : 0 ≤ a) (hRone : 0 ≤ Rone) (hKH : 0 ≤ KH)
    (hRH : 0 ≤ RH) (hCH : 0 ≤ CH)
    (hscore : ∀ omega, |S omega| ≤ 1)
    (hsmall : 2 * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hH : ∀ omega, |H omega| ≤ KH)
    (hmarkedSq :
      mu.expect (fun omega ↦ |H omega| * S omega ^ 2) ≤ RH)
    (hcov : |mu.covariance H S| ≤ CH) :
    |(mu.exponentialTilt S).expect H -
        (mu.expect H + mu.covariance H S)| ≤
      2 * (RH + CH * a + (KH + CH) * Rone) := by
  let Z := mu.expPartition S
  let m := mu.expect H
  let c := mu.covariance H S
  let s := mu.expect S
  let r := mu.expect (fun omega ↦
    H omega * (Real.exp (S omega) - 1 - S omega))
  let rone := mu.expect (fun omega ↦
    Real.exp (S omega) - 1 - S omega)
  have hdelta := mu.exponentialDeviation_le_two_expect_abs S hscore
  have hdeltaHalf : mu.exponentialDeviation S ≤ (1 : ℝ) / 2 :=
    hdelta.trans ((mul_le_mul_of_nonneg_left habsScore (by norm_num)).trans
      hsmall)
  have hZhalf : (1 : ℝ) / 2 ≤ Z := by
    have hlower := mu.expPartition_lower_bound S
    dsimp only [Z]
    linarith
  have hZpos : 0 < Z := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hZhalf
  have hm : |m| ≤ KH := by
    dsimp only [m]
    exact mu.abs_expect_le_of_abs_le H hKH hH
  have hc : |c| ≤ CH := by simpa only [c] using hcov
  have hs : |s| ≤ a := by
    dsimp only [s]
    exact (mu.abs_expect_le_expect_abs S).trans habsScore
  have hr : |r| ≤ RH := by
    dsimp only [r]
    exact (mu.abs_expect_exp_sub_one_sub_score_le H S hscore).trans
      hmarkedSq
  have hrone : |rone| ≤ Rone := by
    have hraw := mu.abs_expect_exp_sub_one_sub_score_le
      (fun _ ↦ (1 : ℝ)) S hscore
    have hrewrite :
        (fun omega ↦ |(1 : ℝ)| * S omega ^ 2) =
          fun omega ↦ S omega ^ 2 := by
      funext omega
      norm_num
    dsimp only [rone]
    rw [hrewrite] at hraw
    simpa only [one_mul] using hraw.trans hscoreSq
  have hpartition : Z = 1 + s + rone := by
    dsimp only [Z, s, rone]
    unfold expPartition expect
    rw [show (∑ omega, mu.mass omega * Real.exp (S omega)) =
        (∑ omega, mu.mass omega * (1 + S omega +
          (Real.exp (S omega) - 1 - S omega))) by
      apply Finset.sum_congr rfl
      intro omega homega
      ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ omega, mu.mass omega * 1) = 1 by
      simpa only [mul_one] using mu.mass_sum]
  have hnumerator :
      mu.expect (fun omega ↦ H omega * Real.exp (S omega)) =
        m + mu.expect (fun omega ↦ H omega * S omega) + r := by
    dsimp only [m, r]
    unfold expect
    rw [show (∑ omega, mu.mass omega *
        (H omega * Real.exp (S omega))) =
      ∑ omega, mu.mass omega *
        (H omega + H omega * S omega +
          H omega * (Real.exp (S omega) - 1 - S omega)) by
      apply Finset.sum_congr rfl
      intro omega homega
      ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcovIdentity :
      mu.expect (fun omega ↦ H omega * S omega) = c + m * s := by
    dsimp only [c, m, s]
    unfold covariance
    ring
  have hdiffIdentity :
      mu.expect (fun omega ↦ H omega * Real.exp (S omega)) -
          (m + c) * Z = r - c * s - (m + c) * rone := by
    rw [hnumerator, hcovIdentity, hpartition]
    ring
  rw [mu.exponentialTilt_expect_eq H S]
  change |mu.expect (fun omega ↦ H omega * Real.exp (S omega)) / Z -
      (m + c)| ≤ _
  rw [show mu.expect (fun omega ↦ H omega * Real.exp (S omega)) / Z -
      (m + c) =
      (mu.expect (fun omega ↦ H omega * Real.exp (S omega)) -
        (m + c) * Z) / Z by field_simp]
  rw [hdiffIdentity, abs_div, abs_of_pos hZpos]
  have hnum : |r - c * s - (m + c) * rone| ≤
      RH + CH * a + (KH + CH) * Rone := by
    calc
      |r - c * s - (m + c) * rone| ≤
          |r| + |c| * |s| + (|m| + |c|) * |rone| := by
        calc
          |r - c * s - (m + c) * rone| ≤
              |r - c * s| + |(m + c) * rone| := abs_sub _ _
          _ ≤ (|r| + |c * s|) + |(m + c) * rone| :=
            add_le_add (abs_sub _ _) le_rfl
          _ ≤ |r| + |c| * |s| + (|m| + |c|) * |rone| := by
            rw [abs_mul, abs_mul]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg rone))
      _ ≤ RH + CH * a + (KH + CH) * Rone := by
        exact add_le_add
          (add_le_add hr (mul_le_mul hc hs (abs_nonneg s) hCH))
          (mul_le_mul (add_le_add hm hc) hrone (abs_nonneg rone)
            (add_nonneg hKH hCH))
  have htarget0 : 0 ≤ RH + CH * a + (KH + CH) * Rone := by positivity
  calc
    |r - c * s - (m + c) * rone| / Z ≤
      (RH + CH * a + (KH + CH) * Rone) / Z :=
        div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (RH + CH * a + (KH + CH) * Rone) / ((1 : ℝ) / 2) := by
      exact div_le_div_of_nonneg_left htarget0 (by norm_num) hZhalf
    _ = 2 * (RH + CH * a + (KH + CH) * Rone) := by ring

/-- Mean-sensitive form of the normalized exponential Taylor estimate.

The older wrapper above obtains the mean bound from a pointwise envelope
`|H| \le KH`.  That is inappropriate for a valuation mark: its pointwise
envelope grows with the physical endpoint, while its actual mean retains the
required reciprocal-prime scale.  This version takes the literal bound on
`|E H|` as input.  The proof is otherwise the same exact finite identity. -/
theorem abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound
    (mu : FiniteProbability Omega) (H S : Omega → ℝ)
    {a Rone MH RH CH : ℝ}
    (ha : 0 ≤ a) (hRone : 0 ≤ Rone)
    (hMH : 0 ≤ MH) (hRH : 0 ≤ RH) (hCH : 0 ≤ CH)
    (hscore : ∀ omega, |S omega| ≤ 1)
    (hsmall : 2 * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hmean : |mu.expect H| ≤ MH)
    (hmarkedSq :
      mu.expect (fun omega ↦ |H omega| * S omega ^ 2) ≤ RH)
    (hcov : |mu.covariance H S| ≤ CH) :
    |(mu.exponentialTilt S).expect H -
        (mu.expect H + mu.covariance H S)| ≤
      2 * (RH + CH * a + (MH + CH) * Rone) := by
  let Z := mu.expPartition S
  let m := mu.expect H
  let c := mu.covariance H S
  let s := mu.expect S
  let r := mu.expect (fun omega ↦
    H omega * (Real.exp (S omega) - 1 - S omega))
  let rone := mu.expect (fun omega ↦
    Real.exp (S omega) - 1 - S omega)
  have hdelta := mu.exponentialDeviation_le_two_expect_abs S hscore
  have hdeltaHalf : mu.exponentialDeviation S ≤ (1 : ℝ) / 2 :=
    hdelta.trans ((mul_le_mul_of_nonneg_left habsScore (by norm_num)).trans
      hsmall)
  have hZhalf : (1 : ℝ) / 2 ≤ Z := by
    have hlower := mu.expPartition_lower_bound S
    dsimp only [Z]
    linarith
  have hZpos : 0 < Z := (by norm_num : (0 : ℝ) < 1 / 2).trans_le hZhalf
  have hm : |m| ≤ MH := by simpa only [m] using hmean
  have hc : |c| ≤ CH := by simpa only [c] using hcov
  have hs : |s| ≤ a := by
    dsimp only [s]
    exact (mu.abs_expect_le_expect_abs S).trans habsScore
  have hr : |r| ≤ RH := by
    dsimp only [r]
    exact (mu.abs_expect_exp_sub_one_sub_score_le H S hscore).trans
      hmarkedSq
  have hrone : |rone| ≤ Rone := by
    have hraw := mu.abs_expect_exp_sub_one_sub_score_le
      (fun _ ↦ (1 : ℝ)) S hscore
    have hrewrite :
        (fun omega ↦ |(1 : ℝ)| * S omega ^ 2) =
          fun omega ↦ S omega ^ 2 := by
      funext omega
      norm_num
    dsimp only [rone]
    rw [hrewrite] at hraw
    simpa only [one_mul] using hraw.trans hscoreSq
  have hpartition : Z = 1 + s + rone := by
    dsimp only [Z, s, rone]
    unfold expPartition expect
    rw [show (∑ omega, mu.mass omega * Real.exp (S omega)) =
        (∑ omega, mu.mass omega * (1 + S omega +
          (Real.exp (S omega) - 1 - S omega))) by
      apply Finset.sum_congr rfl
      intro omega homega
      ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    rw [show (∑ omega, mu.mass omega * 1) = 1 by
      simpa only [mul_one] using mu.mass_sum]
  have hnumerator :
      mu.expect (fun omega ↦ H omega * Real.exp (S omega)) =
        m + mu.expect (fun omega ↦ H omega * S omega) + r := by
    dsimp only [m, r]
    unfold expect
    rw [show (∑ omega, mu.mass omega *
        (H omega * Real.exp (S omega))) =
      ∑ omega, mu.mass omega *
        (H omega + H omega * S omega +
          H omega * (Real.exp (S omega) - 1 - S omega)) by
      apply Finset.sum_congr rfl
      intro omega homega
      ring]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcovIdentity :
      mu.expect (fun omega ↦ H omega * S omega) = c + m * s := by
    dsimp only [c, m, s]
    unfold covariance
    ring
  have hdiffIdentity :
      mu.expect (fun omega ↦ H omega * Real.exp (S omega)) -
          (m + c) * Z = r - c * s - (m + c) * rone := by
    rw [hnumerator, hcovIdentity, hpartition]
    ring
  rw [mu.exponentialTilt_expect_eq H S]
  change |mu.expect (fun omega ↦ H omega * Real.exp (S omega)) / Z -
      (m + c)| ≤ _
  rw [show mu.expect (fun omega ↦ H omega * Real.exp (S omega)) / Z -
      (m + c) =
      (mu.expect (fun omega ↦ H omega * Real.exp (S omega)) -
        (m + c) * Z) / Z by field_simp]
  rw [hdiffIdentity, abs_div, abs_of_pos hZpos]
  have hnum : |r - c * s - (m + c) * rone| ≤
      RH + CH * a + (MH + CH) * Rone := by
    calc
      |r - c * s - (m + c) * rone| ≤
          |r| + |c| * |s| + (|m| + |c|) * |rone| := by
        calc
          |r - c * s - (m + c) * rone| ≤
              |r - c * s| + |(m + c) * rone| := abs_sub _ _
          _ ≤ (|r| + |c * s|) + |(m + c) * rone| :=
            add_le_add (abs_sub _ _) le_rfl
          _ ≤ |r| + |c| * |s| + (|m| + |c|) * |rone| := by
            rw [abs_mul, abs_mul]
            exact add_le_add le_rfl
              (mul_le_mul_of_nonneg_right (abs_add_le _ _) (abs_nonneg rone))
      _ ≤ RH + CH * a + (MH + CH) * Rone := by
        exact add_le_add
          (add_le_add hr (mul_le_mul hc hs (abs_nonneg s) hCH))
          (mul_le_mul (add_le_add hm hc) hrone (abs_nonneg rone)
            (add_nonneg hMH hCH))
  have htarget0 : 0 ≤ RH + CH * a + (MH + CH) * Rone := by positivity
  calc
    |r - c * s - (m + c) * rone| / Z ≤
      (RH + CH * a + (MH + CH) * Rone) / Z :=
        div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (RH + CH * a + (MH + CH) * Rone) / ((1 : ℝ) / 2) := by
      exact div_le_div_of_nonneg_left htarget0 (by norm_num) hZhalf
    _ = 2 * (RH + CH * a + (MH + CH) * Rone) := by ring

/-- Second-order Taylor attachment for a centered covariance.  The leading
correction is exactly `covarianceThirdCentered`; every other displayed term
is quadratic in the score moments.  This is the finite probabilistic core of
the paper's tilted Stieltjes calculation. -/
theorem abs_exponentialTilt_covariance_le_of_centeredTaylor
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ)
    {a Rone KF KG RF RG RFG CF CG CFG Czero Cthird : ℝ}
    (ha : 0 ≤ a) (hRone : 0 ≤ Rone)
    (hKF : 0 ≤ KF) (hKG : 0 ≤ KG)
    (hRF : 0 ≤ RF) (hRG : 0 ≤ RG) (hRFG : 0 ≤ RFG)
    (hCF : 0 ≤ CF) (hCG : 0 ≤ CG) (hCFG : 0 ≤ CFG)
    (hscore : ∀ omega, |S omega| ≤ 1)
    (hsmall : 2 * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hF : ∀ omega, |F omega| ≤ KF)
    (hG : ∀ omega, |G omega| ≤ KG)
    (hmarkedSqF :
      mu.expect (fun omega ↦ |F omega| * S omega ^ 2) ≤ RF)
    (hmarkedSqG :
      mu.expect (fun omega ↦ |G omega| * S omega ^ 2) ≤ RG)
    (hmarkedSqFG :
      mu.expect (fun omega ↦ |F omega * G omega| * S omega ^ 2) ≤ RFG)
    (hcovF : |mu.covariance F S| ≤ CF)
    (hcovG : |mu.covariance G S| ≤ CG)
    (hcovFG : |mu.covariance (fun omega ↦ F omega * G omega) S| ≤ CFG)
    (hbase : |mu.covariance F G| ≤ Czero)
    (hthird : |mu.covarianceThirdCentered F G S| ≤ Cthird) :
    let EF := 2 * (RF + CF * a + (KF + CF) * Rone)
    let EG := 2 * (RG + CG * a + (KG + CG) * Rone)
    let EFG := 2 * (RFG + CFG * a + (KF * KG + CFG) * Rone)
    |(mu.exponentialTilt S).covariance F G| ≤
      Czero + Cthird + CF * CG + EFG +
        (KF + CF) * EG + (KG + CG) * EF + EF * EG := by
  dsimp only
  let EF := 2 * (RF + CF * a + (KF + CF) * Rone)
  let EG := 2 * (RG + CG * a + (KG + CG) * Rone)
  let EFG := 2 * (RFG + CFG * a + (KF * KG + CFG) * Rone)
  let mF := mu.expect F
  let mG := mu.expect G
  let cF := mu.covariance F S
  let cG := mu.covariance G S
  let eF := (mu.exponentialTilt S).expect F - (mF + cF)
  let eG := (mu.exponentialTilt S).expect G - (mG + cG)
  let eFG := (mu.exponentialTilt S).expect
      (fun omega ↦ F omega * G omega) -
    (mu.expect (fun omega ↦ F omega * G omega) +
      mu.covariance (fun omega ↦ F omega * G omega) S)
  have hFG (omega : Omega) : |F omega * G omega| ≤ KF * KG := by
    rw [abs_mul]
    exact mul_le_mul (hF omega) (hG omega) (abs_nonneg _) hKF
  have hEF : |eF| ≤ EF := by
    dsimp only [eF, mF, cF, EF]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le
      F S ha hRone hKF hRF hCF hscore hsmall habsScore hscoreSq hF
        hmarkedSqF hcovF
  have hEG : |eG| ≤ EG := by
    dsimp only [eG, mG, cG, EG]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le
      G S ha hRone hKG hRG hCG hscore hsmall habsScore hscoreSq hG
        hmarkedSqG hcovG
  have hEFG : |eFG| ≤ EFG := by
    dsimp only [eFG, EFG]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le
      (fun omega ↦ F omega * G omega) S ha hRone
        (mul_nonneg hKF hKG) hRFG hCFG hscore hsmall habsScore hscoreSq
        hFG hmarkedSqFG hcovFG
  have hmF : |mF| ≤ KF := by
    dsimp only [mF]
    exact mu.abs_expect_le_of_abs_le F hKF hF
  have hmG : |mG| ≤ KG := by
    dsimp only [mG]
    exact mu.abs_expect_le_of_abs_le G hKG hG
  have hcF : |cF| ≤ CF := by simpa only [cF] using hcovF
  have hcG : |cG| ≤ CG := by simpa only [cG] using hcovG
  have htiltF : (mu.exponentialTilt S).expect F = mF + cF + eF := by
    dsimp only [eF]
    ring
  have htiltG : (mu.exponentialTilt S).expect G = mG + cG + eG := by
    dsimp only [eG]
    ring
  have htiltFG : (mu.exponentialTilt S).expect
      (fun omega ↦ F omega * G omega) =
      mu.expect (fun omega ↦ F omega * G omega) +
        mu.covariance (fun omega ↦ F omega * G omega) S + eFG := by
    dsimp only [eFG]
    ring
  have hexpand :
      (mu.exponentialTilt S).covariance F G =
        mu.covariance F G + mu.covarianceThirdCentered F G S -
          cF * cG + eFG - (mF + cF) * eG -
          (mG + cG) * eF - eF * eG := by
    unfold covariance covarianceThirdCentered
    rw [htiltFG, htiltF, htiltG]
    dsimp only [mF, mG, cF, cG]
    ring
  have hEF0 : 0 ≤ EF := by dsimp only [EF]; positivity
  have hEG0 : 0 ≤ EG := by dsimp only [EG]; positivity
  have hEFG0 : 0 ≤ EFG := by dsimp only [EFG]; positivity
  rw [hexpand]
  let x0 := mu.covariance F G
  let x1 := mu.covarianceThirdCentered F G S
  let x2 := -(cF * cG)
  let x3 := eFG
  let x4 := -((mF + cF) * eG)
  let x5 := -((mG + cG) * eF)
  let x6 := -(eF * eG)
  have hrepack :
      mu.covariance F G + mu.covarianceThirdCentered F G S -
          cF * cG + eFG - (mF + cF) * eG -
          (mG + cG) * eF - eF * eG =
        x0 + x1 + x2 + x3 + x4 + x5 + x6 := by
    dsimp only [x0, x1, x2, x3, x4, x5, x6]
    ring
  rw [hrepack]
  have htri : |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
      |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by
    calc
      |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
          |x0| + |x1 + x2 + x3 + x4 + x5 + x6| := by
        convert abs_add_le x0 (x1 + x2 + x3 + x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + |x2 + x3 + x4 + x5 + x6|) :=
        by
          gcongr
          convert abs_add_le x1 (x2 + x3 + x4 + x5 + x6) using 1
          ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + |x3 + x4 + x5 + x6|)) :=
        by
          gcongr
          convert abs_add_le x2 (x3 + x4 + x5 + x6) using 1
          ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| + |x4 + x5 + x6|))) :=
        by
          gcongr
          convert abs_add_le x3 (x4 + x5 + x6) using 1
          ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| +
          (|x4| + |x5 + x6|)))) :=
        by
          gcongr
          convert abs_add_le x4 (x5 + x6) using 1
          ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| +
          (|x4| + (|x5| + |x6|))))) :=
        by
          gcongr
          exact abs_add_le x5 x6
      _ = |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by ring
  have htriExpanded :
      |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| =
      |mu.covariance F G| + |mu.covarianceThirdCentered F G S| +
        |cF| * |cG| + |eFG| + (|mF + cF| * |eG|) +
        (|mG + cG| * |eF|) + |eF| * |eG| := by
    dsimp only [x0, x1, x2, x3, x4, x5, x6]
    simp only [abs_neg, abs_mul]
  have hcc : |cF| * |cG| ≤ CF * CG :=
    mul_le_mul hcF hcG (abs_nonneg cG) hCF
  have hmFeG : (|mF| + |cF|) * |eG| ≤ (KF + CF) * EG :=
    mul_le_mul (add_le_add hmF hcF) hEG (abs_nonneg eG)
      (add_nonneg hKF hCF)
  have hmGeF : (|mG| + |cG|) * |eF| ≤ (KG + CG) * EF :=
    mul_le_mul (add_le_add hmG hcG) hEF (abs_nonneg eF)
      (add_nonneg hKG hCG)
  have heFeG : |eF| * |eG| ≤ EF * EG :=
    mul_le_mul hEF hEG (abs_nonneg eG) hEF0
  calc
    |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
      |mu.covariance F G| + |mu.covarianceThirdCentered F G S| +
        |cF| * |cG| + |eFG| + (|mF| + |cF|) * |eG| +
        (|mG| + |cG|) * |eF| + |eF| * |eG| := by
      calc
        _ ≤ |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := htri
        _ = |mu.covariance F G| +
            |mu.covarianceThirdCentered F G S| +
            |cF| * |cG| + |eFG| + |mF + cF| * |eG| +
            |mG + cG| * |eF| + |eF| * |eG| := htriExpanded
        _ ≤ |mu.covariance F G| +
            |mu.covarianceThirdCentered F G S| +
            |cF| * |cG| + |eFG| + (|mF| + |cF|) * |eG| +
            (|mG| + |cG|) * |eF| + |eF| * |eG| := by
          have h4 := mul_le_mul_of_nonneg_right (abs_add_le mF cF)
            (abs_nonneg eG)
          have h5 := mul_le_mul_of_nonneg_right (abs_add_le mG cG)
            (abs_nonneg eF)
          linarith
    _ ≤ Czero + Cthird + CF * CG + EFG +
        (KF + CF) * EG + (KG + CG) * EF + EF * EG := by
      linarith

/-- Mean-sensitive covariance Taylor estimate.

All three zeroth-order sizes are bounds for the actual expectations, not
pointwise suprema.  Consequently this theorem can be applied directly to
`F = v_p`: the reciprocal bound for `E v_p` is retained throughout the
normalizing-denominator remainder. -/
theorem abs_exponentialTilt_covariance_le_of_centeredTaylor_expect_bounds
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ)
    {a Rone MF MG MFG RF RG RFG CF CG CFG Czero Cthird : ℝ}
    (ha : 0 ≤ a) (hRone : 0 ≤ Rone)
    (hMF : 0 ≤ MF) (hMG : 0 ≤ MG) (hMFG : 0 ≤ MFG)
    (hRF : 0 ≤ RF) (hRG : 0 ≤ RG) (hRFG : 0 ≤ RFG)
    (hCF : 0 ≤ CF) (hCG : 0 ≤ CG) (hCFG : 0 ≤ CFG)
    (hscore : ∀ omega, |S omega| ≤ 1)
    (hsmall : 2 * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hmeanF : |mu.expect F| ≤ MF)
    (hmeanG : |mu.expect G| ≤ MG)
    (hmeanFG : |mu.expect (fun omega ↦ F omega * G omega)| ≤ MFG)
    (hmarkedSqF :
      mu.expect (fun omega ↦ |F omega| * S omega ^ 2) ≤ RF)
    (hmarkedSqG :
      mu.expect (fun omega ↦ |G omega| * S omega ^ 2) ≤ RG)
    (hmarkedSqFG :
      mu.expect (fun omega ↦ |F omega * G omega| * S omega ^ 2) ≤ RFG)
    (hcovF : |mu.covariance F S| ≤ CF)
    (hcovG : |mu.covariance G S| ≤ CG)
    (hcovFG : |mu.covariance (fun omega ↦ F omega * G omega) S| ≤ CFG)
    (hbase : |mu.covariance F G| ≤ Czero)
    (hthird : |mu.covarianceThirdCentered F G S| ≤ Cthird) :
    let EF := 2 * (RF + CF * a + (MF + CF) * Rone)
    let EG := 2 * (RG + CG * a + (MG + CG) * Rone)
    let EFG := 2 * (RFG + CFG * a + (MFG + CFG) * Rone)
    |(mu.exponentialTilt S).covariance F G| ≤
      Czero + Cthird + CF * CG + EFG +
        (MF + CF) * EG + (MG + CG) * EF + EF * EG := by
  dsimp only
  let EF := 2 * (RF + CF * a + (MF + CF) * Rone)
  let EG := 2 * (RG + CG * a + (MG + CG) * Rone)
  let EFG := 2 * (RFG + CFG * a + (MFG + CFG) * Rone)
  let mF := mu.expect F
  let mG := mu.expect G
  let cF := mu.covariance F S
  let cG := mu.covariance G S
  let eF := (mu.exponentialTilt S).expect F - (mF + cF)
  let eG := (mu.exponentialTilt S).expect G - (mG + cG)
  let eFG := (mu.exponentialTilt S).expect
      (fun omega ↦ F omega * G omega) -
    (mu.expect (fun omega ↦ F omega * G omega) +
      mu.covariance (fun omega ↦ F omega * G omega) S)
  have hEF : |eF| ≤ EF := by
    dsimp only [eF, mF, cF, EF]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound
      F S ha hRone hMF hRF hCF hscore hsmall habsScore hscoreSq
        hmeanF hmarkedSqF hcovF
  have hEG : |eG| ≤ EG := by
    dsimp only [eG, mG, cG, EG]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound
      G S ha hRone hMG hRG hCG hscore hsmall habsScore hscoreSq
        hmeanG hmarkedSqG hcovG
  have hEFG : |eFG| ≤ EFG := by
    dsimp only [eFG, EFG]
    exact mu.abs_exponentialTilt_expect_sub_linearized_le_of_expect_bound
      (fun omega ↦ F omega * G omega) S ha hRone hMFG hRFG hCFG
        hscore hsmall habsScore hscoreSq hmeanFG hmarkedSqFG hcovFG
  have hmF : |mF| ≤ MF := by simpa only [mF] using hmeanF
  have hmG : |mG| ≤ MG := by simpa only [mG] using hmeanG
  have hcF : |cF| ≤ CF := by simpa only [cF] using hcovF
  have hcG : |cG| ≤ CG := by simpa only [cG] using hcovG
  have htiltF : (mu.exponentialTilt S).expect F = mF + cF + eF := by
    dsimp only [eF]
    ring
  have htiltG : (mu.exponentialTilt S).expect G = mG + cG + eG := by
    dsimp only [eG]
    ring
  have htiltFG : (mu.exponentialTilt S).expect
      (fun omega ↦ F omega * G omega) =
      mu.expect (fun omega ↦ F omega * G omega) +
        mu.covariance (fun omega ↦ F omega * G omega) S + eFG := by
    dsimp only [eFG]
    ring
  have hexpand :
      (mu.exponentialTilt S).covariance F G =
        mu.covariance F G + mu.covarianceThirdCentered F G S -
          cF * cG + eFG - (mF + cF) * eG -
          (mG + cG) * eF - eF * eG := by
    unfold covariance covarianceThirdCentered
    rw [htiltFG, htiltF, htiltG]
    dsimp only [mF, mG, cF, cG]
    ring
  have hEF0 : 0 ≤ EF := by dsimp only [EF]; positivity
  have hEG0 : 0 ≤ EG := by dsimp only [EG]; positivity
  have hEFG0 : 0 ≤ EFG := by dsimp only [EFG]; positivity
  rw [hexpand]
  let x0 := mu.covariance F G
  let x1 := mu.covarianceThirdCentered F G S
  let x2 := -(cF * cG)
  let x3 := eFG
  let x4 := -((mF + cF) * eG)
  let x5 := -((mG + cG) * eF)
  let x6 := -(eF * eG)
  have hrepack :
      mu.covariance F G + mu.covarianceThirdCentered F G S -
          cF * cG + eFG - (mF + cF) * eG -
          (mG + cG) * eF - eF * eG =
        x0 + x1 + x2 + x3 + x4 + x5 + x6 := by
    dsimp only [x0, x1, x2, x3, x4, x5, x6]
    ring
  rw [hrepack]
  have htri : |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
      |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by
    calc
      |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
          |x0| + |x1 + x2 + x3 + x4 + x5 + x6| := by
        convert abs_add_le x0 (x1 + x2 + x3 + x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + |x2 + x3 + x4 + x5 + x6|) := by
        gcongr
        convert abs_add_le x1 (x2 + x3 + x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + |x3 + x4 + x5 + x6|)) := by
        gcongr
        convert abs_add_le x2 (x3 + x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| + |x4 + x5 + x6|))) := by
        gcongr
        convert abs_add_le x3 (x4 + x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| +
          (|x4| + |x5 + x6|)))) := by
        gcongr
        convert abs_add_le x4 (x5 + x6) using 1
        ring_nf
      _ ≤ |x0| + (|x1| + (|x2| + (|x3| +
          (|x4| + (|x5| + |x6|))))) := by
        gcongr
        exact abs_add_le x5 x6
      _ = |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := by ring
  have htriExpanded :
      |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| =
      |mu.covariance F G| + |mu.covarianceThirdCentered F G S| +
        |cF| * |cG| + |eFG| + |mF + cF| * |eG| +
        |mG + cG| * |eF| + |eF| * |eG| := by
    dsimp only [x0, x1, x2, x3, x4, x5, x6]
    simp only [abs_neg, abs_mul]
  have hcc : |cF| * |cG| ≤ CF * CG :=
    mul_le_mul hcF hcG (abs_nonneg cG) hCF
  have hmFeG : (|mF| + |cF|) * |eG| ≤ (MF + CF) * EG :=
    mul_le_mul (add_le_add hmF hcF) hEG (abs_nonneg eG)
      (add_nonneg hMF hCF)
  have hmGeF : (|mG| + |cG|) * |eF| ≤ (MG + CG) * EF :=
    mul_le_mul (add_le_add hmG hcG) hEF (abs_nonneg eF)
      (add_nonneg hMG hCG)
  have heFeG : |eF| * |eG| ≤ EF * EG :=
    mul_le_mul hEF hEG (abs_nonneg eG) hEF0
  calc
    |x0 + x1 + x2 + x3 + x4 + x5 + x6| ≤
      |mu.covariance F G| + |mu.covarianceThirdCentered F G S| +
        |cF| * |cG| + |eFG| + (|mF| + |cF|) * |eG| +
        (|mG| + |cG|) * |eF| + |eF| * |eG| := by
      calc
        _ ≤ |x0| + |x1| + |x2| + |x3| + |x4| + |x5| + |x6| := htri
        _ = |mu.covariance F G| +
            |mu.covarianceThirdCentered F G S| +
            |cF| * |cG| + |eFG| + |mF + cF| * |eG| +
            |mG + cG| * |eF| + |eF| * |eG| := htriExpanded
        _ ≤ |mu.covariance F G| +
            |mu.covarianceThirdCentered F G S| +
            |cF| * |cG| + |eFG| + (|mF| + |cF|) * |eG| +
            (|mG| + |cG|) * |eF| + |eF| * |eG| := by
          have h4 := mul_le_mul_of_nonneg_right (abs_add_le mF cF)
            (abs_nonneg eG)
          have h5 := mul_le_mul_of_nonneg_right (abs_add_le mG cG)
            (abs_nonneg eF)
          linarith
    _ ≤ Czero + Cthird + CF * CG + EFG +
        (MF + CF) * EG + (MG + CG) * EF + EF * EG := by
      linarith

/-- Covariance is controlled by one marked absolute first moment and the
two marginal absolute first moments. -/
theorem abs_covariance_le_expect_abs_mul_add
    (mu : FiniteProbability Omega) (F S : Omega → ℝ) :
    |mu.covariance F S| ≤
      mu.expect (fun omega ↦ |F omega| * |S omega|) +
        mu.expect (fun omega ↦ |F omega|) *
          mu.expect (fun omega ↦ |S omega|) := by
  unfold covariance
  calc
    |mu.expect (fun omega ↦ F omega * S omega) -
        mu.expect F * mu.expect S| ≤
      |mu.expect (fun omega ↦ F omega * S omega)| +
        |mu.expect F * mu.expect S| := abs_sub _ _
    _ ≤ mu.expect (fun omega ↦ |F omega * S omega|) +
        (mu.expect (fun omega ↦ |F omega|) *
          mu.expect (fun omega ↦ |S omega|)) := by
      exact add_le_add (mu.abs_expect_le_expect_abs _)
        (by
          rw [abs_mul]
          exact mul_le_mul (mu.abs_expect_le_expect_abs F)
            (mu.abs_expect_le_expect_abs S) (abs_nonneg _)
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _))
    _ = mu.expect (fun omega ↦ |F omega| * |S omega|) +
        mu.expect (fun omega ↦ |F omega|) *
          mu.expect (fun omega ↦ |S omega|) := by
      congr 2
      funext omega
      exact abs_mul _ _

/-- Ready-to-use Taylor estimate for a nonnegative marked statistic and a
prefix indicator.  Every occurrence of the marked statistic is charged
through its reciprocal first or second moment; no pointwise envelope enters
the bound. -/
theorem abs_exponentialTilt_covariance_nonneg_prefix_le_of_moments
    (mu : FiniteProbability Omega) (F G S : Omega → ℝ)
    {a Rone MF RFone RF Czero Cthird : ℝ}
    (ha : 0 ≤ a) (hRone : 0 ≤ Rone)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone) (hRF : 0 ≤ RF)
    (hscore : ∀ omega, |S omega| ≤ 1)
    (hsmall : 2 * a ≤ (1 : ℝ) / 2)
    (habsScore : mu.expect (fun omega ↦ |S omega|) ≤ a)
    (hscoreSq : mu.expect (fun omega ↦ S omega ^ 2) ≤ Rone)
    (hF0 : ∀ omega, 0 ≤ F omega)
    (hmeanF : mu.expect F ≤ MF)
    (hG0 : ∀ omega, 0 ≤ G omega)
    (hG1 : ∀ omega, G omega ≤ 1)
    (hmarkedFirst :
      mu.expect (fun omega ↦ |F omega| * |S omega|) ≤ RFone)
    (hmarkedSqF :
      mu.expect (fun omega ↦ |F omega| * S omega ^ 2) ≤ RF)
    (hbase : |mu.covariance F G| ≤ Czero)
    (hthird : |mu.covarianceThirdCentered F G S| ≤ Cthird) :
    let CF := RFone + MF * a
    let CG := 2 * a
    let EF := 2 * (RF + CF * a + (MF + CF) * Rone)
    let EG := 2 * (Rone + CG * a + (1 + CG) * Rone)
    let EFG := 2 * (RF + CF * a + (MF + CF) * Rone)
    |(mu.exponentialTilt S).covariance F G| ≤
      Czero + Cthird + CF * CG + EFG +
        (MF + CF) * EG + (1 + CG) * EF + EF * EG := by
  dsimp only
  let CF : ℝ := RFone + MF * a
  let CG : ℝ := 2 * a
  have hCF : 0 ≤ CF := by dsimp only [CF]; positivity
  have hCG : 0 ≤ CG := by dsimp only [CG]; positivity
  have hmeanF0 : 0 ≤ mu.expect F := mu.expect_nonneg F hF0
  have hmeanFabs : |mu.expect F| ≤ MF := by
    rw [abs_of_nonneg hmeanF0]
    exact hmeanF
  have hmeanG0 : 0 ≤ mu.expect G := mu.expect_nonneg G hG0
  have hmeanGle : mu.expect G ≤ 1 := by
    calc
      mu.expect G ≤ mu.expect (fun _ ↦ (1 : ℝ)) :=
        mu.expect_mono G _ hG1
      _ = 1 := by
        unfold expect
        rw [← Finset.sum_mul, mu.mass_sum, one_mul]
  have hmeanGabs : |mu.expect G| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hmeanG0]
    exact hmeanGle
  have hFG0 : ∀ omega, 0 ≤ F omega * G omega := fun omega ↦
    mul_nonneg (hF0 omega) (hG0 omega)
  have hFGle : ∀ omega, F omega * G omega ≤ F omega := by
    intro omega
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hG1 omega) (hF0 omega)
  have hmeanFG0 : 0 ≤ mu.expect (fun omega ↦ F omega * G omega) :=
    mu.expect_nonneg _ hFG0
  have hmeanFGle : mu.expect (fun omega ↦ F omega * G omega) ≤ MF :=
    (mu.expect_mono _ F hFGle).trans hmeanF
  have hmeanFGabs :
      |mu.expect (fun omega ↦ F omega * G omega)| ≤ MF := by
    rw [abs_of_nonneg hmeanFG0]
    exact hmeanFGle
  have hFabsPoint : (fun omega ↦ |F omega|) = F := by
    funext omega
    exact abs_of_nonneg (hF0 omega)
  have hGabsPoint : (fun omega ↦ |G omega|) = G := by
    funext omega
    exact abs_of_nonneg (hG0 omega)
  have hcovF : |mu.covariance F S| ≤ CF := by
    have hraw := mu.abs_covariance_le_expect_abs_mul_add F S
    rw [hFabsPoint] at hraw
    calc
      |mu.covariance F S| ≤
          mu.expect (fun omega ↦ |F omega| * |S omega|) +
            mu.expect F * mu.expect (fun omega ↦ |S omega|) := hraw
      _ ≤ RFone + MF * a := by
        exact add_le_add hmarkedFirst
          (mul_le_mul hmeanF habsScore
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) hMF)
      _ = CF := by rfl
  have hmarkedG : mu.expect (fun omega ↦ |G omega| * |S omega|) ≤ a := by
    calc
      mu.expect (fun omega ↦ |G omega| * |S omega|) ≤
          mu.expect (fun omega ↦ |S omega|) := by
        apply mu.expect_mono
        intro omega
        rw [abs_of_nonneg (hG0 omega)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hG1 omega) (abs_nonneg (S omega))
      _ ≤ a := habsScore
  have hcovG : |mu.covariance G S| ≤ CG := by
    have hraw := mu.abs_covariance_le_expect_abs_mul_add G S
    rw [hGabsPoint] at hraw
    calc
      |mu.covariance G S| ≤
          mu.expect (fun omega ↦ |G omega| * |S omega|) +
            mu.expect G * mu.expect (fun omega ↦ |S omega|) := hraw
      _ ≤ a + 1 * a := by
        exact add_le_add hmarkedG
          (mul_le_mul hmeanGle habsScore
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) zero_le_one)
      _ = CG := by dsimp only [CG]; ring
  have hmarkedFG :
      mu.expect (fun omega ↦ |F omega * G omega| * |S omega|) ≤ RFone := by
    calc
      mu.expect (fun omega ↦ |F omega * G omega| * |S omega|) ≤
          mu.expect (fun omega ↦ |F omega| * |S omega|) := by
        apply mu.expect_mono
        intro omega
        rw [abs_mul, abs_of_nonneg (hG0 omega)]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hG1 omega) (abs_nonneg (F omega)))
          (abs_nonneg (S omega))
      _ ≤ RFone := hmarkedFirst
  have hcovFG :
      |mu.covariance (fun omega ↦ F omega * G omega) S| ≤ CF := by
    have hraw := mu.abs_covariance_le_expect_abs_mul_add
      (fun omega ↦ F omega * G omega) S
    calc
      |mu.covariance (fun omega ↦ F omega * G omega) S| ≤
          mu.expect (fun omega ↦ |F omega * G omega| * |S omega|) +
            mu.expect (fun omega ↦ |F omega * G omega|) *
              mu.expect (fun omega ↦ |S omega|) := hraw
      _ ≤ RFone + MF * a := by
        rw [show (fun omega ↦ |F omega * G omega|) =
            fun omega ↦ F omega * G omega by
          funext omega
          exact abs_of_nonneg (hFG0 omega)]
        exact add_le_add hmarkedFG
          (mul_le_mul hmeanFGle habsScore
            (mu.expect_nonneg _ fun omega ↦ abs_nonneg _) hMF)
      _ = CF := by rfl
  have hmarkedSqG :
      mu.expect (fun omega ↦ |G omega| * S omega ^ 2) ≤ Rone := by
    calc
      mu.expect (fun omega ↦ |G omega| * S omega ^ 2) ≤
          mu.expect (fun omega ↦ S omega ^ 2) := by
        apply mu.expect_mono
        intro omega
        rw [abs_of_nonneg (hG0 omega)]
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right (hG1 omega) (sq_nonneg (S omega))
      _ ≤ Rone := hscoreSq
  have hmarkedSqFG :
      mu.expect (fun omega ↦ |F omega * G omega| * S omega ^ 2) ≤ RF := by
    calc
      mu.expect (fun omega ↦ |F omega * G omega| * S omega ^ 2) ≤
          mu.expect (fun omega ↦ |F omega| * S omega ^ 2) := by
        apply mu.expect_mono
        intro omega
        rw [abs_mul, abs_of_nonneg (hG0 omega)]
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            mul_le_mul_of_nonneg_left (hG1 omega) (abs_nonneg (F omega)))
          (sq_nonneg (S omega))
      _ ≤ RF := hmarkedSqF
  have hresult :=
    mu.abs_exponentialTilt_covariance_le_of_centeredTaylor_expect_bounds
      F G S ha hRone hMF (by norm_num) hMF hRF hRone hRF
      hCF hCG hCF hscore hsmall habsScore hscoreSq
      hmeanFabs hmeanGabs hmeanFGabs hmarkedSqF hmarkedSqG hmarkedSqFG
      hcovF hcovG hcovFG hbase hthird
  simpa only [CF, CG] using hresult

/-- Literal second Taylor moment of the genuine valuation score on a finite
cell.  The bound keeps the marked `1/D` factor and the full reciprocal-lcm
ledger; no supremum estimate is used, so no spurious harmonic factor is
introduced. -/
theorem uniformOnFinset_expect_abs_divInd_mul_valuationScore_sq_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcop : ∀ p ∈ P, Nat.Coprime D p)
    (heta : ∀ p ∈ P, |eta p| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2) ≤
      (B / L) ^ 2 *
        ((1 / (c * (D : ℝ))) *
          ∑ a ∈ primePowerModuli P M,
            ∑ b ∈ primePowerModuli P M,
              1 / (Nat.lcm a b : ℝ)) := by
  let R := primePowerModuli P M
  let beta : ℝ := B / L
  have hbeta : 0 ≤ beta := div_nonneg hB hL.le
  have hRpos : ∀ a ∈ R, 0 < a := by
    intro a ha
    exact pos_of_mem_primePowerModuli hprime (by simpa only [R] using ha)
  have hRcop : ∀ a ∈ R, Nat.Coprime D a := by
    intro a ha
    exact coprime_of_mem_primePowerModuli hcop (by simpa only [R] using ha)
  have hpoint : ∀ m : S,
      |divInd D (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2 ≤
        beta ^ 2 *
          (divInd D (m : ℕ) * divisorScore R (m : ℕ) ^ 2) := by
    intro m
    have hscore := abs_valuationScore_le_divisorScore P eta hprime
      (hSpos m m.property) (hSle m m.property) hL heta
    have hscoreSq : valuationScore P eta L (m : ℕ) ^ 2 ≤
        (beta * divisorScore R (m : ℕ)) ^ 2 := by
      have hsquare := pow_le_pow_left₀ (abs_nonneg _)
        (by simpa only [beta, R] using hscore) 2
      simpa only [sq_abs] using hsquare
    have hdiv0 : 0 ≤ divInd D (m : ℕ) := divInd_nonneg _ _
    rw [abs_of_nonneg hdiv0]
    calc
      divInd D (m : ℕ) * valuationScore P eta L (m : ℕ) ^ 2 ≤
          divInd D (m : ℕ) *
            (beta * divisorScore R (m : ℕ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hscoreSq hdiv0
      _ = beta ^ 2 *
          (divInd D (m : ℕ) * divisorScore R (m : ℕ) ^ 2) := by ring
  have havg := DivisibilityMomentBounds.uniformAverage_marked_divisorScore_sq_le
    S R hD hM hc hcard hSpos hSle hRpos hRcop
  calc
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2) ≤
      (uniformOnFinset S hS).expect (fun m : S ↦ beta ^ 2 *
        (divInd D (m : ℕ) * divisorScore R (m : ℕ) ^ 2)) :=
      (uniformOnFinset S hS).expect_mono _ _ hpoint
    _ = beta ^ 2 * DivisibilityMomentBounds.uniformAverage S
        (fun m ↦ divInd D m * divisorScore R m ^ 2) := by
      rw [(uniformOnFinset S hS).expect_smul]
      congr 1
      exact Erdos390.Full.OmittedScoreCell.uniform_expect_eq_uniformAverage
        S hS (fun m ↦ divInd D m * divisorScore R m ^ 2)
    _ ≤ beta ^ 2 *
        ((1 / (c * (D : ℝ))) *
          ∑ a ∈ R, ∑ b ∈ R, 1 / (Nat.lcm a b : ℝ)) :=
      mul_le_mul_of_nonneg_left havg (sq_nonneg beta)
    _ = (B / L) ^ 2 *
        ((1 / (c * (D : ℝ))) *
          ∑ a ∈ primePowerModuli P M,
            ∑ b ∈ primePowerModuli P M,
              1 / (Nat.lcm a b : ℝ)) := by
      rfl

/-- Local-prime version of the marked Taylor second moment.  No
coprimality is assumed between `D` and the score primes; the exact
three-way lcm remains in the conclusion. -/
theorem uniformOnFinset_expect_abs_divInd_mul_valuationScore_sq_lcm_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (heta : ∀ p ∈ P, |eta p| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2) ≤
      (B / L) ^ 2 * ((1 / c) *
        ∑ a ∈ primePowerModuli P M,
          ∑ b ∈ primePowerModuli P M,
            1 / (Nat.lcm D (Nat.lcm a b) : ℝ)) := by
  let R := primePowerModuli P M
  let beta : ℝ := B / L
  have hbeta : 0 ≤ beta := div_nonneg hB hL.le
  have hRpos : ∀ a ∈ R, 0 < a := by
    intro a ha
    exact pos_of_mem_primePowerModuli hprime (by simpa only [R] using ha)
  have hpoint : ∀ m : S,
      |divInd D (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2 ≤
        beta ^ 2 *
          (divInd D (m : ℕ) * divisorScore R (m : ℕ) ^ 2) := by
    intro m
    have hscore := abs_valuationScore_le_divisorScore P eta hprime
      (hSpos m m.property) (hSle m m.property) hL heta
    have hscoreSq : valuationScore P eta L (m : ℕ) ^ 2 ≤
        (beta * divisorScore R (m : ℕ)) ^ 2 := by
      have hsquare := pow_le_pow_left₀ (abs_nonneg _)
        (by simpa only [beta, R] using hscore) 2
      simpa only [sq_abs] using hsquare
    have hdiv0 : 0 ≤ divInd D (m : ℕ) := divInd_nonneg _ _
    rw [abs_of_nonneg hdiv0]
    calc
      divInd D (m : ℕ) * valuationScore P eta L (m : ℕ) ^ 2 ≤
          divInd D (m : ℕ) *
            (beta * divisorScore R (m : ℕ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hscoreSq hdiv0
      _ = beta ^ 2 *
          (divInd D (m : ℕ) * divisorScore R (m : ℕ) ^ 2) := by ring
  have havg :=
    DivisibilityMomentBounds.uniformAverage_marked_divisorScore_sq_lcm_le
      S R hD hM hc hcard hSpos hSle hRpos
  calc
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2) ≤
      (uniformOnFinset S hS).expect (fun m : S ↦ beta ^ 2 *
        (divInd D (m : ℕ) * divisorScore R (m : ℕ) ^ 2)) :=
      (uniformOnFinset S hS).expect_mono _ _ hpoint
    _ = beta ^ 2 * DivisibilityMomentBounds.uniformAverage S
        (fun m ↦ divInd D m * divisorScore R m ^ 2) := by
      rw [(uniformOnFinset S hS).expect_smul]
      congr 1
      exact Erdos390.Full.OmittedScoreCell.uniform_expect_eq_uniformAverage
        S hS (fun m ↦ divInd D m * divisorScore R m ^ 2)
    _ ≤ beta ^ 2 * ((1 / c) *
        ∑ a ∈ R, ∑ b ∈ R,
          1 / (Nat.lcm D (Nat.lcm a b) : ℝ)) :=
      mul_le_mul_of_nonneg_left havg (sq_nonneg beta)
    _ = (B / L) ^ 2 * ((1 / c) *
        ∑ a ∈ primePowerModuli P M,
          ∑ b ∈ primePowerModuli P M,
            1 / (Nat.lcm D (Nat.lcm a b) : ℝ)) := by
      rfl

/-- First-moment counterpart of the literal-lcm Taylor ledger. -/
theorem uniformOnFinset_expect_abs_divInd_mul_abs_valuationScore_lcm_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (heta : ∀ p ∈ P, |eta p| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * ((1 / c) *
        ∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm D a : ℝ)) := by
  let R := primePowerModuli P M
  let beta : ℝ := B / L
  have hbeta : 0 ≤ beta := div_nonneg hB hL.le
  have hRpos : ∀ a ∈ R, 0 < a := by
    intro a ha
    exact pos_of_mem_primePowerModuli hprime (by simpa only [R] using ha)
  have hpoint : ∀ m : S,
      |divInd D (m : ℕ)| * |valuationScore P eta L (m : ℕ)| ≤
        beta * (divInd D (m : ℕ) * divisorScore R (m : ℕ)) := by
    intro m
    have hscore := abs_valuationScore_le_divisorScore P eta hprime
      (hSpos m m.property) (hSle m m.property) hL heta
    have hdiv0 : 0 ≤ divInd D (m : ℕ) := divInd_nonneg _ _
    rw [abs_of_nonneg hdiv0]
    calc
      divInd D (m : ℕ) * |valuationScore P eta L (m : ℕ)| ≤
          divInd D (m : ℕ) *
            (beta * divisorScore R (m : ℕ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [beta, R] using hscore) hdiv0
      _ = beta *
          (divInd D (m : ℕ) * divisorScore R (m : ℕ)) := by ring
  have havg :=
    DivisibilityMomentBounds.uniformAverage_marked_divisorScore_lcm_le
      S R hD hM hc hcard hSpos hSle hRpos
  calc
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (uniformOnFinset S hS).expect (fun m : S ↦ beta *
        (divInd D (m : ℕ) * divisorScore R (m : ℕ))) :=
      (uniformOnFinset S hS).expect_mono _ _ hpoint
    _ = beta * DivisibilityMomentBounds.uniformAverage S
        (fun m ↦ divInd D m * divisorScore R m) := by
      rw [(uniformOnFinset S hS).expect_smul]
      congr 1
      exact Erdos390.Full.OmittedScoreCell.uniform_expect_eq_uniformAverage
        S hS (fun m ↦ divInd D m * divisorScore R m)
    _ ≤ beta * ((1 / c) *
        ∑ a ∈ R, 1 / (Nat.lcm D a : ℝ)) :=
      mul_le_mul_of_nonneg_left havg hbeta
    _ = (B / L) * ((1 / c) *
        ∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm D a : ℝ)) := by
      rfl

/-- Summed local-valuation first Taylor moment.  The complete local-prime
dependence is exposed by the finite two-way lcm ledger. -/
theorem uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M p : ℕ} {B L c : ℝ}
    (hp : p.Prime) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |valuation p (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by
  let mu := uniformOnFinset S hS
  let score : S → ℝ := fun m ↦ valuationScore P eta L (m : ℕ)
  have hpoint : (fun m : S ↦ |valuation p (m : ℕ)| * |score m|) =
      fun m : S ↦ ∑ r ∈ positiveExponents M,
        |divInd (p ^ r) (m : ℕ)| * |score m| := by
    funext m
    rw [abs_of_nonneg (valuation_nonneg p (m : ℕ)),
      valuation_eq_sum_divInd_of_le hp (hSpos m m.property)
        (hSle m m.property)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [abs_of_nonneg (divInd_nonneg (p ^ r) (m : ℕ))]
  have hexpand : mu.expect (fun m : S ↦
      ∑ r ∈ positiveExponents M,
        |divInd (p ^ r) (m : ℕ)| * |score m|) =
      ∑ r ∈ positiveExponents M, mu.expect (fun m : S ↦
        |divInd (p ^ r) (m : ℕ)| * |score m|) := by
    exact PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
      (positiveExponents M)
      (fun r m ↦ |divInd (p ^ r) (m : ℕ)| * |score m|)
  rw [hpoint, hexpand]
  calc
    (∑ r ∈ positiveExponents M, mu.expect (fun m : S ↦
        |divInd (p ^ r) (m : ℕ)| * |score m|)) ≤
      ∑ r ∈ positiveExponents M,
        (B / L) * ((1 / c) *
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hpr : 0 < p ^ r := pow_pos hp.pos r
      simpa only [mu, score] using
        uniformOnFinset_expect_abs_divInd_mul_abs_valuationScore_lcm_le
          S P hS eta hpr hM hB hL hc hcard hSpos hSle hprime heta
    _ = (B / L) * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]

/-- Summed local-valuation quadratic Taylor moment.  This is the exact
finite three-way-lcm ledger required for `v_p`; no endpoint-sized supremum
of the valuation occurs. -/
theorem uniformOnFinset_expect_abs_valuation_mul_valuationScore_sq_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M p : ℕ} {B L c : ℝ}
    (hp : p.Prime) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |valuation p (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2) ≤
      (B / L) ^ 2 * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            ∑ b ∈ primePowerModuli P M,
              1 / (Nat.lcm (p ^ r) (Nat.lcm a b) : ℝ)) := by
  let mu := uniformOnFinset S hS
  let score : S → ℝ := fun m ↦ valuationScore P eta L (m : ℕ)
  have hpoint : (fun m : S ↦ |valuation p (m : ℕ)| * score m ^ 2) =
      fun m : S ↦ ∑ r ∈ positiveExponents M,
        |divInd (p ^ r) (m : ℕ)| * score m ^ 2 := by
    funext m
    rw [abs_of_nonneg (valuation_nonneg p (m : ℕ)),
      valuation_eq_sum_divInd_of_le hp (hSpos m m.property)
        (hSle m m.property)]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [abs_of_nonneg (divInd_nonneg (p ^ r) (m : ℕ))]
  have hexpand : mu.expect (fun m : S ↦
      ∑ r ∈ positiveExponents M,
        |divInd (p ^ r) (m : ℕ)| * score m ^ 2) =
      ∑ r ∈ positiveExponents M, mu.expect (fun m : S ↦
        |divInd (p ^ r) (m : ℕ)| * score m ^ 2) := by
    exact PrimePowerCutoffCovariance.FiniteProbability.expect_sum mu
      (positiveExponents M)
      (fun r m ↦ |divInd (p ^ r) (m : ℕ)| * score m ^ 2)
  rw [hpoint, hexpand]
  calc
    (∑ r ∈ positiveExponents M, mu.expect (fun m : S ↦
        |divInd (p ^ r) (m : ℕ)| * score m ^ 2)) ≤
      ∑ r ∈ positiveExponents M,
        (B / L) ^ 2 * ((1 / c) *
          ∑ a ∈ primePowerModuli P M,
            ∑ b ∈ primePowerModuli P M,
              1 / (Nat.lcm (p ^ r) (Nat.lcm a b) : ℝ)) := by
      apply Finset.sum_le_sum
      intro r hr
      have hpr : 0 < p ^ r := pow_pos hp.pos r
      simpa only [mu, score] using
        uniformOnFinset_expect_abs_divInd_mul_valuationScore_sq_lcm_le
          S P hS eta hpr hM hB hL hc hcard hSpos hSle hprime heta
    _ = (B / L) ^ 2 * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            ∑ b ∈ primePowerModuli P M,
              1 / (Nat.lcm (p ^ r) (Nat.lcm a b) : ℝ)) := by
      rw [Finset.mul_sum, Finset.mul_sum]

end FiniteProbability

namespace PrimePowerTaylorLedger

open LocalFugacityBounds PrimePowerLcmGeometry

/-- A fixed constant controlling the complete same-prime reciprocal-lcm
ledger, including the exponent-one row and column. -/
def positivePrimePowerLcmConstant : ℝ :=
  1 + (4 + quadraticHalfMass) / 2

theorem positivePrimePowerLcmConstant_pos :
    0 < positivePrimePowerLcmConstant := by
  unfold positivePrimePowerLcmConstant
  have hq : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  positivity

/-- The entire same-prime prime-power second-moment ledger costs only a
fixed multiple of `1/p`, uniformly in the moving exponent cutoff. -/
theorem sum_positiveExponents_pair_inv_lcm_le
    {p M : ℕ} (hp : p.Prime) :
    (∑ k ∈ positiveExponents M, ∑ l ∈ positiveExponents M,
        1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) ≤
      positivePrimePowerLcmConstant / (p : ℝ) := by
  by_cases hM0 : M = 0
  · subst M
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    simp [positiveExponents,
      div_nonneg positivePrimePowerLcmConstant_pos.le hpR.le]
  have hM1 : 1 ≤ M := by omega
  have hsplit : positiveExponents M = insert 1 (highExponents M) := by
    ext k
    simp only [mem_positiveExponents, Finset.mem_insert, mem_highExponents]
    omega
  have h1not : 1 ∉ highExponents M := by simp
  let H : ℝ := ∑ k ∈ highExponents M, 1 / ((p ^ k : ℕ) : ℝ)
  let Q : ℝ := ∑ k ∈ highExponents M, ∑ l ∈ highExponents M,
    1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)
  have hfirst :
      (∑ l ∈ highExponents M,
          1 / (Nat.lcm (p ^ 1) (p ^ l) : ℝ)) = H := by
    dsimp only [H]
    apply Finset.sum_congr rfl
    intro l hl
    have hl1 : 1 ≤ l := by
      have := (mem_highExponents.mp hl).1
      omega
    rw [lcm_pow_pow_eq_pow_max, max_eq_right hl1]
  have hsecond :
      (∑ k ∈ highExponents M,
          1 / (Nat.lcm (p ^ k) (p ^ 1) : ℝ)) = H := by
    dsimp only [H]
    apply Finset.sum_congr rfl
    intro k hk
    have hk1 : 1 ≤ k := by
      have := (mem_highExponents.mp hk).1
      omega
    rw [lcm_pow_pow_eq_pow_max, max_eq_left hk1]
  have hinner :
      (∑ k ∈ highExponents M,
          ∑ l ∈ insert 1 (highExponents M),
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
        (∑ k ∈ highExponents M,
            1 / (Nat.lcm (p ^ k) (p ^ 1) : ℝ)) +
          ∑ k ∈ highExponents M,
            ∑ l ∈ highExponents M,
              1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) := by
    calc
      (∑ k ∈ highExponents M,
          ∑ l ∈ insert 1 (highExponents M),
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
        ∑ k ∈ highExponents M,
          (1 / (Nat.lcm (p ^ k) (p ^ 1) : ℝ) +
            ∑ l ∈ highExponents M,
              1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) := by
          apply Finset.sum_congr rfl
          intro k hk
          rw [Finset.sum_insert h1not]
      _ = _ := Finset.sum_add_distrib
  have hinnerHQ :
      (∑ k ∈ highExponents M,
          ∑ l ∈ insert 1 (highExponents M),
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) = H + Q := by
    rw [hinner, hsecond]
  have hdecomp :
      (∑ k ∈ positiveExponents M, ∑ l ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) =
        1 / (p : ℝ) + 2 * H + Q := by
    rw [hsplit, Finset.sum_insert h1not]
    rw [show (∑ l ∈ insert 1 (highExponents M),
        1 / (Nat.lcm (p ^ 1) (p ^ l) : ℝ)) =
          1 / (p : ℝ) + H by
      rw [Finset.sum_insert h1not, hfirst]
      norm_num]
    rw [hinnerHQ]
    ring
  have hH : H ≤ 2 / (p : ℝ) ^ 2 := by
    dsimp only [H]
    simpa only [highExponents] using
      (sum_inv_pow_tail_le (p := p) (r := 1) (A := M) hp.two_le)
  have hQ : Q ≤ quadraticHalfMass / (p : ℝ) ^ 2 := by
    dsimp only [Q]
    exact sum_highExponents_pair_inv_lcm_le hp
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  rw [hdecomp]
  calc
    1 / (p : ℝ) + 2 * H + Q ≤
        1 / (p : ℝ) + 2 * (2 / (p : ℝ) ^ 2) +
          quadraticHalfMass / (p : ℝ) ^ 2 := by
      gcongr
    _ = 1 / (p : ℝ) +
        (4 + quadraticHalfMass) / (p : ℝ) ^ 2 := by ring
    _ ≤ 1 / (p : ℝ) +
        ((4 + quadraticHalfMass) / 2) / (p : ℝ) := by
      have hq0 : 0 ≤ 4 + quadraticHalfMass := by
        exact add_nonneg (by norm_num) quadraticHalfMass_nonneg
      have hden : (2 : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 2 := by
        nlinarith
      have htail :
        (4 + quadraticHalfMass) / (p : ℝ) ^ 2 ≤
            ((4 + quadraticHalfMass) / 2) / (p : ℝ) := by
        calc
          (4 + quadraticHalfMass) / (p : ℝ) ^ 2 ≤
              (4 + quadraticHalfMass) / (2 * (p : ℝ)) :=
            div_le_div_of_nonneg_left hq0 (by positivity) hden
          _ = ((4 + quadraticHalfMass) / 2) / (p : ℝ) := by ring
      exact add_le_add le_rfl htail
    _ = positivePrimePowerLcmConstant / (p : ℝ) := by
      unfold positivePrimePowerLcmConstant
      field_simp [hpPos.ne']

/-- Closed same-prime first-order Taylor ledger.  The lcm term contributes
`C/p`; the two product-denominator terms together contribute `4A/p`. -/
theorem sum_positiveExponents_local_cumulant_ledger_le
    {p M : ℕ} (hp : p.Prime) {A : ℝ} (hA : 0 ≤ A) :
    (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
        (1 / ((p ^ max r k : ℕ) : ℝ) +
          (A / ((p ^ k : ℕ) : ℝ)) *
            (1 / ((p ^ r : ℕ) : ℝ)) +
          (A / ((p ^ r : ℕ) : ℝ)) *
            (1 / ((p ^ k : ℕ) : ℝ)))) ≤
      (positivePrimePowerLcmConstant + 4 * A) / (p : ℝ) := by
  let H : ℝ := ∑ k ∈ positiveExponents M, 1 / ((p ^ k : ℕ) : ℝ)
  let Q : ℝ := ∑ r ∈ positiveExponents M,
    ∑ k ∈ positiveExponents M,
      1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)
  have hfirst :
      (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
          1 / ((p ^ max r k : ℕ) : ℝ)) = Q := by
    dsimp only [Q]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro k hk
    rw [lcm_pow_pow_eq_pow_max]
  have hprod :
      (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
          (1 / ((p ^ k : ℕ) : ℝ)) *
            (1 / ((p ^ r : ℕ) : ℝ))) = H ^ 2 := by
    dsimp only [H]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hprod' :
      (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
          (1 / ((p ^ r : ℕ) : ℝ)) *
            (1 / ((p ^ k : ℕ) : ℝ))) = H ^ 2 := by
    rw [Finset.sum_comm]
    exact hprod
  have hsum :
      (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
          (1 / ((p ^ max r k : ℕ) : ℝ) +
            (A / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((p ^ r : ℕ) : ℝ)) +
            (A / ((p ^ r : ℕ) : ℝ)) *
              (1 / ((p ^ k : ℕ) : ℝ)))) =
        Q + 2 * A * H ^ 2 := by
    simp_rw [Finset.sum_add_distrib]
    rw [hfirst]
    have hmiddle :
        (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
            (A / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((p ^ r : ℕ) : ℝ))) = A * H ^ 2 := by
      calc
        _ = A * (∑ r ∈ positiveExponents M,
            ∑ k ∈ positiveExponents M,
              (1 / ((p ^ k : ℕ) : ℝ)) *
                (1 / ((p ^ r : ℕ) : ℝ))) := by
          simp_rw [div_eq_mul_inv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = A * H ^ 2 := by rw [hprod]
    have hlast :
        (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
            (A / ((p ^ r : ℕ) : ℝ)) *
              (1 / ((p ^ k : ℕ) : ℝ))) = A * H ^ 2 := by
      calc
        _ = A * (∑ r ∈ positiveExponents M,
            ∑ k ∈ positiveExponents M,
              (1 / ((p ^ r : ℕ) : ℝ)) *
                (1 / ((p ^ k : ℕ) : ℝ))) := by
          simp_rw [div_eq_mul_inv]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r hr
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k hk
          ring
        _ = A * H ^ 2 := by rw [hprod']
    rw [hmiddle, hlast]
    ring
  have hQ : Q ≤ positivePrimePowerLcmConstant / (p : ℝ) := by
    dsimp only [Q]
    exact sum_positiveExponents_pair_inv_lcm_le hp
  have hH : H ≤ 2 / (p : ℝ) := by
    dsimp only [H]
    exact sum_inv_prime_powers_le p M hp.two_le
  have hH0 : 0 ≤ H := by dsimp only [H]; positivity
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hHsq : H ^ 2 ≤ 2 / (p : ℝ) := by
    have hsquare : H ^ 2 ≤ (2 / (p : ℝ)) ^ 2 :=
      pow_le_pow_left₀ hH0 hH 2
    have htail : (2 / (p : ℝ)) ^ 2 ≤ 2 / (p : ℝ) := by
      have hden : (2 : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
      calc
        (2 / (p : ℝ)) ^ 2 = 4 / (p : ℝ) ^ 2 := by ring
        _ ≤ 4 / (2 * (p : ℝ)) :=
          div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
        _ = 2 / (p : ℝ) := by ring
    exact hsquare.trans htail
  rw [hsum]
  calc
    Q + 2 * A * H ^ 2 ≤
        positivePrimePowerLcmConstant / (p : ℝ) +
          2 * A * (2 / (p : ℝ)) := by
      exact add_le_add hQ (mul_le_mul_of_nonneg_left hHsq
        (mul_nonneg (by norm_num) hA))
    _ = (positivePrimePowerLcmConstant + 4 * A) / (p : ℝ) := by ring

/-- Deduplicating prime powers does not change the reciprocal-lcm ledger. -/
theorem sum_inv_lcm_primePowerModuli_eq
    (P : Finset ℕ) (M : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∑ a ∈ primePowerModuli P M,
        ∑ b ∈ primePowerModuli P M,
          1 / (Nat.lcm a b : ℝ)) =
      ∑ p ∈ P, ∑ k ∈ positiveExponents M,
        ∑ q ∈ P, ∑ l ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ) := by
  unfold primePowerModuli
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_image]
    · rw [Finset.sum_product]
    · intro a ha b hb hab
      exact primePowerMap_injective hprime ha hb hab
  · intro a ha b hb hab
    exact primePowerMap_injective hprime ha hb hab

/-- The complete prime-power reciprocal-lcm ledger is bounded by the square
of its reciprocal mass plus one same-prime diagonal ledger.  This is the
quantitative `O(H²+H)` estimate used in the second Taylor remainder. -/
theorem sum_inv_lcm_primePowerModuli_le_sq_add
    (P : Finset ℕ) (M : ℕ) (hprime : ∀ p ∈ P, p.Prime) :
    (∑ a ∈ primePowerModuli P M,
        ∑ b ∈ primePowerModuli P M,
          1 / (Nat.lcm a b : ℝ)) ≤
      (∑ p ∈ P, ∑ k ∈ positiveExponents M,
          1 / ((p ^ k : ℕ) : ℝ)) ^ 2 +
        positivePrimePowerLcmConstant * ∑ p ∈ P, 1 / (p : ℝ) := by
  rw [sum_inv_lcm_primePowerModuli_eq P M hprime]
  let H : ℝ := ∑ p ∈ P, ∑ k ∈ positiveExponents M,
    1 / ((p ^ k : ℕ) : ℝ)
  let diagonal : ℝ := ∑ p ∈ P,
    ∑ k ∈ positiveExponents M, ∑ l ∈ positiveExponents M,
      1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)
  have hpair (p : ℕ) (hp : p ∈ P) (k : ℕ)
      (hk : k ∈ positiveExponents M) :
      (∑ q ∈ P, ∑ l ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ)) ≤
        (∑ q ∈ P, ∑ l ∈ positiveExponents M,
          1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) +
        ∑ l ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) := by
    have hterm (q : ℕ) (hq : q ∈ P) :
        (∑ l ∈ positiveExponents M,
            1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ)) ≤
          (∑ l ∈ positiveExponents M,
            1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) +
          if q = p then
            ∑ l ∈ positiveExponents M,
              1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)
          else 0 := by
      by_cases hqp : q = p
      · subst q
        rw [if_pos rfl]
        exact le_add_of_nonneg_left (by positivity)
      · rw [if_neg hqp, add_zero]
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro l hl
        have hpq : Nat.Coprime p q :=
          (Nat.coprime_primes (hprime p hp) (hprime q hq)).mpr
            (Ne.symm hqp)
        have hpqPow : Nat.Coprime (p ^ k) (q ^ l) :=
          (hpq.pow_left k).pow_right l
        rw [hpqPow.lcm_eq_mul]
    calc
      (∑ q ∈ P, ∑ l ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ)) ≤
        ∑ q ∈ P,
          ((∑ l ∈ positiveExponents M,
              1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) +
            if q = p then
              ∑ l ∈ positiveExponents M,
                1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)
            else 0) := Finset.sum_le_sum fun q hq ↦ hterm q hq
      _ = (∑ q ∈ P, ∑ l ∈ positiveExponents M,
            1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) +
          ∑ l ∈ positiveExponents M,
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) := by
        rw [Finset.sum_add_distrib]
        simp [hp]
  have hquad :
      (∑ p ∈ P, ∑ k ∈ positiveExponents M,
          ∑ q ∈ P, ∑ l ∈ positiveExponents M,
            1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ)) ≤
        (∑ p ∈ P, ∑ k ∈ positiveExponents M,
          ∑ q ∈ P, ∑ l ∈ positiveExponents M,
            1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) + diagonal := by
    calc
      _ ≤ ∑ p ∈ P, ∑ k ∈ positiveExponents M,
          ((∑ q ∈ P, ∑ l ∈ positiveExponents M,
              1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) +
            ∑ l ∈ positiveExponents M,
              1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) := by
        exact Finset.sum_le_sum fun p hp ↦
          Finset.sum_le_sum fun k hk ↦ hpair p hp k hk
      _ = _ := by
        rw [show diagonal = ∑ p ∈ P, ∑ k ∈ positiveExponents M,
            ∑ l ∈ positiveExponents M,
              1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ) by rfl]
        simp_rw [Finset.sum_add_distrib]
  have hproduct :
      (∑ p ∈ P, ∑ k ∈ positiveExponents M,
          ∑ q ∈ P, ∑ l ∈ positiveExponents M,
            1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) = H ^ 2 := by
    dsimp only [H]
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p hp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    norm_num only [Nat.cast_mul]
    ring
  have hdiagonal : diagonal ≤
      positivePrimePowerLcmConstant * ∑ p ∈ P, 1 / (p : ℝ) := by
    dsimp only [diagonal]
    calc
      _ ≤ ∑ p ∈ P,
          positivePrimePowerLcmConstant / (p : ℝ) := by
        exact Finset.sum_le_sum fun p hp ↦
          sum_positiveExponents_pair_inv_lcm_le (hprime p hp)
      _ = positivePrimePowerLcmConstant * ∑ p ∈ P, 1 / (p : ℝ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  calc
    _ ≤ (∑ p ∈ P, ∑ k ∈ positiveExponents M,
          ∑ q ∈ P, ∑ l ∈ positiveExponents M,
            1 / (((p ^ k) * (q ^ l) : ℕ) : ℝ)) + diagonal := hquad
    _ = H ^ 2 + diagonal := by rw [hproduct]
    _ ≤ H ^ 2 +
        positivePrimePowerLcmConstant * ∑ p ∈ P, 1 / (p : ℝ) :=
      add_le_add le_rfl hdiagonal
    _ = (∑ p ∈ P, ∑ k ∈ positiveExponents M,
          1 / ((p ^ k : ℕ) : ℝ)) ^ 2 +
        positivePrimePowerLcmConstant * ∑ p ∈ P, 1 / (p : ℝ) := by
      rfl

/-- One forced prime-valuation row against the complete prime-power score
has reciprocal scale `1/p`.  Distinct score primes give the product ledger;
the only non-coprime contribution is the already closed same-prime ledger. -/
theorem sum_positiveExponents_primePowerModuli_inv_lcm_le
    (P : Finset ℕ) (M p : ℕ) (hpP : p ∈ P)
    (hprime : ∀ q ∈ P, q.Prime) :
    (∑ r ∈ positiveExponents M,
        ∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm (p ^ r) a : ℝ)) ≤
      (4 * (∑ q ∈ P, 1 / (q : ℝ)) +
        positivePrimePowerLcmConstant) / (p : ℝ) := by
  have hp := hprime p hpP
  have hrewrite (r : ℕ) :
      (∑ a ∈ primePowerModuli P M,
          1 / (Nat.lcm (p ^ r) a : ℝ)) =
        ∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ) := by
    unfold primePowerModuli
    rw [Finset.sum_image]
    · rw [Finset.sum_product]
    · intro a ha b hb hab
      exact primePowerMap_injective hprime ha hb hab
  simp_rw [hrewrite]
  let Hp : ℝ := ∑ r ∈ positiveExponents M,
    1 / ((p ^ r : ℕ) : ℝ)
  let U : ℝ := ∑ q ∈ P, ∑ k ∈ positiveExponents M,
    1 / ((q ^ k : ℕ) : ℝ)
  let Qp : ℝ := ∑ r ∈ positiveExponents M,
    ∑ k ∈ positiveExponents M,
      1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)
  have hterm (r : ℕ) (hr : r ∈ positiveExponents M) :
      (∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ)) ≤
        (∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
        ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ) := by
    have hq (q : ℕ) (hqP : q ∈ P) :
        (∑ k ∈ positiveExponents M,
            1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ)) ≤
          (∑ k ∈ positiveExponents M,
            1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
          if q = p then
            ∑ k ∈ positiveExponents M,
              1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)
          else 0 := by
      by_cases hqp : q = p
      · subst q
        rw [if_pos rfl]
        exact le_add_of_nonneg_left (by positivity)
      · rw [if_neg hqp, add_zero]
        apply le_of_eq
        apply Finset.sum_congr rfl
        intro k hk
        have hpq : Nat.Coprime p q :=
          (Nat.coprime_primes hp (hprime q hqP)).mpr (Ne.symm hqp)
        rw [((hpq.pow_left r).pow_right k).lcm_eq_mul]
    calc
      _ ≤ ∑ q ∈ P,
          ((∑ k ∈ positiveExponents M,
              1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
            if q = p then
              ∑ k ∈ positiveExponents M,
                1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)
            else 0) := Finset.sum_le_sum fun q hqP ↦ hq q hqP
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp [hpP]
  have hsum :
      (∑ r ∈ positiveExponents M,
        ∑ q ∈ P, ∑ k ∈ positiveExponents M,
          1 / (Nat.lcm (p ^ r) (q ^ k) : ℝ)) ≤ Hp * U + Qp := by
    calc
      _ ≤ ∑ r ∈ positiveExponents M,
          ((∑ q ∈ P, ∑ k ∈ positiveExponents M,
              1 / (((p ^ r) * (q ^ k) : ℕ) : ℝ)) +
            ∑ k ∈ positiveExponents M,
              1 / (Nat.lcm (p ^ r) (p ^ k) : ℝ)) :=
        Finset.sum_le_sum fun r hr ↦ hterm r hr
      _ = Hp * U + Qp := by
        rw [Finset.sum_add_distrib]
        dsimp only [Hp, U, Qp]
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        norm_num only [Nat.cast_mul]
        ring
  have hHp : Hp ≤ 2 / (p : ℝ) := by
    dsimp only [Hp]
    exact sum_inv_prime_powers_le p M hp.two_le
  have hU : U ≤ 2 * (∑ q ∈ P, 1 / (q : ℝ)) := by
    dsimp only [U]
    have hraw := sum_inv_primePowerModuli_le P M hprime
    rw [sum_inv_primePowerModuli_eq P M hprime] at hraw
    exact hraw
  have hQp : Qp ≤ positivePrimePowerLcmConstant / (p : ℝ) := by
    dsimp only [Qp]
    exact sum_positiveExponents_pair_inv_lcm_le hp
  have hHp0 : 0 ≤ Hp := by dsimp only [Hp]; positivity
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hT0 : 0 ≤ (∑ q ∈ P, 1 / (q : ℝ)) := by positivity
  calc
    _ ≤ Hp * U + Qp := hsum
    _ ≤ (2 / (p : ℝ)) *
          (2 * (∑ q ∈ P, 1 / (q : ℝ))) +
        positivePrimePowerLcmConstant / (p : ℝ) := by
      exact add_le_add (mul_le_mul hHp hU hU0 (by positivity)) hQp
    _ = (4 * (∑ q ∈ P, 1 / (q : ℝ)) +
        positivePrimePowerLcmConstant) / (p : ℝ) := by ring

end PrimePowerTaylorLedger

namespace FiniteProbability

open PrimePowerTaylorLedger

variable {Omega : Type*} [Fintype Omega]

/-- Closed local-prime Taylor coefficient.  Restoring the forced prime costs
`O(1/(pL²))`, hence is strictly smaller than the target moving-prefix
`O(1/(pL))` row. -/
theorem abs_covarianceThirdCentered_valuation_localScore_reciprocal_le
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) (p M : ℕ) (eta : ℕ → ℝ)
    {B K A L : ℝ}
    (hp : p.Prime) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hA : 0 ≤ A) (hL : 0 < L)
    (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (heta : |eta p| ≤ B)
    (hcovPow : ∀ r ∈ positiveExponents M,
      |mu.covariance
          (fun omega ↦ divInd (p ^ r) (value omega)) pref| ≤
        K / (((p ^ r : ℕ) : ℝ) * L))
    (hexpectPow : ∀ r ∈ positiveExponents M,
      mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) ≤
        A / ((p ^ r : ℕ) : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ valuation p (value omega)) pref
        (fun omega ↦ valuationScore {p} eta L (value omega))| ≤
      (B * K / L ^ 2) *
        ((positivePrimePowerLcmConstant + 4 * A) / (p : ℝ)) := by
  have hraw := mu.abs_covarianceThirdCentered_valuation_localScore_le
    value pref p M eta hp hB hA hL hvaluePos hvalueLe heta hcovPow
      hexpectPow
  let ledger : ℝ :=
    ∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
      (1 / ((p ^ max r k : ℕ) : ℝ) +
        (A / ((p ^ k : ℕ) : ℝ)) *
          (1 / ((p ^ r : ℕ) : ℝ)) +
        (A / ((p ^ r : ℕ) : ℝ)) *
          (1 / ((p ^ k : ℕ) : ℝ)))
  have hrewrite :
      (∑ r ∈ positiveExponents M, ∑ k ∈ positiveExponents M,
        (B / L) *
          (K / (((p ^ max r k : ℕ) : ℝ) * L) +
            (A / ((p ^ k : ℕ) : ℝ)) *
              (K / (((p ^ r : ℕ) : ℝ) * L)) +
            (A / ((p ^ r : ℕ) : ℝ)) *
              (K / (((p ^ k : ℕ) : ℝ) * L)))) =
        (B * K / L ^ 2) * ledger := by
    dsimp only [ledger]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    field_simp [hL.ne']
  have hledger : ledger ≤
      (positivePrimePowerLcmConstant + 4 * A) / (p : ℝ) := by
    dsimp only [ledger]
    exact sum_positiveExponents_local_cumulant_ledger_le hp hA
  rw [hrewrite] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left hledger (by positivity))

/-- Closed `O(H²+H)` version of the marked second Taylor moment, where
`H=∑_{p∈P}1/p`.  This is the form used for a moving prime band. -/
theorem uniformOnFinset_expect_abs_divInd_mul_valuationScore_sq_reciprocal_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M D : ℕ} {B L c : ℝ}
    (hD : 0 < D) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ p ∈ P, p.Prime)
    (hcop : ∀ p ∈ P, Nat.Coprime D p)
    (heta : ∀ p ∈ P, |eta p| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |divInd D (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2) ≤
      (B / L) ^ 2 * (1 / (c * (D : ℝ))) *
        (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 +
          positivePrimePowerLcmConstant * ∑ p ∈ P, 1 / (p : ℝ)) := by
  let T : ℝ := ∑ p ∈ P, 1 / (p : ℝ)
  let U : ℝ := ∑ p ∈ P, ∑ k ∈ positiveExponents M,
    1 / ((p ^ k : ℕ) : ℝ)
  let Q : ℝ := ∑ a ∈ primePowerModuli P M,
    ∑ b ∈ primePowerModuli P M, 1 / (Nat.lcm a b : ℝ)
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have hU0 : 0 ≤ U := by dsimp only [U]; positivity
  have hU : U ≤ 2 * T := by
    have hraw := sum_inv_primePowerModuli_le P M hprime
    rw [sum_inv_primePowerModuli_eq P M hprime] at hraw
    simpa only [U, T] using hraw
  have hQ : Q ≤ U ^ 2 + positivePrimePowerLcmConstant * T := by
    dsimp only [Q, U, T]
    exact sum_inv_lcm_primePowerModuli_le_sq_add P M hprime
  have hUsq : U ^ 2 ≤ 4 * T ^ 2 := by
    have hsquare : U ^ 2 ≤ (2 * T) ^ 2 :=
      pow_le_pow_left₀ hU0 hU 2
    nlinarith
  have hQclosed : Q ≤
      4 * T ^ 2 + positivePrimePowerLcmConstant * T :=
    hQ.trans (add_le_add hUsq le_rfl)
  have hfactor0 : 0 ≤ (B / L) ^ 2 * (1 / (c * (D : ℝ))) := by
    positivity
  have hraw := uniformOnFinset_expect_abs_divInd_mul_valuationScore_sq_le
    S P hS eta hD hM hB hL hc hcard hSpos hSle hprime hcop heta
  calc
    _ ≤ (B / L) ^ 2 * ((1 / (c * (D : ℝ))) * Q) := by
      simpa only [Q] using hraw
    _ = ((B / L) ^ 2 * (1 / (c * (D : ℝ)))) * Q := by ring
    _ ≤ ((B / L) ^ 2 * (1 / (c * (D : ℝ)))) *
        (4 * T ^ 2 + positivePrimePowerLcmConstant * T) :=
      mul_le_mul_of_nonneg_left hQclosed hfactor0
    _ = (B / L) ^ 2 * (1 / (c * (D : ℝ))) *
        (4 * (∑ p ∈ P, 1 / (p : ℝ)) ^ 2 +
          positivePrimePowerLcmConstant * ∑ p ∈ P, 1 / (p : ℝ)) := by
      rfl

/-- Closed reciprocal version of the marked first Taylor moment for a full
valuation row. -/
theorem uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_reciprocal_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M p : ℕ} {B L c : ℝ}
    (hpP : p ∈ P) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |valuation p (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * (1 / c) *
        ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
          positivePrimePowerLcmConstant) / (p : ℝ)) := by
  have hraw := uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_le
    S P hS eta (hprime p hpP) hM hB hL hc hcard hSpos hSle hprime heta
  have hledger := sum_positiveExponents_primePowerModuli_inv_lcm_le
    P M p hpP hprime
  have hfactor0 : 0 ≤ (B / L) * (1 / c) := by positivity
  calc
    _ ≤ (B / L) * ((1 / c) *
        ∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := hraw
    _ = ((B / L) * (1 / c)) *
        (∑ r ∈ positiveExponents M,
          ∑ a ∈ primePowerModuli P M,
            1 / (Nat.lcm (p ^ r) a : ℝ)) := by ring
    _ ≤ ((B / L) * (1 / c)) *
        ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
          positivePrimePowerLcmConstant) / (p : ℝ)) :=
      mul_le_mul_of_nonneg_left hledger hfactor0
    _ = (B / L) * (1 / c) *
        ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
          positivePrimePowerLcmConstant) / (p : ℝ)) := by ring

/-- Unmarked first moment of the literal valuation score. -/
theorem uniformOnFinset_expect_abs_valuationScore_reciprocal_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M : ℕ} {B L c : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        |valuationScore P eta L (m : ℕ)|) ≤
      (B / L) * ((2 / c) * ∑ q ∈ P, 1 / (q : ℝ)) := by
  have hraw := uniformOnFinset_expect_abs_divInd_mul_abs_valuationScore_lcm_le
    S P hS eta (D := 1) (by omega) hM hB hL hc hcard hSpos hSle
      hprime heta
  have hleft : (fun m : S ↦
      |divInd 1 (m : ℕ)| * |valuationScore P eta L (m : ℕ)|) =
      fun m : S ↦ |valuationScore P eta L (m : ℕ)| := by
    funext m
    simp [divInd]
  rw [hleft] at hraw
  simp only [Nat.lcm_one_left] at hraw
  have hsum := sum_inv_primePowerModuli_le P M hprime
  have hfactor0 : 0 ≤ (B / L) * (1 / c) := by positivity
  calc
    _ ≤ (B / L) * ((1 / c) *
        ∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) := hraw
    _ = ((B / L) * (1 / c)) *
        (∑ a ∈ primePowerModuli P M, 1 / (a : ℝ)) := by ring
    _ ≤ ((B / L) * (1 / c)) *
        (2 * ∑ q ∈ P, 1 / (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum hfactor0
    _ = (B / L) * ((2 / c) * ∑ q ∈ P, 1 / (q : ℝ)) := by ring

/-- Unmarked quadratic moment of the literal valuation score. -/
theorem uniformOnFinset_expect_valuationScore_sq_reciprocal_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M : ℕ} {B L c : ℝ}
    (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B) :
    (uniformOnFinset S hS).expect (fun m : S ↦
        valuationScore P eta L (m : ℕ) ^ 2) ≤
      (B / L) ^ 2 * (1 / c) *
        (4 * (∑ q ∈ P, 1 / (q : ℝ)) ^ 2 +
          positivePrimePowerLcmConstant *
            ∑ q ∈ P, 1 / (q : ℝ)) := by
  have hraw := uniformOnFinset_expect_abs_divInd_mul_valuationScore_sq_lcm_le
    S P hS eta (D := 1) (by omega) hM hB hL hc hcard hSpos hSle
      hprime heta
  have hleft : (fun m : S ↦
      |divInd 1 (m : ℕ)| * valuationScore P eta L (m : ℕ) ^ 2) =
      fun m : S ↦ valuationScore P eta L (m : ℕ) ^ 2 := by
    funext m
    simp [divInd]
  rw [hleft] at hraw
  simp only [Nat.lcm_one_left] at hraw
  let T : ℝ := ∑ q ∈ P, 1 / (q : ℝ)
  let Q : ℝ := ∑ a ∈ primePowerModuli P M,
    ∑ b ∈ primePowerModuli P M, 1 / (Nat.lcm a b : ℝ)
  have hQ : Q ≤ 4 * T ^ 2 + positivePrimePowerLcmConstant * T := by
    have hbase := sum_inv_lcm_primePowerModuli_le_sq_add P M hprime
    let U : ℝ := ∑ q ∈ P, ∑ k ∈ positiveExponents M,
      1 / ((q ^ k : ℕ) : ℝ)
    have hU0 : 0 ≤ U := by dsimp only [U]; positivity
    have hU : U ≤ 2 * T := by
      have hs := sum_inv_primePowerModuli_le P M hprime
      rw [sum_inv_primePowerModuli_eq P M hprime] at hs
      simpa only [U, T] using hs
    have hUsq : U ^ 2 ≤ 4 * T ^ 2 := by
      have hT0 : 0 ≤ T := by dsimp only [T]; positivity
      have hs := pow_le_pow_left₀ hU0 hU 2
      nlinarith
    dsimp only [Q, U, T] at hbase hUsq ⊢
    exact hbase.trans (add_le_add hUsq le_rfl)
  have hfactor0 : 0 ≤ (B / L) ^ 2 * (1 / c) := by positivity
  calc
    _ ≤ (B / L) ^ 2 * ((1 / c) * Q) := by
      simpa only [Q] using hraw
    _ = ((B / L) ^ 2 * (1 / c)) * Q := by ring
    _ ≤ ((B / L) ^ 2 * (1 / c)) *
        (4 * T ^ 2 + positivePrimePowerLcmConstant * T) :=
      mul_le_mul_of_nonneg_left hQ hfactor0
    _ = (B / L) ^ 2 * (1 / c) *
        (4 * (∑ q ∈ P, 1 / (q : ℝ)) ^ 2 +
          positivePrimePowerLcmConstant *
            ∑ q ∈ P, 1 / (q : ℝ)) := by rfl

/-- Reciprocal first moment of one full valuation under the un-tilted
uniform cell law. -/
theorem uniformOnFinset_expect_valuation_reciprocal_le
    (S : Finset ℕ) (hS : S.Nonempty) {M p : ℕ} {c : ℝ}
    (hp : p.Prime) (hM : 0 < M) (hc : 0 < c)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    (uniformOnFinset S hS).expect
        (fun m : S ↦ (valuation p (m : ℕ) : ℝ)) ≤
      2 / (c * (p : ℝ)) := by
  let mu := uniformOnFinset S hS
  have hpoint : (fun m : S ↦ (valuation p (m : ℕ) : ℝ)) =
      fun m : S ↦ ∑ r ∈ positiveExponents M,
        divInd (p ^ r) (m : ℕ) := by
    funext m
    exact valuation_eq_sum_divInd_of_le hp (hSpos m m.property)
      (hSle m m.property)
  rw [hpoint,
    PrimePowerCutoffCovariance.FiniteProbability.expect_sum]
  have hterm (r : ℕ) (hr : r ∈ positiveExponents M) :
      mu.expect (fun m : S ↦ divInd (p ^ r) (m : ℕ)) ≤
        1 / (c * ((p ^ r : ℕ) : ℝ)) := by
    rw [OmittedScoreCell.uniform_expect_eq_uniformAverage]
    exact OmittedTiltFallback.uniformAverage_divInd_le S
      (pow_pos hp.pos r) hM hc hcard hSpos hSle
  calc
    ∑ r ∈ positiveExponents M,
        mu.expect (fun m : S ↦ divInd (p ^ r) (m : ℕ)) ≤
      ∑ r ∈ positiveExponents M,
        1 / (c * ((p ^ r : ℕ) : ℝ)) := by
      exact Finset.sum_le_sum fun r hr ↦ hterm r hr
    _ = (1 / c) * (∑ r ∈ positiveExponents M,
        1 / ((p ^ r : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    _ ≤ (1 / c) * (2 / (p : ℝ)) := by
      exact mul_le_mul_of_nonneg_left
        (sum_inv_prime_powers_le p M hp.two_le) (by positivity)
    _ = 2 / (c * (p : ℝ)) := by ring

/-- The explicit Taylor majorant used for a raw moving-prefix row.  The
quadratic marked moment is charged by the first marked moment using
`S² ≤ |S|` on the pointwise box `|S|≤1`; this is already sharp enough for
the required `log² L / L →0` rate. -/
def rawTiltPrefixTaylorBound
    (a MF RFone Czero Cthird : ℝ) : ℝ :=
  let CF := RFone + MF * a
  let CG := 2 * a
  let EF := 2 * (RFone + CF * a + (MF + CF) * a)
  let EG := 2 * (a + CG * a + (1 + CG) * a)
  let EFG := EF
  Czero + Cthird + CF * CG + EFG +
    (MF + CF) * EG + (1 + CG) * EF + EF * EG

theorem rawTiltPrefixTaylorBound_nonneg
    {a MF RFone Czero Cthird : ℝ}
    (ha : 0 ≤ a) (hMF : 0 ≤ MF) (hRF : 0 ≤ RFone)
    (hCzero : 0 ≤ Czero) (hCthird : 0 ≤ Cthird) :
    0 ≤ rawTiltPrefixTaylorBound a MF RFone Czero Cthird := by
  unfold rawTiltPrefixTaylorBound
  dsimp only
  positivity

/-- Finite raw-cell Taylor closure.  Once the un-tilted moving-prefix row
and its first Taylor third cumulant are supplied, every normalization and
quadratic remainder is discharged by literal multiple-counting ledgers. -/
theorem uniformOnFinset_exponentialTilt_covariance_valuation_prefix_le
    (S P : Finset ℕ) (hS : S.Nonempty) (eta : ℕ → ℝ)
    {M p k : ℕ} {B L c Czero Cthird : ℝ}
    (hpP : p ∈ P) (hM : 0 < M) (hB : 0 ≤ B) (hL : 0 < L)
    (hc : 0 < c) (hCzero : 0 ≤ Czero) (hCthird : 0 ≤ Cthird)
    (hcard : c * (M : ℝ) ≤ (S.card : ℝ))
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M)
    (hprime : ∀ q ∈ P, q.Prime)
    (heta : ∀ q ∈ P, |eta q| ≤ B)
    (hscore : ∀ m : S, |valuationScore P eta L (m : ℕ)| ≤ 1)
    (hsmall : 2 * ((B / L) *
        ((2 / c) * ∑ q ∈ P, 1 / (q : ℝ))) ≤ (1 : ℝ) / 2)
    (hbase :
      |(uniformOnFinset S hS).covariance
          (fun m : S ↦ (valuation p (m : ℕ) : ℝ))
          (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤ Czero)
    (hthird :
      |(uniformOnFinset S hS).covarianceThirdCentered
          (fun m : S ↦ (valuation p (m : ℕ) : ℝ))
          (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
          (fun m : S ↦ valuationScore P eta L (m : ℕ))| ≤ Cthird) :
    let a := (B / L) *
      ((2 / c) * ∑ q ∈ P, 1 / (q : ℝ))
    let MF := 2 / (c * (p : ℝ))
    let RFone := (B / L) * (1 / c) *
      ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
        PrimePowerTaylorLedger.positivePrimePowerLcmConstant) / (p : ℝ))
    |((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L (m : ℕ))).covariance
        (fun m : S ↦ (valuation p (m : ℕ) : ℝ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
      rawTiltPrefixTaylorBound a MF RFone Czero Cthird := by
  dsimp only
  let mu := uniformOnFinset S hS
  let score : S → ℝ := fun m ↦ valuationScore P eta L (m : ℕ)
  let pref : S → ℝ := fun m ↦ if (m : ℕ) ≤ k then 1 else 0
  let F : S → ℝ := fun m ↦ (valuation p (m : ℕ) : ℝ)
  let a : ℝ := (B / L) *
    ((2 / c) * ∑ q ∈ P, 1 / (q : ℝ))
  let MF : ℝ := 2 / (c * (p : ℝ))
  let RFone : ℝ := (B / L) * (1 / c) *
    ((4 * (∑ q ∈ P, 1 / (q : ℝ)) +
      PrimePowerTaylorLedger.positivePrimePowerLcmConstant) / (p : ℝ))
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hMF : 0 ≤ MF := by
    dsimp only [MF]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hpP).pos
    positivity
  have hRFone : 0 ≤ RFone := by
    dsimp only [RFone]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hpP).pos
    have hconst := PrimePowerTaylorLedger.positivePrimePowerLcmConstant_pos
    positivity
  have hmajorant0 :
      0 ≤ rawTiltPrefixTaylorBound a MF RFone Czero Cthird :=
    rawTiltPrefixTaylorBound_nonneg ha hMF hRFone hCzero hCthird
  have habsScore : mu.expect (fun m ↦ |score m|) ≤ a := by
    dsimp only [mu, score, a]
    exact uniformOnFinset_expect_abs_valuationScore_reciprocal_le
      S P hS eta hM hB hL hc hcard hSpos hSle hprime heta
  have hscoreSq : mu.expect (fun m ↦ score m ^ 2) ≤ a := by
    calc
      mu.expect (fun m ↦ score m ^ 2) ≤
          mu.expect (fun m ↦ |score m|) := by
        apply mu.expect_mono
        intro m
        have hs0 := abs_nonneg (score m)
        have hs1 : |score m| ≤ 1 := by simpa only [score] using hscore m
        rw [← sq_abs]
        nlinarith
      _ ≤ a := habsScore
  have hF0 : ∀ m, 0 ≤ F m := by
    intro m
    dsimp only [F]
    exact valuation_nonneg p (m : ℕ)
  have hmeanF : mu.expect F ≤ MF := by
    dsimp only [mu, F, MF]
    exact uniformOnFinset_expect_valuation_reciprocal_le S hS
      (hprime p hpP) hM hc hcard hSpos hSle
  have hpref0 : ∀ m, 0 ≤ pref m := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hpref1 : ∀ m, pref m ≤ 1 := by
    intro m
    dsimp only [pref]
    split_ifs <;> norm_num
  have hmarkedFirst :
      mu.expect (fun m ↦ |F m| * |score m|) ≤ RFone := by
    dsimp only [mu, F, score, RFone]
    exact uniformOnFinset_expect_abs_valuation_mul_abs_valuationScore_reciprocal_le
      S P hS eta hpP hM hB hL hc hcard hSpos hSle hprime heta
  have hmarkedSqF :
      mu.expect (fun m ↦ |F m| * score m ^ 2) ≤ RFone := by
    calc
      mu.expect (fun m ↦ |F m| * score m ^ 2) ≤
          mu.expect (fun m ↦ |F m| * |score m|) := by
        apply mu.expect_mono
        intro m
        apply mul_le_mul_of_nonneg_left _ (abs_nonneg (F m))
        have hs0 := abs_nonneg (score m)
        have hs1 : |score m| ≤ 1 := by simpa only [score] using hscore m
        rw [← sq_abs]
        nlinarith
      _ ≤ RFone := hmarkedFirst
  have hraw := mu.abs_exponentialTilt_covariance_nonneg_prefix_le_of_moments
    F pref score ha ha hMF hRFone hRFone
      (by simpa only [score] using hscore) (by simpa only [a] using hsmall)
      habsScore hscoreSq hF0 hmeanF hpref0 hpref1 hmarkedFirst
      hmarkedSqF (by simpa only [mu, F, pref] using hbase)
      (by simpa only [mu, F, pref, score] using hthird)
  have hfinal :
      |(mu.exponentialTilt score).covariance F pref| ≤
        rawTiltPrefixTaylorBound a MF RFone Czero Cthird := by
    simpa only [rawTiltPrefixTaylorBound, mu, F, pref, score, a, MF, RFone]
      using hraw
  exact hfinal.trans (by linarith [hmajorant0])

end FiniteProbability

namespace FiniteLogStieltjes

open Finset Set

variable {Omega : Type*} [Fintype Omega]

/-- The exact finite Stieltjes implication used by the paper: a uniform
bound for every centered cumulative marked mass is charged once against the
total variation of `log`. -/
theorem abs_covariance_log_le_of_centeredPrefix
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) {lo hi : ℕ} {E : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hE : 0 ≤ E)
    (hsupport : ∀ omega, lo < value omega ∧ value omega ≤ hi)
    (hprefix : ∀ t ∈ Set.Ioc (lo : ℝ) (hi : ℝ),
      |∑ k ∈ Icc 0 ⌊t⌋₊, centeredFiberMass mu value A k| ≤ E) :
    |mu.covariance A (fun omega ↦ Real.log (value omega : ℝ))| ≤
      (E / (lo : ℝ)) * ((hi : ℝ) - (lo : ℝ)) := by
  have hleft := sum_centeredFiberMass_Icc_lo_eq_zero
    mu value A (fun omega ↦ (hsupport omega).1)
  have hright := sum_centeredFiberMass_Icc_hi_eq_zero
    mu value A (fun omega ↦ (hsupport omega).2)
  have hAbel := abs_sum_log_mul_le_of_prefix_bound
    (centeredFiberMass mu value A) hlo hlohi hE hleft hright hprefix
  rw [sum_log_centeredFiberMass_eq_covariance mu value A hsupport] at hAbel
  exact hAbel

/-- A centered cumulative fiber mass is exactly covariance with the
corresponding prefix indicator.  This identity lets the existing literal
guard-deletion covariance estimate act directly on moving prefixes. -/
theorem sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (A : Omega → ℝ) (k : ℕ) :
    (∑ j ∈ Icc 0 k, centeredFiberMass mu value A j) =
      mu.covariance A (fun omega ↦ if value omega ≤ k then 1 else 0) := by
  rw [sum_centeredFiberMass_eq]
  unfold FiniteProbability.covariance FiniteProbability.expect
  simp only [Finset.mem_Icc, Nat.zero_le, true_and]
  let EA : ℝ := ∑ eta, mu.mass eta * A eta
  let prefixMass : ℝ :=
    ∑ omega, if value omega ≤ k then mu.mass omega else 0
  let markedMass : ℝ :=
    ∑ omega, if value omega ≤ k then
      mu.mass omega * A omega else 0
  have hleft :
      (∑ omega, if value omega ≤ k then
          mu.mass omega * (A omega - EA) else 0) =
        markedMass - EA * prefixMass := by
    dsimp only [markedMass, prefixMass]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k
    · simp [h]
      ring
    · simp [h]
  have hmarked :
      (∑ omega, mu.mass omega *
        (A omega * if value omega ≤ k then 1 else 0)) =
          markedMass := by
    dsimp only [markedMass]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k <;> simp [h]
  have hprefix :
      (∑ omega, mu.mass omega *
        (if value omega ≤ k then 1 else 0)) = prefixMass := by
    dsimp only [prefixMass]
    apply Finset.sum_congr rfl
    intro omega homega
    by_cases h : value omega ≤ k <;> simp [h]
  change
    (∑ omega, if value omega ≤ k then
      mu.mass omega * (A omega - EA) else 0) = _
  rw [hleft, hmarked, hprefix]

end FiniteLogStieltjes

namespace GuardedUniformCell

open FiniteLogStieltjes

variable {Alpha : Type*} [DecidableEq Alpha]

/-- Literal guard deletion preserves a uniform moving-prefix estimate with
the explicit covariance perturbation `12 * KA * deletedMass`.  Thus guard
bookkeeping does not require a separate analytic assumption. -/
theorem exists_deleteGuards_centeredPrefix_bound
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (Kscore : ℝ)
    (hscore : ∀ x, |score x| ≤ Kscore)
    (value : S → ℕ) (A : S → ℝ) {KA E : ℝ}
    (hKA : 0 ≤ KA) (hA : ∀ x, |A x| ≤ KA)
    (hsmallCensus :
      Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ) ≤
        (1 : ℝ) / 2)
    (hprefix : ∀ k,
      |∑ j ∈ Finset.Icc 0 k,
        centeredFiberMass
          ((uniformOnFinset S hS).exponentialTilt score) value A j| ≤ E) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      ∀ k,
        |∑ j ∈ Finset.Icc 0 k,
          centeredFiberMass
            (((uniformOnFinset S hS).exponentialTilt score).deleteGuards
              (guardSubtype S G) hsmall) value A j| ≤
          E + 12 * KA *
            (Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ)) := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  let guards := guardSubtype S G
  let delta := Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ)
  have hmass : mu.guardMass guards ≤ delta := by
    simpa only [mu, guards, delta] using
      tilted_uniform_guardMass_le S G hS score Kscore hscore
  have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
    hmass.trans hsmallCensus
  have hsmall : mu.guardMass guards < 1 := by linarith
  refine ⟨hsmall, ?_⟩
  intro k
  let I : S → ℝ := fun x ↦ if value x ≤ k then 1 else 0
  have hI0 : 0 ≤ (1 : ℝ) := by norm_num
  have hI : ∀ x, |I x| ≤ (1 : ℝ) := by
    intro x
    dsimp only [I]
    split_ifs <;> norm_num
  have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
  have hdiffRaw := mu.abs_deleteGuards_covariance_sub_le
    guards hsmall A I hKA hI0 hA hI
  have hmass0 : 0 ≤ mu.guardMass guards := mu.guardMass_nonneg guards
  have hdelta0 : 0 ≤ delta := by
    dsimp only [delta]
    positivity
  have hdiff :
      |(mu.deleteGuards guards hsmall).covariance A I -
          mu.covariance A I| ≤ 12 * KA * delta := by
    calc
      |(mu.deleteGuards guards hsmall).covariance A I -
          mu.covariance A I| ≤
        3 * KA * 1 * mu.guardPerturbation guards := hdiffRaw
      _ ≤ 3 * KA * 1 * (4 * mu.guardMass guards) := by
        exact mul_le_mul_of_nonneg_left hperturb
          (mul_nonneg (mul_nonneg (by norm_num) hKA) (by norm_num))
      _ ≤ 3 * KA * 1 * (4 * delta) := by
        apply mul_le_mul_of_nonneg_left
        · exact mul_le_mul_of_nonneg_left hmass (by norm_num)
        · positivity
      _ = 12 * KA * delta := by ring
  have hbase : |mu.covariance A I| ≤ E := by
    rw [← sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
    simpa only [mu, I] using hprefix k
  have hdeleted :
      |(mu.deleteGuards guards hsmall).covariance A I| ≤
        12 * KA * delta + E := by
    calc
      |(mu.deleteGuards guards hsmall).covariance A I| ≤
        |(mu.deleteGuards guards hsmall).covariance A I -
            mu.covariance A I| + |mu.covariance A I| := by
          have h := abs_add_le
            ((mu.deleteGuards guards hsmall).covariance A I -
              mu.covariance A I) (mu.covariance A I)
          simpa only [sub_add_cancel] using h
      _ ≤ 12 * KA * delta + E := add_le_add hdiff hbase
  rw [sum_centeredFiberMass_Icc_eq_covariance_prefixIndicator]
  simpa only [I, mu, guards, delta, add_comm] using hdeleted

/-- The corresponding expectation perturbation with the guard census
inserted.  Applied to a bounded truncated valuation, this is the exact guard
term in the pairwise component-mean comparison. -/
theorem exists_deleteGuards_expect_bound
    (S G : Finset Alpha) (hS : S.Nonempty)
    (score : S → ℝ) (Kscore : ℝ)
    (hscore : ∀ x, |score x| ≤ Kscore)
    (F : S → ℝ) {KF : ℝ} (hKF : 0 ≤ KF)
    (hF : ∀ x, |F x| ≤ KF)
    (hsmallCensus :
      Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ) ≤
        (1 : ℝ) / 2) :
    ∃ hsmall :
        ((uniformOnFinset S hS).exponentialTilt score).guardMass
          (guardSubtype S G) < 1,
      |(((uniformOnFinset S hS).exponentialTilt score).deleteGuards
          (guardSubtype S G) hsmall).expect F -
        ((uniformOnFinset S hS).exponentialTilt score).expect F| ≤
        4 * KF *
          (Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ)) := by
  let mu := (uniformOnFinset S hS).exponentialTilt score
  let guards := guardSubtype S G
  let delta := Real.exp (2 * Kscore) * (G.card : ℝ) / (S.card : ℝ)
  have hmass : mu.guardMass guards ≤ delta := by
    simpa only [mu, guards, delta] using
      tilted_uniform_guardMass_le S G hS score Kscore hscore
  have hhalf : mu.guardMass guards ≤ (1 : ℝ) / 2 :=
    hmass.trans hsmallCensus
  have hsmall : mu.guardMass guards < 1 := by linarith
  refine ⟨hsmall, ?_⟩
  have hraw := mu.abs_deleteGuards_expect_sub_le guards hsmall F hKF hF
  have hperturb := mu.guardPerturbation_le_four_mul_guardMass guards hhalf
  calc
    |(mu.deleteGuards guards hsmall).expect F - mu.expect F| ≤
      KF * mu.guardPerturbation guards := hraw
    _ ≤ KF * (4 * mu.guardMass guards) :=
      mul_le_mul_of_nonneg_left hperturb hKF
    _ ≤ KF * (4 * delta) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmass (by norm_num)) hKF
    _ = 4 * KF * delta := by ring

end GuardedUniformCell

namespace PrimePowerTail

open Finset

variable {Omega : Type*} [Fintype Omega]

/-- A reciprocal divisor bound controls the literal valuation tail beyond
an arbitrary exponent cutoff.  This is a finite theorem: the valuation is
first expanded only up to the common endpoint `M`, and the remaining finite
geometric sum is then bounded by its infinite tail. -/
theorem abs_expect_valuation_sub_cutoff_le_of_divisor_fallback
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    {M p Kcut : ℕ} {G : ℝ}
    (hp : p.Prime) (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M) (hcut : Kcut ≤ M)
    (hG : 0 ≤ G)
    (hdiv : ∀ D : ℕ, 0 < D →
      mu.expect (fun omega ↦ divInd D (value omega)) ≤
        G * (1 / (D : ℝ))) :
    |mu.expect (fun omega ↦
        valuation p (value omega) -
          ∑ k ∈ positiveExponents Kcut,
            divInd (p ^ k) (value omega))| ≤
      G * (2 / (p : ℝ) ^ (Kcut + 1)) := by
  have hsplit (f : ℕ → ℝ) :
      (∑ k ∈ positiveExponents M, f k) =
        (∑ k ∈ positiveExponents Kcut, f k) +
          ∑ k ∈ Icc (Kcut + 1) M, f k := by
    have hsets : Icc 1 M = Icc 1 Kcut ∪ Icc (Kcut + 1) M := by
      ext k
      simp only [mem_Icc, mem_union]
      omega
    have hdisjoint : Disjoint (Icc 1 Kcut) (Icc (Kcut + 1) M) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      simp only [mem_Icc] at hk hk'
      omega
    unfold positiveExponents
    rw [hsets, Finset.sum_union hdisjoint]
  have hpoint :
      (fun omega ↦ valuation p (value omega) -
        ∑ k ∈ positiveExponents Kcut,
          divInd (p ^ k) (value omega)) =
      fun omega ↦ ∑ k ∈ Icc (Kcut + 1) M,
        divInd (p ^ k) (value omega) := by
    funext omega
    rw [valuation_eq_sum_divInd_of_le hp
      (hvaluePos omega) (hvalueLe omega), hsplit]
    ring
  have hterm0 (k : ℕ) :
      0 ≤ mu.expect (fun omega ↦ divInd (p ^ k) (value omega)) :=
    mu.expect_nonneg _ (fun omega ↦ divInd_nonneg _ _)
  rw [hpoint, PrimePowerCutoffCovariance.FiniteProbability.expect_sum]
  rw [abs_of_nonneg (Finset.sum_nonneg fun k hk ↦ hterm0 k)]
  calc
    (∑ k ∈ Icc (Kcut + 1) M,
        mu.expect (fun omega ↦ divInd (p ^ k) (value omega))) ≤
      ∑ k ∈ Icc (Kcut + 1) M,
        G * (1 / ((p ^ k : ℕ) : ℝ)) := by
          apply Finset.sum_le_sum
          intro k hk
          exact hdiv (p ^ k) (pow_pos hp.pos k)
    _ = G * (∑ k ∈ Icc (Kcut + 1) M,
        1 / ((p ^ k : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
    _ ≤ G * (2 / (p : ℝ) ^ (Kcut + 1)) := by
          exact mul_le_mul_of_nonneg_left
            (LocalFugacityBounds.sum_inv_pow_tail_le
              (p := p) (r := Kcut) (A := M) hp.two_le) hG

end PrimePowerTail

namespace PaperBridgeFit

open ArithmeticBandGeometry FiniteLogStieltjes

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The literal arbitrary-divisor estimate already proved for the medium
cell law controls its valuation tail past any exponent cutoff.  In
particular, the beyond-cutoff tail is not an additional marked-cell input. -/
theorem abs_cellMediumLaw_expect_valuation_sub_cutoff_le_of_census
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A : ℝ} {p Kcut : ℕ}
    (hp : p.Prime) (hcut : Kcut ≤ B.sampleEndpoint)
    (hA : 0 ≤ A) (hW : 1 < B.sampleData.W) (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A) :
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    |(B.cellMediumLaw xi c).expect (fun m ↦
        valuation p (m : ℕ) -
          ∑ k ∈ positiveExponents Kcut,
            divInd (p ^ k) (m : ℕ))| ≤
      G * (2 / (p : ℝ) ^ (Kcut + 1)) := by
  dsimp only
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hvaluePos : ∀ m : B.sampleData.SampleAt c, 0 < (m : ℕ) := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sampleData.value_pos sample
  have hvalueLe : ∀ m : B.sampleData.SampleAt c,
      (m : ℕ) ≤ B.sampleEndpoint := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    simpa only [sample, StructuredSampleData.value] using
      B.sample_value_le_endpoint sample
  have hG : 0 ≤ G := div_nonneg (Real.exp_pos _).le hrho.le
  have hdiv (D : ℕ) (hD : 0 < D) :
      (B.cellMediumLaw xi c).expect (fun m ↦ divInd D (m : ℕ)) ≤
        G * (1 / (D : ℝ)) := by
    have hraw := B.cellMediumLaw_expect_divInd_le xi c
      hD hA hW hrho hcard heta
    dsimp only [G]
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
          (rho * (D : ℝ)) := hraw
      _ = Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) / rho *
          (1 / (D : ℝ)) := by ring
  exact PrimePowerTail.abs_expect_valuation_sub_cutoff_le_of_divisor_fallback
    (B.cellMediumLaw xi c) (fun m ↦ (m : ℕ)) hp hvaluePos hvalueLe
      hcut hG hdiv

/-- At the logarithmic cutoff associated with an integer threshold `T`, the
same tail is at most `2G/T`.  Taking `T = yNat n ^ 4` leaves only the
elementary paper-scale comparison `p L / yNat^4 = o(1)` in order to obtain
the requested `1/(pL)` rate. -/
theorem abs_cellMediumLaw_expect_valuation_sub_logCutoff_le_of_census
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head)
    {rho A : ℝ} {p T : ℕ}
    (hp : p.Prime) (hT : 0 < T)
    (hcut : Nat.log p T ≤ B.sampleEndpoint)
    (hA : 0 ≤ A) (hW : 1 < B.sampleData.W) (hrho : 0 < rho)
    (hcard : rho * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A) :
    let G := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho
    |(B.cellMediumLaw xi c).expect (fun m ↦
        valuation p (m : ℕ) -
          ∑ k ∈ positiveExponents (Nat.log p T),
            divInd (p ^ k) (m : ℕ))| ≤
      G * (2 / (T : ℝ)) := by
  dsimp only
  let G := Real.exp (2 * ((A / B.L) *
    (Real.log (B.sampleData.hi c.2 : ℝ) /
      Real.log (B.sampleData.W : ℝ)))) / rho
  have hraw := B.abs_cellMediumLaw_expect_valuation_sub_cutoff_le_of_census
    xi c hp hcut hA hW hrho hcard heta
  have hG : 0 ≤ G := div_nonneg (Real.exp_pos _).le hrho.le
  have hpowNat : T < p ^ (Nat.log p T + 1) := by
    simpa only [Nat.succ_eq_add_one] using
      Nat.lt_pow_succ_log_self hp.one_lt T
  have hpow : (T : ℝ) ≤ (p : ℝ) ^ (Nat.log p T + 1) := by
    exact_mod_cast hpowNat.le
  have hTreal : (0 : ℝ) < T := by exact_mod_cast hT
  have hrecip : 2 / (p : ℝ) ^ (Nat.log p T + 1) ≤ 2 / (T : ℝ) := by
    exact div_le_div_of_nonneg_left (by norm_num) hTreal hpow
  calc
    |(B.cellMediumLaw xi c).expect (fun m ↦
        valuation p (m : ℕ) -
          ∑ k ∈ positiveExponents (Nat.log p T),
            divInd (p ^ k) (m : ℕ))| ≤
      G * (2 / (p : ℝ) ^ (Nat.log p T + 1)) := by
        simpa only [G] using hraw
    _ ≤ G * (2 / (T : ℝ)) :=
      mul_le_mul_of_nonneg_left hrecip hG

/-- Literal specialization of finite Stieltjes summation to one actual
medium-prime bridge component.  The premise is exactly the centered moving
prefix estimate which the marked-cell/PNT argument must supply; the
conclusion is already the paper's physical statistic, not an abstract test
function. -/
theorem abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) (p : ℕ) {E : ℝ}
    (hlo : 0 < B.sampleData.lo c.2) (hE : 0 ≤ E)
    (hprefix : ∀ t ∈ Set.Ioc
        (B.sampleData.lo c.2 : ℝ) (B.sampleData.hi c.2 : ℝ),
      |∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
        FiniteLogStieltjes.centeredFiberMass
          (B.cellMediumLaw xi c) (fun m ↦ (m : ℕ))
            (fun m ↦ valuation p (m : ℕ)) k| ≤ E) :
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      (E / (B.sampleData.lo c.2 : ℝ)) *
        ((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) := by
  let mu := B.cellMediumLaw xi c
  let value : B.sampleData.SampleAt c → ℕ := fun m ↦ (m : ℕ)
  let V : B.sampleData.SampleAt c → ℝ :=
    fun m ↦ valuation p (m : ℕ)
  have hsupport : ∀ m : B.sampleData.SampleAt c,
      B.sampleData.lo c.2 < value m ∧
        value m ≤ B.sampleData.hi c.2 := by
    intro m
    let sample : B.sampleData.Sample := ⟨c, m⟩
    exact ⟨by
      simpa only [value, sample, StructuredSampleData.value,
        StructuredSampleData.cellOf] using B.sampleData.lo_lt_value sample,
      by
      simpa only [value, sample, StructuredSampleData.value,
        StructuredSampleData.cellOf] using B.sampleData.value_le_hi sample⟩
  have hlohi : B.sampleData.lo c.2 ≤ B.sampleData.hi c.2 := by
    let m : B.sampleData.SampleAt c :=
      ⟨(B.sampleData.cellFinset c).min' (B.sampleData.cell_nonempty c),
        Finset.min'_mem _ _⟩
    exact (hsupport m).1.le.trans (hsupport m).2
  have hlog := FiniteLogStieltjes.abs_covariance_log_le_of_centeredPrefix
    mu value V hlo hlohi hE hsupport (by
      simpa only [mu, value, V] using hprefix)
  have hnR : (B.sampleData.n : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt B.n_gt_one))
  have hphysicalPoint :
      (fun m : B.sampleData.SampleAt c ↦ B.physicalScore ⟨c, m⟩) =
        fun m ↦ Real.log (value m : ℝ) -
          Real.log (B.sampleData.n : ℝ) := by
    funext m
    have hmR : (value m : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hlo.trans (hsupport m).1))
    unfold physicalScore
    change Real.log ((value m : ℝ) / (B.sampleData.n : ℝ)) = _
    rw [Real.log_div hmR hnR]
  rw [hphysicalPoint,
    FiniteProbability.covariance_sub_const_right]
  simpa only [mu, value, V] using hlog

/-- A physical-interval ratio converts the raw Abel bound into the exact
`constant / (p L)` form used by the nuisance Schur row. -/
theorem abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix_rate
    [Nonempty Head]
    (xi : B.ParamSpace) (c : Cell Head) {p : ℕ}
    {Cprefix Kspan Lscale : ℝ}
    (hp : 0 < p) (hCprefix : 0 ≤ Cprefix)
    (hLscale : 0 < Lscale) (hlo : 0 < B.sampleData.lo c.2)
    (hspan :
      ((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) /
          (B.sampleData.lo c.2 : ℝ) ≤ Kspan)
    (hprefix : ∀ t ∈ Set.Ioc
        (B.sampleData.lo c.2 : ℝ) (B.sampleData.hi c.2 : ℝ),
      |∑ k ∈ Finset.Icc 0 ⌊t⌋₊,
        FiniteLogStieltjes.centeredFiberMass
          (B.cellMediumLaw xi c) (fun m ↦ (m : ℕ))
            (fun m ↦ valuation p (m : ℕ)) k| ≤
        (Cprefix / Lscale) * (1 / (p : ℝ))) :
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      ((Kspan * Cprefix) / Lscale) * (1 / (p : ℝ)) := by
  have hE : 0 ≤ (Cprefix / Lscale) * (1 / (p : ℝ)) := by
    positivity
  have hraw :=
    B.abs_cellMediumLaw_covariance_valuation_physical_le_of_prefix
      xi c p hlo hE hprefix
  have hloR : (0 : ℝ) < B.sampleData.lo c.2 := by exact_mod_cast hlo
  have hspan0 : 0 ≤
      ((B.sampleData.hi c.2 : ℝ) -
        (B.sampleData.lo c.2 : ℝ)) := by
    have hle : B.sampleData.lo c.2 ≤ B.sampleData.hi c.2 := by
      obtain ⟨m, hm⟩ := B.sampleData.cell_nonempty c
      have hmCell := (Finset.mem_sdiff.mp hm).1
      exact (StructuredCells.mem_smoothInterval.mp
        (StructuredCells.mem_structuredCell.mp hmCell).1).1.le.trans
          (StructuredCells.mem_smoothInterval.mp
            (StructuredCells.mem_structuredCell.mp hmCell).1).2.1
    exact sub_nonneg.mpr (by exact_mod_cast hle)
  calc
    |(B.cellMediumLaw xi c).covariance
        (fun m ↦ valuation p (m : ℕ))
        (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
      (((Cprefix / Lscale) * (1 / (p : ℝ))) /
          (B.sampleData.lo c.2 : ℝ)) *
        ((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) := hraw
    _ = ((Cprefix / Lscale) * (1 / (p : ℝ))) *
        (((B.sampleData.hi c.2 : ℝ) -
          (B.sampleData.lo c.2 : ℝ)) /
            (B.sampleData.lo c.2 : ℝ)) := by ring
    _ ≤ ((Cprefix / Lscale) * (1 / (p : ℝ))) * Kspan := by
      exact mul_le_mul_of_nonneg_left hspan hE
    _ = ((Kspan * Cprefix) / Lscale) * (1 / (p : ℝ)) := by ring

/-- Exact componentwise prime-power summation for the literal medium law.
The common main profile cancels before any inequalities are taken. -/
theorem abs_cellMediumLaw_expect_valuation_sub_other_of_power_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) (c c' : Cell Head)
    {p Kcut : ℕ} (main error : ℕ → ℝ) {tailError : ℝ}
    (hprofile : ∀ (d : Cell Head) k,
      k ∈ positiveExponents Kcut →
      |(B.cellMediumLaw xi d).expect
          (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| ≤ error k)
    (htail : ∀ d : Cell Head,
      |(B.cellMediumLaw xi d).expect
          (fun m ↦ valuation p (m : ℕ) -
            ∑ k ∈ positiveExponents Kcut,
              divInd (p ^ k) (m : ℕ))| ≤ tailError) :
    |(B.cellMediumLaw xi c).expect (fun m ↦ valuation p (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      2 * (∑ k ∈ positiveExponents Kcut, error k) + 2 * tailError := by
  let mu : ∀ d : Cell Head,
      FiniteProbability (B.sampleData.SampleAt d) :=
    fun d ↦ B.cellMediumLaw xi d
  let trunc (d : Cell Head) : ℝ :=
    (mu d).expect (fun m ↦
      ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ))
  let tail (d : Cell Head) : ℝ :=
    (mu d).expect (fun m ↦ valuation p (m : ℕ) -
      ∑ k ∈ positiveExponents Kcut, divInd (p ^ k) (m : ℕ))
  have hexpect (d : Cell Head) :
      (mu d).expect (fun m ↦ valuation p (m : ℕ)) =
        trunc d + tail d := by
    have hpoint : (fun m : B.sampleData.SampleAt d ↦
        valuation p (m : ℕ)) =
      fun m : B.sampleData.SampleAt d ↦
        (∑ k ∈ positiveExponents Kcut,
          divInd (p ^ k) (m : ℕ)) +
          (valuation p (m : ℕ) -
            ∑ k ∈ positiveExponents Kcut,
              divInd (p ^ k) (m : ℕ)) := by
      funext m
      ring
    rw [hpoint, (mu d).expect_add]
  have htruncExpand (d : Cell Head) :
      trunc d = ∑ k ∈ positiveExponents Kcut,
        (mu d).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) := by
    exact PrimePowerCutoffCovariance.FiniteProbability.expect_sum (mu d)
      (positiveExponents Kcut) (fun k m ↦ divInd (p ^ k) (m : ℕ))
  have hpower (k : ℕ) (hk : k ∈ positiveExponents Kcut) :
      |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
        (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ))| ≤
          2 * error k := by
    have hc := hprofile c k hk
    have hc' := hprofile c' k hk
    calc
      |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
          (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ))| ≤
        |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| +
          |(mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| := by
        have h := abs_add_le
          ((mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k)
          (main k - (mu c').expect
            (fun m ↦ divInd (p ^ k) (m : ℕ)))
        simpa only [sub_add_sub_cancel, abs_sub_comm] using h
      _ ≤ error k + error k := add_le_add hc hc'
      _ = 2 * error k := by ring
  have htrunc : |trunc c - trunc c'| ≤
      2 * (∑ k ∈ positiveExponents Kcut, error k) := by
    rw [htruncExpand, htruncExpand, ← Finset.sum_sub_distrib]
    calc
      |∑ k ∈ positiveExponents Kcut,
          ((mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
            (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ)))| ≤
        ∑ k ∈ positiveExponents Kcut,
          |(mu c).expect (fun m ↦ divInd (p ^ k) (m : ℕ)) -
            (mu c').expect (fun m ↦ divInd (p ^ k) (m : ℕ))| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ positiveExponents Kcut, 2 * error k := by
        apply Finset.sum_le_sum
        intro k hk
        exact hpower k hk
      _ = 2 * (∑ k ∈ positiveExponents Kcut, error k) := by
        rw [Finset.mul_sum]
  have htailPair : |tail c - tail c'| ≤ 2 * tailError := by
    calc
      |tail c - tail c'| ≤ |tail c| + |tail c'| := abs_sub _ _
      _ ≤ tailError + tailError := add_le_add (htail c) (htail c')
      _ = 2 * tailError := by ring
  change |(mu c).expect (fun m ↦ valuation p (m : ℕ)) -
    (mu c').expect (fun m ↦ valuation p (m : ℕ))| ≤ _
  rw [hexpect, hexpect]
  calc
    |trunc c + tail c - (trunc c' + tail c')| =
        |(trunc c - trunc c') + (tail c - tail c')| := by ring_nf
    _ ≤ |trunc c - trunc c'| + |tail c - tail c'| := abs_add_le _ _
    _ ≤ 2 * (∑ k ∈ positiveExponents Kcut, error k) +
        2 * tailError := add_le_add htrunc htailPair

/-- Reciprocal specialization of the preceding exact sum.  The elementary
geometric series is explicit, so the only remaining analytic statements are
the pointwise power profile and the beyond-cutoff valuation tail. -/
theorem abs_cellMediumLaw_expect_valuation_sub_other_of_reciprocal_profiles
    [Nonempty Head]
    (xi : B.ParamSpace) (c c' : Cell Head)
    {p Kcut : ℕ} (main : ℕ → ℝ)
    {Cpower Ctail Lscale : ℝ}
    (hp : p.Prime) (hCpower : 0 ≤ Cpower)
    (hLscale : 0 < Lscale)
    (hprofile : ∀ (d : Cell Head) k,
      k ∈ positiveExponents Kcut →
      |(B.cellMediumLaw xi d).expect
          (fun m ↦ divInd (p ^ k) (m : ℕ)) - main k| ≤
        (Cpower / Lscale) * (1 / ((p ^ k : ℕ) : ℝ)))
    (htail : ∀ d : Cell Head,
      |(B.cellMediumLaw xi d).expect
          (fun m ↦ valuation p (m : ℕ) -
            ∑ k ∈ positiveExponents Kcut,
              divInd (p ^ k) (m : ℕ))| ≤
        (Ctail / Lscale) * (1 / (p : ℝ))) :
    |(B.cellMediumLaw xi c).expect (fun m ↦ valuation p (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      ((4 * Cpower + 2 * Ctail) / Lscale) * (1 / (p : ℝ)) := by
  let error : ℕ → ℝ := fun k ↦
    (Cpower / Lscale) * (1 / ((p ^ k : ℕ) : ℝ))
  have hbase :=
    B.abs_cellMediumLaw_expect_valuation_sub_other_of_power_profiles
      xi c c' main error hprofile htail
  have hcoef0 : 0 ≤ Cpower / Lscale := div_nonneg hCpower hLscale.le
  have hsum : (∑ k ∈ positiveExponents Kcut, error k) ≤
      (Cpower / Lscale) * (2 / (p : ℝ)) := by
    dsimp only [error]
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left
      (by
        simpa only [positiveExponents, zero_add, pow_one, Nat.cast_pow] using
          (LocalFugacityBounds.sum_inv_pow_tail_le
            (p := p) (r := 0) (A := Kcut) hp.two_le)) hcoef0
  calc
    |(B.cellMediumLaw xi c).expect (fun m ↦ valuation p (m : ℕ)) -
        (B.cellMediumLaw xi c').expect
          (fun m ↦ valuation p (m : ℕ))| ≤
      2 * (∑ k ∈ positiveExponents Kcut, error k) +
        2 * ((Ctail / Lscale) * (1 / (p : ℝ))) := hbase
    _ ≤ 2 * ((Cpower / Lscale) * (2 / (p : ℝ))) +
        2 * ((Ctail / Lscale) * (1 / (p : ℝ))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left hsum (by norm_num)) le_rfl
    _ = ((4 * Cpower + 2 * Ctail) / Lscale) *
        (1 / (p : ℝ)) := by ring

end BridgeData

end PaperBridgeFit

end

end Erdos390.Full
