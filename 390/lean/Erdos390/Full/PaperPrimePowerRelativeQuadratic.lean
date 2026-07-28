import Erdos390.Full.PaperActualCompensatedRegression
import Erdos390.Full.PaperPrimePowerLemma75

/-!
# Relative prime-power quadratic transfer for Lemma 8.6

Lemma 7.5 supplies a genuine weighted row estimate for the difference
between full valuation covariance and squarefree covariance.  This file
proves, by finite summation, that the row estimate gives an error at the
relative `w^2` scale for the actual compensated coefficient vector.  The
proof does not replace `sum |Cov|` by `|sum Cov|`.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRelativeQuadratic

open ArithmeticModel PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75

noncomputable section

variable {Omega : Type*} [Fintype Omega] {M : ℕ}

/-- Full-valuation covariance quadratic form on a finite prime set. -/
def fullValuationQuadratic
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, c p * c q * law.covVV p q

/-- Squarefree covariance quadratic form on the same finite prime set. -/
def squarefreeQuadratic
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) : ℝ :=
  ∑ p ∈ S, ∑ q ∈ S, c p * c q * law.covII p q

theorem full_sub_squarefree_eq
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    fullValuationQuadratic law S c - squarefreeQuadratic law S c =
      ∑ p ∈ S, ∑ q ∈ S,
        c p * c q * (law.covVV p q - law.covII p q) := by
  unfold fullValuationQuadratic squarefreeQuadratic
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem fullValuationQuadratic_eq_covariance
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    fullValuationQuadratic law S c =
      law.probability.covariance
        (fun omega ↦ ∑ p ∈ S, c p * law.V p omega)
        (fun omega ↦ ∑ p ∈ S, c p * law.V p omega) := by
  rw [law.probability.covariance_sum_left]
  unfold fullValuationQuadratic covVV
  apply Finset.sum_congr rfl
  intro p hp
  rw [law.probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_left,
    law.probability.covariance_smul_right]
  ring

theorem squarefreeQuadratic_eq_covariance
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) :
    squarefreeQuadratic law S c =
      law.probability.covariance
        (fun omega ↦ ∑ p ∈ S, c p * law.I p omega)
        (fun omega ↦ ∑ p ∈ S, c p * law.I p omega) := by
  rw [law.probability.covariance_sum_left]
  unfold squarefreeQuadratic covII
  apply Finset.sum_congr rfl
  intro p hp
  rw [law.probability.covariance_sum_right]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_left,
    law.probability.covariance_smul_right]
  ring

/-- A weighted row bound and the literal coefficient `L∞`/`L¹` bounds imply
a relative quadratic error. -/
theorem abs_full_sub_squarefree_le_of_row
    (law : BoundedValuationLaw Omega M)
    {n W : ℕ} (c : ℕ → ℝ) {Csup CL1 w R : ℝ}
    (hCsup : 0 ≤ Csup) (hCL1 : 0 ≤ CL1)
    (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hcSup : ∀ p ∈ primeBand n W, |c p| ≤ Csup * w)
    (hcL1 : (∑ p ∈ primeBand n W,
      |c p| * (1 / (p : ℝ))) ≤ CL1 * w)
    (hrow : ∀ p ∈ primeBand n W,
      (p : ℝ) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| ≤ R) :
    |fullValuationQuadratic law (primeBand n W) c -
        squarefreeQuadratic law (primeBand n W) c| ≤
      (Csup * CL1) * R * w ^ 2 := by
  have hCw : 0 ≤ Csup * w := mul_nonneg hCsup hw
  have hLw : 0 ≤ CL1 * w := mul_nonneg hCL1 hw
  rw [full_sub_squarefree_eq]
  calc
    |∑ p ∈ primeBand n W, ∑ q ∈ primeBand n W,
        c p * c q * (law.covVV p q - law.covII p q)| ≤
        ∑ p ∈ primeBand n W,
          |∑ q ∈ primeBand n W,
            c p * c q * (law.covVV p q - law.covII p q)| := by
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ primeBand n W,
        |c p| * (Csup * w) *
          (∑ q ∈ primeBand n W,
            |law.covVV p q - law.covII p q|) := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        |∑ q ∈ primeBand n W,
            c p * c q * (law.covVV p q - law.covII p q)| ≤
            ∑ q ∈ primeBand n W,
              |c p * c q * (law.covVV p q - law.covII p q)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ q ∈ primeBand n W,
            |c p| * |c q| *
              |law.covVV p q - law.covII p q| := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [abs_mul, abs_mul]
        _ ≤ ∑ q ∈ primeBand n W,
            |c p| * (Csup * w) *
              |law.covVV p q - law.covII p q| := by
          apply Finset.sum_le_sum
          intro q hq
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hcSup q hq) (abs_nonneg _))
            (abs_nonneg _)
        _ = |c p| * (Csup * w) *
            (∑ q ∈ primeBand n W,
              |law.covVV p q - law.covII p q|) := by
          rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ primeBand n W,
        (|c p| * (1 / (p : ℝ))) * (Csup * w) * R := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPosNat : 0 < p := (prime_of_mem_primeBand hp).pos
      have hpPos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpPosNat
      have hrowDiv :
          (∑ q ∈ primeBand n W,
            |law.covVV p q - law.covII p q|) ≤ R / (p : ℝ) := by
        exact (le_div_iff₀ hpPos).2 (by
          simpa only [mul_comm] using hrow p hp)
      have hmult : 0 ≤ |c p| * (Csup * w) :=
        mul_nonneg (abs_nonneg _) hCw
      calc
        |c p| * (Csup * w) *
            (∑ q ∈ primeBand n W,
              |law.covVV p q - law.covII p q|) ≤
            |c p| * (Csup * w) * (R / (p : ℝ)) :=
          mul_le_mul_of_nonneg_left hrowDiv hmult
        _ = (|c p| * (1 / (p : ℝ))) * (Csup * w) * R := by
          field_simp [ne_of_gt hpPos]
    _ = (Csup * w) * R *
        (∑ p ∈ primeBand n W, |c p| * (1 / (p : ℝ))) := by
      rw [← Finset.sum_mul]
      have hfactor :
          (∑ p ∈ primeBand n W,
            |c p| * (1 / (p : ℝ)) * (Csup * w)) =
          (Csup * w) *
            ∑ p ∈ primeBand n W, |c p| * (1 / (p : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
      rw [hfactor]
      ring
    _ ≤ (Csup * w) * R * (CL1 * w) := by
      exact mul_le_mul_of_nonneg_left hcL1
        (mul_nonneg hCw hR)
    _ = (Csup * CL1) * R * w ^ 2 := by ring

/-- Direct specialization of the preceding theorem to the row field of
paper Lemma 7.5. -/
theorem abs_full_sub_squarefree_le_of_lemma75
    (law : BoundedValuationLaw Omega M)
    {n W : ℕ} (c : ℕ → ℝ) {Csup CL1 w Cpow epsilon : ℝ}
    (hCsup : 0 ≤ Csup) (hCL1 : 0 ≤ CL1) (hw : 0 ≤ w)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hcSup : ∀ p ∈ primeBand n W, |c p| ≤ Csup * w)
    (hcL1 : (∑ p ∈ primeBand n W,
      |c p| * (1 / (p : ℝ))) ≤ CL1 * w)
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon) :
    |fullValuationQuadratic law (primeBand n W) c -
        squarefreeQuadratic law (primeBand n W) c| ≤
      (Csup * CL1) *
        (Cpow * (1 / (W : ℝ)) + epsilon) * w ^ 2 := by
  exact abs_full_sub_squarefree_le_of_row law c hCsup hCL1 hw
    (add_nonneg (mul_nonneg hCpow (by positivity)) hepsilon)
    hcSup hcL1 h75.row

/-- The full-valuation marked covariance row paired with a coefficient
vector. -/
def fullMarkedRow
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  law.probability.covariance (law.V p)
    (fun omega ↦ ∑ q ∈ S, c q * law.V q omega)

/-- Squarefree companion to `fullMarkedRow`. -/
def squarefreeMarkedRow
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) (p : ℕ) : ℝ :=
  law.probability.covariance (law.I p)
    (fun omega ↦ ∑ q ∈ S, c q * law.I q omega)

theorem fullMarked_sub_squarefree_eq
    (law : BoundedValuationLaw Omega M) (S : Finset ℕ)
    (c : ℕ → ℝ) (p : ℕ) :
    fullMarkedRow law S c p - squarefreeMarkedRow law S c p =
      ∑ q ∈ S, c q * (law.covVV p q - law.covII p q) := by
  unfold fullMarkedRow squarefreeMarkedRow covVV covII
  rw [law.probability.covariance_sum_right,
    law.probability.covariance_sum_right,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q hq
  rw [law.probability.covariance_smul_right,
    law.probability.covariance_smul_right]
  ring

/-- The genuine Lemma 7.5 row estimate gives the relative marked-prime
prime-power error, uniformly for every marked prime in the actual band. -/
theorem abs_fullMarked_sub_squarefree_le_of_row
    (law : BoundedValuationLaw Omega M)
    {n W : ℕ} (c : ℕ → ℝ) {Csup w R : ℝ}
    (hCsup : 0 ≤ Csup) (hw : 0 ≤ w)
    (hcSup : ∀ q ∈ primeBand n W, |c q| ≤ Csup * w)
    (hrow : ∀ p ∈ primeBand n W,
      (p : ℝ) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| ≤ R)
    {p : ℕ} (hp : p ∈ primeBand n W) :
    |fullMarkedRow law (primeBand n W) c p -
        squarefreeMarkedRow law (primeBand n W) c p| ≤
      Csup * w * R * (1 / (p : ℝ)) := by
  have hpPos : (0 : ℝ) < (p : ℝ) := by
    exact_mod_cast (prime_of_mem_primeBand hp).pos
  have hCw : 0 ≤ Csup * w := mul_nonneg hCsup hw
  rw [fullMarked_sub_squarefree_eq]
  calc
    |∑ q ∈ primeBand n W,
        c q * (law.covVV p q - law.covII p q)| ≤
      ∑ q ∈ primeBand n W,
        |c q * (law.covVV p q - law.covII p q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ q ∈ primeBand n W,
        |c q| * |law.covVV p q - law.covII p q| := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [abs_mul]
    _ ≤ ∑ q ∈ primeBand n W,
        (Csup * w) * |law.covVV p q - law.covII p q| := by
      apply Finset.sum_le_sum
      intro q hq
      exact mul_le_mul_of_nonneg_right (hcSup q hq) (abs_nonneg _)
    _ = (Csup * w) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| := by
      rw [Finset.mul_sum]
    _ ≤ (Csup * w) * (R / (p : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ hCw
      exact (le_div_iff₀ hpPos).2 (by
        simpa only [mul_comm] using hrow p hp)
    _ = Csup * w * R * (1 / (p : ℝ)) := by
      field_simp [ne_of_gt hpPos]

/-- Specialization to the actual Lemma 7.5 transfer package. -/
theorem abs_fullMarked_sub_squarefree_le_of_lemma75
    (law : BoundedValuationLaw Omega M)
    {n W : ℕ} (c : ℕ → ℝ) {Csup w Cpow epsilon : ℝ}
    (hCsup : 0 ≤ Csup) (hw : 0 ≤ w)
    (hcSup : ∀ q ∈ primeBand n W, |c q| ≤ Csup * w)
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand n W) :
    |fullMarkedRow law (primeBand n W) c p -
        squarefreeMarkedRow law (primeBand n W) c p| ≤
      Csup * w *
        (Cpow * (1 / (W : ℝ)) + epsilon) * (1 / (p : ℝ)) := by
  exact abs_fullMarked_sub_squarefree_le_of_row law c hCsup hw hcSup
    h75.row hp

end

end Erdos390.Full.PaperPrimePowerRelativeQuadratic
