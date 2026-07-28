import Erdos390.Full.RegularRelativeMesh
import Erdos390.Full.PrimeIntervalPartitionConstructor
import Mathlib.NumberTheory.Bertrand

/-!
# Explicit natural prime cutoffs from the regular relative mesh

The continuum endpoints are converted to natural endpoints by
`floor (exp(t log y))`.  This file proves monotonicity, identifies the last
cutoff with the paper's `floor y`, and uses Bertrand's postulate to populate
every cell once the explicit scale-separation inequalities hold.
-/

open Filter

namespace Erdos390.Full.RegularMeshPrimeCutoffs

noncomputable section

open ArithmeticModel RegularRelativeMesh
open PrimeIntervalPartitionConstructor PositiveCellTransfer

/-- The positive number whose logarithmic coordinate is `t`. -/
def scalePoint (n : ℕ) (t : ℝ) : ℝ :=
  Real.exp (t * Real.log (y n))

/-- Natural cutoffs for one low cell followed by the positive geometric
cells. -/
def fullCutoff {delta eta : ℝ} (M : Mesh delta eta)
    (n W : ℕ) : ℕ → ℕ
  | 0 => W
  | k + 1 => ⌊M.endpoint k |> scalePoint n⌋₊

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

theorem endpoint_mono (hdelta : 0 < delta) : Monotone M.endpoint := by
  intro a b hab
  unfold RegularRelativeMesh.Mesh.endpoint
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ (by linarith [M.ratio_pos]) hab) hdelta.le

theorem fullCutoff_zero (n W : ℕ) :
    fullCutoff M n W 0 = W := rfl

theorem fullCutoff_succ (n W k : ℕ) :
    fullCutoff M n W (k + 1) = ⌊scalePoint n (M.endpoint k)⌋₊ := rfl

/-- The final explicit cutoff is exactly `floor y`. -/
theorem fullCutoff_last {n W : ℕ} (hn : 0 < n) :
    fullCutoff M n W (M.cellCount + 1) = yNat n := by
  rw [fullCutoff_succ M, M.endpoint_cellCount]
  unfold scalePoint yNat
  simp only [one_mul, Real.exp_log (Scale.y_pos hn)]

/-- Monotonicity of all explicit cutoffs, including the junction from the
fixed cutoff `W` to the moving low-cell endpoint. -/
theorem fullCutoff_monotone
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n)
    (hW : W ≤ fullCutoff M n W 1) :
    Monotone (fullCutoff M n W) := by
  have hylog : 0 ≤ Real.log (y n) := by
    have hyOne : 1 < y n := by
      have hlog : 0 < Real.log (y n) := by
        rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
        exact mul_pos (by norm_num)
          (Real.log_pos (by exact_mod_cast hn))
      exact (Real.log_pos_iff (Scale.y_pos
        (Nat.zero_lt_of_lt hn)).le).mp hlog
    exact (Real.log_pos hyOne).le
  intro a b hab
  cases a with
  | zero =>
      cases b with
      | zero => exact le_rfl
      | succ b =>
          calc
            fullCutoff M n W 0 ≤ fullCutoff M n W 1 := hW
            _ ≤ fullCutoff M n W (b + 1) := by
              rw [fullCutoff_succ M, fullCutoff_succ M]
              apply Nat.floor_mono
              unfold scalePoint
              rw [Real.exp_le_exp]
              exact mul_le_mul_of_nonneg_right
                (endpoint_mono M hdelta (Nat.zero_le b)) hylog
  | succ a =>
      cases b with
      | zero => omega
      | succ b =>
          have hab' : a ≤ b := by omega
          rw [fullCutoff_succ M, fullCutoff_succ M]
          apply Nat.floor_mono
          unfold scalePoint
          rw [Real.exp_le_exp]
          exact mul_le_mul_of_nonneg_right
            (endpoint_mono M hdelta hab') hylog

end Mesh

/-- Bertrand's postulate populates a floored interval whenever the upper
real endpoint is at least twice the lower one. -/
theorem exists_prime_between_floors
    {x z : ℝ} (hx : 1 ≤ x) (hdouble : 2 * x ≤ z) :
    ∃ p : ℕ, p.Prime ∧ ⌊x⌋₊ < p ∧ p ≤ ⌊z⌋₊ := by
  have hfloorOne : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by
    exact_mod_cast hx)
  obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
    Nat.exists_prime_lt_and_le_two_mul ⌊x⌋₊ (by omega)
  refine ⟨p, hpPrime, hpLower, hpUpper.trans ?_⟩
  apply Nat.le_floor
  have hfloorLe : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (by positivity)
  calc
    ((2 * ⌊x⌋₊ : ℕ) : ℝ) = 2 * (⌊x⌋₊ : ℝ) := by norm_num
    _ ≤ 2 * x := mul_le_mul_of_nonneg_left hfloorLe (by norm_num)
    _ ≤ z := hdouble

/-- Explicit scale conditions under which all natural mesh cells contain a
prime.  These inequalities are proved eventually below; they are displayed
here to keep the finite Bertrand step transparent. -/
structure ScaleSeparation {delta eta : ℝ} (M : Mesh delta eta)
    (n W : ℕ) : Prop where
  low : (2 * W : ℝ) ≤ scalePoint n delta
  positive : ∀ k : Fin M.cellCount,
    1 ≤ scalePoint n (M.lower k) ∧
      2 * scalePoint n (M.lower k) ≤ scalePoint n (M.upper k)

namespace Mesh

variable {delta eta : ℝ} (M : Mesh delta eta)

/-- Every consecutive explicit cutoff interval contains a genuine prime. -/
theorem every_fullCutoff_cell_has_prime
    {n W : ℕ} (hW : W ≠ 0)
    (S : ScaleSeparation M n W) :
    ∀ j : Fin (M.cellCount + 1), ∃ p : ℕ,
      p.Prime ∧ fullCutoff M n W j.1 < p ∧
        p ≤ fullCutoff M n W (j.1 + 1) := by
  intro j
  by_cases hj : j.1 = 0
  · have hfloor : (2 * W : ℕ) ≤ ⌊scalePoint n delta⌋₊ := by
      apply Nat.le_floor
      exact_mod_cast S.low
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      Nat.exists_prime_lt_and_le_two_mul W hW
    refine ⟨p, hpPrime, ?_, ?_⟩
    · simpa only [hj, fullCutoff_zero M] using hpLower
    · have hp := hpUpper.trans hfloor
      have hendpoint : M.endpoint 0 = delta := M.endpoint_zero
      simpa only [hj, Nat.zero_add, fullCutoff_succ M, hendpoint] using hp
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hj
    have hklt : k < M.cellCount := by omega
    let q : Fin M.cellCount := ⟨k, hklt⟩
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ :=
      exists_prime_between_floors (S.positive q).1 (S.positive q).2
    refine ⟨p, hpPrime, ?_, ?_⟩
    · simpa only [hk, fullCutoff_succ M,
        RegularRelativeMesh.Mesh.lower] using hpLower
    · have hsucc : j.1 + 1 = k + 1 + 1 := by omega
      rw [hsucc, fullCutoff_succ M]
      simpa only [RegularRelativeMesh.Mesh.upper] using hpUpper

/-- The explicit cutoffs therefore construct the actual arithmetic
partition and its interval certificate. -/
theorem exists_partition_and_certificate
    {n W : ℕ} (hdelta : 0 < delta) (hn : 1 < n) (hW : W ≠ 0)
    (S : ScaleSeparation M n W) :
    ∃ P : ArithmeticBandGeometry.Partition n W (Fin (M.cellCount + 1)),
      ∃ E : IntervalCertificate P,
        (∀ j, E.lower j = fullCutoff M n W j.1) ∧
        (∀ j, E.upper j = fullCutoff M n W (j.1 + 1)) := by
  let cut := fullCutoff M n W
  have hWcut : W ≤ cut 1 := by
    apply Nat.le_floor
    have htwo : (W : ℝ) ≤ (2 * W : ℝ) := by
      have hWnonneg : (0 : ℝ) ≤ (W : ℝ) := by positivity
      linarith
    have hscale : (W : ℝ) ≤ scalePoint n delta := htwo.trans S.low
    simpa only [cut, fullCutoff, M.endpoint_zero] using hscale
  have hmono : Monotone cut := fullCutoff_monotone M
    hdelta hn (by simpa only [cut] using hWcut)
  have hzero : cut 0 = W := rfl
  have hlast : cut (M.cellCount + 1) = yNat n :=
    fullCutoff_last M (Nat.zero_lt_of_lt hn)
  have hprime := every_fullCutoff_cell_has_prime M hW S
  have hK : 0 < M.cellCount + 1 := by omega
  let P := PrimeIntervalPartitionConstructor.partition
    hK cut hmono hzero hlast hprime
  let E := PrimeIntervalPartitionConstructor.intervalCertificate
    hK cut hmono hzero hlast hprime
  refine ⟨P, E, ?_, ?_⟩
  · intro j
    rfl
  · intro j
    rfl

end Mesh

end

end Erdos390.Full.RegularMeshPrimeCutoffs
