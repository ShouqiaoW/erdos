import Erdos390.Full.PrimePowerRowTransfer
import Erdos390.Full.PrimeSums

/-!
# The paper prime-band row contraction

This module specializes the actual finite-law contraction to

* the literal band `primeBand n W`,
* `t_p = log p / log y`,
* reciprocal weight `u_p = 1 / p`,
* row normalization `p`, and
* `invW = 1 / W`.

Thus every elementary prime-coordinate and prime-sum input in the final row
step of paper Lemma 7.5 is discharged here.  The remaining hypotheses are
exactly the actual `JI`, `IJ`, `JJ`, diagonal, and endpoint estimates proved
by the marked four-chamber analysis.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperPrimePowerRow

open ArithmeticModel Scale PrimeSums
open PrimePowerCovariance PrimePowerRowTransfer

noncomputable section

lemma tPrime_nonneg_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    0 <= tPrime n p := by
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y (Nat.zero_lt_of_lt hn)]
    nlinarith
  have hlogp : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast (prime_of_mem_primeBand hp).one_le)
  exact div_nonneg hlogp hlogy.le

lemma tPrime_le_one_of_mem_primeBand
    {n W p : Nat} (hn : 1 < n) (hp : p ∈ primeBand n W) :
    tPrime n p <= 1 := by
  have hn0 : 0 < n := Nat.zero_lt_of_lt hn
  have hL : 0 < L n := L_pos hn
  have hlogy : 0 < Real.log (y n) := by
    rw [log_y hn0]
    nlinarith
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : Real) := by exact_mod_cast hpPrime.pos
  have hyfloor : (yNat n : Real) <= y n :=
    Nat.floor_le (le_of_lt (y_pos hn0))
  have hpcast : (p : Real) <= y n := by
    exact (by exact_mod_cast le_yNat_of_mem_primeBand hp :
      (p : Real) <= (yNat n : Real)).trans hyfloor
  have hlog : Real.log (p : Real) <= Real.log (y n) :=
    Real.log_le_log hp0 hpcast
  unfold tPrime
  calc
    Real.log (p : Real) / Real.log (y n) <=
        Real.log (y n) / Real.log (y n) :=
      div_le_div_of_nonneg_right hlog hlogy.le
    _ = 1 := div_self hlogy.ne'

lemma reciprocalPrime_le_reciprocalCutoff
    {n W p : Nat} (hW : 1 < W) (hp : p ∈ primeBand n W) :
    1 / (p : Real) <= 1 / (W : Real) := by
  apply one_div_le_one_div_of_le (by exact_mod_cast Nat.zero_lt_of_lt hW)
  exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le

lemma reciprocalCutoff_le_one {W : Nat} (hW : 1 < W) :
    1 / (W : Real) <= 1 := by
  have h := one_div_le_one_div_of_le (by norm_num : (0 : Real) < 1)
    (by exact_mod_cast hW.le : (1 : Real) <= (W : Real))
  norm_num at h ⊢
  exact h

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : Nat}
  (law : BoundedValuationLaw Omega M)

set_option maxHeartbeats 800000

/-- Exact paper-band row contraction.  No prime-coordinate or prime-sum
hypothesis remains. -/
theorem paperBand_covVV_sub_covII_row_le
    {n W : Nat} (hn : 1 < n) (hW : 1 < W)
    (C epsilon remRow : Real)
    (rJI rIJ rJJ : Nat -> Nat -> Real) (rD : Nat -> Real)
    (hC : 0 <= C) (hepsilon : 0 <= epsilon)
    (hJI : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      |law.covJI p q| <=
        C * tPrime n p * tPrime n q *
            (1 / (p : Real)) ^ 2 * (1 / (q : Real)) +
          epsilon * (1 / (p : Real)) ^ 2 * (1 / (q : Real)) +
          rJI p q)
    (hIJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      |law.covIJ p q| <=
        C * tPrime n p * tPrime n q *
            (1 / (p : Real)) * (1 / (q : Real)) ^ 2 +
          epsilon * (1 / (p : Real)) * (1 / (q : Real)) ^ 2 +
          rIJ p q)
    (hJJ : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
      |law.covJJ p q| <=
        C * tPrime n p * tPrime n q *
            (1 / (p : Real)) ^ 2 * (1 / (q : Real)) ^ 2 +
          epsilon * (1 / (p : Real)) ^ 2 * (1 / (q : Real)) ^ 2 +
          rJJ p q)
    (hMoment : ∀ p ∈ primeBand n W,
      law.probability.expect (fun omega => law.J p omega ^ 2) <=
        (C + epsilon) * (1 / (p : Real)) ^ 2 + rD p)
    (hRowRem : ∀ p ∈ primeBand n W,
      (p : Real) *
        ((∑ q ∈ (primeBand n W).erase p,
            (rJI p q + rIJ p q + rJJ p q)) + 3 * rD p) <= remRow) :
    ∀ p ∈ primeBand n W,
      (p : Real) * ∑ q ∈ primeBand n W,
        |law.covVV p q - law.covII p q| <=
      C * (bandTReciprocalSum n W + 5) * (1 / (W : Real)) +
        epsilon * (bandReciprocalSum n W + 5) * (1 / (W : Real)) +
        remRow := by
  have hW0 : 0 <= 1 / (W : Real) := by positivity
  have hW1 : 1 / (W : Real) <= 1 := reciprocalCutoff_le_one hW
  have hSquare :
      (∑ q ∈ primeBand n W, (1 / (q : Real)) ^ 2) <=
        1 * (1 / (W : Real)) := by
    simpa only [one_mul, bandReciprocalSquareSum, one_div, inv_pow] using
      bandReciprocalSquareSum_le n W hW.le
  have hrow :=
    PrimePowerRowTransfer.BoundedValuationLaw.covVV_sub_covII_row_le law
    (primeBand n W) (tPrime n) (fun p => 1 / (p : Real))
    (fun p => (p : Real)) C epsilon (1 / (W : Real))
    (bandTReciprocalSum n W) (bandReciprocalSum n W) 1 remRow
    rJI rIJ rJJ rD
    (fun p hp => prime_of_mem_primeBand hp)
    hC hepsilon hW0 hW1
    (fun p hp => tPrime_nonneg_of_mem_primeBand hn hp)
    (fun p hp => tPrime_le_one_of_mem_primeBand hn hp)
    (fun p hp => by positivity)
    (fun p hp => reciprocalPrime_le_reciprocalCutoff hW hp)
    (fun p hp => by positivity)
    (fun p hp => by
      have hp0 : (p : Real) ≠ 0 := by
        exact_mod_cast (prime_of_mem_primeBand hp).ne_zero
      field_simp [hp0])
    hJI hIJ hJJ hMoment
    (by simp [bandTReciprocalSum, div_eq_mul_inv])
    (by rfl) hSquare hRowRem
  have hadd (x : Real) : x + 2 + 3 = x + 5 := by ring
  simpa only [mul_one, one_mul, hadd] using hrow

end BoundedValuationLaw

end


end Erdos390.Full.PaperPrimePowerRow
