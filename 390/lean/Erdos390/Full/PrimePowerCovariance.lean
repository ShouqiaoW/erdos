import Erdos390.Full.PowerLedger
import Erdos390.Full.FiniteExponentialFamily
import Erdos390.Full.NuisanceCovariance

/-!
# Exact prime-power covariance expansion

This file replaces the algebraic part of the prime-power transfer by proofs
for the actual valuation and divisor indicators under an actual finite
probability law.  In particular, `V = I + J` and all `JI`, `IJ`, and `JJ`
covariances are finite sums of genuine prime-power indicator covariances.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega Iota : Type*} [Fintype Omega]

theorem expect_zero (mu : FiniteProbability Omega) :
    mu.expect (fun _ ↦ 0) = 0 := by
  simp [expect]

theorem expect_add (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.expect (fun omega ↦ F omega + G omega) = mu.expect F + mu.expect G := by
  unfold expect
  simp_rw [mul_add]
  exact Finset.sum_add_distrib

theorem expect_smul (mu : FiniteProbability Omega) (a : ℝ) (F : Omega → ℝ) :
    mu.expect (fun omega ↦ a * F omega) = a * mu.expect F := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omega _
  ring

theorem expect_nonneg (mu : FiniteProbability Omega) (F : Omega → ℝ)
    (hF : ∀ omega, 0 ≤ F omega) : 0 ≤ mu.expect F := by
  unfold expect
  exact Finset.sum_nonneg fun omega _ ↦
    mul_nonneg (mu.mass_nonneg omega) (hF omega)

theorem expect_mono (mu : FiniteProbability Omega) (F G : Omega → ℝ)
    (hFG : ∀ omega, F omega ≤ G omega) : mu.expect F ≤ mu.expect G := by
  unfold expect
  apply Finset.sum_le_sum
  intro omega _
  exact mul_le_mul_of_nonneg_left (hFG omega) (mu.mass_nonneg omega)

theorem covariance_self_nonneg (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    0 ≤ mu.covariance F F := by
  unfold covariance expect
  rw [show (∑ omega, mu.mass omega * (F omega * F omega)) =
      ∑ omega, mu.mass omega * F omega ^ 2 by
    apply Finset.sum_congr rfl
    intro omega _
    ring]
  rw [show (∑ omega, mu.mass omega * F omega) *
      (∑ omega, mu.mass omega * F omega) =
        (∑ omega, mu.mass omega * F omega) ^ 2 by ring]
  rw [PatternMixture.weightedVariance_pairDifference mu.mass F mu.mass_sum]
  apply mul_nonneg (by norm_num)
  exact Finset.sum_nonneg fun i _ ↦ Finset.sum_nonneg fun j _ ↦
    mul_nonneg
      (mul_nonneg (mu.mass_nonneg i) (mu.mass_nonneg j)) (sq_nonneg _)

theorem covariance_zero_left (mu : FiniteProbability Omega) (G : Omega → ℝ) :
    mu.covariance (fun _ ↦ 0) G = 0 := by
  simp [covariance, expect]

theorem covariance_zero_right (mu : FiniteProbability Omega) (F : Omega → ℝ) :
    mu.covariance F (fun _ ↦ 0) = 0 := by
  simp [covariance, expect]

theorem covariance_add_left (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance (fun omega ↦ F omega + G omega) H =
      mu.covariance F H + mu.covariance G H := by
  unfold covariance
  rw [mu.expect_add F G]
  rw [show (fun omega ↦ (F omega + G omega) * H omega) =
      fun omega ↦ F omega * H omega + G omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring

theorem covariance_add_right (mu : FiniteProbability Omega)
    (F G H : Omega → ℝ) :
    mu.covariance F (fun omega ↦ G omega + H omega) =
      mu.covariance F G + mu.covariance F H := by
  unfold covariance
  rw [mu.expect_add G H]
  rw [show (fun omega ↦ F omega * (G omega + H omega)) =
      fun omega ↦ F omega * G omega + F omega * H omega by
    funext omega
    ring]
  rw [mu.expect_add]
  ring

theorem covariance_smul_left (mu : FiniteProbability Omega)
    (a : ℝ) (F G : Omega → ℝ) :
    mu.covariance (fun omega ↦ a * F omega) G =
      a * mu.covariance F G := by
  unfold covariance
  rw [mu.expect_smul a F]
  rw [show (fun omega ↦ a * F omega * G omega) =
      fun omega ↦ a * (F omega * G omega) by
    funext omega
    ring]
  rw [mu.expect_smul]
  ring

theorem covariance_smul_right (mu : FiniteProbability Omega)
    (a : ℝ) (F G : Omega → ℝ) :
    mu.covariance F (fun omega ↦ a * G omega) =
      a * mu.covariance F G := by
  unfold covariance
  rw [mu.expect_smul a G]
  rw [show (fun omega ↦ F omega * (a * G omega)) =
      fun omega ↦ a * (F omega * G omega) by
    funext omega
    ring]
  rw [mu.expect_smul]
  ring

theorem covariance_sum_left (mu : FiniteProbability Omega)
    (s : Finset Iota) (F : Iota → Omega → ℝ) (G : Omega → ℝ) :
    mu.covariance (fun omega ↦ ∑ i ∈ s, F i omega) G =
      ∑ i ∈ s, mu.covariance (F i) G := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_left]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_left, ih]

theorem covariance_sum_right (mu : FiniteProbability Omega)
    (F : Omega → ℝ) (s : Finset Iota) (G : Iota → Omega → ℝ) :
    mu.covariance F (fun omega ↦ ∑ i ∈ s, G i omega) =
      ∑ i ∈ s, mu.covariance F (G i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [mu.covariance_zero_right]
  | @insert i s hi ih =>
      simp only [Finset.sum_insert hi]
      rw [mu.covariance_add_right, ih]

theorem covariance_comm (mu : FiniteProbability Omega) (F G : Omega → ℝ) :
    mu.covariance F G = mu.covariance G F := by
  unfold covariance
  congr 1
  · apply Finset.sum_congr rfl
    intro omega _
    ring
  · ring

end FiniteProbability

namespace PrimePowerCovariance

open ArithmeticModel

/-- An actual finite law of positive integers with one common endpoint. -/
structure BoundedValuationLaw (Omega : Type*) [Fintype Omega] (M : ℕ) where
  probability : FiniteProbability Omega
  value : Omega → ℕ
  value_pos : ∀ omega, 0 < value omega
  value_le : ∀ omega, value omega ≤ M

namespace BoundedValuationLaw

variable {Omega : Type*} [Fintype Omega] {M : ℕ}

def I (law : BoundedValuationLaw Omega M) (p : ℕ) : Omega → ℝ :=
  fun omega ↦ divInd p (law.value omega)

def V (law : BoundedValuationLaw Omega M) (p : ℕ) : Omega → ℝ :=
  fun omega ↦ valuation p (law.value omega)

def J (law : BoundedValuationLaw Omega M) (p : ℕ) : Omega → ℝ :=
  fun omega ↦ higherValuation p (law.value omega)

def Ip (law : BoundedValuationLaw Omega M) (p : ℕ) (k : ℕ) : Omega → ℝ :=
  fun omega ↦ divInd (p ^ k) (law.value omega)

def covII (law : BoundedValuationLaw Omega M) (p q : ℕ) : ℝ :=
  law.probability.covariance (law.I p) (law.I q)

def covJI (law : BoundedValuationLaw Omega M) (p q : ℕ) : ℝ :=
  law.probability.covariance (law.J p) (law.I q)

def covIJ (law : BoundedValuationLaw Omega M) (p q : ℕ) : ℝ :=
  law.probability.covariance (law.I p) (law.J q)

def covJJ (law : BoundedValuationLaw Omega M) (p q : ℕ) : ℝ :=
  law.probability.covariance (law.J p) (law.J q)

def covVV (law : BoundedValuationLaw Omega M) (p q : ℕ) : ℝ :=
  law.probability.covariance (law.V p) (law.V q)

theorem V_eq_I_add_J (law : BoundedValuationLaw Omega M) (p : ℕ) :
    law.V p = fun omega ↦ law.I p omega + law.J p omega := by
  funext omega
  simp only [V, I, J, higherValuation]
  ring

theorem J_eq_power_sum (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) :
    law.J p = fun omega ↦ ∑ k ∈ highExponents M, law.Ip p k omega := by
  funext omega
  exact higherValuation_eq_sum_high_of_le hp (law.value_pos omega)
    (law.value_le omega)

/-- Exact decomposition of the full-valuation covariance error. -/
theorem covVV_sub_covII (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    law.covVV p q - law.covII p q =
      law.covJI p q + law.covIJ p q + law.covJJ p q := by
  rw [covVV, covII, covJI, covIJ, covJJ,
    law.V_eq_I_add_J p, law.V_eq_I_add_J q]
  rw [law.probability.covariance_add_left,
    law.probability.covariance_add_right,
    law.probability.covariance_add_right]
  ring

theorem abs_covVV_sub_covII_le (law : BoundedValuationLaw Omega M) (p q : ℕ) :
    |law.covVV p q - law.covII p q| ≤
      |law.covJI p q| + |law.covIJ p q| + |law.covJJ p q| := by
  rw [law.covVV_sub_covII p q]
  exact (abs_add_three _ _ _)

/-- `JI` is literally the finite sum of prime-power covariances. -/
theorem covJI_eq_power_sum (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (q : ℕ) :
    law.covJI p q = ∑ k ∈ highExponents M,
      law.probability.covariance (law.Ip p k) (law.I q) := by
  rw [covJI, law.J_eq_power_sum hp,
    law.probability.covariance_sum_left]

/-- `IJ` is literally the transpose prime-power sum. -/
theorem covIJ_eq_power_sum (law : BoundedValuationLaw Omega M)
    (p : ℕ) {q : ℕ} (hq : q.Prime) :
    law.covIJ p q = ∑ k ∈ highExponents M,
      law.probability.covariance (law.I p) (law.Ip q k) := by
  rw [covIJ, law.J_eq_power_sum hq,
    law.probability.covariance_sum_right]

/-- `JJ` is literally the double prime-power sum. -/
theorem covJJ_eq_power_sum (law : BoundedValuationLaw Omega M)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) :
    law.covJJ p q = ∑ k ∈ highExponents M, ∑ l ∈ highExponents M,
      law.probability.covariance (law.Ip p k) (law.Ip q l) := by
  rw [covJJ, law.J_eq_power_sum hp, law.J_eq_power_sum hq,
    law.probability.covariance_sum_left]
  apply Finset.sum_congr rfl
  intro k _
  rw [law.probability.covariance_sum_right]

theorem I_nonneg (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    0 ≤ law.I p omega := divInd_nonneg _ _

theorem I_le_one (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    law.I p omega ≤ 1 := divInd_le_one _ _

theorem J_nonneg (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    0 ≤ law.J p omega := higherValuation_nonneg hp (law.value_pos omega)

theorem J_le_sq (law : BoundedValuationLaw Omega M)
    {p : ℕ} (hp : p.Prime) (omega : Omega) :
    law.J p omega ≤ law.J p omega ^ 2 :=
  higherValuation_le_sq hp (law.value_pos omega)

theorem I_mul_J (law : BoundedValuationLaw Omega M) (p : ℕ) (omega : Omega) :
    law.I p omega * law.J p omega = law.J p omega := by
  exact divInd_mul_higherValuation p (law.value omega)

/-- On the diagonal, the paper's bound
`|Var(V_p)-Var(I_p)| ≤ 3 E[J_p²]` follows from the actual integer-valued
columns, not from a stylized random-variable identity. -/
theorem abs_covVV_sub_covII_diagonal_le
    (law : BoundedValuationLaw Omega M) {p : ℕ} (hp : p.Prime) :
    |law.covVV p p - law.covII p p| ≤
      3 * law.probability.expect (fun omega ↦ law.J p omega ^ 2) := by
  let EI := law.probability.expect (law.I p)
  let EJ := law.probability.expect (law.J p)
  let EJ2 := law.probability.expect (fun omega ↦ law.J p omega ^ 2)
  have hEI0 : 0 ≤ EI := law.probability.expect_nonneg _ (law.I_nonneg p)
  have hEI1 : EI ≤ 1 := by
    calc
      EI ≤ law.probability.expect (fun _ ↦ 1) :=
        law.probability.expect_mono _ _ (law.I_le_one p)
      _ = 1 := by simp [FiniteProbability.expect, law.probability.mass_sum]
  have hEJ0 : 0 ≤ EJ :=
    law.probability.expect_nonneg _ (law.J_nonneg hp)
  have hEJ2_0 : 0 ≤ EJ2 :=
    law.probability.expect_nonneg _ fun omega ↦ sq_nonneg _
  have hEJle : EJ ≤ EJ2 :=
    law.probability.expect_mono _ _ (law.J_le_sq hp)
  have hprod : law.probability.expect
      (fun omega ↦ law.I p omega * law.J p omega) = EJ := by
    change law.probability.expect
      (fun omega ↦ law.I p omega * law.J p omega) =
        law.probability.expect (law.J p)
    congr 1
    funext omega
    exact law.I_mul_J p omega
  have hcovIJ : law.covIJ p p = (1 - EI) * EJ := by
    unfold covIJ FiniteProbability.covariance
    rw [hprod]
    ring
  have hcovIJ0 : 0 ≤ law.covIJ p p := by
    rw [hcovIJ]
    exact mul_nonneg (sub_nonneg.mpr hEI1) hEJ0
  have hcovIJle : law.covIJ p p ≤ EJ2 := by
    rw [hcovIJ]
    have hfactor : (1 - EI) * EJ ≤ EJ := by
      nlinarith [mul_nonneg hEI0 hEJ0]
    exact hfactor.trans hEJle
  have hcovJI : law.covJI p p = law.covIJ p p := by
    unfold covJI covIJ
    exact law.probability.covariance_comm _ _
  have hvarJ0 : 0 ≤ law.covJJ p p := by
    exact law.probability.covariance_self_nonneg (law.J p)
  have hvarJle : law.covJJ p p ≤ EJ2 := by
    unfold covJJ FiniteProbability.covariance
    change law.probability.expect (fun omega ↦ law.J p omega * law.J p omega) -
        EJ * EJ ≤ EJ2
    have hfirst : law.probability.expect
        (fun omega ↦ law.J p omega * law.J p omega) = EJ2 := by
      congr 1
      funext omega
      ring
    rw [hfirst]
    nlinarith [sq_nonneg EJ]
  rw [law.covVV_sub_covII p p, hcovJI]
  rw [abs_of_nonneg (by linarith)]
  linarith

end BoundedValuationLaw

end PrimePowerCovariance

end

end Erdos390.Full
