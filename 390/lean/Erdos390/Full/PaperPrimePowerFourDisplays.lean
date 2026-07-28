import Erdos390.Full.PaperPrimePowerActualSplice
import Erdos390.Full.PaperPrimePowerPairAggregation

/-!
# The four pointwise displays of Lemma 7.5

This file is the exact algebraic specialization of the generic actual-law
splice to `JI`, `IJ`, `JJ`, and the diagonal second-moment input.  One main
constant and one chamber remainder dominate all four orientations.
-/

namespace Erdos390.Full.PaperPrimePowerFourDisplays

open ArithmeticModel Scale
open FiniteProbability PrimePowerCovariance
open PaperPrimePowerChamberError PaperPrimePowerPointwise

noncomputable section

/-- The box-independent coefficient common to all four displays. -/
def primePowerMainConstant (C_K : ℝ) : ℝ :=
  2 * C_K + 1 / DickmanBasic.rho DickmanBasic.U

/-- The common chamber remainder used in all four displays. -/
def primePowerChamberRemainder (epsilon G₀ k : ℝ) : ℝ :=
  aggregateChamberScale epsilon G₀ k

/-- Literal outside-chamber residual in the `JI` orientation. -/
def eJI (G : ℝ) (n p q r : ℕ) : ℝ := covarianceTail G n p q r 1

/-- Literal outside-chamber residual in the `IJ` orientation. -/
def eIJ (G : ℝ) (n p q s : ℕ) : ℝ := covarianceTail G n p q 1 s

/-- Literal outside-chamber residual in the `JJ` orientation. -/
def eJJ (G : ℝ) (n p q r s : ℕ) : ℝ := covarianceTail G n p q r s

/-- Literal outside-chamber residual in the diagonal orientation. -/
def eD (G : ℝ) (n p r : ℕ) : ℝ := probabilityTail G n p r

theorem primePowerMainConstant_nonneg {C_K : ℝ} (hCK : 0 ≤ C_K) :
    0 ≤ primePowerMainConstant C_K := by
  unfold primePowerMainConstant
  exact add_nonneg (mul_nonneg (by norm_num) hCK)
    (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)

theorem primePowerChamberRemainder_nonneg
    {epsilon G₀ k : ℝ} (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k) :
    0 ≤ primePowerChamberRemainder epsilon G₀ k :=
  aggregateChamberScale_nonneg hepsilon hG₀ hk

/-- `JI`: the exponent-one factor is absorbed by the common factor `2`. -/
theorem ji_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p q r : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hgeneric :
      |law.probability.covariance (law.Ip p r) (law.Ip q 1)| ≤
        (C_K * tPrime n p * tPrime n q +
            pairCovarianceScale (pairProbabilityScale epsilon G₀ k)) *
          pairWeight p q r 1 + covarianceTail Gf n p q r 1) :
    |law.probability.covariance (law.Ip p r) (law.I q)| ≤
      (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
        (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
      eJI Gf n p q r := by
  have hIq : law.Ip q 1 = law.I q := by
    funext omega
    simp only [BoundedValuationLaw.Ip, BoundedValuationLaw.I, pow_one]
  rw [← hIq]
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) ≤
        primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith [mul_nonneg hR (mul_nonneg htp htq)]
  calc
    |law.probability.covariance (law.Ip p r) (law.Ip q 1)| ≤
        (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q r 1 + covarianceTail Gf n p q r 1 := by
      simpa only [E] using hgeneric
    _ = (2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E)) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
        eJI Gf n p q r := by
      unfold pairWeight eJI
      norm_num
      ring
    _ ≤ (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
          (((r : ℝ) + 1) / ((p : ℝ) ^ r * (q : ℝ))) +
        eJI Gf n p q r := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) le_rfl

/-- `IJ`: the transposed exponent-one specialization. -/
theorem ij_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p q s : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hgeneric :
      |law.probability.covariance (law.Ip p 1) (law.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q +
            pairCovarianceScale (pairProbabilityScale epsilon G₀ k)) *
          pairWeight p q 1 s + covarianceTail Gf n p q 1 s) :
    |law.probability.covariance (law.I p) (law.Ip q s)| ≤
      (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
        (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
      eIJ Gf n p q s := by
  have hIp : law.Ip p 1 = law.I p := by
    funext omega
    simp only [BoundedValuationLaw.Ip, BoundedValuationLaw.I, pow_one]
  rw [← hIp]
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) ≤
        primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith [mul_nonneg hR (mul_nonneg htp htq)]
  calc
    |law.probability.covariance (law.Ip p 1) (law.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q 1 s + covarianceTail Gf n p q 1 s := by
      simpa only [E] using hgeneric
    _ = (2 * (C_K * tPrime n p * tPrime n q + pairCovarianceScale E)) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
        eIJ Gf n p q s := by
      unfold pairWeight eIJ
      norm_num
      ring
    _ ≤ (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
          (((s : ℝ) + 1) / ((p : ℝ) * (q : ℝ) ^ s)) +
        eIJ Gf n p q s := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hcoef (by positivity)) le_rfl

/-- `JJ`: no exponent-one loss is needed. -/
theorem jj_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p q r s : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hCK : 0 ≤ C_K) (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hgeneric :
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        (C_K * tPrime n p * tPrime n q +
            pairCovarianceScale (pairProbabilityScale epsilon G₀ k)) *
          pairWeight p q r s + covarianceTail Gf n p q r s) :
    |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
      (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) *
        ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) +
      eJJ Gf n p q r s := by
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      C_K * tPrime n p * tPrime n q + pairCovarianceScale E ≤
        primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith [mul_nonneg hCK (mul_nonneg htp htq),
      mul_nonneg hR (mul_nonneg htp htq)]
  calc
    _ ≤ (C_K * tPrime n p * tPrime n q + pairCovarianceScale E) *
          pairWeight p q r s + covarianceTail Gf n p q r s := by
      simpa only [E] using hgeneric
    _ ≤ (primePowerMainConstant C_K * tPrime n p * tPrime n q +
          primePowerChamberRemainder epsilon G₀ k) * pairWeight p q r s +
        covarianceTail Gf n p q r s :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef
        (pairWeight_nonneg p q r s)) le_rfl
    _ = _ := by rfl

/-- Diagonal probability display. -/
theorem diagonal_display_of_generic
    {Omega : Type*} [Fintype Omega] {M n p r : ℕ}
    (law : BoundedValuationLaw Omega M)
    {C_K epsilon G₀ k Gf : ℝ}
    (hCK : 0 ≤ C_K) (hepsilon : 0 ≤ epsilon)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hgeneric : law.probability.expect (law.Ip p r) ≤
      ((1 / DickmanBasic.rho DickmanBasic.U) +
          pairProbabilityScale epsilon G₀ k) * singleWeight p r +
        probabilityTail Gf n p r) :
    law.probability.expect (law.Ip p r) ≤
      (primePowerMainConstant C_K +
          primePowerChamberRemainder epsilon G₀ k) *
        (((r : ℝ) + 1) / (p : ℝ) ^ r) + eD Gf n p r := by
  let E := pairProbabilityScale epsilon G₀ k
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hECov : 0 ≤ pairCovarianceScale E := pairCovarianceScale_nonneg hE
  have hcoef :
      (1 / DickmanBasic.rho DickmanBasic.U) + E ≤
        primePowerMainConstant C_K +
          primePowerChamberRemainder epsilon G₀ k := by
    unfold primePowerMainConstant primePowerChamberRemainder
      aggregateChamberScale
    have hR : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U :=
      one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
    have hProb : 0 ≤ pairProbabilityScale epsilon G₀ k := hE
    dsimp only [E] at hECov
    nlinarith
  calc
    law.probability.expect (law.Ip p r) ≤
        ((1 / DickmanBasic.rho DickmanBasic.U) + E) * singleWeight p r +
          probabilityTail Gf n p r := by simpa only [E] using hgeneric
    _ ≤ (primePowerMainConstant C_K +
          primePowerChamberRemainder epsilon G₀ k) * singleWeight p r +
        probabilityTail Gf n p r :=
      add_le_add (mul_le_mul_of_nonneg_right hcoef (singleWeight_nonneg p r))
        le_rfl
    _ = _ := by rfl

end

end Erdos390.Full.PaperPrimePowerFourDisplays
