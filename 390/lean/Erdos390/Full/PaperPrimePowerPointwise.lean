import Erdos390.Full.PaperPrimePowerChamberError
import Erdos390.Full.PaperPrimePowerTailLedger

/-!
# Literal-chamber pointwise prime-power estimates

This file performs the deterministic splice used in Lemma 7.5.  Inside the
literal arithmetic chamber `p^r q^s <= yNat n ^ 4` it uses the sharp
Dickman covariance term and the explicit restoration ledger.  Outside the
chamber it records the uniform reciprocal fallback as a named residual.
-/

namespace Erdos390.Full.PaperPrimePowerPointwise

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open OmittedTiltPairChamber
open FullTiltPairChamber FullTiltPrimePowerCovariance
open FullTiltPrimePowerActualChamber FullTiltPrimePowerFallback
open PaperPrimePowerChamberError

noncomputable section

/-- The literal beyond-four covariance residual. -/
def covarianceTail (G : ℝ) (n p q r s : ℕ) : ℝ :=
  if pairPower p q r s ≤ yNat n ^ 4 then 0
  else (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)

/-- The literal beyond-four one-prime probability residual. -/
def probabilityTail (G : ℝ) (n p r : ℕ) : ℝ :=
  if p ^ r ≤ yNat n ^ 4 then 0 else G / (p : ℝ) ^ r

theorem covarianceTail_nonneg {G : ℝ} (hG : 0 ≤ G) (n p q r s : ℕ) :
    0 ≤ covarianceTail G n p q r s := by
  unfold covarianceTail
  split_ifs
  · exact le_rfl
  · exact div_nonneg (by nlinarith [sq_nonneg G]) (by positivity)

theorem probabilityTail_nonneg {G : ℝ} (hG : 0 ≤ G) (n p r : ℕ) :
    0 ≤ probabilityTail G n p r := by
  unfold probabilityTail
  split_ifs
  · exact le_rfl
  · exact div_nonneg hG (by positivity)

/-- The deterministic Dickman product term is no larger than its natural
product weight. -/
theorem kernelTerm_le_pairWeight
    {C_K : ℝ} (hCK : 0 ≤ C_K) {n p q r s : ℕ}
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q) :
    C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤
      (C_K * tPrime n p * tPrime n q) * pairWeight p q r s := by
  have hrs : (r : ℝ) * (s : ℝ) ≤
      ((r : ℝ) + 1) * ((s : ℝ) + 1) := by
    nlinarith [show (0 : ℝ) ≤ r by positivity,
      show (0 : ℝ) ≤ s by positivity]
  have hcoef : 0 ≤ C_K * tPrime n p * tPrime n q := by positivity
  have hnum := mul_le_mul_of_nonneg_left hrs hcoef
  unfold pairWeight
  have hden : 0 ≤ (p : ℝ) ^ r * (q : ℝ) ^ s := by positivity
  calc
    C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) =
        (C_K * tPrime n p * tPrime n q * ((r : ℝ) * (s : ℝ))) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) := by ring
    _ ≤ (C_K * tPrime n p * tPrime n q *
          (((r : ℝ) + 1) * ((s : ℝ) + 1))) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) :=
      div_le_div_of_nonneg_right hnum hden
    _ = (C_K * tPrime n p * tPrime n q) *
        ((((r : ℝ) + 1) * ((s : ℝ) + 1)) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s)) := by ring

/-- Chamber/fallback splice for a genuine two-prime covariance. -/
theorem covariance_le_chamber_add_tail
    {C_K E G : ℝ} (hCK : 0 ≤ C_K) (hE : 0 ≤ E)
    {n p q r s : ℕ} {covariance chamberError : ℝ}
    (htp : 0 ≤ tPrime n p) (htq : 0 ≤ tPrime n q)
    (hchamber : pairPower p q r s ≤ yNat n ^ 4 →
      |covariance| ≤
        C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s) + chamberError)
    (herror : pairPower p q r s ≤ yNat n ^ 4 →
      chamberError ≤ E * pairWeight p q r s)
    (hfallback : |covariance| ≤
      (G + G ^ 2) / ((p : ℝ) ^ r * (q : ℝ) ^ s)) :
    |covariance| ≤
      (C_K * tPrime n p * tPrime n q + E) * pairWeight p q r s +
        covarianceTail G n p q r s := by
  by_cases hD4 : pairPower p q r s ≤ yNat n ^ 4
  · rw [covarianceTail, if_pos hD4, add_zero]
    calc
      |covariance| ≤
          C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
              ((p : ℝ) ^ r * (q : ℝ) ^ s) + chamberError :=
        hchamber hD4
      _ ≤ (C_K * tPrime n p * tPrime n q) * pairWeight p q r s +
          E * pairWeight p q r s :=
        add_le_add (kernelTerm_le_pairWeight hCK htp htq) (herror hD4)
      _ = (C_K * tPrime n p * tPrime n q + E) *
          pairWeight p q r s := by ring
  · rw [covarianceTail, if_neg hD4]
    exact hfallback.trans (le_add_of_nonneg_left
      (mul_nonneg (by positivity) (pairWeight_nonneg p q r s)))

/-- Chamber/fallback splice for a one-prime divisibility probability. -/
theorem probability_le_chamber_add_tail
    {R E G : ℝ} (hR : 0 ≤ R) (hE : 0 ≤ E)
    {n p r : ℕ} {probability chamberError : ℝ}
    (hchamber : p ^ r ≤ yNat n ^ 4 →
      probability ≤ R * singleWeight p r + chamberError)
    (herror : p ^ r ≤ yNat n ^ 4 →
      chamberError ≤ E * singleWeight p r)
    (hfallback : probability ≤ G / (p : ℝ) ^ r) :
    probability ≤ (R + E) * singleWeight p r + probabilityTail G n p r := by
  by_cases hD4 : p ^ r ≤ yNat n ^ 4
  · rw [probabilityTail, if_pos hD4, add_zero]
    calc
      probability ≤ R * singleWeight p r + chamberError := hchamber hD4
      _ ≤ R * singleWeight p r + E * singleWeight p r :=
        add_le_add le_rfl (herror hD4)
      _ = (R + E) * singleWeight p r := by ring
  · rw [probabilityTail, if_neg hD4]
    exact hfallback.trans (le_add_of_nonneg_left
      (mul_nonneg (add_nonneg hR hE) (singleWeight_nonneg p r)))

end

end Erdos390.Full.PaperPrimePowerPointwise
