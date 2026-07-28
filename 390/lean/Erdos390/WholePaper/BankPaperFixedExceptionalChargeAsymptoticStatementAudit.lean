import Erdos390.WholePaper.BankPaperFixedExceptionalChargeAsymptotic

/-! # Statement audit for the fixed exceptional charge asymptotics -/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example : paperExceptionalTheta = (2 / 9 : ℝ) := rfl

example :
    paperExceptionalSelbergMainConstant =
      tangentSelbergCanonicalMainConstant := rfl

example :
    paperExceptionalSelbergRemainderConstant =
      tangentSelbergCanonicalLambdaConstant ^ 2 +
        tangentSelbergCanonicalMainConstant := rfl

example (c : ℝ) :
    paperExceptionalChargeConstant c =
      16 * c * tangentSelbergCanonicalMainConstant := rfl

example (c deltaStar : ℝ) :
    paperExceptionalChargeConstant c *
        (deltaStar / paperExceptionalTheta) =
      72 * c * tangentSelbergCanonicalMainConstant * deltaStar := by
  norm_num [paperExceptionalChargeConstant, paperExceptionalTheta,
    paperExceptionalSelbergMainConstant]
  ring

example : 0 < paperExceptionalTheta :=
  paperExceptionalTheta_pos

example : 0 < paperExceptionalSelbergMainConstant :=
  paperExceptionalSelbergMainConstant_pos

example : 0 < paperExceptionalSelbergRemainderConstant :=
  paperExceptionalSelbergRemainderConstant_pos

example {c : ℝ} (hc : 0 < c) :
    0 < paperExceptionalChargeConstant c :=
  paperExceptionalChargeConstant_pos hc

example (c deltaStar : ℝ) (n p : ℕ) :
    paperExceptionalFiniteChargeMajorant c deltaStar n p =
      4 * tangentSelbergCanonicalMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) +
      4 * (tangentSelbergCanonicalLambdaConstant ^ 2 +
          tangentSelbergCanonicalMainConstant) *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) := rfl

example (deltaStar : ℝ) (n : ℕ) :
    paperExceptionalChargeEpsilon deltaStar n =
      4 * (tangentSelbergCanonicalLambdaConstant ^ 2 +
          tangentSelbergCanonicalMainConstant) *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 * L n ^ 2 /
        ((n : ℝ) * Real.log (yNat n : ℝ) ^ 2) := rfl

example (deltaStar : ℝ) (n : ℕ) :
    0 ≤ paperExceptionalChargeEpsilon deltaStar n :=
  paperExceptionalChargeEpsilon_nonneg deltaStar n

example {n h b : ℕ} (hb : 0 < b) :
    ((((2 * n + h) / b - (2 * n) / b : ℕ) : ℝ)) ≤
      (h : ℝ) / (b : ℝ) + 1 :=
  paperExceptionalQuotientLength_cast_le hb

example {deltaStar : ℝ} {n p : ℕ}
    (hn : 1 < n) (hp : 0 < p)
    (hlogY : 0 < Real.log (yNat n : ℝ)) :
    4 * paperExceptionalSelbergRemainderConstant *
          (tangentPaperExceptionalCutoff deltaStar n : ℝ) *
          (yNat n : ℝ) ^ 4 /
        ((p : ℝ) * Real.log (yNat n : ℝ) ^ 2) =
      paperExceptionalChargeEpsilon deltaStar n *
        secondOrderScale n / ((p : ℝ) * L n) :=
  paperExceptionalFiniteRemainder_eq_epsilon_mul_scale
    hn hp hlogY

example {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    Tendsto (paperExceptionalChargeEpsilon deltaStar)
      atTop (nhds 0) :=
  paperExceptionalChargeEpsilon_tendsto_zero
    hdeltaNonneg hdeltaUpper

example {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      paperExceptionalChargeEpsilon deltaStar n ≤
        200 * paperExceptionalSelbergRemainderConstant *
          (n : ℝ) ^ (deltaStar + 8 / 9 - 1) :=
  eventually_paperExceptionalChargeEpsilon_le_power hdeltaNonneg

example {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      (upperTailLength c n : ℝ) ≤
        2 * c * secondOrderScale n :=
  eventually_upperTailLength_cast_le_two_mul_secondOrderScale hc

example {deltaStar : ℝ} (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      1 + Real.log
          ((2 * tangentPaperExceptionalCutoff deltaStar n : ℕ) : ℝ) ≤
        2 * deltaStar * L n :=
  eventually_one_add_log_two_mul_exceptionalCutoff_le hdelta

example
    {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar)
    {n p : ℕ} (hn : 1 < n) (hp : 0 < p)
    (hlogY : (1 / 5 : ℝ) * L n ≤ Real.log (yNat n : ℝ))
    (htail : (upperTailLength c n : ℝ) ≤
      2 * c * secondOrderScale n) :
    4 * paperExceptionalSelbergMainConstant * deltaStar * L n *
          (upperTailLength c n : ℝ) /
        ((p : ℝ) * Real.log (yNat n : ℝ)) ≤
      paperExceptionalChargeConstant c *
        (deltaStar / paperExceptionalTheta) *
        secondOrderScale n / (p : ℝ) :=
  paperExceptionalFiniteChargeMain_le_paperReserve
    hc hdelta hn hp hlogY htail

example {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p →
      paperExceptionalFiniteChargeMajorant c deltaStar n p ≤
        paperExceptionalChargeConstant c *
            (deltaStar / paperExceptionalTheta) *
            secondOrderScale n / (p : ℝ) +
          paperExceptionalChargeEpsilon deltaStar n *
            secondOrderScale n / ((p : ℝ) * L n) :=
  eventually_paperExceptionalFiniteChargeMajorant_le hc hdelta

example {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
            ℝ) ≤
          paperExceptionalFiniteChargeMajorant c deltaStar n p :=
  eventually_paperFixedExceptionalFactors_charge_le_finiteMajorant
    hc hdelta

example {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar)
    (hdeltaUpper : deltaStar < 1 / 18) :
    Tendsto (paperExceptionalChargeEpsilon deltaStar) atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (R : BankPaperRealization n
          (upperEndpoint n (upperTailLength c n))) (p : ℕ),
          p.Prime → p ≤ yNat n →
          (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
              ℝ) ≤
            paperExceptionalChargeConstant c *
                (deltaStar / paperExceptionalTheta) *
                secondOrderScale n / (p : ℝ) +
              paperExceptionalChargeEpsilon deltaStar n *
                secondOrderScale n / ((p : ℝ) * L n) :=
  paperFixedExceptionalCharge_asymptoticPackage hc hdelta hdeltaUpper

example {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    (completeSmoothPart (yNat n) a : ℝ) <
      2 * (n : ℝ) ^ deltaStar :=
  completeSmoothPart_cast_lt_two_mul_realExceptionalCutoff
    hdeltaNonneg hn hh ha

example {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h a : ℕ} (hn : 1 ≤ n) (hh : h ≤ n)
    (ha : a ∈ paperExceptionalUpperFactors n h deltaStar) :
    completeSmoothPart (yNat n) a <
      2 * tangentPaperExceptionalCutoff deltaStar n :=
  completeSmoothPart_lt_two_mul_exceptionalCutoff
    hdeltaNonneg hn hh ha

example {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h : ℕ} (hn : 1 ≤ n) (hh : h ≤ n) :
    paperExceptionalSmoothParts n h deltaStar ⊆
      Finset.Icc 1
        (2 * tangentPaperExceptionalCutoff deltaStar n) :=
  paperExceptionalSmoothParts_subset_Icc_two_mul_cutoff
    hdeltaNonneg hn hh

example {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (hn : 1 ≤ n) (hh : h ≤ n) (hp : p.Prime)
    (hpLow : p ≤ yNat n)
    (hpCut : 2 * (n : ℝ) ^ deltaStar < (p : ℝ)) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
      0 :=
  R.paperFixedExceptionalFactors_prod_factorization_eq_zero_of_realCutoff
    hdeltaNonneg hn hh hp hpLow hpCut

example {deltaStar : ℝ} (hdeltaNonneg : 0 ≤ deltaStar)
    {n h p : ℕ}
    (R : BankPaperRealization n (upperEndpoint n h))
    (hn : 1 ≤ n) (hh : h ≤ n) (hp : p.Prime)
    (hpLow : p ≤ yNat n)
    (hpCut : 2 * tangentPaperExceptionalCutoff deltaStar n < p) :
    ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
      0 :=
  R.paperFixedExceptionalFactors_prod_factorization_eq_zero
    hdeltaNonneg hn hh hp hpLow hpCut

example {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        2 * (n : ℝ) ^ deltaStar < (p : ℝ) →
        ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
          0 :=
  eventually_paperFixedExceptionalFactors_prod_factorization_eq_zero_of_realCutoff
    hc hdelta

example {c deltaStar : ℝ} (hc : 0 < c) (hdelta : 0 < deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        2 * tangentPaperExceptionalCutoff deltaStar n < p →
        ((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p =
          0 :=
  eventually_paperFixedExceptionalFactors_prod_factorization_eq_zero
    hc hdelta

end

end Erdos390.WholePaper
