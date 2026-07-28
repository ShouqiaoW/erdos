import Erdos390.WholePaper.BankPaperCanonicalPostHfitSlackConnector

/-!
# Eventual feasibility of the canonical Post-Hfit balanced coefficient

The paper first chooses a positive total broad coefficient
`beta < c / (3 * roughHeadDensity W)` and then takes the fixed high-block
multiplicity sufficiently large.  This file records that choice at the
exact finite level.

No quota or height-ledger asymptotic is needed.  The defining ceiling gives

`c * n / log n <= upperTailLength c n`

pointwise, which already makes the numerator of the balanced coefficient
nonnegative.  Taking the multiplicity at least the reciprocal head density
makes the same numerator at most its denominator.
-/

open Filter Set

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.PaperBridgeFit

noncomputable section

/-! ## Finite balanced-coefficient algebra -/

/-- The exact two inequalities behind feasibility of the balanced raw
coefficient.  The hypotheses are deliberately stated before specializing
`h` to the paper's integral upper-tail length. -/
theorem roughHeadBalancedAlpha_mem_Icc_of_tail_lower
    {W n h K : Nat} {c beta ell : Real}
    (hc : 0 < c) (hn : 0 < n) (hKpos : 0 < K)
    (hell : 0 < ell) (hbeta : 0 ≤ beta)
    (hbetaUpper : beta ≤ c / roughHeadDensity W)
    (hKlarge : 1 / roughHeadDensity W ≤ (K : Real))
    (htail : c * (n : Real) / ell ≤ (h : Real)) :
    roughHeadBalancedAlpha W n h K beta ell ∈
      Icc (0 : Real) 1 := by
  have hdensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hnReal : (0 : Real) < (n : Real) := by
    exact_mod_cast hn
  have htailBase : 0 < c * (n : Real) / ell :=
    div_pos (mul_pos hc hnReal) hell
  have hhReal : (0 : Real) < (h : Real) :=
    htailBase.trans_le htail
  have hh : 0 < h := by
    exact_mod_cast hhReal
  have hden :
      0 < (((K * h : Nat) : Real)) := by
    exact_mod_cast Nat.mul_pos hKpos hh
  have hsub :
      (((n - K * h : Nat) : Real)) ≤ (n : Real) := by
    exact_mod_cast Nat.sub_le n (K * h)
  have hbetaDiv : 0 ≤ beta / ell :=
    div_nonneg hbeta hell.le
  have htermNonneg :
      0 ≤ (beta / ell) * (((n - K * h : Nat) : Real)) :=
    mul_nonneg hbetaDiv (Nat.cast_nonneg _)
  have htermUpper :
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
        (h : Real) / roughHeadDensity W := by
    calc
      (beta / ell) * (((n - K * h : Nat) : Real)) ≤
          (beta / ell) * (n : Real) :=
        mul_le_mul_of_nonneg_left hsub hbetaDiv
      _ = beta * ((n : Real) / ell) := by ring
      _ ≤ (c / roughHeadDensity W) * ((n : Real) / ell) :=
        mul_le_mul_of_nonneg_right hbetaUpper
          (div_nonneg hnReal.le hell.le)
      _ = (c * (n : Real) / ell) / roughHeadDensity W := by ring
      _ ≤ (h : Real) / roughHeadDensity W :=
        div_le_div_of_nonneg_right htail hdensity.le
  have hnumNonneg :
      0 ≤ (h : Real) / roughHeadDensity W -
        (beta / ell) * (((n - K * h : Nat) : Real)) :=
    sub_nonneg.mpr htermUpper
  have hheadUpper :
      (h : Real) / roughHeadDensity W ≤
        (((K * h : Nat) : Real)) := by
    calc
      (h : Real) / roughHeadDensity W =
          (1 / roughHeadDensity W) * (h : Real) := by ring
      _ ≤ (K : Real) * (h : Real) :=
        mul_le_mul_of_nonneg_right hKlarge hhReal.le
      _ = (((K * h : Nat) : Real)) := by
        norm_num only [Nat.cast_mul]
  constructor
  · rw [roughHeadBalancedAlpha]
    exact div_nonneg hnumNonneg hden.le
  · rw [roughHeadBalancedAlpha]
    exact
      (div_le_one hden).2
        ((sub_le_self _ htermNonneg).trans hheadUpper)

namespace BankPaperRealization

/-! ## Canonical bridge specialization -/

/-- Pointwise feasibility for the literal Post-Hfit coefficient.  The only
scale input is the paper's exact upper-tail ceiling. -/
theorem bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) {c : Real} (K0 : Nat)
    (betaProt betaAct : Real) (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤
        c / roughHeadDensity B.sampleData.W)
    (hKlarge :
      1 / roughHeadDensity B.sampleData.W ≤
        (((K0 + 1 : Nat) : Real))) :
    bankPaperCanonicalPostHfitBalancedAlpha
        B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  have htail :
      c * (B.sampleData.n : Real) / B.L ≤
        (upperTailLength c B.sampleData.n : Real) := by
    calc
      c * (B.sampleData.n : Real) / B.L =
          c * secondOrderScale B.sampleData.n := by
        unfold BridgeData.L secondOrderScale
        ring
      _ ≤ (upperTailLength c B.sampleData.n : Real) := by
        simpa only [upperTailLength] using
          (Nat.le_ceil
            (c * secondOrderScale B.sampleData.n))
  simpa only [bankPaperCanonicalPostHfitBalancedAlpha] using
    (roughHeadBalancedAlpha_mem_Icc_of_tail_lower
      (W := B.sampleData.W) (n := B.sampleData.n)
      (h := upperTailLength c B.sampleData.n) (K := K0 + 1)
      (c := c) (beta := betaProt + betaAct) (ell := B.L)
      hc (Nat.zero_lt_of_lt B.n_gt_one) (by omega)
      B.L_pos hbeta hbetaUpper hKlarge htail)

/-- Uniform family form used by the Section 9 supplier.  It applies to every
bridge with the synchronized width, hence in particular to the coherent
canonical/post-height bridge family. -/
theorem eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W K0 : Nat) {c betaProt betaAct : Real} (hc : 0 < c)
    (hbeta : 0 ≤ betaProt + betaAct)
    (hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W)
    (hKlarge :
      1 / roughHeadDensity W ≤ (((K0 + 1 : Nat) : Real))) :
    ∀ᶠ n : Nat in atTop,
      ∀ B : BridgeData Head Band,
        B.sampleData.n = n →
        B.sampleData.W = W →
        bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  refine Eventually.of_forall ?_
  intro n B _hBn hBW
  apply
    bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBounds
      B K0 betaProt betaAct hc hbeta
  · simpa only [hBW] using hbetaUpper
  · simpa only [hBW] using hKlarge

/-- The manuscript's strict beta choice always admits one fixed
multiplicity and therefore closes the uniform `[0,1]` obligation. -/
theorem
    exists_K0_eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBeta
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W : Nat) {c betaProt betaAct : Real}
    (hc : 0 < c) (hbetaProt : 0 < betaProt)
    (hbetaAct : 0 < betaAct)
    (hbetaSmall :
      betaProt + betaAct <
        c / (3 * roughHeadDensity W)) :
    ∃ K0 : Nat,
      ∀ᶠ n : Nat in atTop,
        ∀ B : BridgeData Head Band,
          B.sampleData.n = n →
          B.sampleData.W = W →
          bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  have hdensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hthreeDensity : 0 < 3 * roughHeadDensity W :=
    mul_pos (by norm_num) hdensity
  have hdenomStrict :
      roughHeadDensity W < 3 * roughHeadDensity W := by
    linarith
  have hthird :
      c / (3 * roughHeadDensity W) <
        c / roughHeadDensity W :=
    (div_lt_div_iff_of_pos_left
      hc hthreeDensity hdensity).2 hdenomStrict
  have hbeta : 0 ≤ betaProt + betaAct :=
    add_nonneg hbetaProt.le hbetaAct.le
  have hbetaUpper :
      betaProt + betaAct ≤ c / roughHeadDensity W :=
    hbetaSmall.le.trans hthird.le
  obtain ⟨K0, hK0⟩ :=
    exists_nat_gt (1 / roughHeadDensity W)
  have hKlarge :
      1 / roughHeadDensity W ≤
        (((K0 + 1 : Nat) : Real)) := by
    calc
      1 / roughHeadDensity W ≤ (K0 : Real) := hK0.le
      _ ≤ (((K0 + 1 : Nat) : Real)) := by
        norm_num
  exact
    ⟨K0,
      eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
        W K0 hc hbeta hbetaUpper hKlarge⟩

/-- A concrete positive split and one fixed multiplicity exist for every
positive paper tail parameter.  This form introduces no new downstream
parameter contract. -/
theorem
    exists_paperParameters_eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (W : Nat) {c : Real} (hc : 0 < c) :
    ∃ betaProt betaAct : Real, ∃ K0 : Nat,
      0 < betaProt ∧
      0 < betaAct ∧
      betaProt + betaAct <
        c / (3 * roughHeadDensity W) ∧
      ∀ᶠ n : Nat in atTop,
        ∀ B : BridgeData Head Band,
          B.sampleData.n = n →
          B.sampleData.W = W →
          bankPaperCanonicalPostHfitBalancedAlpha
              B c K0 betaProt betaAct ∈ Icc (0 : Real) 1 := by
  let betaPiece : Real :=
    (c / (3 * roughHeadDensity W)) / 4
  have hdensity : 0 < roughHeadDensity W :=
    roughHeadDensity_pos W
  have hpaperBetaScale :
      0 < c / (3 * roughHeadDensity W) :=
    div_pos hc (mul_pos (by norm_num) hdensity)
  have hbetaPiece : 0 < betaPiece := by
    dsimp only [betaPiece]
    positivity
  have hbetaSmall :
      betaPiece + betaPiece <
        c / (3 * roughHeadDensity W) := by
    dsimp only [betaPiece]
    linarith
  obtain ⟨K0, hK0⟩ :=
    exists_K0_eventually_bankPaperCanonicalPostHfitBalancedAlpha_mem_Icc_of_paperBeta
      (Head := Head) (Band := Band) W hc
        hbetaPiece hbetaPiece hbetaSmall
  exact
    ⟨betaPiece, betaPiece, K0,
      hbetaPiece, hbetaPiece, hbetaSmall, hK0⟩

end BankPaperRealization

end

end Erdos390.WholePaper
