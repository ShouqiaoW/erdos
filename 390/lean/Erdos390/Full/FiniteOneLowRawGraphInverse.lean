import Erdos390.Full.FiniteGraphQuotientInverse

/-!
# An ordinary-sup inverse for a graph with one moving low coordinate

The sharp graph maximum principle by itself controls `q = b / alpha` and
therefore only gives the weighted norm `max |b i| / alpha i`.  This file
records the additional argument needed when exactly one centre tends to
zero.  The positive block still has a uniform graph anchor.  Its coupling
to the low coordinate is `O(alphaLow)`, while the low row has a uniformly
positive diagonal mass.  The two estimates close by absorption and give an
ordinary `max |b i|` bound.

All hypotheses below are elementary edge, centre, and gauge inequalities.
In particular no inverse, surjectivity, or spectral-gap assertion is an
input.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteOneLowRawGraphInverse

open FiniteGraphQuotientInverse

variable {Pos : Type*} [Fintype Pos] [DecidableEq Pos]

/-- The positive-coordinate restriction of an edge family. -/
def positiveEdge (edge : Option Pos → Option Pos → ℝ) (i j : Pos) : ℝ :=
  edge (some i) (some j)

/-- The positive-coordinate restriction of a vector. -/
def positivePart (q : Option Pos → ℝ) (i : Pos) : ℝ := q (some i)

omit [DecidableEq Pos] in
lemma graphOperator_some_decomposition
    (edge : Option Pos → Option Pos → ℝ) (q : Option Pos → ℝ) (i : Pos) :
    graphOperator edge q (some i) =
      graphOperator (positiveEdge edge) (positivePart q) i +
        edge (some i) none * (q (some i) - q none) := by
  simp [graphOperator, positiveEdge, positivePart, add_comm]

omit [DecidableEq Pos] in
lemma graphOperator_none_decomposition
    (edge : Option Pos → Option Pos → ℝ) (q : Option Pos → ℝ) :
    graphOperator edge q none =
      ∑ j : Pos, edge none (some j) * (q none - q (some j)) := by
  simp [graphOperator]

omit [DecidableEq Pos] in
/-- A weighted positive mean is close to any common pointwise centre. -/
lemma abs_weightedMean_le_of_close
    [Nonempty Pos]
    (omega q : Pos → ℝ) (mu R : ℝ)
    (homega : ∀ i, 0 ≤ omega i)
    (hOmega : 0 < ∑ i, omega i)
    (hclose : ∀ i, |q i - mu| ≤ R) :
    |(∑ i, omega i * q i) / (∑ i, omega i) - mu| ≤ R := by
  have hOmega0 : (∑ i, omega i) ≠ 0 := ne_of_gt hOmega
  have hidentity :
      (∑ i, omega i * q i) / (∑ i, omega i) - mu =
        (∑ i, omega i * (q i - mu)) / (∑ i, omega i) := by
    rw [show (∑ i, omega i * (q i - mu)) =
        (∑ i, omega i * q i) - mu * (∑ i, omega i) by
      calc
        (∑ i, omega i * (q i - mu)) =
            ∑ i, (omega i * q i - omega i * mu) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = (∑ i, omega i * q i) - ∑ i, omega i * mu := by
          rw [Finset.sum_sub_distrib]
        _ = _ := by rw [← Finset.sum_mul]; ring]
    field_simp [hOmega0]
  rw [hidentity, abs_div, abs_of_pos hOmega]
  apply (div_le_iff₀ hOmega).2
  calc
    |∑ i, omega i * (q i - mu)| ≤
        ∑ i, |omega i * (q i - mu)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, omega i * R := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul, abs_of_nonneg (homega i)]
      exact mul_le_mul_of_nonneg_left (hclose i) (homega i)
    _ = R * ∑ i, omega i := by
      rw [← Finset.sum_mul]
      ring

omit [DecidableEq Pos] in
/-- Quantitative ordinary-coordinate estimate for one low cell.

`alpha none` is allowed to tend to zero.  The first smallness inequality
absorbs its effect on the anchored positive block; the second absorbs the
positive block back into the low row.  Every displayed constant is chosen
from structural edge/gauge data before `alpha none` is specialized. -/
theorem ordinary_raw_bound
    [Nonempty Pos]
    (edge : Option Pos → Option Pos → ℝ)
    (anchor omega alpha q : Option Pos → ℝ)
    {kappa anchorMass alphaMin alphaMax incoming gaugeRatio
      lowMass lowRowMass G : ℝ}
    (hG : 0 ≤ G)
    (hkappa : 0 < kappa)
    (hAnchorMass : ∑ j : Pos, anchor (some j) = anchorMass)
    (hAnchorMassPos : 0 < anchorMass)
    (hPositiveDom : ∀ i j : Pos,
      kappa * anchor (some j) ≤ edge (some i) (some j))
    (hAlphaLow : 0 < alpha none)
    (hAlphaPositiveLower : ∀ i : Pos, alphaMin ≤ alpha (some i))
    (hAlphaMin : 0 < alphaMin)
    (hAlphaPositiveUpper : ∀ i : Pos, alpha (some i) ≤ alphaMax)
    (hAlphaPositiveNonneg : ∀ i : Pos, 0 ≤ alpha (some i))
    (hIncomingNonneg : ∀ i : Pos, 0 ≤ edge (some i) none)
    (hIncoming : ∀ i : Pos,
      edge (some i) none ≤ incoming * alpha none)
    (hIncomingNonnegConst : 0 ≤ incoming)
    (hOmegaPositiveNonneg : ∀ i : Pos, 0 ≤ omega (some i))
    (hOmegaPositive : 0 < ∑ i : Pos, omega (some i))
    (hOmegaLowNonneg : 0 ≤ omega none)
    (hGaugeRatio : omega none ≤
      gaugeRatio * alpha none * (∑ i : Pos, omega (some i)))
    (hGaugeRatioNonneg : 0 ≤ gaugeRatio)
    (hGauge : ∑ i : Option Pos, omega i * q i = 0)
    (hLowEdgeNonneg : ∀ j : Pos, 0 ≤ edge none (some j))
    (hLowMassLower : lowMass ≤ ∑ j : Pos, edge none (some j))
    (hLowMassPos : 0 < lowMass)
    (hLowMassUpper : ∑ j : Pos, edge none (some j) ≤ lowRowMass)
    (hLowRowMassNonneg : 0 ≤ lowRowMass)
    (hOutput : ∀ i : Option Pos,
      |alpha i * graphOperator edge q i| ≤ G)
    (hAbsorbPositive :
      2 * (1 / (kappa * anchorMass)) * incoming * alpha none ≤ 1 / 2)
    (hAbsorbLow :
      alpha none * lowRowMass *
          (4 * (1 / (kappa * anchorMass)) * incoming +
            2 * gaugeRatio) / lowMass ≤ 1 / 2) :
    ∀ i : Option Pos,
      |alpha i * q i| ≤
        max
          (2 * (1 / lowMass +
            alpha none * lowRowMass *
              (4 * (1 / (kappa * anchorMass)) / alphaMin) / lowMass))
          (alphaMax *
            ((4 * (1 / (kappa * anchorMass)) / alphaMin) +
              (4 * (1 / (kappa * anchorMass)) * incoming +
                2 * gaugeRatio) *
                (2 * (1 / lowMass +
                  alpha none * lowRowMass *
                    (4 * (1 / (kappa * anchorMass)) / alphaMin) /
                      lowMass)))) * G := by
  let K : ℝ := 1 / (kappa * anchorMass)
  let Q : ℝ := ‖positivePart q‖
  let B₀ : ℝ := |alpha none * q none|
  have hKpos : 0 < K := by
    dsimp only [K]
    positivity
  have hQnonneg : 0 ≤ Q := norm_nonneg _
  have hB₀nonneg : 0 ≤ B₀ := abs_nonneg _
  have hAlphaPos (i : Pos) : 0 < alpha (some i) :=
    hAlphaMin.trans_le (hAlphaPositiveLower i)
  have hFullPositive (i : Pos) :
      |graphOperator edge q (some i)| ≤ G / alphaMin := by
    have hout := hOutput (some i)
    rw [abs_mul, abs_of_pos (hAlphaPos i)] at hout
    calc
      |graphOperator edge q (some i)| ≤ G / alpha (some i) := by
        exact (le_div_iff₀ (hAlphaPos i)).2 (by
          simpa [mul_comm] using hout)
      _ ≤ G / alphaMin := by
        exact div_le_div_of_nonneg_left hG hAlphaMin
          (hAlphaPositiveLower i)
  have hQpoint (i : Pos) : |q (some i)| ≤ Q := by
    change |positivePart q i| ≤ ‖positivePart q‖
    rw [← Real.norm_eq_abs]
    exact norm_le_pi_norm (positivePart q) i
  have hRestricted (i : Pos) :
      |graphOperator (positiveEdge edge) (positivePart q) i| ≤
        G / alphaMin + incoming * alpha none * Q + incoming * B₀ := by
    have hincoming := hIncoming i
    have hincoming0 := hIncomingNonneg i
    have hqnone : |q none| = B₀ / alpha none := by
      dsimp only [B₀]
      rw [abs_mul, abs_of_pos hAlphaLow]
      field_simp [ne_of_gt hAlphaLow]
    have hdiff : |q (some i) - q none| ≤ Q + B₀ / alpha none := by
      calc
        |q (some i) - q none| ≤ |q (some i)| + |q none| := abs_sub _ _
        _ ≤ Q + B₀ / alpha none := add_le_add (hQpoint i) hqnone.le
    have hcoupling :
        |edge (some i) none * (q (some i) - q none)| ≤
          incoming * alpha none * Q + incoming * B₀ := by
      rw [abs_mul, abs_of_nonneg hincoming0]
      calc
        edge (some i) none * |q (some i) - q none| ≤
            (incoming * alpha none) * (Q + B₀ / alpha none) :=
          mul_le_mul hincoming hdiff (abs_nonneg _)
            (mul_nonneg hIncomingNonnegConst hAlphaLow.le)
        _ = incoming * alpha none * Q + incoming * B₀ := by
          field_simp [ne_of_gt hAlphaLow]
    calc
      |graphOperator (positiveEdge edge) (positivePart q) i| =
          |graphOperator edge q (some i) -
            edge (some i) none * (q (some i) - q none)| := by
        rw [graphOperator_some_decomposition]
        ring
      _ ≤ |graphOperator edge q (some i)| +
          |edge (some i) none * (q (some i) - q none)| := abs_sub _ _
      _ ≤ G / alphaMin +
          (incoming * alpha none * Q + incoming * B₀) :=
        add_le_add (hFullPositive i) hcoupling
      _ = _ := by ring
  obtain ⟨mu, hmu⟩ := exists_center_of_graphOperator_bound
    (positiveEdge edge) (fun j : Pos => anchor (some j))
    (positivePart q) hPositiveDom hkappa (by rw [hAnchorMass]; exact hAnchorMassPos)
      hRestricted
  have hmuK (i : Pos) :
      |q (some i) - mu| ≤
        K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀) := by
    have hi := hmu i
    rw [hAnchorMass] at hi
    calc
      |q (some i) - mu| ≤
          (G / alphaMin + incoming * alpha none * Q + incoming * B₀) /
            (kappa * anchorMass) := hi
      _ = K *
          (G / alphaMin + incoming * alpha none * Q + incoming * B₀) := by
        dsimp only [K]
        ring
  have hGaugeSplit :
      ∑ i : Pos, omega (some i) * q (some i) = -(omega none * q none) := by
    have hg : omega none * q none +
        ∑ i : Pos, omega (some i) * q (some i) = 0 := by
      simpa using hGauge
    linarith
  have hMeanClose := abs_weightedMean_le_of_close
    (fun i : Pos => omega (some i)) (positivePart q) mu
    (K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀))
    hOmegaPositiveNonneg hOmegaPositive hmuK
  have hMeanAbs :
      |(∑ i : Pos, omega (some i) * q (some i)) /
          (∑ i : Pos, omega (some i))| ≤ gaugeRatio * B₀ := by
    rw [hGaugeSplit, abs_div, abs_neg, abs_mul,
      abs_of_nonneg hOmegaLowNonneg, abs_of_pos hOmegaPositive]
    have hq0 : |q none| = B₀ / alpha none := by
      dsimp only [B₀]
      rw [abs_mul, abs_of_pos hAlphaLow]
      field_simp [ne_of_gt hAlphaLow]
    rw [hq0]
    apply (div_le_iff₀ hOmegaPositive).2
    calc
      omega none * (B₀ / alpha none) ≤
          (gaugeRatio * alpha none * (∑ i : Pos, omega (some i))) *
            (B₀ / alpha none) :=
        mul_le_mul_of_nonneg_right hGaugeRatio (div_nonneg hB₀nonneg hAlphaLow.le)
      _ = gaugeRatio * B₀ * (∑ i : Pos, omega (some i)) := by
        field_simp [ne_of_gt hAlphaLow]
  have hMuAbs :
      |mu| ≤
        K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀) +
          gaugeRatio * B₀ := by
    let m := (∑ i : Pos, omega (some i) * q (some i)) /
      (∑ i : Pos, omega (some i))
    calc
      |mu| = |(mu - m) + m| := by ring_nf
      _ ≤ |mu - m| + |m| := abs_add_le _ _
      _ = |m - mu| + |m| := by rw [abs_sub_comm]
      _ ≤ K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀) +
          gaugeRatio * B₀ := add_le_add hMeanClose hMeanAbs
  have hQIneq :
      Q ≤ 2 * K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀) +
        gaugeRatio * B₀ := by
    have hrightNonneg : 0 ≤
        2 * K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀) +
          gaugeRatio * B₀ := by positivity
    change ‖positivePart q‖ ≤ _
    rw [pi_norm_le_iff_of_nonneg hrightNonneg]
    intro i
    rw [Real.norm_eq_abs]
    calc
      |positivePart q i| = |(q (some i) - mu) + mu| := by
        simp [positivePart]
      _ ≤ |q (some i) - mu| + |mu| := abs_add_le _ _
      _ ≤ K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀) +
          (K * (G / alphaMin + incoming * alpha none * Q + incoming * B₀) +
            gaugeRatio * B₀) := add_le_add (hmuK i) hMuAbs
      _ = _ := by ring
  have hQClosed :
      Q ≤ (4 * K / alphaMin) * G +
        (4 * K * incoming + 2 * gaugeRatio) * B₀ := by
    have habsorb : 2 * K * incoming * alpha none ≤ 1 / 2 := by
      simpa only [K] using hAbsorbPositive
    have hQIneq' :
        Q ≤ (2 * K / alphaMin) * G +
          (2 * K * incoming * alpha none) * Q +
          (2 * K * incoming + gaugeRatio) * B₀ := by
      calc
        Q ≤ 2 * K *
            (G / alphaMin + incoming * alpha none * Q + incoming * B₀) +
              gaugeRatio * B₀ := hQIneq
        _ = _ := by ring
    have habsorbQ :
        (2 * K * incoming * alpha none) * Q ≤ (1 / 2 : ℝ) * Q :=
      mul_le_mul_of_nonneg_right habsorb hQnonneg
    have hhalf : (1 / 2 : ℝ) * Q ≤
        (2 * K / alphaMin) * G +
          (2 * K * incoming + gaugeRatio) * B₀ := by
      linarith [hQIneq', habsorbQ]
    calc
      Q = 2 * ((1 / 2 : ℝ) * Q) := by ring
      _ ≤ 2 * ((2 * K / alphaMin) * G +
          (2 * K * incoming + gaugeRatio) * B₀) :=
        mul_le_mul_of_nonneg_left hhalf (by norm_num)
      _ = _ := by ring
  have hLowEquation :
      alpha none * graphOperator edge q none =
        (∑ j : Pos, edge none (some j)) * (alpha none * q none) -
          alpha none * (∑ j : Pos, edge none (some j) * q (some j)) := by
    rw [graphOperator_none_decomposition, Finset.mul_sum]
    calc
      (∑ j : Pos, alpha none *
          (edge none (some j) * (q none - q (some j)))) =
          ∑ j : Pos,
            (edge none (some j) * (alpha none * q none) -
              alpha none * (edge none (some j) * q (some j))) := by
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j : Pos, edge none (some j) * (alpha none * q none)) -
          ∑ j : Pos, alpha none * (edge none (some j) * q (some j)) :=
        by rw [Finset.sum_sub_distrib]
      _ = _ := by
        rw [Finset.sum_mul, ← Finset.mul_sum]
  have hLowIneq :
      lowMass * B₀ ≤ G + alpha none * lowRowMass * Q := by
    have hout := hOutput none
    have hsumNonneg : 0 ≤ ∑ j : Pos, edge none (some j) :=
      Finset.sum_nonneg (fun j hj => hLowEdgeNonneg j)
    have hsumTerm :
        |∑ j : Pos, edge none (some j) * q (some j)| ≤
          lowRowMass * Q := by
      calc
        |∑ j : Pos, edge none (some j) * q (some j)| ≤
            ∑ j : Pos, |edge none (some j) * q (some j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Pos, edge none (some j) * Q := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul, abs_of_nonneg (hLowEdgeNonneg j)]
          exact mul_le_mul_of_nonneg_left (hQpoint j) (hLowEdgeNonneg j)
        _ = (∑ j : Pos, edge none (some j)) * Q := by
          rw [Finset.sum_mul]
        _ ≤ lowRowMass * Q :=
          mul_le_mul_of_nonneg_right hLowMassUpper hQnonneg
    have hmain :
        (∑ j : Pos, edge none (some j)) * B₀ ≤
          G + alpha none * lowRowMass * Q := by
      calc
        (∑ j : Pos, edge none (some j)) * B₀ =
            |(∑ j : Pos, edge none (some j)) *
              (alpha none * q none)| := by
          rw [abs_mul, abs_of_nonneg hsumNonneg]
        _ ≤ |alpha none * graphOperator edge q none| +
            |alpha none *
              (∑ j : Pos, edge none (some j) * q (some j))| := by
          have heq :
              (∑ j : Pos, edge none (some j)) * (alpha none * q none) =
                alpha none * graphOperator edge q none +
                  alpha none *
                    (∑ j : Pos, edge none (some j) * q (some j)) := by
            linarith [hLowEquation]
          rw [heq]
          exact abs_add_le _ _
        _ ≤ G + alpha none * (lowRowMass * Q) := by
          apply add_le_add hout
          rw [abs_mul, abs_of_pos hAlphaLow]
          exact mul_le_mul_of_nonneg_left hsumTerm hAlphaLow.le
        _ = _ := by ring
    exact (mul_le_mul_of_nonneg_right hLowMassLower hB₀nonneg).trans hmain
  have hB₀Closed :
      B₀ ≤
        2 * (1 / lowMass +
          alpha none * lowRowMass * (4 * K / alphaMin) / lowMass) * G := by
    have hcoef :
        alpha none * lowRowMass *
          (4 * K * incoming + 2 * gaugeRatio) / lowMass ≤ 1 / 2 := by
      simpa only [K] using hAbsorbLow
    have hlowDiv :
        B₀ ≤ G / lowMass +
          (alpha none * lowRowMass / lowMass) * Q := by
      calc
        B₀ ≤ (G + alpha none * lowRowMass * Q) / lowMass := by
          exact (le_div_iff₀ hLowMassPos).2 (by
            simpa [mul_comm] using hLowIneq)
        _ = G / lowMass +
            (alpha none * lowRowMass / lowMass) * Q := by ring
    have hscaleNonneg : 0 ≤ alpha none * lowRowMass / lowMass := by
      positivity
    have hQSub := mul_le_mul_of_nonneg_left hQClosed hscaleNonneg
    have hsub :
        B₀ ≤
          (1 / lowMass +
            alpha none * lowRowMass * (4 * K / alphaMin) / lowMass) * G +
          (alpha none * lowRowMass *
            (4 * K * incoming + 2 * gaugeRatio) / lowMass) * B₀ := by
      calc
        B₀ ≤ G / lowMass +
            (alpha none * lowRowMass / lowMass) * Q := hlowDiv
        _ ≤ G / lowMass +
            (alpha none * lowRowMass / lowMass) *
              ((4 * K / alphaMin) * G +
                (4 * K * incoming + 2 * gaugeRatio) * B₀) :=
          add_le_add le_rfl hQSub
        _ = _ := by ring
    have hcoefB :
        (alpha none * lowRowMass *
          (4 * K * incoming + 2 * gaugeRatio) / lowMass) * B₀ ≤
            (1 / 2 : ℝ) * B₀ :=
      mul_le_mul_of_nonneg_right hcoef hB₀nonneg
    have hhalf : (1 / 2 : ℝ) * B₀ ≤
        (1 / lowMass +
          alpha none * lowRowMass * (4 * K / alphaMin) / lowMass) * G := by
      linarith [hsub, hcoefB]
    linarith
  intro i
  cases i with
  | none =>
      exact hB₀Closed.trans (le_max_left _ _ |> fun h =>
        mul_le_mul_of_nonneg_right h hG)
  | some i =>
      have hAlphaMaxNonneg : 0 ≤ alphaMax :=
        (hAlphaPositiveNonneg i).trans (hAlphaPositiveUpper i)
      have hraw : |alpha (some i) * q (some i)| ≤ alphaMax * Q := by
        rw [abs_mul, abs_of_nonneg (hAlphaPositiveNonneg i)]
        exact mul_le_mul (hAlphaPositiveUpper i) (hQpoint i)
          (abs_nonneg _) hAlphaMaxNonneg
      calc
        |alpha (some i) * q (some i)| ≤ alphaMax * Q := hraw
        _ ≤ alphaMax * ((4 * K / alphaMin) * G +
            (4 * K * incoming + 2 * gaugeRatio) * B₀) := by
          exact mul_le_mul_of_nonneg_left hQClosed
            (hAlphaPositiveNonneg i |>.trans (hAlphaPositiveUpper i))
        _ ≤ alphaMax *
            ((4 * K / alphaMin) +
              (4 * K * incoming + 2 * gaugeRatio) *
                (2 * (1 / lowMass +
                  alpha none * lowRowMass * (4 * K / alphaMin) /
                    lowMass))) * G := by
          have hcoefNonneg :
              0 ≤ 4 * K * incoming + 2 * gaugeRatio := by positivity
          have hscaled :=
            mul_le_mul_of_nonneg_left hB₀Closed hcoefNonneg
          have hinterior :
              (4 * K / alphaMin) * G +
                  (4 * K * incoming + 2 * gaugeRatio) * B₀ ≤
                ((4 * K / alphaMin) +
                  (4 * K * incoming + 2 * gaugeRatio) *
                    (2 * (1 / lowMass +
                      alpha none * lowRowMass * (4 * K / alphaMin) /
                        lowMass))) * G := by
            calc
              (4 * K / alphaMin) * G +
                  (4 * K * incoming + 2 * gaugeRatio) * B₀ ≤
                (4 * K / alphaMin) * G +
                  (4 * K * incoming + 2 * gaugeRatio) *
                    (2 * (1 / lowMass +
                      alpha none * lowRowMass * (4 * K / alphaMin) /
                        lowMass) * G) := add_le_add le_rfl hscaled
              _ = _ := by ring
          calc
            alphaMax * ((4 * K / alphaMin) * G +
                (4 * K * incoming + 2 * gaugeRatio) * B₀) ≤
              alphaMax * (((4 * K / alphaMin) +
                (4 * K * incoming + 2 * gaugeRatio) *
                  (2 * (1 / lowMass +
                    alpha none * lowRowMass * (4 * K / alphaMin) /
                      lowMass))) * G) :=
                mul_le_mul_of_nonneg_left hinterior hAlphaMaxNonneg
            _ = _ := by ring
        _ ≤ max
            (2 * (1 / lowMass +
              alpha none * lowRowMass * (4 * K / alphaMin) / lowMass))
            (alphaMax *
              ((4 * K / alphaMin) +
                (4 * K * incoming + 2 * gaugeRatio) *
                  (2 * (1 / lowMass +
                    alpha none * lowRowMass * (4 * K / alphaMin) /
                      lowMass)))) * G := by
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) hG

end Erdos390.Full.FiniteOneLowRawGraphInverse
