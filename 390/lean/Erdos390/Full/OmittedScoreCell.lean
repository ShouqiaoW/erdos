import Erdos390.Full.OmittedScoreTilt
import Erdos390.Full.UniformFiniteProbability
import Erdos390.Full.DivisibilityMomentBounds

/-!
# Omitted-score normalization on an actual arithmetic cell

This module composes the genuine uniform probability law of a finite cell
with the marked exponential-tilt inequality.  All expectations in the result
are literal counting averages over that same cell; there is no implicit
identification between a counting formula and an abstract probability law.
-/

namespace Erdos390.Full.OmittedScoreCell

open FiniteProbability DivisibilityMomentBounds

noncomputable section

/-- Counting average on a nonempty finite cell is exactly expectation under
its genuine uniform finite probability law. -/
theorem uniform_expect_eq_uniformAverage
    (S : Finset ℕ) (hS : S.Nonempty) (F : ℕ → ℝ) :
    (uniformOnFinset S hS).expect (fun m : S ↦ F m) =
      uniformAverage S F := by
  rw [uniformOnFinset_expect_ambient_eq]
  rfl

/-- Exact marked-event comparison after a bounded score tilt, written only
in terms of actual cell averages. -/
theorem abs_uniformCell_tilt_expect_sub_average_le
    (S : Finset ℕ) (hS : S.Nonempty) (A score : ℕ → ℝ) {K : ℝ}
    (hA0 : ∀ m ∈ S, 0 ≤ A m)
    (hA1 : ∀ m ∈ S, A m ≤ 1)
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotal : Real.exp K *
        uniformAverage S (fun m ↦ |score m|) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect (fun m : S ↦ A m) -
        uniformAverage S A| ≤
      (Real.exp K * uniformAverage S
          (fun m ↦ A m * |score m|) +
        Real.exp K * uniformAverage S A *
          uniformAverage S (fun m ↦ |score m|)) /
        (1 - Real.exp K *
          uniformAverage S (fun m ↦ |score m|)) := by
  have havgA :
      (uniformOnFinset S hS).expect (fun m : S ↦ A m) =
        uniformAverage S A :=
    uniform_expect_eq_uniformAverage S hS A
  have havgAbs :
      (uniformOnFinset S hS).expect (fun m : S ↦ |score m|) =
        uniformAverage S (fun m ↦ |score m|) :=
    uniform_expect_eq_uniformAverage S hS (fun m ↦ |score m|)
  have havgMarked :
      (uniformOnFinset S hS).expect
          (fun m : S ↦ A m * |score m|) =
        uniformAverage S (fun m ↦ A m * |score m|) :=
    uniform_expect_eq_uniformAverage S hS
      (fun m ↦ A m * |score m|)
  have hbase :=
    (uniformOnFinset S hS).abs_exponentialTilt_expect_sub_expect_le_of_bounded_score
      (fun m : S ↦ A m) (fun m : S ↦ score m)
      (fun m ↦ hA0 m m.property)
      (fun m ↦ hA1 m m.property)
      (fun m ↦ hscore m m.property)
      (by rw [havgAbs]; exact htotal)
  rw [havgA, havgAbs, havgMarked] at hbase
  exact hbase

/-- Divisibility indicators satisfy the exact event hypotheses in the
preceding theorem. -/
theorem abs_uniformCell_tilt_divInd_sub_average_le
    (S : Finset ℕ) (hS : S.Nonempty) (D : ℕ) (score : ℕ → ℝ) {K : ℝ}
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotal : Real.exp K *
        uniformAverage S (fun m ↦ |score m|) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) -
        uniformAverage S (ArithmeticModel.divInd D)| ≤
      (Real.exp K * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * |score m|) +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          uniformAverage S (fun m ↦ |score m|)) /
        (1 - Real.exp K *
          uniformAverage S (fun m ↦ |score m|)) := by
  apply abs_uniformCell_tilt_expect_sub_average_le S hS
  · intro m hm
    exact ArithmeticModel.divInd_nonneg D m
  · intro m hm
    exact ArithmeticModel.divInd_le_one D m
  · exact hscore
  · exact htotal

/-- The paper-facing form: a weighted omitted score is pointwise dominated
by `beta` times the divisor-indicator score.  The conclusion now depends only
on the first unmarked and marked divisor-score moments, exactly the quantities
supplied by `DivisibilityMomentBounds`. -/
theorem abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
    (S R : Finset ℕ) (hS : S.Nonempty) (D : ℕ)
    (score : ℕ → ℝ) {K beta : ℝ}
    (hdom : ∀ m ∈ S,
      |score m| ≤ beta * divisorScore R m)
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotal : Real.exp K * beta *
        uniformAverage S (divisorScore R) < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) -
        uniformAverage S (ArithmeticModel.divInd D)| ≤
      (Real.exp K * beta * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * uniformAverage S (divisorScore R))) /
        (1 - Real.exp K * beta *
          uniformAverage S (divisorScore R)) := by
  let mu := uniformOnFinset S hS
  let p := uniformAverage S (ArithmeticModel.divInd D)
  let a := uniformAverage S (fun m ↦ |score m|)
  let Abar := beta * uniformAverage S (divisorScore R)
  let b := uniformAverage S
    (fun m ↦ ArithmeticModel.divInd D m * |score m|)
  let Bbar := beta * uniformAverage S
    (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m)
  have ha : a ≤ Abar := by
    have hmono := mu.expect_mono
      (fun m : S ↦ |score m|)
      (fun m : S ↦ beta * divisorScore R m)
      (fun m ↦ hdom m m.property)
    rw [uniform_expect_eq_uniformAverage S hS
        (fun m ↦ |score m|),
      uniform_expect_eq_uniformAverage S hS
        (fun m ↦ beta * divisorScore R m)] at hmono
    have hfactor : uniformAverage S
        (fun m ↦ beta * divisorScore R m) =
        beta * uniformAverage S (divisorScore R) := by
      unfold uniformAverage
      rw [← Finset.mul_sum]
      ring
    simpa only [a, Abar, hfactor] using hmono
  have hb : b ≤ Bbar := by
    have hpoint (m : S) :
        ArithmeticModel.divInd D m * |score m| ≤
          beta * (ArithmeticModel.divInd D m * divisorScore R m) := by
      have hmark := ArithmeticModel.divInd_nonneg D m
      calc
        ArithmeticModel.divInd D m * |score m| ≤
            ArithmeticModel.divInd D m *
              (beta * divisorScore R m) :=
          mul_le_mul_of_nonneg_left (hdom m m.property) hmark
        _ = beta *
            (ArithmeticModel.divInd D m * divisorScore R m) := by ring
    have hmono := mu.expect_mono
      (fun m : S ↦ ArithmeticModel.divInd D m * |score m|)
      (fun m : S ↦ beta *
        (ArithmeticModel.divInd D m * divisorScore R m)) hpoint
    rw [uniform_expect_eq_uniformAverage S hS
        (fun m ↦ ArithmeticModel.divInd D m * |score m|),
      uniform_expect_eq_uniformAverage S hS
        (fun m ↦ beta *
          (ArithmeticModel.divInd D m * divisorScore R m))] at hmono
    have hfactor : uniformAverage S
        (fun m ↦ beta *
          (ArithmeticModel.divInd D m * divisorScore R m)) =
        beta * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) := by
      unfold uniformAverage
      rw [← Finset.mul_sum]
      ring
    simpa only [b, Bbar, hfactor] using hmono
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    rw [← uniform_expect_eq_uniformAverage S hS
      (ArithmeticModel.divInd D)]
    exact mu.expect_nonneg _ fun m ↦ ArithmeticModel.divInd_nonneg D m
  have ha0 : 0 ≤ a := by
    dsimp only [a]
    rw [← uniform_expect_eq_uniformAverage S hS (fun m ↦ |score m|)]
    exact mu.expect_nonneg _ fun m ↦ abs_nonneg _
  have hb0 : 0 ≤ b := by
    dsimp only [b]
    rw [← uniform_expect_eq_uniformAverage S hS
      (fun m ↦ ArithmeticModel.divInd D m * |score m|)]
    exact mu.expect_nonneg _ fun m ↦
      mul_nonneg (ArithmeticModel.divInd_nonneg D m) (abs_nonneg _)
  have hAbar0 : 0 ≤ Abar := ha0.trans ha
  have hBbar0 : 0 ≤ Bbar := hb0.trans hb
  have hactualTotal : Real.exp K * a < 1 := by
    calc
      Real.exp K * a ≤ Real.exp K * Abar :=
        mul_le_mul_of_nonneg_left ha (Real.exp_pos K).le
      _ < 1 := by simpa only [Abar, mul_assoc] using htotal
  have hraw := abs_uniformCell_tilt_divInd_sub_average_le
    S hS D score hscore (by simpa only [a] using hactualTotal)
  change |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤ _
  have hraw' :
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤
        (Real.exp K * b + Real.exp K * p * a) /
          (1 - Real.exp K * a) := by
    simpa only [p, a, b] using hraw
  refine hraw'.trans ?_
  have hdenActual : 0 < 1 - Real.exp K * a :=
    sub_pos.mpr hactualTotal
  have hdenBound : 0 < 1 - Real.exp K * Abar := by
    simpa only [Abar, mul_assoc] using sub_pos.mpr htotal
  have hnum :
      Real.exp K * b + Real.exp K * p * a ≤
        Real.exp K * Bbar + Real.exp K * p * Abar := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hb (Real.exp_pos K).le)
      (mul_le_mul_of_nonneg_left ha
        (mul_nonneg (Real.exp_pos K).le hp0))
  have htarget0 :
      0 ≤ Real.exp K * Bbar + Real.exp K * p * Abar :=
    add_nonneg
      (mul_nonneg (Real.exp_pos K).le hBbar0)
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hp0) hAbar0)
  calc
    (Real.exp K * b + Real.exp K * p * a) /
        (1 - Real.exp K * a) ≤
      (Real.exp K * Bbar + Real.exp K * p * Abar) /
        (1 - Real.exp K * a) :=
      div_le_div_of_nonneg_right hnum hdenActual.le
    _ ≤ (Real.exp K * Bbar + Real.exp K * p * Abar) /
        (1 - Real.exp K * Abar) := by
      apply div_le_div_of_nonneg_left htarget0 hdenBound
      linarith [mul_le_mul_of_nonneg_left ha (Real.exp_pos K).le]
    _ = (Real.exp K * beta * uniformAverage S
          (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * uniformAverage S (divisorScore R))) /
        (1 - Real.exp K * beta *
          uniformAverage S (divisorScore R)) := by
      dsimp only [Abar, Bbar, p]
      ring

/-- Substitute explicit upper bounds for the unmarked and marked
divisor-score moments.  This is the final deterministic comparison needed
before inserting the common-multiple estimates. -/
theorem abs_uniformCell_tilt_divInd_le_of_divisorScore_moment_bounds
    (S R : Finset ℕ) (hS : S.Nonempty) (D : ℕ)
    (score : ℕ → ℝ) {K beta totalBound markedBound : ℝ}
    (hbeta : 0 ≤ beta)
    (hdom : ∀ m ∈ S,
      |score m| ≤ beta * divisorScore R m)
    (hscore : ∀ m ∈ S, |score m| ≤ K)
    (htotalMoment :
      uniformAverage S (divisorScore R) ≤ totalBound)
    (hmarkedMoment : uniformAverage S
      (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m) ≤
        markedBound)
    (htotalBound : 0 ≤ totalBound)
    (hmarkedBound : 0 ≤ markedBound)
    (hsmall : Real.exp K * beta * totalBound < 1) :
    |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) -
        uniformAverage S (ArithmeticModel.divInd D)| ≤
      (Real.exp K * beta * markedBound +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * totalBound)) /
        (1 - Real.exp K * beta * totalBound) := by
  have hactualSmall : Real.exp K * beta *
      uniformAverage S (divisorScore R) < 1 := by
    calc
      Real.exp K * beta * uniformAverage S (divisorScore R) ≤
          Real.exp K * beta * totalBound :=
        mul_le_mul_of_nonneg_left htotalMoment
          (mul_nonneg (Real.exp_pos K).le hbeta)
      _ < 1 := hsmall
  have hbase :=
    abs_uniformCell_tilt_divInd_le_of_divisorScore_domination
      S R hS D score hdom hscore hactualSmall
  let p := uniformAverage S (ArithmeticModel.divInd D)
  let Tactual := uniformAverage S (divisorScore R)
  let Bactual := uniformAverage S
    (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m)
  have hp0 : 0 ≤ p := by
    dsimp only [p]
    rw [← uniform_expect_eq_uniformAverage S hS
      (ArithmeticModel.divInd D)]
    exact (uniformOnFinset S hS).expect_nonneg _ fun m ↦
      ArithmeticModel.divInd_nonneg D m
  have hTactual0 : 0 ≤ Tactual := by
    dsimp only [Tactual]
    rw [← uniform_expect_eq_uniformAverage S hS (divisorScore R)]
    exact (uniformOnFinset S hS).expect_nonneg _ fun m ↦ by
      unfold divisorScore
      exact Finset.sum_nonneg fun a ha ↦
        ArithmeticModel.divInd_nonneg a m
  have hBactual0 : 0 ≤ Bactual := by
    dsimp only [Bactual]
    rw [← uniform_expect_eq_uniformAverage S hS
      (fun m ↦ ArithmeticModel.divInd D m * divisorScore R m)]
    exact (uniformOnFinset S hS).expect_nonneg _ fun m ↦
      mul_nonneg (ArithmeticModel.divInd_nonneg D m) (by
        unfold divisorScore
        exact Finset.sum_nonneg fun a ha ↦
          ArithmeticModel.divInd_nonneg a m)
  have hdenActual : 0 < 1 - Real.exp K * beta * Tactual := by
    dsimp only [Tactual]
    exact sub_pos.mpr hactualSmall
  have hdenBound : 0 < 1 - Real.exp K * beta * totalBound :=
    sub_pos.mpr hsmall
  have hnum :
      Real.exp K * beta * Bactual +
          Real.exp K * p * (beta * Tactual) ≤
        Real.exp K * beta * markedBound +
          Real.exp K * p * (beta * totalBound) := by
    exact add_le_add
      (mul_le_mul_of_nonneg_left hmarkedMoment
        (mul_nonneg (Real.exp_pos K).le hbeta))
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left htotalMoment hbeta)
        (mul_nonneg (Real.exp_pos K).le hp0))
  have htarget0 : 0 ≤
      Real.exp K * beta * markedBound +
        Real.exp K * p * (beta * totalBound) :=
    add_nonneg
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hbeta) hmarkedBound)
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hp0)
        (mul_nonneg hbeta htotalBound))
  have hbase' :
      |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤
        (Real.exp K * beta * Bactual +
          Real.exp K * p * (beta * Tactual)) /
          (1 - Real.exp K * beta * Tactual) := by
    simpa only [p, Tactual, Bactual] using hbase
  change |((uniformOnFinset S hS).exponentialTilt
          (fun m : S ↦ score m)).expect
          (fun m : S ↦ ArithmeticModel.divInd D m) - p| ≤ _
  refine hbase'.trans ?_
  calc
    (Real.exp K * beta * Bactual +
        Real.exp K * p * (beta * Tactual)) /
        (1 - Real.exp K * beta * Tactual) ≤
      (Real.exp K * beta * markedBound +
        Real.exp K * p * (beta * totalBound)) /
        (1 - Real.exp K * beta * Tactual) :=
      div_le_div_of_nonneg_right hnum hdenActual.le
    _ ≤ (Real.exp K * beta * markedBound +
        Real.exp K * p * (beta * totalBound)) /
        (1 - Real.exp K * beta * totalBound) := by
      apply div_le_div_of_nonneg_left htarget0 hdenBound
      have hscaled : Real.exp K * beta * Tactual ≤
          Real.exp K * beta * totalBound :=
        mul_le_mul_of_nonneg_left htotalMoment
          (mul_nonneg (Real.exp_pos K).le hbeta)
      linarith
    _ = (Real.exp K * beta * markedBound +
        Real.exp K * uniformAverage S (ArithmeticModel.divInd D) *
          (beta * totalBound)) /
        (1 - Real.exp K * beta * totalBound) := by
      rfl

end

end Erdos390.Full.OmittedScoreCell
