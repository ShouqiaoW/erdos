import Erdos390.Full.FiniteTiltTV
import Erdos390.Full.PrimePowerCovariance

/-!
# Normalized marked-event bounds under an omitted-score tilt

The four-mark step in Lemma 7.5 first omits the forced local primes from
the score, estimates a marked numerator, and then divides by the tilted
partition function.  This file proves that normalization step for an actual
finite probability law.  The result keeps the marked and unmarked
exponential deviations separate, so a `1 / D` marked moment is not replaced
by an unscaled total-variation error.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Exponential deviation carrying an additional nonnegative mark. -/
def markedExponentialDeviation (mu : FiniteProbability Omega)
    (A S : Omega → ℝ) : ℝ :=
  mu.expect (fun omega ↦ A omega * |Real.exp (S omega) - 1|)

theorem markedExponentialDeviation_nonneg
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    0 ≤ mu.markedExponentialDeviation A S := by
  unfold markedExponentialDeviation
  exact mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA omega) (abs_nonneg _)

/-- Global real-exponential increment bound, with no smallness hypothesis. -/
theorem abs_exp_sub_one_le_exp_abs_mul_abs (x : ℝ) :
    |Real.exp x - 1| ≤ Real.exp |x| * |x| := by
  by_cases hx : 0 ≤ x
  · have hexpOne : 1 ≤ Real.exp x := Real.one_le_exp hx
    have hbase := Real.add_one_le_exp (-x)
    have hmul := mul_le_mul_of_nonneg_left hbase (Real.exp_pos x).le
    have hprod : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add]
      simp
    rw [hprod] at hmul
    rw [abs_of_nonneg hx, abs_of_nonneg (sub_nonneg.mpr hexpOne)]
    nlinarith [Real.exp_pos x]
  · have hxneg : x < 0 := lt_of_not_ge hx
    have hexpOne : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hxneg.le
    have hlinear := Real.add_one_le_exp x
    have hone : 1 ≤ Real.exp (-x) := Real.one_le_exp (neg_nonneg.mpr hxneg.le)
    have hmul : -x ≤ Real.exp (-x) * (-x) := by
      simpa using
        (mul_le_mul_of_nonneg_right hone (neg_nonneg.mpr hxneg.le))
    rw [abs_of_neg hxneg, abs_of_nonpos (sub_nonpos.mpr hexpOne)]
    nlinarith

/-- A pointwise score bound converts the marked first absolute moment into
an exponential-deviation bound.  The constant may depend on the already
fixed score box, while the arithmetic mark remains visible. -/
theorem markedExponentialDeviation_le_exp_mul_expect_abs
    (mu : FiniteProbability Omega) (A S : Omega → ℝ) {K : ℝ}
    (hA : ∀ omega, 0 ≤ A omega)
    (hbound : ∀ omega, |S omega| ≤ K) :
    mu.markedExponentialDeviation A S ≤
      Real.exp K * mu.expect (fun omega ↦ A omega * |S omega|) := by
  unfold markedExponentialDeviation expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  have hexp : Real.exp |S omega| ≤ Real.exp K :=
    Real.exp_le_exp.mpr (hbound omega)
  have hinc : |Real.exp (S omega) - 1| ≤
      Real.exp K * |S omega| := by
    exact (abs_exp_sub_one_le_exp_abs_mul_abs (S omega)).trans
      (mul_le_mul_of_nonneg_right hexp (abs_nonneg _))
  calc
    mu.mass omega * (A omega * |Real.exp (S omega) - 1|) ≤
        mu.mass omega * (A omega * (Real.exp K * |S omega|)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hinc (hA omega))
        (mu.mass_nonneg omega)
    _ = Real.exp K * (mu.mass omega * (A omega * |S omega|)) := by ring

theorem exponentialDeviation_le_exp_mul_expect_abs
    (mu : FiniteProbability Omega) (S : Omega → ℝ) {K : ℝ}
    (hbound : ∀ omega, |S omega| ≤ K) :
    mu.exponentialDeviation S ≤
      Real.exp K * mu.expect (fun omega ↦ |S omega|) := by
  have hmarked := mu.markedExponentialDeviation_le_exp_mul_expect_abs
    (fun _ ↦ (1 : ℝ)) S (fun _ ↦ zero_le_one) hbound
  simpa [markedExponentialDeviation] using hmarked

/-- A box-uniform total-variation estimate for a normalized exponential
tilt.  The score need not converge uniformly to zero: it is enough that it
remain in a fixed box and that its first absolute moment tend to zero.  This
is the form needed when the medium-prime score is pointwise bounded but only
small on average. -/
theorem l1Distance_exponentialTilt_le_of_bounded_score
    (mu : FiniteProbability Omega) (S : Omega → ℝ) {K : ℝ}
    (hbound : ∀ omega, |S omega| ≤ K)
    (htotal : Real.exp K * mu.expect (fun omega ↦ |S omega|) < 1) :
    mu.l1Distance (mu.exponentialTilt S) ≤
      (2 * (Real.exp K * mu.expect (fun omega ↦ |S omega|))) /
        (1 - Real.exp K * mu.expect (fun omega ↦ |S omega|)) := by
  let a := mu.expect (fun omega ↦ |S omega|)
  let eps := mu.exponentialDeviation S
  let M := Real.exp K * a
  have ha0 : 0 ≤ a := mu.expect_nonneg _ fun omega ↦ abs_nonneg _
  have hM0 : 0 ≤ M :=
    mul_nonneg (Real.exp_pos K).le ha0
  have heps0 : 0 ≤ eps := mu.exponentialDeviation_nonneg S
  have hepsM : eps ≤ M :=
    mu.exponentialDeviation_le_exp_mul_expect_abs S hbound
  have heps1 : eps < 1 := hepsM.trans_lt htotal
  have hdenEps : 0 < 1 - eps := sub_pos.mpr heps1
  have hdenM : 0 < 1 - M := sub_pos.mpr htotal
  refine (mu.l1Distance_exponentialTilt_le S heps1).trans ?_
  change 2 * eps / (1 - eps) ≤ 2 * M / (1 - M)
  apply (div_le_div_iff₀ hdenEps hdenM).2
  nlinarith

/-- Exact expectation formula under the normalized exponential tilt. -/
theorem exponentialTilt_expect_eq
    (mu : FiniteProbability Omega) (A S : Omega → ℝ) :
    (mu.exponentialTilt S).expect A =
      mu.expect (fun omega ↦ A omega * Real.exp (S omega)) /
        mu.expPartition S := by
  unfold expect
  change (∑ omega, (mu.mass omega * Real.exp (S omega) /
      mu.expPartition S) * A omega) = _
  calc
    (∑ omega, (mu.mass omega * Real.exp (S omega) /
        mu.expPartition S) * A omega) =
        ∑ omega, (mu.mass omega * (A omega * Real.exp (S omega))) /
          mu.expPartition S := by
      apply Finset.sum_congr rfl
      intro omega _
      ring
    _ = (∑ omega, mu.mass omega *
        (A omega * Real.exp (S omega))) / mu.expPartition S := by
      rw [Finset.sum_div]

/-- The marked numerator differs from its untilted value by at most the
marked exponential deviation. -/
theorem abs_expWeighted_expect_sub_expect_le
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA : ∀ omega, 0 ≤ A omega) :
    |mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
        mu.expect A| ≤ mu.markedExponentialDeviation A S := by
  have hrearrange :
      mu.expect (fun omega ↦ A omega * Real.exp (S omega)) -
          mu.expect A =
        ∑ omega, mu.mass omega * A omega *
          (Real.exp (S omega) - 1) := by
    unfold expect
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro omega _
    ring
  rw [hrearrange]
  calc
    |∑ omega, mu.mass omega * A omega *
        (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * A omega *
          (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.markedExponentialDeviation A S := by
      unfold markedExponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_mul, abs_of_nonneg (mu.mass_nonneg omega),
        abs_of_nonneg (hA omega)]
      ring

/-- Exact normalization inequality for a marked event/statistic.  Unlike a
global total-variation estimate, the leading numerator error retains the
mark and hence its arithmetic `1 / D` scale. -/
theorem abs_exponentialTilt_expect_sub_expect_le
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hdev : mu.exponentialDeviation S < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (mu.markedExponentialDeviation A S +
          mu.expect A * mu.exponentialDeviation S) /
        (1 - mu.exponentialDeviation S) := by
  let Z := mu.expPartition S
  let p := mu.expect A
  let N := mu.expect (fun omega ↦ A omega * Real.exp (S omega))
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have hZpos : 0 < Z := mu.expPartition_pos S
  have hdenpos : 0 < 1 - delta := sub_pos.mpr hdev
  have hZlower : 1 - delta ≤ Z := mu.expPartition_lower_bound S
  have hp0 : 0 ≤ p := mu.expect_nonneg A hA0
  have hp1 : p ≤ 1 := by
    calc
      p ≤ mu.expect (fun _ ↦ (1 : ℝ)) := mu.expect_mono A _ hA1
      _ = 1 := by simp [expect, mu.mass_sum]
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have heta0 : 0 ≤ eta :=
    mu.markedExponentialDeviation_nonneg A S hA0
  have hN : |N - p| ≤ eta := by
    exact mu.abs_expWeighted_expect_sub_expect_le A S hA0
  have hZ : |Z - 1| ≤ delta :=
    mu.abs_expPartition_sub_one_le_deviation S
  rw [mu.exponentialTilt_expect_eq A S]
  change |N / Z - p| ≤ (eta + p * delta) / (1 - delta)
  have hid : N / Z - p = ((N - p) + p * (1 - Z)) / Z := by
    field_simp
    ring
  rw [hid, abs_div, abs_of_pos hZpos]
  have hnum : |(N - p) + p * (1 - Z)| ≤ eta + p * delta := by
    calc
      |(N - p) + p * (1 - Z)| ≤
          |N - p| + |p * (1 - Z)| := abs_add_le _ _
      _ = |N - p| + p * |Z - 1| := by
        rw [abs_mul, abs_of_nonneg hp0, abs_sub_comm 1 Z]
      _ ≤ eta + p * delta := by
        exact add_le_add hN (mul_le_mul_of_nonneg_left hZ hp0)
  calc
    |(N - p) + p * (1 - Z)| / Z ≤
        (eta + p * delta) / Z :=
      div_le_div_of_nonneg_right hnum hZpos.le
    _ ≤ (eta + p * delta) / (1 - delta) := by
      apply div_le_div_of_nonneg_left
      · exact add_nonneg heta0 (mul_nonneg hp0 hdelta0)
      · exact hdenpos
      · exact hZlower

/-- If the score itself is pointwise at most one, first marked and unmarked
absolute moments give a completely explicit version of the normalization
bound. -/
theorem abs_exponentialTilt_expect_sub_expect_le_of_small_score
    (mu : FiniteProbability Omega) (A S : Omega → ℝ)
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hsmall : ∀ omega, |S omega| ≤ 1)
    (htotal : 2 * mu.expect (fun omega ↦ |S omega|) < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (2 * mu.expect (fun omega ↦ A omega * |S omega|) +
          2 * mu.expect A * mu.expect (fun omega ↦ |S omega|)) /
        (1 - 2 * mu.expect (fun omega ↦ |S omega|)) := by
  let a := mu.expect (fun omega ↦ |S omega|)
  let b := mu.expect (fun omega ↦ A omega * |S omega|)
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have ha0 : 0 ≤ a := mu.expect_nonneg _ fun omega ↦ abs_nonneg _
  have hb0 : 0 ≤ b := mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA0 omega) (abs_nonneg _)
  have hp0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have hdelta : delta ≤ 2 * a :=
    mu.exponentialDeviation_le_two_expect_abs S hsmall
  have hdelta1 : delta < 1 := hdelta.trans_lt htotal
  have heta : eta ≤ 2 * b := by
    unfold eta markedExponentialDeviation b expect
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro omega _
    calc
      mu.mass omega *
          (A omega * |Real.exp (S omega) - 1|) ≤
          mu.mass omega * (A omega * (2 * |S omega|)) := by
        apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
        exact mul_le_mul_of_nonneg_left
          (Real.abs_exp_sub_one_le (hsmall omega)) (hA0 omega)
      _ = 2 * (mu.mass omega * (A omega * |S omega|)) := by ring
  have hbase :=
    mu.abs_exponentialTilt_expect_sub_expect_le A S hA0 hA1 hdelta1
  refine hbase.trans ?_
  have hdenDelta : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hdenA : 0 < 1 - 2 * a := sub_pos.mpr htotal
  apply (div_le_div_iff₀ hdenDelta hdenA).2
  have hnum : eta + mu.expect A * delta ≤
      2 * b + 2 * mu.expect A * a := by
    calc
      eta + mu.expect A * delta ≤
          2 * b + mu.expect A * (2 * a) :=
        add_le_add heta (mul_le_mul_of_nonneg_left hdelta hp0)
      _ = 2 * b + 2 * mu.expect A * a := by ring
  nlinarith

/-- Box-uniform version of the same result.  Only the explicit factor
`exp K` depends on the pointwise score box; the marked first moment is left
on its original arithmetic scale. -/
theorem abs_exponentialTilt_expect_sub_expect_le_of_bounded_score
    (mu : FiniteProbability Omega) (A S : Omega → ℝ) {K : ℝ}
    (hA0 : ∀ omega, 0 ≤ A omega)
    (hA1 : ∀ omega, A omega ≤ 1)
    (hbound : ∀ omega, |S omega| ≤ K)
    (htotal : Real.exp K * mu.expect (fun omega ↦ |S omega|) < 1) :
    |(mu.exponentialTilt S).expect A - mu.expect A| ≤
      (Real.exp K * mu.expect (fun omega ↦ A omega * |S omega|) +
          Real.exp K * mu.expect A *
            mu.expect (fun omega ↦ |S omega|)) /
        (1 - Real.exp K * mu.expect (fun omega ↦ |S omega|)) := by
  let a := mu.expect (fun omega ↦ |S omega|)
  let b := mu.expect (fun omega ↦ A omega * |S omega|)
  let delta := mu.exponentialDeviation S
  let eta := mu.markedExponentialDeviation A S
  have ha0 : 0 ≤ a := mu.expect_nonneg _ fun omega ↦ abs_nonneg _
  have hb0 : 0 ≤ b := mu.expect_nonneg _ fun omega ↦
    mul_nonneg (hA0 omega) (abs_nonneg _)
  have hp0 : 0 ≤ mu.expect A := mu.expect_nonneg A hA0
  have hdelta0 : 0 ≤ delta := mu.exponentialDeviation_nonneg S
  have hdelta : delta ≤ Real.exp K * a :=
    mu.exponentialDeviation_le_exp_mul_expect_abs S hbound
  have hdelta1 : delta < 1 := hdelta.trans_lt htotal
  have heta : eta ≤ Real.exp K * b :=
    mu.markedExponentialDeviation_le_exp_mul_expect_abs A S hA0 hbound
  have hbase :=
    mu.abs_exponentialTilt_expect_sub_expect_le A S hA0 hA1 hdelta1
  refine hbase.trans ?_
  have hdenDelta : 0 < 1 - delta := sub_pos.mpr hdelta1
  have hdenA : 0 < 1 - Real.exp K * a := sub_pos.mpr htotal
  have hnum : eta + mu.expect A * delta ≤
      Real.exp K * b + Real.exp K * mu.expect A * a := by
    calc
      eta + mu.expect A * delta ≤
          Real.exp K * b + mu.expect A * (Real.exp K * a) :=
        add_le_add heta (mul_le_mul_of_nonneg_left hdelta hp0)
      _ = Real.exp K * b + Real.exp K * mu.expect A * a := by ring
  have htarget0 : 0 ≤ Real.exp K * b + Real.exp K * mu.expect A * a := by
    exact add_nonneg
      (mul_nonneg (Real.exp_pos K).le hb0)
      (mul_nonneg (mul_nonneg (Real.exp_pos K).le hp0) ha0)
  calc
    (eta + mu.expect A * delta) / (1 - delta) ≤
        (Real.exp K * b + Real.exp K * mu.expect A * a) /
          (1 - delta) :=
      div_le_div_of_nonneg_right hnum hdenDelta.le
    _ ≤ (Real.exp K * b + Real.exp K * mu.expect A * a) /
          (1 - Real.exp K * a) := by
      apply div_le_div_of_nonneg_left htarget0 hdenA
      linarith

end FiniteProbability

end

end Erdos390.Full
