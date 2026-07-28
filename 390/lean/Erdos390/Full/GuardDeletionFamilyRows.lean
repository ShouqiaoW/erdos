import Erdos390.Full.GuardDeletionProbability

/-!
# Family-summed guard-deletion bounds

A pointwise covariance perturbation followed by a sum over every medium prime
would lose the cardinality of the prime band.  The paper instead uses that, on
each integer, the *total* medium-prime valuation is `O(log n)`.  The lemmas in
this file formalize exactly that argument for an arbitrary finite family.
-/

open scoped BigOperators

namespace Erdos390.Full.FiniteProbability

noncomputable section

variable {Omega I : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype I]

omit [DecidableEq Omega] in
/-- Summing absolute expectations costs the pointwise `l¹` envelope of the
whole family, not the cardinality of the index set. -/
theorem sum_abs_expect_le_familyEnvelope
    (mu : FiniteProbability Omega) (H : I → Omega → ℝ)
    {K : ℝ}
    (henv : ∀ x, ∑ i, |H i x| ≤ K) :
    ∑ i, |mu.expect (H i)| ≤ K := by
  calc
    ∑ i, |mu.expect (H i)| ≤
        ∑ i, ∑ x, mu.mass x * |H i x| := by
      apply Finset.sum_le_sum
      intro i hi
      unfold expect
      calc
        |∑ x, mu.mass x * H i x| ≤
            ∑ x, |mu.mass x * H i x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x, mu.mass x * |H i x| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ = ∑ x, mu.mass x * ∑ i, |H i x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ ≤ ∑ x, mu.mass x * K := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (henv x) (mu.mass_nonneg x)
    _ = K := by rw [← Finset.sum_mul, mu.mass_sum, one_mul]

omit [DecidableEq Omega] in
/-- The same family envelope controls the sum of all unnormalized guard
moments. -/
theorem sum_abs_guardMoment_le_familyEnvelope
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (H : I → Omega → ℝ) {K : ℝ}
    (henv : ∀ x, ∑ i, |H i x| ≤ K) :
    ∑ i, |mu.guardMoment G (H i)| ≤ mu.guardMass G * K := by
  calc
    ∑ i, |mu.guardMoment G (H i)| ≤
        ∑ i, ∑ x ∈ G, mu.mass x * |H i x| := by
      apply Finset.sum_le_sum
      intro i hi
      unfold guardMoment
      calc
        |∑ x ∈ G, mu.mass x * H i x| ≤
            ∑ x ∈ G, |mu.mass x * H i x| :=
          Finset.abs_sum_le_sum_abs _ _
        _ = ∑ x ∈ G, mu.mass x * |H i x| := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ = ∑ x ∈ G, mu.mass x * ∑ i, |H i x| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.mul_sum]
    _ ≤ ∑ x ∈ G, mu.mass x * K := by
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (henv x) (mu.mass_nonneg x)
    _ = mu.guardMass G * K := by
      unfold guardMass
      rw [Finset.sum_mul]

/-- Family-summed expectation perturbation.  The proof uses the exact
conditional-normalization formula and therefore has no hidden factor
`card I`. -/
theorem sum_abs_deleteGuards_expect_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (H : I → Omega → ℝ) {K : ℝ}
    (henv : ∀ x, ∑ i, |H i x| ≤ K) :
    ∑ i,
        |(mu.deleteGuards G hsmall).expect (H i) - mu.expect (H i)| ≤
      K * mu.guardPerturbation G := by
  let delta := mu.guardMass G
  let nu := mu.deleteGuards G hsmall
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := sub_pos.mpr hsmall
  have hE := mu.sum_abs_expect_le_familyEnvelope H henv
  have hR := mu.sum_abs_guardMoment_le_familyEnvelope G H henv
  have hpoint (i : I) :
      |nu.expect (H i) - mu.expect (H i)| ≤
        (delta * |mu.expect (H i)| + |mu.guardMoment G (H i)|) /
          (1 - delta) := by
    rw [show nu.expect (H i) =
        (mu.expect (H i) - mu.guardMoment G (H i)) / (1 - delta) by
      simpa only [nu, delta] using mu.deleteGuards_expect G hsmall (H i)]
    have hid :
        (mu.expect (H i) - mu.guardMoment G (H i)) / (1 - delta) -
            mu.expect (H i) =
          (delta * mu.expect (H i) - mu.guardMoment G (H i)) /
            (1 - delta) := by
      field_simp [hden.ne']
      ring
    rw [hid, abs_div, abs_of_pos hden]
    apply div_le_div_of_nonneg_right _ hden.le
    calc
      |delta * mu.expect (H i) - mu.guardMoment G (H i)| ≤
          |delta * mu.expect (H i)| + |mu.guardMoment G (H i)| :=
        abs_sub _ _
      _ = delta * |mu.expect (H i)| + |mu.guardMoment G (H i)| := by
        rw [abs_mul, abs_of_nonneg hdelta0]
  calc
    ∑ i, |nu.expect (H i) - mu.expect (H i)| ≤
        ∑ i,
          (delta * |mu.expect (H i)| + |mu.guardMoment G (H i)|) /
            (1 - delta) := Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (delta * (∑ i, |mu.expect (H i)|) +
          ∑ i, |mu.guardMoment G (H i)|) / (1 - delta) := by
      rw [← Finset.sum_div]
      congr 1
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ (delta * K + delta * K) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact add_le_add (mul_le_mul_of_nonneg_left hE hdelta0) hR
    _ = K * mu.guardPerturbation G := by
      unfold guardPerturbation
      dsimp only [delta]
      ring

/-- Family-summed covariance perturbation.  This is the row estimate needed
for guard deletion: its right side sees the pointwise sum of the marked
statistics, never their number. -/
theorem sum_abs_deleteGuards_covariance_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (F : Omega → ℝ) (H : I → Omega → ℝ)
    {KF KH : ℝ} (hKF : 0 ≤ KF)
    (hF : ∀ x, |F x| ≤ KF)
    (hH : ∀ x, ∑ i, |H i x| ≤ KH) :
    ∑ i,
        |(mu.deleteGuards G hsmall).covariance F (H i) -
          mu.covariance F (H i)| ≤
      3 * KF * KH * mu.guardPerturbation G := by
  let nu := mu.deleteGuards G hsmall
  let d := mu.guardPerturbation G
  let FH : I → Omega → ℝ := fun i x ↦ F x * H i x
  have hd0 : 0 ≤ d := mu.guardPerturbation_nonneg G hsmall
  have hFH : ∀ x, ∑ i, |FH i x| ≤ KF * KH := by
    intro x
    calc
      ∑ i, |FH i x| = |F x| * ∑ i, |H i x| := by
        simp only [FH, abs_mul, Finset.mul_sum]
      _ ≤ KF * KH := mul_le_mul (hF x) (hH x) (by positivity) hKF
  have hprod : ∑ i, |nu.expect (FH i) - mu.expect (FH i)| ≤
      (KF * KH) * d := by
    simpa only [nu, d] using
      mu.sum_abs_deleteGuards_expect_sub_le G hsmall FH
        hFH
  have hHdiff : ∑ i, |nu.expect (H i) - mu.expect (H i)| ≤
      KH * d := by
    simpa only [nu, d] using
      mu.sum_abs_deleteGuards_expect_sub_le G hsmall H hH
  have hnuH : ∑ i, |nu.expect (H i)| ≤ KH :=
    nu.sum_abs_expect_le_familyEnvelope H hH
  have hmuF : |mu.expect F| ≤ KF :=
    mu.abs_expect_le_of_abs_le F hKF hF
  have hFdiff : |nu.expect F - mu.expect F| ≤ KF * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall F hKF hF
  have hpoint (i : I) :
      |nu.covariance F (H i) - mu.covariance F (H i)| ≤
        |nu.expect (FH i) - mu.expect (FH i)| +
          |nu.expect F - mu.expect F| * |nu.expect (H i)| +
          |mu.expect F| * |nu.expect (H i) - mu.expect (H i)| := by
    unfold covariance
    have hmean :
        nu.expect F * nu.expect (H i) - mu.expect F * mu.expect (H i) =
          (nu.expect F - mu.expect F) * nu.expect (H i) +
            mu.expect F * (nu.expect (H i) - mu.expect (H i)) := by ring
    rw [show
      (nu.expect (fun x ↦ F x * H i x) -
          nu.expect F * nu.expect (H i)) -
        (mu.expect (fun x ↦ F x * H i x) -
          mu.expect F * mu.expect (H i)) =
        (nu.expect (FH i) - mu.expect (FH i)) -
          (nu.expect F * nu.expect (H i) -
            mu.expect F * mu.expect (H i)) by
          simp only [FH]
          ring,
      hmean]
    let A := nu.expect (FH i) - mu.expect (FH i)
    let B₁ := (nu.expect F - mu.expect F) * nu.expect (H i)
    let B₂ := mu.expect F * (nu.expect (H i) - mu.expect (H i))
    have houter : |A - (B₁ + B₂)| ≤ |A| + |B₁ + B₂| :=
      abs_sub A (B₁ + B₂)
    have hinner : |B₁ + B₂| ≤ |B₁| + |B₂| := abs_add_le B₁ B₂
    have htotal : |A - (B₁ + B₂)| ≤ |A| + |B₁| + |B₂| := by
      exact houter.trans (by linarith)
    dsimp only [A, B₁, B₂] at htotal
    simpa only [abs_mul] using htotal
  calc
    ∑ i, |nu.covariance F (H i) - mu.covariance F (H i)| ≤
        ∑ i, (|nu.expect (FH i) - mu.expect (FH i)| +
          |nu.expect F - mu.expect F| * |nu.expect (H i)| +
          |mu.expect F| * |nu.expect (H i) - mu.expect (H i)|) :=
      Finset.sum_le_sum fun i hi ↦ hpoint i
    _ = (∑ i, |nu.expect (FH i) - mu.expect (FH i)|) +
          |nu.expect F - mu.expect F| * (∑ i, |nu.expect (H i)|) +
          |mu.expect F| *
            (∑ i, |nu.expect (H i) - mu.expect (H i)|) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        Finset.mul_sum, Finset.mul_sum]
    _ ≤ (KF * KH) * d + (KF * d) * KH + KF * (KH * d) := by
      exact add_le_add
        (add_le_add hprod
          (mul_le_mul hFdiff hnuH (by positivity) (mul_nonneg hKF hd0)))
        (mul_le_mul hmuF hHdiff (by positivity) hKF)
    _ = 3 * KF * KH * mu.guardPerturbation G := by
      dsimp only [d]
      ring

end

end Erdos390.Full.FiniteProbability
