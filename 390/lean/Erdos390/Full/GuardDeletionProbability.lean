import Erdos390.Full.FiniteTiltTV
import Erdos390.Full.OmittedTiltFallback
import Erdos390.Full.PrimePowerCovariance

/-!
# Exact perturbation bounds for deleting a finite guard set

This module contains the finite-probability algebra used by the guarded-cell
corollary after the arithmetic guard census supplies a cardinality bound.
Deletion is defined on the original finite sample type (guarded points receive
mass zero) and is normalized exactly.  The expectation and covariance losses
are proved from the deleted mass; they are not stored in a certificate.
-/

open scoped BigOperators

namespace Erdos390.Full
namespace FiniteProbability

noncomputable section

variable {Omega : Type*} [Fintype Omega] [DecidableEq Omega]

/-- Probability mass carried by the declared guard set. -/
def guardMass (mu : FiniteProbability Omega) (G : Finset Omega) : ℝ :=
  ∑ x ∈ G, mu.mass x

omit [DecidableEq Omega] in
theorem guardMass_nonneg (mu : FiniteProbability Omega) (G : Finset Omega) :
    0 ≤ mu.guardMass G :=
  Finset.sum_nonneg fun x _ => mu.mass_nonneg x

omit [DecidableEq Omega] in
theorem guardMass_le_one (mu : FiniteProbability Omega) (G : Finset Omega) :
    mu.guardMass G ≤ 1 := by
  rw [← mu.mass_sum]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ G)
    (fun x hx hnot => mu.mass_nonneg x)

/- A guard census and a point-mass bound give the deleted-mass bound used in
the marked-cell application.  This is an inequality for the actual deleted
set, rather than a total-variation hypothesis stored in a certificate. -/
omit [DecidableEq Omega] in
theorem guardMass_le_card_mul_of_mass_le
    (mu : FiniteProbability Omega) (G : Finset Omega) {eta : ℝ}
    (hmass : ∀ x ∈ G, mu.mass x ≤ eta) :
    mu.guardMass G ≤ (G.card : ℝ) * eta := by
  unfold guardMass
  calc
    (∑ x ∈ G, mu.mass x) ≤ ∑ x ∈ G, eta :=
      Finset.sum_le_sum fun x hx => hmass x hx
    _ = (G.card : ℝ) * eta := by simp

/-- A bounded exponential tilt enlarges every individual atom by at most
the exact density-ratio factor `exp (2K)`. -/
theorem exponentialTilt_mass_le_exp_two_mul
    (mu : FiniteProbability Omega) (score : Omega → ℝ) (K : ℝ)
    (hscore : ∀ x, |score x| ≤ K) (x : Omega) :
    (mu.exponentialTilt score).mass x ≤ Real.exp (2 * K) * mu.mass x := by
  have h := mu.exponentialTilt_expect_le_exp_two_mul
    (fun y : Omega => if y = x then 1 else 0) score K
    (fun y => by by_cases hy : y = x <;> simp [hy]) hscore
  simpa [expect] using h

/-- The same density-ratio estimate summed over the actual guard set. -/
theorem exponentialTilt_guardMass_le_exp_two_mul
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (score : Omega → ℝ) (K : ℝ) (hscore : ∀ x, |score x| ≤ K) :
    (mu.exponentialTilt score).guardMass G ≤
      Real.exp (2 * K) * mu.guardMass G := by
  unfold guardMass
  calc
    (∑ x ∈ G, (mu.exponentialTilt score).mass x) ≤
        ∑ x ∈ G, Real.exp (2 * K) * mu.mass x :=
      Finset.sum_le_sum fun x hx =>
        mu.exponentialTilt_mass_le_exp_two_mul score K hscore x
    _ = Real.exp (2 * K) * ∑ x ∈ G, mu.mass x := by
      rw [Finset.mul_sum]

/-- Combined guard-census bound after a bounded tilt. -/
theorem exponentialTilt_guardMass_le_card_mul
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (score : Omega → ℝ) (K eta : ℝ)
    (hscore : ∀ x, |score x| ≤ K)
    (hmass : ∀ x ∈ G, mu.mass x ≤ eta) :
    (mu.exponentialTilt score).guardMass G ≤
      Real.exp (2 * K) * (G.card : ℝ) * eta := by
  calc
    (mu.exponentialTilt score).guardMass G ≤
        Real.exp (2 * K) * mu.guardMass G :=
      mu.exponentialTilt_guardMass_le_exp_two_mul G score K hscore
    _ ≤ Real.exp (2 * K) * ((G.card : ℝ) * eta) :=
      mul_le_mul_of_nonneg_left
        (mu.guardMass_le_card_mul_of_mass_le G hmass)
        (Real.exp_pos _).le
    _ = Real.exp (2 * K) * (G.card : ℝ) * eta := by ring

theorem sum_mass_complement_guard
    (mu : FiniteProbability Omega) (G : Finset Omega) :
    (∑ x ∈ (Finset.univ \ G), mu.mass x) = 1 - mu.guardMass G := by
  have h := Finset.sum_sdiff (Finset.subset_univ G) (f := mu.mass)
  rw [mu.mass_sum] at h
  unfold guardMass
  linarith

/-- The probability law obtained after deleting `G` and renormalizing. -/
def deleteGuards (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) : FiniteProbability Omega where
  mass x := if x ∈ G then 0 else mu.mass x / (1 - mu.guardMass G)
  mass_nonneg x := by
    split_ifs
    · exact le_rfl
    · exact div_nonneg (mu.mass_nonneg x) (sub_nonneg.mpr hsmall.le)
  mass_sum := by
    have hden : 1 - mu.guardMass G ≠ 0 := ne_of_gt (sub_pos.mpr hsmall)
    calc
      (∑ x, if x ∈ G then 0 else
          mu.mass x / (1 - mu.guardMass G)) =
          ∑ x ∈ (Finset.univ \ G),
            mu.mass x / (1 - mu.guardMass G) := by
        rw [Finset.sdiff_eq_filter, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxG : x ∈ G <;> simp [hxG]
      _ = (∑ x ∈ (Finset.univ \ G), mu.mass x) /
          (1 - mu.guardMass G) := by rw [Finset.sum_div]
      _ = 1 := by
        rw [mu.sum_mass_complement_guard G]
        exact div_self hden

@[simp] theorem deleteGuards_mass_of_mem
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) {x : Omega} (hx : x ∈ G) :
    (mu.deleteGuards G hsmall).mass x = 0 := by
  simp [deleteGuards, hx]

@[simp] theorem deleteGuards_mass_of_not_mem
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) {x : Omega} (hx : x ∉ G) :
    (mu.deleteGuards G hsmall).mass x =
      mu.mass x / (1 - mu.guardMass G) := by
  simp [deleteGuards, hx]

/-- Guard contribution to an unnormalized moment. -/
def guardMoment (mu : FiniteProbability Omega) (G : Finset Omega)
    (F : Omega → ℝ) : ℝ :=
  ∑ x ∈ G, mu.mass x * F x

/-- Exact expectation formula after guard deletion. -/
theorem deleteGuards_expect
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) (F : Omega → ℝ) :
    (mu.deleteGuards G hsmall).expect F =
      (mu.expect F - mu.guardMoment G F) / (1 - mu.guardMass G) := by
  unfold expect guardMoment
  have hsplit := Finset.sum_sdiff (Finset.subset_univ G)
    (f := fun x => mu.mass x * F x)
  change (∑ x, (if x ∈ G then 0 else
      mu.mass x / (1 - mu.guardMass G)) * F x) = _
  calc
    (∑ x, (if x ∈ G then 0 else
        mu.mass x / (1 - mu.guardMass G)) * F x) =
        ∑ x ∈ (Finset.univ \ G),
          (mu.mass x * F x) / (1 - mu.guardMass G) := by
      rw [Finset.sdiff_eq_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x hx
      by_cases hxG : x ∈ G
      · simp [hxG]
      · simp [hxG]
        ring
    _ = (∑ x ∈ (Finset.univ \ G), mu.mass x * F x) /
        (1 - mu.guardMass G) := by rw [Finset.sum_div]
    _ = ((∑ x, mu.mass x * F x) -
          ∑ x ∈ G, mu.mass x * F x) /
        (1 - mu.guardMass G) := by
      congr 1
      linarith

/-- A normalized scalar measuring the effect of deleting the guard mass. -/
def guardPerturbation (mu : FiniteProbability Omega) (G : Finset Omega) : ℝ :=
  2 * mu.guardMass G / (1 - mu.guardMass G)

omit [DecidableEq Omega] in
theorem guardPerturbation_nonneg
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1) :
    0 ≤ mu.guardPerturbation G := by
  unfold guardPerturbation
  exact div_nonneg (mul_nonneg (by norm_num) (mu.guardMass_nonneg G))
    (sub_pos.mpr hsmall).le

/- On the paper's small-deletion regime, the exact renormalization loss is
at most four times the deleted probability mass. -/
omit [DecidableEq Omega] in
theorem guardPerturbation_le_four_mul_guardMass
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hhalf : mu.guardMass G ≤ (1 : ℝ) / 2) :
    mu.guardPerturbation G ≤ 4 * mu.guardMass G := by
  let delta := mu.guardMass G
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := by
    dsimp only [delta] at hhalf ⊢
    linarith
  unfold guardPerturbation
  dsimp only [delta] at hdelta0 hden ⊢
  rw [div_le_iff₀ hden]
  nlinarith

omit [DecidableEq Omega] in
/- Absolute expectation under a finite probability is bounded by any
pointwise absolute envelope. -/
theorem abs_expect_le_of_abs_le
    (mu : FiniteProbability Omega) (F : Omega → ℝ) {K : ℝ}
    (_hK : 0 ≤ K) (hF : ∀ x, |F x| ≤ K) :
    |mu.expect F| ≤ K := by
  unfold expect
  calc
    |∑ x, mu.mass x * F x| ≤
        ∑ x, |mu.mass x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x, mu.mass x * |F x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ ≤ ∑ x, mu.mass x * K := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hF x) (mu.mass_nonneg x)
    _ = K := by rw [← Finset.sum_mul, mu.mass_sum, one_mul]

omit [DecidableEq Omega] in
theorem abs_guardMoment_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (F : Omega → ℝ) {K : ℝ} (_hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) :
    |mu.guardMoment G F| ≤ mu.guardMass G * K := by
  unfold guardMoment guardMass
  calc
    |∑ x ∈ G, mu.mass x * F x| ≤
        ∑ x ∈ G, |mu.mass x * F x| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ x ∈ G, mu.mass x * |F x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg x)]
    _ ≤ ∑ x ∈ G, mu.mass x * K := by
      exact Finset.sum_le_sum fun x hx =>
        mul_le_mul_of_nonneg_left (hF x) (mu.mass_nonneg x)
    _ = (∑ x ∈ G, mu.mass x) * K := by rw [Finset.sum_mul]

/-- Quantitative expectation perturbation after deleting guards. -/
theorem abs_deleteGuards_expect_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (F : Omega → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hF : ∀ x, |F x| ≤ K) :
    |(mu.deleteGuards G hsmall).expect F - mu.expect F| ≤
      K * mu.guardPerturbation G := by
  let delta := mu.guardMass G
  let E := mu.expect F
  let R := mu.guardMoment G F
  have hdelta0 : 0 ≤ delta := mu.guardMass_nonneg G
  have hden : 0 < 1 - delta := sub_pos.mpr hsmall
  have hE : |E| ≤ K := mu.abs_expect_le_of_abs_le F hK hF
  have hR : |R| ≤ delta * K := by
    simpa only [delta, R] using mu.abs_guardMoment_le G F hK hF
  rw [mu.deleteGuards_expect G hsmall F]
  have hre : (E - R) / (1 - delta) - E =
      (delta * E - R) / (1 - delta) := by
    field_simp [ne_of_gt hden]
    ring
  change |(E - R) / (1 - delta) - E| ≤ _
  rw [hre, abs_div, abs_of_pos hden]
  calc
    |delta * E - R| / (1 - delta) ≤
        (delta * |E| + |R|) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      calc
        |delta * E - R| ≤ |delta * E| + |R| := abs_sub _ _
        _ = delta * |E| + |R| := by
          rw [abs_mul, abs_of_nonneg hdelta0]
    _ ≤ (delta * K + delta * K) / (1 - delta) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left hE hdelta0) hR
    _ = K * mu.guardPerturbation G := by
      unfold guardPerturbation
      dsimp only [delta]
      ring

/-- Covariance perturbation for two pointwise bounded statistics. -/
theorem abs_deleteGuards_covariance_sub_le
    (mu : FiniteProbability Omega) (G : Finset Omega)
    (hsmall : mu.guardMass G < 1)
    (F H : Omega → ℝ) {KF KH : ℝ}
    (hKF : 0 ≤ KF) (hKH : 0 ≤ KH)
    (hF : ∀ x, |F x| ≤ KF) (hH : ∀ x, |H x| ≤ KH) :
    |(mu.deleteGuards G hsmall).covariance F H - mu.covariance F H| ≤
      3 * KF * KH * mu.guardPerturbation G := by
  let nu := mu.deleteGuards G hsmall
  let d := mu.guardPerturbation G
  have hd0 : 0 ≤ d := mu.guardPerturbation_nonneg G hsmall
  have hFH : ∀ x, |F x * H x| ≤ KF * KH := by
    intro x
    rw [abs_mul]
    exact mul_le_mul (hF x) (hH x) (abs_nonneg _) hKF
  have hKprod : 0 ≤ KF * KH := mul_nonneg hKF hKH
  have hprodDiff : |nu.expect (fun x => F x * H x) -
      mu.expect (fun x => F x * H x)| ≤ (KF * KH) * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall
        (fun x => F x * H x) hKprod hFH
  have hFDiff : |nu.expect F - mu.expect F| ≤ KF * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall F hKF hF
  have hHDiff : |nu.expect H - mu.expect H| ≤ KH * d := by
    simpa only [nu, d] using
      mu.abs_deleteGuards_expect_sub_le G hsmall H hKH hH
  have hmuF : |mu.expect F| ≤ KF := mu.abs_expect_le_of_abs_le F hKF hF
  have hnuH : |nu.expect H| ≤ KH := nu.abs_expect_le_of_abs_le H hKH hH
  have hmeanFirst :
      |(nu.expect F - mu.expect F) * nu.expect H| ≤
        (KF * d) * KH := by
    rw [abs_mul]
    exact mul_le_mul hFDiff hnuH (abs_nonneg _)
      (mul_nonneg hKF hd0)
  have hmeanSecond :
      |mu.expect F * (nu.expect H - mu.expect H)| ≤
        KF * (KH * d) := by
    rw [abs_mul]
    exact mul_le_mul hmuF hHDiff (abs_nonneg _) hKF
  unfold covariance
  have hmeanIdentity :
      nu.expect F * nu.expect H - mu.expect F * mu.expect H =
        (nu.expect F - mu.expect F) * nu.expect H +
          mu.expect F * (nu.expect H - mu.expect H) := by ring
  rw [show
    (nu.expect (fun x => F x * H x) - nu.expect F * nu.expect H) -
      (mu.expect (fun x => F x * H x) - mu.expect F * mu.expect H) =
      (nu.expect (fun x => F x * H x) -
        mu.expect (fun x => F x * H x)) -
      (nu.expect F * nu.expect H - mu.expect F * mu.expect H) by ring,
    hmeanIdentity]
  calc
    |(nu.expect (fun x => F x * H x) -
          mu.expect (fun x => F x * H x)) -
        ((nu.expect F - mu.expect F) * nu.expect H +
          mu.expect F * (nu.expect H - mu.expect H))| ≤
        |nu.expect (fun x => F x * H x) -
          mu.expect (fun x => F x * H x)| +
        |(nu.expect F - mu.expect F) * nu.expect H| +
        |mu.expect F * (nu.expect H - mu.expect H)| := by
      calc
        |(nu.expect (fun x => F x * H x) -
              mu.expect (fun x => F x * H x)) -
            ((nu.expect F - mu.expect F) * nu.expect H +
              mu.expect F * (nu.expect H - mu.expect H))| ≤
            |nu.expect (fun x => F x * H x) -
              mu.expect (fun x => F x * H x)| +
            |(nu.expect F - mu.expect F) * nu.expect H +
              mu.expect F * (nu.expect H - mu.expect H)| := abs_sub _ _
        _ ≤ |nu.expect (fun x => F x * H x) -
              mu.expect (fun x => F x * H x)| +
            (|(nu.expect F - mu.expect F) * nu.expect H| +
              |mu.expect F * (nu.expect H - mu.expect H)|) :=
          add_le_add_right (abs_add_le _ _) _
        _ = _ := by ring
    _ ≤ (KF * KH) * d + (KF * d) * KH + KF * (KH * d) := by
      exact add_le_add (add_le_add hprodDiff hmeanFirst) hmeanSecond
    _ = 3 * KF * KH * mu.guardPerturbation G := by
      dsimp only [d]
      ring

end

end FiniteProbability
end Erdos390.Full
