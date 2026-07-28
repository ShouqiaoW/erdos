import Erdos390.Full.FiniteExponentialFamily

/-!
# Total-variation control for finite exponential tilts

This supplies the normalization estimate used to compare each finite-`n`
tilted nuisance covariance with its own finite-`n` baseline.  The bound is
proved directly from the exponential density ratio.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

def expPartition (mu : FiniteProbability Omega) (S : Omega → ℝ) : ℝ :=
  mu.expect (fun omega ↦ Real.exp (S omega))

theorem expPartition_pos (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    0 < mu.expPartition S := by
  have hex : ∃ omega, 0 < mu.mass omega := by
    have hsum : 0 < ∑ omega, mu.mass omega := by
      rw [mu.mass_sum]
      exact zero_lt_one
    rw [Finset.sum_pos_iff_of_nonneg
      (fun omega (_ : omega ∈ (Finset.univ : Finset Omega)) ↦
        mu.mass_nonneg omega)] at hsum
    exact hsum.imp fun omega h ↦ h.2
  obtain ⟨omega, homega⟩ := hex
  rw [expPartition, expect, Finset.sum_pos_iff_of_nonneg]
  · exact ⟨omega, Finset.mem_univ omega,
      mul_pos homega (Real.exp_pos _)⟩
  · intro eta _
    exact mul_nonneg (mu.mass_nonneg eta) (Real.exp_pos _).le

def exponentialTilt (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    FiniteProbability Omega where
  mass := fun omega ↦ mu.mass omega * Real.exp (S omega) / mu.expPartition S
  mass_nonneg := by
    intro omega
    exact div_nonneg
      (mul_nonneg (mu.mass_nonneg omega) (Real.exp_pos _).le)
      (mu.expPartition_pos S).le
  mass_sum := by
    rw [← Finset.sum_div, expPartition, expect]
    exact div_self (ne_of_gt (mu.expPartition_pos S))

def exponentialDeviation (mu : FiniteProbability Omega) (S : Omega → ℝ) : ℝ :=
  mu.expect (fun omega ↦ |Real.exp (S omega) - 1|)

def l1Distance (mu nu : FiniteProbability Omega) : ℝ :=
  ∑ omega, |mu.mass omega - nu.mass omega|

theorem exponentialDeviation_nonneg (mu : FiniteProbability Omega)
    (S : Omega → ℝ) : 0 ≤ mu.exponentialDeviation S := by
  unfold exponentialDeviation expect
  exact Finset.sum_nonneg fun omega _ ↦
    mul_nonneg (mu.mass_nonneg omega) (abs_nonneg _)

theorem exponentialDeviation_le_two_expect_abs
    (mu : FiniteProbability Omega) (S : Omega → ℝ)
    (hsmall : ∀ omega, |S omega| ≤ 1) :
    mu.exponentialDeviation S ≤
      2 * mu.expect (fun omega ↦ |S omega|) := by
  unfold exponentialDeviation expect
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro omega _
  calc
    mu.mass omega * |Real.exp (S omega) - 1| ≤
        mu.mass omega * (2 * |S omega|) :=
      mul_le_mul_of_nonneg_left
        (Real.abs_exp_sub_one_le (hsmall omega)) (mu.mass_nonneg omega)
    _ = 2 * (mu.mass omega * |S omega|) := by ring

theorem abs_expPartition_sub_one_le_deviation
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    |mu.expPartition S - 1| ≤ mu.exponentialDeviation S := by
  have hrewrite : mu.expPartition S - 1 =
      ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
    calc
      mu.expPartition S - 1 =
          (∑ omega, mu.mass omega * Real.exp (S omega)) -
            ∑ omega, mu.mass omega := by
              rw [expPartition, expect, mu.mass_sum]
      _ = ∑ omega,
          (mu.mass omega * Real.exp (S omega) - mu.mass omega) := by
            rw [Finset.sum_sub_distrib]
      _ = ∑ omega, mu.mass omega * (Real.exp (S omega) - 1) := by
            apply Finset.sum_congr rfl
            intro omega _
            ring
  rw [hrewrite]
  calc
    |∑ omega, mu.mass omega * (Real.exp (S omega) - 1)| ≤
        ∑ omega, |mu.mass omega * (Real.exp (S omega) - 1)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = mu.exponentialDeviation S := by
      unfold exponentialDeviation expect
      apply Finset.sum_congr rfl
      intro omega _
      rw [abs_mul, abs_of_nonneg (mu.mass_nonneg omega)]

theorem expPartition_lower_bound
    (mu : FiniteProbability Omega) (S : Omega → ℝ) :
    1 - mu.exponentialDeviation S ≤ mu.expPartition S := by
  have h := mu.abs_expPartition_sub_one_le_deviation S
  have hneg : -mu.exponentialDeviation S ≤
      -|mu.expPartition S - 1| := neg_le_neg h
  have habs : -|mu.expPartition S - 1| ≤
      mu.expPartition S - 1 := neg_abs_le _
  linarith

/-- Exact normalized-density estimate. -/
theorem l1Distance_exponentialTilt_le
    (mu : FiniteProbability Omega) (S : Omega → ℝ)
    (heps : mu.exponentialDeviation S < 1) :
    mu.l1Distance (mu.exponentialTilt S) ≤
      2 * mu.exponentialDeviation S /
        (1 - mu.exponentialDeviation S) := by
  let Z := mu.expPartition S
  let eps := mu.exponentialDeviation S
  have hZpos : 0 < Z := mu.expPartition_pos S
  have hdenpos : 0 < 1 - eps := sub_pos.mpr heps
  have hZlower : 1 - eps ≤ Z := mu.expPartition_lower_bound S
  have hZdev : |Z - 1| ≤ eps := mu.abs_expPartition_sub_one_le_deviation S
  have heps0 : 0 ≤ eps := mu.exponentialDeviation_nonneg S
  have hpoint (omega : Omega) :
      |mu.mass omega - (mu.exponentialTilt S).mass omega| ≤
        mu.mass omega *
          (|Real.exp (S omega) - 1| + |Z - 1|) / Z := by
    simp only [exponentialTilt, Z]
    have hid : mu.mass omega -
        mu.mass omega * Real.exp (S omega) / Z =
        mu.mass omega * (Z - Real.exp (S omega)) / Z := by
      field_simp
    rw [hid, abs_div, abs_mul,
      abs_of_nonneg (mu.mass_nonneg omega), abs_of_pos hZpos]
    apply div_le_div_of_nonneg_right _ hZpos.le
    apply mul_le_mul_of_nonneg_left _ (mu.mass_nonneg omega)
    calc
      |Z - Real.exp (S omega)| = |Real.exp (S omega) - Z| := abs_sub_comm _ _
      _ ≤ |Real.exp (S omega) - 1| + |1 - Z| := abs_sub_le _ _ _
      _ = |Real.exp (S omega) - 1| + |Z - 1| := by
        rw [abs_sub_comm 1 Z]
  have hsum :
      (∑ omega, mu.mass omega *
        (|Real.exp (S omega) - 1| + |Z - 1|)) =
        eps + |Z - 1| := by
    rw [show (∑ omega, mu.mass omega *
        (|Real.exp (S omega) - 1| + |Z - 1|)) =
        (∑ omega, mu.mass omega * |Real.exp (S omega) - 1|) +
          ∑ omega, mu.mass omega * |Z - 1| by
      simp_rw [mul_add]
      exact Finset.sum_add_distrib]
    have hfirst : (∑ omega,
        mu.mass omega * |Real.exp (S omega) - 1|) = eps := by
      rfl
    rw [hfirst, ← Finset.sum_mul, mu.mass_sum, one_mul]
  unfold l1Distance
  calc
    (∑ omega, |mu.mass omega - (mu.exponentialTilt S).mass omega|) ≤
        ∑ omega, mu.mass omega *
          (|Real.exp (S omega) - 1| + |Z - 1|) / Z :=
      Finset.sum_le_sum fun omega _ ↦ hpoint omega
    _ = (eps + |Z - 1|) / Z := by
      rw [← Finset.sum_div]
      rw [hsum]
    _ ≤ (2 * eps) / Z := by
      exact div_le_div_of_nonneg_right (by linarith)
        hZpos.le
    _ ≤ (2 * eps) / (1 - eps) := by
      apply div_le_div_of_nonneg_left
      · exact mul_nonneg (by norm_num) heps0
      · exact hdenpos
      · exact hZlower

theorem l1Distance_exponentialTilt_le_of_small_score
    (mu : FiniteProbability Omega) (S : Omega → ℝ)
    (hsmall : ∀ omega, |S omega| ≤ 1)
    (hexpect : 2 * mu.expect (fun omega ↦ |S omega|) < 1) :
    mu.l1Distance (mu.exponentialTilt S) ≤
      (4 * mu.expect (fun omega ↦ |S omega|)) /
        (1 - 2 * mu.expect (fun omega ↦ |S omega|)) := by
  let a := mu.expect (fun omega ↦ |S omega|)
  let eps := mu.exponentialDeviation S
  have ha0 : 0 ≤ a := by
    unfold a expect
    exact Finset.sum_nonneg fun omega _ ↦
      mul_nonneg (mu.mass_nonneg omega) (abs_nonneg _)
  have heps0 : 0 ≤ eps := mu.exponentialDeviation_nonneg S
  have hepsa : eps ≤ 2 * a :=
    mu.exponentialDeviation_le_two_expect_abs S hsmall
  have heps1 : eps < 1 := hepsa.trans_lt hexpect
  refine (mu.l1Distance_exponentialTilt_le S heps1).trans ?_
  have hdeneps : 0 < 1 - eps := sub_pos.mpr heps1
  have hdena : 0 < 1 - 2 * a := sub_pos.mpr hexpect
  apply (div_le_div_iff₀ hdeneps hdena).mpr
  have hleft : 2 * eps ≤ 4 * a := by linarith
  nlinarith

end FiniteProbability

end

end Erdos390.Full
