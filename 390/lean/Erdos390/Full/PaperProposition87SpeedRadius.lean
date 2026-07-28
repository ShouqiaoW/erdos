import Erdos390.Full.PaperProposition87CanonicalTwoStageAssembly

/-!
# Noncircular speed, radius, and eventual slack choices for Proposition 8.7

These are purely quantitative closure lemmas.  All structural bounds are
fixed first; the effective ODE speed is their maximum, and the box radius is
four times that speed.  The ambient threshold is then increased.  No bound
is inferred from an already constructed path.
-/

open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open scoped BigOperators

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The mixed-norm compensated target is `w` times a structural constant.
This is the cancellation that prevents the moving low-cell scale from
entering the later ODE box. -/
theorem twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
    {Creg Tband Tslow K : ℝ}
    (hCreg : 0 ≤ Creg) (hTband : 0 ≤ Tband)
    (hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ K) :
    B.twoStageCompensatedTargetBoundOrdinaryFast
        Creg Tband Tslow ≤
      B.w * (K * Creg * Tband + Tslow) := by
  unfold twoStageCompensatedTargetBoundOrdinaryFast
  have hw : 0 ≤ B.w := B.w_pos.le
  have hprod : 0 ≤ Creg * B.w * Tband := by positivity
  calc
    (∑ j : Band, B.harmonicMass j * B.bandCenter j) *
          (Creg * B.w) * Tband + B.w * Tslow ≤
        K * (Creg * B.w) * Tband + B.w * Tslow := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hmoment
            (mul_nonneg hCreg hw)) hTband) le_rfl
    _ = B.w * (K * Creg * Tband + Tslow) := by ring

/-- After writing the compensated prime and nuisance rows as `Cc*w` and
`Cz*w`, all three inverse-speed contributions are bounded independently of
`w`.  This is the exact algebra behind the parameter order
`W -> box -> n`. -/
theorem twoStage_uniform_speed_bounds_of_scaled_rows
    {Creg Tband Tslow K gamma Cc Cz Cord Cfast : ℝ}
    (hCreg : 0 ≤ Creg) (hTband : 0 ≤ Tband)
    (hgamma : 0 < gamma) (hCc : 0 ≤ Cc) (hCz : 0 ≤ Cz)
    (hmoment : (∑ j : Band,
      B.harmonicMass j * B.bandCenter j) ≤ K) :
    let A := K * Creg * Tband + Tslow
    Cord * Tband +
        (B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2)) * (Cc * B.w) ≤
          Cord * Tband + (A / gamma) * Cc ∧
      Cfast +
        (B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2)) * (Cz * B.w) ≤
          Cfast + (A / gamma) * Cz ∧
      B.w *
        (B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2)) ≤ A / gamma := by
  dsimp only
  let A : ℝ := K * Creg * Tband + Tslow
  have hstage := B.twoStageCompensatedTargetBoundOrdinaryFast_le_w_mul
    (Tslow := Tslow) hCreg hTband hmoment
  have hden : 0 < gamma * B.w ^ 2 :=
    mul_pos hgamma (sq_pos_of_pos B.w_pos)
  have hquot :
      B.twoStageCompensatedTargetBoundOrdinaryFast
          Creg Tband Tslow / (gamma * B.w ^ 2) ≤
        (B.w * A) / (gamma * B.w ^ 2) :=
    div_le_div_of_nonneg_right hstage hden.le
  have hCcW : 0 ≤ Cc * B.w := mul_nonneg hCc B.w_pos.le
  have hCzW : 0 ≤ Cz * B.w := mul_nonneg hCz B.w_pos.le
  have hPrime := mul_le_mul_of_nonneg_right hquot hCcW
  have hNuisance := mul_le_mul_of_nonneg_right hquot hCzW
  have hSlow := mul_le_mul_of_nonneg_left hquot B.w_pos.le
  have hPrimeCancel :
      ((B.w * A) / (gamma * B.w ^ 2)) * (Cc * B.w) =
        (A / gamma) * Cc := by
    field_simp [B.w_pos.ne', hgamma.ne']
  have hNuisanceCancel :
      ((B.w * A) / (gamma * B.w ^ 2)) * (Cz * B.w) =
        (A / gamma) * Cz := by
    field_simp [B.w_pos.ne', hgamma.ne']
  have hSlowCancel :
      B.w * ((B.w * A) / (gamma * B.w ^ 2)) = A / gamma := by
    field_simp [B.w_pos.ne', hgamma.ne']
  refine ⟨?_, ?_, ?_⟩
  · simpa only [A] using
      add_le_add (le_refl (Cord * Tband))
        (hPrime.trans_eq hPrimeCancel)
  · simpa only [A] using
      add_le_add (le_refl Cfast)
        (hNuisance.trans_eq hNuisanceCancel)
  · exact hSlow.trans_eq hSlowCancel

/-- A unit nuisance reserve suffices after the radius is fixed.  Reserve
one half for the fast nuisance coefficient and require the slow nuisance
coefficient to be at most
`gamma * w / (2 * (1 + A))`.  Since the compensated target is at most
`w*A`, the slow contribution is at most `A/(2(1+A)) ≤ 1/2`.

The small covariance-row estimates which realize these two reserves are
chosen only after the radius-dependent nuisance gap is fixed. -/
theorem twoStage_nuisance_speed_le_one_of_half_reserves
    {Tstage A gamma : ℝ}
    (hA : 0 ≤ A) (hgamma : 0 < gamma)
    (hstage : Tstage ≤ B.w * A) :
    (1 / 2 : ℝ) +
        (Tstage / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) ≤ 1 := by
  have hden : 0 < gamma * B.w ^ 2 :=
    mul_pos hgamma (sq_pos_of_pos B.w_pos)
  have hreserveDen : 0 < 2 * (1 + A) := by positivity
  have hslowReserve : 0 ≤ gamma * B.w / (2 * (1 + A)) := by
    exact div_nonneg (mul_nonneg hgamma.le B.w_pos.le) hreserveDen.le
  have hquot :
      Tstage / (gamma * B.w ^ 2) ≤
        (B.w * A) / (gamma * B.w ^ 2) :=
    div_le_div_of_nonneg_right hstage hden.le
  have hmul := mul_le_mul_of_nonneg_right hquot hslowReserve
  have hcancel :
      ((B.w * A) / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) =
        A / (2 * (1 + A)) := by
    field_simp [B.w_pos.ne', hgamma.ne', hreserveDen.ne']
  have hhalf : A / (2 * (1 + A)) ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hreserveDen).2
    nlinarith
  calc
    (1 / 2 : ℝ) +
        (Tstage / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) ≤
      1 / 2 +
        ((B.w * A) / (gamma * B.w ^ 2)) *
          (gamma * B.w / (2 * (1 + A))) := add_le_add le_rfl hmul
    _ = 1 / 2 + A / (2 * (1 + A)) := by rw [hcancel]
    _ ≤ 1 := by linarith

end BridgeData

/-- Three nonnegative component bounds admit a single speed and a radius
chosen with the paper's factor-four reserve. -/
theorem exists_speed_and_fourfold_radius
    (prime nuisance slow : ℝ)
    (hprime : 0 ≤ prime) :
    ∃ speed a : NNReal,
      prime ≤ (speed : ℝ) ∧
      nuisance ≤ (speed : ℝ) ∧
      slow ≤ (speed : ℝ) ∧
      speed ≤ a ∧
      (a : ℝ) = 4 * (speed : ℝ) := by
  let M : ℝ := max prime (max nuisance slow)
  have hM : 0 ≤ M := hprime.trans (le_max_left prime (max nuisance slow))
  let speed : NNReal := ⟨M, hM⟩
  let a : NNReal := 4 * speed
  refine ⟨speed, a, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · exact (le_max_left nuisance slow).trans (le_max_right prime _)
  · exact (le_max_right nuisance slow).trans (le_max_right prime _)
  · dsimp only [a]
    exact le_mul_of_one_le_left (zero_le speed) (by norm_num)
  · rfl

/-- Noncircular version used in the paper.  Only the box-independent prime
and stored-slow bounds enter the choice.  A unit reserve is built in for the
nuisance component; after this radius is fixed, the marked nuisance rate is
made smaller than that reserve by increasing `n`. -/
theorem exists_speed_radius_before_vanishing_nuisance
    (prime slow : ℝ) :
    ∃ speed a : NNReal,
      1 ≤ (speed : ℝ) ∧
      prime ≤ (speed : ℝ) ∧
      slow ≤ (speed : ℝ) ∧
      speed ≤ a ∧
      (a : ℝ) = 4 * (speed : ℝ) := by
  let M : ℝ := max 1 (max prime slow)
  have hM : 0 ≤ M := (by norm_num : (0 : ℝ) ≤ 1).trans
    (le_max_left 1 (max prime slow))
  let speed : NNReal := ⟨M, hM⟩
  let a : NNReal := 4 * speed
  refine ⟨speed, a, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_max_left _ _
  · exact (le_max_left prime slow).trans (le_max_right 1 _)
  · exact (le_max_right prime slow).trans (le_max_right 1 _)
  · dsimp only [a]
    exact le_mul_of_one_le_left (zero_le speed) (by norm_num)
  · rfl

/-- Every constant depending on the already fixed effective box may multiply
a vanishing row rate without feeding back into the box choice. -/
theorem eventually_const_mul_vanishing_rate_le
    (rate : ℕ → ℝ) (K reserve : ℝ)
    (hrate : Tendsto rate atTop (nhds 0))
    (hreserve : 0 < reserve) :
    ∀ᶠ n : ℕ in atTop, K * rate n ≤ reserve := by
  have hscaled : Tendsto (fun n : ℕ ↦ K * rate n)
      atTop (nhds 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hrate
  exact hscaled.eventually (eventually_le_nhds hreserve)

/-- Once all constants and the radius are fixed, the logarithmic ambient
slack inequality used by the feasibility ledger holds eventually. -/
theorem eventually_fixed_exponential_slack_le_L
    (Cfixed K Cactive : ℝ) :
    ∀ᶠ n : ℕ in atTop,
      Cfixed + Real.exp K * Cactive ≤ Scale.L n := by
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  exact hLTop.eventually
    (eventually_ge_atTop (Cfixed + Real.exp K * Cactive))

end

end Erdos390.Full.PaperBridgeFit
