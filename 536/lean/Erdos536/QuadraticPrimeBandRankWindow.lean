import Erdos536.PrimeBandRootProfileRank
import Erdos536.QuadraticPrimeBandFirstMoment
import Erdos536.UniformLocalPrimeBand

/-!
# Uniform reciprocal windows at delayed pivot ranks

The delayed pivot cutoff moves towards zero with the profile horizon, so
the fixed-compact-center local-band theorem is not applicable.  The
validity of every delayed check instead gives the uniform quantitative
lower bound

`log (T^6 - 1) < T^2 * quadraticDelayedPivotLower i`.

This is enough to run the Mertens error estimate directly, uniformly over
all forced pivot ranks.
-/

open scoped BigOperators
open Finset Filter Topology Set

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

/-- The local-band numerator used for a normalized window of width
`4 * quadraticAnchorWidth T η`. -/
def quadraticDelayedRankLocalNumerator (η : ℝ) : ℝ :=
  Real.log (Real.exp (4 * η + Real.log 4) + 1) + 1

/-- A fixed constant controlling every delayed-rank reciprocal window. -/
def quadraticDelayedRankWindowConstant (η : ℝ) : ℝ :=
  4 * quadraticDelayedRankLocalNumerator η / η

theorem quadraticDelayedRankLocalNumerator_nonneg (η : ℝ) :
    0 ≤ quadraticDelayedRankLocalNumerator η := by
  unfold quadraticDelayedRankLocalNumerator
  have hlog :
      0 ≤ Real.log (Real.exp (4 * η + Real.log 4) + 1) := by
    exact Real.log_nonneg (by
      linarith [Real.exp_pos (4 * η + Real.log 4)])
  linarith

theorem quadraticDelayedRankWindowConstant_nonneg
    {η : ℝ} (hη : 0 < η) :
    0 ≤ quadraticDelayedRankWindowConstant η := by
  unfold quadraticDelayedRankWindowConstant
  exact div_nonneg
    (mul_nonneg (by norm_num)
      (quadraticDelayedRankLocalNumerator_nonneg η))
    hη.le

/-- Validity of the delayed check at rank `i` forces a quantitative
lower bound on the moving normalized-weight cutoff. -/
theorem log_quadraticLowerCutoff_sub_one_lt_scaled_delayedPivotLower
    {T H i : ℕ}
    (hcutoff : 1 < quadraticLowerCutoff T)
    (hchecks :
      ∀ k ≤ H,
        k ∈ quadraticDelayedProfileChecks T H)
    (hi : i < quadraticDelayedPivotCount H) :
    Real.log ((quadraticLowerCutoff T : ℝ) - 1) <
      ((T ^ 2 : ℕ) : ℝ) * quadraticDelayedPivotLower i := by
  have hkH :
      quadraticDelayedPivotCheck i ≤ H :=
    quadraticDelayedPivotCheck_le_of_lt_count hi
  have hk :=
    (mem_quadraticDelayedProfileChecks.mp
      (hchecks (quadraticDelayedPivotCheck i) hkH)).2
  have hkR :
      (quadraticLowerCutoff T : ℝ) ≤
        (expEndpoint
          (quadraticDelayedPivotLower i) (T ^ 2) : ℝ) := by
    exact_mod_cast hk
  have hceil :
      (expEndpoint
          (quadraticDelayedPivotLower i) (T ^ 2) : ℝ) <
        Real.exp
            (((T ^ 2 : ℕ) : ℝ) *
              quadraticDelayedPivotLower i) + 1 := by
    unfold expEndpoint
    exact_mod_cast
      (Nat.ceil_lt_add_one
        (Real.exp_nonneg
          (((T ^ 2 : ℕ) : ℝ) *
            quadraticDelayedPivotLower i)))
  have hsub :
      (quadraticLowerCutoff T : ℝ) - 1 <
        Real.exp
          (((T ^ 2 : ℕ) : ℝ) *
            quadraticDelayedPivotLower i) := by
    linarith
  have hsubpos :
      0 < (quadraticLowerCutoff T : ℝ) - 1 := by
    have hcutoffR :
        (1 : ℝ) < (quadraticLowerCutoff T : ℝ) := by
      exact_mod_cast hcutoff
    linarith
  have hlog := Real.log_lt_log hsubpos hsub
  simpa only [Real.log_exp] using hlog

/-- The logarithm of the polynomial lower cutoff tends to infinity. -/
theorem tendsto_log_quadraticLowerCutoff_sub_one :
    Tendsto
      (fun T : ℕ =>
        Real.log ((quadraticLowerCutoff T : ℝ) - 1))
      atTop atTop := by
  have hpow :
      Tendsto (fun T : ℕ => (quadraticLowerCutoff T : ℝ))
        atTop atTop := by
    have hpowNat :
        Tendsto (fun T : ℕ => T ^ 6) atTop atTop :=
      tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0)
    simpa only [quadraticLowerCutoff] using
      tendsto_natCast_atTop_atTop.comp hpowNat
  exact Real.tendsto_log_atTop.comp
    (by
      simpa only [sub_eq_add_neg] using
        tendsto_atTop_add_const_right atTop (-1 : ℝ) hpow)

namespace LocalPrimeBand

/-- Quantitative local-band upper bound whose positive lower center may
depend on the scale.  This is the moving-center version of
`eventually_uniform_normalizedLocalBand_upper`. -/
theorem localBandShiftedReciprocalMass_upper_of_scaled_center
    {N X₀ : ℕ} {ell t h C : ℝ}
    (hN : 0 < N)
    (hell : 0 < ell)
    (hellt : ell / 2 ≤ t)
    (hh : 0 < h)
    (hC : 0 ≤ C)
    (hcut :
      X₀ ≤ localLowerEndpoint N (ell / 2))
    (herror :
      5 * C ≤ (((N : ℝ) * (ell / 2)) ^ 2))
    (hquad : ∀ A Y : ℕ, X₀ ≤ A → A ≤ Y →
      |fullReciprocalSum Y - fullReciprocalSum A -
          (Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)))| ≤
        5 * C / Real.log (A : ℝ) ^ 3) :
    localBandShiftedReciprocalMass N t h ≤
      (Real.log (Real.exp h + 1) + 1) /
        ((N : ℝ) * (ell / 2)) := by
  let A := localLowerEndpoint N t
  let Y := localUpperEndpoint N t h
  have hellHalf : 0 < ell / 2 := by positivity
  have ht : 0 < t := hellHalf.trans_le hellt
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hAposN : 0 < A := localLowerEndpoint_pos N t
  have hApos : (0 : ℝ) < A := by exact_mod_cast hAposN
  have hAY : A ≤ Y :=
    localLowerEndpoint_le_upper
      (T := N) (t := t) hh.le
  have hYpos : (0 : ℝ) < Y := by
    exact_mod_cast hAposN.trans_le hAY
  have hcutA :
      X₀ ≤ A := by
    exact hcut.trans
      (expEndpoint_mono hellt N)
  have hloglower :
      (N : ℝ) * (ell / 2) ≤ Real.log (A : ℝ) := by
    calc
      (N : ℝ) * (ell / 2) ≤ (N : ℝ) * t :=
        mul_le_mul_of_nonneg_left hellt hNR.le
      _ ≤ Real.log (A : ℝ) :=
        localLowerEndpoint_log_lower N t
  have hscaledPos :
      0 < (N : ℝ) * (ell / 2) :=
    mul_pos hNR hellHalf
  have hlogApos : 0 < Real.log (A : ℝ) :=
    hscaledPos.trans_le hloglower
  have hYupper :
      (Y : ℝ) <
        (Real.exp h + 1) * (A : ℝ) := by
    have hceil :
        (Y : ℝ) <
          Real.exp h * (A : ℝ) + 1 := by
      exact_mod_cast
        (Nat.ceil_lt_add_one
          (mul_nonneg (Real.exp_nonneg _) (Nat.cast_nonneg A)))
    have hAone : (1 : ℝ) ≤ A := by
      exact_mod_cast hAposN
    calc
      (Y : ℝ) < Real.exp h * (A : ℝ) + 1 := hceil
      _ ≤ (Real.exp h + 1) * (A : ℝ) := by
        nlinarith
  have hlogYupper :
      Real.log (Y : ℝ) - Real.log (A : ℝ) ≤
        Real.log (Real.exp h + 1) := by
    have hfactor : 0 < Real.exp h + 1 := by positivity
    have hlog :=
      Real.log_lt_log hYpos hYupper
    rw [Real.log_mul hfactor.ne' hApos.ne'] at hlog
    linarith
  have hdepthMain :
      Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) ≤
        Real.log (Real.exp h + 1) /
          ((N : ℝ) * (ell / 2)) := by
    have hlogYpos :
        0 < Real.log (Y : ℝ) := by
      exact hlogApos.trans_le
        (Real.log_le_log hApos (by exact_mod_cast hAY))
    have hbasic :=
      Real.log_le_sub_one_of_pos
        (div_pos hlogYpos hlogApos)
    have hratio :
        Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) ≤
          (Real.log (Y : ℝ) - Real.log (A : ℝ)) /
            Real.log (A : ℝ) := by
      rw [← Real.log_div hlogYpos.ne' hlogApos.ne']
      calc
        Real.log
            (Real.log (Y : ℝ) / Real.log (A : ℝ)) ≤
            Real.log (Y : ℝ) / Real.log (A : ℝ) - 1 :=
          hbasic
        _ = (Real.log (Y : ℝ) - Real.log (A : ℝ)) /
            Real.log (A : ℝ) := by
          field_simp [hlogApos.ne']
    have hfactorlog :
        0 ≤ Real.log (Real.exp h + 1) := by
      exact Real.log_nonneg (by
        linarith [Real.exp_pos h])
    calc
      Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) ≤
          (Real.log (Y : ℝ) - Real.log (A : ℝ)) /
            Real.log (A : ℝ) := hratio
      _ ≤ Real.log (Real.exp h + 1) /
            Real.log (A : ℝ) := by
        exact div_le_div_of_nonneg_right hlogYupper hlogApos.le
      _ ≤ Real.log (Real.exp h + 1) /
            ((N : ℝ) * (ell / 2)) := by
        exact div_le_div_of_nonneg_left hfactorlog
          hscaledPos hloglower
  have hquadrature := hquad A Y hcutA hAY
  have herror' :
      5 * C / Real.log (A : ℝ) ^ 3 ≤
        1 / ((N : ℝ) * (ell / 2)) := by
    have hlogcube :
        ((N : ℝ) * (ell / 2)) ^ 3 ≤
          Real.log (A : ℝ) ^ 3 :=
      pow_le_pow_left₀ hscaledPos.le hloglower 3
    calc
      5 * C / Real.log (A : ℝ) ^ 3 ≤
          5 * C / (((N : ℝ) * (ell / 2)) ^ 3) := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (by norm_num) hC)
          (pow_pos hscaledPos 3) hlogcube
      _ ≤ 1 / ((N : ℝ) * (ell / 2)) := by
        apply (div_le_iff₀ (pow_pos hscaledPos 3)).2
        calc
          5 * C ≤ ((N : ℝ) * (ell / 2)) ^ 2 := herror
          _ = 1 / ((N : ℝ) * (ell / 2)) *
              ((N : ℝ) * (ell / 2)) ^ 3 := by
            field_simp [hscaledPos.ne']
  have hunshifted :
      localBandReciprocalMass N t h ≤
        Real.log (Real.log (Y : ℝ)) -
            Real.log (Real.log (A : ℝ)) +
          5 * C / Real.log (A : ℝ) ^ 3 := by
    dsimp [localBandReciprocalMass, A, Y]
    rw [abs_le] at hquadrature
    linarith
  have hshifted :
      localBandShiftedReciprocalMass N t h ≤
        localBandReciprocalMass N t h := by
    rw [localBandShiftedReciprocalMass_eq_sum hh.le,
      localBandReciprocalMass_eq_sum hh.le]
    apply Finset.sum_le_sum
    intro p hp
    have hpR : (0 : ℝ) < p := by
      exact_mod_cast (mem_localPrimeBand.mp hp).1.pos
    exact one_div_le_one_div_of_le hpR (by linarith)
  calc
    localBandShiftedReciprocalMass N t h ≤
        localBandReciprocalMass N t h := hshifted
    _ ≤ Real.log (Real.log (Y : ℝ)) -
          Real.log (Real.log (A : ℝ)) +
        5 * C / Real.log (A : ℝ) ^ 3 := hunshifted
    _ ≤ Real.log (Real.exp h + 1) /
          ((N : ℝ) * (ell / 2)) +
        1 / ((N : ℝ) * (ell / 2)) :=
      add_le_add hdepthMain herror'
    _ = (Real.log (Real.exp h + 1) + 1) /
          ((N : ℝ) * (ell / 2)) := by ring

end LocalPrimeBand

/-- A moving normalized-weight cutoff converts the quantitative local
prime-band bound into the reciprocal window used by the rank-two
collision estimate. -/
theorem reciprocalWindowMassAlong_normalized_le_of_moving_lower
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {N : ℕ} (hN : 0 < N)
    {η ell D : ℝ} (hη : 0 < η) (hell : 0 < ell)
    (hsize :
      (4 * η + Real.log 4) / (N : ℝ) ≤ ell / 2)
    (hlocal : ∀ t : ℝ, ell / 2 ≤ t →
      LocalPrimeBand.localBandShiftedReciprocalMass
          N t (4 * η + Real.log 4) ≤
        D / ((N : ℝ) * (ell / 2))) :
    ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ
          (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight (N : ℝ) p.1)
          (fun p : ↥R =>
            ell ≤ normalizedLogWeight (N : ℝ) p.1)
          x (4 * (η / (N : ℝ))) ≤
        4 * D / ((N : ℝ) * ell) := by
  classical
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hpadNonneg :
      0 ≤ 4 * η + Real.log 4 := by
    exact add_nonneg (mul_nonneg (by norm_num) hη.le)
      (Real.log_nonneg (by norm_num))
  have hDdiv :
      0 ≤ D / ((N : ℝ) * (ell / 2)) := by
    exact
      (LocalPrimeBand.localBandShiftedReciprocalMass_nonneg
        hpadNonneg).trans
      (hlocal (ell / 2) le_rfl)
  intro x
  let t := x - Real.log 4 / (N : ℝ)
  by_cases ht : ell / 2 ≤ t
  · have hbridge :=
      reciprocalWindowMassAlong_le_localBandShifted
        hR hN
        (fun p : ↥R =>
          ell ≤ normalizedLogWeight (N : ℝ) p.1)
        x (4 * η) (mul_nonneg (by norm_num) hη.le)
    have hwidth :
        (4 * η) / (N : ℝ) =
          4 * (η / (N : ℝ)) := by
      ring
    rw [hwidth] at hbridge
    calc
      reciprocalWindowMassAlong
          Finset.univ
          (fun p : ↥R => p.1)
          (fun p : ↥R =>
            normalizedLogWeight (N : ℝ) p.1)
          (fun p : ↥R =>
            ell ≤ normalizedLogWeight (N : ℝ) p.1)
          x (4 * (η / (N : ℝ))) ≤
        2 * LocalPrimeBand.localBandShiftedReciprocalMass
          N t (4 * η + Real.log 4) := by
        simpa only [t] using hbridge
      _ ≤ 2 * (D / ((N : ℝ) * (ell / 2))) :=
        mul_le_mul_of_nonneg_left (hlocal t ht) (by norm_num)
      _ = 4 * D / ((N : ℝ) * ell) := by
        ring
  · have hzero :
        reciprocalWindowMassAlong
            Finset.univ
            (fun p : ↥R => p.1)
            (fun p : ↥R =>
              normalizedLogWeight (N : ℝ) p.1)
            (fun p : ↥R =>
              ell ≤ normalizedLogWeight (N : ℝ) p.1)
            x (4 * (η / (N : ℝ))) = 0 := by
      unfold reciprocalWindowMassAlong
      apply Finset.sum_eq_zero
      intro p _hp
      by_cases hpData :
          ell ≤ normalizedLogWeight (N : ℝ) p.1 ∧
            x ≤ normalizedLogWeight (N : ℝ) p.1 ∧
            normalizedLogWeight (N : ℝ) p.1 ≤
              x + 4 * (η / (N : ℝ))
      · have hxLower :
            ell - 4 * (η / (N : ℝ)) ≤ x := by
          linarith [hpData.1, hpData.2.2]
        have hcenterLower :
            ell - (4 * η + Real.log 4) / (N : ℝ) ≤
              t := by
          dsimp [t]
          calc
            ell - (4 * η + Real.log 4) / (N : ℝ) =
                (ell - 4 * (η / (N : ℝ))) -
                  Real.log 4 / (N : ℝ) := by
              ring
            _ ≤ x - Real.log 4 / (N : ℝ) :=
              sub_le_sub_right hxLower _
        have hcut :
            ell / 2 ≤
              ell - (4 * η + Real.log 4) / (N : ℝ) := by
          linarith
        exact False.elim (ht (hcut.trans hcenterLower))
      · simp [hpData]
    rw [hzero]
    have hD : 0 ≤ D := by
      have hden :
          0 < (N : ℝ) * (ell / 2) := by positivity
      rcases div_nonneg_iff.mp hDdiv with hpos | hneg
      · exact hpos.1
      · exact False.elim ((not_le_of_gt hden) hneg.2)
    exact div_nonneg
      (mul_nonneg (by norm_num) hD)
      (mul_nonneg hNR.le hell.le)

/-- Uniform rank-local reciprocal-window estimate on the quadratic
profile band.  The constant depends only on `η`, while the precise
moving-rank dependence is `quadraticAnchorWidth T η /
quadraticDelayedPivotLower i`. -/
theorem eventually_quadraticDelayedRank_reciprocalWindow_le
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      ∀ i : ℕ,
        i <
            quadraticDelayedPivotCount
              (quadraticDelayedProfileHorizon T) →
        ∀ x : ℝ,
          reciprocalWindowMassAlong
              Finset.univ
              (fun p : ↥(quadraticProfilePrimeBand T) => p.1)
              (fun p : ↥(quadraticProfilePrimeBand T) =>
                normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
              (fun p : ↥(quadraticProfilePrimeBand T) =>
                quadraticDelayedPivotLower i ≤
                  normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
              x (4 * quadraticAnchorWidth T η) ≤
            quadraticDelayedRankWindowConstant η *
                quadraticAnchorWidth T η /
              quadraticDelayedPivotLower i := by
  obtain ⟨C, hC, X₀, hquad₀⟩ :=
    exists_fullReciprocalSum_interval_error_bound
  let X : ℕ := max X₀ 1
  let g : ℕ → ℝ := fun T =>
    Real.log ((quadraticLowerCutoff T : ℝ) - 1)
  let pad : ℝ := 4 * η + Real.log 4
  have hXpos : 0 < X := by
    dsimp [X]
    omega
  have hpad : 0 < pad := by
    dsimp [pad]
    exact add_pos (mul_pos (by norm_num) hη)
      (Real.log_pos (by norm_num))
  have hg :
      Tendsto g atTop atTop := by
    simpa only [g] using
      tendsto_log_quadraticLowerCutoff_sub_one
  have hgSquare :
      Tendsto (fun T : ℕ => (g T) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hg
  have hcutLogEventually :
      ∀ᶠ T : ℕ in atTop,
        2 * Real.log (X : ℝ) ≤ g T :=
    hg.eventually
      (eventually_ge_atTop (2 * Real.log (X : ℝ)))
  have hpadEventually :
      ∀ᶠ T : ℕ in atTop,
        2 * pad ≤ g T :=
    hg.eventually (eventually_ge_atTop (2 * pad))
  have hgNonnegEventually :
      ∀ᶠ T : ℕ in atTop, 0 ≤ g T :=
    hg.eventually (eventually_ge_atTop 0)
  have herrorEventually :
      ∀ᶠ T : ℕ in atTop, 20 * C ≤ (g T) ^ 2 :=
    hgSquare.eventually (eventually_ge_atTop (20 * C))
  have hcutoffTendsto :
      Tendsto quadraticLowerCutoff atTop atTop := by
    simpa only [quadraticLowerCutoff] using
      (tendsto_pow_atTop (by norm_num : (6 : ℕ) ≠ 0))
  have hcutoffEventually :
      ∀ᶠ T : ℕ in atTop, 1 < quadraticLowerCutoff T :=
    hcutoffTendsto.eventually (eventually_gt_atTop 1)
  filter_upwards [
      eventually_quadraticDelayedProfileHorizon_checks,
      hcutLogEventually,
      hpadEventually,
      hgNonnegEventually,
      herrorEventually,
      hcutoffEventually,
      eventually_gt_atTop 0] with
      T hchecksT hcutLogT hpadT hgT herrorT hcutoffT hT
  intro i hi x
  let N : ℕ := T ^ 2
  let ell : ℝ := quadraticDelayedPivotLower i
  have hN : 0 < N := by
    dsimp [N]
    exact pow_pos hT 2
  have hNR : (0 : ℝ) < N := by
    exact_mod_cast hN
  have hell : 0 < ell := by
    dsimp [ell]
    exact quadraticDelayedPivotLower_pos i
  have hscaled :
      g T < (N : ℝ) * ell := by
    dsimp only [g, N, ell]
    exact
      log_quadraticLowerCutoff_sub_one_lt_scaled_delayedPivotLower
        hcutoffT hchecksT hi
  have hlocalCut :
      X ≤ LocalPrimeBand.localLowerEndpoint N (ell / 2) := by
    have hXR : (0 : ℝ) < X := by
      exact_mod_cast hXpos
    have hlogX :
        Real.log (X : ℝ) ≤
          ((N : ℝ) * ell) / 2 := by
      nlinarith
    have hXexp :
        (X : ℝ) ≤
          Real.exp (((N : ℝ) * ell) / 2) := by
      calc
        (X : ℝ) =
            Real.exp (Real.log (X : ℝ)) := by
          symm
          exact Real.exp_log hXR
        _ ≤ Real.exp (((N : ℝ) * ell) / 2) :=
          Real.exp_le_exp.mpr hlogX
    have hhalf :
        ((N : ℝ) * ell) / 2 =
          (N : ℝ) * (ell / 2) := by ring
    have hceil :
        Real.exp ((N : ℝ) * (ell / 2)) ≤
          (LocalPrimeBand.localLowerEndpoint
            N (ell / 2) : ℝ) := by
      unfold LocalPrimeBand.localLowerEndpoint expEndpoint
      exact_mod_cast
        (Nat.le_ceil
          (Real.exp ((N : ℝ) * (ell / 2))))
    have hcast :
        (X : ℝ) ≤
          (LocalPrimeBand.localLowerEndpoint
            N (ell / 2) : ℝ) := by
      rw [← hhalf] at hceil
      exact hXexp.trans hceil
    exact_mod_cast hcast
  have hquadrature :
      ∀ A Y : ℕ, X ≤ A → A ≤ Y →
        |fullReciprocalSum Y - fullReciprocalSum A -
            (Real.log (Real.log (Y : ℝ)) -
              Real.log (Real.log (A : ℝ)))| ≤
          5 * C / Real.log (A : ℝ) ^ 3 := by
    intro A Y hXA hAY
    apply hquad₀ A Y
    · exact (le_max_left X₀ 1).trans hXA
    · exact hAY
  have hscaledHalfError :
      5 * C ≤
        (((N : ℝ) * (ell / 2)) ^ 2) := by
    have hzNonneg :
        0 ≤ (N : ℝ) * ell := by positivity
    have hgsquare :
        (g T) ^ 2 ≤ ((N : ℝ) * ell) ^ 2 := by
      nlinarith
    nlinarith
  have hsize :
      pad / (N : ℝ) ≤ ell / 2 := by
    apply (div_le_iff₀ hNR).2
    nlinarith
  have hlocal :
      ∀ t : ℝ, ell / 2 ≤ t →
        LocalPrimeBand.localBandShiftedReciprocalMass
            N t pad ≤
          quadraticDelayedRankLocalNumerator η /
            ((N : ℝ) * (ell / 2)) := by
    intro t ht
    simpa only [pad, quadraticDelayedRankLocalNumerator] using
      (LocalPrimeBand.localBandShiftedReciprocalMass_upper_of_scaled_center
          hN hell ht hpad hC.le hlocalCut hscaledHalfError
          hquadrature)
  have hwindow :=
    reciprocalWindowMassAlong_normalized_le_of_moving_lower
      (R := quadraticProfilePrimeBand T)
      (by
        simpa only [quadraticProfilePrimeBand] using
          quadraticPrimeBand_prime T 1)
      hN hη hell
      (by simpa only [pad] using hsize)
      (by simpa only [pad] using hlocal)
      x
  calc
    reciprocalWindowMassAlong
          Finset.univ
          (fun p : ↥(quadraticProfilePrimeBand T) => p.1)
          (fun p : ↥(quadraticProfilePrimeBand T) =>
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
          (fun p : ↥(quadraticProfilePrimeBand T) =>
            quadraticDelayedPivotLower i ≤
              normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
          x (4 * quadraticAnchorWidth T η) ≤
        4 * quadraticDelayedRankLocalNumerator η /
          (((T ^ 2 : ℕ) : ℝ) *
            quadraticDelayedPivotLower i) := by
      simpa only [N, ell, quadraticAnchorWidth] using hwindow
    _ =
        quadraticDelayedRankWindowConstant η *
            quadraticAnchorWidth T η /
          quadraticDelayedPivotLower i := by
      unfold quadraticDelayedRankWindowConstant
        quadraticAnchorWidth
      field_simp [hη.ne',
        (show (((T ^ 2 : ℕ) : ℝ)) ≠ 0 by positivity),
        (quadraticDelayedPivotLower_pos i).ne']

end Erdos536
