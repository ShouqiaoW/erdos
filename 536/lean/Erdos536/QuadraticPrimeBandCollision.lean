import Erdos536.PrimeBandCollision
import Erdos536.QuadraticPrimeBand

/-!
# Collision windows on quadratically parametrized prime bands

This file specializes the exact exposed-root missing-petal analysis to
`quadraticPrimeBand T a`, normalized scale `T^2`, and target width
`η / T^2`.  The only analytic input is the uniform local-prime-band
upper estimate proved in `UniformLocalPrimeBand`.
-/

open scoped BigOperators
open Filter Topology

noncomputable section

namespace Erdos536

/-- The local-band constant after the fixed endpoint padding. -/
def quadraticMissingLocalConstant (η d : ℝ) : ℝ :=
  (Real.log (Real.exp (2 * η + Real.log 4) + 1) + 1) /
    (Real.exp (-d) / 2)

/-- The one-copy normalized reciprocal-window constant. -/
def quadraticMissingWindowConstant (η d : ℝ) : ℝ :=
  2 * quadraticMissingLocalConstant η d / η

theorem quadraticMissingLocalConstant_nonneg
    {η d : ℝ} :
    0 ≤ quadraticMissingLocalConstant η d := by
  unfold quadraticMissingLocalConstant
  apply div_nonneg
  · have hlog :
        0 ≤ Real.log
          (Real.exp (2 * η + Real.log 4) + 1) := by
      exact Real.log_nonneg (by
        linarith [Real.exp_pos (2 * η + Real.log 4)])
    linarith
  · positivity

theorem quadraticMissingWindowConstant_nonneg
    {η d : ℝ} (hη : 0 < η) :
    0 ≤ quadraticMissingWindowConstant η d := by
  unfold quadraticMissingWindowConstant
  exact div_nonneg
    (mul_nonneg (by norm_num)
      quadraticMissingLocalConstant_nonneg)
    hη.le

/-- The uniform local-band theorem, together with the exact endpoint
bridge, gives the translated reciprocal-window estimate needed in every
exposed-root fiber. -/
theorem eventually_quadraticPrimeBand_reciprocalWindow_le
    (a : ℝ) {η d : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop, ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ
          (fun p : ↥(quadraticPrimeBand T a) => p.1)
          (fun p : ↥(quadraticPrimeBand T a) =>
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
          (fun p : ↥(quadraticPrimeBand T a) =>
            normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p.1 ≤ d)
          x (2 * (η / ((T ^ 2 : ℕ) : ℝ))) ≤
        quadraticMissingWindowConstant η d *
          (η / ((T ^ 2 : ℕ) : ℝ)) := by
  let r₀ : ℝ := Real.exp (-d) / 2
  let H : ℝ := 2 * η + Real.log 4
  let c₀ : ℝ := H / η
  have hr₀ : 0 < r₀ := by
    dsimp [r₀]
    positivity
  have hH : 0 < H := by
    dsimp [H]
    exact add_pos (mul_pos (by norm_num) hη)
      (Real.log_pos (by norm_num))
  have hc₀ : 0 < c₀ := div_pos hH hη
  have hc₀η : c₀ * η = H := by
    dsimp [c₀]
    field_simp [hη.ne']
  have hlocalEventually :=
    eventually_uniform_quadraticLocalBand_upper
      hr₀ hc₀ hη
  have hpowNat :
      Tendsto (fun T : ℕ => T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpowReal :
      Tendsto (fun T : ℕ => ((T ^ 2 : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  have hratio :
      Tendsto
        (fun T : ℕ => H / ((T ^ 2 : ℕ) : ℝ))
        atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hpowReal
  have hsizeEventually :
      ∀ᶠ T : ℕ in atTop,
        H / ((T ^ 2 : ℕ) : ℝ) ≤ r₀ :=
    (hratio.eventually (Iio_mem_nhds hr₀)).mono
      (fun _ h => h.le)
  filter_upwards [
    hlocalEventually, hsizeEventually,
    eventually_gt_atTop 0] with T hlocalT hsizeT hT
  have hN : 0 < T ^ 2 := pow_pos hT 2
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by
    exact_mod_cast hN
  have hlocal :
      ∀ t : ℝ, Real.exp (-d) / 2 ≤ t →
        LocalPrimeBand.localBandShiftedReciprocalMass
            (T ^ 2) t (2 * η + Real.log 4) ≤
          quadraticMissingLocalConstant η d /
            ((T ^ 2 : ℕ) : ℝ) := by
    intro t ht
    have ht' : r₀ ≤ t := by
      simpa only [r₀] using ht
    have hbound := hlocalT t ht'
    rw [hc₀η] at hbound
    calc
      LocalPrimeBand.localBandShiftedReciprocalMass
          (T ^ 2) t (2 * η + Real.log 4) ≤
        (Real.log
            (Real.exp (2 * η + Real.log 4) + 1) + 1) /
          (((T ^ 2 : ℕ) : ℝ) * r₀) := by
        simpa only [H] using hbound
      _ = quadraticMissingLocalConstant η d /
          ((T ^ 2 : ℕ) : ℝ) := by
        dsimp [quadraticMissingLocalConstant, r₀]
        field_simp [hNR.ne', (Real.exp_pos (-d)).ne']
  have hwindow :=
    reciprocalWindowMassAlong_normalized_le_of_localBand
      (quadraticPrimeBand_prime T a) hN hη
      (by simpa only [H, r₀] using hsizeT)
      hlocal
  intro x
  have hx := hwindow x
  calc
    reciprocalWindowMassAlong
          Finset.univ
          (fun p : ↥(quadraticPrimeBand T a) => p.1)
          (fun p : ↥(quadraticPrimeBand T a) =>
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
          (fun p : ↥(quadraticPrimeBand T a) =>
            normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p.1 ≤ d)
          x (2 * (η / ((T ^ 2 : ℕ) : ℝ))) ≤
        2 * quadraticMissingLocalConstant η d /
          ((T ^ 2 : ℕ) : ℝ) := hx
    _ = quadraticMissingWindowConstant η d *
        (η / ((T ^ 2 : ℕ) : ℝ)) := by
      unfold quadraticMissingWindowConstant
      field_simp [hη.ne', hNR.ne']

/-- Per-scale quadratic-band collision theorem.  It consumes the
exposed-root two-pivot estimate and the reciprocal-window conclusion
above, with the corrected scale `T^2` and width `η / T^2`. -/
theorem quadraticPrimeBandCollision_le_of_twoPivot_and_window
    {T : ℕ} (hT : 0 < T)
    (a lower upper η : ℝ) (hη : 0 < η)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀)
    (s : Fin 3)
    (Ctwo Cone Lrank Eone Ezero : ℝ)
    [DecidablePred
      (PrimeBandRootGood (quadraticPrimeBand T a)
        ((T ^ 2 : ℕ) : ℝ)
        (η / ((T ^ 2 : ℕ) : ℝ))
        depths threshold s)]
    (hroot :
      (∑ o : FiveRootObservation (quadraticPrimeBand T a),
        if PrimeBandRootGood (quadraticPrimeBand T a)
            ((T ^ 2 : ℕ) : ℝ)
            (η / ((T ^ 2 : ℕ) : ℝ))
            depths threshold s o
        then
          finiteFiberMass
            (fiveRootPairAtom
              (quadraticPrimeBand T a) reciprocalBernoulli s)
            (fiveRootObservation
              (quadraticPrimeBand T a) s)
            o (fun _ => True)
        else 0) ≤
      primeBandRootSmallBallConstant
          Ctwo Cone Lrank Eone Ezero *
        (η / ((T ^ 2 : ℕ) : ℝ)) ^ 2)
    (hwindow : ∀ x : ℝ,
      reciprocalWindowMassAlong
          Finset.univ
          (fun p : ↥(quadraticPrimeBand T a) => p.1)
          (fun p : ↥(quadraticPrimeBand T a) =>
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1)
          (fun p : ↥(quadraticPrimeBand T a) =>
            normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p.1 ≤ d₀)
          x (2 * (η / ((T ^ 2 : ℕ) : ℝ))) ≤
        quadraticMissingWindowConstant η d₀ *
          (η / ((T ^ 2 : ℕ) : ℝ))) :
    fiveRootCollision
        (quadraticPrimeBand T a) reciprocalBernoulli
        (fivePrimeBandEvent
          (quadraticPrimeBand T a)
          ((T ^ 2 : ℕ) : ℝ) lower upper
          (η / ((T ^ 2 : ℕ) : ℝ))
          depths threshold) s ≤
      primeBandRootSmallBallConstant
          Ctwo Cone Lrank Eone Ezero *
        quadraticMissingWindowConstant η d₀ ^ 2 *
          (η / ((T ^ 2 : ℕ) : ℝ)) ^ 4 := by
  exact fiveRootCollision_le_of_twoPivot_and_window
    (quadraticPrimeBand_prime T a)
    ((T ^ 2 : ℕ) : ℝ) lower upper
    (η / ((T ^ 2 : ℕ) : ℝ))
    depths threshold hd₀ hthreshold s
          Ctwo Cone Lrank Eone Ezero
    (quadraticMissingWindowConstant η d₀)
    (div_nonneg hη.le (by positivity))
    (quadraticMissingWindowConstant_nonneg hη)
    hroot hwindow

end Erdos536
