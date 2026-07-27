import Erdos536.PrimeBandAdaptiveAnchors
import Erdos536.PrimeBandProfileConcrete
import Erdos536.QuadraticPrimeBandBase
import Erdos536.QuadraticPrimeBandTail

/-!
# Concrete first moment on the quadratic prime band

This file combines a shallow singleton anchor with two adaptive local
prime-band reservoirs.  The singleton fixes petal `2`; the two local
reservoirs fill the deficits of petals `0` and `1`.  The endpoint
rounding estimate in `PrimeBandAdaptiveAnchors` makes the completed
petal totals balanced at scale `T⁻²`.
-/

open scoped BigOperators
open Finset Filter Topology

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

/-- The shallow carrier is the depth interval `(0,75]`. -/
abbrev quadraticAnchorShallowCarrier (T : ℕ) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  quadraticDepthBandCarrier T 0 75

/-- Width in normalized logarithmic coordinates. -/
def quadraticAnchorWidth (T : ℕ) (η : ℝ) : ℝ :=
  η / (((T ^ 2 : ℕ) : ℝ))

/-- Deficit of petal `s` from the already present petal `2`. -/
noncomputable def quadraticAnchorDeficit
    (T : ℕ) (c : FiveConfiguration (quadraticProfilePrimeBand T))
    (s : Fin 3) : ℝ :=
  fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
      ((T ^ 2 : ℕ) : ℝ) c 2 -
    fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
      ((T ^ 2 : ℕ) : ℝ) c s

/-- The raw local reservoir filling one petal deficit. -/
noncomputable def quadraticAnchorRawCarrier
    (T : ℕ) (η : ℝ)
    (c : FiveConfiguration (quadraticProfilePrimeBand T))
    (s : Fin 3) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  quadraticLocalBandCarrier T 1
    (quadraticAnchorDeficit T c s) (η / 8)

/-- Remove the at most one occupied shallow anchor from a raw reservoir. -/
noncomputable def quadraticAnchorCarrier
    (T : ℕ) (η : ℝ)
    (c : FiveConfiguration (quadraticProfilePrimeBand T))
    (s : Fin 3) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  unusedSubcarrier c (quadraticAnchorRawCarrier T η c s)

/-- The concrete balanced/profile event used by the first moment. -/
noncomputable def quadraticAnchorEvent
    (T H : ℕ) (η : ℝ) :
    FiveConfiguration (quadraticProfilePrimeBand T) → Bool :=
  fivePrimeBandEvent
    (quadraticProfilePrimeBand T) ((T ^ 2 : ℕ) : ℝ)
    (9 / 20) (11 / 20) (quadraticAnchorWidth T η)
    (quadraticDelayedProfileDepths T H)
    quadraticDelayedProfileThresholdAtDepth

theorem quadraticAnchorRawCarrier_subset_shallow
    {T : ℕ} {η : ℝ}
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    {s : Fin 3}
    (hdeficit :
      depthCoordinate 75 ≤ quadraticAnchorDeficit T c s) :
    quadraticAnchorRawCarrier T η c s ⊆
      quadraticAnchorShallowCarrier T := by
  intro p hp
  have hpLocal :=
    mem_quadraticLocalBandCarrier.mp hp
  have hpLocalData :=
    LocalPrimeBand.mem_localPrimeBand.mp hpLocal
  rw [mem_quadraticDepthBandCarrier,
    mem_depthPrimeBand]
  refine ⟨hpLocalData.1, ?_, ?_⟩
  · have hendpoint :
      expEndpoint (depthCoordinate 75) (T ^ 2) ≤
        LocalPrimeBand.localLowerEndpoint (T ^ 2)
          (quadraticAnchorDeficit T c s) := by
      unfold LocalPrimeBand.localLowerEndpoint
      exact expEndpoint_mono hdeficit (T ^ 2)
    exact hendpoint.trans_lt hpLocalData.2.1
  · have hpGlobal :=
      (mem_quadraticPrimeBand.mp p.2).2.2
    simpa [depthCoordinate] using hpGlobal

theorem quadraticAnchorCarrier_subset_shallow
    {T : ℕ} {η : ℝ}
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    {s : Fin 3}
    (hdeficit :
      depthCoordinate 75 ≤ quadraticAnchorDeficit T c s) :
    quadraticAnchorCarrier T η c s ⊆
      quadraticAnchorShallowCarrier T :=
  (unusedSubcarrier_subset _ _).trans
    (quadraticAnchorRawCarrier_subset_shallow hdeficit)

theorem quadraticAnchorRawCarrier_weight_window
    {T : ℕ} {η : ℝ}
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    {s : Fin 3}
    (hT : 0 < T) (hη : 0 < η)
    (hdeficit :
      9 / 20 ≤ quadraticAnchorDeficit T c s)
    (hround :
      2 * Real.exp
          (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))) ≤
        η / 8)
    {p : ↥(quadraticProfilePrimeBand T)}
    (hp : p ∈ quadraticAnchorRawCarrier T η c s) :
    0 <
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 -
          quadraticAnchorDeficit T c s ∧
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 -
          quadraticAnchorDeficit T c s <
        quadraticAnchorWidth T η / 4 := by
  have hN : 0 < T ^ 2 := pow_pos hT _
  have hNR : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hN
  have hpLocal :=
    mem_quadraticLocalBandCarrier.mp hp
  have hlower :=
    normalizedLogWeight_mem_localPrimeBand_lower
      hN hpLocal
  have hupper :=
    normalizedLogWeight_mem_localPrimeBand_upper
      hN hdeficit (div_nonneg hη.le (by norm_num)) hpLocal
  constructor
  · linarith
  · unfold quadraticAnchorWidth
    rw [show
      η / (((T ^ 2 : ℕ) : ℝ)) / 4 =
        (η / 4) / (((T ^ 2 : ℕ) : ℝ)) by ring]
    apply (lt_div_iff₀ hNR).2
    have hbound :
        η / 8 +
            2 * Real.exp
              (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))) ≤
          η / 4 := by
      linarith
    have hscaled :
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 -
            quadraticAnchorDeficit T c s <
          (η / 8 +
            2 * Real.exp
              (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ)))) /
            ((T ^ 2 : ℕ) : ℝ) := by
      linarith
    calc
      (normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 -
          quadraticAnchorDeficit T c s) *
          ((T ^ 2 : ℕ) : ℝ) <
        η / 8 +
          2 * Real.exp
            (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))) := by
        exact (lt_div_iff₀ hNR).mp hscaled
      _ ≤ η / 4 := hbound

theorem eventually_quadraticAnchor_rounding
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      2 * Real.exp
          (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))) ≤
        η / 8 := by
  have hpowNat :
      Tendsto (fun T : ℕ ↦ T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpowReal :
      Tendsto (fun T : ℕ ↦ ((T ^ 2 : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  have hscale :
      Tendsto
        (fun T : ℕ ↦
          ((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))
        atTop atTop := by
    have h :=
      hpowReal.const_mul_atTop
        (show (0 : ℝ) < 9 / 20 by norm_num)
    simpa only [mul_comm] using h
  have hexp :
      Tendsto
        (fun T : ℕ ↦
          Real.exp
            (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))))
        atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hscale
  have htwo :
      Tendsto
        (fun T : ℕ ↦
          2 * Real.exp
            (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hexp)
  have hev := htwo.eventually
    (Iio_mem_nhds (show (0 : ℝ) < η / 8 by positivity))
  filter_upwards [hev] with T hT
  exact hT.le

theorem eventually_quadraticAnchor_width_small
    (η : ℝ) :
    ∀ᶠ T : ℕ in atTop,
      quadraticAnchorWidth T η / 4 ≤ 1 / 100 := by
  have hpow :
      Tendsto (fun T : ℕ ↦ T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hinv :
      Tendsto
        (fun T : ℕ ↦ 1 / (((T ^ 2 : ℕ) : ℝ)))
        atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hpow
  have hwidth :
      Tendsto
        (fun T : ℕ ↦ quadraticAnchorWidth T η / 4)
        atTop (𝓝 0) := by
    have hmul :
        Tendsto
          (fun T : ℕ ↦ η * (1 / (((T ^ 2 : ℕ) : ℝ))))
          atTop (𝓝 (η * 0)) :=
      (tendsto_const_nhds (x := η)).mul hinv
    have hdiv := hmul.div_const (4 : ℝ)
    simpa [quadraticAnchorWidth, div_eq_mul_inv,
      mul_assoc] using hdiv
  have hev := hwidth.eventually
    (Iio_mem_nhds (show (0 : ℝ) < 1 / 100 by norm_num))
  filter_upwards [hev] with T hT
  exact hT.le

theorem eventually_quadraticAnchorCarrier_intensity_lower
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      ∀ (c : FiveConfiguration (quadraticProfilePrimeBand T))
        (s : Fin 3),
        9 / 20 ≤ quadraticAnchorDeficit T c s →
        quadraticAnchorDeficit T c s ≤ 3 / 5 →
        (((quadraticAnchorRawCarrier T η c s).filter
          fun p ↦ c p ≠ 0).card) ≤ 1 →
        quadraticAnchorWidth T η / 400 ≤
          ∑ p ∈ quadraticAnchorCarrier T η c s,
            reciprocalBernoulli p.1 / 3 := by
  have hlocal :=
    eventually_uniform_quadraticLocalBand_lower
      (r₀ := (9 / 20 : ℝ)) (r₁ := (3 / 5 : ℝ))
      (c₀ := (1 / 8 : ℝ)) (η := η)
      (by norm_num) (by norm_num) (by norm_num) hη
  have hsub :=
    eventually_localPrimeBand_square_subset_quadraticPrimeBand
      (a := (1 : ℝ)) (r₀ := (9 / 20 : ℝ))
      (r₁ := (3 / 5 : ℝ)) (h := η / 8)
      (by norm_num) (by norm_num)
  have hatom :=
    eventually_quadraticAnchor_atom_loss_absorption
      (k := (1 / 200 : ℝ)) (η := η)
      (by norm_num) hη
  filter_upwards [
    hlocal, hsub, hatom, eventually_ge_atTop 1] with
      T hlocalT hsubT hatomT hT
  intro c s hdefLower hdefUpper hcard
  have hwidthPos : 0 < quadraticAnchorWidth T η := by
    unfold quadraticAnchorWidth
    have hTN : 0 < T := zero_lt_one.trans_le hT
    have hN : 0 < T ^ 2 := pow_pos hTN _
    positivity
  have hmass :=
    hlocalT (quadraticAnchorDeficit T c s)
      hdefLower hdefUpper
  rw [show (1 / 8 : ℝ) * η = η / 8 by ring] at hmass
  have hmass' :
      (1 / 8 : ℝ) * quadraticAnchorWidth T η /
          (8 * (3 / 5 : ℝ)) ≤
        LocalPrimeBand.localBandShiftedReciprocalMass
          (T ^ 2) (quadraticAnchorDeficit T c s) (η / 8) := by
    simpa [quadraticAnchorWidth] using hmass
  have hraw :
      quadraticAnchorWidth T η / 200 ≤
        LocalPrimeBand.localBandShiftedReciprocalMass
          (T ^ 2) (quadraticAnchorDeficit T c s) (η / 8) / 3 := by
    calc
      quadraticAnchorWidth T η / 200 ≤
          ((1 / 8 : ℝ) * quadraticAnchorWidth T η /
            (8 * (3 / 5 : ℝ))) / 3 := by
        have hw := hwidthPos.le
        norm_num
        nlinarith
      _ ≤ LocalPrimeBand.localBandShiftedReciprocalMass
          (T ^ 2) (quadraticAnchorDeficit T c s) (η / 8) / 3 :=
        div_le_div_of_nonneg_right hmass' (by norm_num)
  have hunused :=
    sum_unused_quadraticLocalBandCarrier_lower
      hT c (div_nonneg hη.le (by norm_num))
      (hsubT (quadraticAnchorDeficit T c s)
        hdefLower hdefUpper)
      hcard hraw
  change
    quadraticAnchorWidth T η / 200 -
        1 / (3 * (quadraticLowerCutoff T : ℝ)) ≤
      ∑ p ∈ quadraticAnchorCarrier T η c s,
        reciprocalBernoulli p.1 / 3 at hunused
  have hatom' :
      1 / (3 * (quadraticLowerCutoff T : ℝ)) ≤
        quadraticAnchorWidth T η / 400 := by
    change
      1 / (3 * (quadraticLowerCutoff T : ℝ)) ≤
        (1 / 200 : ℝ) * quadraticAnchorWidth T η / 2 at hatomT
    calc
      1 / (3 * (quadraticLowerCutoff T : ℝ)) ≤
          (1 / 200 : ℝ) * quadraticAnchorWidth T η / 2 :=
        hatomT
      _ = quadraticAnchorWidth T η / 400 := by ring
  linarith

theorem activeFiveLabel_ne_zero (l : ActiveFiveLabel) :
    activeFiveLabel l ≠ 0 := by
  cases l with
  | none => decide
  | some s =>
      intro h
      have hval := congrArg Fin.val h
      simp [activeFiveLabel, petalLabel] at hval

theorem fiveLabelDepthPrefix_subset_twoAnchorCompletion
    (R : Finset ℕ) (N : ℝ)
    (c : FiveConfiguration R) {px py : ↥R}
    (hcx : c px = 0) (hcy : c py = 0)
    (lx ly : FiveLabel) (l : ActiveFiveLabel) (d : ℝ) :
    fiveLabelDepthPrefix R N c l d ⊆
      fiveLabelDepthPrefix R N
        (twoAnchorCompletion c px py lx ly) l d := by
  intro p hp
  rw [mem_fiveLabelDepthPrefix] at hp ⊢
  have hpx : p ≠ px := by
    intro h
    subst p
    rw [hcx] at hp
    exact (activeFiveLabel_ne_zero l) hp.1.symm
  have hpy : p ≠ py := by
    intro h
    subst p
    rw [hcy] at hp
    exact (activeFiveLabel_ne_zero l) hp.1.symm
  exact ⟨by
    simpa [twoAnchorCompletion, hpx, hpy] using hp.1, hp.2⟩

theorem fiveLabelPrefixCount_le_twoAnchorCompletion
    (R : Finset ℕ) (N : ℝ)
    (c : FiveConfiguration R) {px py : ↥R}
    (hcx : c px = 0) (hcy : c py = 0)
    (lx ly : FiveLabel) (l : ActiveFiveLabel) (d : ℝ) :
    fiveLabelPrefixCount R N c l d ≤
      fiveLabelPrefixCount R N
        (twoAnchorCompletion c px py lx ly) l d := by
  unfold fiveLabelPrefixCount
  exact Finset.card_le_card
    (fiveLabelDepthPrefix_subset_twoAnchorCompletion
      R N c hcx hcy lx ly l d)

theorem quadraticAnchorCompletion_mem_event
    {T H : ℕ} {η : ℝ}
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    {px py : ↥(quadraticProfilePrimeBand T)}
    (hT : 0 < T) (hη : 0 < η)
    (hxy : px ≠ py) (hcx : c px = 0) (hcy : c py = 0)
    (hround :
      2 * Real.exp
          (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))) ≤
        η / 8)
    (hwidthSmall : quadraticAnchorWidth T η / 4 ≤ 1 / 100)
    (hcenterLower :
      23 / 50 ≤
        fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ) c 2)
    (hcenterUpper :
      fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ) c 2 ≤ 27 / 50)
    (hdeficitZero :
      9 / 20 ≤ quadraticAnchorDeficit T c 0)
    (hdeficitOne :
      9 / 20 ≤ quadraticAnchorDeficit T c 1)
    (hprofile :
      ∀ l : ActiveFiveLabel,
        ∀ d : ↥(quadraticDelayedProfileDepths T H),
          quadraticDelayedProfileThresholdAtDepth d.1 ≤
            fiveLabelPrefixCount
              (quadraticProfilePrimeBand T)
              ((T ^ 2 : ℕ) : ℝ) c l d.1)
    (hpx : px ∈ quadraticAnchorRawCarrier T η c 0)
    (hpy : py ∈ quadraticAnchorRawCarrier T η c 1) :
    quadraticAnchorEvent T H η
      (twoAnchorCompletion c px py
        (petalLabel 0) (petalLabel 1)) := by
  have hwidthPos : 0 < quadraticAnchorWidth T η := by
    unfold quadraticAnchorWidth
    have hN : 0 < T ^ 2 := pow_pos hT _
    positivity
  have hxWindow :=
    quadraticAnchorRawCarrier_weight_window
      hT hη hdeficitZero hround hpx
  have hyWindow :=
    quadraticAnchorRawCarrier_weight_window
      hT hη hdeficitOne hround hpy
  have hx :
      |fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ) c 0 +
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) px.1 -
        fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ) c 2| ≤
        quadraticAnchorWidth T η / 4 := by
    have heq :
        fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
              ((T ^ 2 : ℕ) : ℝ) c 0 +
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) px.1 -
          fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
              ((T ^ 2 : ℕ) : ℝ) c 2 =
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) px.1 -
          quadraticAnchorDeficit T c 0 := by
      unfold quadraticAnchorDeficit
      ring
    rw [heq, abs_of_nonneg hxWindow.1.le]
    exact hxWindow.2.le
  have hy :
      |fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ) c 1 +
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) py.1 -
        fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ) c 2| ≤
        quadraticAnchorWidth T η / 4 := by
    have heq :
        fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
              ((T ^ 2 : ℕ) : ℝ) c 1 +
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) py.1 -
          fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
              ((T ^ 2 : ℕ) : ℝ) c 2 =
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) py.1 -
          quadraticAnchorDeficit T c 1 := by
      unfold quadraticAnchorDeficit
      ring
    rw [heq, abs_of_nonneg hyWindow.1.le]
    exact hyWindow.2.le
  have hgeometry :=
    twoAnchorCompletion_petal_interval_balance
      (quadraticProfilePrimeBand T) ((T ^ 2 : ℕ) : ℝ)
      (9 / 20) (11 / 20)
      (quadraticAnchorWidth T η / 4)
      (quadraticAnchorWidth T η)
      c hxy hcx hcy
      (div_nonneg hwidthPos.le (by norm_num))
      (by linarith [hwidthPos])
      (by linarith)
      (by linarith)
      hx hy
  rw [quadraticAnchorEvent, fivePrimeBandEvent_iff]
  refine ⟨hgeometry.1, hgeometry.2, ?_⟩
  intro l d
  exact (hprofile l d).trans
    (fiveLabelPrefixCount_le_twoAnchorCompletion
      (quadraticProfilePrimeBand T) ((T ^ 2 : ℕ) : ℝ)
      c hcx hcy (petalLabel 0) (petalLabel 1) l d.1)

/-- Deterministic data required of every background configuration. -/
structure QuadraticAnchorBackgroundGood
    (T H : ℕ) (η : ℝ)
    (c : FiveConfiguration (quadraticProfilePrimeBand T)) : Prop where
  shallowFree :
    ∀ p ∈ quadraticAnchorShallowCarrier T,
      c p ≠ petalLabel 0 ∧ c p ≠ petalLabel 1
  centerLower :
    23 / 50 ≤
      fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ) c 2
  centerUpper :
    fivePetalNormalizedTotal (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ) c 2 ≤ 27 / 50
  deficitZeroLower :
    9 / 20 ≤ quadraticAnchorDeficit T c 0
  deficitZeroUpper :
    quadraticAnchorDeficit T c 0 ≤ 3 / 5
  deficitOneLower :
    9 / 20 ≤ quadraticAnchorDeficit T c 1
  deficitOneUpper :
    quadraticAnchorDeficit T c 1 ≤ 3 / 5
  occupiedZero :
    (((quadraticAnchorRawCarrier T η c 0).filter
      fun p ↦ c p ≠ 0).card) ≤ 1
  occupiedOne :
    (((quadraticAnchorRawCarrier T η c 1).filter
      fun p ↦ c p ≠ 0).card) ≤ 1
  profile :
    ∀ l : ActiveFiveLabel,
      ∀ d : ↥(quadraticDelayedProfileDepths T H),
        quadraticDelayedProfileThresholdAtDepth d.1 ≤
          fiveLabelPrefixCount
            (quadraticProfilePrimeBand T)
            ((T ^ 2 : ℕ) : ℝ) c l d.1

/-- Fixed-scale first-moment assembly from a positive background family. -/
theorem quadraticAnchorEventMass_lower_of_base
    {T H : ℕ} {η b : ℝ}
    (Base : Finset
      (FiveConfiguration (quadraticProfilePrimeBand T)))
    (hT : 1 ≤ T) (hη : 0 < η)
    (hround :
      2 * Real.exp
          (-(((T ^ 2 : ℕ) : ℝ) * (9 / 20 : ℝ))) ≤
        η / 8)
    (hwidthSmall : quadraticAnchorWidth T η / 4 ≤ 1 / 100)
    (hgood :
      ∀ c ∈ Base, QuadraticAnchorBackgroundGood T H η c)
    (hbase :
      b ≤ ∑ c ∈ Base,
        poissonCompatibleConfigurationWeight
          (quadraticProfilePrimeBand T) reciprocalBernoulli c)
    (hIntensity :
      ∀ (c : FiveConfiguration (quadraticProfilePrimeBand T))
        (s : Fin 3),
        9 / 20 ≤ quadraticAnchorDeficit T c s →
        quadraticAnchorDeficit T c s ≤ 3 / 5 →
        (((quadraticAnchorRawCarrier T η c s).filter
          fun p ↦ c p ≠ 0).card) ≤ 1 →
        quadraticAnchorWidth T η / 400 ≤
          ∑ p ∈ quadraticAnchorCarrier T η c s,
            reciprocalBernoulli p.1 / 3)
    (hcutoffDiagonal :
      1 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
        ((1 / 400 : ℝ) * quadraticAnchorWidth T η) ^ 2 / 2)
    (htransfer :
      16 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
        b * ((1 / 400 : ℝ) * quadraticAnchorWidth T η) ^ 2 / 4) :
    (b * (1 / 400 : ℝ) ^ 2 / 4) *
        quadraticAnchorWidth T η ^ 2 ≤
      fiveEventMass (quadraticProfilePrimeBand T)
        reciprocalBernoulli (quadraticAnchorEvent T H η) := by
  let K := quadraticAnchorShallowCarrier T
  let Ix :
      FiveConfiguration (quadraticProfilePrimeBand T) →
        Finset ↥(quadraticProfilePrimeBand T) :=
    fun c ↦ quadraticAnchorCarrier T η c 0
  let Iy :
      FiveConfiguration (quadraticProfilePrimeBand T) →
        Finset ↥(quadraticProfilePrimeBand T) :=
    fun c ↦ quadraticAnchorCarrier T η c 1
  have hdepth :
      depthCoordinate 75 ≤ (9 / 20 : ℝ) := by
    unfold depthCoordinate
    exact exp_neg_seventyFive_lt.le.trans (by norm_num)
  have hclean :
      TwoAnchorBaseClean K Base Ix Iy
        (petalLabel 0) (petalLabel 1) := by
    apply twoAnchorBaseClean_unusedSubcarriers
    intro c hc p hp
    exact (hgood c hc).shallowFree p hp
  have hIx : ∀ c ∈ Base, Ix c ⊆ K := by
    intro c hc
    exact quadraticAnchorCarrier_subset_shallow
      (hdepth.trans (hgood c hc).deficitZeroLower)
  have hIy : ∀ c ∈ Base, Iy c ⊆ K := by
    intro c hc
    exact quadraticAnchorCarrier_subset_shallow
      (hdepth.trans (hgood c hc).deficitOneLower)
  have hB :
      ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
        quadraticAnchorEvent T H η
          (completeTwoAnchorChoice
            (petalLabel 0) (petalLabel 1) z) := by
    intro z hz
    rw [mem_adaptiveTwoAnchorChoices] at hz
    rcases z with ⟨c, ⟨px, py⟩⟩
    have hpx := mem_unusedSubcarrier.mp hz.2.1
    have hpy := mem_unusedSubcarrier.mp hz.2.2.1
    have hg := hgood c hz.1
    exact quadraticAnchorCompletion_mem_event
      (show 0 < T by omega) hη hz.2.2.2 hpx.2 hpy.2
      hround hwidthSmall
      hg.centerLower hg.centerUpper
      hg.deficitZeroLower hg.deficitOneLower
      hg.profile hpx.1 hpy.1
  have hX :
      ∀ c ∈ Base,
        (1 / 400 : ℝ) * quadraticAnchorWidth T η ≤
          ∑ p ∈ Ix c, reciprocalBernoulli p.1 / 3 := by
    intro c hc
    have hg := hgood c hc
    rw [show
      (1 / 400 : ℝ) * quadraticAnchorWidth T η =
        quadraticAnchorWidth T η / 400 by ring]
    simpa only [Ix] using
      hIntensity c 0 hg.deficitZeroLower
        hg.deficitZeroUpper hg.occupiedZero
  have hY :
      ∀ c ∈ Base,
        (1 / 400 : ℝ) * quadraticAnchorWidth T η ≤
          ∑ p ∈ Iy c, reciprocalBernoulli p.1 / 3 := by
    intro c hc
    have hg := hgood c hc
    rw [show
      (1 / 400 : ℝ) * quadraticAnchorWidth T η =
        quadraticAnchorWidth T η / 400 by ring]
    simpa only [Iy] using
      hIntensity c 1 hg.deficitOneLower
        hg.deficitOneUpper hg.occupiedOne
  apply quadraticFiveEventMass_adaptiveTwoAnchor_moment_lower
    hT (1 : ℝ) (quadraticAnchorEvent T H η)
    K Base Ix Iy (petalLabel 0) (petalLabel 1)
    (by decide) (by decide) (by decide)
    hclean hIx hIy hB hbase
    (by norm_num)
    (by
      unfold quadraticAnchorWidth
      positivity)
    hX hY hcutoffDiagonal htransfer

/-- Eventual form of the background-to-first-moment assembly. -/
theorem eventually_quadraticAnchorEventMass_lower_of_base
    {η b : ℝ} (hη : 0 < η) (hb : 0 < b)
    (H : ℕ → ℕ)
    (Base : ∀ T : ℕ, Finset
      (FiveConfiguration (quadraticProfilePrimeBand T)))
    (hbase :
      ∀ᶠ T : ℕ in atTop,
        b ≤ ∑ c ∈ Base T,
          poissonCompatibleConfigurationWeight
            (quadraticProfilePrimeBand T) reciprocalBernoulli c)
    (hgood :
      ∀ᶠ T : ℕ in atTop,
        ∀ c ∈ Base T,
          QuadraticAnchorBackgroundGood T (H T) η c) :
    ∀ᶠ T : ℕ in atTop,
      (b * (1 / 400 : ℝ) ^ 2 / 4) *
          quadraticAnchorWidth T η ^ 2 ≤
        fiveEventMass (quadraticProfilePrimeBand T)
          reciprocalBernoulli
          (quadraticAnchorEvent T (H T) η) := by
  have hround := eventually_quadraticAnchor_rounding hη
  have hwidth := eventually_quadraticAnchor_width_small η
  have hIntensity :=
    eventually_quadraticAnchorCarrier_intensity_lower hη
  have hcutoff :=
    eventually_quadraticAnchor_cutoff_absorptions
      hb (show (0 : ℝ) < 1 / 400 by norm_num) hη
  filter_upwards [
    hbase, hgood, hround, hwidth, hIntensity, hcutoff,
    eventually_ge_atTop 1] with
      T hbaseT hgoodT hroundT hwidthT hIntensityT
        hcutoffT hT
  exact quadraticAnchorEventMass_lower_of_base
    (Base T) hT hη hroundT hwidthT hgoodT hbaseT
    hIntensityT hcutoffT.1 hcutoffT.2

theorem quadraticAnchorEvent_petalLogBalanced
    {T H : ℕ} {η : ℝ} (hT : 0 < T) :
    FiveEventPetalLogBalanced
      (quadraticProfilePrimeBand T)
      (quadraticAnchorEvent T H η) η := by
  have hN : 0 < T ^ 2 := pow_pos hT _
  have hNR : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hN
  have h :=
    fivePrimeBandEvent_petalLogBalanced
      (R := quadraticProfilePrimeBand T)
      (T := ((T ^ 2 : ℕ) : ℝ))
      (lower := (9 / 20 : ℝ)) (upper := (11 / 20 : ℝ))
      (w := quadraticAnchorWidth T η)
      (depths := quadraticDelayedProfileDepths T H)
      (threshold := quadraticDelayedProfileThresholdAtDepth)
      hNR
  have hscale :
      ((T ^ 2 : ℕ) : ℝ) * quadraticAnchorWidth T η = η := by
    unfold quadraticAnchorWidth
    field_simp [hNR.ne']
  simpa only [quadraticAnchorEvent, hscale] using h

theorem eventually_quadraticAnchorEvent_hasPetals
    (H : ℕ → ℕ) (η : ℝ) :
    ∀ᶠ T : ℕ in atTop,
      FiveEventHasPetals
        (quadraticProfilePrimeBand T)
        (quadraticAnchorEvent T (H T) η) := by
  have hfirst :=
    eventually_quadraticDelayedProfileFirstDepth
  filter_upwards [hfirst] with T hfirstT
  simpa only [quadraticAnchorEvent] using
    (fivePrimeBandEvent_hasPetals
      (R := quadraticProfilePrimeBand T)
      (T := ((T ^ 2 : ℕ) : ℝ))
      (lower := (9 / 20 : ℝ)) (upper := (11 / 20 : ℝ))
      (w := quadraticAnchorWidth T η)
      (depths := quadraticDelayedProfileDepths T (H T))
      (threshold := quadraticDelayedProfileThresholdAtDepth)
      (hfirstT (H T)).1 (hfirstT (H T)).2)

/-- Eventual first-moment package in the interface consumed by the
quadratic moment/collision assembly. -/
theorem eventually_quadraticAnchorFirstMomentPackage_of_base
    {η b : ℝ} (hη : 0 < η) (hb : 0 < b)
    (H : ℕ → ℕ)
    (Base : ∀ T : ℕ, Finset
      (FiveConfiguration (quadraticProfilePrimeBand T)))
    (hbase :
      ∀ᶠ T : ℕ in atTop,
        b ≤ ∑ c ∈ Base T,
          poissonCompatibleConfigurationWeight
            (quadraticProfilePrimeBand T) reciprocalBernoulli c)
    (hgood :
      ∀ᶠ T : ℕ in atTop,
        ∀ c ∈ Base T,
          QuadraticAnchorBackgroundGood T (H T) η c) :
    ∀ᶠ T : ℕ in atTop,
      0 < quadraticAnchorWidth T η ∧
        FiveEventHasPetals
          (quadraticProfilePrimeBand T)
          (quadraticAnchorEvent T (H T) η) ∧
        FiveEventPetalLogBalanced
          (quadraticProfilePrimeBand T)
          (quadraticAnchorEvent T (H T) η) η ∧
        (b * (1 / 400 : ℝ) ^ 2 / 4) *
            quadraticAnchorWidth T η ^ 2 ≤
          fiveEventMass (quadraticProfilePrimeBand T)
            reciprocalBernoulli
            (quadraticAnchorEvent T (H T) η) := by
  have hmass :=
    eventually_quadraticAnchorEventMass_lower_of_base
      hη hb H Base hbase hgood
  have hpetals :=
    eventually_quadraticAnchorEvent_hasPetals H η
  filter_upwards [
    hmass, hpetals, eventually_gt_atTop 0] with
      T hmassT hpetalsT hT
  have hwidth :
      0 < quadraticAnchorWidth T η := by
    unfold quadraticAnchorWidth
    have hN : 0 < T ^ 2 := pow_pos hT _
    positivity
  exact
    ⟨hwidth, hpetalsT,
      quadraticAnchorEvent_petalLogBalanced hT, hmassT⟩

end Erdos536
