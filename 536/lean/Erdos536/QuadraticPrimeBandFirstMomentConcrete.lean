import Erdos536.QuadraticPrimeBandAnchorGood
import Erdos536.QuadraticPrimeBandFirstMoment

/-!
# Concrete quadratic first moment

This file joins the positive background event from
`QuadraticPrimeBandAnchorBase` to the adaptive two-anchor construction
from `QuadraticPrimeBandFirstMoment`.
-/

open scoped BigOperators
open Finset Filter Topology

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

local instance (T : ℕ) :
    DecidablePred (quadraticShallowPred T) :=
  fun p ↦ inferInstanceAs (Decidable (p ∈ quadraticShallowCarrier T))

theorem exp_seven_tenths_gt_two :
    (2 : ℝ) < Real.exp (7 / 10 : ℝ) := by
  refine lt_of_lt_of_le ?_
    (Real.sum_le_exp_of_nonneg
      (show (0 : ℝ) ≤ 7 / 10 by norm_num) 4)
  norm_num [Finset.sum_range_succ, Nat.factorial]

theorem exp_three_fourths_lt_fifty_div_twenty_three :
    Real.exp (3 / 4 : ℝ) < 50 / 23 := by
  have h :=
    Real.exp_bound'
      (show (0 : ℝ) ≤ 3 / 4 by norm_num)
      (show (3 / 4 : ℝ) ≤ 1 by norm_num)
      (n := 5) (by norm_num)
  calc
    Real.exp (3 / 4 : ℝ) ≤
        (∑ m ∈ Finset.range 5,
          (3 / 4 : ℝ) ^ m / m.factorial) +
          (3 / 4 : ℝ) ^ 5 * (5 + 1) /
            (Nat.factorial 5 * 5) := h
    _ < 50 / 23 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]

theorem twenty_three_fiftieths_lt_depthCoordinate_three_fourths :
    (23 / 50 : ℝ) < depthCoordinate (3 / 4) := by
  unfold depthCoordinate
  rw [Real.exp_neg]
  have h :=
    one_div_lt_one_div_of_lt (Real.exp_pos (3 / 4 : ℝ))
      exp_three_fourths_lt_fifty_div_twenty_three
  norm_num at h ⊢
  exact h

theorem depthCoordinate_seven_tenths_lt_one_half :
    depthCoordinate (7 / 10) < (1 / 2 : ℝ) := by
  unfold depthCoordinate
  rw [Real.exp_neg]
  simpa only [one_div] using
    one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 2)
      exp_seven_tenths_gt_two

/-- Every prime in the background anchor cell has normalized logarithmic
weight in the fixed interval `(23/50, 51/100)` once `T ≥ 10`. -/
theorem quadraticBackgroundAnchorCarrier_weight_bounds
    {T : ℕ} (hT : 10 ≤ T)
    {p : ↥(quadraticProfilePrimeBand T)}
    (hp : p ∈ quadraticBackgroundAnchorCarrier T) :
    (23 / 50 : ℝ) <
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 ∧
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 <
        (51 / 100 : ℝ) := by
  have hpCarrier :
      p ∈ quadraticDepthBandCarrier T (7 / 10) (3 / 4) := by
    simpa only [quadraticBackgroundAnchorCarrier] using hp
  have hpBand :=
    mem_quadraticDepthBandCarrier.mp hpCarrier
  have hp' := mem_depthPrimeBand.mp hpBand
  have hTpos : 0 < T := by omega
  have hN : 0 < T ^ 2 := pow_pos hTpos _
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by
    exact_mod_cast hN
  have hN100Nat : 100 ≤ T ^ 2 := by
    simpa using Nat.pow_le_pow_left hT 2
  have hN100 : (100 : ℝ) ≤ ((T ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hN100Nat
  have hpR : (0 : ℝ) < p.1 := by
    exact_mod_cast hp'.1.pos
  constructor
  · have hEndpointPos :
        (0 : ℝ) <
          expEndpoint (depthCoordinate (3 / 4)) (T ^ 2) := by
      exact_mod_cast
        (Nat.ceil_pos.mpr
          (Real.exp_pos
            (((T ^ 2 : ℕ) : ℝ) *
              depthCoordinate (3 / 4))))
    have hEndpointLt :
        (expEndpoint (depthCoordinate (3 / 4)) (T ^ 2) : ℝ) <
          (p.1 : ℝ) := by
      exact_mod_cast hp'.2.1
    have hlogEndpointLt :
        Real.log
            (expEndpoint
              (depthCoordinate (3 / 4)) (T ^ 2) : ℝ) <
          Real.log (p.1 : ℝ) :=
      Real.log_lt_log hEndpointPos hEndpointLt
    have hlogEndpointLower :
        ((T ^ 2 : ℕ) : ℝ) * depthCoordinate (3 / 4) ≤
          Real.log
            (expEndpoint
              (depthCoordinate (3 / 4)) (T ^ 2) : ℝ) := by
      simpa only [LocalPrimeBand.localLowerEndpoint] using
        LocalPrimeBand.localLowerEndpoint_log_lower
          (T ^ 2) (depthCoordinate (3 / 4))
    have hcoordinate :
        depthCoordinate (3 / 4) <
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 := by
      rw [normalizedLogWeight]
      apply (lt_div_iff₀ hNR).2
      nlinarith
    exact
      twenty_three_fiftieths_lt_depthCoordinate_three_fourths.trans
        hcoordinate
  · have hpEndpoint :
        (p.1 : ℝ) ≤
          expEndpoint (depthCoordinate (7 / 10)) (T ^ 2) := by
      exact_mod_cast hp'.2.2
    have hlogpEndpoint :
        Real.log (p.1 : ℝ) ≤
          Real.log
            (expEndpoint
              (depthCoordinate (7 / 10)) (T ^ 2) : ℝ) :=
      Real.log_le_log hpR hpEndpoint
    have hlogEndpoint :
        Real.log
            (expEndpoint
              (depthCoordinate (7 / 10)) (T ^ 2) : ℝ) <
          ((T ^ 2 : ℕ) : ℝ) * depthCoordinate (7 / 10) + 1 := by
      simpa only [LocalPrimeBand.localLowerEndpoint] using
        LocalPrimeBand.localLowerEndpoint_log_upper
          (T ^ 2) (show 0 ≤ depthCoordinate (7 / 10) by
            exact (depthCoordinate_pos _).le)
    rw [normalizedLogWeight]
    apply (div_lt_iff₀ hNR).2
    nlinarith [depthCoordinate_seven_tenths_lt_one_half]

/-- Eventual form of the uniform background-anchor weight interval. -/
theorem eventually_quadraticBackgroundAnchorCarrier_weight_bounds :
    ∀ᶠ T : ℕ in atTop,
      ∀ p ∈ quadraticBackgroundAnchorCarrier T,
        (23 / 50 : ℝ) <
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 ∧
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1 <
            (51 / 100 : ℝ) := by
  filter_upwards [eventually_ge_atTop 10] with T hT
  intro p hp
  exact quadraticBackgroundAnchorCarrier_weight_bounds hT hp

/-! ## Deterministic shallow-anchor consequences -/

/-- Membership in the generic background family exposes the unique
shallow anchor coordinate and the exact shallow restriction. -/
theorem quadraticFirstMomentBase_exists_anchor
    {T : ℕ} {D : (QuadraticDeepIndex T → FiveLabel) → Prop}
    [DecidablePred D]
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    (hc : c ∈ quadraticAnchorBase T D) :
    ∃ q : QuadraticShallowIndex T,
      q.1 ∈ quadraticBackgroundAnchorCarrier T ∧
        (fun p : QuadraticShallowIndex T ↦ c p.1) =
          singletonFiveConfiguration (petalLabel 2) q := by
  classical
  have hshallow :=
    (mem_quadraticAnchorBase.mp hc).1
  change
    (fun p : QuadraticShallowIndex T ↦ c p.1) ∈
      singletonFiveConfigurations
        (quadraticBackgroundAnchorShallowCarrier T)
        (petalLabel 2) at hshallow
  rw [singletonFiveConfigurations] at hshallow
  obtain ⟨q, hq, hrestriction⟩ :=
    Finset.mem_image.mp hshallow
  exact
    ⟨q,
      mem_quadraticBackgroundAnchorShallowCarrier.mp hq,
      hrestriction.symm⟩

/-- Under a shallow singleton restriction, any carrier supported on the
shallow coordinates has at most one occupied coordinate. -/
theorem quadraticShallowSingleton_occupied_le_one
    {T : ℕ}
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    {q : QuadraticShallowIndex T}
    (hrestriction :
      (fun p : QuadraticShallowIndex T ↦ c p.1) =
        singletonFiveConfiguration (petalLabel 2) q)
    {S : Finset ↥(quadraticProfilePrimeBand T)}
    (hS : S ⊆ quadraticShallowCarrier T) :
    ((S.filter fun p ↦ c p ≠ 0).card) ≤ 1 := by
  classical
  have hsubset :
      S.filter (fun p ↦ c p ≠ 0) ⊆ {q.1} := by
    intro p hp
    have hpS := (Finset.mem_filter.mp hp).1
    have hcp := (Finset.mem_filter.mp hp).2
    let p' : QuadraticShallowIndex T :=
      ⟨p, hS hpS⟩
    have hpvalue := congrFun hrestriction p'
    have hpq : p' = q := by
      by_contra hpq
      have hpzero : c p = 0 := by
        simpa [p', singletonFiveConfiguration,
          emptyFiveConfiguration, hpq] using hpvalue
      exact hcp hpzero
    simp only [Finset.mem_singleton]
    exact congrArg Subtype.val hpq
  exact
    (Finset.card_le_card hsubset).trans_eq
      (Finset.card_singleton q.1)

/-- The normalized total of a background configuration splits into its
deep total and the contribution of its unique shallow anchor. -/
theorem fivePetalNormalizedTotal_eq_deep_add_anchor
    {T : ℕ}
    (c : FiveConfiguration (quadraticProfilePrimeBand T))
    (q : QuadraticShallowIndex T)
    (hrestriction :
      (fun p : QuadraticShallowIndex T ↦ c p.1) =
        singletonFiveConfiguration (petalLabel 2) q)
    (s : Fin 3) :
    fivePetalNormalizedTotal
        (quadraticProfilePrimeBand T)
        ((T ^ 2 : ℕ) : ℝ) c s =
      quadraticDeepPetalTotal T s
          (fun p : QuadraticDeepIndex T ↦ c p.1) +
        if s = 2 then
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) q.1.1
        else 0 := by
  let f : ↥(quadraticProfilePrimeBand T) → ℝ :=
    fun p ↦
      if c p = petalLabel s then
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1
      else 0
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (quadraticShallowPred T) f
  have hdeep :
      (∑ p : QuadraticDeepIndex T, f p.1) =
        quadraticDeepPetalTotal T s
          (fun p : QuadraticDeepIndex T ↦ c p.1) := by
    unfold quadraticDeepPetalTotal
    simp only [f]
  have hshallow :
      (∑ p : QuadraticShallowIndex T, f p.1) =
        if s = 2 then
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) q.1.1
        else 0 := by
    by_cases hs : s = 2
    · subst s
      rw [if_pos rfl]
      calc
        (∑ p : QuadraticShallowIndex T, f p.1) = f q.1 := by
          apply Fintype.sum_eq_single q
          intro p hpq
          have hpvalue := congrFun hrestriction p
          have hpzero : c p.1 = 0 := by
            simpa [singletonFiveConfiguration,
              emptyFiveConfiguration, hpq] using hpvalue
          simp [f, hpzero, petalLabel]
        _ =
            normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) q.1.1 := by
          have hqvalue := congrFun hrestriction q
          have hqpetal :
              c q.1 = petalLabel (2 : Fin 3) := by
            simpa [singletonFiveConfiguration] using hqvalue
          simp [f, hqpetal]
    · rw [if_neg hs]
      apply Finset.sum_eq_zero
      intro p _hp
      have hpvalue := congrFun hrestriction p
      by_cases hpq : p = q
      · subst p
        have hqpetal :
            c q.1 = petalLabel (2 : Fin 3) := by
          simpa [singletonFiveConfiguration] using hpvalue
        have hpetal :
            petalLabel (2 : Fin 3) ≠ petalLabel s := by
          intro heq
          apply hs
          apply Fin.ext
          have hval := congrArg Fin.val heq
          simp only [petalLabel] at hval
          omega
        simp [f, hqpetal, hpetal]
      · have hpzero : c p.1 = 0 := by
          simpa [singletonFiveConfiguration,
            emptyFiveConfiguration, hpq] using hpvalue
        simp [f, hpzero, petalLabel]
  rw [fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal]
  unfold fiveLabelWeightedTotal
  change (∑ p, f p) = _
  calc
    (∑ p, f p) =
        (∑ p : QuadraticShallowIndex T, f p.1) +
          ∑ p : QuadraticDeepIndex T, f p.1 :=
      hsplit.symm
    _ = _ := by rw [hshallow, hdeep, add_comm]

/-! ## From a deep-good restriction to an adaptive background -/

/-- The shallow singleton, deep tail bounds, and deep profile success are
exactly the deterministic hypotheses required by the adaptive
two-anchor construction. -/
theorem quadraticAnchorBackgroundGood_of_base
    {T H : ℕ} {η : ℝ}
    {D : (QuadraticDeepIndex T → FiveLabel) → Prop}
    [DecidablePred D]
    {c : FiveConfiguration (quadraticProfilePrimeBand T)}
    (hT : 10 ≤ T)
    (hc : c ∈ quadraticAnchorBase T D)
    (hprofile :
      quadraticDeepProfileFailure T H
          (fun p : QuadraticDeepIndex T ↦ c p.1) = false)
    (htail :
      ∀ s : Fin 3,
        quadraticDeepPetalTotal T s
            (fun p : QuadraticDeepIndex T ↦ c p.1) ≤
          1 / 100) :
    QuadraticAnchorBackgroundGood T H η c := by
  obtain ⟨q, hqCarrier, hrestriction⟩ :=
    quadraticFirstMomentBase_exists_anchor hc
  have hTpos : 0 < T := by omega
  have hqBounds :=
    quadraticBackgroundAnchorCarrier_weight_bounds hT hqCarrier
  have hreservoirSubset :
      quadraticAnchorShallowCarrier T ⊆
        quadraticShallowCarrier T := by
    exact quadraticDepthBandCarrier_mono
      (show (0 : ℝ) ≤ 0 by norm_num)
      (show (75 : ℝ) ≤ 76 by norm_num)
  have htotalZero :
      fivePetalNormalizedTotal
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ) c 0 =
        quadraticDeepPetalTotal T 0
          (fun p : QuadraticDeepIndex T ↦ c p.1) := by
    have h :=
      fivePetalNormalizedTotal_eq_deep_add_anchor
        c q hrestriction (0 : Fin 3)
    rw [if_neg (show (0 : Fin 3) ≠ 2 by decide), add_zero] at h
    exact h
  have htotalOne :
      fivePetalNormalizedTotal
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ) c 1 =
        quadraticDeepPetalTotal T 1
          (fun p : QuadraticDeepIndex T ↦ c p.1) := by
    have h :=
      fivePetalNormalizedTotal_eq_deep_add_anchor
        c q hrestriction (1 : Fin 3)
    rw [if_neg (show (1 : Fin 3) ≠ 2 by decide), add_zero] at h
    exact h
  have htotalTwo :
      fivePetalNormalizedTotal
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ) c 2 =
        quadraticDeepPetalTotal T 2
            (fun p : QuadraticDeepIndex T ↦ c p.1) +
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) q.1.1 := by
    simpa only [if_pos rfl] using
      (fivePetalNormalizedTotal_eq_deep_add_anchor
        c q hrestriction (2 : Fin 3))
  have hdeepZeroNonneg :
      0 ≤ quadraticDeepPetalTotal T 0
        (fun p : QuadraticDeepIndex T ↦ c p.1) :=
    quadraticDeepPetalTotal_nonneg hTpos 0 _
  have hdeepOneNonneg :
      0 ≤ quadraticDeepPetalTotal T 1
        (fun p : QuadraticDeepIndex T ↦ c p.1) :=
    quadraticDeepPetalTotal_nonneg hTpos 1 _
  have hdeepTwoNonneg :
      0 ≤ quadraticDeepPetalTotal T 2
        (fun p : QuadraticDeepIndex T ↦ c p.1) :=
    quadraticDeepPetalTotal_nonneg hTpos 2 _
  have hcenterLower :
      23 / 50 ≤
        fivePetalNormalizedTotal
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ) c 2 := by
    rw [htotalTwo]
    linarith
  have hcenterUpper :
      fivePetalNormalizedTotal
          (quadraticProfilePrimeBand T)
          ((T ^ 2 : ℕ) : ℝ) c 2 ≤
        27 / 50 := by
    rw [htotalTwo]
    nlinarith [htail 2]
  have hdeficitZeroLower :
      9 / 20 ≤ quadraticAnchorDeficit T c 0 := by
    unfold quadraticAnchorDeficit
    rw [htotalTwo, htotalZero]
    nlinarith [htail 0]
  have hdeficitZeroUpper :
      quadraticAnchorDeficit T c 0 ≤ 3 / 5 := by
    unfold quadraticAnchorDeficit
    rw [htotalTwo, htotalZero]
    nlinarith [htail 2]
  have hdeficitOneLower :
      9 / 20 ≤ quadraticAnchorDeficit T c 1 := by
    unfold quadraticAnchorDeficit
    rw [htotalTwo, htotalOne]
    nlinarith [htail 1]
  have hdeficitOneUpper :
      quadraticAnchorDeficit T c 1 ≤ 3 / 5 := by
    unfold quadraticAnchorDeficit
    rw [htotalTwo, htotalOne]
    nlinarith [htail 2]
  have hdepth :
      depthCoordinate 75 ≤ (9 / 20 : ℝ) := by
    unfold depthCoordinate
    exact exp_neg_seventyFive_lt.le.trans (by norm_num)
  have hrawZero :
      quadraticAnchorRawCarrier T η c 0 ⊆
        quadraticShallowCarrier T :=
    (quadraticAnchorRawCarrier_subset_shallow
      (hdepth.trans hdeficitZeroLower)).trans hreservoirSubset
  have hrawOne :
      quadraticAnchorRawCarrier T η c 1 ⊆
        quadraticShallowCarrier T :=
    (quadraticAnchorRawCarrier_subset_shallow
      (hdepth.trans hdeficitOneLower)).trans hreservoirSubset
  have hsuccess :
      fiveIndexedCarrierProfileFailure
          (quadraticProfilePrimeBand T)
          (quadraticDelayedProfileChecks T H)
          (quadraticDelayedProfileCarrier T)
          quadraticDelayedProfileThreshold c = false := by
    rw [← quadraticDelayedProfileFailure_extend_restriction T H c]
    simpa only [quadraticDeepProfileFailure] using hprofile
  refine
    { shallowFree := ?_
      centerLower := hcenterLower
      centerUpper := hcenterUpper
      deficitZeroLower := hdeficitZeroLower
      deficitZeroUpper := hdeficitZeroUpper
      deficitOneLower := hdeficitOneLower
      deficitOneUpper := hdeficitOneUpper
      occupiedZero :=
        quadraticShallowSingleton_occupied_le_one
          hrestriction hrawZero
      occupiedOne :=
        quadraticShallowSingleton_occupied_le_one
          hrestriction hrawOne
      profile :=
        quadraticDelayedProfileSuccess_prefix hTpos hsuccess }
  intro p hp
  let p' : QuadraticShallowIndex T :=
    ⟨p, hreservoirSubset hp⟩
  have hpvalue := congrFun hrestriction p'
  by_cases hpq : p' = q
  · have hppetaltwo : c p = petalLabel (2 : Fin 3) := by
      have hpUnderlying : p = q.1 :=
        congrArg Subtype.val hpq
      have hqvalue := congrFun hrestriction q
      have hqpetal :
          c q.1 = petalLabel (2 : Fin 3) := by
        simpa [singletonFiveConfiguration] using hqvalue
      exact (congrArg c hpUnderlying).trans hqpetal
    rw [hppetaltwo]
    constructor <;> decide
  · have hpzero : c p = 0 := by
      simpa [p', singletonFiveConfiguration,
        emptyFiveConfiguration, hpq] using hpvalue
    rw [hpzero]
    constructor <;> decide

/-- Every configuration in the concrete Base is an admissible adaptive
background, eventually and uniformly in the profile horizon. -/
theorem eventually_quadraticConcreteAnchorBackgroundGood
    (H : ℕ → ℕ) (η : ℝ) :
    ∀ᶠ T : ℕ in atTop,
      ∀ c ∈
          quadraticAnchorBase T
            (QuadraticDeepBackgroundGood T (H T)),
        QuadraticAnchorBackgroundGood T (H T) η c := by
  filter_upwards [eventually_ge_atTop 10] with T hT
  intro c hc
  have hdeep :=
    (mem_quadraticAnchorBase.mp hc).2
  exact quadraticAnchorBackgroundGood_of_base
    hT hc hdeep.1 hdeep.2

/-- Fully concrete first-moment package on the quadratic band.  The
profile horizon may vary arbitrarily with the scale. -/
theorem eventually_quadraticConcreteAnchorFirstMomentPackage
    {η : ℝ} (hη : 0 < η) (H : ℕ → ℕ) :
    ∀ᶠ T : ℕ in atTop,
      0 < quadraticAnchorWidth T η ∧
        FiveEventHasPetals
          (quadraticProfilePrimeBand T)
          (quadraticAnchorEvent T (H T) η) ∧
        FiveEventPetalLogBalanced
          (quadraticProfilePrimeBand T)
          (quadraticAnchorEvent T (H T) η) η ∧
        (quadraticConcreteAnchorBaseMassLower *
              (1 / 400 : ℝ) ^ 2 / 4) *
            quadraticAnchorWidth T η ^ 2 ≤
          fiveEventMass (quadraticProfilePrimeBand T)
            reciprocalBernoulli
            (quadraticAnchorEvent T (H T) η) := by
  have hbaseAll :=
    eventually_quadraticConcreteAnchorBase_compatibleMass_lower
  have hbase :
      ∀ᶠ T : ℕ in atTop,
        quadraticConcreteAnchorBaseMassLower ≤
          ∑ c ∈ quadraticConcreteAnchorBase T (H T),
            poissonCompatibleConfigurationWeight
              (quadraticProfilePrimeBand T) reciprocalBernoulli c := by
    filter_upwards [hbaseAll] with T hbaseT
    exact hbaseT (H T)
  have hgood :=
    eventually_quadraticConcreteAnchorBackgroundGood H η
  exact
    eventually_quadraticAnchorFirstMomentPackage_of_base
      hη quadraticConcreteAnchorBaseMassLower_pos H
      (fun T ↦ quadraticConcreteAnchorBase T (H T))
      hbase
      (by
        simpa only [quadraticConcreteAnchorBase] using hgood)

end Erdos536
