import Erdos536.FinitePiProbability
import Erdos536.PrimeBandAdaptiveAnchors
import Erdos536.PrimeBandProfileConcrete
import Erdos536.QuadraticPrimeBandBase
import Erdos536.QuadraticPrimeBandTail

set_option maxHeartbeats 800000

/-!
# A positive background event for the quadratic two-anchor construction

The shallow coordinates carry exactly one fixed-label atom in a small
depth cell.  All remaining restrictions are imposed on the complementary
coordinates.  This file keeps the product split explicit, so that the
shallow atom contributes a fixed positive factor independently of the
growing delayed profile.
-/

open scoped BigOperators
open Finset Filter Topology

noncomputable section

namespace Erdos536

open PrimeSums
open PrimeBandTimeChange

/-- The fixed shallow part of the quadratic band. -/
def quadraticShallowCarrier (T : ℕ) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  quadraticDepthBandCarrier T 0 76

/-- A fixed positive-length cell containing the background `z` anchor. -/
def quadraticBackgroundAnchorCarrier (T : ℕ) :
    Finset ↥(quadraticProfilePrimeBand T) :=
  quadraticDepthBandCarrier T (7 / 10) (3 / 4)

/-- The predicate used for the shallow/deep product split.  Keeping it as
a named predicate also gives both sides of the split the same canonical
finite subtype instance. -/
def quadraticShallowPred
    (T : ℕ) (p : ↥(quadraticProfilePrimeBand T)) : Prop :=
  p ∈ quadraticShallowCarrier T

local instance (T : ℕ) :
    DecidablePred (quadraticShallowPred T) :=
  fun p ↦ inferInstanceAs (Decidable (p ∈ quadraticShallowCarrier T))

abbrev QuadraticShallowIndex (T : ℕ) :=
  {p : ↥(quadraticProfilePrimeBand T) //
    quadraticShallowPred T p}

abbrev QuadraticDeepIndex (T : ℕ) :=
  {p : ↥(quadraticProfilePrimeBand T) //
    ¬ quadraticShallowPred T p}

/-- The fixed anchor cell lies in the shallow carrier. -/
theorem quadraticBackgroundAnchorCarrier_subset_shallow (T : ℕ) :
    quadraticBackgroundAnchorCarrier T ⊆
      quadraticShallowCarrier T := by
  exact quadraticDepthBandCarrier_mono
    (show (0 : ℝ) ≤ 7 / 10 by norm_num)
    (show (3 / 4 : ℝ) ≤ 76 by norm_num)

/-- Embed the attached fixed anchor cell in the shallow-coordinate type. -/
def quadraticBackgroundAnchorEmbedding (T : ℕ) :
    ↥(quadraticBackgroundAnchorCarrier T) ↪
      QuadraticShallowIndex T where
  toFun p :=
    ⟨p.1,
      quadraticBackgroundAnchorCarrier_subset_shallow T p.2⟩
  inj' := by
    intro p q h
    apply Subtype.ext
    exact congrArg (fun x : QuadraticShallowIndex T ↦ x.1) h

/-- The anchor cell, regarded as a finset of shallow coordinates. -/
def quadraticBackgroundAnchorShallowCarrier (T : ℕ) :
    Finset (QuadraticShallowIndex T) :=
  (quadraticBackgroundAnchorCarrier T).attach.map
    (quadraticBackgroundAnchorEmbedding T)

@[simp]
theorem mem_quadraticBackgroundAnchorShallowCarrier
    {T : ℕ} {p : QuadraticShallowIndex T} :
    p ∈ quadraticBackgroundAnchorShallowCarrier T ↔
      p.1 ∈ quadraticBackgroundAnchorCarrier T := by
  classical
  constructor
  · intro hp
    rw [quadraticBackgroundAnchorShallowCarrier,
      Finset.mem_map] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    have hqA : q.1 ∈ quadraticBackgroundAnchorCarrier T :=
      q.2
    simpa only [quadraticBackgroundAnchorEmbedding] using
      hqp ▸ hqA
  · intro hp
    let q : ↥(quadraticBackgroundAnchorCarrier T) := ⟨p.1, hp⟩
    refine Finset.mem_map.mpr ⟨q, by simp [q], ?_⟩
    exact Subtype.ext rfl

/-- Extend a configuration on the deep complement by the empty label on
the shallow carrier. -/
def extendQuadraticDeepConfiguration
    (T : ℕ) (v : QuadraticDeepIndex T → FiveLabel) :
    FiveConfiguration (quadraticProfilePrimeBand T) :=
  (Equiv.piEquivPiSubtypeProd
      (fun p : ↥(quadraticProfilePrimeBand T) ↦
        quadraticShallowPred T p)
      (fun _ ↦ FiveLabel)).symm
    (fun _ ↦ 0, v)

@[simp]
theorem extendQuadraticDeepConfiguration_shallow
    {T : ℕ} (v : QuadraticDeepIndex T → FiveLabel)
    (p : QuadraticShallowIndex T) :
    extendQuadraticDeepConfiguration T v p.1 = 0 := by
  simp [extendQuadraticDeepConfiguration, p.2]

@[simp]
theorem extendQuadraticDeepConfiguration_deep
    {T : ℕ} (v : QuadraticDeepIndex T → FiveLabel)
    (p : QuadraticDeepIndex T) :
    extendQuadraticDeepConfiguration T v p.1 = v p := by
  simp [extendQuadraticDeepConfiguration, p.2]

/-- The complement of the rounded depth-`76` shallow band is eventually
strictly deeper than `75`.  The one-unit gap absorbs ceiling rounding. -/
theorem eventually_quadraticDeepIndex_depth_gt_75 :
    ∀ᶠ T : ℕ in atTop, ∀ p : QuadraticDeepIndex T,
      75 <
        normalizedLogDepth ((T ^ 2 : ℕ) : ℝ) p.1.1 := by
  have hcoordinate :
      0 < depthCoordinate 75 - depthCoordinate 76 := by
    unfold depthCoordinate
    rw [sub_pos, Real.exp_lt_exp]
    norm_num
  have hpowNat :
      Tendsto (fun T : ℕ => T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpowReal :
      Tendsto (fun T : ℕ => ((T ^ 2 : ℕ) : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  have hgap :
      Tendsto
        (fun T : ℕ =>
          ((T ^ 2 : ℕ) : ℝ) *
            (depthCoordinate 75 - depthCoordinate 76))
        atTop atTop := by
    have h :=
      hpowReal.const_mul_atTop hcoordinate
    simpa only [mul_comm] using h
  filter_upwards [
      hgap.eventually (eventually_gt_atTop 1),
      eventually_gt_atTop 0] with T hgapT hT
  intro p
  have hpBand := p.1.2
  have hp' := mem_quadraticProfilePrimeBand.mp hpBand
  have hN : 0 < T ^ 2 := pow_pos hT _
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by
    exact_mod_cast hN
  have hpEndpoint :
      p.1.1 ≤ expEndpoint (depthCoordinate 76) (T ^ 2) := by
    by_contra hnot
    have hlower :
        expEndpoint (depthCoordinate 76) (T ^ 2) < p.1.1 :=
      Nat.lt_of_not_ge hnot
    have hdepth :
        p.1.1 ∈ depthPrimeBand (T ^ 2) 0 76 := by
      rw [mem_depthPrimeBand]
      refine ⟨hp'.1, hlower, ?_⟩
      simpa [depthCoordinate] using hp'.2.2
    apply p.2
    simpa [quadraticShallowPred, quadraticShallowCarrier] using hdepth
  have hpR : (0 : ℝ) < p.1.1 := by
    exact_mod_cast hp'.1.pos
  have hpEndpointR :
      (p.1.1 : ℝ) ≤
        expEndpoint (depthCoordinate 76) (T ^ 2) := by
    exact_mod_cast hpEndpoint
  have hlogpEndpoint :
      Real.log (p.1.1 : ℝ) ≤
        Real.log
          (expEndpoint (depthCoordinate 76) (T ^ 2) : ℝ) :=
    Real.log_le_log hpR hpEndpointR
  have hlogEndpoint :
      Real.log
          (expEndpoint (depthCoordinate 76) (T ^ 2) : ℝ) <
        ((T ^ 2 : ℕ) : ℝ) * depthCoordinate 76 + 1 := by
    simpa only [LocalPrimeBand.localLowerEndpoint] using
      LocalPrimeBand.localLowerEndpoint_log_upper
        (T ^ 2) (show 0 ≤ depthCoordinate 76 by
          exact (depthCoordinate_pos 76).le)
  have hlogp :
      Real.log (p.1.1 : ℝ) <
        ((T ^ 2 : ℕ) : ℝ) * depthCoordinate 75 := by
    calc
      _ ≤ Real.log
          (expEndpoint (depthCoordinate 76) (T ^ 2) : ℝ) :=
        hlogpEndpoint
      _ < ((T ^ 2 : ℕ) : ℝ) * depthCoordinate 76 + 1 :=
        hlogEndpoint
      _ < ((T ^ 2 : ℕ) : ℝ) * depthCoordinate 75 := by
        nlinarith
  have hweight :
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1.1 <
        depthCoordinate 75 := by
    rw [normalizedLogWeight]
    apply (div_lt_iff₀ hNR).2
    simpa only [mul_comm] using hlogp
  have hlogpPos :
      0 < Real.log (p.1.1 : ℝ) :=
    Real.log_pos (by exact_mod_cast hp'.1.one_lt)
  have hweightPos :
      0 <
        normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1.1 := by
    rw [normalizedLogWeight]
    exact div_pos hlogpPos hNR
  have hlogweight :
      Real.log
          (normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1.1) <
        Real.log (depthCoordinate 75) :=
    Real.log_lt_log hweightPos hweight
  unfold normalizedLogDepth
  unfold depthCoordinate at hlogweight
  rw [Real.log_exp] at hlogweight
  linarith

/-! ## A direct finite-type compatible-law comparison -/

/-- Embed a direct finite function into the collapsed state space. -/
def embedDirectFiveConfiguration
    {ι : Type} (c : ι → FiveLabel) : ι → Option FiveLabel :=
  fun i ↦ some (c i)

theorem embedDirectFiveConfiguration_injective
    {ι : Type} :
    Function.Injective
      (embedDirectFiveConfiguration :
        (ι → FiveLabel) → (ι → Option FiveLabel)) := by
  intro c d h
  funext i
  simpa [embedDirectFiveConfiguration] using congrFun h i

def embedDirectFiveConfigurationEmbedding
    (ι : Type) :
    (ι → FiveLabel) ↪ (ι → Option FiveLabel) :=
  ⟨embedDirectFiveConfiguration,
    embedDirectFiveConfiguration_injective⟩

/-- An event on direct five-label functions, embedded in the normalized
collapsed product space. -/
noncomputable def directEmbeddedFiveEvent
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (D : (ι → FiveLabel) → Prop) [DecidablePred D] :
    Finset (ι → Option FiveLabel) :=
  (Finset.univ.filter D).map
    (embedDirectFiveConfigurationEmbedding ι)

theorem directEmbeddedFiveEvent_categoricalMass
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ)
    (D : (ι → FiveLabel) → Prop) [DecidablePred D] :
    (∑ x ∈ directEmbeddedFiveEvent D,
        finitePiWeight
          (fun i ↦ categoricalCellWeight (r i)) x) =
      ∑ c : ι → FiveLabel,
        if D c then ∏ i, fiveLabelWeight (r i) (c i) else 0 := by
  classical
  rw [directEmbeddedFiveEvent, Finset.sum_map]
  rw [← Finset.sum_filter]
  rfl

theorem directEmbeddedFiveEvent_compatibleMass
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ)
    (D : (ι → FiveLabel) → Prop) [DecidablePred D] :
    (∑ x ∈ directEmbeddedFiveEvent D,
        finitePiWeight
          (fun i ↦ collapsedPoissonCellWeight (r i)) x) =
      ∑ c : ι → FiveLabel,
        if D c then
          ∏ i, collapsedPoissonCellWeight (r i) (some (c i))
        else 0 := by
  classical
  rw [directEmbeddedFiveEvent, Finset.sum_map]
  rw [← Finset.sum_filter]
  rfl

/-- Total-variation comparison for an event on a direct finite function
space, without introducing an additional `Finset.univ` subtype. -/
theorem directFiveEvent_compatible_abs_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (r : ι → ℝ)
    (D : (ι → FiveLabel) → Prop) [DecidablePred D]
    (hr0 : ∀ i, 0 ≤ r i)
    (hr34 : ∀ i, r i ≤ 3 / 4) :
    |(∑ c : ι → FiveLabel,
          if D c then ∏ i, fiveLabelWeight (r i) (c i) else 0) -
        ∑ c : ι → FiveLabel,
          if D c then
            ∏ i, collapsedPoissonCellWeight (r i) (some (c i))
          else 0| ≤
      16 * ∑ i, (r i / 3) ^ 2 := by
  classical
  have hμsum :
      ∀ i : ι,
        ∑ x : Option FiveLabel,
          categoricalCellWeight (r i) x = 1 :=
    fun i ↦ sum_categoricalCellWeight (r i)
  have hνsum :
      ∀ i : ι,
        ∑ x : Option FiveLabel,
          collapsedPoissonCellWeight (r i) x = 1 :=
    fun i ↦ sum_collapsedPoissonCellWeight (r i)
  have hmain :=
    finitePiEvent_abs_sub_le_half_sum
      (ι := ι) (Ω := Option FiveLabel)
      (directEmbeddedFiveEvent D)
      (fun i ↦ categoricalCellWeight (r i))
      (fun i ↦ collapsedPoissonCellWeight (r i))
      (fun i x ↦ categoricalCellWeight_nonneg
        (hr0 i) (hr34 i) x)
      (fun i x ↦ collapsedPoissonCellWeight_nonneg
        (hr0 i) x)
      hμsum hνsum
  rw [directEmbeddedFiveEvent_categoricalMass,
    directEmbeddedFiveEvent_compatibleMass] at hmain
  calc
    _ ≤ (1 / 2 : ℝ) *
        ∑ i, ∑ x,
          |categoricalCellWeight (r i) x -
            collapsedPoissonCellWeight (r i) x| := hmain
    _ ≤ (1 / 2 : ℝ) *
        ∑ i, 32 * (r i / 3) ^ 2 := by
      gcongr with i
      exact cell_l1_le (hr0 i)
    _ = 16 * ∑ i, (r i / 3) ^ 2 := by
      rw [← Finset.mul_sum]
      ring

/-! ## Delayed profiles on the deep complement -/

/-- Every delayed-profile carrier is disjoint from the shallow
depth-`76` carrier, with no asymptotic rounding condition. -/
theorem quadraticDelayedProfileCarrier_not_shallow
    {T k : ℕ} {p : ↥(quadraticProfilePrimeBand T)}
    (hp : p ∈ quadraticDelayedProfileCarrier T k) :
    ¬ quadraticShallowPred T p := by
  intro hshallow
  have hpDeep :=
    mem_depthPrimeBand.mp
      (mem_quadraticDepthBandCarrier.mp hp)
  have hpShallow :=
    mem_depthPrimeBand.mp
      (mem_quadraticDepthBandCarrier.mp
        (show p ∈ quadraticShallowCarrier T by
          exact hshallow))
  omega

/-- Restricting a configuration to the deep complement and extending it
by zero does not alter any delayed carrier count. -/
theorem fiveActiveLabelCountOn_extendQuadraticDeep_restriction
    (T k : ℕ)
    (c : FiveConfiguration (quadraticProfilePrimeBand T))
    (l : ActiveFiveLabel) :
    fiveActiveLabelCountOn
        (quadraticDelayedProfileCarrier T k) l
        (extendQuadraticDeepConfiguration T
          (fun p : QuadraticDeepIndex T ↦ c p.1)) =
      fiveActiveLabelCountOn
        (quadraticDelayedProfileCarrier T k) l c := by
  classical
  unfold fiveActiveLabelCountOn
  congr 1
  ext p
  simp only [Finset.mem_filter]
  by_cases hp :
      p ∈ quadraticDelayedProfileCarrier T k
  · have hpDeep :
        ¬ quadraticShallowPred T p :=
      quadraticDelayedProfileCarrier_not_shallow hp
    let q : QuadraticDeepIndex T := ⟨p, hpDeep⟩
    have heq :
        extendQuadraticDeepConfiguration T
            (fun a : QuadraticDeepIndex T ↦ c a.1) p =
          c p := by
      simpa only [q] using
        (extendQuadraticDeepConfiguration_deep
          (T := T)
          (fun a : QuadraticDeepIndex T ↦ c a.1) q)
    simp [hp, heq]
  · simp [hp]

/-- The delayed-profile failure Boolean depends only on the deep
restriction. -/
theorem quadraticDelayedProfileFailure_extend_restriction
    (T H : ℕ)
    (c : FiveConfiguration (quadraticProfilePrimeBand T)) :
    fiveIndexedCarrierProfileFailure
        (quadraticProfilePrimeBand T)
        (quadraticDelayedProfileChecks T H)
        (quadraticDelayedProfileCarrier T)
        quadraticDelayedProfileThreshold
        (extendQuadraticDeepConfiguration T
          (fun p : QuadraticDeepIndex T ↦ c p.1)) =
      fiveIndexedCarrierProfileFailure
        (quadraticProfilePrimeBand T)
        (quadraticDelayedProfileChecks T H)
        (quadraticDelayedProfileCarrier T)
        quadraticDelayedProfileThreshold c := by
  apply Bool.eq_iff_iff.mpr
  simp only [fiveIndexedCarrierProfileFailure_iff]
  constructor
  · rintro ⟨l, k, hk, hcount⟩
    refine ⟨l, k, hk, ?_⟩
    simpa only [
      fiveActiveLabelCountOn_extendQuadraticDeep_restriction
        T k c l] using hcount
  · rintro ⟨l, k, hk, hcount⟩
    refine ⟨l, k, hk, ?_⟩
    simpa only [
      fiveActiveLabelCountOn_extendQuadraticDeep_restriction
        T k c l] using hcount

/-- Delayed-profile failure, expressed directly on the deep-coordinate
function space. -/
noncomputable def quadraticDeepProfileFailure
    (T H : ℕ) (v : QuadraticDeepIndex T → FiveLabel) : Bool :=
  fiveIndexedCarrierProfileFailure
    (quadraticProfilePrimeBand T)
    (quadraticDelayedProfileChecks T H)
    (quadraticDelayedProfileCarrier T)
    quadraticDelayedProfileThreshold
    (extendQuadraticDeepConfiguration T v)

/-- The direct categorical mass of deep profile failure equals its
whole-band categorical mass. -/
theorem quadraticDeepProfileFailure_categoricalMass_eq
    (T H : ℕ) :
    (∑ v : QuadraticDeepIndex T → FiveLabel,
        if quadraticDeepProfileFailure T H v then
          ∏ p : QuadraticDeepIndex T,
            fiveLabelWeight (reciprocalBernoulli p.1.1) (v p)
        else 0) =
      fiveEventMass (quadraticProfilePrimeBand T)
        reciprocalBernoulli
        (fiveIndexedCarrierProfileFailure
          (quadraticProfilePrimeBand T)
          (quadraticDelayedProfileChecks T H)
          (quadraticDelayedProfileCarrier T)
          quadraticDelayedProfileThreshold) := by
  classical
  let μ : ↥(quadraticProfilePrimeBand T) → FiveLabel → ℝ :=
    fun p ↦ fiveLabelWeight (reciprocalBernoulli p.1)
  have hmass : ∀ p, ∑ l, μ p l = 1 :=
    fun p ↦ sum_fiveLabelWeight _
  have hmarg :=
    finitePiEventMass_complRestriction
      (quadraticShallowPred T) μ hmass
      (fun v : QuadraticDeepIndex T → FiveLabel ↦
        quadraticDeepProfileFailure T H v)
  rw [← hmarg]
  unfold fiveEventMass
  apply Finset.sum_congr rfl
  intro c _hc
  rw [quadraticDeepProfileFailure,
    quadraticDelayedProfileFailure_extend_restriction T H c]
  rfl

/-! ## Weighted petal tails on the deep complement -/

/-- The underlying natural-prime finset of the deep complement. -/
def quadraticDeepComplementPrimeBand (T : ℕ) : Finset ℕ :=
  (quadraticProfilePrimeBand T).filter fun p ↦
    p ∉ depthPrimeBand (T ^ 2) 0 76

@[simp]
theorem mem_quadraticDeepComplementPrimeBand
    {T p : ℕ} :
    p ∈ quadraticDeepComplementPrimeBand T ↔
      p ∈ quadraticProfilePrimeBand T ∧
        p ∉ depthPrimeBand (T ^ 2) 0 76 := by
  simp [quadraticDeepComplementPrimeBand]

/-- The rounded deep complement lies in the actual normalized depth-`75`
tail, eventually. -/
theorem eventually_quadraticDeepComplementPrimeBand_subset_tail :
    ∀ᶠ T : ℕ in atTop,
      quadraticDeepComplementPrimeBand T ⊆
        quadraticDeepPrimeBand T 1 75 := by
  filter_upwards [eventually_quadraticDeepIndex_depth_gt_75] with
      T hdepthT
  intro p hp
  have hp' := mem_quadraticDeepComplementPrimeBand.mp hp
  let q : ↥(quadraticProfilePrimeBand T) := ⟨p, hp'.1⟩
  have hqDeep : ¬ quadraticShallowPred T q := by
    simpa [quadraticShallowPred, quadraticShallowCarrier] using hp'.2
  let d : QuadraticDeepIndex T := ⟨q, hqDeep⟩
  rw [mem_quadraticDeepPrimeBand]
  exact ⟨by simpa [quadraticProfilePrimeBand] using hp'.1,
    by simpa [d, q] using hdepthT d⟩

/-- Direct normalized weight carried by one petal on the deep
coordinates. -/
noncomputable def quadraticDeepPetalTotal
    (T : ℕ) (s : Fin 3)
    (v : QuadraticDeepIndex T → FiveLabel) : ℝ :=
  ∑ p : QuadraticDeepIndex T,
    if v p = petalLabel s then
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1.1
    else 0

theorem quadraticDeepPetalTotal_nonneg
    {T : ℕ} (hT : 0 < T) (s : Fin 3)
    (v : QuadraticDeepIndex T → FiveLabel) :
    0 ≤ quadraticDeepPetalTotal T s v := by
  unfold quadraticDeepPetalTotal
  apply Finset.sum_nonneg
  intro p _hp
  split_ifs
  · have hpPrime :=
      (mem_quadraticProfilePrimeBand.mp p.1.2).1
    unfold normalizedLogWeight
    exact div_nonneg
      (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
      (by positivity)
  · norm_num

/-- The full weighted total of a deep extension is its direct deep total. -/
theorem fiveLabelWeightedTotal_extendQuadraticDeep_eq
    {T : ℕ} (v : QuadraticDeepIndex T → FiveLabel)
    (s : Fin 3) :
    fiveLabelWeightedTotal
        (quadraticProfilePrimeBand T)
        (normalizedLogWeight ((T ^ 2 : ℕ) : ℝ))
        (petalLabel s)
        (extendQuadraticDeepConfiguration T v) =
      quadraticDeepPetalTotal T s v := by
  let f : ↥(quadraticProfilePrimeBand T) → ℝ :=
    fun p ↦
      if extendQuadraticDeepConfiguration T v p = petalLabel s
      then normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p.1
      else 0
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (quadraticShallowPred T) f
  have hshallow :
      (∑ p : QuadraticShallowIndex T, f p.1) = 0 := by
    apply Finset.sum_eq_zero
    intro p _hp
    simp [f, extendQuadraticDeepConfiguration_shallow,
      show (0 : FiveLabel) ≠ petalLabel s by
        fin_cases s <;> decide]
  have hdeep :
      (∑ p : QuadraticDeepIndex T, f p.1) =
        quadraticDeepPetalTotal T s v := by
    unfold quadraticDeepPetalTotal
    apply Finset.sum_congr rfl
    intro p _hp
    simp only [f, extendQuadraticDeepConfiguration_deep]
  unfold fiveLabelWeightedTotal
  change (∑ p, f p) = _
  rw [← hsplit, hshallow, zero_add, hdeep]

/-- Reindex any natural-prime sum on the deep subtype as a sum over the
underlying complementary prime finset. -/
theorem sum_quadraticDeepIndex_eq_complement
    (T : ℕ) (f : ℕ → ℝ) :
    (∑ p : QuadraticDeepIndex T, f p.1.1) =
      ∑ p ∈ quadraticDeepComplementPrimeBand T, f p := by
  classical
  let g : ↥(quadraticProfilePrimeBand T) → ℝ :=
    fun p ↦ f p.1
  have hs :=
    Finset.sum_subtype
      (p := fun p : ↥(quadraticProfilePrimeBand T) ↦
        ¬ quadraticShallowPred T p)
      (F := inferInstanceAs (Fintype (QuadraticDeepIndex T)))
      ((Finset.univ :
        Finset ↥(quadraticProfilePrimeBand T)).filter
          fun p ↦ ¬ quadraticShallowPred T p)
      (fun p ↦ by simp)
      g
  have hs' :
      (∑ p : ↥(quadraticProfilePrimeBand T),
          if ¬ quadraticShallowPred T p then g p else 0) =
        ∑ p : QuadraticDeepIndex T, g p.1 := by
    simpa only [Finset.sum_filter, Finset.sum_const_zero,
      Finset.sum_add_distrib] using hs
  rw [← hs']
  unfold quadraticDeepComplementPrimeBand
  rw [Finset.sum_filter]
  conv_rhs => rw [← Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro p _hp
  simp only [g]
  congr 1
  simp [quadraticShallowPred, quadraticShallowCarrier,
    quadraticDepthBandCarrier]

/-- The normalized weight function supported on the deep complement. -/
noncomputable def quadraticDeepWeight
    (T : ℕ) (p : ℕ) : ℝ :=
  if p ∈ quadraticDeepComplementPrimeBand T
  then normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p
  else 0

/-- A full-band weighted total with the deep-supported weight is exactly
the direct deep petal total of the restricted configuration. -/
theorem fiveLabelWeightedTotal_quadraticDeepWeight_eq
    (T : ℕ)
    (c : FiveConfiguration (quadraticProfilePrimeBand T))
    (s : Fin 3) :
    fiveLabelWeightedTotal
        (quadraticProfilePrimeBand T)
        (quadraticDeepWeight T)
        (petalLabel s) c =
      quadraticDeepPetalTotal T s
        (fun p : QuadraticDeepIndex T ↦ c p.1) := by
  let f : ↥(quadraticProfilePrimeBand T) → ℝ :=
    fun p ↦
      if c p = petalLabel s then quadraticDeepWeight T p.1 else 0
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype
      (quadraticShallowPred T) f
  have hshallow :
      (∑ p : QuadraticShallowIndex T, f p.1) = 0 := by
    apply Finset.sum_eq_zero
    intro p _hp
    have hnot :
        p.1.1 ∉ quadraticDeepComplementPrimeBand T := by
      intro hdeep
      have hdeep' :=
        (mem_quadraticDeepComplementPrimeBand.mp hdeep).2
      apply hdeep'
      apply mem_quadraticDepthBandCarrier.mp
      exact p.2
    simp only [f]
    split_ifs
    · rw [quadraticDeepWeight, if_neg hnot]
    · rfl
  have hdeep :
      (∑ p : QuadraticDeepIndex T, f p.1) =
        quadraticDeepPetalTotal T s
          (fun p : QuadraticDeepIndex T ↦ c p.1) := by
    unfold quadraticDeepPetalTotal
    apply Finset.sum_congr rfl
    intro p _hp
    have hpMem :
        p.1.1 ∈ quadraticDeepComplementPrimeBand T := by
      rw [mem_quadraticDeepComplementPrimeBand]
      refine ⟨p.1.2, ?_⟩
      intro hdepth
      apply p.2
      apply mem_quadraticDepthBandCarrier.mpr
      exact hdepth
    simp only [f]
    split_ifs
    · rw [quadraticDeepWeight, if_pos hpMem]
    · rfl
  unfold fiveLabelWeightedTotal
  change (∑ p, f p) = _
  rw [← hsplit, hshallow, zero_add, hdeep]

/-- Expected one-label deep normalized weight. -/
noncomputable def quadraticDeepComplementOneLabelMean
    (T : ℕ) : ℝ :=
  ∑ p ∈ quadraticDeepComplementPrimeBand T,
    reciprocalBernoulli p / 3 *
      normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p

theorem eventually_quadraticDeepComplementOneLabelMean_le :
    ∀ᶠ T : ℕ in atTop,
      quadraticDeepComplementOneLabelMean T ≤
        1 / 15000 := by
  filter_upwards [
    eventually_quadraticDeepComplementPrimeBand_subset_tail,
    eventually_quadraticDeepOneLabelMean_le_one_div_fifteenThousand
      (1 : ℝ)] with T hsubset htail
  unfold quadraticDeepComplementOneLabelMean
  calc
    (∑ p ∈ quadraticDeepComplementPrimeBand T,
        reciprocalBernoulli p / 3 *
          normalizedLogWeight ((T ^ 2 : ℕ) : ℝ) p) ≤
      quadraticDeepOneLabelMean T 1 75 := by
        unfold quadraticDeepOneLabelMean
        apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
        intro p hp _hp'
        have hpPrime :=
          (mem_quadraticDeepPrimeBand.mp hp).1
        have hlog :
            0 ≤ Real.log (p : ℝ) :=
          Real.log_nonneg (by
            exact_mod_cast
              (mem_quadraticPrimeBand.mp hpPrime).1.one_le)
        unfold normalizedLogWeight
        exact mul_nonneg
          (div_nonneg (reciprocalBernoulli_nonneg p) (by norm_num))
          (div_nonneg hlog (Nat.cast_nonneg _))
    _ ≤ 1 / 15000 := htail

/-- The categorical first moment of the deep-supported weighted total is
the complementary one-label mean. -/
theorem quadraticDeepWeight_categoricalFirstMoment
    (T : ℕ) (s : Fin 3) :
    (∑ p : ↥(quadraticProfilePrimeBand T),
        fiveLabelWeight (reciprocalBernoulli p.1) (petalLabel s) *
          quadraticDeepWeight T p.1) =
      quadraticDeepComplementOneLabelMean T := by
  rw [Finset.sum_coe_sort
    (quadraticProfilePrimeBand T)
    (fun p : ℕ ↦
      fiveLabelWeight (reciprocalBernoulli p) (petalLabel s) *
        quadraticDeepWeight T p)]
  unfold quadraticDeepComplementOneLabelMean
  symm
  apply Finset.sum_subset_zero_on_sdiff
    (Finset.filter_subset _ _)
  · intro p hp
    have hpNot : p ∉ quadraticDeepComplementPrimeBand T :=
      (Finset.mem_sdiff.mp hp).2
    rw [quadraticDeepWeight, if_neg hpNot]
    ring
  · intro p hp
    have hpDeep :
        p ∈ quadraticDeepComplementPrimeBand T :=
      by simpa [quadraticDeepComplementPrimeBand] using hp
    rw [quadraticDeepWeight, if_pos hpDeep]
    fin_cases s <;> rfl

/-- A direct deep-petal upper tail has categorical mass at most `1/150`,
eventually, uniformly in the petal. -/
theorem eventually_quadraticDeepPetalFailure_categoricalMass_le :
    ∀ᶠ T : ℕ in atTop, ∀ s : Fin 3,
      (∑ v : QuadraticDeepIndex T → FiveLabel,
          if (1 / 100 : ℝ) < quadraticDeepPetalTotal T s v then
            ∏ p : QuadraticDeepIndex T,
              fiveLabelWeight (reciprocalBernoulli p.1.1) (v p)
          else 0) ≤
        1 / 150 := by
  filter_upwards [
    eventually_quadraticDeepComplementOneLabelMean_le,
    eventually_ge_atTop 1] with T hmean hT
  intro s
  let μ : ↥(quadraticProfilePrimeBand T) → FiveLabel → ℝ :=
    fun p ↦ fiveLabelWeight (reciprocalBernoulli p.1)
  have hmass : ∀ p, ∑ l, μ p l = 1 :=
    fun p ↦ sum_fiveLabelWeight _
  have hmarg :=
    finitePiEventMass_complRestriction
      (quadraticShallowPred T) μ hmass
      (fun v : QuadraticDeepIndex T → FiveLabel ↦
        (1 / 100 : ℝ) < quadraticDeepPetalTotal T s v)
  have hmarkov :=
    fiveLabelWeightedTotal_failureMass_le
      (quadraticProfilePrimeBand T)
      reciprocalBernoulli (quadraticDeepWeight T)
      (petalLabel s)
      (show (0 : ℝ) < 1 / 100 by norm_num)
      (fun p _hp ↦ reciprocalBernoulli_nonneg p)
      (fun p hp ↦ reciprocalBernoulli_le_three_quarters
        (quadraticPrimeBand_prime T 1 p hp).one_le)
      (fun p hp ↦ by
        unfold quadraticDeepWeight
        split_ifs
        · have hpPrime :=
            (mem_quadraticProfilePrimeBand.mp hp).1
          unfold normalizedLogWeight
          exact div_nonneg
            (Real.log_nonneg (by exact_mod_cast hpPrime.one_le))
            (by positivity)
        · norm_num)
  rw [quadraticDeepWeight_categoricalFirstMoment T s] at hmarkov
  have hfull :
      (∑ c : FiveConfiguration (quadraticProfilePrimeBand T),
          if
            (1 / 100 : ℝ) <
              quadraticDeepPetalTotal T s
                (fun p : QuadraticDeepIndex T ↦ c p.1)
          then fiveConfigurationWeight
            (quadraticProfilePrimeBand T) reciprocalBernoulli c
          else 0) ≤
        quadraticDeepComplementOneLabelMean T / (1 / 100) := by
    calc
      _ =
          ∑ c : FiveConfiguration (quadraticProfilePrimeBand T),
            if
              (1 / 100 : ℝ) <
                fiveLabelWeightedTotal
                  (quadraticProfilePrimeBand T)
                  (quadraticDeepWeight T)
                  (petalLabel s) c
            then fiveConfigurationWeight
              (quadraticProfilePrimeBand T) reciprocalBernoulli c
            else 0 := by
              apply Finset.sum_congr rfl
              intro c _hc
              rw [fiveLabelWeightedTotal_quadraticDeepWeight_eq]
      _ ≤ _ := hmarkov
  rw [← hmarg]
  calc
    _ ≤ quadraticDeepComplementOneLabelMean T / (1 / 100) := by
      simpa [μ, finitePiWeight, fiveConfigurationWeight] using hfull
    _ ≤ (1 / 15000 : ℝ) / (1 / 100) :=
      div_le_div_of_nonneg_right hmean (by norm_num)
    _ = 1 / 150 := by norm_num

/-- Exactly one shallow `z` atom, in the fixed anchor cell. -/
abbrev QuadraticShallowAnchorEvent
    (T : ℕ) (u : QuadraticShallowIndex T → FiveLabel) : Prop :=
  u ∈ singletonFiveConfigurations
    (quadraticBackgroundAnchorShallowCarrier T) (petalLabel 2)

/-- A generic product background event: the shallow part is the fixed
singleton anchor and the complementary restriction satisfies `D`. -/
def quadraticAnchorBase
    (T : ℕ) (D : (QuadraticDeepIndex T → FiveLabel) → Prop)
    [DecidablePred D] :
    Finset (FiveConfiguration (quadraticProfilePrimeBand T)) :=
  by
    classical
    exact Finset.univ.filter fun c ↦
      QuadraticShallowAnchorEvent T (fun p ↦ c p.1) ∧
        D (fun p ↦ c p.1)

@[simp]
theorem mem_quadraticAnchorBase
    {T : ℕ} {D : (QuadraticDeepIndex T → FiveLabel) → Prop}
    [DecidablePred D]
    {c : FiveConfiguration (quadraticProfilePrimeBand T)} :
    c ∈ quadraticAnchorBase T D ↔
      QuadraticShallowAnchorEvent T (fun p ↦ c p.1) ∧
        D (fun p ↦ c p.1) := by
  simp [quadraticAnchorBase]

/-- Exact independence of the shallow singleton and an arbitrary event on
the deep complement under the compatible product weights. -/
theorem quadraticAnchorBase_compatibleMass_eq
    (T : ℕ) (D : (QuadraticDeepIndex T → FiveLabel) → Prop)
    [DecidablePred D] :
    (∑ c ∈ quadraticAnchorBase T D,
        poissonCompatibleConfigurationWeight
          (quadraticProfilePrimeBand T) reciprocalBernoulli c) =
      (∑ u : QuadraticShallowIndex T → FiveLabel,
          if QuadraticShallowAnchorEvent T u then
            ∏ p : QuadraticShallowIndex T,
              collapsedPoissonCellWeight
                (reciprocalBernoulli p.1.1) (some (u p))
          else 0) *
        ∑ v : QuadraticDeepIndex T → FiveLabel,
          if D v then
            ∏ p : QuadraticDeepIndex T,
              collapsedPoissonCellWeight
                (reciprocalBernoulli p.1.1) (some (v p))
          else 0 := by
  classical
  let μ : ↥(quadraticProfilePrimeBand T) → FiveLabel → ℝ :=
    fun p l ↦ collapsedPoissonCellWeight
      (reciprocalBernoulli p.1) (some l)
  have hsplit :=
    finitePiEventMass_split
      (fun p : ↥(quadraticProfilePrimeBand T) ↦
        quadraticShallowPred T p)
      μ
      (QuadraticShallowAnchorEvent T) D
  have hsplit' :
      (∑ x : FiveConfiguration (quadraticProfilePrimeBand T),
          if
            QuadraticShallowAnchorEvent T (fun p ↦ x p.1) ∧
              D (fun p ↦ x p.1)
          then
            poissonCompatibleConfigurationWeight
              (quadraticProfilePrimeBand T) reciprocalBernoulli x
          else 0) =
        (∑ u : QuadraticShallowIndex T → FiveLabel,
            if QuadraticShallowAnchorEvent T u then
              ∏ p : QuadraticShallowIndex T,
                collapsedPoissonCellWeight
                  (reciprocalBernoulli p.1.1) (some (u p))
            else 0) *
          ∑ v : QuadraticDeepIndex T → FiveLabel,
            if D v then
              ∏ p : QuadraticDeepIndex T,
                collapsedPoissonCellWeight
                  (reciprocalBernoulli p.1.1) (some (v p))
            else 0 := by
    simpa [μ, finitePiWeight,
      poissonCompatibleConfigurationWeight] using hsplit
  calc
    (∑ c ∈ quadraticAnchorBase T D,
        poissonCompatibleConfigurationWeight
          (quadraticProfilePrimeBand T) reciprocalBernoulli c) =
      ∑ x : FiveConfiguration (quadraticProfilePrimeBand T),
        if
          QuadraticShallowAnchorEvent T (fun p ↦ x p.1) ∧
            D (fun p ↦ x p.1)
        then
          poissonCompatibleConfigurationWeight
            (quadraticProfilePrimeBand T) reciprocalBernoulli x
        else 0 := by
      rw [quadraticAnchorBase, Finset.sum_filter]
    _ = _ := hsplit'

/-- The shallow compatible mass has the closed singleton formula. -/
theorem quadraticShallowAnchorMass_eq (T : ℕ) :
    (∑ u : QuadraticShallowIndex T → FiveLabel,
        if QuadraticShallowAnchorEvent T u then
          ∏ p : QuadraticShallowIndex T,
            collapsedPoissonCellWeight
              (reciprocalBernoulli p.1.1) (some (u p))
        else 0) =
      Real.exp
          (-(4 *
            ∑ p : QuadraticShallowIndex T,
              reciprocalBernoulli p.1.1 / 3)) *
        ∑ p ∈ quadraticBackgroundAnchorShallowCarrier T,
          reciprocalBernoulli p.1.1 / 3 := by
  classical
  have hfilter :
    (∑ u : QuadraticShallowIndex T → FiveLabel,
        if QuadraticShallowAnchorEvent T u then
          ∏ p : QuadraticShallowIndex T,
            collapsedPoissonCellWeight
              (reciprocalBernoulli p.1.1) (some (u p))
        else 0) =
      ∑ u ∈ singletonFiveConfigurations
          (quadraticBackgroundAnchorShallowCarrier T)
          (petalLabel 2),
        ∏ p : QuadraticShallowIndex T,
          collapsedPoissonCellWeight
            (reciprocalBernoulli p.1.1) (some (u p)) := by
    change
      (∑ u : QuadraticShallowIndex T → FiveLabel,
          if u ∈ singletonFiveConfigurations
              (quadraticBackgroundAnchorShallowCarrier T)
              (petalLabel 2)
          then
            ∏ p : QuadraticShallowIndex T,
              collapsedPoissonCellWeight
                (reciprocalBernoulli p.1.1) (some (u p))
          else 0) =
        ∑ u ∈ singletonFiveConfigurations
            (quadraticBackgroundAnchorShallowCarrier T)
            (petalLabel 2),
          ∏ p : QuadraticShallowIndex T,
            collapsedPoissonCellWeight
              (reciprocalBernoulli p.1.1) (some (u p))
    exact Finset.sum_ite_mem_eq
      (singletonFiveConfigurations
        (quadraticBackgroundAnchorShallowCarrier T)
        (petalLabel 2))
      (fun u ↦
        ∏ p : QuadraticShallowIndex T,
          collapsedPoissonCellWeight
            (reciprocalBernoulli p.1.1) (some (u p)))
  rw [hfilter]
  simpa only using
    singletonFiveConfigurations_compatibleMass
    (fun p : QuadraticShallowIndex T ↦
      reciprocalBernoulli p.1.1)
    (quadraticBackgroundAnchorShallowCarrier T)
    (petalLabel 2) (by decide)

/-- Reindex the shallow subtype sum as the original carrier sum. -/
theorem sum_quadraticShallowIndex_reciprocal_third (T : ℕ) :
    (∑ p : QuadraticShallowIndex T,
        reciprocalBernoulli p.1.1 / 3) =
      ∑ p ∈ quadraticShallowCarrier T,
        reciprocalBernoulli p.1 / 3 := by
  symm
  simpa only [quadraticShallowPred] using
    (Finset.sum_subtype
      (quadraticShallowCarrier T)
      (fun _p ↦ Iff.rfl)
      (fun p : ↥(quadraticProfilePrimeBand T) ↦
        reciprocalBernoulli p.1 / 3))

/-- Reindex the shallow anchor-cell sum as the original depth-cell sum. -/
theorem sum_quadraticBackgroundAnchorShallowCarrier_reciprocal_third
    (T : ℕ) :
    (∑ p ∈ quadraticBackgroundAnchorShallowCarrier T,
        reciprocalBernoulli p.1.1 / 3) =
      ∑ p ∈ quadraticBackgroundAnchorCarrier T,
        reciprocalBernoulli p.1 / 3 := by
  classical
  rw [quadraticBackgroundAnchorShallowCarrier, Finset.sum_map]
  simpa only using
    (Finset.sum_attach
      (quadraticBackgroundAnchorCarrier T)
      (fun p : ↥(quadraticProfilePrimeBand T) ↦
        reciprocalBernoulli p.1 / 3))

/-- A fixed lower bound for the shallow compatible singleton mass. -/
def quadraticShallowAnchorMassLower : ℝ :=
  Real.exp (-104) / 120

theorem quadraticShallowAnchorMassLower_pos :
    0 < quadraticShallowAnchorMassLower := by
  unfold quadraticShallowAnchorMassLower
  positivity

/-- The shallow singleton event has a fixed positive compatible mass,
eventually in the quadratic scale. -/
theorem eventually_quadraticShallowAnchorMass_lower :
    ∀ᶠ T : ℕ in atTop,
      quadraticShallowAnchorMassLower ≤
        ∑ u : QuadraticShallowIndex T → FiveLabel,
          if QuadraticShallowAnchorEvent T u then
            ∏ p : QuadraticShallowIndex T,
              collapsedPoissonCellWeight
                (reciprocalBernoulli p.1.1) (some (u p))
          else 0 := by
  have hshallow :=
    eventually_quadraticDepthBandCarrier_intensity_lt
      (r := (0 : ℝ)) (s := (76 : ℝ))
      (ε := (2 / 3 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  have hanchor :=
    eventually_quadraticDepthBandCarrier_intensity_gt
      (r := (7 / 10 : ℝ)) (s := (3 / 4 : ℝ))
      (ε := (1 / 120 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
  filter_upwards [hshallow, hanchor] with T hshallowT hanchorT
  rw [quadraticShallowAnchorMass_eq,
    sum_quadraticShallowIndex_reciprocal_third,
    sum_quadraticBackgroundAnchorShallowCarrier_reciprocal_third]
  have htotal :
      (∑ p ∈ quadraticShallowCarrier T,
          reciprocalBernoulli p.1 / 3) ≤ 26 := by
    norm_num at hshallowT
    simpa [quadraticShallowCarrier] using hshallowT.le
  have hcell :
      (1 / 120 : ℝ) ≤
        ∑ p ∈ quadraticBackgroundAnchorCarrier T,
          reciprocalBernoulli p.1 / 3 := by
    have h := hanchorT.le
    norm_num [quadraticBackgroundAnchorCarrier] at h ⊢
    linarith
  have hexp :
      Real.exp (-104) ≤
        Real.exp
          (-(4 *
            ∑ p ∈ quadraticShallowCarrier T,
              reciprocalBernoulli p.1 / 3)) := by
    apply Real.exp_le_exp.mpr
    linarith
  unfold quadraticShallowAnchorMassLower
  have hnonneg : (0 : ℝ) ≤ 1 / 120 := by norm_num
  calc
    Real.exp (-104) / 120 =
        Real.exp (-104) * (1 / 120) := by ring
    _ ≤
        Real.exp
            (-(4 *
              ∑ p ∈ quadraticShallowCarrier T,
                reciprocalBernoulli p.1 / 3)) *
          ∑ p ∈ quadraticBackgroundAnchorCarrier T,
            reciprocalBernoulli p.1 / 3 :=
      mul_le_mul hexp hcell hnonneg (Real.exp_nonneg _)

/-- Combine the fixed shallow factor with any quantitative lower bound for
the compatible mass of the deep event. -/
theorem quadraticAnchorBase_compatibleMass_lower
    {T : ℕ} (D : (QuadraticDeepIndex T → FiveLabel) → Prop)
    [DecidablePred D] {d : ℝ}
    (hshallow :
      quadraticShallowAnchorMassLower ≤
        ∑ u : QuadraticShallowIndex T → FiveLabel,
          if QuadraticShallowAnchorEvent T u then
            ∏ p : QuadraticShallowIndex T,
              collapsedPoissonCellWeight
                (reciprocalBernoulli p.1.1) (some (u p))
          else 0)
    (hd0 : 0 ≤ d)
    (hdeep :
      d ≤
        ∑ v : QuadraticDeepIndex T → FiveLabel,
          if D v then
            ∏ p : QuadraticDeepIndex T,
              collapsedPoissonCellWeight
                (reciprocalBernoulli p.1.1) (some (v p))
          else 0) :
    quadraticShallowAnchorMassLower * d ≤
      ∑ c ∈ quadraticAnchorBase T D,
        poissonCompatibleConfigurationWeight
          (quadraticProfilePrimeBand T) reciprocalBernoulli c := by
  rw [quadraticAnchorBase_compatibleMass_eq]
  exact mul_le_mul hshallow hdeep hd0
    (quadraticShallowAnchorMassLower_pos.le.trans hshallow)

end Erdos536
