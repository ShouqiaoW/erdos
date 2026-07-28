import Erdos390.WholePaper.TangentCollisionLocalLemma
import Mathlib.Tactic

/-!
# Counting the tangent collision events

This file is the finite counting layer immediately before the local-lemma
module.  It does three things which are kept separate in the paper's prose.

* It proves that the product of the request-wise uniform laws is the uniform
  law on the finite dependent product.  Consequently an actual collision
  probability is exactly

  `number of colliding configurations / number of all configurations`.

* A two-request collision is covered by the four literal endpoint equations.
  For prime endpoint labels, the equation `p*a=q*b` has at most
  `N/p+1` solutions when `p=q`, and at most `N/(p*q)+1` solutions when
  `p != q`, provided the left endpoint is at most `N`.

* The incident-event sum for one request is reindexed exactly by all other
  requests.  A pairwise cardinality/counting estimate can therefore be
  summed using the two endpoint-label loads of the fixed request and the
  total request count.

No collision-free choice and no bound on a collision probability are assumed
here.  In the clean-list terminal the remaining inputs are request-wise list
cardinality lower bounds and an explicit arithmetic comparison of the finite
counting budget with the paper's shared-label and disjoint-label charges.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos390.WholePaper

noncomputable section

/-! ## The product law is uniform -/

/-- The uniform probability measure on an abstract nonempty finite type.
Keeping the carrier abstract here prevents later cardinality proofs from
unfolding the dependent request/list `Fintype` construction. -/
def tangentFiniteUniformMeasure (α : Type*) [MeasurableSpace α]
    [MeasurableSingletonClass α] [Finite α]
    (hα : Nonempty α) : Measure α := by
  letI : Fintype α := Fintype.ofFinite α
  letI : Nonempty α := hα
  exact (PMF.uniformOfFintype α).toMeasure

/-- Cardinality formula for the preceding abstract finite uniform law. -/
theorem tangentFiniteUniformMeasure_apply
    (α : Type*) [MeasurableSpace α] [MeasurableSingletonClass α]
    [Finite α] (hα : Nonempty α)
    (s : Set α) (hs : MeasurableSet s) :
    tangentFiniteUniformMeasure α hα s = Nat.card s / Nat.card α := by
  classical
  letI : Fintype α := Fintype.ofFinite α
  letI : Nonempty α := hα
  unfold tangentFiniteUniformMeasure
  calc
    (PMF.uniformOfFintype α).toMeasure s =
        Fintype.card s / Fintype.card α :=
      PMF.toMeasure_uniformOfFintype_apply s hs
    _ = Nat.card s / Nat.card α := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card]

/-- Uniform measure on the whole dependent product, with nonemptiness
installed from the request-wise list proofs. -/
def tangentUniformMultiplierOutcomeMeasure
    {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    Measure (TangentMultiplierOutcome lists) := by
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  exact tangentFiniteUniformMeasure
    (TangentMultiplierOutcome lists) inferInstance

/-- Uniform measure on the dependent product over a finite request support. -/
def tangentUniformMultiplierRestrictionMeasure
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (support : Finset Request) :
    Measure (∀ request : ↑support,
      TangentMultiplierChoice lists request.1) :=
  tangentUniformMultiplierOutcomeMeasure (Request := ↑support)
    (fun request : ↑support ↦ lists request.1)
    (fun request : ↑support ↦ hlist request.1)

/-- A finite product of nonempty uniform list laws is the uniform law on the
dependent product of the list subtypes. -/
theorem tangentUniformMultiplierMeasure_eq_uniformOfFintype
    {Request : Type*} [Fintype Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty) :
    tangentUniformMultiplierMeasure lists hlist =
      tangentUniformMultiplierOutcomeMeasure lists hlist := by
  classical
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  apply Measure.ext_of_singleton
  intro outcome
  unfold tangentUniformMultiplierMeasure
    tangentUniformMultiplierOutcomeMeasure tangentFiniteUniformMeasure
  rw [Measure.pi_singleton]
  simp_rw [PMF.toMeasure_apply_singleton _ _
    (measurableSet_singleton _)]
  simp_rw [PMF.uniformOfFintype_apply]
  simp_rw [Fintype.card_eq_nat_card]
  rw [Nat.card_pi]
  simp_rw [Nat.card_eq_finsetCard, Nat.cast_prod]
  rw [ENNReal.prod_inv_distrib]
  exact fun _ _ _ _ _ ↦ Or.inr ENNReal.coe_ne_top

/-- Restricting the full product experiment to any finite set of request
coordinates gives the uniform law on the corresponding dependent product. -/
theorem tangentUniformMultiplierRestriction_map_eq_uniformOfFintype
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (support : Finset Request) :
    (tangentUniformMultiplierMeasure lists hlist).map
        (fun outcome (request : ↑support) ↦ outcome request.1) =
      tangentUniformMultiplierRestrictionMeasure lists hlist support := by
  let μ := tangentUniformMultiplierMeasure lists hlist
  let restrictedLists : ↑support → Finset ℕ :=
    fun request ↦ lists request.1
  let hrestricted : ∀ request, (restrictedLists request).Nonempty :=
    fun request ↦ hlist request.1
  letI : ∀ request, Nonempty (TangentMultiplierChoice lists request) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request)
  letI : IsProbabilityMeasure μ :=
    tangentUniformMultiplierMeasure_isProbability lists hlist
  have hindep : iIndepFun
      (fun request : ↑support =>
        fun outcome : TangentMultiplierOutcome lists => outcome request.1) μ :=
    (tangentUniformMultiplierCoordinates_iIndep lists hlist).precomp
      Subtype.val_injective
  have hcoordinate : ∀ request : ↑support,
      μ.map (fun outcome : TangentMultiplierOutcome lists ↦ outcome request.1) =
        (PMF.uniformOfFintype
          (TangentMultiplierChoice lists request.1)).toMeasure := by
    intro request
    dsimp only [μ]
    unfold tangentUniformMultiplierMeasure
    letI : ∀ r, Nonempty (TangentMultiplierChoice lists r) :=
      fun r ↦ Finset.nonempty_coe_sort.mpr (hlist r)
    exact (measurePreserving_eval
      (fun r ↦ (PMF.uniformOfFintype
        (TangentMultiplierChoice lists r)).toMeasure) request.1).map_eq
  calc
    μ.map (fun outcome (request : ↑support) ↦ outcome request.1) =
        Measure.pi (fun request : ↑support ↦
          μ.map (fun outcome : TangentMultiplierOutcome lists ↦
            outcome request.1)) :=
      (iIndepFun_iff_map_fun_eq_pi_map
        (fun request : ↑support ↦
          (measurable_pi_apply request.1).aemeasurable)).mp hindep
    _ = tangentUniformMultiplierMeasure restrictedLists hrestricted := by
      change Measure.pi (fun request : ↑support ↦
          μ.map (fun outcome : TangentMultiplierOutcome lists ↦
            outcome request.1)) =
        Measure.pi (fun request : ↑support ↦
          (PMF.uniformOfFintype
            (TangentMultiplierChoice lists request.1)).toMeasure)
      have hmeasureFamily :
          (fun request : ↑support ↦
            μ.map (fun outcome : TangentMultiplierOutcome lists ↦
              outcome request.1)) =
          (fun request : ↑support ↦
            (PMF.uniformOfFintype
              (TangentMultiplierChoice lists request.1)).toMeasure) :=
        funext hcoordinate
      exact congrArg (fun measures ↦ Measure.pi measures) hmeasureFamily
    _ = tangentUniformMultiplierRestrictionMeasure lists hlist support := by
      simpa only [tangentUniformMultiplierRestrictionMeasure,
        restrictedLists, hrestricted] using
        tangentUniformMultiplierMeasure_eq_uniformOfFintype
          (Request := ↑support) restrictedLists hrestricted

/-- Cardinality formula for the preceding supported uniform measure. -/
theorem tangentUniformMultiplierRestrictionMeasure_apply
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (support : Finset Request)
    (s : Set (∀ request : ↑support,
      TangentMultiplierChoice lists request.1))
    (hs : MeasurableSet s) :
    tangentUniformMultiplierRestrictionMeasure lists hlist support s =
      Nat.card s /
        Nat.card (∀ request : ↑support,
          TangentMultiplierChoice lists request.1) := by
  classical
  letI : ∀ request : ↑support,
      Nonempty (TangentMultiplierChoice lists request.1) :=
    fun request ↦ Finset.nonempty_coe_sort.mpr (hlist request.1)
  unfold tangentUniformMultiplierRestrictionMeasure
    tangentUniformMultiplierOutcomeMeasure
  exact tangentFiniteUniformMeasure_apply
    (∀ request : ↑support,
      TangentMultiplierChoice lists request.1) inferInstance s hs

/-! ## Exact collision configurations -/

/-- All assignments on the two coordinates supporting one collision. -/
abbrev TangentCollisionConfiguration
    {Request : Type*} {lists : Request → Finset ℕ}
    (collision : TangentCollisionIndex Request) :=
  ∀ request : ↑collision.1,
    TangentMultiplierChoice lists request.1

/-- The colliding assignments on one two-request support. -/
def tangentCollisionConfigurations
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    Finset (TangentCollisionConfiguration (lists := lists) collision) := by
  classical
  exact Finset.univ.filter fun outcome ↦
    tangentCollisionOn source target collision outcome

/-- Number of all assignments on a two-request support. -/
def tangentCollisionChoiceCount
    {Request : Type*} {lists : Request → Finset ℕ}
    (collision : TangentCollisionIndex Request) : ℕ :=
  ∏ request : ↑collision.1, (lists request.1).card

/-- The actual collision probability is exactly the ratio of the number of
colliding configurations to the product of the two list cardinalities. -/
theorem tangentCollisionProbability_eq_configurationCount_div
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionProbability lists hlist source target collision =
      ((tangentCollisionConfigurations
          (lists := lists) source target collision).card : ℝ) /
        tangentCollisionChoiceCount (lists := lists) collision := by
  classical
  let restriction := fun outcome : TangentMultiplierOutcome lists =>
    fun request : ↑collision.1 => outcome request.1
  have hrestriction : Measurable restriction := by
    exact measurable_pi_iff.mpr fun request ↦ measurable_pi_apply request.1
  have hcollisionMeasurable : MeasurableSet
      ({outcome : TangentCollisionConfiguration (lists := lists) collision |
        tangentCollisionOn source target collision outcome} : Set _) :=
    (Set.toFinite _).measurableSet
  rw [tangentCollisionProbability]
  change ENNReal.toReal
      ((tangentUniformMultiplierMeasure lists hlist)
        (restriction ⁻¹'
          {outcome | tangentCollisionOn source target collision outcome})) = _
  rw [← Measure.map_apply hrestriction hcollisionMeasurable,
    tangentUniformMultiplierRestriction_map_eq_uniformOfFintype
      lists hlist collision.1]
  rw [tangentUniformMultiplierRestrictionMeasure_apply
    lists hlist collision.1
      {outcome | tangentCollisionOn source target collision outcome}
      hcollisionMeasurable]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast,
    Nat.card_eq_fintype_card, Fintype.card_pi, Fintype.card_coe,
    tangentCollisionChoiceCount]
  congr 1
  rw [Fintype.card_subtype]
  rfl

/-! ## Naming the two requests and the four endpoint equations -/

/-- Canonical first request on a two-element collision support. -/
def tangentCollisionFirstRequest
    {Request : Type*} (collision : TangentCollisionIndex Request) :
    ↑collision.1 :=
  (collision.1.equivFinOfCardEq collision.2).symm 0

/-- Canonical second request on a two-element collision support. -/
def tangentCollisionSecondRequest
    {Request : Type*} (collision : TangentCollisionIndex Request) :
    ↑collision.1 :=
  (collision.1.equivFinOfCardEq collision.2).symm 1

theorem tangentCollisionFirstRequest_ne_secondRequest
    {Request : Type*} (collision : TangentCollisionIndex Request) :
    tangentCollisionFirstRequest collision ≠
      tangentCollisionSecondRequest collision := by
  intro heq
  have h := congrArg (collision.1.equivFinOfCardEq collision.2) heq
  have hzeroOne : (0 : Fin 2) = 1 := by
    simpa only [tangentCollisionFirstRequest,
      tangentCollisionSecondRequest, Equiv.apply_symm_apply] using h
  exact Fin.zero_ne_one hzeroOne

/-- The canonical two requests exhaust the support. -/
theorem tangentCollisionSupport_eq_pair
    {Request : Type*} [DecidableEq Request]
    (collision : TangentCollisionIndex Request) :
    collision.1 =
      {(tangentCollisionFirstRequest collision).1,
        (tangentCollisionSecondRequest collision).1} := by
  let first := tangentCollisionFirstRequest collision
  let second := tangentCollisionSecondRequest collision
  have hne : first.1 ≠ second.1 := by
    intro h
    exact tangentCollisionFirstRequest_ne_secondRequest collision
      (Subtype.ext h)
  have hsubset : ({first.1, second.1} : Finset Request) ⊆ collision.1 := by
    intro request hrequest
    simp only [Finset.mem_insert, Finset.mem_singleton] at hrequest
    rcases hrequest with rfl | rfl
    · exact first.2
    · exact second.2
  have hcard : collision.1.card ≤
      ({first.1, second.1} : Finset Request).card := by
    rw [collision.2, Finset.card_pair hne]
  exact (Finset.eq_of_subset_of_card_le hsubset hcard).symm

/-- The existential collision predicate can be read using the canonical
first and second requests. -/
theorem tangentCollisionOn_iff_canonicalPair
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (outcome : TangentCollisionConfiguration
      (lists := lists) collision) :
    tangentCollisionOn source target collision outcome ↔
      ¬Disjoint
        (tangentRestrictedEndpointSet source target collision.1 outcome
          (tangentCollisionFirstRequest collision))
        (tangentRestrictedEndpointSet source target collision.1 outcome
          (tangentCollisionSecondRequest collision)) := by
  let first := tangentCollisionFirstRequest collision
  let second := tangentCollisionSecondRequest collision
  have hsupport : collision.1 =
      ({first.1, second.1} : Finset Request) :=
    tangentCollisionSupport_eq_pair collision
  have hsupportSubset : collision.1 ⊆
      ({first.1, second.1} : Finset Request) := by
    intro request hrequest
    rw [← hsupport]
    exact hrequest
  constructor
  · rintro ⟨r, s, hrs, hoverlap⟩
    have hr : r.1 = first.1 ∨ r.1 = second.1 := by
      have hmem := hsupportSubset r.property
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    have hs : s.1 = first.1 ∨ s.1 = second.1 := by
      have hmem := hsupportSubset s.property
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact (hrs (Subtype.ext (hr.trans hs.symm))).elim
    · have hrEq : r = first := Subtype.ext hr
      have hsEq : s = second := Subtype.ext hs
      subst r
      subst s
      exact hoverlap
    · have hrEq : r = second := Subtype.ext hr
      have hsEq : s = first := Subtype.ext hs
      subst r
      subst s
      simpa only [_root_.disjoint_comm] using hoverlap
    · exact (hrs (Subtype.ext (hr.trans hs.symm))).elim
  · intro hoverlap
    exact ⟨first, second,
      tangentCollisionFirstRequest_ne_secondRequest collision,
      by simpa only [first, second] using hoverlap⟩

/-- The two choices of endpoint on one request. -/
inductive TangentEndpointSide
  | source
  | target
  deriving DecidableEq, Fintype

/-- Label selected by one endpoint side. -/
def tangentEndpointLabel
    {Request : Type*} (source target : Request → ℕ)
    (side : TangentEndpointSide) (request : Request) : ℕ :=
  match side with
  | .source => source request
  | .target => target request

/-- Numerical endpoint selected by a side in a restricted outcome. -/
def tangentRestrictedEndpointValue
    {Request : Type*} {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    {support : Finset Request}
    (outcome : ∀ request : ↑support,
      TangentMultiplierChoice lists request.1)
    (side : TangentEndpointSide) (request : ↑support) : ℕ :=
  tangentEndpointLabel source target side request.1 *
    (outcome request).1

/-- Collision is equivalent to one of the literal four endpoint equations. -/
theorem tangentCollisionOn_iff_exists_endpointEquation
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (outcome : TangentCollisionConfiguration
      (lists := lists) collision) :
    tangentCollisionOn source target collision outcome ↔
      ∃ leftSide rightSide : TangentEndpointSide,
        tangentRestrictedEndpointValue source target outcome leftSide
            (tangentCollisionFirstRequest collision) =
          tangentRestrictedEndpointValue source target outcome rightSide
            (tangentCollisionSecondRequest collision) := by
  rw [tangentCollisionOn_iff_canonicalPair]
  constructor
  · intro hoverlap
    obtain ⟨value, hleft, hright⟩ :=
      Finset.not_disjoint_iff.mp hoverlap
    simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
      Finset.mem_singleton] at hleft hright
    rcases hleft with hleft | hleft <;>
      rcases hright with hright | hright
    · exact ⟨.source, .source, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
    · exact ⟨.source, .target, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
    · exact ⟨.target, .source, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
    · exact ⟨.target, .target, by
        simpa [tangentRestrictedEndpointValue, tangentEndpointLabel]
          using hleft.symm.trans hright⟩
  · rintro ⟨leftSide, rightSide, heq⟩
    apply Finset.not_disjoint_iff.mpr
    cases leftSide <;> cases rightSide
    all_goals
      simp only [tangentRestrictedEndpointValue,
        tangentEndpointLabel] at heq
    · exact ⟨source (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inl heq⟩
    · exact ⟨source (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inr heq⟩
    · exact ⟨target (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inl heq⟩
    · exact ⟨target (tangentCollisionFirstRequest collision).1 *
          (outcome (tangentCollisionFirstRequest collision)).1,
        by
          simp [tangentRestrictedEndpointSet],
        by
          simp only [tangentRestrictedEndpointSet, Finset.mem_insert,
            Finset.mem_singleton]
          exact Or.inr heq⟩

/-- Configurations satisfying one specified endpoint equation. -/
def tangentEndpointEquationConfigurations
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (leftSide rightSide : TangentEndpointSide) :
    Finset (TangentCollisionConfiguration (lists := lists) collision) := by
  classical
  exact Finset.univ.filter fun outcome ↦
    tangentRestrictedEndpointValue source target outcome leftSide
        (tangentCollisionFirstRequest collision) =
      tangentRestrictedEndpointValue source target outcome rightSide
        (tangentCollisionSecondRequest collision)

/-- The collision count is at most the sum of the four endpoint-equation
configuration counts. -/
theorem card_tangentCollisionConfigurations_le_fourEndpointEquations
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) :
    (tangentCollisionConfigurations
      (lists := lists) source target collision).card ≤
      ∑ leftSide : TangentEndpointSide,
        ∑ rightSide : TangentEndpointSide,
          (tangentEndpointEquationConfigurations
            (lists := lists) source target collision
              leftSide rightSide).card := by
  classical
  let equationUnion := Finset.univ.biUnion fun leftSide : TangentEndpointSide ↦
    Finset.univ.biUnion fun rightSide : TangentEndpointSide ↦
      tangentEndpointEquationConfigurations
        (lists := lists) source target collision leftSide rightSide
  have hsubset : tangentCollisionConfigurations
    (lists := lists) source target collision ⊆ equationUnion := by
    intro outcome houtcome
    have hcollision :
        tangentCollisionOn source target collision outcome := by
      simpa only [tangentCollisionConfigurations, Finset.mem_filter,
        Finset.mem_univ, true_and] using houtcome
    obtain ⟨leftSide, rightSide, heq⟩ :=
      (tangentCollisionOn_iff_exists_endpointEquation
        source target collision outcome).mp hcollision
    apply Finset.mem_biUnion.mpr
    refine ⟨leftSide, Finset.mem_univ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨rightSide, Finset.mem_univ _, ?_⟩
    simpa only [tangentEndpointEquationConfigurations,
      Finset.mem_filter, Finset.mem_univ, true_and] using heq
  calc
    (tangentCollisionConfigurations
        (lists := lists) source target collision).card ≤
        equationUnion.card := Finset.card_le_card hsubset
    _ ≤ ∑ leftSide ∈ (Finset.univ : Finset TangentEndpointSide),
        (Finset.univ.biUnion fun rightSide : TangentEndpointSide ↦
          tangentEndpointEquationConfigurations
            (lists := lists) source target collision
              leftSide rightSide).card := Finset.card_biUnion_le
    _ ≤ ∑ leftSide ∈ (Finset.univ : Finset TangentEndpointSide),
        ∑ rightSide ∈ (Finset.univ : Finset TangentEndpointSide),
          (tangentEndpointEquationConfigurations
            (lists := lists) source target collision
              leftSide rightSide).card := by
      exact Finset.sum_le_sum fun leftSide _hleft ↦
        Finset.card_biUnion_le
    _ = _ := rfl

/-! ## Raw solutions of `p*a=q*b` -/

/-- Pairs from two lists satisfying one endpoint equation. -/
def tangentEndpointEquationSolutions
    (leftList rightList : Finset ℕ) (leftLabel rightLabel : ℕ) :
    Finset (ℕ × ℕ) :=
  (leftList.product rightList).filter fun pair ↦
    leftLabel * pair.1 = rightLabel * pair.2

/-- Reading the two selected multipliers is injective on assignments to a
two-element support. -/
theorem tangentCollisionValuePair_injective
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (collision : TangentCollisionIndex Request) :
    Function.Injective
      (fun outcome : TangentCollisionConfiguration
          (lists := lists) collision ↦
        ((outcome (tangentCollisionFirstRequest collision)).1,
          (outcome (tangentCollisionSecondRequest collision)).1)) := by
  intro left right heq
  funext request
  apply Subtype.ext
  have hsupport : collision.1 =
      ({(tangentCollisionFirstRequest collision).1,
        (tangentCollisionSecondRequest collision).1} : Finset Request) :=
    tangentCollisionSupport_eq_pair collision
  have hsupportSubset : collision.1 ⊆
      ({(tangentCollisionFirstRequest collision).1,
        (tangentCollisionSecondRequest collision).1} : Finset Request) := by
    intro candidate hcandidate
    rw [← hsupport]
    exact hcandidate
  have hrequest : request.1 =
        (tangentCollisionFirstRequest collision).1 ∨
      request.1 = (tangentCollisionSecondRequest collision).1 := by
    have hmem := hsupportSubset request.property
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rcases hrequest with hrequest | hrequest
  · have hr : request = tangentCollisionFirstRequest collision :=
      Subtype.ext hrequest
    subst request
    exact congrArg Prod.fst heq
  · have hr : request = tangentCollisionSecondRequest collision :=
      Subtype.ext hrequest
    subst request
    exact congrArg Prod.snd heq

/-- An endpoint-equation configuration injects into the raw pair solutions
from the two actual request lists. -/
theorem card_tangentEndpointEquationConfigurations_le_solutions
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request)
    (leftSide rightSide : TangentEndpointSide) :
    (tangentEndpointEquationConfigurations
      (lists := lists) source target collision
        leftSide rightSide).card ≤
      (tangentEndpointEquationSolutions
        (lists (tangentCollisionFirstRequest collision).1)
        (lists (tangentCollisionSecondRequest collision).1)
        (tangentEndpointLabel source target leftSide
          (tangentCollisionFirstRequest collision).1)
        (tangentEndpointLabel source target rightSide
          (tangentCollisionSecondRequest collision).1)).card := by
  apply Finset.card_le_card_of_injOn
    (s := tangentEndpointEquationConfigurations
      (lists := lists) source target collision leftSide rightSide)
    (t := tangentEndpointEquationSolutions
      (lists (tangentCollisionFirstRequest collision).1)
      (lists (tangentCollisionSecondRequest collision).1)
      (tangentEndpointLabel source target leftSide
        (tangentCollisionFirstRequest collision).1)
      (tangentEndpointLabel source target rightSide
        (tangentCollisionSecondRequest collision).1))
    (fun outcome ↦
      ((outcome (tangentCollisionFirstRequest collision)).1,
        (outcome (tangentCollisionSecondRequest collision)).1))
  · intro outcome houtcome
    have heq := (Finset.mem_filter.mp houtcome).2
    exact Finset.mem_filter.mpr ⟨
      Finset.mem_product.mpr ⟨
        (outcome (tangentCollisionFirstRequest collision)).2,
        (outcome (tangentCollisionSecondRequest collision)).2⟩,
      by simpa [tangentRestrictedEndpointValue] using heq⟩
  · exact (tangentCollisionValuePair_injective
      (lists := lists) collision).injOn

/-- If the two positive labels are equal, cancellation and the endpoint
cutoff give at most `N/p+1` raw solutions. -/
theorem card_tangentEndpointEquationSolutions_same_le
    {leftList rightList : Finset ℕ} {label N : ℕ}
    (hlabel : 0 < label)
    (hupper : ∀ a ∈ leftList, label * a ≤ N) :
    (tangentEndpointEquationSolutions
      leftList rightList label label).card ≤ N / label + 1 := by
  have hcard : (tangentEndpointEquationSolutions
      leftList rightList label label).card ≤
      (Finset.range (N / label + 1)).card := by
    apply Finset.card_le_card_of_injOn
      (s := tangentEndpointEquationSolutions
        leftList rightList label label)
      (t := Finset.range (N / label + 1))
      (fun pair : ℕ × ℕ ↦ pair.1)
    · intro pair hpair
      have hdata := Finset.mem_filter.mp hpair
      have hleftMem : pair.1 ∈ leftList :=
        (Finset.mem_product.mp hdata.1).1
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le hlabel).mpr
      simpa only [Nat.mul_comm] using hupper pair.1 hleftMem
    · intro left hleft right hright hfirst
      have hleftEq := (Finset.mem_filter.mp hleft).2
      have hrightEq := (Finset.mem_filter.mp hright).2
      change left.1 = right.1 at hfirst
      apply Prod.ext hfirst
      apply mul_left_cancel₀ hlabel.ne'
      calc
        label * left.2 = label * left.1 := hleftEq.symm
        _ = label * right.1 := by rw [hfirst]
        _ = label * right.2 := hrightEq
  simpa only [Finset.card_range] using hcard

/-- For coprime positive distinct labels, write `a=q*m`; the endpoint cutoff
then gives `m <= N/(p*q)`. -/
theorem card_tangentEndpointEquationSolutions_coprime_le
    {leftList rightList : Finset ℕ} {leftLabel rightLabel N : ℕ}
    (hleft : 0 < leftLabel) (hright : 0 < rightLabel)
    (hcoprime : Nat.Coprime leftLabel rightLabel)
    (hupper : ∀ a ∈ leftList, leftLabel * a ≤ N) :
    (tangentEndpointEquationSolutions
      leftList rightList leftLabel rightLabel).card ≤
        N / (leftLabel * rightLabel) + 1 := by
  let quotient := fun pair : ℕ × ℕ ↦ pair.1 / rightLabel
  have hdivisible : ∀ pair ∈
      tangentEndpointEquationSolutions
        leftList rightList leftLabel rightLabel,
      rightLabel ∣ pair.1 := by
    intro pair hpair
    have heq := (Finset.mem_filter.mp hpair).2
    apply (hcoprime.symm.dvd_mul_right).mp
    rw [Nat.mul_comm]
    exact ⟨pair.2, heq⟩
  have hcard : (tangentEndpointEquationSolutions
      leftList rightList leftLabel rightLabel).card ≤
      (Finset.range (N / (leftLabel * rightLabel) + 1)).card := by
    apply Finset.card_le_card_of_injOn
      (s := tangentEndpointEquationSolutions
        leftList rightList leftLabel rightLabel)
      (t := Finset.range (N / (leftLabel * rightLabel) + 1))
      quotient
    · intro pair hpair
      have hproduct : pair ∈ leftList.product rightList :=
        (Finset.mem_filter.mp hpair).1
      have hleftMem : pair.1 ∈ leftList :=
        (Finset.mem_product.mp hproduct).1
      apply Finset.mem_range.mpr
      apply Nat.lt_succ_of_le
      apply (Nat.le_div_iff_mul_le (Nat.mul_pos hleft hright)).mpr
      calc
        quotient pair * (leftLabel * rightLabel) =
            leftLabel * (rightLabel * quotient pair) := by ac_rfl
        _ = leftLabel * pair.1 := by
          rw [Nat.mul_div_cancel' (hdivisible pair hpair)]
        _ ≤ N := hupper pair.1 hleftMem
    · intro left hleftMem right hrightMem hquotient
      have hleftFirst : left.1 = rightLabel * quotient left := by
        exact (Nat.mul_div_cancel' (hdivisible left hleftMem)).symm
      have hrightFirst : right.1 = rightLabel * quotient right := by
        exact (Nat.mul_div_cancel' (hdivisible right hrightMem)).symm
      have hfirst : left.1 = right.1 := by
        rw [hleftFirst, hrightFirst, hquotient]
      apply Prod.ext hfirst
      apply mul_left_cancel₀ hright.ne'
      have hleftEq := (Finset.mem_filter.mp hleftMem).2
      have hrightEq := (Finset.mem_filter.mp hrightMem).2
      calc
        rightLabel * left.2 = leftLabel * left.1 := hleftEq.symm
        _ = leftLabel * right.1 := by rw [hfirst]
        _ = rightLabel * right.2 := hrightEq
  simpa only [Finset.card_range] using hcard

/-- Exact integer budget for one endpoint equation in the paper's two
cases: a shared label, or two distinct prime labels. -/
def tangentEndpointEquationBudget (N leftLabel rightLabel : ℕ) : ℕ :=
  if leftLabel = rightLabel then N / leftLabel + 1
  else N / (leftLabel * rightLabel) + 1

/-- Prime labels obey the preceding literal endpoint-equation budget. -/
theorem card_tangentEndpointEquationSolutions_prime_le_budget
    {leftList rightList : Finset ℕ} {leftLabel rightLabel N : ℕ}
    (hleftPrime : leftLabel.Prime)
    (hrightPrime : rightLabel.Prime)
    (hupper : ∀ a ∈ leftList, leftLabel * a ≤ N) :
    (tangentEndpointEquationSolutions
      leftList rightList leftLabel rightLabel).card ≤
        tangentEndpointEquationBudget N leftLabel rightLabel := by
  by_cases heq : leftLabel = rightLabel
  · subst rightLabel
    simpa [tangentEndpointEquationBudget] using
      card_tangentEndpointEquationSolutions_same_le
        hleftPrime.pos hupper
  · simpa [tangentEndpointEquationBudget, heq] using
      card_tangentEndpointEquationSolutions_coprime_le
        hleftPrime.pos hrightPrime.pos
        ((Nat.coprime_primes hleftPrime hrightPrime).mpr heq) hupper

/-- Sum of the four literal endpoint-equation budgets for a collision. -/
def tangentCollisionEndpointBudget
    {Request : Type*} (N : ℕ) (source target : Request → ℕ)
    (collision : TangentCollisionIndex Request) : ℕ :=
  ∑ leftSide : TangentEndpointSide,
    ∑ rightSide : TangentEndpointSide,
      tangentEndpointEquationBudget N
        (tangentEndpointLabel source target leftSide
          (tangentCollisionFirstRequest collision).1)
        (tangentEndpointLabel source target rightSide
          (tangentCollisionSecondRequest collision).1)

/-- The same four-equation budget written for an ordered pair of requests. -/
def tangentOrderedPairEndpointBudget
    {Request : Type*} (N : ℕ) (source target : Request → ℕ)
    (left right : Request) : ℕ :=
  ∑ leftSide : TangentEndpointSide,
    ∑ rightSide : TangentEndpointSide,
      tangentEndpointEquationBudget N
        (tangentEndpointLabel source target leftSide left)
        (tangentEndpointLabel source target rightSide right)

theorem tangentEndpointEquationBudget_comm
    (N leftLabel rightLabel : ℕ) :
    tangentEndpointEquationBudget N leftLabel rightLabel =
      tangentEndpointEquationBudget N rightLabel leftLabel := by
  by_cases heq : leftLabel = rightLabel
  · subst rightLabel
    rfl
  · have hne : rightLabel ≠ leftLabel := Ne.symm heq
    simp [tangentEndpointEquationBudget, heq, hne, Nat.mul_comm]

theorem tangentOrderedPairEndpointBudget_comm
    {Request : Type*} (N : ℕ) (source target : Request → ℕ)
    (left right : Request) :
    tangentOrderedPairEndpointBudget N source target left right =
      tangentOrderedPairEndpointBudget N source target right left := by
  unfold tangentOrderedPairEndpointBudget
  calc
    (∑ leftSide : TangentEndpointSide,
      ∑ rightSide : TangentEndpointSide,
        tangentEndpointEquationBudget N
          (tangentEndpointLabel source target leftSide left)
          (tangentEndpointLabel source target rightSide right)) =
      ∑ leftSide : TangentEndpointSide,
        ∑ rightSide : TangentEndpointSide,
          tangentEndpointEquationBudget N
            (tangentEndpointLabel source target rightSide right)
            (tangentEndpointLabel source target leftSide left) := by
      exact Finset.sum_congr rfl fun leftSide _hleft ↦
        Finset.sum_congr rfl fun rightSide _hright ↦
          tangentEndpointEquationBudget_comm N _ _
    _ = _ := by rw [Finset.sum_comm]

/-- The number of colliding assignments is controlled by the sum of the
four explicit prime-equation budgets. -/
theorem card_tangentCollisionConfigurations_le_endpointBudget
    {Request : Type*} [DecidableEq Request]
    {lists : Request → Finset ℕ}
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (collision : TangentCollisionIndex Request) :
    (tangentCollisionConfigurations
      (lists := lists) source target collision).card ≤
      tangentCollisionEndpointBudget N source target collision := by
  refine (card_tangentCollisionConfigurations_le_fourEndpointEquations
    (lists := lists) source target collision).trans ?_
  exact Finset.sum_le_sum fun leftSide _hleft ↦
    Finset.sum_le_sum fun rightSide _hright ↦
      (card_tangentEndpointEquationConfigurations_le_solutions
        (lists := lists) source target collision leftSide rightSide).trans
        (card_tangentEndpointEquationSolutions_prime_le_budget
          (hprime _ leftSide) (hprime _ rightSide)
          (fun multiplier hmultiplier ↦
            hupper _ leftSide multiplier hmultiplier))

/-! ## From list cardinalities to pair probabilities -/

/-- Product of request-wise lower cardinalities on a collision support. -/
def tangentCollisionLowerChoiceCount
    {Request : Type*} (lowerCard : Request → ℕ)
    (collision : TangentCollisionIndex Request) : ℕ :=
  ∏ request : ↑collision.1, lowerCard request.1

theorem tangentCollisionLowerChoiceCount_pos
    {Request : Type*} (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (collision : TangentCollisionIndex Request) :
    0 < tangentCollisionLowerChoiceCount lowerCard collision := by
  exact Finset.prod_pos fun request _hrequest ↦ hlowerPos request.1

theorem tangentCollisionLowerChoiceCount_le_choiceCount
    {Request : Type*} {lists : Request → Finset ℕ}
    (lowerCard : Request → ℕ)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionLowerChoiceCount lowerCard collision ≤
      tangentCollisionChoiceCount (lists := lists) collision := by
  exact Finset.prod_le_prod
    (fun _request _hrequest ↦ Nat.zero_le _)
    (fun request _hrequest ↦ hlower request.1)

/-- Probability estimate obtained only from the four equation counts and
request-wise list cardinality lower bounds. -/
theorem tangentCollisionProbability_le_endpointBudget_div_lowerChoiceCount
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (collision : TangentCollisionIndex Request) :
    tangentCollisionProbability lists hlist source target collision ≤
      (tangentCollisionEndpointBudget N source target collision : ℝ) /
        tangentCollisionLowerChoiceCount lowerCard collision := by
  rw [tangentCollisionProbability_eq_configurationCount_div]
  calc
    ((tangentCollisionConfigurations
          (lists := lists) source target collision).card : ℝ) /
        tangentCollisionChoiceCount (lists := lists) collision ≤
      (tangentCollisionEndpointBudget N source target collision : ℝ) /
        tangentCollisionChoiceCount (lists := lists) collision := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast card_tangentCollisionConfigurations_le_endpointBudget
        (lists := lists) N source target hprime hupper collision
    _ ≤ (tangentCollisionEndpointBudget N source target collision : ℝ) /
        tangentCollisionLowerChoiceCount lowerCard collision := by
      apply div_le_div_of_nonneg_left (by positivity)
      · exact_mod_cast tangentCollisionLowerChoiceCount_pos
          lowerCard hlowerPos collision
      · exact_mod_cast tangentCollisionLowerChoiceCount_le_choiceCount
          (lists := lists) lowerCard hlower collision

/-! ## Exact reindexing of an incident-event sum -/

/-- Erasing one member from a two-element collision support leaves a
nonempty singleton. -/
private theorem tangentIncidentErase_nonempty
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    (collision.1.erase request).Nonempty := by
  rw [← Finset.card_pos, Finset.card_erase_of_mem hrequest, collision.2]
  norm_num

/-- The other request in a two-request support containing `request`.  It is
totalized by returning `request` when the incidence premise is false. -/
def tangentIncidentOtherRequest
    {Request : Type*} [DecidableEq Request]
    (request : Request) (collision : TangentCollisionIndex Request) :
    Request :=
  if hrequest : request ∈ collision.1 then
    (tangentIncidentErase_nonempty hrequest).choose
  else request

theorem tangentIncidentOtherRequest_mem_erase
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    tangentIncidentOtherRequest request collision ∈
      collision.1.erase request := by
  simp only [tangentIncidentOtherRequest, dif_pos hrequest]
  exact (tangentIncidentErase_nonempty hrequest).choose_spec

theorem tangentIncidentOtherRequest_ne
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    tangentIncidentOtherRequest request collision ≠ request := by
  exact Finset.ne_of_mem_erase
    (tangentIncidentOtherRequest_mem_erase hrequest)

theorem tangentIncidentSupport_eq_pair
    {Request : Type*} [DecidableEq Request]
    {request : Request} {collision : TangentCollisionIndex Request}
    (hrequest : request ∈ collision.1) :
    collision.1 = {request, tangentIncidentOtherRequest request collision} := by
  have hcard : (collision.1.erase request).card = 1 := by
    rw [Finset.card_erase_of_mem hrequest, collision.2]
  obtain ⟨other, hother⟩ := Finset.card_eq_one.mp hcard
  have hchosen := tangentIncidentOtherRequest_mem_erase hrequest
  rw [hother] at hchosen
  have hchosenEq : tangentIncidentOtherRequest request collision = other := by
    simpa only [Finset.mem_singleton] using hchosen
  rw [← Finset.insert_erase hrequest, hother, hchosenEq]

/-- Collision index attached to two distinct requests. -/
def tangentCollisionIndexOfDistinctRequests
    {Request : Type*} [DecidableEq Request]
    (left right : Request) (hne : left ≠ right) :
    TangentCollisionIndex Request :=
  ⟨{left, right}, Finset.card_pair hne⟩

/-- On the pair collision index, the internal support ordering gives the
same (symmetric) four-equation budget as the displayed ordered pair. -/
theorem tangentCollisionEndpointBudget_pair
    {Request : Type*} [DecidableEq Request]
    (N : ℕ) (source target : Request → ℕ)
    (left right : Request) (hne : left ≠ right) :
    tangentCollisionEndpointBudget N source target
        (tangentCollisionIndexOfDistinctRequests left right hne) =
      tangentOrderedPairEndpointBudget N source target left right := by
  let collision := tangentCollisionIndexOfDistinctRequests left right hne
  have hfirst : (tangentCollisionFirstRequest collision).1 = left ∨
      (tangentCollisionFirstRequest collision).1 = right := by
    have hmem := (tangentCollisionFirstRequest collision).2
    simpa only [collision, tangentCollisionIndexOfDistinctRequests,
      Finset.mem_insert, Finset.mem_singleton] using hmem
  have hsecond : (tangentCollisionSecondRequest collision).1 = left ∨
      (tangentCollisionSecondRequest collision).1 = right := by
    have hmem := (tangentCollisionSecondRequest collision).2
    simpa only [collision, tangentCollisionIndexOfDistinctRequests,
      Finset.mem_insert, Finset.mem_singleton] using hmem
  change tangentOrderedPairEndpointBudget N source target
      (tangentCollisionFirstRequest collision).1
      (tangentCollisionSecondRequest collision).1 =
    tangentOrderedPairEndpointBudget N source target left right
  rcases hfirst with hfirst | hfirst <;>
    rcases hsecond with hsecond | hsecond
  · exact (tangentCollisionFirstRequest_ne_secondRequest collision
      (Subtype.ext (hfirst.trans hsecond.symm))).elim
  · rw [hfirst, hsecond]
  · rw [hfirst, hsecond]
    exact tangentOrderedPairEndpointBudget_comm
      N source target right left
  · exact (tangentCollisionFirstRequest_ne_secondRequest collision
      (Subtype.ext (hfirst.trans hsecond.symm))).elim

/-- On an ordered pair, the supported product is literally the product of
the two lower cardinalities. -/
theorem tangentCollisionLowerChoiceCount_pair
    {Request : Type*} [DecidableEq Request]
    (lowerCard : Request → ℕ) (left right : Request) (hne : left ≠ right) :
      tangentCollisionLowerChoiceCount lowerCard
        (tangentCollisionIndexOfDistinctRequests left right hne) =
      lowerCard left * lowerCard right := by
  rw [tangentCollisionLowerChoiceCount, Finset.prod_coe_sort]
  change (∏ request ∈ ({left, right} : Finset Request),
      lowerCard request) = lowerCard left * lowerCard right
  simp only [Finset.prod_insert, Finset.prod_singleton,
    Finset.mem_singleton, hne, not_false_eq_true]

/-- The actual supported choice count is likewise the product of the two
actual list cardinalities. -/
theorem tangentCollisionChoiceCount_pair
    {Request : Type*} [DecidableEq Request]
    (lists : Request → Finset ℕ) (left right : Request) (hne : left ≠ right) :
    tangentCollisionChoiceCount (lists := lists)
        (tangentCollisionIndexOfDistinctRequests left right hne) =
      (lists left).card * (lists right).card := by
  change tangentCollisionLowerChoiceCount
      (fun request ↦ (lists request).card)
      (tangentCollisionIndexOfDistinctRequests left right hne) =
    (lists left).card * (lists right).card
  exact tangentCollisionLowerChoiceCount_pair
    (fun request ↦ (lists request).card) left right hne

/-- Totalized collision probability for an ordered pair of requests. -/
def tangentPairCollisionProbability
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ) (left right : Request) : ℝ :=
  if hne : left ≠ right then
    tangentCollisionProbability lists hlist source target
      (tangentCollisionIndexOfDistinctRequests left right hne)
  else 0

/-- The incident collision sum is exactly the sum over all other requests;
there is no factor two and no double counting in this reindexing. -/
theorem tangentRequestCollisionMass_eq_sum_otherRequests
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ) (request : Request) :
    tangentRequestCollisionMass lists hlist source target request =
      ∑ other ∈ Finset.univ.erase request,
        tangentPairCollisionProbability lists hlist source target
          request other := by
  classical
  unfold tangentRequestCollisionMass tangentIncidentCollisions
  apply Finset.sum_bij
    (fun collision _hcollision ↦
      tangentIncidentOtherRequest request collision)
  · intro collision hcollision
    have hrequest := (Finset.mem_filter.mp hcollision).2
    exact Finset.mem_erase.mpr ⟨
      tangentIncidentOtherRequest_ne hrequest,
      Finset.mem_univ _⟩
  · intro left hleft right hright hother
    apply Subtype.ext
    have hleftRequest := (Finset.mem_filter.mp hleft).2
    have hrightRequest := (Finset.mem_filter.mp hright).2
    rw [tangentIncidentSupport_eq_pair hleftRequest,
      tangentIncidentSupport_eq_pair hrightRequest, hother]
  · intro other hother
    have hne : request ≠ other := by
      exact (Finset.mem_erase.mp hother).1.symm
    let collision := tangentCollisionIndexOfDistinctRequests
      request other hne
    have hrequestMem : request ∈ collision.1 := by
      simp only [collision, tangentCollisionIndexOfDistinctRequests,
        Finset.mem_insert, Finset.mem_singleton, true_or]
    have hcollision : collision ∈
        Finset.univ.filter fun event : TangentCollisionIndex Request ↦
          request ∈ event.1 := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hrequestMem⟩
    refine ⟨collision, hcollision, ?_⟩
    have hmem := tangentIncidentOtherRequest_mem_erase
      (collision := collision) (request := request) hrequestMem
    have herase : collision.1.erase request = {other} := by
      ext candidate
      simp only [collision, tangentCollisionIndexOfDistinctRequests,
        Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨_hneRequest, hcandidate⟩
        exact hcandidate.resolve_left _hneRequest
      · intro hcandidate
        subst candidate
        exact ⟨hne.symm, Or.inr rfl⟩
    rw [herase] at hmem
    exact Finset.mem_singleton.mp hmem
  · intro collision hcollision
    have hrequest := (Finset.mem_filter.mp hcollision).2
    have hne : request ≠ tangentIncidentOtherRequest request collision :=
      (tangentIncidentOtherRequest_ne hrequest).symm
    simp only [tangentPairCollisionProbability, dif_pos hne]
    congr 1
    apply Subtype.ext
    exact tangentIncidentSupport_eq_pair hrequest

/-! ## Request loads and the literal `1/8` terminal -/

/-- Whether a request has a specified endpoint label. -/
def tangentRequestHasLabel
    {Request : Type*} (source target : Request → ℕ)
    (label : ℕ) (request : Request) : Prop :=
  source request = label ∨ target request = label

instance instDecidableTangentRequestHasLabel
    {Request : Type*} (source target : Request → ℕ)
    (label : ℕ) (request : Request) :
    Decidable (tangentRequestHasLabel source target label request) := by
  unfold tangentRequestHasLabel
  infer_instance

/-- Number of requests other than `anchor` incident to `label`. -/
def tangentOtherRequestLabelLoad
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (anchor : Request) (label : ℕ) : ℕ :=
  ((Finset.univ.erase anchor).filter
    (tangentRequestHasLabel source target label)).card

/-- Paper load `k_p`: number of all requests incident to label `p`. -/
def tangentRequestLabelLoad
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (label : ℕ) : ℕ :=
  (Finset.univ.filter
    (tangentRequestHasLabel source target label)).card

/-- Number of other requests. -/
def tangentOtherRequestCount
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (anchor : Request) : ℕ :=
  (Finset.univ.erase anchor).card

/-- Paper total request count `K_req`. -/
def tangentTotalRequestCount (Request : Type*) [Fintype Request] : ℕ :=
  Fintype.card Request

theorem tangentOtherRequestLabelLoad_le_fullLoad
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (anchor : Request) (label : ℕ) :
    tangentOtherRequestLabelLoad source target anchor label ≤
      tangentRequestLabelLoad source target label := by
  apply Finset.card_le_card
  intro request hrequest
  have hdata : request ∈ Finset.univ.erase anchor ∧
      tangentRequestHasLabel source target label request :=
    Finset.mem_filter.mp hrequest
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hdata.2⟩

theorem tangentOtherRequestCount_le_requestCount
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (anchor : Request) :
    tangentOtherRequestCount anchor ≤ tangentTotalRequestCount Request := by
  unfold tangentOtherRequestCount tangentTotalRequestCount
  rw [Finset.card_erase_of_mem (Finset.mem_univ anchor),
    Finset.card_univ]
  exact Nat.sub_le _ _

/-- Sum of a label indicator is exactly the corresponding request load. -/
theorem sum_tangentRequestHasLabel_indicator
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (source target : Request → ℕ) (anchor : Request) (label : ℕ)
    (charge : ℝ) :
    ∑ other ∈ Finset.univ.erase anchor,
        (if tangentRequestHasLabel source target label other
        then charge else (0 : ℝ)) =
      (tangentOtherRequestLabelLoad source target anchor label : ℝ) *
        charge := by
  classical
  rw [← Finset.sum_filter]
  simp [tangentOtherRequestLabelLoad, Finset.sum_const,
    nsmul_eq_mul]

/-- Abstract load summation.  A disjoint-label charge is paid for every
other request, while a shared-label surcharge is paid only on requests
incident to either endpoint label of the fixed request. -/
theorem tangentRequestCollisionMass_le_loadBudget
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hpair : ∀ left right, left ≠ right →
      tangentPairCollisionProbability lists hlist source target left right ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (request : Request) :
    tangentRequestCollisionMass lists hlist source target request ≤
      (tangentOtherRequestCount request : ℝ) * disjointCharge +
        (tangentOtherRequestLabelLoad source target request
          (source request) : ℝ) * sharedCharge (source request) +
        (tangentOtherRequestLabelLoad source target request
          (target request) : ℝ) * sharedCharge (target request) := by
  rw [tangentRequestCollisionMass_eq_sum_otherRequests]
  calc
    (∑ other ∈ Finset.univ.erase request,
        tangentPairCollisionProbability lists hlist source target
          request other) ≤
      ∑ other ∈ Finset.univ.erase request,
        (disjointCharge +
          (if tangentRequestHasLabel source target (source request) other
            then sharedCharge (source request) else 0) +
          (if tangentRequestHasLabel source target (target request) other
            then sharedCharge (target request) else 0)) := by
      apply Finset.sum_le_sum
      intro other hother
      exact hpair request other (Finset.mem_erase.mp hother).1.symm
    _ = _ := by
      simp_rw [Finset.sum_add_distrib]
      rw [sum_tangentRequestHasLabel_indicator,
        sum_tangentRequestHasLabel_indicator]
      simp [tangentOtherRequestCount, Finset.sum_const, nsmul_eq_mul]

/-- Paper-facing version using the full loads `K_req`, `k_u`, and `k_v`.
The other-request version above is slightly sharper. -/
theorem tangentRequestCollisionMass_le_fullLoadBudget
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (source target : Request → ℕ)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hdisjointNonneg : 0 ≤ disjointCharge)
    (hsharedNonneg : ∀ label, 0 ≤ sharedCharge label)
    (hpair : ∀ left right, left ≠ right →
      tangentPairCollisionProbability lists hlist source target left right ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (request : Request) :
    tangentRequestCollisionMass lists hlist source target request ≤
      (tangentTotalRequestCount Request : ℝ) * disjointCharge +
        (tangentRequestLabelLoad source target
          (source request) : ℝ) * sharedCharge (source request) +
        (tangentRequestLabelLoad source target
          (target request) : ℝ) * sharedCharge (target request) := by
  refine (tangentRequestCollisionMass_le_loadBudget
    lists hlist source target disjointCharge sharedCharge hpair request).trans ?_
  apply add_le_add
  · apply add_le_add
    · apply mul_le_mul_of_nonneg_right _ hdisjointNonneg
      exact_mod_cast tangentOtherRequestCount_le_requestCount request
    · apply mul_le_mul_of_nonneg_right _ (hsharedNonneg (source request))
      exact_mod_cast tangentOtherRequestLabelLoad_le_fullLoad
        source target request (source request)
  · apply mul_le_mul_of_nonneg_right _ (hsharedNonneg (target request))
    exact_mod_cast tangentOtherRequestLabelLoad_le_fullLoad
      source target request (target request)

/-- The pairwise endpoint-counting estimate obtained from the exact finite
cardinality hypotheses, packaged in the totalized ordered-pair notation. -/
theorem tangentPairCollisionProbability_le_endpointBudget
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (left right : Request) (hne : left ≠ right) :
    tangentPairCollisionProbability lists hlist source target left right ≤
      (tangentCollisionEndpointBudget N source target
          (tangentCollisionIndexOfDistinctRequests left right hne) : ℝ) /
        tangentCollisionLowerChoiceCount lowerCard
          (tangentCollisionIndexOfDistinctRequests left right hne) := by
  rw [tangentPairCollisionProbability, dif_pos hne]
  exact tangentCollisionProbability_le_endpointBudget_div_lowerChoiceCount
    lists hlist lowerCard hlowerPos hlower N source target
      hprime hupper _

/-- Totalized version of the explicit endpoint-counting quotient for an
ordered pair. -/
def tangentPairEndpointBudgetQuotient
    {Request : Type*} [DecidableEq Request]
    (lowerCard : Request → ℕ) (N : ℕ)
    (source target : Request → ℕ) (left right : Request) : ℝ :=
  if _hne : left ≠ right then
    (tangentOrderedPairEndpointBudget N source target left right : ℝ) /
      (lowerCard left * lowerCard right)
  else 0

/-- Pair probability is bounded by the totalized exact counting quotient. -/
theorem tangentPairCollisionProbability_le_budgetQuotient
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (left right : Request) :
    tangentPairCollisionProbability lists hlist source target left right ≤
      tangentPairEndpointBudgetQuotient lowerCard N source target left right := by
  by_cases hne : left ≠ right
  · rw [tangentPairEndpointBudgetQuotient, dif_pos hne]
    simpa only [tangentCollisionEndpointBudget_pair,
      tangentCollisionLowerChoiceCount_pair, Nat.cast_mul] using
      tangentPairCollisionProbability_le_endpointBudget
      lists hlist lowerCard hlowerPos hlower N source target
        hprime hupper left right hne
  · rw [tangentPairEndpointBudgetQuotient, dif_neg hne,
      tangentPairCollisionProbability, dif_neg hne]

/-- Exact per-request reduction using only the four endpoint-equation
budgets and request-wise list cardinality lower bounds. -/
theorem tangentRequestCollisionMass_le_sum_endpointBudgetQuotients
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (lists : Request → Finset ℕ)
    (hlist : ∀ request, (lists request).Nonempty)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request, lowerCard request ≤ (lists request).card)
    (N : ℕ) (source target : Request → ℕ)
    (hprime : ∀ request side,
      (tangentEndpointLabel source target side request).Prime)
    (hupper : ∀ request side multiplier,
      multiplier ∈ lists request →
        tangentEndpointLabel source target side request * multiplier ≤ N)
    (request : Request) :
    tangentRequestCollisionMass lists hlist source target request ≤
      ∑ other ∈ Finset.univ.erase request,
        tangentPairEndpointBudgetQuotient
          lowerCard N source target request other := by
  rw [tangentRequestCollisionMass_eq_sum_otherRequests]
  exact Finset.sum_le_sum fun other _hother ↦
    tangentPairCollisionProbability_le_budgetQuotient
      lists hlist lowerCard hlowerPos hlower N source target
        hprime hupper request other

/-! ## Specialization to the actual clean common lists -/

/-- Every endpoint of an actual clean-list member is below the broad cutoff.
This is a deterministic consequence of membership in the literal interval. -/
theorem tangentCleanMultiplierLists_endpoint_le_broadUpper
    {Request : Type*}
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hpositive : ∀ request,
      0 < source request ∧ 0 < target request)
    (request : Request) (side : TangentEndpointSide)
    (multiplier : ℕ)
    (hmultiplier : multiplier ∈
      tangentCleanMultiplierLists n K h Phead X0 y source target
        dedicatedRows numericalGuards request) :
    tangentEndpointLabel source target side request * multiplier ≤
      tangentBroadUpper n K h := by
  have hdata := mem_tangentCleanCommonMultiplierList.mp hmultiplier
  have hmaxPos : 0 < max (source request) (target request) := by
    exact lt_of_lt_of_le (hpositive request).1 (le_max_left _ _)
  have hmaxUpper : max (source request) (target request) * multiplier ≤
      tangentBroadUpper n K h := by
    have hbound := (Nat.le_div_iff_mul_le hmaxPos).mp hdata.1.2
    simpa only [Nat.mul_comm] using hbound
  cases side
  · exact (Nat.mul_le_mul_right multiplier (le_max_left _ _)).trans
      hmaxUpper
  · exact (Nat.mul_le_mul_right multiplier (le_max_right _ _)).trans
      hmaxUpper

/-- For the actual clean lists, the exact incident collision mass is bounded
by a sum containing only the four-equation integer budgets and the supplied
list cardinality lower bounds. -/
theorem tangentCleanRequestCollisionMass_le_sum_endpointBudgetQuotients
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards request).card)
    (hprime : ∀ request,
      (source request).Prime ∧ (target request).Prime)
    (request : Request) :
    tangentRequestCollisionMass
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards)
        (fun r ↦ Finset.card_pos.mp ((hlowerPos r).trans_le (hlower r)))
        source target request ≤
      ∑ other ∈ Finset.univ.erase request,
        tangentPairEndpointBudgetQuotient lowerCard
          (tangentBroadUpper n K h) source target request other := by
  let lists := tangentCleanMultiplierLists
    n K h Phead X0 y source target dedicatedRows numericalGuards
  let hlist : ∀ r, (lists r).Nonempty :=
    fun r ↦ Finset.card_pos.mp ((hlowerPos r).trans_le (hlower r))
  exact tangentRequestCollisionMass_le_sum_endpointBudgetQuotients
    lists hlist lowerCard hlowerPos hlower (tangentBroadUpper n K h)
      source target
      (by
        intro r side
        cases side
        · exact (hprime r).1
        · exact (hprime r).2)
      (by
        intro r side multiplier hmultiplier
        exact tangentCleanMultiplierLists_endpoint_le_broadUpper
          n K h Phead X0 y source target dedicatedRows numericalGuards
          (fun r ↦ ⟨(hprime r).1.pos, (hprime r).2.pos⟩)
          r side multiplier hmultiplier)
      request

/-- Literal `1/8` consequence of the exact finite counting sum.  Apart from
primality, its structural input is only the request-wise clean-list
cardinality lower bound. -/
theorem tangentCleanRequestCollisionMass_le_eighth_of_exactCounting
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards request).card)
    (hprime : ∀ request,
      (source request).Prime ∧ (target request).Prime)
    (hcounting : ∀ request,
      (∑ other ∈ Finset.univ.erase request,
        tangentPairEndpointBudgetQuotient lowerCard
          (tangentBroadUpper n K h) source target request other) ≤ 1 / 8) :
    ∀ request,
      tangentRequestCollisionMass
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards)
        (fun r ↦ Finset.card_pos.mp ((hlowerPos r).trans_le (hlower r)))
        source target request ≤ 1 / 8 := by
  intro request
  exact (tangentCleanRequestCollisionMass_le_sum_endpointBudgetQuotients
    n K h Phead X0 y source target dedicatedRows numericalGuards
      lowerCard hlowerPos hlower hprime request).trans (hcounting request)

/-- Collision-free clean-list selection from the exact finite counting sum;
no collision probability or collision-free assignment is an input. -/
theorem tangentCleanCommonMultiplier_collisionFree_of_exactCounting
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ request, source request ≠ target request)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards request).card)
    (hprime : ∀ request,
      (source request).Prime ∧ (target request).Prime)
    (hcounting : ∀ request,
      (∑ other ∈ Finset.univ.erase request,
        tangentPairEndpointBudgetQuotient lowerCard
          (tangentBroadUpper n K h) source target request other) ≤ 1 / 8) :
    ∃ multiplier : Request → ℕ,
      (∀ request,
        multiplier request ∈ tangentCleanCommonMultiplierList
          n K h Phead X0 y
            (max (source request) (target request))
            (min (source request) (target request))
            dedicatedRows numericalGuards) ∧
      TangentEndpointsDistinct Finset.univ source target multiplier := by
  let hlist : ∀ request,
      (tangentCleanMultiplierLists n K h Phead X0 y source target
        dedicatedRows numericalGuards request).Nonempty :=
    fun request ↦ Finset.card_pos.mp
      ((hlowerPos request).trans_le (hlower request))
  apply tangentCleanCommonMultiplier_collisionFree_of_requestMass
    n K h Phead X0 y source target dedicatedRows numericalGuards
      hsourceTarget hlist
  exact tangentCleanRequestCollisionMass_le_eighth_of_exactCounting
    n K h Phead X0 y source target dedicatedRows numericalGuards
      lowerCard hlowerPos hlower hprime hcounting

/-- Actual clean-list request-mass bound.  The only list-size premise is the
displayed request-wise cardinality lower bound.  `hpairArithmetic` is a
finite arithmetic comparison between the explicit four-equation quotient
and the chosen disjoint/shared charges; it contains no probability and no
existence assertion. -/
theorem tangentCleanRequestCollisionMass_le_loadBudget
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards request).card)
    (hprime : ∀ request,
      (source request).Prime ∧ (target request).Prime)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          source target left right : ℝ) /
        (lowerCard left * lowerCard right) ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (request : Request) :
    tangentRequestCollisionMass
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards)
        (fun r ↦ Finset.card_pos.mp ((hlowerPos r).trans_le (hlower r)))
        source target request ≤
      (tangentOtherRequestCount request : ℝ) * disjointCharge +
        (tangentOtherRequestLabelLoad source target request
          (source request) : ℝ) * sharedCharge (source request) +
        (tangentOtherRequestLabelLoad source target request
          (target request) : ℝ) * sharedCharge (target request) := by
  let lists := tangentCleanMultiplierLists
    n K h Phead X0 y source target dedicatedRows numericalGuards
  let hlist : ∀ request, (lists request).Nonempty :=
    fun request ↦ Finset.card_pos.mp
      ((hlowerPos request).trans_le (hlower request))
  apply tangentRequestCollisionMass_le_loadBudget
    lists hlist source target disjointCharge sharedCharge
  intro left right hne
  refine (tangentPairCollisionProbability_le_budgetQuotient
    lists hlist lowerCard hlowerPos hlower
      (tangentBroadUpper n K h) source target
      (by
        intro r side
        cases side
        · exact (hprime r).1
        · exact (hprime r).2)
      (by
        intro r side multiplier hmultiplier
        exact tangentCleanMultiplierLists_endpoint_le_broadUpper
          n K h Phead X0 y source target dedicatedRows numericalGuards
          (fun r ↦ ⟨(hprime r).1.pos, (hprime r).2.pos⟩)
          r side multiplier hmultiplier)
      left right).trans ?_
  rw [tangentPairEndpointBudgetQuotient, dif_pos hne]
  exact hpairArithmetic left right hne

/-- Literal `1/8` conclusion obtained from list cardinalities, the four
endpoint-equation counts, and the two endpoint-label request loads.  The
final premise is an explicit numerical inequality between those displayed
quantities; it is not a collision-mass assumption. -/
theorem tangentCleanRequestCollisionMass_le_eighth_of_counting
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards request).card)
    (hprime : ∀ request,
      (source request).Prime ∧ (target request).Prime)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          source target left right : ℝ) /
        (lowerCard left * lowerCard right) ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (hload : ∀ request,
      (tangentOtherRequestCount request : ℝ) * disjointCharge +
          (tangentOtherRequestLabelLoad source target request
            (source request) : ℝ) * sharedCharge (source request) +
          (tangentOtherRequestLabelLoad source target request
            (target request) : ℝ) * sharedCharge (target request) ≤
        1 / 8) :
    ∀ request,
      tangentRequestCollisionMass
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards)
        (fun r ↦ Finset.card_pos.mp ((hlowerPos r).trans_le (hlower r)))
        source target request ≤ 1 / 8 := by
  intro request
  exact (tangentCleanRequestCollisionMass_le_loadBudget
    n K h Phead X0 y source target dedicatedRows numericalGuards
      lowerCard hlowerPos hlower hprime disjointCharge sharedCharge
      hpairArithmetic request).trans (hload request)

/-- Collision-free multiplier selection with the old probability hypothesis
replaced by explicit list cardinalities, four-equation arithmetic, and
request-load arithmetic. -/
theorem tangentCleanCommonMultiplier_collisionFree_of_counting
    {Request : Type*} [Fintype Request] [DecidableEq Request]
    (n K h Phead X0 y : ℕ) (source target : Request → ℕ)
    (dedicatedRows numericalGuards : Finset ℕ)
    (hsourceTarget : ∀ request, source request ≠ target request)
    (lowerCard : Request → ℕ)
    (hlowerPos : ∀ request, 0 < lowerCard request)
    (hlower : ∀ request,
      lowerCard request ≤
        (tangentCleanMultiplierLists n K h Phead X0 y source target
          dedicatedRows numericalGuards request).card)
    (hprime : ∀ request,
      (source request).Prime ∧ (target request).Prime)
    (disjointCharge : ℝ) (sharedCharge : ℕ → ℝ)
    (hpairArithmetic : ∀ left right, ∀ _hne : left ≠ right,
      (tangentOrderedPairEndpointBudget (tangentBroadUpper n K h)
          source target left right : ℝ) /
        (lowerCard left * lowerCard right) ≤
        disjointCharge +
          (if tangentRequestHasLabel source target (source left) right
            then sharedCharge (source left) else 0) +
          (if tangentRequestHasLabel source target (target left) right
            then sharedCharge (target left) else 0))
    (hload : ∀ request,
      (tangentOtherRequestCount request : ℝ) * disjointCharge +
          (tangentOtherRequestLabelLoad source target request
            (source request) : ℝ) * sharedCharge (source request) +
          (tangentOtherRequestLabelLoad source target request
            (target request) : ℝ) * sharedCharge (target request) ≤
        1 / 8) :
    ∃ multiplier : Request → ℕ,
      (∀ request,
        multiplier request ∈ tangentCleanCommonMultiplierList
          n K h Phead X0 y
            (max (source request) (target request))
            (min (source request) (target request))
            dedicatedRows numericalGuards) ∧
      TangentEndpointsDistinct Finset.univ source target multiplier := by
  let hlist : ∀ request,
      (tangentCleanMultiplierLists n K h Phead X0 y source target
        dedicatedRows numericalGuards request).Nonempty :=
    fun request ↦ Finset.card_pos.mp
      ((hlowerPos request).trans_le (hlower request))
  apply tangentCleanCommonMultiplier_collisionFree_of_requestMass
    n K h Phead X0 y source target dedicatedRows numericalGuards
      hsourceTarget hlist
  exact tangentCleanRequestCollisionMass_le_eighth_of_counting
    n K h Phead X0 y source target dedicatedRows numericalGuards
      lowerCard hlowerPos hlower hprime disjointCharge sharedCharge
      hpairArithmetic hload

end

end Erdos390.WholePaper
