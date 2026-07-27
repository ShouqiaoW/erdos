import Erdos536.PrimeBandFirstMoment
import Erdos536.QuadraticPrimeBand
import Erdos536.PrimeBandBase

/-!
# Adaptive singleton anchors in a finite prime band

This file isolates the exact finite first-moment calculation for two
configuration-dependent singleton anchors.  A background configuration
is required to leave an anchor reservoir unused.  Replacing two distinct
reservoir points by two distinct active labels is injective, and multiplies
the collision-free Poisson-compatible weight by the product of the two
one-label intensities.

Consequently, two adaptive anchor windows contribute the product of their
intensities, with only the same-prime diagonal removed.  The final theorems
package this as a quantitative compatible-law lower bound and transfer it
to the reciprocal categorical law with the explicit prime-tail error.
-/

open scoped BigOperators
open Finset
open Filter Topology

namespace Erdos536

open PrimeSums

theorem prod_two_update_mul
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) {i j : ι} (hij : i ≠ j) (a b : ℝ) :
    (∏ k, Function.update
        (Function.update f i (f i * a)) j (f j * b) k) =
      (∏ k, f k) * a * b := by
  have hi : i ∈ (Finset.univ \ {j} : Finset ι) := by
    simp [hij]
  rw [Finset.prod_update_of_mem (Finset.mem_univ j)]
  rw [Finset.prod_update_of_mem hi]
  rw [Finset.prod_eq_mul_prod_diff_singleton (Finset.mem_univ j)]
  rw [Finset.prod_eq_mul_prod_diff_singleton hi]
  ring

theorem sum_two_update_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℝ) {i j : ι} (hij : i ≠ j) (a b : ℝ) :
    (∑ k, Function.update
        (Function.update f i (f i + a)) j (f j + b) k) =
      (∑ k, f k) + a + b := by
  have hi : i ∈ (Finset.univ \ {j} : Finset ι) := by
    simp [hij]
  rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
  rw [Finset.sum_update_of_mem hi]
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j)]
  rw [Finset.sum_eq_add_sum_diff_singleton hi]
  ring

def twoAnchorCompletion
    {α : Type*} [DecidableEq α] {P : Finset α}
    (c : FiveConfiguration P) (px py : ↥P)
    (lx ly : FiveLabel) : FiveConfiguration P :=
  Function.update (Function.update c px lx) py ly

theorem fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal
    (R : Finset ℕ) (T : ℝ)
    (c : FiveConfiguration R) (s : Fin 3) :
    fivePetalNormalizedTotal R T c s =
      fiveLabelWeightedTotal R
        (normalizedLogWeight T) (petalLabel s) c := by
  unfold fivePetalNormalizedTotal
    fiveActiveLabelNormalizedTotal
    fiveActiveLabelSubtype
    fiveLabelWeightedTotal
  rw [Finset.sum_filter]
  simp [activeFiveLabel]

theorem fiveLabelWeightedTotal_twoAnchor_left
    {α : Type*} [DecidableEq α] (P : Finset α)
    (u : α → ℝ) (c : FiveConfiguration P)
    {px py : ↥P} (hxy : px ≠ py)
    {lx ly : FiveLabel} (hlx0 : lx ≠ 0)
    (hlyx : ly ≠ lx)
    (hcx : c px = 0) (hcy : c py = 0) :
    fiveLabelWeightedTotal P u lx
        (twoAnchorCompletion c px py lx ly) =
      fiveLabelWeightedTotal P u lx c + u px.1 := by
  classical
  let f : ↥P → ℝ :=
    fun p ↦ if c p = lx then u p.1 else 0
  have hfun :
      (fun p : ↥P ↦
          if twoAnchorCompletion c px py lx ly p = lx
          then u p.1 else 0) =
        Function.update
          (Function.update f px (f px + u px.1))
          py (f py + 0) := by
    funext p
    by_cases hpY : p = py
    · subst p
      simp [twoAnchorCompletion, f, hlyx, hcy, Ne.symm hlx0]
    · by_cases hpX : p = px
      · subst p
        simp [twoAnchorCompletion, f, hxy, hcx, Ne.symm hlx0]
      · simp [twoAnchorCompletion, f, hpX, hpY]
  unfold fiveLabelWeightedTotal
  rw [hfun]
  simpa using sum_two_update_add f hxy (u px.1) 0

theorem fiveLabelWeightedTotal_twoAnchor_right
    {α : Type*} [DecidableEq α] (P : Finset α)
    (u : α → ℝ) (c : FiveConfiguration P)
    {px py : ↥P} (hxy : px ≠ py)
    {lx ly : FiveLabel} (hly0 : ly ≠ 0)
    (hlxy : lx ≠ ly)
    (hcx : c px = 0) (hcy : c py = 0) :
    fiveLabelWeightedTotal P u ly
        (twoAnchorCompletion c px py lx ly) =
      fiveLabelWeightedTotal P u ly c + u py.1 := by
  classical
  let f : ↥P → ℝ :=
    fun p ↦ if c p = ly then u p.1 else 0
  have hfun :
      (fun p : ↥P ↦
          if twoAnchorCompletion c px py lx ly p = ly
          then u p.1 else 0) =
        Function.update
          (Function.update f px (f px + 0))
          py (f py + u py.1) := by
    funext p
    by_cases hpY : p = py
    · subst p
      simp [twoAnchorCompletion, f, hcy, Ne.symm hly0]
    · by_cases hpX : p = px
      · subst p
        simp [twoAnchorCompletion, f, hxy, hlxy, hcx,
          Ne.symm hly0]
      · simp [twoAnchorCompletion, f, hpX, hpY]
  unfold fiveLabelWeightedTotal
  rw [hfun]
  simpa using sum_two_update_add f hxy 0 (u py.1)

theorem fiveLabelWeightedTotal_twoAnchor_other
    {α : Type*} [DecidableEq α] (P : Finset α)
    (u : α → ℝ) (c : FiveConfiguration P)
    {px py : ↥P} (hxy : px ≠ py)
    {lx ly lz : FiveLabel}
    (hlz0 : lz ≠ 0) (hxlz : lx ≠ lz) (hylz : ly ≠ lz)
    (hcx : c px = 0) (hcy : c py = 0) :
    fiveLabelWeightedTotal P u lz
        (twoAnchorCompletion c px py lx ly) =
      fiveLabelWeightedTotal P u lz c := by
  classical
  let f : ↥P → ℝ :=
    fun p ↦ if c p = lz then u p.1 else 0
  have hfun :
      (fun p : ↥P ↦
          if twoAnchorCompletion c px py lx ly p = lz
          then u p.1 else 0) =
        Function.update
          (Function.update f px (f px + 0))
          py (f py + 0) := by
    funext p
    by_cases hpY : p = py
    · subst p
      simp [twoAnchorCompletion, f, hylz, hcy, Ne.symm hlz0]
    · by_cases hpX : p = px
      · subst p
        simp [twoAnchorCompletion, f, hxy, hxlz, hcx,
          Ne.symm hlz0]
      · simp [twoAnchorCompletion, f, hpX, hpY]
  unfold fiveLabelWeightedTotal
  rw [hfun]
  change
    (∑ p, Function.update
      (Function.update f px (f px + 0)) py (f py + 0) p) =
        ∑ p, f p
  simpa only [add_zero] using sum_two_update_add f hxy 0 0

theorem fivePetalNormalizedTotal_twoAnchor_zero
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    {px py : ↥R} (hxy : px ≠ py)
    (hcx : c px = 0) (hcy : c py = 0) :
    fivePetalNormalizedTotal R T
        (twoAnchorCompletion c px py
          (petalLabel 0) (petalLabel 1)) 0 =
      fivePetalNormalizedTotal R T c 0 +
        normalizedLogWeight T px.1 := by
  rw [fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal,
    fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal]
  exact fiveLabelWeightedTotal_twoAnchor_left
    R (normalizedLogWeight T) c hxy
      (by decide) (by decide) hcx hcy

theorem fivePetalNormalizedTotal_twoAnchor_one
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    {px py : ↥R} (hxy : px ≠ py)
    (hcx : c px = 0) (hcy : c py = 0) :
    fivePetalNormalizedTotal R T
        (twoAnchorCompletion c px py
          (petalLabel 0) (petalLabel 1)) 1 =
      fivePetalNormalizedTotal R T c 1 +
        normalizedLogWeight T py.1 := by
  rw [fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal,
    fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal]
  exact fiveLabelWeightedTotal_twoAnchor_right
    R (normalizedLogWeight T) c hxy
      (by decide) (by decide) hcx hcy

theorem fivePetalNormalizedTotal_twoAnchor_two
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    {px py : ↥R} (hxy : px ≠ py)
    (hcx : c px = 0) (hcy : c py = 0) :
    fivePetalNormalizedTotal R T
        (twoAnchorCompletion c px py
          (petalLabel 0) (petalLabel 1)) 2 =
      fivePetalNormalizedTotal R T c 2 := by
  rw [fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal,
    fivePetalNormalizedTotal_eq_fiveLabelWeightedTotal]
  exact fiveLabelWeightedTotal_twoAnchor_other
    R (normalizedLogWeight T) c hxy
      (by decide) (by decide) (by decide) hcx hcy

theorem three_close_to_center_interval_balance
    (v : Fin 3 → ℝ) {center lower upper δ w : ℝ}
    (hwidth : 2 * δ ≤ w)
    (hlower : lower + δ ≤ center)
    (hupper : center + δ ≤ upper)
    (hclose : ∀ s, |v s - center| ≤ δ) :
    (∀ s, lower ≤ v s ∧ v s ≤ upper) ∧
      ∀ s t, |v s - v t| ≤ w := by
  constructor
  · intro s
    have hs := abs_le.mp (hclose s)
    constructor <;> linarith
  · intro s t
    have hs := abs_le.mp (hclose s)
    have ht := abs_le.mp (hclose t)
    apply (abs_le.mpr ⟨?_, ?_⟩).trans hwidth
    · linarith
    · linarith

theorem twoAnchorCompletion_petal_interval_balance
    (R : Finset ℕ) (T lower upper δ w : ℝ)
    (c : FiveConfiguration R) {px py : ↥R}
    (hxy : px ≠ py) (hcx : c px = 0) (hcy : c py = 0)
    (hδ : 0 ≤ δ) (hwidth : 2 * δ ≤ w)
    (hlower :
      lower + δ ≤ fivePetalNormalizedTotal R T c 2)
    (hupper :
      fivePetalNormalizedTotal R T c 2 + δ ≤ upper)
    (hx :
      |fivePetalNormalizedTotal R T c 0 +
          normalizedLogWeight T px.1 -
        fivePetalNormalizedTotal R T c 2| ≤ δ)
    (hy :
      |fivePetalNormalizedTotal R T c 1 +
          normalizedLogWeight T py.1 -
        fivePetalNormalizedTotal R T c 2| ≤ δ) :
    (∀ s : Fin 3,
        lower ≤ fivePetalNormalizedTotal R T
            (twoAnchorCompletion c px py
              (petalLabel 0) (petalLabel 1)) s ∧
          fivePetalNormalizedTotal R T
            (twoAnchorCompletion c px py
              (petalLabel 0) (petalLabel 1)) s ≤ upper) ∧
      ∀ s t : Fin 3,
        |fivePetalNormalizedTotal R T
            (twoAnchorCompletion c px py
              (petalLabel 0) (petalLabel 1)) s -
          fivePetalNormalizedTotal R T
            (twoAnchorCompletion c px py
              (petalLabel 0) (petalLabel 1)) t| ≤ w := by
  apply three_close_to_center_interval_balance
    (fun s ↦ fivePetalNormalizedTotal R T
      (twoAnchorCompletion c px py
        (petalLabel 0) (petalLabel 1)) s)
    hwidth hlower hupper
  intro s
  fin_cases s
  · simpa [fivePetalNormalizedTotal_twoAnchor_zero
      R T c hxy hcx hcy] using hx
  · simpa [fivePetalNormalizedTotal_twoAnchor_one
      R T c hxy hcx hcy] using hy
  · simp [fivePetalNormalizedTotal_twoAnchor_two
      R T c hxy hcx hcy, hδ]

theorem poissonCompatibleConfigurationWeight_twoAnchorCompletion
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (c : FiveConfiguration P)
    {px py : ↥P} (hxy : px ≠ py)
    {lx ly : FiveLabel} (hlx : lx ≠ 0) (hly : ly ≠ 0)
    (hcx : c px = 0) (hcy : c py = 0) :
    poissonCompatibleConfigurationWeight P r
        (twoAnchorCompletion c px py lx ly) =
      poissonCompatibleConfigurationWeight P r c *
        (r px.1 / 3) * (r py.1 / 3) := by
  let f : ↥P → ℝ := fun p ↦
    collapsedPoissonCellWeight (r p.1) (some (c p))
  have hfun :
      (fun p : ↥P ↦
          collapsedPoissonCellWeight (r p.1)
            (some (twoAnchorCompletion c px py lx ly p))) =
        Function.update
          (Function.update f px (f px * (r px.1 / 3)))
          py (f py * (r py.1 / 3)) := by
    funext p
    by_cases hpY : p = py
    · subst p
      simp [twoAnchorCompletion, f, hcy,
        collapsedPoissonCellWeight, hly]
      ring
    · by_cases hpX : p = px
      · subst p
        simp [twoAnchorCompletion, f, hxy, hcx,
          collapsedPoissonCellWeight, hlx]
        ring
      · simp [twoAnchorCompletion, f, hpX, hpY]
  unfold poissonCompatibleConfigurationWeight
  rw [hfun]
  exact prod_two_update_mul f hxy _ _

abbrev TwoAnchorChoice
    {α : Type*} [DecidableEq α] (P : Finset α) :=
  FiveConfiguration P × (↥P × ↥P)

def completeTwoAnchorChoice
    {α : Type*} [DecidableEq α] {P : Finset α}
    (lx ly : FiveLabel) (z : TwoAnchorChoice P) :
    FiveConfiguration P :=
  twoAnchorCompletion z.1 z.2.1 z.2.2 lx ly

noncomputable def adaptiveTwoAnchorChoices
    {α : Type*} [DecidableEq α] {P : Finset α}
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P) :
    Finset (TwoAnchorChoice P) :=
  Finset.univ.filter fun z ↦
    z.1 ∈ Base ∧ z.2.1 ∈ Ix z.1 ∧
      z.2.2 ∈ Iy z.1 ∧ z.2.1 ≠ z.2.2

abbrev TwoAnchorSigmaChoice
    {α : Type*} [DecidableEq α] (P : Finset α) :=
  Σ _z : (Σ _c : FiveConfiguration P, ↥P), ↥P

def flattenTwoAnchorSigmaChoice
    {α : Type*} [DecidableEq α] {P : Finset α}
    (z : TwoAnchorSigmaChoice P) : TwoAnchorChoice P :=
  (z.1.1, (z.1.2, z.2))

theorem flattenTwoAnchorSigmaChoice_injective
    {α : Type*} [DecidableEq α] {P : Finset α} :
    Function.Injective
      (flattenTwoAnchorSigmaChoice (P := P)) := by
  rintro ⟨⟨c, x⟩, y⟩ ⟨⟨c', x'⟩, y'⟩ h
  simp only [flattenTwoAnchorSigmaChoice, Prod.mk.injEq] at h
  rcases h with ⟨hc, hx, hy⟩
  subst c'
  subst x'
  subst y'
  rfl

def flattenTwoAnchorSigmaChoiceEmbedding
    {α : Type*} [DecidableEq α] (P : Finset α) :
    TwoAnchorSigmaChoice P ↪ TwoAnchorChoice P :=
  ⟨flattenTwoAnchorSigmaChoice,
    flattenTwoAnchorSigmaChoice_injective⟩

noncomputable def adaptiveTwoAnchorSigmaChoices
    {α : Type*} [DecidableEq α] {P : Finset α}
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P) :
    Finset (TwoAnchorSigmaChoice P) :=
  (Base.sigma Ix).sigma fun z ↦
    (Iy z.1).filter fun py ↦ z.2 ≠ py

theorem adaptiveTwoAnchorSigmaChoices_map
    {α : Type*} [DecidableEq α] {P : Finset α}
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P) :
    (adaptiveTwoAnchorSigmaChoices Base Ix Iy).map
        (flattenTwoAnchorSigmaChoiceEmbedding P) =
      adaptiveTwoAnchorChoices Base Ix Iy := by
  classical
  ext z
  rw [Finset.mem_map]
  simp only [adaptiveTwoAnchorChoices, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨q, hq, hqz⟩
    rcases q with ⟨⟨c, x⟩, y⟩
    simp only [adaptiveTwoAnchorSigmaChoices, Finset.mem_sigma,
      Finset.mem_filter] at hq
    change (c, (x, y)) = z at hqz
    subst z
    exact ⟨hq.1.1, hq.1.2, hq.2.1, hq.2.2⟩
  · intro hz
    refine ⟨⟨⟨z.1, z.2.1⟩, z.2.2⟩, ?_, rfl⟩
    simp only [adaptiveTwoAnchorSigmaChoices, Finset.mem_sigma,
      Finset.mem_filter]
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2.1, hz.2.2.2⟩

theorem mem_adaptiveTwoAnchorChoices
    {α : Type*} [DecidableEq α] {P : Finset α}
    {Base : Finset (FiveConfiguration P)}
    {Ix Iy : FiveConfiguration P → Finset ↥P}
    {z : TwoAnchorChoice P} :
    z ∈ adaptiveTwoAnchorChoices Base Ix Iy ↔
      z.1 ∈ Base ∧ z.2.1 ∈ Ix z.1 ∧
        z.2.2 ∈ Iy z.1 ∧ z.2.1 ≠ z.2.2 := by
  classical
  simp [adaptiveTwoAnchorChoices]

def TwoAnchorBaseClean
    {α : Type*} [DecidableEq α] {P : Finset α}
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel) : Prop :=
  ∀ c ∈ Base,
    (∀ p ∈ K, c p ≠ lx ∧ c p ≠ ly) ∧
      (∀ p ∈ Ix c, c p = 0) ∧
      ∀ p ∈ Iy c, c p = 0

def unusedSubcarrier
    {α : Type*} [DecidableEq α] {P : Finset α}
    (c : FiveConfiguration P) (S : Finset ↥P) :
    Finset ↥P :=
  S.filter fun p ↦ c p = 0

@[simp]
theorem mem_unusedSubcarrier
    {α : Type*} [DecidableEq α] {P : Finset α}
    {c : FiveConfiguration P} {S : Finset ↥P} {p : ↥P} :
    p ∈ unusedSubcarrier c S ↔ p ∈ S ∧ c p = 0 := by
  simp [unusedSubcarrier]

theorem unusedSubcarrier_subset
    {α : Type*} [DecidableEq α] {P : Finset α}
    (c : FiveConfiguration P) (S : Finset ↥P) :
    unusedSubcarrier c S ⊆ S :=
  Finset.filter_subset _ _

theorem twoAnchorBaseClean_unusedSubcarriers
    {α : Type*} [DecidableEq α] {P : Finset α}
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Wx Wy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hfree : ∀ c ∈ Base, ∀ p ∈ K,
      c p ≠ lx ∧ c p ≠ ly) :
    TwoAnchorBaseClean K Base
      (fun c ↦ unusedSubcarrier c (Wx c))
      (fun c ↦ unusedSubcarrier c (Wy c)) lx ly := by
  intro c hc
  refine ⟨hfree c hc, ?_, ?_⟩
  · intro p hp
    exact (mem_unusedSubcarrier.mp hp).2
  · intro p hp
    exact (mem_unusedSubcarrier.mp hp).2

theorem unusedSubcarrier_subset_of_subset
    {α : Type*} [DecidableEq α] {P : Finset α}
    (c : FiveConfiguration P) {S K : Finset ↥P}
    (hSK : S ⊆ K) :
    unusedSubcarrier c S ⊆ K :=
  (unusedSubcarrier_subset c S).trans hSK

theorem sum_unusedSubcarrier_lower_of_card_nonzero_le_one
    {α : Type*} [DecidableEq α] {P : Finset α}
    (c : FiveConfiguration P) (S : Finset ↥P)
    (h : ↥P → ℝ) {e : ℝ}
    (he0 : 0 ≤ e)
    (hmax : ∀ p ∈ S, h p ≤ e)
    (hcard :
      ((S.filter fun p ↦ c p ≠ 0).card) ≤ 1) :
    (∑ p ∈ S, h p) - e ≤
      ∑ p ∈ unusedSubcarrier c S, h p := by
  let O : Finset ↥P := S.filter fun p ↦ c p ≠ 0
  have hOmax : ∀ p ∈ O, h p ≤ e := by
    intro p hp
    exact hmax p (Finset.mem_filter.mp hp).1
  have hOraw := Finset.sum_le_card_nsmul O h e hOmax
  have hcardR : (O.card : ℝ) ≤ 1 := by
    exact_mod_cast hcard
  have hO : (∑ p ∈ O, h p) ≤ e := by
    calc
      (∑ p ∈ O, h p) ≤ O.card • e := hOraw
      _ = (O.card : ℝ) * e := by simp
      _ ≤ 1 * e := mul_le_mul_of_nonneg_right hcardR he0
      _ = e := one_mul e
  have hsplit :
      (∑ p ∈ unusedSubcarrier c S, h p) +
          ∑ p ∈ O, h p =
        ∑ p ∈ S, h p := by
    simpa [unusedSubcarrier, O] using
      (Finset.sum_filter_add_sum_filter_not
        S (fun p ↦ c p = 0) h)
  linarith

theorem completeTwoAnchorChoice_injOn
    {α : Type*} [DecidableEq α] {P : Finset α}
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K) :
    Set.InjOn (completeTwoAnchorChoice lx ly)
      (↑(adaptiveTwoAnchorChoices Base Ix Iy) :
        Set (TwoAnchorChoice P)) := by
  classical
  intro z hz z' hz' heq
  change z ∈ adaptiveTwoAnchorChoices Base Ix Iy at hz
  change z' ∈ adaptiveTwoAnchorChoices Base Ix Iy at hz'
  rw [mem_adaptiveTwoAnchorChoices] at hz hz'
  have hzXK : z.2.1 ∈ K := hIx z.1 hz.1 hz.2.1
  have hzYK : z.2.2 ∈ K := hIy z.1 hz.1 hz.2.2.1
  have hx : z.2.1 = z'.2.1 := by
    by_contra hxx
    have hvalue := congrFun heq z.2.1
    have hleft :
        completeTwoAnchorChoice lx ly z z.2.1 = lx := by
      simp [completeTwoAnchorChoice, twoAnchorCompletion,
        hz.2.2.2]
    have hzBaseNotX : z'.1 z.2.1 ≠ lx :=
      ((hclean z'.1 hz'.1).1 z.2.1 hzXK).1
    by_cases hxy' : z.2.1 = z'.2.2
    · have hright :
          completeTwoAnchorChoice lx ly z' z.2.1 = ly := by
        rw [hxy']
        simp [completeTwoAnchorChoice, twoAnchorCompletion]
      rw [hleft, hright] at hvalue
      exact hlxy hvalue
    · have hright :
          completeTwoAnchorChoice lx ly z' z.2.1 =
            z'.1 z.2.1 := by
        simp [completeTwoAnchorChoice, twoAnchorCompletion,
          hxx, hxy']
      rw [hleft, hright] at hvalue
      exact hzBaseNotX hvalue.symm
  have hy : z.2.2 = z'.2.2 := by
    by_contra hyy
    have hvalue := congrFun heq z.2.2
    have hleft :
        completeTwoAnchorChoice lx ly z z.2.2 = ly := by
      simp [completeTwoAnchorChoice, twoAnchorCompletion]
    have hzBaseNotY : z'.1 z.2.2 ≠ ly :=
      ((hclean z'.1 hz'.1).1 z.2.2 hzYK).2
    have hyx : z.2.2 ≠ z'.2.1 := by
      rw [← hx]
      exact Ne.symm hz.2.2.2
    have hright :
        completeTwoAnchorChoice lx ly z' z.2.2 =
          z'.1 z.2.2 := by
      simp [completeTwoAnchorChoice, twoAnchorCompletion,
        hyy, hyx]
    rw [hleft, hright] at hvalue
    exact hzBaseNotY hvalue.symm
  have heqAligned :
      twoAnchorCompletion z.1 z.2.1 z.2.2 lx ly =
        twoAnchorCompletion z'.1 z.2.1 z.2.2 lx ly := by
    simpa only [completeTwoAnchorChoice, hx.symm, hy.symm] using heq
  have hbase : z.1 = z'.1 := by
    funext p
    by_cases hpX : p = z.2.1
    · subst p
      have hzZero :=
        (hclean z.1 hz.1).2.1 z.2.1 hz.2.1
      have hz'Zero :=
        (hclean z'.1 hz'.1).2.1 z'.2.1 hz'.2.1
      rw [← hx] at hz'Zero
      exact hzZero.trans hz'Zero.symm
    · by_cases hpY : p = z.2.2
      · subst p
        have hzZero :=
          (hclean z.1 hz.1).2.2 z.2.2 hz.2.2.1
        have hz'Zero :=
          (hclean z'.1 hz'.1).2.2 z'.2.2 hz'.2.2.1
        rw [← hy] at hz'Zero
        exact hzZero.trans hz'Zero.symm
      · have hvalue := congrFun heqAligned p
        simpa [twoAnchorCompletion, hpX, hpY] using hvalue
  apply Prod.ext hbase
  exact Prod.ext hx hy

noncomputable def adaptiveTwoAnchorCompletions
    {α : Type*} [DecidableEq α] {P : Finset α}
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel) :
    Finset (FiveConfiguration P) :=
  (adaptiveTwoAnchorChoices Base Ix Iy).image
    (completeTwoAnchorChoice lx ly)

theorem sum_adaptiveTwoAnchorChoices_weight
    {α : Type*} [DecidableEq α] {P : Finset α}
    (r : α → ℝ)
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly) :
    (∑ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
        poissonCompatibleConfigurationWeight P r
          (completeTwoAnchorChoice lx ly z)) =
      ∑ c ∈ Base, ∑ px ∈ Ix c,
        ∑ py ∈ (Iy c).filter (fun py ↦ px ≠ py),
          poissonCompatibleConfigurationWeight P r c *
            (r px.1 / 3) * (r py.1 / 3) := by
  classical
  rw [← adaptiveTwoAnchorSigmaChoices_map]
  rw [Finset.sum_map]
  rw [adaptiveTwoAnchorSigmaChoices, Finset.sum_sigma,
    Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro c hc
  apply Finset.sum_congr rfl
  intro px hpx
  apply Finset.sum_congr rfl
  intro py hpy
  have hpy' := Finset.mem_filter.mp hpy
  exact poissonCompatibleConfigurationWeight_twoAnchorCompletion
    P r c hpy'.2 hlx0 hly0
      ((hclean c hc).2.1 px hpx)
      ((hclean c hc).2.2 py hpy'.1)

theorem sum_adaptiveTwoAnchorCompletions_weight
    {α : Type*} [DecidableEq α] {P : Finset α}
    (r : α → ℝ)
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K) :
    (∑ c ∈ adaptiveTwoAnchorCompletions Base Ix Iy lx ly,
        poissonCompatibleConfigurationWeight P r c) =
      ∑ c ∈ Base, ∑ px ∈ Ix c,
        ∑ py ∈ (Iy c).filter (fun py ↦ px ≠ py),
          poissonCompatibleConfigurationWeight P r c *
            (r px.1 / 3) * (r py.1 / 3) := by
  classical
  rw [adaptiveTwoAnchorCompletions, Finset.sum_image]
  · exact sum_adaptiveTwoAnchorChoices_weight
      r K Base Ix Iy lx ly hlx0 hly0 hclean
  · intro z hz z' hz' heq
    exact completeTwoAnchorChoice_injOn
      K Base Ix Iy lx ly hlxy
      hclean hIx hIy hz hz' heq

theorem poissonCompatibleConfigurationWeight_nonneg
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (c : FiveConfiguration P) :
    0 ≤ poissonCompatibleConfigurationWeight P r c := by
  unfold poissonCompatibleConfigurationWeight
  apply Finset.prod_nonneg
  intro p _hp
  exact collapsedPoissonCellWeight_nonneg (hr0 p.1 p.2) _

theorem sum_adaptiveTwoAnchorCompletions_le_eventMass
    {α : Type*} [DecidableEq α] {P : Finset α}
    (r : α → ℝ) (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (B : FiveConfiguration P → Bool)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z)) :
    (∑ c ∈ adaptiveTwoAnchorCompletions Base Ix Iy lx ly,
        poissonCompatibleConfigurationWeight P r c) ≤
      poissonCompatibleEventMass P r B := by
  classical
  unfold poissonCompatibleEventMass
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro c hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ c, ?_⟩
    rw [adaptiveTwoAnchorCompletions, Finset.mem_image] at hc
    obtain ⟨z, hz, rfl⟩ := hc
    exact hB z hz
  · intro c _hc _hc'
    exact poissonCompatibleConfigurationWeight_nonneg P r hr0 c

theorem sum_filter_ne_lower
    {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) (x : ι) :
    (∑ y ∈ B, h y) - h x ≤
      ∑ y ∈ B.filter (fun y ↦ x ≠ y), h y := by
  have hfilter :
      B.filter (fun y ↦ x ≠ y) = B.erase x := by
    ext y
    simp [ne_comm, and_comm]
  rw [hfilter]
  by_cases hx : x ∈ B
  · have hsplit := Finset.add_sum_erase B h hx
    linarith
  · rw [Finset.erase_eq_of_notMem hx]
    linarith [hh x]

theorem distinct_pair_sum_lower
    {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) (h : ι → ℝ)
    (hh : ∀ i, 0 ≤ h i) :
    (∑ x ∈ A, h x) * (∑ y ∈ B, h y) -
        ∑ x ∈ A, (h x) ^ 2 ≤
      ∑ x ∈ A,
        ∑ y ∈ B.filter (fun y ↦ x ≠ y), h x * h y := by
  have hrewrite :
      (∑ x ∈ A, h x) * (∑ y ∈ B, h y) -
          ∑ x ∈ A, (h x) ^ 2 =
        ∑ x ∈ A, h x * ((∑ y ∈ B, h y) - h x) := by
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro x _hx
    ring
  rw [hrewrite]
  apply Finset.sum_le_sum
  intro x _hx
  calc
    h x * ((∑ y ∈ B, h y) - h x) ≤
        h x * ∑ y ∈ B.filter (fun y ↦ x ≠ y), h y :=
      mul_le_mul_of_nonneg_left
        (sum_filter_ne_lower B h hh x) (hh x)
    _ = ∑ y ∈ B.filter (fun y ↦ x ≠ y), h x * h y := by
      rw [Finset.mul_sum]

theorem adaptiveTwoAnchorCompletions_weight_lower
    {α : Type*} [DecidableEq α] {P : Finset α}
    (r : α → ℝ) (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K) :
    (∑ c ∈ Base,
        poissonCompatibleConfigurationWeight P r c *
          ((∑ px ∈ Ix c, r px.1 / 3) *
              (∑ py ∈ Iy c, r py.1 / 3) -
            ∑ px ∈ Ix c, (r px.1 / 3) ^ 2)) ≤
      ∑ c ∈ adaptiveTwoAnchorCompletions Base Ix Iy lx ly,
        poissonCompatibleConfigurationWeight P r c := by
  classical
  rw [sum_adaptiveTwoAnchorCompletions_weight
    r K Base Ix Iy lx ly hlx0 hly0 hlxy hclean hIx hIy]
  apply Finset.sum_le_sum
  intro c hc
  let h : ↥P → ℝ := fun p ↦ r p.1 / 3
  have hh : ∀ p : ↥P, 0 ≤ h p := fun p ↦ by
    dsimp [h]
    exact div_nonneg (hr0 p.1 p.2) (by norm_num)
  have hpairs := distinct_pair_sum_lower (Ix c) (Iy c) h hh
  have hw :
      0 ≤ poissonCompatibleConfigurationWeight P r c :=
    poissonCompatibleConfigurationWeight_nonneg P r hr0 c
  calc
    poissonCompatibleConfigurationWeight P r c *
        ((∑ px ∈ Ix c, r px.1 / 3) *
            (∑ py ∈ Iy c, r py.1 / 3) -
          ∑ px ∈ Ix c, (r px.1 / 3) ^ 2) ≤
      poissonCompatibleConfigurationWeight P r c *
        ∑ px ∈ Ix c,
          ∑ py ∈ (Iy c).filter (fun py ↦ px ≠ py),
            (r px.1 / 3) * (r py.1 / 3) := by
        exact mul_le_mul_of_nonneg_left hpairs hw
    _ = ∑ px ∈ Ix c,
        ∑ py ∈ (Iy c).filter (fun py ↦ px ≠ py),
          poissonCompatibleConfigurationWeight P r c *
            (r px.1 / 3) * (r py.1 / 3) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro px _hpx
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro py _hpy
      ring

theorem poissonCompatibleEventMass_adaptiveTwoAnchor_lower
    {α : Type*} [DecidableEq α] {P : Finset α}
    (r : α → ℝ) (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (B : FiveConfiguration P → Bool)
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z))
    {b mx my D : ℝ}
    (hbase : b ≤ ∑ c ∈ Base,
      poissonCompatibleConfigurationWeight P r c)
    (hmy0 : 0 ≤ my)
    (hX : ∀ c ∈ Base, mx ≤ ∑ p ∈ Ix c, r p.1 / 3)
    (hY : ∀ c ∈ Base, my ≤ ∑ p ∈ Iy c, r p.1 / 3)
    (hdiag : ∀ c ∈ Base,
      (∑ p ∈ Ix c, (r p.1 / 3) ^ 2) ≤ D)
    (hanchor : 0 ≤ mx * my - D) :
    b * (mx * my - D) ≤
      poissonCompatibleEventMass P r B := by
  classical
  have hstructured :=
    adaptiveTwoAnchorCompletions_weight_lower
      r hr0 K Base Ix Iy lx ly
      hlx0 hly0 hlxy hclean hIx hIy
  have hevent :=
    sum_adaptiveTwoAnchorCompletions_le_eventMass
      r hr0 B Base Ix Iy lx ly hB
  calc
    b * (mx * my - D) ≤
        (∑ c ∈ Base,
          poissonCompatibleConfigurationWeight P r c) *
            (mx * my - D) :=
      mul_le_mul_of_nonneg_right hbase hanchor
    _ = ∑ c ∈ Base,
        poissonCompatibleConfigurationWeight P r c *
          (mx * my - D) := by
      rw [Finset.sum_mul]
    _ ≤ ∑ c ∈ Base,
        poissonCompatibleConfigurationWeight P r c *
          ((∑ px ∈ Ix c, r px.1 / 3) *
              (∑ py ∈ Iy c, r py.1 / 3) -
            ∑ px ∈ Ix c, (r px.1 / 3) ^ 2) := by
      apply Finset.sum_le_sum
      intro c hc
      have hsumX0 :
          0 ≤ ∑ p ∈ Ix c, r p.1 / 3 := by
        apply Finset.sum_nonneg
        intro p _hp
        exact div_nonneg (hr0 p.1 p.2) (by norm_num)
      have hprod :
          mx * my ≤
            (∑ p ∈ Ix c, r p.1 / 3) *
              ∑ p ∈ Iy c, r p.1 / 3 :=
        mul_le_mul (hX c hc) (hY c hc) hmy0 hsumX0
      have hfactor :
          mx * my - D ≤
            (∑ p ∈ Ix c, r p.1 / 3) *
                (∑ p ∈ Iy c, r p.1 / 3) -
              ∑ p ∈ Ix c, (r p.1 / 3) ^ 2 := by
        linarith [hdiag c hc]
      exact mul_le_mul_of_nonneg_left hfactor
        (poissonCompatibleConfigurationWeight_nonneg P r hr0 c)
    _ ≤ ∑ c ∈ adaptiveTwoAnchorCompletions Base Ix Iy lx ly,
        poissonCompatibleConfigurationWeight P r c :=
      hstructured
    _ ≤ poissonCompatibleEventMass P r B := hevent

theorem poissonCompatibleEventMass_adaptiveTwoAnchor_lower_of_reservoir
    {α : Type*} [DecidableEq α] {P : Finset α}
    (r : α → ℝ) (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (B : FiveConfiguration P → Bool)
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z))
    {b mx my D : ℝ}
    (hbase : b ≤ ∑ c ∈ Base,
      poissonCompatibleConfigurationWeight P r c)
    (hmy0 : 0 ≤ my)
    (hX : ∀ c ∈ Base, mx ≤ ∑ p ∈ Ix c, r p.1 / 3)
    (hY : ∀ c ∈ Base, my ≤ ∑ p ∈ Iy c, r p.1 / 3)
    (hreservoir :
      (∑ p ∈ K, (r p.1 / 3) ^ 2) ≤ D)
    (hanchor : 0 ≤ mx * my - D) :
    b * (mx * my - D) ≤
      poissonCompatibleEventMass P r B := by
  apply poissonCompatibleEventMass_adaptiveTwoAnchor_lower
    r hr0 B K Base Ix Iy lx ly
    hlx0 hly0 hlxy hclean hIx hIy hB
    hbase hmy0 hX hY
  · intro c hc
    calc
      (∑ p ∈ Ix c, (r p.1 / 3) ^ 2) ≤
          ∑ p ∈ K, (r p.1 / 3) ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg (hIx c hc)
        intro p _hpK _hpIx
        positivity
      _ ≤ D := hreservoir
  · exact hanchor

theorem poissonCompatibleEventMass_adaptiveTwoAnchor_square_lower
    {α : Type*} [DecidableEq α] {P : Finset α}
    (r : α → ℝ) (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (B : FiveConfiguration P → Bool)
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z))
    {b m : ℝ}
    (hbase : b ≤ ∑ c ∈ Base,
      poissonCompatibleConfigurationWeight P r c)
    (hm0 : 0 ≤ m)
    (hX : ∀ c ∈ Base, m ≤ ∑ p ∈ Ix c, r p.1 / 3)
    (hY : ∀ c ∈ Base, m ≤ ∑ p ∈ Iy c, r p.1 / 3)
    (hreservoir :
      (∑ p ∈ K, (r p.1 / 3) ^ 2) ≤ m ^ 2 / 2) :
    b * (m ^ 2 / 2) ≤
      poissonCompatibleEventMass P r B := by
  have h := poissonCompatibleEventMass_adaptiveTwoAnchor_lower_of_reservoir
    r hr0 B K Base Ix Iy lx ly
    hlx0 hly0 hlxy hclean hIx hIy hB
    hbase hm0 hX hY hreservoir
    (show 0 ≤ m * m - m ^ 2 / 2 by nlinarith [sq_nonneg m])
  rw [show m * m - m ^ 2 / 2 = m ^ 2 / 2 by ring] at h
  exact h

theorem reciprocalFiveEventMass_adaptiveTwoAnchor_square_lower
    {P : Finset ℕ} (hP : IsPrimeSupport P)
    {A : ℕ} (hA : 1 ≤ A)
    (habove : ∀ p ∈ P, A < p)
    (B : FiveConfiguration P → Bool)
    (K : Finset ↥P)
    (Base : Finset (FiveConfiguration P))
    (Ix Iy : FiveConfiguration P → Finset ↥P)
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z))
    {b m : ℝ}
    (hbase : b ≤ ∑ c ∈ Base,
      poissonCompatibleConfigurationWeight P reciprocalBernoulli c)
    (hm0 : 0 ≤ m)
    (hX : ∀ c ∈ Base,
      m ≤ ∑ p ∈ Ix c, reciprocalBernoulli p.1 / 3)
    (hY : ∀ c ∈ Base,
      m ≤ ∑ p ∈ Iy c, reciprocalBernoulli p.1 / 3)
    (hreservoir :
      (∑ p ∈ K, (reciprocalBernoulli p.1 / 3) ^ 2) ≤
        m ^ 2 / 2) :
    b * (m ^ 2 / 2) - 16 / (9 * (A : ℝ)) ≤
      fiveEventMass P reciprocalBernoulli B := by
  apply reciprocalFiveEventMass_lower_transfer
    hP hA habove B
  exact poissonCompatibleEventMass_adaptiveTwoAnchor_square_lower
    reciprocalBernoulli
    (fun p _hp ↦ reciprocalBernoulli_nonneg p)
    B K Base Ix Iy lx ly
    hlx0 hly0 hlxy hclean hIx hIy hB
    hbase hm0 hX hY hreservoir

theorem normalizedLogWeight_mem_localPrimeBand_lower
    {N p : ℕ} {t h : ℝ}
    (hN : 0 < N)
    (hp : p ∈ LocalPrimeBand.localPrimeBand N t h) :
    t < normalizedLogWeight (N : ℝ) p := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpData := LocalPrimeBand.mem_localPrimeBand.mp hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
  have hexp :
      Real.exp ((N : ℝ) * t) < (p : ℝ) := by
    have hceil :
        Real.exp ((N : ℝ) * t) ≤
          (LocalPrimeBand.localLowerEndpoint N t : ℝ) := by
      exact Nat.le_ceil _
    have hpLower :
        (LocalPrimeBand.localLowerEndpoint N t : ℝ) <
          (p : ℝ) := by
      exact_mod_cast hpData.2.1
    exact hceil.trans_lt hpLower
  have hlog :
      (N : ℝ) * t < Real.log (p : ℝ) := by
    simpa only [Real.log_exp] using
      (Real.log_lt_log (Real.exp_pos _) hexp)
  rw [normalizedLogWeight]
  exact (lt_div_iff₀ hNR).2 (by
    simpa only [mul_comm] using hlog)

theorem normalizedLogWeight_mem_localPrimeBand_upper
    {N p : ℕ} {r₀ t h : ℝ}
    (hN : 0 < N) (hr₀t : r₀ ≤ t) (hh : 0 ≤ h)
    (hp : p ∈ LocalPrimeBand.localPrimeBand N t h) :
    normalizedLogWeight (N : ℝ) p <
      t + (h + 2 * Real.exp (-((N : ℝ) * r₀))) / (N : ℝ) := by
  let A := LocalPrimeBand.localLowerEndpoint N t
  let Y := LocalPrimeBand.localUpperEndpoint N t h
  let ε := Real.exp (-((N : ℝ) * r₀))
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hNt :
      (N : ℝ) * r₀ ≤ (N : ℝ) * t :=
    mul_le_mul_of_nonneg_left hr₀t hNR.le
  have hApos : (0 : ℝ) < A := by
    exact_mod_cast LocalPrimeBand.localLowerEndpoint_pos N t
  have hYpos : (0 : ℝ) < Y := by
    have hAY :
        A ≤ Y :=
      LocalPrimeBand.localLowerEndpoint_le_upper
        (T := N) (t := t) hh
    have hAposNat : 0 < A := by exact_mod_cast hApos
    exact_mod_cast hAposNat.trans_le hAY
  have hεpos : 0 < ε := Real.exp_pos _
  have hexpNtA :
      Real.exp ((N : ℝ) * t) ≤ (A : ℝ) := by
    exact Nat.le_ceil _
  have hexpNrA :
      Real.exp ((N : ℝ) * r₀) ≤ (A : ℝ) :=
    (Real.exp_le_exp.mpr hNt).trans hexpNtA
  have hinvA :
      1 / (A : ℝ) ≤ ε := by
    calc
      1 / (A : ℝ) ≤
          1 / Real.exp ((N : ℝ) * r₀) :=
        one_div_le_one_div_of_le (Real.exp_pos _) hexpNrA
      _ = ε := by
        rw [one_div, ← Real.exp_neg]
  have hexpNegNt :
      Real.exp (-((N : ℝ) * t)) ≤ ε :=
    Real.exp_le_exp.mpr (by linarith)
  have hAceil :
      (A : ℝ) <
        Real.exp ((N : ℝ) * t) + 1 := by
    dsimp [A]
    exact_mod_cast Nat.ceil_lt_add_one
      (Real.exp_nonneg ((N : ℝ) * t))
  have hAfactor :
      Real.exp ((N : ℝ) * t) + 1 =
        Real.exp ((N : ℝ) * t) *
          (1 + Real.exp (-((N : ℝ) * t))) := by
    rw [mul_add, mul_one, ← Real.exp_add]
    simp
  have honeNt :
      1 + Real.exp (-((N : ℝ) * t)) ≤
        Real.exp (Real.exp (-((N : ℝ) * t))) := by
    linarith [Real.add_one_le_exp
      (Real.exp (-((N : ℝ) * t)))]
  have hAupper :
      (A : ℝ) <
        Real.exp ((N : ℝ) * t + ε) := by
    apply hAceil.trans_le
    calc
      Real.exp ((N : ℝ) * t) + 1 =
          Real.exp ((N : ℝ) * t) *
            (1 + Real.exp (-((N : ℝ) * t))) := hAfactor
      _ ≤ Real.exp ((N : ℝ) * t) *
          Real.exp (Real.exp (-((N : ℝ) * t))) :=
        mul_le_mul_of_nonneg_left honeNt (Real.exp_nonneg _)
      _ ≤ Real.exp ((N : ℝ) * t) * Real.exp ε :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hexpNegNt) (Real.exp_nonneg _)
      _ = Real.exp ((N : ℝ) * t + ε) := by
        rw [Real.exp_add]
  have hlogA :
      Real.log (A : ℝ) <
        (N : ℝ) * t + ε := by
    simpa only [Real.log_exp] using
      (Real.log_lt_log hApos hAupper)
  have hexpNegH :
      Real.exp (-h) ≤ 1 := by
    simpa only [← Real.exp_zero] using
      (Real.exp_le_exp.mpr (neg_nonpos.mpr hh))
  have hqε :
      Real.exp (-h) / (A : ℝ) ≤ ε := by
    calc
      Real.exp (-h) / (A : ℝ) ≤ 1 / (A : ℝ) :=
        div_le_div_of_nonneg_right hexpNegH hApos.le
      _ ≤ ε := hinvA
  have hYceil :
      (Y : ℝ) <
        Real.exp h * (A : ℝ) + 1 := by
    dsimp [Y]
    exact_mod_cast Nat.ceil_lt_add_one
      (mul_nonneg (Real.exp_nonneg h) hApos.le)
  have hYfactor :
      Real.exp h * (A : ℝ) + 1 =
        Real.exp h * (A : ℝ) *
          (1 + Real.exp (-h) / (A : ℝ)) := by
    field_simp [hApos.ne']
    rw [mul_add, ← Real.exp_add]
    simp
  have honeH :
      1 + Real.exp (-h) / (A : ℝ) ≤
        Real.exp (Real.exp (-h) / (A : ℝ)) := by
    linarith [Real.add_one_le_exp
      (Real.exp (-h) / (A : ℝ))]
  have hYupper :
      (Y : ℝ) <
        Real.exp (h + ε) * (A : ℝ) := by
    apply hYceil.trans_le
    calc
      Real.exp h * (A : ℝ) + 1 =
          Real.exp h * (A : ℝ) *
            (1 + Real.exp (-h) / (A : ℝ)) := hYfactor
      _ ≤ Real.exp h * (A : ℝ) *
          Real.exp (Real.exp (-h) / (A : ℝ)) :=
        mul_le_mul_of_nonneg_left honeH
          (mul_nonneg (Real.exp_nonneg h) hApos.le)
      _ ≤ Real.exp h * (A : ℝ) * Real.exp ε :=
        mul_le_mul_of_nonneg_left
          (Real.exp_le_exp.mpr hqε)
          (mul_nonneg (Real.exp_nonneg h) hApos.le)
      _ = Real.exp (h + ε) * (A : ℝ) := by
        rw [Real.exp_add]
        ring
  have hlogY :
      Real.log (Y : ℝ) <
        h + ε + Real.log (A : ℝ) := by
    have hlog :=
      Real.log_lt_log hYpos hYupper
    rw [Real.log_mul (Real.exp_ne_zero _) hApos.ne',
      Real.log_exp] at hlog
    linarith
  have hpData := LocalPrimeBand.mem_localPrimeBand.mp hp
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpData.1.pos
  have hpY : (p : ℝ) ≤ (Y : ℝ) := by
    exact_mod_cast hpData.2.2
  have hlogp :
      Real.log (p : ℝ) <
        (N : ℝ) * t + h + 2 * ε := by
    have hpLogY : Real.log (p : ℝ) ≤ Real.log (Y : ℝ) :=
      Real.log_le_log hpR hpY
    linarith
  rw [normalizedLogWeight]
  apply (div_lt_iff₀ hNR).2
  dsimp [ε] at hlogp ⊢
  calc
    Real.log (p : ℝ) <
        (N : ℝ) * t + h +
          2 * Real.exp (-((N : ℝ) * r₀)) := hlogp
    _ = (t +
          (h + 2 * Real.exp (-((N : ℝ) * r₀))) / (N : ℝ)) *
        (N : ℝ) := by
      field_simp [hNR.ne']
      ring

noncomputable def quadraticLocalBandCarrier
    (T : ℕ) (a t h : ℝ) :
    Finset ↥(quadraticPrimeBand T a) :=
  Finset.univ.filter fun p ↦
    p.1 ∈ LocalPrimeBand.localPrimeBand (T ^ 2) t h

@[simp]
theorem mem_quadraticLocalBandCarrier
    {T : ℕ} {a t h : ℝ}
    {p : ↥(quadraticPrimeBand T a)} :
    p ∈ quadraticLocalBandCarrier T a t h ↔
      p.1 ∈ LocalPrimeBand.localPrimeBand (T ^ 2) t h := by
  simp [quadraticLocalBandCarrier]

theorem subtypeSupportVal_quadraticLocalBandCarrier
    {T : ℕ} {a t h : ℝ}
    (hsub : LocalPrimeBand.localPrimeBand (T ^ 2) t h ⊆
      quadraticPrimeBand T a) :
    subtypeSupportVal (quadraticLocalBandCarrier T a t h) =
      LocalPrimeBand.localPrimeBand (T ^ 2) t h := by
  ext p
  constructor
  · intro hp
    obtain ⟨_hpBand, hpCarrier⟩ :=
      mem_subtypeSupportVal.mp hp
    exact mem_quadraticLocalBandCarrier.mp hpCarrier
  · intro hp
    exact mem_subtypeSupportVal.mpr
      ⟨hsub hp, mem_quadraticLocalBandCarrier.mpr hp⟩

theorem sum_quadraticLocalBandCarrier_reciprocal_third
    {T : ℕ} {a t h : ℝ} (hh : 0 ≤ h)
    (hsub : LocalPrimeBand.localPrimeBand (T ^ 2) t h ⊆
      quadraticPrimeBand T a) :
    (∑ p ∈ quadraticLocalBandCarrier T a t h,
        reciprocalBernoulli p.1 / 3) =
      LocalPrimeBand.localBandShiftedReciprocalMass
        (T ^ 2) t h / 3 := by
  have hval :=
    subtypeSupportVal_quadraticLocalBandCarrier hsub
  have hsum :
      (∑ p ∈ quadraticLocalBandCarrier T a t h,
          1 / ((p.1 : ℝ) + 1)) =
        ∑ p ∈ LocalPrimeBand.localPrimeBand (T ^ 2) t h,
          1 / ((p : ℝ) + 1) := by
    rw [← hval, subtypeSupportVal, Finset.sum_map]
    rfl
  rw [LocalPrimeBand.localBandShiftedReciprocalMass_eq_sum hh]
  simp only [reciprocalBernoulli]
  rw [← Finset.sum_div]
  exact congrArg (fun x : ℝ ↦ x / 3) hsum

theorem reciprocalBernoulli_third_le_quadraticCutoff
    {T : ℕ} {a : ℝ} {p : ℕ}
    (hT : 1 ≤ T)
    (hp : p ∈ quadraticPrimeBand T a) :
    reciprocalBernoulli p / 3 ≤
      1 / (3 * (quadraticLowerCutoff T : ℝ)) := by
  have hpLower :=
    (mem_quadraticPrimeBand.mp hp).2.1
  have hAposNat :
      0 < quadraticLowerCutoff T :=
    zero_lt_one.trans_le (by
      unfold quadraticLowerCutoff
      exact one_le_pow₀ hT)
  have hdenomNat :
      quadraticLowerCutoff T ≤ p + 1 := by omega
  have hApos :
      (0 : ℝ) < quadraticLowerCutoff T := by
    exact_mod_cast hAposNat
  have hdenom :
      (quadraticLowerCutoff T : ℝ) ≤ (p : ℝ) + 1 := by
    exact_mod_cast hdenomNat
  have hrec :
      1 / ((p : ℝ) + 1) ≤
        1 / (quadraticLowerCutoff T : ℝ) :=
    one_div_le_one_div_of_le hApos hdenom
  rw [reciprocalBernoulli]
  calc
    1 / ((p : ℝ) + 1) / 3 ≤
        (1 / (quadraticLowerCutoff T : ℝ)) / 3 :=
      div_le_div_of_nonneg_right hrec (by norm_num)
    _ = 1 / (3 * (quadraticLowerCutoff T : ℝ)) := by ring

theorem sum_unused_quadraticLocalBandCarrier_lower
    {T : ℕ} {a t h : ℝ}
    (hT : 1 ≤ T)
    (c : FiveConfiguration (quadraticPrimeBand T a))
    (hh : 0 ≤ h)
    (hsub : LocalPrimeBand.localPrimeBand (T ^ 2) t h ⊆
      quadraticPrimeBand T a)
    (hcard :
      (((quadraticLocalBandCarrier T a t h).filter
        fun p ↦ c p ≠ 0).card) ≤ 1)
    {m : ℝ}
    (hm : m ≤
      LocalPrimeBand.localBandShiftedReciprocalMass
        (T ^ 2) t h / 3) :
    m - 1 / (3 * (quadraticLowerCutoff T : ℝ)) ≤
      ∑ p ∈ unusedSubcarrier c
          (quadraticLocalBandCarrier T a t h),
        reciprocalBernoulli p.1 / 3 := by
  have hApos :
      (0 : ℝ) < quadraticLowerCutoff T := by
    exact_mod_cast
      (zero_lt_one.trans_le (by
        unfold quadraticLowerCutoff
        exact one_le_pow₀ hT))
  have hloss :=
    sum_unusedSubcarrier_lower_of_card_nonzero_le_one
      c (quadraticLocalBandCarrier T a t h)
      (fun p ↦ reciprocalBernoulli p.1 / 3)
      (e := 1 / (3 * (quadraticLowerCutoff T : ℝ)))
      (by positivity)
      (fun p _hp ↦
        reciprocalBernoulli_third_le_quadraticCutoff hT p.2)
      hcard
  rw [sum_quadraticLocalBandCarrier_reciprocal_third
    hh hsub] at hloss
  exact (sub_le_sub_right hm _).trans hloss

theorem quadraticFiveEventMass_lower_transfer
    {T : ℕ} (hT : 1 ≤ T) (a : ℝ)
    (B : FiveConfiguration (quadraticPrimeBand T a) → Bool)
    {L : ℝ}
    (hL : L ≤ poissonCompatibleEventMass
      (quadraticPrimeBand T a) reciprocalBernoulli B) :
    L - 16 /
        (9 * (quadraticLowerCutoff T : ℝ)) ≤
      fiveEventMass
        (quadraticPrimeBand T a) reciprocalBernoulli B := by
  apply reciprocalFiveEventMass_lower_transfer
    (quadraticPrimeBand_prime T a)
    (by
      unfold quadraticLowerCutoff
      exact one_le_pow₀ hT)
    (fun p hp ↦ (mem_quadraticPrimeBand.mp hp).2.1)
    B hL

theorem quadraticFiveEventMass_adaptiveTwoAnchor_square_lower
    {T : ℕ} (hT : 1 ≤ T) (a : ℝ)
    (B : FiveConfiguration (quadraticPrimeBand T a) → Bool)
    (K : Finset ↥(quadraticPrimeBand T a))
    (Base : Finset
      (FiveConfiguration (quadraticPrimeBand T a)))
    (Ix Iy : FiveConfiguration (quadraticPrimeBand T a) →
      Finset ↥(quadraticPrimeBand T a))
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z))
    {b m : ℝ}
    (hbase : b ≤ ∑ c ∈ Base,
      poissonCompatibleConfigurationWeight
        (quadraticPrimeBand T a) reciprocalBernoulli c)
    (hm0 : 0 ≤ m)
    (hX : ∀ c ∈ Base,
      m ≤ ∑ p ∈ Ix c, reciprocalBernoulli p.1 / 3)
    (hY : ∀ c ∈ Base,
      m ≤ ∑ p ∈ Iy c, reciprocalBernoulli p.1 / 3)
    (hreservoir :
      (∑ p ∈ K, (reciprocalBernoulli p.1 / 3) ^ 2) ≤
        m ^ 2 / 2) :
    b * (m ^ 2 / 2) -
        16 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
      fiveEventMass
        (quadraticPrimeBand T a) reciprocalBernoulli B := by
  apply quadraticFiveEventMass_lower_transfer hT a B
  exact poissonCompatibleEventMass_adaptiveTwoAnchor_square_lower
    reciprocalBernoulli
    (fun p _hp ↦ reciprocalBernoulli_nonneg p)
    B K Base Ix Iy lx ly
    hlx0 hly0 hlxy hclean hIx hIy hB
    hbase hm0 hX hY hreservoir

theorem quadraticFiveEventMass_adaptiveTwoAnchor_square_lower_of_cutoff
    {T : ℕ} (hT : 1 ≤ T) (a : ℝ)
    (B : FiveConfiguration (quadraticPrimeBand T a) → Bool)
    (K : Finset ↥(quadraticPrimeBand T a))
    (Base : Finset
      (FiveConfiguration (quadraticPrimeBand T a)))
    (Ix Iy : FiveConfiguration (quadraticPrimeBand T a) →
      Finset ↥(quadraticPrimeBand T a))
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z))
    {b m : ℝ}
    (hbase : b ≤ ∑ c ∈ Base,
      poissonCompatibleConfigurationWeight
        (quadraticPrimeBand T a) reciprocalBernoulli c)
    (hm0 : 0 ≤ m)
    (hX : ∀ c ∈ Base,
      m ≤ ∑ p ∈ Ix c, reciprocalBernoulli p.1 / 3)
    (hY : ∀ c ∈ Base,
      m ≤ ∑ p ∈ Iy c, reciprocalBernoulli p.1 / 3)
    (hcutoffDiagonal :
      1 / (9 * (quadraticLowerCutoff T : ℝ)) ≤ m ^ 2 / 2) :
    b * (m ^ 2 / 2) -
        16 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
      fiveEventMass
        (quadraticPrimeBand T a) reciprocalBernoulli B := by
  apply quadraticFiveEventMass_adaptiveTwoAnchor_square_lower
    hT a B K Base Ix Iy lx ly
    hlx0 hly0 hlxy hclean hIx hIy hB
    hbase hm0 hX hY
  calc
    (∑ p ∈ K, (reciprocalBernoulli p.1 / 3) ^ 2) ≤
        ∑ p : ↥(quadraticPrimeBand T a),
          (reciprocalBernoulli p.1 / 3) ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ K)
      intro p _hp _hpK
      positivity
    _ ≤ 1 / (9 * (quadraticLowerCutoff T : ℝ)) :=
      sum_reciprocalBernoulli_third_sq_le
        (quadraticPrimeBand_prime T a)
        (by
          unfold quadraticLowerCutoff
          exact one_le_pow₀ hT)
        (fun p hp ↦ (mem_quadraticPrimeBand.mp hp).2.1)
    _ ≤ m ^ 2 / 2 := hcutoffDiagonal

theorem quadraticFiveEventMass_adaptiveTwoAnchor_moment_lower
    {T : ℕ} (hT : 1 ≤ T) (a : ℝ)
    (B : FiveConfiguration (quadraticPrimeBand T a) → Bool)
    (K : Finset ↥(quadraticPrimeBand T a))
    (Base : Finset
      (FiveConfiguration (quadraticPrimeBand T a)))
    (Ix Iy : FiveConfiguration (quadraticPrimeBand T a) →
      Finset ↥(quadraticPrimeBand T a))
    (lx ly : FiveLabel)
    (hlx0 : lx ≠ 0) (hly0 : ly ≠ 0) (hlxy : lx ≠ ly)
    (hclean : TwoAnchorBaseClean K Base Ix Iy lx ly)
    (hIx : ∀ c ∈ Base, Ix c ⊆ K)
    (hIy : ∀ c ∈ Base, Iy c ⊆ K)
    (hB : ∀ z ∈ adaptiveTwoAnchorChoices Base Ix Iy,
      B (completeTwoAnchorChoice lx ly z))
    {b k w : ℝ}
    (hbase : b ≤ ∑ c ∈ Base,
      poissonCompatibleConfigurationWeight
        (quadraticPrimeBand T a) reciprocalBernoulli c)
    (hk0 : 0 ≤ k) (hw0 : 0 ≤ w)
    (hX : ∀ c ∈ Base,
      k * w ≤ ∑ p ∈ Ix c, reciprocalBernoulli p.1 / 3)
    (hY : ∀ c ∈ Base,
      k * w ≤ ∑ p ∈ Iy c, reciprocalBernoulli p.1 / 3)
    (hcutoffDiagonal :
      1 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
        (k * w) ^ 2 / 2)
    (htransfer :
      16 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
        b * (k * w) ^ 2 / 4) :
    (b * k ^ 2 / 4) * w ^ 2 ≤
      fiveEventMass
        (quadraticPrimeBand T a) reciprocalBernoulli B := by
  have hmass :=
    quadraticFiveEventMass_adaptiveTwoAnchor_square_lower_of_cutoff
      hT a B K Base Ix Iy lx ly
      hlx0 hly0 hlxy hclean hIx hIy hB
      hbase (mul_nonneg hk0 hw0) hX hY hcutoffDiagonal
  calc
    (b * k ^ 2 / 4) * w ^ 2 =
        b * (k * w) ^ 2 / 4 := by ring
    _ ≤ b * ((k * w) ^ 2 / 2) -
        16 / (9 * (quadraticLowerCutoff T : ℝ)) := by
      linarith
    _ ≤ fiveEventMass
        (quadraticPrimeBand T a) reciprocalBernoulli B :=
      hmass

theorem eventually_inv_quadraticLowerCutoff_le_const_div_square_sq
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ T : ℕ in atTop,
      1 / (quadraticLowerCutoff T : ℝ) ≤
        c / (((T ^ 2 : ℕ) : ℝ) ^ 2) := by
  have hpow :
      Tendsto (fun T : ℕ ↦ T ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hinv :
      Tendsto
        (fun T : ℕ ↦ 1 / (((T ^ 2 : ℕ) : ℝ)))
        atTop (𝓝 0) :=
    tendsto_one_div_atTop_nhds_zero_nat.comp hpow
  have hev := hinv.eventually (Iio_mem_nhds hc)
  filter_upwards [hev, eventually_ge_atTop 1] with T hinvT hT
  have hTR : (0 : ℝ) < T := by positivity
  have hcut :
      (quadraticLowerCutoff T : ℝ) = (T : ℝ) ^ 6 := by
    simp [quadraticLowerCutoff, Nat.cast_pow]
  have htwo :
      ((T ^ 2 : ℕ) : ℝ) = (T : ℝ) ^ 2 := by
    simp [Nat.cast_pow]
  rw [htwo] at hinvT
  rw [hcut, htwo]
  have hfour :
      ((T : ℝ) ^ 2) ^ 2 = (T : ℝ) ^ 4 := by ring
  rw [hfour]
  apply (le_div_iff₀ (pow_pos hTR 4)).2
  calc
    1 / (T : ℝ) ^ 6 * (T : ℝ) ^ 4 =
        1 / (T : ℝ) ^ 2 := by
      field_simp [hTR.ne']
    _ ≤ c := hinvT.le

theorem eventually_quadraticAnchor_cutoff_absorptions
    {b k η : ℝ} (hb : 0 < b) (hk : 0 < k) (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      1 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
          (k * (η / (((T ^ 2 : ℕ) : ℝ)))) ^ 2 / 2 ∧
        16 / (9 * (quadraticLowerCutoff T : ℝ)) ≤
          b * (k * (η / (((T ^ 2 : ℕ) : ℝ)))) ^ 2 / 4 := by
  have hc1 :
      0 < 9 * (k * η) ^ 2 / 2 := by positivity
  have hc2 :
      0 < 9 * b * (k * η) ^ 2 / 64 := by positivity
  have h1 :=
    eventually_inv_quadraticLowerCutoff_le_const_div_square_sq hc1
  have h2 :=
    eventually_inv_quadraticLowerCutoff_le_const_div_square_sq hc2
  filter_upwards [h1, h2, eventually_gt_atTop 0] with T h1T h2T hT
  have hq :
      (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := by
    positivity
  constructor
  · calc
      1 / (9 * (quadraticLowerCutoff T : ℝ)) =
          (1 / (quadraticLowerCutoff T : ℝ)) / 9 := by ring
      _ ≤
          (9 * (k * η) ^ 2 / 2 /
            (((T ^ 2 : ℕ) : ℝ) ^ 2)) / 9 :=
        div_le_div_of_nonneg_right h1T (by norm_num)
      _ = (k * (η / (((T ^ 2 : ℕ) : ℝ)))) ^ 2 / 2 := by
        field_simp [hq.ne']
  · calc
      16 / (9 * (quadraticLowerCutoff T : ℝ)) =
          (16 / 9) *
            (1 / (quadraticLowerCutoff T : ℝ)) := by ring
      _ ≤ (16 / 9) *
          (9 * b * (k * η) ^ 2 / 64 /
            (((T ^ 2 : ℕ) : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left h2T (by norm_num)
      _ = b * (k * (η / (((T ^ 2 : ℕ) : ℝ)))) ^ 2 / 4 := by
        field_simp [hq.ne']
        norm_num

theorem eventually_quadraticAnchor_atom_loss_absorption
    {k η : ℝ} (hk : 0 < k) (hη : 0 < η) :
    ∀ᶠ T : ℕ in atTop,
      1 / (3 * (quadraticLowerCutoff T : ℝ)) ≤
        k * (η / (((T ^ 2 : ℕ) : ℝ))) / 2 := by
  have hc :
      0 < 3 * k * η / 2 := by positivity
  have hinv :=
    eventually_inv_quadraticLowerCutoff_le_const_div_square_sq hc
  filter_upwards [hinv, eventually_ge_atTop 1] with T hinvT hT
  have hq :
      (1 : ℝ) ≤ ((T ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast (one_le_pow₀ hT : 1 ≤ T ^ 2)
  have hq0 :
      (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := zero_lt_one.trans_le hq
  have hqSq :
      (((T ^ 2 : ℕ) : ℝ)) ≤
        (((T ^ 2 : ℕ) : ℝ) ^ 2) := by
    nlinarith [sq_nonneg (((T ^ 2 : ℕ) : ℝ) - 1)]
  have hcoarse :
      3 * k * η / 2 /
          (((T ^ 2 : ℕ) : ℝ) ^ 2) ≤
        3 * k * η / 2 /
          ((T ^ 2 : ℕ) : ℝ) := by
    exact div_le_div_of_nonneg_left hc.le hq0 hqSq
  calc
    1 / (3 * (quadraticLowerCutoff T : ℝ)) =
        (1 / (quadraticLowerCutoff T : ℝ)) / 3 := by ring
    _ ≤ (3 * k * η / 2 /
        (((T ^ 2 : ℕ) : ℝ) ^ 2)) / 3 :=
      div_le_div_of_nonneg_right hinvT (by norm_num)
    _ ≤ (3 * k * η / 2 /
        ((T ^ 2 : ℕ) : ℝ)) / 3 :=
      div_le_div_of_nonneg_right hcoarse (by norm_num)
    _ = k * (η / (((T ^ 2 : ℕ) : ℝ))) / 2 := by
      field_simp [hq0.ne']

end Erdos536
