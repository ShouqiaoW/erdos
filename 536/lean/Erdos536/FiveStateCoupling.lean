import Erdos536.FiniteProbability
import Mathlib.Data.ZMod.Basic

/-!
# The finite five-state coupling

This file records the exact, finite product law behind the prime-band
construction.  A prime is either unused, common to all three states, or
assigned to one of the three petals.  Each active label has mass `r / 3`;
the unused label has the remaining mass.  Consequently every one of the
three represented supports has the Bernoulli product law with parameter
`r`, before any balancing event is imposed.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Labels `0,1,2,3,4` mean respectively unused, common, and the three
petals. -/
abbrev FiveLabel := Fin 5

/-- The petal label corresponding to a ternary state. -/
def petalLabel (s : Fin 3) : FiveLabel :=
  ⟨s.1 + 2, by omega⟩

/-- Whether a label contributes to the support represented by state `s`.
The state contains the common label and the two petals other than its
omitted petal. -/
def fiveLabelIncluded (s : Fin 3) (l : FiveLabel) : Bool :=
  l == 1 || (l != 0 && l != petalLabel s)

/-- The local five-state mass with target Bernoulli parameter `r`. -/
noncomputable def fiveLabelWeight (r : ℝ) (l : FiveLabel) : ℝ :=
  if l = 0 then 1 - 4 * (r / 3) else r / 3

theorem sum_fiveLabelWeight (r : ℝ) :
    (∑ l : FiveLabel, fiveLabelWeight r l) = 1 := by
  simp [fiveLabelWeight, Fin.sum_univ_succ]

theorem sum_fiveLabelWeight_included (r : ℝ) (s : Fin 3) :
    (∑ l : FiveLabel,
        if fiveLabelIncluded s l then fiveLabelWeight r l else 0) = r := by
  fin_cases s <;>
    simp [fiveLabelIncluded, petalLabel, fiveLabelWeight, Fin.sum_univ_succ] <;>
    ring

theorem sum_fiveLabelWeight_excluded (r : ℝ) (s : Fin 3) :
    (∑ l : FiveLabel,
        if ¬fiveLabelIncluded s l then fiveLabelWeight r l else 0) = 1 - r := by
  have htotal := sum_fiveLabelWeight r
  have hincluded := sum_fiveLabelWeight_included r s
  calc
    (∑ l : FiveLabel,
        if ¬fiveLabelIncluded s l then fiveLabelWeight r l else 0) =
        (∑ l : FiveLabel, fiveLabelWeight r l) -
          ∑ l : FiveLabel,
            if fiveLabelIncluded s l then fiveLabelWeight r l else 0 := by
              apply eq_sub_of_add_eq
              rw [← Finset.sum_add_distrib]
              apply Finset.sum_congr rfl
              intro l _hl
              by_cases h : fiveLabelIncluded s l <;> simp [h]
    _ = 1 - r := by rw [htotal, hincluded]

theorem fiveLabelWeight_nonneg {r : ℝ}
    (hr0 : 0 ≤ r) (hr : r ≤ 3 / 4) (l : FiveLabel) :
    0 ≤ fiveLabelWeight r l := by
  rw [fiveLabelWeight]
  split_ifs
  · linarith
  · positivity

/-- A labelled configuration on a finite ground set. -/
abbrev FiveConfiguration {α : Type*} [DecidableEq α] (P : Finset α) :=
  (p : ↥P) → FiveLabel

/-- Product mass of a labelled configuration. -/
noncomputable def fiveConfigurationWeight
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (c : FiveConfiguration P) : ℝ :=
  ∏ p : ↥P, fiveLabelWeight (r p.1) (c p)

/-- The represented support, as a finset of the subtype `P`. -/
noncomputable def fiveStateSupport
    {α : Type*} [DecidableEq α] (P : Finset α) (s : Fin 3)
    (c : FiveConfiguration P) : Finset ↥P :=
  Finset.univ.filter fun p ↦ fiveLabelIncluded s (c p)

theorem mem_fiveStateSupport
    {α : Type*} [DecidableEq α] (P : Finset α) (s : Fin 3)
    (c : FiveConfiguration P) (p : ↥P) :
    p ∈ fiveStateSupport P s c ↔ fiveLabelIncluded s (c p) := by
  simp [fiveStateSupport]

/-- The unconditioned five-state product masses sum to one. -/
theorem sum_fiveConfigurationWeight
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ) :
    (∑ c : FiveConfiguration P, fiveConfigurationWeight P r c) = 1 := by
  unfold fiveConfigurationWeight
  rw [← Fintype.prod_sum]
  simp only [sum_fiveLabelWeight, Finset.prod_const_one]

/-- Exact one-word marginal identity on the subtype ground set. -/
theorem fiveStateSupport_marginal
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (s : Fin 3) (S : Finset ↥P) :
    (∑ c : FiveConfiguration P,
        if fiveStateSupport P s c = S
        then fiveConfigurationWeight P r c else 0) =
      (∏ p ∈ S, r p.1) * ∏ p ∈ (Finset.univ \ S), (1 - r p.1) := by
  classical
  have hlocal (p : ↥P) :
      (∑ l : FiveLabel,
          if fiveLabelIncluded s l ↔ p ∈ S
          then fiveLabelWeight (r p.1) l else 0) =
        if p ∈ S then r p.1 else 1 - r p.1 := by
    by_cases hp : p ∈ S
    · simp only [hp, iff_true, if_true]
      exact sum_fiveLabelWeight_included (r p.1) s
    · simp only [hp, iff_false, if_false]
      exact sum_fiveLabelWeight_excluded (r p.1) s
  calc
    (∑ c : FiveConfiguration P,
        if fiveStateSupport P s c = S
        then fiveConfigurationWeight P r c else 0) =
        ∑ c : FiveConfiguration P,
          ∏ p : ↥P,
            if fiveLabelIncluded s (c p) ↔ p ∈ S
            then fiveLabelWeight (r p.1) (c p) else 0 := by
              apply Finset.sum_congr rfl
              intro c _hc
              by_cases hsupport : fiveStateSupport P s c = S
              · rw [if_pos hsupport]
                rw [fiveConfigurationWeight]
                apply Finset.prod_congr rfl
                intro p _hp
                rw [if_pos]
                simpa [mem_fiveStateSupport] using
                  Finset.ext_iff.mp hsupport p
              · rw [if_neg hsupport]
                rw [Finset.ext_iff] at hsupport
                push_neg at hsupport
                obtain ⟨p, hp⟩ := hsupport
                symm
                apply Finset.prod_eq_zero (i := p) (Finset.mem_univ p)
                rw [if_neg]
                intro hiff
                rcases hp with ⟨hincluded, hpS⟩ | ⟨hexcluded, hpS⟩
                · have hincluded' :
                      fiveLabelIncluded s (c p) = true :=
                    (mem_fiveStateSupport P s c p).mp hincluded
                  exact hpS (hiff.mp hincluded')
                · have hexcluded' :
                      fiveLabelIncluded s (c p) = false := by
                    simpa [mem_fiveStateSupport] using hexcluded
                  have hincluded' := hiff.mpr hpS
                  simp [hexcluded'] at hincluded'
    _ = ∏ p : ↥P,
        ∑ l : FiveLabel,
          if fiveLabelIncluded s l ↔ p ∈ S
          then fiveLabelWeight (r p.1) l else 0 := by
            rw [Fintype.prod_sum]
    _ = ∏ p : ↥P, if p ∈ S then r p.1 else 1 - r p.1 := by
          apply Finset.prod_congr rfl
          intro p _hp
          exact hlocal p
    _ = (∏ p ∈ S, r p.1) *
        ∏ p ∈ (Finset.univ \ S), (1 - r p.1) := by
          rw [Finset.prod_ite, Finset.filter_mem_eq_inter,
            Finset.univ_inter, Finset.filter_notMem_eq_sdiff]

/-- The Bernoulli product mass on a support of the subtype ground set. -/
noncomputable def subtypeBernoulliWeight
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (S : Finset ↥P) : ℝ :=
  (∏ p ∈ S, r p.1) * ∏ p ∈ (Finset.univ \ S), (1 - r p.1)

theorem fiveStateSupport_marginal_eq_subtypeBernoulliWeight
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (s : Fin 3) (S : Finset ↥P) :
    (∑ c : FiveConfiguration P,
        if fiveStateSupport P s c = S
        then fiveConfigurationWeight P r c else 0) =
      subtypeBernoulliWeight P r S := by
  exact fiveStateSupport_marginal P r s S

/-- Total mass of an event in the finite five-state configuration space. -/
noncomputable def fiveEventMass
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) : ℝ :=
  ∑ c : FiveConfiguration P,
    if B c then fiveConfigurationWeight P r c else 0

/-- Joint mass of an event and one represented support. -/
noncomputable def fiveEventSupportMass
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3)
    (S : Finset ↥P) : ℝ :=
  ∑ c : FiveConfiguration P,
    if B c ∧ fiveStateSupport P s c = S
    then fiveConfigurationWeight P r c else 0

/-- The root likelihood `P(B | support = S)`, written as a finite ratio. -/
noncomputable def fiveRootLikelihood
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3)
    (S : Finset ↥P) : ℝ :=
  fiveEventSupportMass P r B s S / subtypeBernoulliWeight P r S

/-- The support mass after conditioning the five-state law on `B`. -/
noncomputable def conditionedFiveSupportMass
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3)
    (S : Finset ↥P) : ℝ :=
  fiveEventSupportMass P r B s S / fiveEventMass P r B

/-- Exact finite Bayes identity for the conditioned word marginal. -/
theorem conditionedFiveSupportMass_eq_bayes
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3)
    (S : Finset ↥P)
    (hμ : subtypeBernoulliWeight P r S ≠ 0) :
    conditionedFiveSupportMass P r B s S =
      subtypeBernoulliWeight P r S *
        (fiveRootLikelihood P r B s S / fiveEventMass P r B) := by
  rw [conditionedFiveSupportMass, fiveRootLikelihood]
  field_simp

/-- The joint event/support masses regroup to the total event mass. -/
theorem sum_fiveEventSupportMass
    {α : Type*} [DecidableEq α] (P : Finset α) (r : α → ℝ)
    (B : FiveConfiguration P → Bool) (s : Fin 3) :
    (∑ S : Finset ↥P, fiveEventSupportMass P r B s S) =
      fiveEventMass P r B := by
  classical
  unfold fiveEventMass fiveEventSupportMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hB : B c = true
  · rw [Finset.sum_eq_single (fiveStateSupport P s c)]
    · simp [hB]
    · intro S _hS hne
      simp [hB, hne.symm]
    · simp
  · simp [hB]

end Erdos536
