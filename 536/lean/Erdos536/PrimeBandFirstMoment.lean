import Erdos536.FinitePiProbability
import Erdos536.CubeLawTensorDistance
import Erdos536.BernoulliSquarefree
import Erdos536.PrimeTail
import Erdos536.PrimeBandEvent

/-!
# Finite first-moment transfer for a prime band

This file formalizes the whole-band categorical-to-Poisson comparison
used in the first-moment argument. Four independent Poisson variables of
rate `h = r / 3` are collapsed to six outcomes: the empty outcome, four
singleton outcomes, and one overflow outcome recording every collision.

The local total variation is at most `16 * h^2`. The comparison is
tensorized over an arbitrary finite ground set. For reciprocal-Bernoulli
weights on primes above `A`, the resulting event-transfer error is at most
`16 / (9*A)`.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- `L¹` distance between finite independent product laws is bounded by
the sum of their coordinatewise `L¹` distances. -/
theorem finitePiL1_le_sum
    {ι Ω : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (μ ν : ι → Ω → ℝ)
    (hμ : ∀ i x, 0 ≤ μ i x)
    (hν : ∀ i x, 0 ≤ ν i x)
    (hμsum : ∀ i, ∑ x, μ i x = 1)
    (hνsum : ∀ i, ∑ x, ν i x = 1) :
    (∑ x : ι → Ω,
        |(∏ i, μ i (x i)) - ∏ i, ν i (x i)|) ≤
      ∑ i, ∑ x, |μ i x - ν i x| := by
  classical
  let P : ∀ (κ : Type) [Fintype κ], Prop :=
    fun κ _ ↦ ∀ [DecidableEq κ] (μ ν : κ → Ω → ℝ),
      (∀ i x, 0 ≤ μ i x) →
      (∀ i x, 0 ≤ ν i x) →
      (∀ i, ∑ x, μ i x = 1) →
      (∀ i, ∑ x, ν i x = 1) →
      (∑ x : κ → Ω,
          |(∏ i, μ i (x i)) - ∏ i, ν i (x i)|) ≤
        ∑ i, ∑ x, |μ i x - ν i x|
  have hP : P ι := by
    apply Fintype.induction_empty_option
    · intro α β _ e ih
      letI : Fintype α := Fintype.ofEquiv β e.symm
      dsimp [P] at ih ⊢
      intro _ μ ν hμ hν hμsum hνsum
      letI : DecidableEq α := Classical.decEq α
      letI : Fintype (α → Ω) := Pi.instFintype
      let μ' : α → Ω → ℝ := fun i ↦ μ (e i)
      let ν' : α → Ω → ℝ := fun i ↦ ν (e i)
      have h := ih μ' ν'
        (fun i x ↦ hμ (e i) x)
        (fun i x ↦ hν (e i) x)
        (fun i ↦ hμsum (e i))
        (fun i ↦ hνsum (e i))
      let E : (α → Ω) ≃ (β → Ω) :=
        Equiv.piCongrLeft (fun _ : β ↦ Ω) e
      rw [← E.sum_comp]
      rw [← e.sum_comp]
      have hμprod (x : α → Ω) :
          (∏ b, μ b ((E x) b)) =
            ∏ a, μ (e a) (x a) := by
        rw [← e.prod_comp]
        simp [E]
      have hνprod (x : α → Ω) :
          (∏ b, ν b ((E x) b)) =
            ∏ a, ν (e a) (x a) := by
        rw [← e.prod_comp]
        simp [E]
      simp_rw [hμprod, hνprod]
      exact h
    · dsimp [P]
      intro _ μ ν hμ hν hμsum hνsum
      simp
    · intro α _ ih
      dsimp [P] at ih ⊢
      intro _ μ ν hμ hν hμsum hνsum
      letI : DecidableEq α := Classical.decEq α
      letI : Fintype (α → Ω) := Pi.instFintype
      let μtail : α → Ω → ℝ := fun i ↦ μ (some i)
      let νtail : α → Ω → ℝ := fun i ↦ ν (some i)
      have htail := ih μtail νtail
        (fun i x ↦ hμ (some i) x)
        (fun i x ↦ hν (some i) x)
        (fun i ↦ hμsum (some i))
        (fun i ↦ hνsum (some i))
      let E : ((Option α) → Ω) ≃ Ω × (α → Ω) :=
        Equiv.piOptionEquivProd
      rw [← E.symm.sum_comp]
      rw [Fintype.sum_prod_type]
      have hprod := Erdos536.product_l1_distance_le
        (Finset.univ : Finset Ω)
        (Finset.univ : Finset (α → Ω))
        (μ none) (ν none)
        (fun x ↦ ∏ i, μtail i (x i))
        (fun x ↦ ∏ i, νtail i (x i))
        (fun x _ ↦ Finset.prod_nonneg fun i _ ↦ hμ (some i) (x i))
        (fun x _ ↦ hν none x)
        (by
          simpa [μtail] using
            Erdos536.sum_finitePiWeight μtail
              (fun i ↦ hμsum (some i)))
        (by simpa using hνsum none)
      calc
        (∑ a : Ω, ∑ x : α → Ω,
            |(∏ i, μ i ((E.symm (a, x)) i)) -
              ∏ i, ν i ((E.symm (a, x)) i)|) ≤
            (∑ a : Ω, |μ none a - ν none a|) +
              ∑ x : α → Ω,
                |(∏ i, μtail i (x i)) -
                  ∏ i, νtail i (x i)| := by
              simpa [E, μtail, νtail, Fintype.prod_option] using hprod
        _ ≤ (∑ a : Ω, |μ none a - ν none a|) +
              ∑ i : α, ∑ a : Ω, |μtail i a - νtail i a| :=
            add_le_add (le_refl _) htail
        _ = ∑ i : Option α, ∑ a : Ω, |μ i a - ν i a| := by
            simp [Fintype.sum_option, μtail, νtail]
  exact hP μ ν hμ hν hμsum hνsum

theorem eventMass_abs_sub_le_half_l1
    {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (S : Finset Ω) (μ ν : Ω → ℝ)
    (hμsum : ∑ x, μ x = 1)
    (hνsum : ∑ x, ν x = 1) :
    |(∑ x ∈ S, μ x) - ∑ x ∈ S, ν x| ≤
      (1 / 2 : ℝ) * ∑ x, |μ x - ν x| := by
  classical
  let d : Ω → ℝ := fun x ↦ μ x - ν x
  have htotal : ∑ x, d x = 0 := by
    dsimp [d]
    rw [Finset.sum_sub_distrib, hμsum, hνsum, sub_self]
  have hsplit :
      (∑ x ∈ S, d x) +
        ∑ x ∈ (Finset.univ \ S), d x = 0 := by
    rw [add_comm, Finset.sum_sdiff (Finset.subset_univ S)]
    exact htotal
  have hcomp :
      (∑ x ∈ (Finset.univ \ S), d x) =
        -(∑ x ∈ S, d x) := by
    linarith
  have hS :
      |∑ x ∈ S, d x| ≤ ∑ x ∈ S, |d x| :=
    Finset.abs_sum_le_sum_abs _ _
  have hSc :
      |∑ x ∈ (Finset.univ \ S), d x| ≤
        ∑ x ∈ (Finset.univ \ S), |d x| :=
    Finset.abs_sum_le_sum_abs _ _
  have htwice :
      2 * |∑ x ∈ S, d x| ≤ ∑ x, |d x| := by
    calc
      2 * |∑ x ∈ S, d x| =
          |∑ x ∈ S, d x| +
            |∑ x ∈ (Finset.univ \ S), d x| := by
        rw [hcomp, abs_neg]
        ring
      _ ≤ (∑ x ∈ S, |d x|) +
          ∑ x ∈ (Finset.univ \ S), |d x| :=
        add_le_add hS hSc
      _ = ∑ x, |d x| := by
        rw [add_comm, Finset.sum_sdiff (Finset.subset_univ S)]
  have hevent :
      (∑ x ∈ S, μ x) - ∑ x ∈ S, ν x =
        ∑ x ∈ S, d x := by
    simp [d, Finset.sum_sub_distrib]
  rw [hevent]
  change |∑ x ∈ S, d x| ≤
    (1 / 2 : ℝ) * ∑ x, |d x|
  nlinarith

theorem finitePiEvent_abs_sub_le_half_sum
    {ι Ω : Type} [Fintype ι] [DecidableEq ι]
    [Fintype Ω] [DecidableEq Ω]
    (S : Finset (ι → Ω)) (μ ν : ι → Ω → ℝ)
    (hμ : ∀ i x, 0 ≤ μ i x)
    (hν : ∀ i x, 0 ≤ ν i x)
    (hμsum : ∀ i, ∑ x, μ i x = 1)
    (hνsum : ∀ i, ∑ x, ν i x = 1) :
    |(∑ x ∈ S, Erdos536.finitePiWeight μ x) -
        ∑ x ∈ S, Erdos536.finitePiWeight ν x| ≤
      (1 / 2 : ℝ) *
        ∑ i, ∑ x, |μ i x - ν i x| := by
  have hmassμ : ∑ x, Erdos536.finitePiWeight μ x = 1 :=
    Erdos536.sum_finitePiWeight μ hμsum
  have hmassν : ∑ x, Erdos536.finitePiWeight ν x = 1 :=
    Erdos536.sum_finitePiWeight ν hνsum
  have hevent := eventMass_abs_sub_le_half_l1 S
    (Erdos536.finitePiWeight μ) (Erdos536.finitePiWeight ν)
    hmassμ hmassν
  have hl1 := finitePiL1_le_sum μ ν hμ hν hμsum hνsum
  calc
    |(∑ x ∈ S, Erdos536.finitePiWeight μ x) -
        ∑ x ∈ S, Erdos536.finitePiWeight ν x| ≤
        (1 / 2 : ℝ) *
          ∑ x, |Erdos536.finitePiWeight μ x -
            Erdos536.finitePiWeight ν x| :=
      hevent
    _ ≤ (1 / 2 : ℝ) *
        ∑ i, ∑ x, |μ i x - ν i x| :=
      mul_le_mul_of_nonneg_left hl1 (by norm_num)

/-- The categorical five-state law with a zero-mass overflow outcome. -/
noncomputable def categoricalCellWeight (r : ℝ) :
    Option FiveLabel → ℝ
  | none => 0
  | some l => fiveLabelWeight r l

noncomputable def collapsedPoissonCellWeight (r : ℝ) :
    Option FiveLabel → ℝ
  | none =>
      1 - (1 + 4 * (r / 3)) * Real.exp (-(4 * (r / 3)))
  | some l =>
      if l = 0 then Real.exp (-(4 * (r / 3)))
      else (r / 3) * Real.exp (-(4 * (r / 3)))

theorem sum_categoricalCellWeight (r : ℝ) :
    ∑ l, categoricalCellWeight r l = 1 := by
  rw [Fintype.sum_option]
  simp [categoricalCellWeight, sum_fiveLabelWeight]

theorem sum_collapsedPoissonCellWeight (r : ℝ) :
    ∑ l, collapsedPoissonCellWeight r l = 1 := by
  rw [Fintype.sum_option]
  simp [collapsedPoissonCellWeight, Fin.sum_univ_succ]
  ring

private theorem exp_neg_le_one {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  linarith

private theorem one_sub_le_exp_neg (x : ℝ) :
    1 - x ≤ Real.exp (-x) := by
  linarith [Real.add_one_le_exp (-x)]

private theorem one_add_mul_exp_neg_le_one (x : ℝ) :
    (1 + x) * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hmul := mul_le_mul_of_nonneg_right h (Real.exp_nonneg (-x))
  rw [← Real.exp_add] at hmul
  norm_num at hmul
  simpa [add_comm] using hmul

theorem collapsedPoissonCellWeight_nonneg {r : ℝ} (hr : 0 ≤ r)
    (l : Option FiveLabel) :
    0 ≤ collapsedPoissonCellWeight r l := by
  cases l with
  | none =>
      dsimp [collapsedPoissonCellWeight]
      apply sub_nonneg.mpr
      exact one_add_mul_exp_neg_le_one _
  | some l =>
      dsimp [collapsedPoissonCellWeight]
      split_ifs <;> positivity

theorem categoricalCellWeight_nonneg {r : ℝ}
    (hr : 0 ≤ r) (hrmax : r ≤ 3 / 4)
    (l : Option FiveLabel) :
    0 ≤ categoricalCellWeight r l := by
  cases l with
  | none => simp [categoricalCellWeight]
  | some l =>
      exact fiveLabelWeight_nonneg hr hrmax l

theorem cell_l1_eq {r : ℝ} (hr : 0 ≤ r) :
    (∑ l, |categoricalCellWeight r l -
      collapsedPoissonCellWeight r l|) =
      8 * (r / 3) * (1 - Real.exp (-(4 * (r / 3)))) := by
  have hx : 0 ≤ 4 * (r / 3) := by positivity
  have he : Real.exp (-(4 * (r / 3))) ≤ 1 :=
    exp_neg_le_one hx
  have hlinear :
      1 - 4 * (r / 3) ≤ Real.exp (-(4 * (r / 3))) :=
    one_sub_le_exp_neg _
  have hover :
      (1 + 4 * (r / 3)) * Real.exp (-(4 * (r / 3))) ≤ 1 :=
    one_add_mul_exp_neg_le_one _
  have hOverflow :
      0 ≤ 1 - (1 + 4 * (r / 3)) *
        Real.exp (-(4 * (r / 3))) :=
    sub_nonneg.mpr hover
  have hZero :
      0 ≤ Real.exp (-(4 * (r / 3))) -
        (1 - 4 * (r / 3)) :=
    sub_nonneg.mpr hlinear
  have hActive :
      0 ≤ r / 3 - (r / 3) *
        Real.exp (-(4 * (r / 3))) := by
    apply sub_nonneg.mpr
    exact mul_le_of_le_one_right
      (div_nonneg hr (by norm_num)) he
  have habs (l : Option FiveLabel) :
      |categoricalCellWeight r l -
          collapsedPoissonCellWeight r l| =
        match l with
        | none =>
            1 - (1 + 4 * (r / 3)) *
              Real.exp (-(4 * (r / 3)))
        | some k =>
            if k = 0 then
              Real.exp (-(4 * (r / 3))) -
                (1 - 4 * (r / 3))
            else
              r / 3 - (r / 3) *
                Real.exp (-(4 * (r / 3))) := by
    cases l with
    | none =>
        dsimp [categoricalCellWeight, collapsedPoissonCellWeight]
        rw [abs_of_nonpos]
        · ring
        · linarith
    | some k =>
        fin_cases k
        · dsimp [categoricalCellWeight, collapsedPoissonCellWeight,
            fiveLabelWeight]
          rw [abs_of_nonpos]
          · ring
          · linarith
        all_goals
          dsimp [categoricalCellWeight, collapsedPoissonCellWeight,
            fiveLabelWeight]
          rw [abs_of_nonneg hActive]
  simp_rw [habs]
  rw [Fintype.sum_option]
  simp [Fin.sum_univ_succ]
  ring

theorem cell_l1_le {r : ℝ} (hr : 0 ≤ r) :
    (∑ l, |categoricalCellWeight r l -
      collapsedPoissonCellWeight r l|) ≤
      32 * (r / 3) ^ 2 := by
  rw [cell_l1_eq hr]
  have he : 1 - Real.exp (-(4 * (r / 3))) ≤ 4 * (r / 3) := by
    linarith [one_sub_le_exp_neg (4 * (r / 3))]
  have hh : 0 ≤ 8 * (r / 3) := by positivity
  calc
    8 * (r / 3) * (1 - Real.exp (-(4 * (r / 3)))) ≤
        8 * (r / 3) * (4 * (r / 3)) :=
      mul_le_mul_of_nonneg_left he hh
    _ = 32 * (r / 3) ^ 2 := by ring

abbrev CollapsedConfiguration {α : Type*} [DecidableEq α]
    (P : Finset α) :=
  (p : ↥P) → Option FiveLabel

def embedFiveConfiguration
    {α : Type*} [DecidableEq α] {P : Finset α}
    (c : FiveConfiguration P) : CollapsedConfiguration P :=
  fun p ↦ some (c p)

theorem embedFiveConfiguration_injective
    {α : Type*} [DecidableEq α] {P : Finset α} :
    Function.Injective
      (embedFiveConfiguration (P := P)) := by
  intro c d h
  funext p
  have hp := congrFun h p
  simpa [embedFiveConfiguration] using hp

def embedFiveConfigurationEmbedding
    {α : Type*} [DecidableEq α] (P : Finset α) :
    FiveConfiguration P ↪ CollapsedConfiguration P :=
  ⟨embedFiveConfiguration, embedFiveConfiguration_injective⟩

def embeddedFiveEvent
    {α : Type*} [DecidableEq α] (P : Finset α)
    (B : FiveConfiguration P → Bool) :
    Finset (CollapsedConfiguration P) :=
  (Finset.univ.filter fun c ↦ B c).map
    (embedFiveConfigurationEmbedding P)

noncomputable def poissonCompatibleConfigurationWeight
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (c : FiveConfiguration P) : ℝ :=
  ∏ p : ↥P,
    collapsedPoissonCellWeight (r p.1) (some (c p))

noncomputable def poissonCompatibleEventMass
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (B : FiveConfiguration P → Bool) : ℝ :=
  ∑ c : FiveConfiguration P,
    if B c then poissonCompatibleConfigurationWeight P r c else 0

theorem finitePiWeight_categorical_embed
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (c : FiveConfiguration P) :
    Erdos536.finitePiWeight
      (fun p : ↥P ↦ categoricalCellWeight (r p.1))
      (embedFiveConfiguration c) =
      fiveConfigurationWeight P r c := by
  rfl

theorem finitePiWeight_poisson_embed
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (c : FiveConfiguration P) :
    Erdos536.finitePiWeight
      (fun p : ↥P ↦ collapsedPoissonCellWeight (r p.1))
      (embedFiveConfiguration c) =
      poissonCompatibleConfigurationWeight P r c := by
  rfl

theorem embeddedFiveEvent_categoricalMass
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (B : FiveConfiguration P → Bool) :
    (∑ x ∈ embeddedFiveEvent P B,
      Erdos536.finitePiWeight
        (fun p : ↥P ↦ categoricalCellWeight (r p.1)) x) =
      fiveEventMass P r B := by
  classical
  rw [embeddedFiveEvent, Finset.sum_map]
  unfold fiveEventMass
  rw [← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  exact finitePiWeight_categorical_embed P r c

theorem embeddedFiveEvent_poissonMass
    {α : Type*} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (B : FiveConfiguration P → Bool) :
    (∑ x ∈ embeddedFiveEvent P B,
      Erdos536.finitePiWeight
        (fun p : ↥P ↦ collapsedPoissonCellWeight (r p.1)) x) =
      poissonCompatibleEventMass P r B := by
  classical
  rw [embeddedFiveEvent, Finset.sum_map]
  unfold poissonCompatibleEventMass
  rw [← Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro c hc
  exact finitePiWeight_poisson_embed P r c

theorem fiveEventMass_sub_poissonCompatible_abs_le
    {α : Type} [DecidableEq α] (P : Finset α)
    (r : α → ℝ) (B : FiveConfiguration P → Bool)
    (hr0 : ∀ p ∈ P, 0 ≤ r p)
    (hrmax : ∀ p ∈ P, r p ≤ 3 / 4) :
    |fiveEventMass P r B -
        poissonCompatibleEventMass P r B| ≤
      16 * ∑ p : ↥P, (r p.1 / 3) ^ 2 := by
  classical
  let μ : ↥P → Option FiveLabel → ℝ :=
    fun p ↦ categoricalCellWeight (r p.1)
  let ν : ↥P → Option FiveLabel → ℝ :=
    fun p ↦ collapsedPoissonCellWeight (r p.1)
  have hmain := finitePiEvent_abs_sub_le_half_sum
    (embeddedFiveEvent P B) μ ν
    (fun p x ↦ categoricalCellWeight_nonneg
      (hr0 p.1 p.2) (hrmax p.1 p.2) x)
    (fun p x ↦ collapsedPoissonCellWeight_nonneg
      (hr0 p.1 p.2) x)
    (fun p ↦ sum_categoricalCellWeight (r p.1))
    (fun p ↦ sum_collapsedPoissonCellWeight (r p.1))
  rw [embeddedFiveEvent_categoricalMass,
    embeddedFiveEvent_poissonMass] at hmain
  calc
    |fiveEventMass P r B -
        poissonCompatibleEventMass P r B| ≤
        (1 / 2 : ℝ) *
          ∑ p : ↥P, ∑ x,
            |μ p x - ν p x| :=
      hmain
    _ ≤ (1 / 2 : ℝ) *
        ∑ p : ↥P, 32 * (r p.1 / 3) ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro p _hp
      exact cell_l1_le (hr0 p.1 p.2)
    _ = 16 * ∑ p : ↥P, (r p.1 / 3) ^ 2 := by
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring

private theorem reciprocalBernoulli_le_inv
    {p : ℕ} (hp : 0 < p) :
    reciprocalBernoulli p ≤ (p : ℝ)⁻¹ := by
  unfold reciprocalBernoulli
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have h := one_div_le_one_div_of_le
    (a := (p : ℝ)) (b := (p : ℝ) + 1) hpR (by linarith)
  simpa only [one_div] using h

theorem sum_reciprocalBernoulli_third_sq_le
    {P : Finset ℕ} (hP : IsPrimeSupport P)
    {A : ℕ} (hA : 1 ≤ A)
    (habove : ∀ p ∈ P, A < p) :
    (∑ p : ↥P, (reciprocalBernoulli p.1 / 3) ^ 2) ≤
      1 / (9 * (A : ℝ)) := by
  have hpoint (p : ↥P) :
      (reciprocalBernoulli p.1 / 3) ^ 2 ≤
        (p.1 : ℝ)⁻¹ ^ 2 / 9 := by
    have hp := (hP p.1 p.2).pos
    have hrec := reciprocalBernoulli_le_inv hp
    have hr0 := reciprocalBernoulli_nonneg p.1
    have hinv0 : 0 ≤ (p.1 : ℝ)⁻¹ := by positivity
    nlinarith [sq_nonneg
      (reciprocalBernoulli p.1 - (p.1 : ℝ)⁻¹)]
  calc
    (∑ p : ↥P, (reciprocalBernoulli p.1 / 3) ^ 2) ≤
        ∑ p : ↥P, (p.1 : ℝ)⁻¹ ^ 2 / 9 := by
      apply Finset.sum_le_sum
      intro p _hp
      exact hpoint p
    _ = (1 / 9 : ℝ) *
        ∑ p ∈ P, (p : ℝ)⁻¹ ^ 2 := by
      rw [Finset.sum_coe_sort P
        (fun p : ℕ ↦ (p : ℝ)⁻¹ ^ 2 / 9)]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ (1 / 9 : ℝ) * (1 / (A : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (sum_primeSupport_inv_sq_le hP hA habove)
      norm_num
    _ = 1 / (9 * (A : ℝ)) := by ring

theorem reciprocalFiveEventMass_poissonCompatible_abs_le
    {P : Finset ℕ} (hP : IsPrimeSupport P)
    {A : ℕ} (hA : 1 ≤ A)
    (habove : ∀ p ∈ P, A < p)
    (B : FiveConfiguration P → Bool) :
    |fiveEventMass P reciprocalBernoulli B -
        poissonCompatibleEventMass P reciprocalBernoulli B| ≤
      16 / (9 * (A : ℝ)) := by
  have hbase := fiveEventMass_sub_poissonCompatible_abs_le
    P reciprocalBernoulli B
    (fun p _hp ↦ reciprocalBernoulli_nonneg p)
    (fun p hp ↦ reciprocalBernoulli_le_three_quarters
      (hP p hp).one_le)
  calc
    |fiveEventMass P reciprocalBernoulli B -
        poissonCompatibleEventMass P reciprocalBernoulli B| ≤
        16 * ∑ p : ↥P,
          (reciprocalBernoulli p.1 / 3) ^ 2 :=
      hbase
    _ ≤ 16 * (1 / (9 * (A : ℝ))) :=
      mul_le_mul_of_nonneg_left
        (sum_reciprocalBernoulli_third_sq_le hP hA habove)
        (by norm_num)
    _ = 16 / (9 * (A : ℝ)) := by ring

theorem reciprocalFiveEventMass_lower_transfer
    {P : Finset ℕ} (hP : IsPrimeSupport P)
    {A : ℕ} (hA : 1 ≤ A)
    (habove : ∀ p ∈ P, A < p)
    (B : FiveConfiguration P → Bool) {L : ℝ}
    (hL : L ≤
      poissonCompatibleEventMass P reciprocalBernoulli B) :
    L - 16 / (9 * (A : ℝ)) ≤
      fiveEventMass P reciprocalBernoulli B := by
  have herr :=
    reciprocalFiveEventMass_poissonCompatible_abs_le
      hP hA habove B
  rw [abs_le] at herr
  linarith

/-- The transfer theorem specialized to the concrete symmetric
prime-band event.  The remaining first-moment task is exactly a lower
bound for the collision-free Poisson-compatible mass in the hypothesis. -/
theorem fivePrimeBandEventMass_lower_transfer
    {P : Finset ℕ} (hP : IsPrimeSupport P)
    {A : ℕ} (hA : 1 ≤ A)
    (habove : ∀ p ∈ P, A < p)
    (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    {L : ℝ}
    (hL : L ≤ poissonCompatibleEventMass P reciprocalBernoulli
      (fivePrimeBandEvent P T lower upper w depths threshold)) :
    L - 16 / (9 * (A : ℝ)) ≤
      fiveEventMass P reciprocalBernoulli
        (fivePrimeBandEvent P T lower upper w depths threshold) :=
  reciprocalFiveEventMass_lower_transfer
    hP hA habove
    (fivePrimeBandEvent P T lower upper w depths threshold) hL

end Erdos536
