import Mathlib

/-!
# One rank-deficient floating-rounding step

This file isolates the linear-algebra move used in the paper's floating
rounding lemma.  If fewer equations than fractional coordinates are being
retained, one may preserve every retained equation, keep all coordinates in
`[0,1]`, freeze every already integral coordinate, and make at least one new
coordinate integral.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Coordinates strictly between the two integral boundary values. -/
def fractionalSupport {A : Type*} [Fintype A] (x : A → ℝ) : Finset A := by
  classical
  exact Finset.univ.filter fun a ↦ x a ≠ 0 ∧ x a ≠ 1

@[simp]
theorem mem_fractionalSupport {A : Type*} [Fintype A]
    {x : A → ℝ} {a : A} :
    a ∈ fractionalSupport x ↔ x a ≠ 0 ∧ x a ≠ 1 := by
  classical
  simp [fractionalSupport]

private theorem exists_positive_boundary_step
    {A : Type*} [Fintype A]
    (x z : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hstrict : ∀ a, z a ≠ 0 → 0 < x a ∧ x a < 1)
    (hz : z ≠ 0) :
    ∃ t : ℝ,
      0 < t ∧
      (∀ a, 0 ≤ x a + t * z a ∧ x a + t * z a ≤ 1) ∧
      ∃ a, z a ≠ 0 ∧
        (x a + t * z a = 0 ∨ x a + t * z a = 1) := by
  classical
  have hzexists : ∃ a, z a ≠ 0 := by
    by_contra h
    push_neg at h
    exact hz (funext h)
  obtain ⟨a₁, ha₁⟩ := hzexists
  letI : Nonempty A := ⟨a₁⟩
  let ratio : A → ℝ := fun a ↦
    if 0 < z a then z a / (1 - x a)
    else if z a < 0 then (-z a) / x a
    else 0
  have hratio_nonneg (a : A) : 0 ≤ ratio a := by
    by_cases hp : 0 < z a
    · have hden : 0 < 1 - x a := sub_pos.mpr (hstrict a hp.ne').2
      simp only [ratio, if_pos hp]
      exact (div_pos hp hden).le
    · by_cases hn : z a < 0
      · have hden : 0 < x a := (hstrict a hn.ne).1
        simp only [ratio, if_neg hp, if_pos hn]
        exact (div_pos (neg_pos.mpr hn) hden).le
      · simp [ratio, hp, hn]
  have hratio_pos : 0 < ratio a₁ := by
    rcases lt_or_gt_of_ne ha₁ with hn | hp
    · have hxpos : 0 < x a₁ := (hstrict a₁ ha₁).1
      simp only [ratio, if_neg (not_lt.mpr hn.le), if_pos hn]
      exact div_pos (neg_pos.mpr hn) hxpos
    · have hxlt : x a₁ < 1 := (hstrict a₁ ha₁).2
      simp only [ratio, if_pos hp]
      exact div_pos hp (sub_pos.mpr hxlt)
  let K : ℝ := Finset.univ.sup' Finset.univ_nonempty ratio
  have hratio_le (a : A) : ratio a ≤ K := by
    exact Finset.le_sup' ratio (Finset.mem_univ a)
  have hKpos : 0 < K := hratio_pos.trans_le (hratio_le a₁)
  obtain ⟨a₀, -, hKmax⟩ :=
    Finset.exists_mem_eq_sup' Finset.univ_nonempty ratio
  refine ⟨K⁻¹, inv_pos.mpr hKpos, ?_, ?_⟩
  · intro a
    by_cases hp : 0 < z a
    · have hden : 0 < 1 - x a := sub_pos.mpr (hstrict a hp.ne').2
      have hr : z a / (1 - x a) ≤ K := by
        simpa only [ratio, if_pos hp] using hratio_le a
      have hzle : z a / K ≤ 1 - x a := by
        apply (div_le_iff₀ hKpos).2
        have := (div_le_iff₀ hden).1 hr
        simpa only [mul_comm] using this
      have hstep : K⁻¹ * z a = z a / K := by
        simp [div_eq_mul_inv, mul_comm]
      rw [hstep]
      have hzdiv : 0 ≤ z a / K := div_nonneg hp.le hKpos.le
      exact ⟨add_nonneg (hx a).1 hzdiv, by linarith⟩
    · by_cases hn : z a < 0
      · have hden : 0 < x a := (hstrict a hn.ne).1
        have hr : (-z a) / x a ≤ K := by
          simpa only [ratio, if_neg hp, if_pos hn] using hratio_le a
        have hzle : (-z a) / K ≤ x a := by
          apply (div_le_iff₀ hKpos).2
          have := (div_le_iff₀ hden).1 hr
          simpa only [mul_comm] using this
        have hstep : K⁻¹ * z a = z a / K := by
          simp [div_eq_mul_inv, mul_comm]
        rw [hstep]
        have hzneg : z a / K = -((-z a) / K) := by ring
        rw [hzneg]
        have hzdiv : 0 ≤ (-z a) / K :=
          div_nonneg (neg_nonneg.mpr hn.le) hKpos.le
        constructor <;> nlinarith [hx a]
      · have hz0 : z a = 0 := le_antisymm (not_lt.mp hp) (not_lt.mp hn)
        simp [hz0, hx a]
  · have hratio_a₀_pos : 0 < ratio a₀ := by
      rw [← hKmax]
      exact hKpos
    have hza₀ : z a₀ ≠ 0 := by
      intro hz0
      simp [ratio, hz0] at hratio_a₀_pos
    rcases lt_or_gt_of_ne hza₀ with hn | hp
    · have hxpos : 0 < x a₀ := (hstrict a₀ hza₀).1
      have hratio_eq : K = (-z a₀) / x a₀ := by
        simpa only [ratio, if_neg (not_lt.mpr hn.le), if_pos hn] using hKmax
      have hnum : -z a₀ = K * x a₀ :=
        (div_eq_iff hxpos.ne').1 hratio_eq.symm
      have hstep : K⁻¹ * z a₀ = -x a₀ := by
        calc
          K⁻¹ * z a₀ = z a₀ / K := by
            simp [div_eq_mul_inv, mul_comm]
          _ = -x a₀ := by
            apply (div_eq_iff hKpos.ne').2
            nlinarith [hnum]
      exact ⟨a₀, hza₀, Or.inl (by rw [hstep]; ring)⟩
    · have hxlt : x a₀ < 1 := (hstrict a₀ hza₀).2
      have hratio_eq : K = z a₀ / (1 - x a₀) := by
        simpa only [ratio, if_pos hp] using hKmax
      have hnum : z a₀ = K * (1 - x a₀) :=
        (div_eq_iff (sub_pos.mpr hxlt).ne').1 hratio_eq.symm
      have hstep : K⁻¹ * z a₀ = 1 - x a₀ := by
        calc
          K⁻¹ * z a₀ = z a₀ / K := by
            simp [div_eq_mul_inv, mul_comm]
          _ = 1 - x a₀ := by
            apply (div_eq_iff hKpos.ne').2
            nlinarith [hnum]
      exact ⟨a₀, hza₀, Or.inr (by rw [hstep]; ring)⟩

/-- A rank-deficient retained system admits a feasible move that freezes at
least one additional coordinate.  The weights are completely arbitrary;
the zero-one and sparsity hypotheses enter only in the later iteration. -/
theorem exists_floating_step
    {A E : Type*} [Fintype A] [Fintype E]
    (w : E → A → ℝ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hcard : Fintype.card E < (fractionalSupport x).card) :
    ∃ x' : A → ℝ,
      (∀ a, 0 ≤ x' a ∧ x' a ≤ 1) ∧
      (∀ a, x a = 0 ∨ x a = 1 → x' a = x a) ∧
      (∀ e, ∑ a, w e a * x' a = ∑ a, w e a * x a) ∧
      (fractionalSupport x').card < (fractionalSupport x).card := by
  classical
  let F : Finset A := fractionalSupport x
  let outside : Finset A := Finset.univ \ F
  let I : Type _ := ↥outside
  let L : (A → ℝ) →ₗ[ℝ] (Sum E I → ℝ) :=
    { toFun := fun z i ↦ match i with
        | Sum.inl e => ∑ a, w e a * z a
        | Sum.inr a => z a.1
      map_add' := by
        intro z z'
        funext i
        cases i with
        | inl e => simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
        | inr a => simp
      map_smul' := by
        intro c z
        funext i
        cases i with
        | inl e =>
            simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro a _
            change w e a * (c * z a) = c * (w e a * z a)
            ring
        | inr a => simp }
  have houtside : outside.card + F.card = Fintype.card A := by
    simpa only [outside, Finset.card_univ] using
      Finset.card_sdiff_add_card_eq_card (Finset.subset_univ F)
  have hdimNat : Fintype.card E + Fintype.card I < Fintype.card A := by
    have hIcard : Fintype.card I = outside.card := Fintype.card_coe outside
    have hcard' : Fintype.card E < F.card := by
      simpa only [F] using hcard
    rw [hIcard]
    omega
  have hdim :
      Module.finrank ℝ (Sum E I → ℝ) < Module.finrank ℝ (A → ℝ) := by
    simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_sum] using hdimNat
  have hker : LinearMap.ker L ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hdim
  obtain ⟨z, hzker, hzne⟩ := (LinearMap.ker L).ne_bot_iff.mp hker
  have hLzero : L z = 0 := hzker
  have hzoutside (a : A) (ha : a ∉ F) : z a = 0 := by
    have hai : a ∈ outside := by simp [outside, ha]
    have h := congrFun hLzero (Sum.inr (⟨a, hai⟩ : I))
    simpa only [L, Pi.zero_apply] using h
  have hzstrict (a : A) (hza : z a ≠ 0) : 0 < x a ∧ x a < 1 := by
    have haF : a ∈ F := by
      by_contra ha
      exact hza (hzoutside a ha)
    have hmem : x a ≠ 0 ∧ x a ≠ 1 := by
      simpa only [F, mem_fractionalSupport] using haF
    exact ⟨lt_of_le_of_ne (hx a).1 hmem.1.symm,
      lt_of_le_of_ne (hx a).2 hmem.2⟩
  obtain ⟨t, ht, hbounds, a₀, hza₀, ha₀⟩ :=
    exists_positive_boundary_step x z hx hzstrict hzne
  let x' : A → ℝ := fun a ↦ x a + t * z a
  refine ⟨x', ?_, ?_, ?_, ?_⟩
  · exact hbounds
  · intro a ha
    have haF : a ∉ F := by
      intro hmem
      have hfrac : x a ≠ 0 ∧ x a ≠ 1 := by
        simpa only [F, mem_fractionalSupport] using hmem
      exact ha.elim hfrac.1 hfrac.2
    simp [x', hzoutside a haF]
  · intro e
    have heq := congrFun hLzero (Sum.inl e)
    have hsumz : ∑ a, w e a * z a = 0 := by
      simpa only [L, Pi.zero_apply] using heq
    simp only [x', mul_add, Finset.sum_add_distrib]
    have hweighted : ∑ a, w e a * (t * z a) =
        t * ∑ a, w e a * z a := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [hweighted, hsumz, mul_zero, add_zero]
  · have hsub : fractionalSupport x' ⊆ fractionalSupport x := by
      intro a ha
      by_contra haF
      have hz0 : z a = 0 := hzoutside a (by simpa only [F] using haF)
      have hxa : x' a = x a := by simp [x', hz0]
      have hnot : a ∉ fractionalSupport x := by simpa only [F] using haF
      have hfrac := mem_fractionalSupport.mp ha
      exact hnot (mem_fractionalSupport.mpr (by simpa only [hxa] using hfrac))
    have ha₀F : a₀ ∈ fractionalSupport x := by
      by_contra hnot
      exact hza₀ (hzoutside a₀ (by simpa only [F] using hnot))
    have ha₀not : a₀ ∉ fractionalSupport x' := by
      rw [mem_fractionalSupport]
      exact fun h ↦ ha₀.elim h.1 h.2
    exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨hsub, fun heq ↦ ha₀not (heq ▸ ha₀F)⟩)

end

end Erdos390.WholePaper
