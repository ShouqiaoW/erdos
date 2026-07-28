import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstMainAsymptoticConnector
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

/-!
# Formal Conjectures bridge for Erdős 390

This module deliberately has no dependency on the `formal-conjectures`
repository. It gives a namespaced literal copy of that repository's
extremal function, identifies it eventually with `Erdos390.WholePaper.f`,
and exports the two conclusion shapes used upstream.

The namespace is nested below `Erdos390.WholePaper`, so this module can be
imported together with `FormalConjectures.ErdosProblems.390` without
colliding with its declarations `Erdos390.f`, `Erdos390.erdos_390`, or
`Erdos390.erdos_390.variants.theta`.
-/

open scoped Nat BigOperators
open Filter Asymptotics Real

namespace Erdos390.WholePaper.FormalConjecturesBridge

noncomputable section

/-! ## Literal Formal Conjectures endpoint model -/

/-- The endpoint predicate used by the Formal Conjectures formulation. -/
def FCAdmissible (n m : ℕ) : Prop :=
  ∃ k, ∃ g : ℕ → ℕ, StrictMono g ∧
    n < g 0 ∧ g (k - 1) = m ∧ ∏ i < k, g i = n.factorial

/-- A literal, independently namespaced copy of the Formal Conjectures
extremal function. -/
noncomputable def formalF (n : ℕ) : ℕ :=
  sInf {m : ℕ | ∃ k, ∃ g : ℕ → ℕ, StrictMono g ∧
    n < g 0 ∧ g (k - 1) = m ∧ ∏ i < k, g i = n.factorial}

theorem formalF_eq_sInf_FCAdmissible (n : ℕ) :
    formalF n = sInf {m : ℕ | FCAdmissible n m} := by
  rfl

/-! ## Pointwise endpoint bridge -/

/-- A Formal Conjectures strictly increasing prefix gives the corresponding
finite set of distinct factors. -/
theorem fcAdmissible_to_isAdmissibleEndpoint {n m : ℕ} (hn : 3 ≤ n)
    (h : FCAdmissible n m) :
    Erdos390.WholePaper.IsAdmissibleEndpoint n m := by
  rcases h with ⟨k, g, hg, hg0, hlast, hprod⟩
  rw [Nat.Iio_eq_range] at hprod
  have hk : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    subst k
    simp only [Finset.range_zero, Finset.prod_empty] at hprod
    have hn_le_one : n ≤ 1 := Nat.factorial_eq_one.mp hprod.symm
    omega
  refine ⟨(Finset.range k).image g, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    have hi_lt : i < k := Finset.mem_range.mp hi
    rw [Erdos390.WholePaper.factorInterval, Finset.mem_Ioc]
    constructor
    · exact hg0.trans_le (hg.monotone (Nat.zero_le i))
    · rw [← hlast]
      exact hg.monotone (by omega)
  · calc
      ((Finset.range k).image g).prod id =
          (Finset.range k).prod (fun i ↦ id (g i)) :=
        Finset.prod_image hg.injective.injOn
      _ = n.factorial := by simpa using hprod

/-- Every finite admissible set can be increasingly enumerated and extended
to a globally strictly increasing sequence. -/
theorem isAdmissibleEndpoint_to_exists_fcAdmissible {n M : ℕ} (hn : 3 ≤ n)
    (hM : Erdos390.WholePaper.IsAdmissibleEndpoint n M) :
    ∃ m ≤ M, FCAdmissible n m := by
  rcases hM with ⟨S, hS, hprod⟩
  have hS_nonempty : S.Nonempty := by
    by_contra hnot
    have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnot
    subst S
    simp only [Finset.prod_empty] at hprod
    have hn_le_one : n ≤ 1 := Nat.factorial_eq_one.mp hprod.symm
    omega
  let k : ℕ := S.card
  have hk : 0 < k := by
    simpa only [k] using Finset.card_pos.mpr hS_nonempty
  have hcard : S.card = k := rfl
  let e : Fin k ↪o ℕ := S.orderEmbOfFin hcard
  let g : ℕ → ℕ := fun i ↦
    if hi : i < k then e ⟨i, hi⟩ else M + i
  have hg : StrictMono g := by
    intro i j hij
    by_cases hi : i < k
    · by_cases hj : j < k
      · simp only [g, dif_pos hi, dif_pos hj]
        exact e.strictMono hij
      · have hei_mem : e ⟨i, hi⟩ ∈ S := by
          simpa only [e] using S.orderEmbOfFin_mem hcard ⟨i, hi⟩
        have hei_le : e ⟨i, hi⟩ ≤ M :=
          (Finset.mem_Ioc.mp (hS hei_mem)).2
        have hj_pos : 0 < j := by omega
        simp only [g, dif_pos hi, dif_neg hj]
        omega
    · have hj : ¬j < k := by omega
      simp only [g, dif_neg hi, dif_neg hj]
      omega
  have hlast_lt : k - 1 < k := by omega
  let m : ℕ := e ⟨k - 1, hlast_lt⟩
  have hm_mem : m ∈ S := by
    simpa only [m, e] using S.orderEmbOfFin_mem hcard ⟨k - 1, hlast_lt⟩
  have hm_le : m ≤ M := (Finset.mem_Ioc.mp (hS hm_mem)).2
  refine ⟨m, hm_le, k, g, hg, ?_, ?_, ?_⟩
  · have he0_mem : e ⟨0, hk⟩ ∈ S := by
      simpa only [e] using S.orderEmbOfFin_mem hcard ⟨0, hk⟩
    have hn_e0 : n < e ⟨0, hk⟩ :=
      (Finset.mem_Ioc.mp (hS he0_mem)).1
    simpa only [g, dif_pos hk] using hn_e0
  · simp only [g, m, dif_pos hlast_lt]
  · rw [Nat.Iio_eq_range]
    have himage : (Finset.range k).image g = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        have hi_lt : i < k := Finset.mem_range.mp hi
        simp only [g, dif_pos hi_lt]
        simpa only [e] using S.orderEmbOfFin_mem hcard ⟨i, hi_lt⟩
      · rw [Finset.card_image_of_injective _ hg.injective, Finset.card_range, hcard]
    calc
      (Finset.range k).prod g =
          ((Finset.range k).image g).prod id := by
        symm
        exact Finset.prod_image hg.injective.injOn
      _ = S.prod id := by rw [himage]
      _ = n.factorial := hprod

/-- For `n ≥ 3`, the independently defined endpoint minima coincide. -/
theorem formalF_eq_wholePaper_f {n : ℕ} (hn : 3 ≤ n) :
    formalF n = Erdos390.WholePaper.f n := by
  rw [formalF_eq_sInf_FCAdmissible]
  apply le_antisymm
  · obtain ⟨m, hm, hfc⟩ :=
      isAdmissibleEndpoint_to_exists_fcAdmissible hn
        (Erdos390.WholePaper.f_spec hn)
    exact (Nat.sInf_le hfc).trans hm
  · have hset_nonempty : Set.Nonempty {m : ℕ | FCAdmissible n m} := by
      obtain ⟨m, _hm, hfc⟩ :=
        isAdmissibleEndpoint_to_exists_fcAdmissible hn
          (Erdos390.WholePaper.f_spec hn)
      exact ⟨m, hfc⟩
    have hmin : FCAdmissible n (sInf {m : ℕ | FCAdmissible n m}) :=
      Nat.sInf_mem hset_nonempty
    exact Erdos390.WholePaper.f_le_of_admissible hn
      (fcAdmissible_to_isAdmissibleEndpoint hn hmin)

/-- The two endpoint functions are eventually equal; the exceptional values
`n < 3` are irrelevant to all `atTop` statements. -/
theorem eventually_formalF_eq_wholePaper_f :
    formalF =ᶠ[atTop] Erdos390.WholePaper.f :=
  eventually_atTop.2 ⟨3, fun _n hn ↦ formalF_eq_wholePaper_f hn⟩

/-! ## Small-o to asymptotic-equivalence wrapper -/

private lemma C0_ne_zero : Erdos390.WholePaper.C0 ≠ 0 := by
  norm_num [Erdos390.WholePaper.C0]

/-- The local literal small-o theorem implies equivalence with its fixed
second-order coefficient. -/
theorem wholePaper_isEquivalent_fixedC0_of_mainAsymptotic
    (h : Erdos390.WholePaper.MainAsymptotic) :
    (fun n : ℕ =>
        (Erdos390.WholePaper.f n : ℝ) - 2 * (n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        Erdos390.WholePaper.C0 * (n : ℝ) / Real.log (n : ℝ)) := by
  have hsmall :
      Erdos390.WholePaper.mainError =o[atTop]
        Erdos390.WholePaper.secondOrderScale := by
    simpa only [Erdos390.WholePaper.MainAsymptotic] using h
  have hscaled :
      Erdos390.WholePaper.mainError =o[atTop]
        (fun n : ℕ =>
          Erdos390.WholePaper.C0 *
            Erdos390.WholePaper.secondOrderScale n) :=
    hsmall.const_mul_right C0_ne_zero
  rw [IsEquivalent]
  have hleft :
      (fun n : ℕ =>
          (Erdos390.WholePaper.f n : ℝ) - 2 * (n : ℝ)) -
          (fun n : ℕ =>
            Erdos390.WholePaper.C0 * (n : ℝ) /
              Real.log (n : ℝ)) =
        Erdos390.WholePaper.mainError := by
    funext n
    simp only [Pi.sub_apply, Erdos390.WholePaper.mainError,
      Erdos390.WholePaper.secondOrderScale, sub_add_eq_sub_sub,
      mul_div_assoc]
  rw [hleft]
  simpa only [Erdos390.WholePaper.secondOrderScale, mul_div_assoc] using hscaled

/-- The local small-o theorem, together with the endpoint bridge, implies
fixed-coefficient equivalence for the literal Formal Conjectures function. -/
theorem formalF_isEquivalent_fixedC0_of_mainAsymptotic
    (h : Erdos390.WholePaper.MainAsymptotic) :
    (fun n : ℕ => (formalF n : ℝ) - 2 * (n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        Erdos390.WholePaper.C0 * (n : ℝ) / Real.log (n : ℝ)) := by
  have hleft :
      (fun n : ℕ => (formalF n : ℝ) - 2 * (n : ℝ)) =ᶠ[atTop]
        (fun n : ℕ =>
          (Erdos390.WholePaper.f n : ℝ) - 2 * (n : ℝ)) :=
    eventually_formalF_eq_wholePaper_f.mono fun n hn ↦ by
      change
        (formalF n : ℝ) - 2 * (n : ℝ) =
          (Erdos390.WholePaper.f n : ℝ) - 2 * (n : ℝ)
      rw [hn]
  exact hleft.trans_isEquivalent
    (wholePaper_isEquivalent_fixedC0_of_mainAsymptotic h)

/-- Closed fixed-coefficient equivalence for the literal Formal Conjectures
endpoint function. -/
theorem formalF_isEquivalent_fixedC0 :
    (fun n : ℕ => (formalF n : ℝ) - 2 * (n : ℝ)) ~[atTop]
      (fun n : ℕ =>
        Erdos390.WholePaper.C0 * (n : ℝ) / Real.log (n : ℝ)) :=
  formalF_isEquivalent_fixedC0_of_mainAsymptotic
    Erdos390.WholePaper.bankPaperCanonicalSectionNinePostHeight_sourceFirstMainAsymptotic

/-! ## Exact upstream conclusion shapes -/

/-- Exact statement shape of
`Erdos390.erdos_390.variants.theta`, with the collision-free `formalF`. -/
theorem formalF_theta :
    (fun n => formalF n - 2 * n : ℕ → ℝ) =Θ[atTop]
      (fun n => n / log (n : ℝ)) := by
  have hscaled :
      (fun n => formalF n - 2 * n : ℕ → ℝ) =Θ[atTop]
        (fun n =>
          Erdos390.WholePaper.C0 * (n / log (n : ℝ))) := by
    simpa only [mul_div_assoc] using formalF_isEquivalent_fixedC0.isTheta
  exact (isTheta_const_mul_right C0_ne_zero).mp hscaled

/-- Exact right-hand-side shape of `Erdos390.erdos_390`, with witness
`Erdos390.WholePaper.C0`. -/
theorem formalF_rhs :
    ∃ c,
      (fun n => formalF n - 2 * n : ℕ → ℝ) ~[atTop]
        (fun n => c * n / log (n : ℝ)) :=
  ⟨Erdos390.WholePaper.C0, formalF_isEquivalent_fixedC0⟩

/-! ## Adapter API for a jointly imported upstream function -/

/-- Transfer the exact theta conclusion to any endpoint function eventually
equal to `formalF`. A downstream module importing the upstream conjecture
can instantiate `g := Erdos390.f`; its two literal definitions agree by
`rfl`. -/
theorem theta_of_eventuallyEq_formalF {g : ℕ → ℕ}
    (hg : g =ᶠ[atTop] formalF) :
    (fun n => g n - 2 * n : ℕ → ℝ) =Θ[atTop]
      (fun n => n / log (n : ℝ)) := by
  have hleft :
      (fun n => g n - 2 * n : ℕ → ℝ) =ᶠ[atTop]
        (fun n => formalF n - 2 * n : ℕ → ℝ) :=
    hg.mono fun n hn ↦ by
      change
        (g n : ℝ) - 2 * (n : ℝ) =
          (formalF n : ℝ) - 2 * (n : ℝ)
      rw [hn]
  exact hleft.trans_isTheta formalF_theta

/-- Transfer the exact open-problem right-hand side to any endpoint function
eventually equal to `formalF`. -/
theorem rhs_of_eventuallyEq_formalF {g : ℕ → ℕ}
    (hg : g =ᶠ[atTop] formalF) :
    ∃ c,
      (fun n => g n - 2 * n : ℕ → ℝ) ~[atTop]
        (fun n => c * n / log (n : ℝ)) := by
  refine ⟨Erdos390.WholePaper.C0, ?_⟩
  have hleft :
      (fun n => g n - 2 * n : ℕ → ℝ) =ᶠ[atTop]
        (fun n => formalF n - 2 * n : ℕ → ℝ) :=
    hg.mono fun n hn ↦ by
      change
        (g n : ℝ) - 2 * (n : ℝ) =
          (formalF n : ℝ) - 2 * (n : ℝ)
      rw [hn]
  exact hleft.trans_isEquivalent formalF_isEquivalent_fixedC0

end

end Erdos390.WholePaper.FormalConjecturesBridge
