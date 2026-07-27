import Erdos536.CubeMaximum

/-!
# Finite mixtures of cube laws

A sample from a mixture consists of a component index together with a
certified sample from that component.  The sigma type is important here:
different components may use genuinely different sample types.
-/

open scoped BigOperators
open Finset

namespace Erdos536

private theorem FiniteCubeLaw.subtype_mass_sum_mixture
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) :
    ∑ a : ↥L.samples, L.mass a = 1 := by
  simpa only [Finset.sum_coe_sort] using L.mass_sum

/-- A weighted mixture of finitely many cube laws.  Component sample types
may depend on the component index. -/
noncomputable def FiniteCubeLaw.weightedMixture
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (weight : ι → ℝ)
    (weight_nonneg : ∀ i, 0 ≤ weight i)
    (weight_sum : ∑ i, weight i = 1) :
    FiniteCubeLaw (Σ i, ↥(L i).samples) H R where
  samples := Finset.univ
  mass := fun x ↦ weight x.1 * (L x.1).mass x.2
  cube := fun x ↦ (L x.1).cube x.2
  mass_nonneg := by
    intro x _hx
    exact mul_nonneg (weight_nonneg x.1)
      ((L x.1).mass_nonneg x.2 x.2.property)
  mass_sum := by
    simp only [Fintype.sum_sigma]
    calc
      (∑ i, ∑ a : ↥(L i).samples, weight i * (L i).mass a) =
          ∑ i, weight i * ∑ a : ↥(L i).samples, (L i).mass a := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
      _ = ∑ i, weight i := by
            apply Finset.sum_congr rfl
            intro i _hi
            rw [(L i).subtype_mass_sum_mixture, mul_one]
      _ = 1 := weight_sum
  wordSupport_subset := by
    intro x _hx ω
    exact (L x.1).wordSupport_subset x.2 x.2.property ω

@[simp]
theorem FiniteCubeLaw.weightedMixture_samples
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (weight : ι → ℝ)
    (weight_nonneg : ∀ i, 0 ≤ weight i)
    (weight_sum : ∑ i, weight i = 1) :
    (FiniteCubeLaw.weightedMixture α L weight
      weight_nonneg weight_sum).samples = Finset.univ := rfl

@[simp]
theorem FiniteCubeLaw.weightedMixture_mass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (weight : ι → ℝ)
    (weight_nonneg : ∀ i, 0 ≤ weight i)
    (weight_sum : ∑ i, weight i = 1)
    (x : Σ i, ↥(L i).samples) :
    (FiniteCubeLaw.weightedMixture α L weight
      weight_nonneg weight_sum).mass x =
        weight x.1 * (L x.1).mass x.2 := rfl

@[simp]
theorem FiniteCubeLaw.weightedMixture_cube
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (weight : ι → ℝ)
    (weight_nonneg : ∀ i, 0 ≤ weight i)
    (weight_sum : ∑ i, weight i = 1)
    (x : Σ i, ↥(L i).samples) :
    (FiniteCubeLaw.weightedMixture α L weight
      weight_nonneg weight_sum).cube x =
        (L x.1).cube x.2 := rfl

/-- A support marginal of a mixture is exactly the corresponding weighted
mixture of the component marginals. -/
theorem FiniteCubeLaw.weightedMixture_wordSupportMass
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (weight : ι → ℝ)
    (weight_nonneg : ∀ i, 0 ≤ weight i)
    (weight_sum : ∑ i, weight i = 1)
    (ω : Fin H → ZMod 3) (S : Finset ℕ) :
    (FiniteCubeLaw.weightedMixture α L weight
      weight_nonneg weight_sum).wordSupportMass ω S =
        ∑ i, weight i * (L i).wordSupportMass ω S := by
  classical
  rw [FiniteCubeLaw.wordSupportMass]
  simp only [FiniteCubeLaw.weightedMixture, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [FiniteCubeLaw.wordSupportMass]
  calc
    (∑ a : ↥(L i).samples,
        if ((L i).cube a).wordSupport ω = S then
          weight i * (L i).mass a else 0) =
        ∑ a : ↥(L i).samples,
          weight i *
            (if ((L i).cube a).wordSupport ω = S then
              (L i).mass a else 0) := by
                apply Finset.sum_congr rfl
                intro a _ha
                by_cases hS : ((L i).cube a).wordSupport ω = S <;>
                  simp [hS]
    _ = weight i *
          ∑ a : ↥(L i).samples,
            if ((L i).cube a).wordSupport ω = S then
              (L i).mass a else 0 := by
            rw [Finset.mul_sum]
    _ = weight i *
          ∑ a ∈ (L i).samples,
            if ((L i).cube a).wordSupport ω = S then
              (L i).mass a else 0 := by
            congr 1
            exact Finset.sum_coe_sort (L i).samples
              (fun a ↦
                if ((L i).cube a).wordSupport ω = S then
                  (L i).mass a else 0)

/-- Multiplicative balance is a componentwise property, hence is inherited
by every finite weighted mixture. -/
theorem FiniteCubeLaw.weightedMixture_multiplicativelyBalanced
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (weight : ι → ℝ)
    (weight_nonneg : ∀ i, 0 ≤ weight i)
    (weight_sum : ∑ i, weight i = 1)
    {δ : ℝ}
    (hbalanced : ∀ i, (L i).MultiplicativelyBalanced δ) :
    (FiniteCubeLaw.weightedMixture α L weight
      weight_nonneg weight_sum).MultiplicativelyBalanced δ := by
  intro x _hx ω τ
  exact hbalanced x.1 x.2 x.2.property ω τ

/-- The `L¹` error of a weighted mixture is at most the weighted average
of the component errors. -/
theorem FiniteCubeLaw.weightedMixture_wordSupportDistance_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (α : ι → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (weight : ι → ℝ)
    (weight_nonneg : ∀ i, 0 ≤ weight i)
    (weight_sum : ∑ i, weight i = 1)
    (ω : Fin H → ZMod 3) :
    (FiniteCubeLaw.weightedMixture α L weight
      weight_nonneg weight_sum).wordSupportDistance ω ≤
        ∑ i, weight i * (L i).wordSupportDistance ω := by
  classical
  have hpoint :
      ∀ S : Finset ℕ,
        |(∑ i, weight i * (L i).wordSupportMass ω S) -
            1 / (squarefreeZ R * (primeProduct S : ℝ))| ≤
          ∑ i, weight i *
            |(L i).wordSupportMass ω S -
              1 / (squarefreeZ R * (primeProduct S : ℝ))| := by
    intro S
    let q : ℝ := 1 / (squarefreeZ R * (primeProduct S : ℝ))
    have hrewrite :
        (∑ i, weight i * (L i).wordSupportMass ω S) - q =
          ∑ i, weight i * ((L i).wordSupportMass ω S - q) := by
      calc
        (∑ i, weight i * (L i).wordSupportMass ω S) - q =
            (∑ i, weight i * (L i).wordSupportMass ω S) -
              (∑ i, weight i) * q := by rw [weight_sum, one_mul]
        _ = (∑ i, weight i * (L i).wordSupportMass ω S) -
              ∑ i, weight i * q := by
                rw [Finset.sum_mul]
        _ = ∑ i, ((weight i * (L i).wordSupportMass ω S) -
              (weight i * q)) := by
                  rw [Finset.sum_sub_distrib]
        _ = ∑ i, weight i * ((L i).wordSupportMass ω S - q) := by
              apply Finset.sum_congr rfl
              intro i _hi
              ring
    change
      |(∑ i, weight i * (L i).wordSupportMass ω S) - q| ≤
        ∑ i, weight i * |(L i).wordSupportMass ω S - q|
    rw [hrewrite]
    calc
      |∑ i, weight i * ((L i).wordSupportMass ω S - q)| ≤
          ∑ i, |weight i *
            ((L i).wordSupportMass ω S - q)| :=
        Finset.abs_sum_le_sum_abs
          (fun i ↦ weight i *
            ((L i).wordSupportMass ω S - q)) Finset.univ
      _ = ∑ i, weight i *
            |(L i).wordSupportMass ω S - q| := by
              apply Finset.sum_congr rfl
              intro i _hi
              rw [abs_mul, abs_of_nonneg (weight_nonneg i)]
  rw [FiniteCubeLaw.wordSupportDistance]
  simp_rw [FiniteCubeLaw.weightedMixture_wordSupportMass]
  calc
    (∑ S ∈ R.powerset,
        |(∑ i, weight i * (L i).wordSupportMass ω S) -
          1 / (squarefreeZ R * (primeProduct S : ℝ))|) ≤
        ∑ S ∈ R.powerset, ∑ i, weight i *
          |(L i).wordSupportMass ω S -
            1 / (squarefreeZ R * (primeProduct S : ℝ))| := by
              apply Finset.sum_le_sum
              intro S _hS
              exact hpoint S
    _ = ∑ i, weight i *
          ∑ S ∈ R.powerset,
            |(L i).wordSupportMass ω S -
              1 / (squarefreeZ R * (primeProduct S : ℝ))| := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [Finset.mul_sum]
    _ = ∑ i, weight i * (L i).wordSupportDistance ω := by
          rfl

/-- The uniform mixture of `M > 0` finite cube laws. -/
noncomputable def FiniteCubeLaw.uniformMixture
    {M : ℕ} (hM : 0 < M)
    (α : Fin M → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R) :
    FiniteCubeLaw (Σ i, ↥(L i).samples) H R :=
  FiniteCubeLaw.weightedMixture α L
    (fun _ ↦ (M : ℝ)⁻¹)
    (fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg M))
    (by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      rw [mul_inv_cancel₀]
      exact_mod_cast hM.ne')

/-- Each word marginal of the uniform mixture is the arithmetic average of
the corresponding component marginals. -/
theorem FiniteCubeLaw.uniformMixture_wordSupportMass
    {M : ℕ} (hM : 0 < M)
    (α : Fin M → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (ω : Fin H → ZMod 3) (S : Finset ℕ) :
    (FiniteCubeLaw.uniformMixture hM α L).wordSupportMass ω S =
      (M : ℝ)⁻¹ * ∑ i, (L i).wordSupportMass ω S := by
  rw [FiniteCubeLaw.uniformMixture,
    FiniteCubeLaw.weightedMixture_wordSupportMass]
  rw [Finset.mul_sum]

/-- A uniform mixture inherits a common multiplicative-balance bound. -/
theorem FiniteCubeLaw.uniformMixture_multiplicativelyBalanced
    {M : ℕ} (hM : 0 < M)
    (α : Fin M → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    {δ : ℝ}
    (hbalanced : ∀ i, (L i).MultiplicativelyBalanced δ) :
    (FiniteCubeLaw.uniformMixture hM α L).MultiplicativelyBalanced δ := by
  apply FiniteCubeLaw.weightedMixture_multiplicativelyBalanced
  exact hbalanced

/-- Convexity of support-law error for the uniform mixture. -/
theorem FiniteCubeLaw.uniformMixture_wordSupportDistance_le
    {M : ℕ} (hM : 0 < M)
    (α : Fin M → Type*) [∀ i, DecidableEq (α i)]
    {H : ℕ} {R : Finset ℕ}
    (L : ∀ i, FiniteCubeLaw (α i) H R)
    (ω : Fin H → ZMod 3) :
    (FiniteCubeLaw.uniformMixture hM α L).wordSupportDistance ω ≤
      (M : ℝ)⁻¹ * ∑ i, (L i).wordSupportDistance ω := by
  have hsum : ∑ _ : Fin M, (M : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [mul_inv_cancel₀]
    exact_mod_cast hM.ne'
  have hconvex :=
    FiniteCubeLaw.weightedMixture_wordSupportDistance_le
      α L (fun _ ↦ (M : ℝ)⁻¹)
      (fun _ ↦ inv_nonneg.mpr (Nat.cast_nonneg M)) hsum ω
  calc
    (FiniteCubeLaw.uniformMixture hM α L).wordSupportDistance ω ≤
        ∑ i, (M : ℝ)⁻¹ * (L i).wordSupportDistance ω := by
          simpa only [FiniteCubeLaw.uniformMixture] using hconvex
    _ = (M : ℝ)⁻¹ * ∑ i, (L i).wordSupportDistance ω := by
          rw [Finset.mul_sum]

end Erdos536
