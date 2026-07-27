import Erdos536.BalancedCubeCutoff

/-!
# The maximum product in a finite pair-product cube

The common cutoff construction uses the largest word product of each sampled
cube.  Since the word space is finite, this maximum is an elementary finite
supremum.  The lemmas below package all three side conditions required by
`FiniteCubeLaw.toCutoffLaw`.
-/

open Finset

namespace Erdos536

/-- Largest integer represented by a word of a pair-product cube. -/
noncomputable def PairProductCube.maxWordProduct {H : ℕ}
    (c : PairProductCube H) : ℕ :=
  (Finset.univ : Finset (Fin H → ZMod 3)).sup
    fun ω => primeProduct (c.wordSupport ω)

theorem PairProductCube.wordProduct_le_max {H : ℕ}
    (c : PairProductCube H) (ω : Fin H → ZMod 3) :
    primeProduct (c.wordSupport ω) ≤ c.maxWordProduct := by
  exact Finset.le_sup (s := Finset.univ)
    (f := fun τ => primeProduct (c.wordSupport τ))
    (Finset.mem_univ ω)

theorem PairProductCube.one_le_maxWordProduct {H : ℕ}
    (c : PairProductCube H) {R : Finset ℕ}
    (hR : IsPrimeSupport R)
    (hsub : ∀ ω : Fin H → ZMod 3, c.wordSupport ω ⊆ R) :
    1 ≤ c.maxWordProduct := by
  let ω : Fin H → ZMod 3 := fun _ => 0
  have hword : 1 ≤ primeProduct (c.wordSupport ω) :=
    primeProduct_pos (isPrimeSupport_mono hR (hsub ω))
  exact hword.trans (c.wordProduct_le_max ω)

theorem PairProductCube.maxWordProduct_le_total {H : ℕ}
    (c : PairProductCube H) {R : Finset ℕ}
    (hR : IsPrimeSupport R)
    (hsub : ∀ ω : Fin H → ZMod 3, c.wordSupport ω ⊆ R) :
    c.maxWordProduct ≤ primeProduct R := by
  apply Finset.sup_le
  intro ω _hω
  exact primeProduct_le_total hR (hsub ω)

/-- The maximum-product cutoff attached pointwise to a finite cube law. -/
noncomputable def FiniteCubeLaw.maxWordProduct
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (a : α) : ℕ :=
  (L.cube a).maxWordProduct

theorem FiniteCubeLaw.one_le_maxWordProduct
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    {a : α} (ha : a ∈ L.samples) :
    1 ≤ L.maxWordProduct a := by
  exact (L.cube a).one_le_maxWordProduct hR
    (fun ω => L.wordSupport_subset a ha ω)

theorem FiniteCubeLaw.maxWordProduct_le_total
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    {a : α} (ha : a ∈ L.samples) :
    L.maxWordProduct a ≤ primeProduct R := by
  exact (L.cube a).maxWordProduct_le_total hR
    (fun ω => L.wordSupport_subset a ha ω)

theorem FiniteCubeLaw.wordProduct_le_max
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (a : α) (ω : Fin H → ZMod 3) :
    primeProduct ((L.cube a).wordSupport ω) ≤ L.maxWordProduct a :=
  (L.cube a).wordProduct_le_max ω

/-- Every two words of every sampled cube differ by at most the displayed
multiplicative factor. -/
def FiniteCubeLaw.MultiplicativelyBalanced
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (δ : ℝ) : Prop :=
  ∀ a ∈ L.samples, ∀ ω τ : Fin H → ZMod 3,
    (primeProduct ((L.cube a).wordSupport τ) : ℝ) ≤
      (1 + δ) *
        (primeProduct ((L.cube a).wordSupport ω) : ℝ)

theorem FiniteCubeLaw.maxWordProduct_cast_le_of_balanced
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) {δ : ℝ}
    (hbalance : L.MultiplicativelyBalanced δ)
    {a : α} (ha : a ∈ L.samples) (ω : Fin H → ZMod 3) :
    (L.maxWordProduct a : ℝ) ≤
      (1 + δ) *
        (primeProduct ((L.cube a).wordSupport ω) : ℝ) := by
  rw [FiniteCubeLaw.maxWordProduct, PairProductCube.maxWordProduct]
  obtain ⟨τ, _hτ, hτ⟩ :=
    Finset.exists_mem_eq_sup
      (Finset.univ : Finset (Fin H → ZMod 3))
      Finset.univ_nonempty
      (fun σ => primeProduct ((L.cube a).wordSupport σ))
  rw [hτ]
  exact hbalance a ha ω τ

/-- A balanced finite cube law, equipped with its maximum word cutoff,
directly satisfies the joint-prefix error estimate. -/
theorem FiniteCubeLaw.maxCutoff_wordPrefixDistance_le
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbalance : L.MultiplicativelyBalanced δ)
    (ω : Fin H → ZMod 3) :
    (L.toCutoffLaw hR L.maxWordProduct
      (fun _a ha => L.one_le_maxWordProduct hR ha)
      (fun _a ha => L.maxWordProduct_le_total hR ha)
      (fun a _ha τ => L.wordProduct_le_max a τ)).wordPrefixDistance ω ≤
        L.wordSupportDistance ω + 2 * δ := by
  apply L.toCutoffLaw_wordPrefixDistance_le hR L.maxWordProduct
    (fun _a ha => L.one_le_maxWordProduct hR ha)
    (fun _a ha => L.maxWordProduct_le_total hR ha)
    (fun a _ha τ => L.wordProduct_le_max a τ)
    hδ
  exact fun a ha τ =>
    L.maxWordProduct_cast_le_of_balanced hbalance ha τ

end Erdos536
