import Erdos536.CubeMaximum

/-!
# Capacity bounds from balanced cube laws

This is the finite endpoint of the analytic construction.  Once a law of
pair-product cubes has approximately reciprocal squarefree word marginals
and its word products are multiplicatively balanced, the cap-set saving and
the common-cutoff kernel give the desired normalized capacity bound.
-/

namespace Erdos536

/-- A fixed-dimensional balanced cube law transfers its support-marginal
error to normalized squarefree capacity. -/
theorem squarefreeCapacity_le_of_balancedCubeLaw
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    {κ ε δ : ℝ}
    (hcube : ∀ (c : PairProductCube H) (𝓕 : Finset (Finset ℕ)),
      Admissible 𝓕 →
      ((c.familyWords 𝓕).card : ℝ) ≤ κ * (3 : ℝ) ^ H)
    (hε : ∀ ω : Fin H → ZMod 3, L.wordSupportDistance ω ≤ ε)
    (hδ : 0 ≤ δ)
    (hbalance : L.MultiplicativelyBalanced δ) :
    squarefreeI R / squarefreeZ R ≤ κ + (ε + 2 * δ) := by
  let C := L.toCutoffLaw hR L.maxWordProduct
    (fun _a ha => L.one_le_maxWordProduct hR ha)
    (fun _a ha => L.maxWordProduct_le_total hR ha)
    (fun a _ha ω => L.wordProduct_le_max a ω)
  apply finite_jointPrefix_transference_of_familyWords C hR
    (ε := ε + 2 * δ) (κ := κ)
  · intro ω
    exact (L.maxCutoff_wordPrefixDistance_le hR hδ hbalance ω).trans
      (add_le_add (hε ω) le_rfl)
  · exact hcube

/-- Qualitative cap-set input with all analytic requirements exposed as a
single finite cube-law interface. -/
theorem exists_dimension_squarefreeCapacity_le_of_balancedCubeLaw
    (κ : ℝ) (hκ : 0 < κ) :
    ∃ H : ℕ, ∀ (α : Type*) [DecidableEq α] (R : Finset ℕ)
      (L : FiniteCubeLaw α H R), IsPrimeSupport R →
      ∀ {ε δ : ℝ},
        (∀ ω : Fin H → ZMod 3, L.wordSupportDistance ω ≤ ε) →
        0 ≤ δ →
        L.MultiplicativelyBalanced δ →
        squarefreeI R / squarefreeZ R ≤ κ + (ε + 2 * δ) := by
  obtain ⟨H, hH⟩ := exists_dimension_cubeSaving_card_le κ hκ
  refine ⟨H, ?_⟩
  intro α _inst R L hR ε δ hε hδ hbalance
  exact squarefreeCapacity_le_of_balancedCubeLaw
    L hR hH hε hδ hbalance

end Erdos536
