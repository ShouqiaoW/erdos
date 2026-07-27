import Erdos536.CubeLawTensorDistance
import Erdos536.CubeMaximum

/-!
# Multiplicative balance under tensor products

The support of a tensor word is a disjoint union of its two component
supports.  Consequently its prime product is the product of the two
component prime products, and multiplicative balance factors multiply.
-/

open Finset

namespace Erdos536

private theorem tensorWordSupports_disjoint
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hRS : Disjoint R S)
    (a : ↥L.samples) (b : ↥M.samples)
    (ω : Fin H → ZMod 3) (τ : Fin K → ZMod 3) :
    Disjoint
      ((L.cube a).wordSupport ω)
      ((M.cube b).wordSupport τ) := by
  rw [Finset.disjoint_left]
  intro p hpL hpM
  exact Finset.disjoint_left.mp hRS
    (L.wordSupport_subset a a.property ω hpL)
    (M.wordSupport_subset b b.property τ hpM)

/-- Tensoring laws with balance factors `1 + δ` and `1 + ε` gives balance
factor `(1 + δ) * (1 + ε)`. -/
theorem FiniteCubeLaw.tensor_multiplicativelyBalanced
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hRS : Disjoint R S)
    {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hL : L.MultiplicativelyBalanced δ)
    (hM : M.MultiplicativelyBalanced ε) :
    (L.tensor M hRS).MultiplicativelyBalanced
      ((1 + δ) * (1 + ε) - 1) := by
  intro ab _hab ω τ
  let ωL : Fin H → ZMod 3 := fun i ↦ ω (Fin.castAdd K i)
  let ωM : Fin K → ZMod 3 := fun j ↦ ω (Fin.natAdd H j)
  let τL : Fin H → ZMod 3 := fun i ↦ τ (Fin.castAdd K i)
  let τM : Fin K → ZMod 3 := fun j ↦ τ (Fin.natAdd H j)
  have hleft := hL ab.1 ab.1.property ωL τL
  have hright := hM ab.2 ab.2.property ωM τM
  have hleftNonneg :
      0 ≤ (primeProduct ((L.cube ab.1).wordSupport ωL) : ℝ) :=
    Nat.cast_nonneg _
  have hrightNonneg :
      0 ≤ (primeProduct ((M.cube ab.2).wordSupport τM) : ℝ) :=
    Nat.cast_nonneg _
  have hfactorLeft : 0 ≤ 1 + δ := by linarith
  have hfactorRight : 0 ≤ 1 + ε := by linarith
  rw [L.tensor_wordSupport M hRS,
    L.tensor_wordSupport M hRS,
    primeProduct_union_of_disjoint
      (tensorWordSupports_disjoint L M hRS ab.1 ab.2 τL τM),
    primeProduct_union_of_disjoint
      (tensorWordSupports_disjoint L M hRS ab.1 ab.2 ωL ωM)]
  push_cast
  calc
    (primeProduct ((L.cube ab.1).wordSupport τL) : ℝ) *
        (primeProduct ((M.cube ab.2).wordSupport τM) : ℝ) ≤
      ((1 + δ) *
          (primeProduct ((L.cube ab.1).wordSupport ωL) : ℝ)) *
        ((1 + ε) *
          (primeProduct ((M.cube ab.2).wordSupport ωM) : ℝ)) :=
      mul_le_mul hleft hright
        hrightNonneg
        (mul_nonneg hfactorLeft hleftNonneg)
    _ = (1 + ((1 + δ) * (1 + ε) - 1)) *
        ((primeProduct ((L.cube ab.1).wordSupport ωL) : ℝ) *
          (primeProduct ((M.cube ab.2).wordSupport ωM) : ℝ)) := by
      ring

end Erdos536
