import Erdos390.Full.FiniteGraphQuotientInverse

/-!
# Relabelling `Fin (k+1)` as one low cell plus `Fin k`
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FinOneLowRelabel

open FiniteGraphQuotientInverse

variable {k : ℕ}

/-- The canonical relabelling sends `none` to coordinate zero and `some i`
to coordinate `i+1`. -/
def optionFinEquiv : Option (Fin k) ≃ Fin (k + 1) :=
  (finSuccEquiv k).symm

@[simp] theorem optionFinEquiv_none : optionFinEquiv (k := k) none = 0 := by
  rfl

@[simp] theorem optionFinEquiv_some (i : Fin k) :
    optionFinEquiv (some i) = i.succ := by
  rfl

theorem sum_pull (f : Fin (k + 1) → ℝ) :
    ∑ i : Option (Fin k), f (optionFinEquiv i) = ∑ j, f j := by
  exact Fintype.sum_equiv optionFinEquiv _ _ (fun _ ↦ rfl)

theorem graphOperator_pull
    (edge : Fin (k + 1) → Fin (k + 1) → ℝ)
    (q : Fin (k + 1) → ℝ) (i : Option (Fin k)) :
    graphOperator
        (fun a b ↦ edge (optionFinEquiv a) (optionFinEquiv b))
        (fun a ↦ q (optionFinEquiv a)) i =
      graphOperator edge q (optionFinEquiv i) := by
  unfold graphOperator
  exact Fintype.sum_equiv optionFinEquiv _ _ (fun j ↦ rfl)

theorem weightedMean_pull (omega x : Fin (k + 1) → ℝ) :
    weightedMean (fun i ↦ omega (optionFinEquiv i))
        (fun i ↦ x (optionFinEquiv i)) =
      weightedMean omega x := by
  unfold weightedMean weightTotal
  rw [sum_pull (fun j ↦ omega j * x j), sum_pull omega]

theorem meanProjection_pull (omega x : Fin (k + 1) → ℝ)
    (i : Option (Fin k)) :
    meanProjection (fun a ↦ omega (optionFinEquiv a))
        (fun a ↦ x (optionFinEquiv a)) i =
      meanProjection omega x (optionFinEquiv i) := by
  unfold meanProjection
  rw [weightedMean_pull]

end Erdos390.Full.FinOneLowRelabel
