import Mathlib

/-!
# Erdős Problem 536: finite extremal definitions

The definitions in this file follow the original problem literally:
`lcmTriangleFree A` says that the finite set `A` contains no three
distinct members whose three pairwise least common multiples are equal,
and `f N` is the largest cardinality of such a subset of `{1, ..., N}`.
-/

open Filter Finset Nat Set

namespace Erdos536

/-- Three natural numbers form the forbidden configuration when they are
distinct and all three pairwise least common multiples agree. -/
def IsLcmTriangle (a b c : ℕ) : Prop :=
  ({a, b, c} : Finset ℕ).card = 3 ∧
    a.lcm b = b.lcm c ∧ b.lcm c = a.lcm c

/-- A finite set is safe if it contains no forbidden LCM triangle. -/
def LcmTriangleFree (A : Finset ℕ) : Prop :=
  ∀ ⦃a b c : ℕ⦄, a ∈ A → b ∈ A → c ∈ A → ¬IsLcmTriangle a b c

/-- All safe subsets of `{1, ..., N}`. -/
noncomputable def safeFamilies (N : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 N).powerset.filter LcmTriangleFree

/-- The extremal function from Erdős Problem 536. -/
noncomputable def f (N : ℕ) : ℕ :=
  (safeFamilies N).sup card

end Erdos536
