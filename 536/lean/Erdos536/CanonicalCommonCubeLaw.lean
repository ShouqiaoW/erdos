import Erdos536.BalancedCubeCutoff

/-!
# The canonical reciprocal law as a zero-dimensional common cube

An inactive prime band contributes the same reciprocal-Bernoulli support to
every word.  It is therefore naturally a dimension-zero cube law whose common
part is the sampled support.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- A zero-dimensional cube with prescribed common support. -/
def commonOnlyCube (S : Finset ℕ) : PairProductCube 0 where
  common := S
  petal := fun i => Fin.elim0 i
  petal_nonempty := fun i => Fin.elim0 i
  common_disjoint := fun i => Fin.elim0 i
  petal_disjoint := fun i => Fin.elim0 i

theorem commonOnlyCube_wordSupport (S : Finset ℕ)
    (ω : Fin 0 → ZMod 3) :
    (commonOnlyCube S).wordSupport ω = S := by
  simp [commonOnlyCube, PairProductCube.wordSupport]

/-- Reciprocal squarefree mass of one support. -/
noncomputable def canonicalSupportMass (R S : Finset ℕ) : ℝ :=
  1 / (squarefreeZ R * (primeProduct S : ℝ))

theorem canonicalSupportMass_nonneg (R S : Finset ℕ) :
    0 ≤ canonicalSupportMass R S := by
  unfold canonicalSupportMass
  apply one_div_nonneg.mpr
  apply mul_nonneg
  · rw [squarefreeZ]
    exact Finset.sum_nonneg fun T _hT => inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact Nat.cast_nonneg _

theorem sum_canonicalSupportMass
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    ∑ S ∈ R.powerset, canonicalSupportMass R S = 1 := by
  have hZ : squarefreeZ R ≠ 0 := (squarefreeZ_pos R hR).ne'
  calc
    (∑ S ∈ R.powerset, canonicalSupportMass R S) =
        (∑ S ∈ R.powerset, (primeProduct S : ℝ)⁻¹) /
          squarefreeZ R := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro S _hS
      rw [canonicalSupportMass, one_div, div_eq_mul_inv]
      ring
    _ = squarefreeZ R / squarefreeZ R := by
      rw [squarefreeZ]
    _ = 1 := div_self hZ

/-- The canonical reciprocal squarefree support law, viewed as common mass
in a zero-dimensional cube. -/
noncomputable def canonicalCommonCubeLaw
    (R : Finset ℕ) (hR : IsPrimeSupport R) :
    FiniteCubeLaw (Finset ℕ) 0 R where
  samples := R.powerset
  mass := canonicalSupportMass R
  cube := commonOnlyCube
  mass_nonneg := fun S _hS => canonicalSupportMass_nonneg R S
  mass_sum := sum_canonicalSupportMass R hR
  wordSupport_subset := by
    intro S hS ω
    rw [commonOnlyCube_wordSupport]
    exact Finset.mem_powerset.mp hS

theorem canonicalCommonCubeLaw_wordSupportMass
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    (ω : Fin 0 → ZMod 3) {S : Finset ℕ} (hS : S ∈ R.powerset) :
    (canonicalCommonCubeLaw R hR).wordSupportMass ω S =
      canonicalSupportMass R S := by
  classical
  rw [FiniteCubeLaw.wordSupportMass]
  rw [Finset.sum_eq_single S]
  · simp [canonicalCommonCubeLaw, commonOnlyCube_wordSupport]
  · intro T hT hTS
    simp [canonicalCommonCubeLaw, commonOnlyCube_wordSupport, hTS]
  · exact fun hnot => (hnot hS).elim

theorem canonicalCommonCubeLaw_wordSupportDistance
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    (ω : Fin 0 → ZMod 3) :
    (canonicalCommonCubeLaw R hR).wordSupportDistance ω = 0 := by
  rw [FiniteCubeLaw.wordSupportDistance]
  apply Finset.sum_eq_zero
  intro S hS
  rw [canonicalCommonCubeLaw_wordSupportMass R hR ω hS]
  simp [canonicalSupportMass]

end Erdos536
