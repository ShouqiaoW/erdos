import Erdos390.Full.NuisanceCovariance

/-!
# Canonical coarse mixtures

Given an actual fine finite law and a map to finitely many reserved cells,
the coarse weights and conditional-mean pattern vectors are defined by finite
sums.  This removes the need to assume the law-of-total-variance connection
used in the nuisance covariance argument.
-/

open scoped BigOperators

namespace Erdos390.Full

noncomputable section

namespace CanonicalCoarseMixture

variable {Fine Cell Nuisance : Type*} [Fintype Fine] [Fintype Cell]
  [DecidableEq Cell]
  [NormedAddCommGroup Nuisance] [InnerProductSpace ℝ Nuisance]

def fiberWeight (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) : ℝ :=
  ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c, fine.weight f

def fiberMoment (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) : Nuisance :=
  ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c,
    fine.weight f • fine.pattern f

def conditionalPattern (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) : Nuisance :=
  (fiberWeight fine cell c)⁻¹ • fiberMoment fine cell c

omit [Fintype Cell] in
theorem fiberWeight_nonneg (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) :
    0 ≤ fiberWeight fine cell c := by
  exact Finset.sum_nonneg fun f hf ↦ fine.weight_nonneg f

theorem fiberWeight_sum (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) :
    ∑ c, fiberWeight fine cell c = 1 := by
  change (∑ c, ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c,
    fine.weight f) = 1
  rw [Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset Fine))
    (t := (Finset.univ : Finset Cell))
    (g := cell) (fun f _ ↦ Finset.mem_univ (cell f)) fine.weight]
  exact fine.weight_sum

def coarse (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) : PatternMixture Cell Nuisance where
  weight := fiberWeight fine cell
  weight_nonneg := fiberWeight_nonneg fine cell
  weight_sum := fiberWeight_sum fine cell
  pattern := conditionalPattern fine cell

@[simp] theorem coarse_weight (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) :
    (coarse fine cell).weight c = fiberWeight fine cell c := rfl

@[simp] theorem coarse_pattern (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) :
    (coarse fine cell).pattern c = conditionalPattern fine cell c := rfl

omit [Fintype Cell] in
theorem inner_fiberMoment (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (c : Cell) (x : Nuisance) :
    inner ℝ x (fiberMoment fine cell c) =
      ∑ f ∈ (Finset.univ : Finset Fine) with cell f = c,
        fine.weight f * inner ℝ x (fine.pattern f) := by
  simp only [fiberMoment, inner_sum, inner_smul_right]

/-- The coarse conditional-mean certificate follows from the definitions,
provided every coarse cell has positive mass. -/
def certificate (fine : PatternMixture Fine Nuisance)
    (cell : Fine → Cell) (hpos : ∀ c, 0 < fiberWeight fine cell c) :
    PatternMixture.CoarseMeanCertificate fine (coarse fine cell) where
  cell := cell
  cell_mass := fun _ ↦ rfl
  cell_firstMoment := by
    intro c x
    rw [← inner_fiberMoment fine cell c x]
    simp only [coarse_weight, coarse_pattern, conditionalPattern,
      inner_smul_right]
    field_simp [ne_of_gt (hpos c)]

end CanonicalCoarseMixture

end

end Erdos390.Full
