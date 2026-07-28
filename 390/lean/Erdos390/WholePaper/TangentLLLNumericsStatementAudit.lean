import Erdos390.WholePaper.TangentLLLNumerics

open scoped BigOperators

namespace Erdos390.WholePaper

example {I : Type*} (s : Finset I) (x : I → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i ∧ x i ≤ 1) :
    1 - ∑ i ∈ s, x i ≤ ∏ i ∈ s, (1 - x i) :=
  one_sub_sum_le_prod_one_sub s x hx

example {I : Type*} [DecidableEq I]
    (neighbors : Finset I) (probability : I → ℝ)
    (event : I)
    (hprobability : ∀ i ∈ insert event neighbors,
      0 ≤ probability i)
    (hneighborhood : ∑ i ∈ neighbors, probability i ≤ 1 / 4) :
    probability event ≤
      (2 * probability event) *
        ∏ i ∈ neighbors, (1 - 2 * probability i) :=
  probability_le_two_mul_probability_mul_neighborProduct
    neighbors probability event hprobability hneighborhood

example {I : Type*} [DecidableEq I]
    (neighbors : Finset I) (probability : I → ℝ)
    (event : I)
    (hprobability : ∀ i ∈ insert event neighbors,
      0 ≤ probability i)
    (requestMass : ℝ) (hrequestMass : requestMass ≤ 1 / 8)
    (hneighborhood : ∑ i ∈ neighbors, probability i ≤
      2 * requestMass) :
    probability event ≤
      (2 * probability event) *
        ∏ i ∈ neighbors, (1 - 2 * probability i) :=
  probability_le_two_mul_probability_mul_neighborProduct_of_requestMass
    neighbors probability event hprobability requestMass hrequestMass
      hneighborhood

end Erdos390.WholePaper
