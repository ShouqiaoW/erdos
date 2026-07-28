import Erdos390.WholePaper.FloatingRoundingStep

open scoped BigOperators

namespace Erdos390.WholePaper

example {A E : Type*} [Fintype A] [Fintype E]
    (w : E → A → ℝ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hcard : Fintype.card E < (fractionalSupport x).card) :
    ∃ x' : A → ℝ,
      (∀ a, 0 ≤ x' a ∧ x' a ≤ 1) ∧
      (∀ a, x a = 0 ∨ x a = 1 → x' a = x a) ∧
      (∀ e, ∑ a, w e a * x' a = ∑ a, w e a * x a) ∧
      (fractionalSupport x').card < (fractionalSupport x).card :=
  exists_floating_step w x hx hcard

end Erdos390.WholePaper
