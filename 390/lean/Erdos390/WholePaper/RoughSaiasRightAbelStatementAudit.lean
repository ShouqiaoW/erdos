import Erdos390.WholePaper.RoughSaiasRightAbel

open scoped BigOperators Interval

namespace Erdos390.WholePaper

open Finset MeasureTheory Set

noncomputable section

#check RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right
#check RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right'

example (c : ℕ → ℝ) {f f' : ℝ → ℝ} {n m : ℕ}
    (hnm : n ≤ m)
    (hf_cont : ContinuousOn f (Set.Icc (n : ℝ) m))
    (hf_right : ∀ t ∈ Set.Ioo (n : ℝ) m,
      HasDerivWithinAt f (f' t) (Set.Ioi t) t)
    (hf'_int : IntegrableOn f' (Set.Icc (n : ℝ) m)) :
    (∑ k ∈ Finset.Ioc n m, f k * c k) =
      f m * (∑ k ∈ Finset.Icc 0 m, c k) -
        f n * (∑ k ∈ Finset.Icc 0 n, c k) -
        ∫ t in Set.Ioc (n : ℝ) m,
          f' t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k :=
  RoughSaiasRightAbel.sum_mul_eq_sub_sub_integral_mul_right'
    c hnm hf_cont hf_right hf'_int

end

end Erdos390.WholePaper
