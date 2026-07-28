import Erdos390.WholePaper.UpperEndpointBound

/-! # Expanded statement audit for the pointwise upper endpoint bound -/

namespace Erdos390.WholePaper

example {n h : ℕ} (hn : 3 ≤ n)
    (hadmissible : ∃ factors : Finset ℕ,
      factors ⊆ Finset.Ioc n (2 * n + h) ∧
        factors.prod id = n.factorial) :
    (((f n : ℝ) -
        (2 * (n : ℝ) +
          ((4029639598 : ℝ) / 25970038185) *
            ((n : ℝ) / Real.log (n : ℝ)))) /
      ((n : ℝ) / Real.log (n : ℝ))) ≤
        (h : ℝ) / ((n : ℝ) / Real.log (n : ℝ)) -
          (4029639598 : ℝ) / 25970038185 := by
  simpa only [IsAdmissibleEndpoint, factorInterval, mainError,
    secondOrderScale, C0] using
      mainError_normalized_le_of_admissible hn hadmissible

end Erdos390.WholePaper
