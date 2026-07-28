import Erdos390.WholePaper.MainTargetEquivalence

/-!
# Expanded statement audit for the whole-paper target

These are definitional audits of the two propositions to be proved.  They do
not assert either proposition.  The first display is the paper's literal
small-`o(n / log n)` expansion; the second is its displayed normalized
limit.
-/

open Filter Topology Asymptotics

namespace Erdos390.WholePaper

noncomputable section

example :
    MainAsymptotic ↔
      ((fun n : ℕ ↦
          (f n : ℝ) -
            (2 * (n : ℝ) +
              ((4029639598 : ℝ) / 25970038185) *
                ((n : ℝ) / Real.log (n : ℝ))))
        =o[atTop]
          (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ))) := by
  rfl

example :
    MainNormalizedLimit ↔
      Tendsto
        (fun n : ℕ ↦
          (((f n : ℝ) - 2 * (n : ℝ)) * Real.log (n : ℝ)) /
            (n : ℝ))
        atTop
        (nhds ((4029639598 : ℝ) / 25970038185)) := by
  rfl

/-! This certifies only the equivalence of the two displayed targets. -/
example : MainAsymptotic ↔ MainNormalizedLimit :=
  mainAsymptotic_iff_mainNormalizedLimit

end

end Erdos390.WholePaper
