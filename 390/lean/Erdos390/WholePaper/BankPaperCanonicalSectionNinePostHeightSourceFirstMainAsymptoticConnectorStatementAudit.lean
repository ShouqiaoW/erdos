import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstMainAsymptoticConnector

/-!
# Expanded statement audit: source-first Section 9 main asymptotic

The first closed example exposes the exact upper-endpoint contract consumed
by the final normalization theorem.  The second closed example unfolds
`MainAsymptotic`, `mainError`, `C0`, and `secondOrderScale`, so the audited
conclusion is literally the paper's small-`o` formula and carries no
hypotheses.
-/

open Filter Asymptotics

namespace Erdos390.WholePaper

noncomputable section

/-! ## Public declaration census -/

#check
  BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
#check
  eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
#check mainAsymptotic_of_eventually_f_le_upperScaledEndpoint
#check bankPaperCanonicalSectionNinePostHeight_sourceFirstMainAsymptotic

/-! ## Exact closed upper-endpoint contract used by the final reduction -/

example :
    ∀ c : ℝ, ((4029639598 : ℝ) / 25970038185) < c →
      ∀ᶠ n : ℕ in atTop,
        f n ≤
          2 * n +
            Nat.ceil
              (c * ((n : ℝ) / Real.log (n : ℝ))) := by
  intro c hc
  have hc' : C0 < c := by
    simpa only [C0] using hc
  obtain
      ⟨depth, _W, _r0, deltaStar, hdepth, _hWtwo, _hprefix,
        _hMertens, _hMoment, _hr0one, _hr0three, _hdeltaStar,
        _Hcharge, Hterminal⟩ :=
    BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
      hc'
  have hupper :
      ∀ᶠ n : ℕ in atTop,
        f n ≤ upperEndpoint n (upperTailLength c n) :=
    eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
      hc' hdepth Hterminal
  simpa only [upperEndpoint, upperTailLength, secondOrderScale] using hupper

/-! ## Literal assumption-free paper main theorem -/

example :
    (fun n : ℕ =>
        (f n : ℝ) -
          (2 * (n : ℝ) +
            ((4029639598 : ℝ) / 25970038185) *
              ((n : ℝ) / Real.log (n : ℝ))))
      =o[atTop]
        (fun n : ℕ => (n : ℝ) / Real.log (n : ℝ)) := by
  simpa only [MainAsymptotic, mainError, C0, secondOrderScale] using
    bankPaperCanonicalSectionNinePostHeight_sourceFirstMainAsymptotic

end

end Erdos390.WholePaper
