import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstCutoffAwareDistributedTerminalConnector
import Erdos390.WholePaper.BankPaperMainAsymptoticReduction

/-!
# Source-first Section 9 terminal to the paper's main asymptotic

The cutoff-aware source-first construction supplies, for each paper scale
`c > C0`, a distributed Section 9 terminal at one capacity-permitted depth.
The same-depth capacity bridge converts that terminal to the eventual upper
endpoint required by the final normalization theorem.

This is the terminal connector for the source-first chain.  Its conclusion
is the paper's literal small-`o` statement `MainAsymptotic`, and it has no
remaining hypotheses.
-/

open Filter

namespace Erdos390.WholePaper

noncomputable section

/-- The cutoff-aware source-first Section 9 construction proves the paper's
literal main asymptotic with no additional assumptions. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_sourceFirstMainAsymptotic :
    MainAsymptotic := by
  apply mainAsymptotic_of_eventually_f_le_upperScaledEndpoint
  intro c hc
  obtain
      ⟨depth, _W, _r0, deltaStar, hdepth, _hWtwo, _hprefix,
        _hMertens, _hMoment, _hr0one, _hr0three, _hdeltaStar,
        _Hcharge, Hterminal⟩ :=
    BankPaperRealization.exists_bankPaperCanonicalSectionNinePostHeight_sourceFirstCutoffAwareDistributedTerminal
      hc
  exact
    eventually_bankPaper_f_le_upperEndpoint_of_canonicalDistributedSectionNineTerminalAtDepth
      hc hdepth Hterminal

end

end Erdos390.WholePaper
