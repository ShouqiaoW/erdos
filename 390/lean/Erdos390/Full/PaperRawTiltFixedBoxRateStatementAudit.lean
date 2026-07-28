import Erdos390.Full.PaperRawTiltFixedBoxRate

/-! Independent restatement of the fixed-box row domination. -/

namespace Erdos390.Full.PaperRawTiltFixedBoxRateStatementAudit

open Erdos390.Full.FiniteProbability

example {K a MF RFone Czero Cthird : ℝ}
    (hK : 0 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone) :
    rawTiltPrefixTaylorBoundFixedBox K a MF RFone Czero Cthird ≤
      Czero + Cthird +
        fixedBoxTaylorDominationConstant K * (RFone + MF * a) := by
  exact rawTiltPrefixTaylorBoundFixedBox_le hK ha ha1 hMF hRFone

example {K a MF RFone Czero Cthird epsilonZero epsilonThird nonlinear : ℝ}
    {p : ℕ}
    (hp : 0 < p) (hK : 0 ≤ K) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone)
    (hzero : Czero ≤ epsilonZero / (p : ℝ))
    (hthird : Cthird ≤ epsilonThird / (p : ℝ))
    (hnonlinear : (p : ℝ) *
      (fixedBoxTaylorDominationConstant K * (RFone + MF * a)) ≤ nonlinear) :
    rawTiltPrefixTaylorBoundFixedBox K a MF RFone Czero Cthird ≤
      (epsilonZero + epsilonThird + nonlinear) / (p : ℝ) := by
  exact rawTiltPrefixTaylorBoundFixedBox_le_row hp hK ha ha1 hMF hRFone
    hzero hthird hnonlinear

end Erdos390.Full.PaperRawTiltFixedBoxRateStatementAudit
