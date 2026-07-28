import Erdos390.Full.PaperRawTiltTaylorRate

/-! Independent statement-shape audit for the raw Taylor-rate closure. -/

open Filter Topology

namespace Erdos390.Full.PaperRawTiltTaylorRateStatementAudit

open Erdos390.Full
open ArithmeticModel Scale PrimeSums
open FiniteProbability

example {a MF RFone Czero Cthird : ℝ}
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone) :
    rawTiltPrefixTaylorBound a MF RFone Czero Cthird ≤
      Czero + Cthird + 128 * (RFone + MF * a) :=
  rawTiltPrefixTaylorBound_le_add_128 ha ha1 hMF hRFone

example {a MF RFone Czero Cthird epsilonZero epsilonThird nonlinear : ℝ}
    {p : ℕ} (hp : 0 < p)
    (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hMF : 0 ≤ MF) (hRFone : 0 ≤ RFone)
    (hzero : Czero ≤ epsilonZero / (p : ℝ))
    (hthird : Cthird ≤ epsilonThird / (p : ℝ))
    (hnonlinear : (p : ℝ) * (128 * (RFone + MF * a)) ≤ nonlinear) :
    rawTiltPrefixTaylorBound a MF RFone Czero Cthird ≤
      (epsilonZero + epsilonThird + nonlinear) / (p : ℝ) :=
  rawTiltPrefixTaylorBound_le_row hp ha ha1 hMF hRFone hzero hthird
    hnonlinear

example (B c : ℝ) (W : ℕ) (hB : 0 ≤ B) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, 0 < p →
      let H := bandReciprocalSum n W
      let a := (B / L n) * ((2 / c) * H)
      let MF := 2 / (c * (p : ℝ))
      let RFone := (B / L n) * (1 / c) *
        ((4 * H + PrimePowerTaylorLedger.positivePrimePowerLcmConstant) /
          (p : ℝ))
      (p : ℝ) * (128 * (RFone + MF * a)) ≤
        rawTiltNonlinearRateMajorant B c n :=
  eventually_rawTiltNonlinear_row_le B c W hB hc

example (B c : ℝ) :
    Tendsto (fun n : ℕ ↦
      rawTiltNonlinearRateMajorant B c n * Real.log (L n))
      atTop (nhds 0) :=
  tendsto_rawTiltNonlinearRateMajorant_mul_logL_zero B c

end Erdos390.Full.PaperRawTiltTaylorRateStatementAudit
