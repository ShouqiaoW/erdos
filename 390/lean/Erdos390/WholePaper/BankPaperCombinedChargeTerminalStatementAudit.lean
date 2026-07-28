import Erdos390.WholePaper.BankPaperCombinedChargeTerminal

/-! # Expanded statement audit for the combined-charge terminal -/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example (c deltaStar : ℝ) :
    IsPaperCombinedChargeDeltaStar c deltaStar ↔
      0 < deltaStar ∧
        deltaStar < 1 / 18 ∧
          paperExceptionalChargeConstant c *
              (deltaStar / paperExceptionalTheta) ≤
            (c - C0) / 48 := by
  rfl

example (c : ℝ) :
    paperCombinedChargeDeltaStar c =
      min (1 / 36)
        ((c - C0) * paperExceptionalTheta /
          (48 * paperExceptionalChargeConstant c)) := by
  rfl

example {c : ℝ} (hc : C0 < c) :
    0 < paperCombinedChargeDeltaStar c ∧
      paperCombinedChargeDeltaStar c < 1 / 18 ∧
        paperExceptionalChargeConstant c *
            (paperCombinedChargeDeltaStar c / paperExceptionalTheta) ≤
          (c - C0) / 48 :=
  paperCombinedChargeDeltaStar_spec hc

example {c : ℝ} (hc : C0 < c) :
    0 < paperCombinedChargeDeltaStar c :=
  paperCombinedChargeDeltaStar_pos hc

example {c : ℝ} (hc : C0 < c) :
    paperCombinedChargeDeltaStar c < 1 / 18 :=
  paperCombinedChargeDeltaStar_lt_one_eighteenth hc

example {c deltaStar : ℝ} (hc : C0 < c)
    (hdelta : IsPaperCombinedChargeDeltaStar c deltaStar) :
    ∀ᶠ n : ℕ in atTop,
      ∀ (R : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n))) (p : ℕ),
        p.Prime → p ≤ yNat n →
        (((R.paperFixedExceptionalFactors deltaStar).prod id).factorization p :
            ℝ) ≤
          (c - C0) / 24 * secondOrderScale n / (p : ℝ) :=
  eventually_paperFixedExceptionalFactors_charge_le_combinedReserve
    hc hdelta

example {c deltaStar : ℝ} (hc : C0 < c)
    (hdelta : IsPaperCombinedChargeDeltaStar c deltaStar) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          ∃ certificate : GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth),
            centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * bank.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n) ∧
              bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors deltaStar) ∣
                certificate.prechargedTailTarget ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (bank.selectorTailCharge
                      (bank.paperFixedExceptionalFactors deltaStar)).factorization p ≤
                  certificate.prechargedTailTarget.factorization p) ∧
              certificate.selectorTailTarget bank
                    (bank.paperFixedExceptionalFactors deltaStar) *
                  bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors deltaStar) =
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) :=
  exists_eventually_bankPaperCombinedChargeTerminal_of_deltaStar
    hc hdelta

example {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (upperEndpoint n (upperTailLength c n)),
          ∃ certificate : GuardedCentralAnchorCertificate c depth n
              bank.anchorGuardLeftCore bank.anchorGuardRightCore
              (bank.centralChangedMarkers depth),
            centralAnchorDivisor n (centralAnchorCutoff depth n)
                  certificate.q * bank.prechargeBaseStateProduct ∣
                centralTailProduct n (upperTailLength c n) ∧
              bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors
                      (paperCombinedChargeDeltaStar c)) ∣
                certificate.prechargedTailTarget ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (bank.selectorTailCharge
                      (bank.paperFixedExceptionalFactors
                        (paperCombinedChargeDeltaStar c))).factorization p ≤
                  certificate.prechargedTailTarget.factorization p) ∧
              certificate.selectorTailTarget bank
                    (bank.paperFixedExceptionalFactors
                      (paperCombinedChargeDeltaStar c)) *
                  bank.selectorTailCharge
                    (bank.paperFixedExceptionalFactors
                      (paperCombinedChargeDeltaStar c)) =
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) :=
  exists_eventually_bankPaperCombinedChargeTerminal hc

end

end Erdos390.WholePaper
