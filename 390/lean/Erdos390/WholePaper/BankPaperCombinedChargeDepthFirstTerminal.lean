import Erdos390.WholePaper.BankPaperCanonicalTangentSlackIntegration

/-!
# Depth-first combined charge terminal

The original combined-charge terminal specializes `deltaStar` before it
exposes the capacity depth.  For the Section 9 clean-list application this
creates an artificial cycle: the clean-list width `W` must dominate the
chosen depth, while the tangent-compatible `deltaStar` is defined using
`W`.

The strengthened precharge-capacity theorem actually chooses its depth
using only `c`.  This file preserves that proof order.  It first fixes one
capacity depth and then proves the complete combined-charge conclusion
uniformly for every admissible `deltaStar`.  The tangent-choice corollary
therefore allows `W` and `r0` to be chosen after the depth is known.

The payload also retains the base exactification-bank divisibility fact
needed by `BankPaperCanonicalPostTangentContinuationAtDepth`; the older
combined-charge terminal discarded this already-proved capacity fact.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Fixed-depth payload -/

/-- The complete combined fixed-factor and precharge output at one already
chosen capacity depth.

Besides the existing combined-charge conclusions, this interface retains
the base exactification-bank divisibility required by the downstream
capacity continuation. -/
def BankPaperCombinedChargeTerminalAtDepth
    (c deltaStar : ℝ) (depth : ℕ) : Prop :=
  ∀ᶠ n : ℕ in atTop,
    ∃ bank : BankPaperRealization n
        (upperEndpoint n (upperTailLength c n)),
      ∃ certificate : GuardedCentralAnchorCertificate c depth n
          bank.anchorGuardLeftCore bank.anchorGuardRightCore
          (bank.centralChangedMarkers depth),
        centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q * bank.prechargeBaseStateProduct ∣
            centralTailProduct n (upperTailLength c n) ∧
          (baseBankFactors bank.exactificationState).prod id ∣
            certificate.prechargedTailTarget ∧
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
            centralTailProduct n (upperTailLength c n)

/-! ## Uniform admissible exponent after capacity -/

set_option maxHeartbeats 800000 in
/-- One capacity depth works for every combined-charge-admissible
`deltaStar`.  In particular, the exponent may be chosen after the depth. -/
theorem exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ deltaStar : ℝ, IsPaperCombinedChargeDeltaStar c deltaStar →
        BankPaperCombinedChargeTerminalAtDepth c deltaStar depth := by
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hgap : 0 < c - C0 := sub_pos.mpr hc
  obtain ⟨depth, hdepth, hprecharge⟩ :=
    exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve hc
  have hsupportCutoff :=
    eventually_bankAnchor_fixed_le_yNat (2 * depth + 1)
  have hcapacitySmall :=
    (bankPaperPrechargeUniformCapacityCost_normalized_tendsto_zero hcPos).eventually
      (eventually_lt_nhds (by positivity : (0 : ℝ) < c / 4))
  have htailLarge :=
    (upperTailLength_normalized_tendsto hcPos).eventually
      (eventually_gt_nhds (by linarith : c / 2 < c))
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  refine ⟨depth, hdepth, ?_⟩
  intro deltaStar hdelta
  have hfixedCharge :=
    eventually_paperFixedExceptionalFactors_charge_le_combinedReserve
      hc hdelta
  simp only [BankPaperCombinedChargeTerminalAtDepth]
  filter_upwards [hprecharge, hfixedCharge, hsupportCutoff,
      hcapacitySmall, htailLarge, hendpoint,
      eventually_secondOrderScale_pos]
      with n hprechargeN hfixedChargeN hsupportN hcapacityN htailN
        hendpointN hscale
  obtain ⟨bank, certificate, hanchorBank, hretainedBefore,
      hretainedTarget, hbaseDvd, htargetIdentity⟩ := hprechargeN
  let fixed : Finset ℕ := bank.paperFixedExceptionalFactors deltaStar
  let charge : ℕ := bank.selectorTailCharge fixed
  let divisor : ℕ :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  let tail : ℕ := centralTailProduct n (upperTailLength c n)
  have hfixedPositive : ∀ a ∈ fixed, 0 < a := by
    intro a ha
    have htail := bank.paperFixedExceptionalFactors_subset_tail
      deltaStar (by simpa only [fixed] using ha)
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp htail).1
  have hfixedProdPos : 0 < fixed.prod id := by
    apply Finset.prod_pos
    intro a ha
    simpa only [id_eq] using hfixedPositive a ha
  have hbasePos : 0 < bank.prechargeBaseStateProduct := by
    rw [BankPaperRealization.prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := bank.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hchargePos : 0 < charge := by
    exact bank.selectorTailCharge_pos fixed hfixedPositive
  have hdivisorPos : 0 < divisor := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have htailPos : 0 < tail := by
    exact centralTailProduct_pos n (upperTailLength c n)
  have hchargeFactorization : ∀ p : ℕ,
      charge.factorization p =
        (fixed.prod id).factorization p +
          bank.prechargeBaseStateProduct.factorization p := by
    intro p
    dsimp only [charge]
    rw [bank.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct,
      Nat.factorization_mul hfixedProdPos.ne' hbasePos.ne',
      Finsupp.add_apply]
  have hdivisorHigh : ∀ p, p.Prime → yNat n < p →
      divisor.factorization p = 0 := by
    intro p hpPrime hpHigh
    apply Nat.factorization_eq_zero_of_not_dvd
    intro hpDvd
    have hpSupport := certificate.divisor_prime_support p hpPrime
      (by simpa only [divisor] using hpDvd)
    have hpLe := (mem_primesUpTo.mp hpSupport).2
    omega
  have hlow : ∀ p, p.Prime → p ≤ yNat n →
      divisor.factorization p + charge.factorization p ≤
        tail.factorization p := by
    intro p hpPrime hpLow
    have hpPos : 0 < p := hpPrime.pos
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
    have hpredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hpPrime.one_lt
    have hpredPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpredPosNat
    have hpredLe : (((p - 1 : ℕ) : ℝ)) ≤ (p : ℝ) := by
      exact_mod_cast Nat.sub_le p 1
    have hfixedP := hfixedChargeN bank p hpPrime hpLow
    have hfixedPred :
        ((fixed.prod id).factorization p : ℝ) ≤
          (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
      have hinv : 1 / (p : ℝ) ≤
          1 / (((p - 1 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le hpredPos hpredLe
      calc
        ((fixed.prod id).factorization p : ℝ) ≤
            (c - C0) / 24 * secondOrderScale n / (p : ℝ) := by
          simpa only [fixed] using hfixedP
        _ = ((c - C0) / 24 * secondOrderScale n) *
              (1 / (p : ℝ)) := by ring
        _ ≤ ((c - C0) / 24 * secondOrderScale n) *
              (1 / (((p - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hinv
            (mul_nonneg (by positivity) hscale.le)
        _ = (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
              secondOrderScale n := by
          field_simp [hpredPos.ne']
    by_cases hpSupport : p ∈ primesUpTo (2 * depth + 1)
    · have hretained := hretainedBefore p hpSupport
      have hcombinedReal :
          ((divisor.factorization p + charge.factorization p : ℕ) : ℝ) ≤
            (upperTailValuation c n p : ℝ) := by
        have hchargeCast : (charge.factorization p : ℝ) =
            ((fixed.prod id).factorization p : ℝ) +
              (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
          exact_mod_cast hchargeFactorization p
        have hreserveNonneg : 0 ≤
            (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
              secondOrderScale n := by positivity
        rw [Nat.cast_add, hchargeCast]
        calc
          (divisor.factorization p : ℝ) +
                (((fixed.prod id).factorization p : ℝ) +
                  (bank.prechargeBaseStateProduct.factorization p : ℝ)) ≤
              (divisor.factorization p : ℝ) +
                ((c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
                  secondOrderScale n) +
                (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
            linarith
          _ ≤ (divisor.factorization p : ℝ) +
                ((c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                  secondOrderScale n) +
                (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
            have htwice :
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                    secondOrderScale n =
                  2 * ((c - C0) /
                    (24 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n) := by
              field_simp [hpredPos.ne']
              ; ring
            rw [htwice]
            linarith
          _ ≤ (upperTailValuation c n p : ℝ) := by
            have hretained' := hretained
            simp only [Nat.cast_add] at hretained'
            linarith
      dsimp only [tail]
      rw [← upperTailValuation_eq_centralTailProduct_factorization]
      exact_mod_cast hcombinedReal
    · have hdivisorZero : divisor.factorization p = 0 := by
        apply Nat.factorization_eq_zero_of_not_dvd
        intro hpDvd
        exact hpSupport
          (certificate.divisor_prime_support p hpPrime
            (by simpa only [divisor] using hpDvd))
      rw [hdivisorZero, zero_add]
      have hbaseBound :=
        bank.prechargeBaseStateProduct_factorization_le_anchorMarkerBudget_log2_three_mul
          hpPrime hendpointN.2
      have hchargeCost :
          (p - 1) *
              (charge.factorization p + Nat.log2 (upperTailLength c n) + 1) ≤
            upperTailLength c n := by
        have hchargeBoundNat :
            charge.factorization p ≤
              (fixed.prod id).factorization p +
                bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) := by
          rw [hchargeFactorization p]
          exact Nat.add_le_add_left hbaseBound _
        have hpredFixed :
            (((p - 1) * (fixed.prod id).factorization p : ℕ) : ℝ) ≤
              (c - C0) / 24 * secondOrderScale n := by
          rw [Nat.cast_mul]
          calc
            (((p - 1 : ℕ) : ℝ)) *
                  ((fixed.prod id).factorization p : ℝ) ≤
                (((p - 1 : ℕ) : ℝ)) *
                  ((c - C0) / 24 * secondOrderScale n / (p : ℝ)) :=
              mul_le_mul_of_nonneg_left
                (by simpa only [fixed] using hfixedP)
                (Nat.cast_nonneg _)
            _ = ((c - C0) / 24 * secondOrderScale n) *
                ((((p - 1 : ℕ) : ℝ)) / (p : ℝ)) := by ring
            _ ≤ ((c - C0) / 24 * secondOrderScale n) * 1 := by
              apply mul_le_mul_of_nonneg_left
              · exact (div_le_one hpR).2 hpredLe
              · positivity
            _ = (c - C0) / 24 * secondOrderScale n := by ring
        have hpredOverheadNat :
            (p - 1) *
                (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                  Nat.log2 (upperTailLength c n) + 1) ≤
              bankPaperPrechargeUniformCapacityCost c n := by
          rw [bankPaperPrechargeUniformCapacityCost,
            Nat.log2_eq_log_two]
          exact Nat.mul_le_mul_right _
            ((Nat.sub_le p 1).trans hpLow)
        have hcapacityCast :
            (bankPaperPrechargeUniformCapacityCost c n : ℝ) <
              c / 4 * secondOrderScale n := by
          exact (div_lt_iff₀ hscale).mp hcapacityN
        have htailCast :
            c / 2 * secondOrderScale n <
              (upperTailLength c n : ℝ) := by
          exact (lt_div_iff₀ hscale).mp htailN
        have hoverheadCast :
            (((p - 1) *
                (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                  Nat.log2 (upperTailLength c n) + 1) : ℕ) : ℝ) ≤
              (bankPaperPrechargeUniformCapacityCost c n : ℝ) := by
          exact_mod_cast hpredOverheadNat
        have hcoeff :
            (c - C0) / 24 + c / 4 < c / 2 := by
          nlinarith
        have hsum :
            (((p - 1) * (fixed.prod id).factorization p : ℕ) : ℝ) +
                (((p - 1) *
                  (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                    Nat.log2 (upperTailLength c n) + 1) : ℕ) : ℝ) <
              c / 2 * secondOrderScale n := by
          calc
            _ ≤ (c - C0) / 24 * secondOrderScale n +
                  (bankPaperPrechargeUniformCapacityCost c n : ℝ) :=
              add_le_add hpredFixed hoverheadCast
            _ < (c - C0) / 24 * secondOrderScale n +
                  c / 4 * secondOrderScale n :=
              add_lt_add_right hcapacityCast _
            _ = ((c - C0) / 24 + c / 4) * secondOrderScale n := by ring
            _ < c / 2 * secondOrderScale n :=
              mul_lt_mul_of_pos_right hcoeff hscale
        have hsumTail :
            (((p - 1) * (fixed.prod id).factorization p : ℕ) : ℝ) +
                (((p - 1) *
                  (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                    Nat.log2 (upperTailLength c n) + 1) : ℕ) : ℝ) <
              (upperTailLength c n : ℝ) := hsum.trans htailCast
        have hsumNat :
            (p - 1) * (fixed.prod id).factorization p +
                (p - 1) *
                  (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                    Nat.log2 (upperTailLength c n) + 1) ≤
              upperTailLength c n := by
          exact_mod_cast hsumTail.le
        have hcrossNat :
            (p - 1) *
                ((fixed.prod id).factorization p +
                  bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
                  Nat.log2 (upperTailLength c n) + 1) ≤
              upperTailLength c n := by
          simpa only [Nat.add_assoc, Nat.mul_add] using hsumNat
        exact (Nat.mul_le_mul_left (p - 1)
          (by
            simpa only [Nat.add_assoc] using
              Nat.add_le_add_right hchargeBoundNat
                (Nat.log2 (upperTailLength c n) + 1))).trans hcrossNat
      simpa only [tail] using
        (centralTailProduct_factorization_ge_of_cross_capacity
          (n := n) hpPrime hchargeCost)
  have hhigh : ∀ p, p.Prime → yNat n < p →
      charge.factorization p ≤ tail.factorization p := by
    intro p hpPrime hpHigh
    simpa only [charge, fixed, tail] using
      bank.paperFixedExceptional_selectorTailCharge_factorization_le
        deltaStar hpHigh
  have hanchorCharge : divisor * charge ∣ tail :=
    mul_dvd_of_factorization_split hdivisorPos hchargePos htailPos
      hdivisorHigh hlow hhigh
  have hchargeDvd : charge ∣ certificate.prechargedTailTarget := by
    rw [GuardedCentralAnchorCertificate.prechargedTailTarget]
    exact (Nat.dvd_div_iff_mul_dvd certificate.divisor_dvd_tail).2
      (by simpa only [divisor, tail] using hanchorCharge)
  have hselectorIdentity :
      certificate.selectorTailTarget bank fixed * charge =
        certificate.prechargedTailTarget := by
    simpa only [charge] using
      certificate.selectorTailTarget_mul_selectorTailCharge
        bank fixed hchargeDvd
  have hcombinedRetained : ∀ p ∈ primesUpTo (2 * depth + 1),
      (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n + charge.factorization p ≤
        certificate.prechargedTailTarget.factorization p := by
    intro p hpSupport
    have hpPrime := (mem_primesUpTo.mp hpSupport).1
    have hpLow := (mem_primesUpTo.mp hpSupport).2.trans hsupportN
    have hpPredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hpPrime.one_lt
    have hpPredPos : (0 : ℝ) < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpPredPosNat
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    have hpPredLe : (((p - 1 : ℕ) : ℝ)) ≤ (p : ℝ) := by
      exact_mod_cast Nat.sub_le p 1
    have hfixedP := hfixedChargeN bank p hpPrime hpLow
    have hfixedPred :
        ((fixed.prod id).factorization p : ℝ) ≤
          (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n := by
      have hinv : 1 / (p : ℝ) ≤
          1 / (((p - 1 : ℕ) : ℝ)) :=
        one_div_le_one_div_of_le hpPredPos hpPredLe
      calc
        ((fixed.prod id).factorization p : ℝ) ≤
            (c - C0) / 24 * secondOrderScale n / (p : ℝ) := by
          simpa only [fixed] using hfixedP
        _ = ((c - C0) / 24 * secondOrderScale n) *
              (1 / (p : ℝ)) := by ring
        _ ≤ ((c - C0) / 24 * secondOrderScale n) *
              (1 / (((p - 1 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_left hinv
            (mul_nonneg (by positivity) hscale.le)
        _ = (c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
              secondOrderScale n := by
          field_simp [hpPredPos.ne']
    have htarget := hretainedTarget p hpSupport
    have hchargeCast : (charge.factorization p : ℝ) =
        ((fixed.prod id).factorization p : ℝ) +
          (bank.prechargeBaseStateProduct.factorization p : ℝ) := by
      exact_mod_cast hchargeFactorization p
    rw [hchargeCast]
    have htwice :
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n =
          2 * ((c - C0) / (24 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n) := by
      field_simp [hpPredPos.ne']
      ; ring
    rw [htwice] at htarget
    linarith
  refine ⟨bank, certificate, hanchorBank, hbaseDvd, ?_, ?_, ?_,
    htargetIdentity⟩
  · simpa only [charge, fixed] using hchargeDvd
  · intro p hpSupport
    simpa only [charge, fixed, Nat.cast_ofNat] using
      hcombinedRetained p hpSupport
  · simpa only [charge, fixed] using hselectorIdentity

/-! ## Tangent-compatible exponent after capacity -/

/-- After the capacity depth has been selected, every later choice of
`W` and every `r0 < 2` has a simultaneous charge/clean-list exponent and
the fixed-depth combined-charge terminal for that same exponent. -/
theorem exists_depth_bankPaperCombinedChargeTerminal_uniform_tangentChoice
    {c : ℝ} (hc : C0 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ (W : ℕ) (r0 : ℝ), r0 < 2 →
        IsPaperCombinedTangentDeltaStar c W r0
            (paperCombinedTangentDeltaStar c W r0) ∧
          BankPaperCombinedChargeTerminalAtDepth c
            (paperCombinedTangentDeltaStar c W r0) depth := by
  obtain ⟨depth, hdepth, huniform⟩ :=
    exists_depth_bankPaperCombinedChargeTerminal_uniform_deltaStar hc
  refine ⟨depth, hdepth, ?_⟩
  intro W r0 hr0
  have hspec := paperCombinedTangentDeltaStar_spec W hc hr0
  exact ⟨hspec, huniform _ hspec.1⟩

end

end Erdos390.WholePaper
