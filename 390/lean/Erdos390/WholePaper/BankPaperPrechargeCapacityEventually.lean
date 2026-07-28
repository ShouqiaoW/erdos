import Erdos390.WholePaper.BankAnchorCollisionFree
import Erdos390.WholePaper.BankGuardedCentralAnchorExistence
import Erdos390.WholePaper.BankPaperPrechargeCapacityAlgebra
import Erdos390.WholePaper.BankPaperPrechargeUniformCapacityAsymptotic
import Erdos390.WholePaper.BankPaperPrechargedTailTarget

/-!
# Eventual literal capacity for the guarded anchor and precharged bank

The analytic uniform-capacity estimates discharge every numerical input of
the finite capacity algebra.  Combining them with the actual guarded-anchor
existence theorem produces, at every sufficiently large paper endpoint, a
literal bank realization and certificate for which the guarded central
divisor together with the complete precharged base bank divides the
factorial tail.  Equivalently, the generic exactification base bank divides
the quotient target left after the anchor charge.
-/

open Filter Topology

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

/-- Terminal output of the precharge-capacity stage.  The witnesses are the
actual paper bank and its guarded modified central-anchor certificate; all
three displayed conclusions are division-free or literal natural-number
divisibility statements. -/
theorem exists_eventually_bankPaperPrechargedTailTarget
    {c : ℝ} (hc : C0 < c) :
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
              (baseBankFactors bank.exactificationState).prod id ∣
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) := by
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hdelta : (0 : ℝ) < (c - C0) / 6 := by linarith
  obtain ⟨depth, hdepth, hanchors⟩ :=
    exists_eventually_bankGuardedCentralAnchorCertificate hc
  have hperPrime :=
    eventually_bankPaperPrecharge_perPrimeCapacity hdelta
  have hmoving :=
    eventually_bankPaperPrecharge_uniformMovingPrimeCapacity hcPos
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  have hsupport := eventually_bankAnchor_fixed_le_yNat (2 * depth + 1)
  refine ⟨depth, hdepth, ?_⟩
  filter_upwards [hanchors, hperPrime, hmoving, hendpoint, hsupport]
      with n hanchorN hperPrimeN hmovingN hendpointN hsupportN
  obtain ⟨bank, hcertificate⟩ := hanchorN
  obtain ⟨certificate⟩ := hcertificate
  have hfixedReserve : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n := by
    intro p hpMem
    have hpData := mem_primesUpTo.mp hpMem
    have hpCutoff : p ≤ yNat n := hpData.2.trans hsupportN
    simpa only [Nat.log2_eq_log_two, div_div] using
      hperPrimeN p hpData.1 hpCutoff
  have huniformCapacity : ∀ p, p.Prime → p ≤ yNat n →
      p ∉ primesUpTo (2 * depth + 1) →
        (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          upperTailLength c n := by
    intro p _hpPrime hpCutoff _hpSupport
    have hpPred : p - 1 ≤ yNat n := (Nat.sub_le p 1).trans hpCutoff
    calc
      (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          yNat n *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) :=
        Nat.mul_le_mul_right _ hpPred
      _ ≤ upperTailLength c n := by
        simpa only [Nat.log2_eq_log_two] using hmovingN
  have hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q * bank.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n) :=
    certificate.mul_prechargeBaseStateProduct_dvd_centralTailProduct_of_capacity
      bank hsupportN hendpointN.2 hfixedReserve huniformCapacity
  refine ⟨bank, certificate, hcombined, ?_, ?_⟩
  · exact certificate.baseExactificationBank_prod_dvd_prechargedTailTarget
      bank hcombined
  · exact certificate.prechargedTailTarget_mul_centralAnchorDivisor

namespace GuardedCentralAnchorCertificate

/-- A retained real valuation bound beside the anchor and precharged bank
descends exactly to the quotient target left after the anchor charge. -/
theorem prechargeBaseStateProduct_factorization_add_retained_le_prechargedTailTarget
    {c : ℝ} {depth n p : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ} {retained : ℝ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (bank : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (hretained :
      retained +
          (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                certificate.q).factorization p +
            bank.prechargeBaseStateProduct.factorization p : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ)) :
    retained +
        (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
      (certificate.prechargedTailTarget.factorization p : ℝ) := by
  have htargetPos : 0 < certificate.prechargedTailTarget :=
    certificate.prechargedTailTarget_pos
  have hdivisorPos :
      0 < centralAnchorDivisor n (centralAnchorCutoff depth n)
        certificate.q :=
    centralAnchorDivisor_pos certificate.isCofactorChoice
  have htailFactorization :
      (centralTailProduct n
          (upperTailLength c n)).factorization p =
        certificate.prechargedTailTarget.factorization p +
          (centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p := by
    calc
      (centralTailProduct n
          (upperTailLength c n)).factorization p =
          (certificate.prechargedTailTarget *
            centralAnchorDivisor n (centralAnchorCutoff depth n)
              certificate.q).factorization p := by
        rw [certificate.prechargedTailTarget_mul_centralAnchorDivisor]
      _ = certificate.prechargedTailTarget.factorization p +
          (centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p := by
        rw [Nat.factorization_mul htargetPos.ne' hdivisorPos.ne',
          Finsupp.add_apply]
  have hbound := hretained
  rw [upperTailValuation_eq_centralTailProduct_factorization,
    htailFactorization] at hbound
  simp only [Nat.cast_add] at hbound
  linarith

end GuardedCentralAnchorCertificate

/-- Strengthened terminal precharge output.  One twelfth of the original
`c - C0` reserve pays for the bank on every fixed anchor prime and a second
twelfth remains visible, both before and after passing to the quotient target
left by the anchor charge. -/
theorem exists_eventually_bankPaperPrechargedTailTarget_with_twelfthReserve
    {c : ℝ} (hc : C0 < c) :
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
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (((centralAnchorDivisor n (centralAnchorCutoff depth n)
                          certificate.q).factorization p +
                      bank.prechargeBaseStateProduct.factorization p : ℕ) : ℝ) ≤
                  (upperTailValuation c n p : ℝ)) ∧
              (∀ p ∈ primesUpTo (2 * depth + 1),
                (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
                      secondOrderScale n +
                    (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
                  (certificate.prechargedTailTarget.factorization p : ℝ)) ∧
              (baseBankFactors bank.exactificationState).prod id ∣
                certificate.prechargedTailTarget ∧
              certificate.prechargedTailTarget *
                  centralAnchorDivisor n (centralAnchorCutoff depth n)
                    certificate.q =
                centralTailProduct n (upperTailLength c n) := by
  have hC0Pos : (0 : ℝ) < C0 := by norm_num [C0]
  have hcPos : 0 < c := hC0Pos.trans hc
  have hdeltaSixth : (0 : ℝ) < (c - C0) / 6 := by linarith
  have hdeltaTwelfth : (0 : ℝ) < (c - C0) / 12 := by linarith
  obtain ⟨depth, hdepth, hanchors⟩ :=
    exists_eventually_bankGuardedCentralAnchorCertificate hc
  have hperPrimeSixth :=
    eventually_bankPaperPrecharge_perPrimeCapacity hdeltaSixth
  have hperPrimeTwelfth :=
    eventually_bankPaperPrecharge_perPrimeCapacity hdeltaTwelfth
  have hmoving :=
    eventually_bankPaperPrecharge_uniformMovingPrimeCapacity hcPos
  have hendpoint := eventually_upperScaledEndpoint_bounds hcPos
  have hsupport := eventually_bankAnchor_fixed_le_yNat (2 * depth + 1)
  refine ⟨depth, hdepth, ?_⟩
  filter_upwards [hanchors, hperPrimeSixth, hperPrimeTwelfth, hmoving,
      hendpoint, hsupport]
      with n hanchorN hperPrimeSixthN hperPrimeTwelfthN hmovingN
        hendpointN hsupportN
  obtain ⟨bank, hcertificate⟩ := hanchorN
  obtain ⟨certificate⟩ := hcertificate
  have hfixedReserve : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n := by
    intro p hpMem
    have hpData := mem_primesUpTo.mp hpMem
    have hpCutoff : p ≤ yNat n := hpData.2.trans hsupportN
    simpa only [Nat.log2_eq_log_two, div_div] using
      hperPrimeSixthN p hpData.1 hpCutoff
  have hfixedTwelfth : ∀ p ∈ primesUpTo (2 * depth + 1),
      ((bankPaperAnchorMarkerBudget n *
          Nat.log2 (3 * n) : ℕ) : ℝ) ≤
        (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
          secondOrderScale n := by
    intro p hpMem
    have hpData := mem_primesUpTo.mp hpMem
    have hpCutoff : p ≤ yNat n := hpData.2.trans hsupportN
    simpa only [Nat.log2_eq_log_two, div_div] using
      hperPrimeTwelfthN p hpData.1 hpCutoff
  have huniformCapacity : ∀ p, p.Prime → p ≤ yNat n →
      p ∉ primesUpTo (2 * depth + 1) →
        (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          upperTailLength c n := by
    intro p _hpPrime hpCutoff _hpSupport
    have hpPred : p - 1 ≤ yNat n := (Nat.sub_le p 1).trans hpCutoff
    calc
      (p - 1) *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) ≤
          yNat n *
            (bankPaperAnchorMarkerBudget n * Nat.log2 (3 * n) +
              Nat.log2 (upperTailLength c n) + 1) :=
        Nat.mul_le_mul_right _ hpPred
      _ ≤ upperTailLength c n := by
        simpa only [Nat.log2_eq_log_two] using hmovingN
  have hcombined :
      centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q * bank.prechargeBaseStateProduct ∣
        centralTailProduct n (upperTailLength c n) :=
    certificate.mul_prechargeBaseStateProduct_dvd_centralTailProduct_of_capacity
      bank hsupportN hendpointN.2 hfixedReserve huniformCapacity
  have hretained :=
    certificate.precharge_fixedSupport_factorization_add_twelfthReserve_le_upperTailValuation
      bank hendpointN.2 hfixedTwelfth
  have htargetRetained : ∀ p ∈ primesUpTo (2 * depth + 1),
      (c - C0) / (12 * (((p - 1 : ℕ) : ℝ))) *
            secondOrderScale n +
          (bank.prechargeBaseStateProduct.factorization p : ℝ) ≤
        (certificate.prechargedTailTarget.factorization p : ℝ) := by
    intro p hpMem
    exact
      certificate.prechargeBaseStateProduct_factorization_add_retained_le_prechargedTailTarget
        bank (hretained p hpMem)
  refine ⟨bank, certificate, hcombined, hretained, htargetRetained, ?_, ?_⟩
  · exact certificate.baseExactificationBank_prod_dvd_prechargedTailTarget
      bank hcombined
  · exact certificate.prechargedTailTarget_mul_centralAnchorDivisor

end

end Erdos390.WholePaper
