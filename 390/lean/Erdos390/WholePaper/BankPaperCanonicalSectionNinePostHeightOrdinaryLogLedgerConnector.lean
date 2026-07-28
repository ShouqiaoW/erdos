import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightPlacedMeasureConnector
import Erdos390.WholePaper.BankPaperCanonicalTopFrozenOrdinaryLogHeightReductionConnector
import Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector

/-!
# Exact post-height ordinary-log ledger

The post-height baseline realizes the paper's ordinary logarithm exactly.
This file connects that finite moment to the residual selector target.

There are two logically separate ingredients.

* The target/frozen charge ledger identifies the logarithm left for the
  fractional selector after the fixed factors and the state-zero bank.
* Primewise source support says that every valuation deficit outside
  `W < p <= y` is already zero.

Together with the exact post-height moment these imply that the
`tPrime`-weighted initial residual is zero.  No ordinary-log compatibility,
weighted-residual identity, or target envelope is assumed as an input.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.PaperHeadSimplex

noncomputable section

/-! ## A finite factorization support for a selector -/

/-- The finite set containing every prime occurring in either the residual
target or one of the numerical selector coordinates. -/
def bankPaperCanonicalSelectorLogSupport
    (target : Nat) (candidates : Finset Nat) : Finset Nat :=
  target.factorization.support ∪
    candidates.biUnion fun a => a.factorization.support

/-- Expand the target logarithm on the common finite selector support. -/
theorem bankPaperCanonical_log_target_eq_sum_factorization_on_selectorLogSupport
    (target : Nat) (candidates : Finset Nat) :
    Real.log (target : Real) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (target.factorization p : Real) * Real.log (p : Real) := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  change
    (∑ p ∈ target.factorization.support,
        (target.factorization p : Real) * Real.log (p : Real)) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (target.factorization p : Real) * Real.log (p : Real)
  apply Finset.sum_subset
  · exact Finset.subset_union_left
  · intro p _hp hpNotSupport
    have hpZero : target.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNotSupport
    simp [hpZero]

/-- Expand one candidate logarithm on the same common finite support. -/
theorem bankPaperCanonical_log_candidate_eq_sum_factorization_on_selectorLogSupport
    (target : Nat) (candidates : Finset Nat)
    {a : Nat} (ha : a ∈ candidates) :
    Real.log (a : Real) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (a.factorization p : Real) * Real.log (p : Real) := by
  classical
  rw [Real.log_nat_eq_sum_factorization]
  change
    (∑ p ∈ a.factorization.support,
        (a.factorization p : Real) * Real.log (p : Real)) =
      ∑ p ∈ bankPaperCanonicalSelectorLogSupport target candidates,
        (a.factorization p : Real) * Real.log (p : Real)
  apply Finset.sum_subset
  · intro p hp
    exact Finset.mem_union_right _
      (Finset.mem_biUnion.mpr ⟨a, ha, hp⟩)
  · intro p _hp hpNotSupport
    have hpZero : a.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNotSupport
    simp [hpZero]

/-! ## Ordinary logarithm equals the logarithmically weighted deficit -/

/-- Once the selector deficit is supported on the medium-prime band, its
ordinary logarithmic defect is exactly the `log p`-weighted band deficit.

This is the finite unique-factorization calculation underlying the paper's
display `sum_p r_p log p = 0`. -/
theorem bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates selector) :
    Real.log (certificate.selectorTailTarget R fixed : Real) -
        ∑ a ∈ candidates, selector a * Real.log (a : Real) =
      ∑ p ∈ primeBand n W,
        bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector p *
          Real.log (p : Real) := by
  classical
  let target := certificate.selectorTailTarget R fixed
  let support :=
    bankPaperCanonicalSelectorLogSupport target candidates ∪ primeBand n W
  have htarget :
      Real.log (target : Real) =
        ∑ p ∈ support,
          (target.factorization p : Real) * Real.log (p : Real) := by
    rw [
      bankPaperCanonical_log_target_eq_sum_factorization_on_selectorLogSupport
        target candidates]
    apply Finset.sum_subset
    · exact Finset.subset_union_left
    · intro p _hp hpNot
      have hpZero : target.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hpFactor
        apply hpNot
        exact Finset.mem_union_left _ hpFactor
      simp [hpZero]
  have hcandidate (a : Nat) (ha : a ∈ candidates) :
      Real.log (a : Real) =
        ∑ p ∈ support,
          (a.factorization p : Real) * Real.log (p : Real) := by
    rw [
      bankPaperCanonical_log_candidate_eq_sum_factorization_on_selectorLogSupport
        target candidates ha]
    apply Finset.sum_subset
    · exact Finset.subset_union_left
    · intro p _hp hpNot
      have hpZero : a.factorization p = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro hpFactor
        apply hpNot
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨a, ha, hpFactor⟩)
      simp [hpZero]
  have hselectorSwap :
      (∑ a ∈ candidates,
          selector a *
            ∑ p ∈ support,
              (a.factorization p : Real) * Real.log (p : Real)) =
        ∑ p ∈ support,
          (∑ a ∈ candidates,
              selector a * (a.factorization p : Real)) *
            Real.log (p : Real) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  have hfull :
      Real.log (target : Real) -
          ∑ a ∈ candidates, selector a * Real.log (a : Real) =
        ∑ p ∈ support,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real) := by
    have hselectorLog :
        (∑ a ∈ candidates, selector a * Real.log (a : Real)) =
          ∑ a ∈ candidates,
            selector a *
              ∑ p ∈ support,
                (a.factorization p : Real) * Real.log (p : Real) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hcandidate a ha]
    rw [htarget]
    rw [hselectorLog]
    rw [hselectorSwap, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    unfold bankPaperCanonicalSelectorValuationDeficit
    dsimp only [target]
    ring
  have hbandSubset : primeBand n W ⊆ support :=
    Finset.subset_union_right
  have houtside :
      (∑ p ∈ support,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real)) =
        ∑ p ∈ primeBand n W,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real) := by
    symm
    apply Finset.sum_subset hbandSubset
    intro p _hpSupport hpNotBand
    have hpZero :
        bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector p = 0 := by
      by_cases hpPrime : p.Prime
      · exact hsupport p hpPrime hpNotBand
      · exact
          bankPaperCanonicalSelectorValuationDeficit_eq_zero_of_not_prime
            R certificate fixed candidates selector hpPrime
    simp [hpZero]
  simpa only [target] using hfull.trans houtside

/-- Normalizing the preceding identity by `log y` gives exactly the
`tPrime`-weighted residual used by Proposition 8.7. -/
theorem bankPaperCanonical_selectorWeightedResidual_eq_selectorLogDefect_div
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates selector) :
    (∑ p : BankPaperCanonicalTangentPrime n W,
        tPrime n p.1 *
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) =
      (Real.log (certificate.selectorTailTarget R fixed : Real) -
          ∑ a ∈ candidates, selector a * Real.log (a : Real)) /
        Real.log (y n) := by
  have hattach :
      (∑ p : BankPaperCanonicalTangentPrime n W,
          tPrime n p.1 *
            bankPaperCanonicalTangentResidual
              R certificate fixed candidates selector p) =
        ∑ p ∈ primeBand n W,
          tPrime n p *
            bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p := by
    simpa only [Finset.univ_eq_attach,
      bankPaperCanonicalTangentResidual] using
      (Finset.sum_attach (primeBand n W)
        (fun p =>
          tPrime n p *
            bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p))
  rw [hattach]
  calc
    (∑ p ∈ primeBand n W,
        tPrime n p *
          bankPaperCanonicalSelectorValuationDeficit
            R certificate fixed candidates selector p) =
        (∑ p ∈ primeBand n W,
          bankPaperCanonicalSelectorValuationDeficit
              R certificate fixed candidates selector p *
            Real.log (p : Real)) /
          Real.log (y n) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro p _hp
      unfold tPrime
      ring
    _ =
        (Real.log (certificate.selectorTailTarget R fixed : Real) -
            ∑ a ∈ candidates, selector a * Real.log (a : Real)) /
          Real.log (y n) := by
      rw [
        bankPaperCanonical_selectorLogDefect_eq_sum_log_mul_deficit
          R certificate fixed candidates selector hsupport]

/-- Exact equality of the selector logarithm and target logarithm therefore
supplies exact ordinary-log compatibility, with no mesh constant. -/
theorem bankPaperCanonicalSelector_ordinaryLogCompatible_of_selectorLog
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := W) R certificate fixed candidates selector)
    (hlog :
      Real.log (certificate.selectorTailTarget R fixed : Real) =
        ∑ a ∈ candidates, selector a * Real.log (a : Real)) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := W) R certificate fixed candidates selector := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatible
  rw [
    bankPaperCanonical_selectorWeightedResidual_eq_selectorLogDefect_div
      R certificate fixed candidates selector hsupport,
    hlog, sub_self, zero_div]

/-! ## Exact active/frozen logarithmic decomposition -/

/-- The ambient push-forward preserves every finite weighted statistic, not
just total mass. -/
theorem sum_bankPaperCanonicalActiveSeedAmbientWeight_mul
    {Head : Type*} [Fintype Head] [Nonempty Head]
    {D : StructuredSampleData Head} {T : BarycentricTarget D}
    {candidates : Finset Nat} {preSelector : Nat -> Real}
    {activeSeed : D.Sample -> Real}
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed)
    (F : Nat -> Real) :
    (∑ a ∈ candidates,
        bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a * F a) =
      ∑ m : D.Sample, activeSeed m * F (D.value m) := by
  classical
  unfold bankPaperCanonicalActiveSeedAmbientWeight
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [Finset.sum_eq_single (D.value m)]
  · simp
  · intro a _ha hne
    simp [hne.symm]
  · intro hnot
    exact (hnot (bankPaperCanonicalActiveSeed_value_mem_candidates H m)).elim

/-- Adding the literal active ordinary-log moment back to the exact frozen
logarithmic mass recovers the fixed charges plus the logarithm of the whole
pre-selector. -/
theorem bankPaperCanonicalActualFrozenLogMass_add_activeOrdinaryLog_eq
    {Head : Type*} [Fintype Head] [Nonempty Head]
    (D : StructuredSampleData Head) (T : BarycentricTarget D)
    (fixed bankBase candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : D.Sample -> Real)
    (H : BankPaperCanonicalActualActiveMeasureConstructor
      D T candidates preSelector activeSeed) :
    bankPaperCanonicalActualFrozenLogMass
          D fixed bankBase candidates preSelector activeSeed +
        (∑ m : D.Sample,
          activeSeed m * Real.log (D.value m : Real)) =
      (∑ a ∈ fixed, Real.log (a : Real)) +
        (∑ a ∈ bankBase, Real.log (a : Real)) +
        ∑ a ∈ candidates,
          preSelector a * Real.log (a : Real) := by
  classical
  have hpush :=
    sum_bankPaperCanonicalActiveSeedAmbientWeight_mul
      H (fun a => Real.log (a : Real))
  have hcandidates :
      (∑ a : BankPaperCanonicalActualFrozenIndex candidates,
          bankPaperCanonicalActualFrozenWeight
              D candidates preSelector activeSeed a *
            Real.log (bankPaperCanonicalActualFrozenValue a : Real)) +
          (∑ m : D.Sample,
            activeSeed m * Real.log (D.value m : Real)) =
        ∑ a ∈ candidates,
          preSelector a * Real.log (a : Real) := by
    rw [← hpush]
    unfold bankPaperCanonicalActualFrozenWeight
      bankPaperCanonicalActualFrozenValue
    rw [← Finset.sum_subtype candidates (fun _ => Iff.rfl)
      (fun a =>
        (preSelector a -
            bankPaperCanonicalActiveSeedAmbientWeight D activeSeed a) *
          Real.log (a : Real))]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    ring
  unfold bankPaperCanonicalActualFrozenLogMass
  linarith only [hcandidates]

/-! ## The exact selector-tail charge -/

/-- Logarithm of a positive natural-number product as a sum of logarithms. -/
theorem bankPaperCanonical_log_finset_prod_id
    (s : Finset Nat) (hpos : ∀ a ∈ s, 0 < a) :
    Real.log ((s.prod (fun a : Nat => a) : Nat) : Real) =
      ∑ a ∈ s, Real.log (a : Real) := by
  rw [Nat.cast_prod]
  apply Real.log_prod
  intro a ha
  exact_mod_cast (hpos a ha).ne'

/-- The quotient identity for `selectorTailTarget` gives the exact
fixed-plus-bank logarithmic charge of the precharged target. -/
theorem GuardedCentralAnchorCertificate.selectorTailTarget_log_charge
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset Nat)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget) :
    Real.log (certificate.prechargedTailTarget : Real) =
      (∑ a ∈ fixed, Real.log (a : Real)) +
        (∑ a ∈ baseBankFactors R.exactificationState,
          Real.log (a : Real)) +
        Real.log (certificate.selectorTailTarget R fixed : Real) := by
  have hbasePositive :
      ∀ a ∈ baseBankFactors R.exactificationState, 0 < a := by
    intro a ha
    rw [R.baseExactificationBank_eq_prechargeBaseState] at ha
    have hinterval := R.prechargeBaseState_subset_factorInterval ha
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1
  have hfixedProdPos :
      0 < ((fixed.prod (fun a : Nat => a) : Nat) : Real) := by
    exact_mod_cast
      (Finset.prod_pos fun a ha => hfixedPositive a ha)
  have hbaseProdPos :
      0 <
        (((baseBankFactors R.exactificationState).prod
          (fun a : Nat => a) : Nat) : Real) := by
    exact_mod_cast
      (Finset.prod_pos fun a ha => hbasePositive a ha)
  have htargetPos :
      0 < certificate.selectorTailTarget R fixed :=
    certificate.selectorTailTarget_pos
      R fixed hfixedPositive hchargeDvd
  have hchargePos : 0 < R.selectorTailCharge fixed :=
    R.selectorTailCharge_pos fixed hfixedPositive
  have hproduct :=
    certificate.selectorTailTarget_mul_selectorTailCharge
      R fixed hchargeDvd
  calc
    Real.log (certificate.prechargedTailTarget : Real) =
        Real.log
          ((certificate.selectorTailTarget R fixed *
            R.selectorTailCharge fixed : Nat) : Real) := by
      rw [hproduct]
    _ =
        Real.log (certificate.selectorTailTarget R fixed : Real) +
          Real.log (R.selectorTailCharge fixed : Real) := by
      rw [Nat.cast_mul, Real.log_mul]
      · exact_mod_cast htargetPos.ne'
      · exact_mod_cast hchargePos.ne'
    _ =
        Real.log (certificate.selectorTailTarget R fixed : Real) +
          (Real.log
              ((fixed.prod (fun a : Nat => a) : Nat) : Real) +
            Real.log
              (((baseBankFactors R.exactificationState).prod
                (fun a : Nat => a) : Nat) : Real)) := by
      unfold BankPaperRealization.selectorTailCharge
      simp only [id_eq] at hfixedProdPos hbaseProdPos ⊢
      rw [Nat.cast_mul,
        Real.log_mul hfixedProdPos.ne' hbaseProdPos.ne']
    _ =
        (∑ a ∈ fixed, Real.log (a : Real)) +
          (∑ a ∈ baseBankFactors R.exactificationState,
            Real.log (a : Real)) +
          Real.log (certificate.selectorTailTarget R fixed : Real) := by
      rw [
        bankPaperCanonical_log_finset_prod_id fixed hfixedPositive,
        bankPaperCanonical_log_finset_prod_id
          (baseBankFactors R.exactificationState) hbasePositive]
      ring

/-! ## The fresh post-height seed realizes `logY - Lambda0` -/

/-- The exact post-height ordinary-log moment is `logY - Lambda0` whenever
the scalar height input is the literal frozen-height defect. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment_eq_logY_sub_Lambda0
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (logY Lambda0 : Real)
    (hA0 : A0 = logY - Lambda0 - q0 * B.L) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalSectionNinePostHeightActiveSeed
            B I hlo hhi H m *
          B.ordinaryLogScore m) =
      logY - Lambda0 := by
  rw [
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment
      B I hlo hhi H]
  unfold bankPaperCanonicalSectionNinePostHeightActiveHeight
    bankPaperCanonicalSectionNinePostHeightActiveMass
  rw [hA0]
  ring

/-! ## Complete post-height selector ledger -/

/-- The active/frozen split and the scalar post-height identity recover the
exact logarithm of the whole pre-selector.  The charge premise is a source
product ledger, not an ordinary-log compatibility assumption. -/
theorem bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed bankBase candidates : Finset Nat)
    (preSelector : Nat -> Real)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H))
    (logY Lambda0 : Real)
    (hA0 : A0 = logY - Lambda0 - q0 * B.L)
    (hLambda0 :
      Lambda0 =
        bankPaperCanonicalActualFrozenLogMass B.sampleData
          fixed bankBase candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H))
    (hcharge :
      logY =
        (∑ a ∈ fixed, Real.log (a : Real)) +
          (∑ a ∈ bankBase, Real.log (a : Real)) +
          Real.log (certificate.selectorTailTarget R fixed : Real)) :
    Real.log (certificate.selectorTailTarget R fixed : Real) =
      ∑ a ∈ candidates, preSelector a * Real.log (a : Real) := by
  have hactive :=
    bankPaperCanonicalSectionNinePostHeight_activeSeed_ordinaryLogMoment_eq_logY_sub_Lambda0
      B I hlo hhi H logY Lambda0 hA0
  have hfrozen :=
    bankPaperCanonicalActualFrozenLogMass_add_activeOrdinaryLog_eq
      B.sampleData
      (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      fixed bankBase candidates preSelector
      (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H)
      Hmeasure
  have htotal :
      (∑ a ∈ fixed, Real.log (a : Real)) +
          (∑ a ∈ bankBase, Real.log (a : Real)) +
          ∑ a ∈ candidates, preSelector a * Real.log (a : Real) =
        logY := by
    calc
      (∑ a ∈ fixed, Real.log (a : Real)) +
            (∑ a ∈ bankBase, Real.log (a : Real)) +
            ∑ a ∈ candidates, preSelector a * Real.log (a : Real) =
          bankPaperCanonicalActualFrozenLogMass B.sampleData
                fixed bankBase candidates preSelector
                  (bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H) +
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m *
                Real.log (B.sampleData.value m : Real)) := hfrozen.symm
      _ = Lambda0 +
            (∑ m : B.sampleData.Sample,
              bankPaperCanonicalSectionNinePostHeightActiveSeed
                    B I hlo hhi H m *
                B.ordinaryLogScore m) := by
          rw [hLambda0]
          rfl
      _ = Lambda0 + (logY - Lambda0) := by rw [hactive]
      _ = logY := by ring
  linarith only [htotal, hcharge]

/-- Specialization of the preceding theorem to the literal quotient target:
`logY` is the logarithm of `prechargedTailTarget`, and the frozen integral
charges are exactly the selector-fixed factors and state-zero bank. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target_of_prechargedTail
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H))
    (Lambda0 : Real)
    (hA0 :
      A0 =
        Real.log (certificate.prechargedTailTarget : Real) -
          Lambda0 - q0 * B.L)
    (hLambda0 :
      Lambda0 =
        bankPaperCanonicalActualFrozenLogMass B.sampleData
          fixed (baseBankFactors R.exactificationState)
          candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget) :
    Real.log (certificate.selectorTailTarget R fixed : Real) =
      ∑ a ∈ candidates, preSelector a * Real.log (a : Real) := by
  apply bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target
    B R certificate fixed (baseBankFactors R.exactificationState)
      candidates preSelector I hlo hhi H Hmeasure
      (Real.log (certificate.prechargedTailTarget : Real)) Lambda0
      hA0 hLambda0
  exact certificate.selectorTailTarget_log_charge
    R fixed hfixedPositive hchargeDvd

/-- The literal quotient charge, exact post-height moment, actual frozen
ledger, and prime-band source support imply exact initial compatibility. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_initialSelector_ordinaryLogCompatible
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H))
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (Lambda0 : Real)
    (hA0 :
      A0 =
        Real.log (certificate.prechargedTailTarget : Real) -
          Lambda0 - q0 * B.L)
    (hLambda0 :
      Lambda0 =
        bankPaperCanonicalActualFrozenLogMass B.sampleData
          fixed (baseBankFactors R.exactificationState)
          candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget) :
    BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := B.sampleData.W) R certificate fixed candidates preSelector := by
  apply bankPaperCanonicalSelector_ordinaryLogCompatible_of_selectorLog
    R certificate fixed candidates preSelector hsupport
  exact
    bankPaperCanonicalSectionNinePostHeight_selectorLog_eq_target_of_prechargedTail
      B R certificate fixed candidates preSelector I hlo hhi H Hmeasure
        Lambda0 hA0 hLambda0 hfixedPositive hchargeDvd

/-- In the actual bridge, the exact compatibility just proved is the
requested active-target minus initial prime-log identity. -/
theorem
    bankPaperCanonicalSectionNinePostHeight_weightedActiveTarget_sub_primeLogMoment_eq_zero
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (I : PhysicalIntervals)
    (hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n)
    (hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n)
    {q0 A0 : Real} {d : Int} {exponent : Nat}
    {activeHeadTarget : {p : Nat // p ∈ P} -> Real}
    (H : BankPaperCanonicalSectionNinePostHeightBaselineTargetInputs
      B I q0 A0 d exponent activeHeadTarget)
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData
        (bankPaperCanonicalSectionNinePostHeightTarget B I hlo hhi H)
      candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H))
    (hseed : ∀ m,
      B.baseline.baseWeight m =
        bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H m)
    (hsupport : BankPaperCanonicalSelectorDeficitSupportedOnPrimeBand
      (W := B.sampleData.W) R certificate fixed candidates preSelector)
    (Lambda0 : Real)
    (hA0 :
      A0 =
        Real.log (certificate.prechargedTailTarget : Real) -
          Lambda0 - q0 * B.L)
    (hLambda0 :
      Lambda0 =
        bankPaperCanonicalActualFrozenLogMass B.sampleData
          fixed (baseBankFactors R.exactificationState)
          candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H))
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd :
      R.selectorTailCharge fixed ∣ certificate.prechargedTailTarget) :
    (∑ p : BankPaperCanonicalTangentPrime
        B.sampleData.n B.sampleData.W,
      tPrime B.sampleData.n p.1 *
        bankPaperCanonicalActualActiveMarkedTarget B R certificate
          fixed candidates preSelector
            (bankPaperCanonicalSectionNinePostHeightActiveSeed
              B I hlo hhi H) p.1) -
      B.paperMoment B.primeLogScore 0 = 0 := by
  have hordinary :=
    bankPaperCanonicalSectionNinePostHeight_initialSelector_ordinaryLogCompatible
      B R certificate fixed candidates preSelector I hlo hhi H Hmeasure
        hsupport Lambda0 hA0 hLambda0 hfixedPositive hchargeDvd
  have hresidual :=
    bankPaperCanonicalActualInitialSelector_weightedResidual_eq
      B R certificate fixed candidates preSelector
        (bankPaperCanonicalSectionNinePostHeightActiveSeed B I hlo hhi H)
        Hmeasure hseed
  rw [← hresidual]
  exact hordinary

end

end Erdos390.WholePaper
