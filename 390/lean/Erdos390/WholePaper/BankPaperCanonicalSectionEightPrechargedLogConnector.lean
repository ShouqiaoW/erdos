import Erdos390.WholePaper.BankPaperCanonicalSectionEightActualDataConnector
import Erdos390.WholePaper.BankPaperPrechargedTailTarget
import Erdos390.WholePaper.UpperTailValuationAsymptotic

/-!
# Paper-faithful precharged logarithmic target for Section 8

Section 8 removes the guarded central-anchor divisor before it forms the
ordinary-log target used by the smooth height ledger.  Thus the literal
quantity called `log Y` in the paper is

`log (centralTailProduct / centralAnchorDivisor)`,

not the logarithm of the complete central tail.  This file gives that
certificate-dependent target a total extension on an honest guarded tail
family.  On the finite prefix the extension agrees with the complete-tail
logarithm and the anchor log is zero; this convention changes no asymptotic
statement and makes their exact additive identity valid at every index.

The anchor logarithm is `O(secondOrderScale)` without any new analytic
assumption.  Its factorization has fixed support
`primesUpTo (2 * depth + 1)`, and exact divisibility bounds each supported
valuation by the corresponding upper-tail valuation.  The existing
fixed-prime valuation asymptotic then supplies the required finite sum
bound.  Subtracting this anchor log transfers both the centered complete-tail
estimate and any already-constructed Section 8 analytic ledger to the
paper's precharged logarithmic target.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperCanonicalGuardedTailFamily

/-- Total extension of the paper's residual logarithmic target.  Below the
honest tail threshold it is set equal to the complete-tail log, so no
realization or certificate is requested there. -/
def extendedPrechargedTailLogTarget
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) : Real :=
  if hn : N <= n then
    Real.log
      ((BankPaperCanonicalGuardedTailFamily.certificate
        F n hn).prechargedTailTarget : Real)
  else
    bankPaperCanonicalCentralTailLogTarget c n

/-- Total extension of the logarithm of the guarded central-anchor divisor.
The synthetic finite prefix is zero, complementary to
`extendedPrechargedTailLogTarget`. -/
def extendedCentralAnchorDivisorLog
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) : Real :=
  if hn : N <= n then
    Real.log
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
        (BankPaperCanonicalGuardedTailFamily.certificate F n hn).q :
          Real)
  else
    0

/-- On a genuine tail fiber, the total precharged target is the literal
certificate-dependent quotient target. -/
theorem extendedPrechargedTailLogTarget_eq
    {c : Real} {depth N n : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hn : N <= n) :
    F.extendedPrechargedTailLogTarget n =
      Real.log ((F.certificate n hn).prechargedTailTarget : Real) := by
  rw [extendedPrechargedTailLogTarget, dif_pos hn]

/-- On a genuine tail fiber, the total anchor log is the literal guarded
central-anchor-divisor log. -/
theorem extendedCentralAnchorDivisorLog_eq
    {c : Real} {depth N n : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hn : N <= n) :
    F.extendedCentralAnchorDivisorLog n =
      Real.log
        (centralAnchorDivisor n (centralAnchorCutoff depth n)
          (F.certificate n hn).q : Real) := by
  rw [extendedCentralAnchorDivisorLog, dif_pos hn]

/-- Exact paper identity on every genuine tail fiber:
`log Y + log D' = log T`. -/
theorem extendedPrechargedTailLogTarget_add_anchorLog_of_tail
    {c : Real} {depth N n : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (hn : N <= n) :
    F.extendedPrechargedTailLogTarget n +
        F.extendedCentralAnchorDivisorLog n =
      bankPaperCanonicalCentralTailLogTarget c n := by
  let certificate := F.certificate n hn
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  have htarget : certificate.prechargedTailTarget * divisor =
      centralTailProduct n (upperTailLength c n) := by
    simpa only [divisor] using
      certificate.prechargedTailTarget_mul_centralAnchorDivisor
  have htargetNe : (certificate.prechargedTailTarget : Real) ≠ 0 := by
    exact_mod_cast certificate.prechargedTailTarget_pos.ne'
  have hdivisorNe : (divisor : Real) ≠ 0 := by
    exact_mod_cast
      (centralAnchorDivisor_pos certificate.isCofactorChoice).ne'
  rw [extendedPrechargedTailLogTarget_eq F hn,
    extendedCentralAnchorDivisorLog_eq F hn,
    bankPaperCanonicalCentralTailLogTarget]
  change
    Real.log (certificate.prechargedTailTarget : Real) +
        Real.log (divisor : Real) =
      Real.log (centralTailProduct n (upperTailLength c n) : Real)
  rw [← Real.log_mul htargetNe hdivisorNe, ← Nat.cast_mul, htarget]

/-- The complementary finite-prefix conventions make the same exact
identity valid at every natural-number index. -/
theorem extendedPrechargedTailLogTarget_add_extendedCentralAnchorDivisorLog
    {c : Real} {depth N : Nat}
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (n : Nat) :
    F.extendedPrechargedTailLogTarget n +
        F.extendedCentralAnchorDivisorLog n =
      bankPaperCanonicalCentralTailLogTarget c n := by
  by_cases hn : N <= n
  · exact F.extendedPrechargedTailLogTarget_add_anchorLog_of_tail hn
  · simp only [extendedPrechargedTailLogTarget,
      extendedCentralAnchorDivisorLog, dif_neg hn, add_zero]

end BankPaperCanonicalGuardedTailFamily

namespace GuardedCentralAnchorCertificate

/-- Exact divisibility bounds every guarded anchor valuation by the
corresponding literal upper-tail valuation. -/
theorem centralAnchorDivisor_factorization_le_upperTailValuation
    {c : Real} {depth n p : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    ((centralAnchorDivisor n (centralAnchorCutoff depth n)
        certificate.q).factorization p : Real) <=
      (upperTailValuation c n p : Real) := by
  have hdivisorPos :
      0 < centralAnchorDivisor n (centralAnchorCutoff depth n)
        certificate.q :=
    centralAnchorDivisor_pos certificate.isCofactorChoice
  have htailPos :
      0 < centralTailProduct n (upperTailLength c n) :=
    centralTailProduct_pos n (upperTailLength c n)
  have hfactorization :
      (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q).factorization p <=
        (centralTailProduct n
          (upperTailLength c n)).factorization p :=
    ((Nat.factorization_le_iff_dvd hdivisorPos.ne' htailPos.ne').mpr
      certificate.divisor_dvd_tail) p
  rw [upperTailValuation_eq_centralTailProduct_factorization]
  exact_mod_cast hfactorization

/-- Fixed-support expansion of the guarded anchor-divisor logarithm. -/
theorem centralAnchorDivisorLog_eq_sum_primesUpTo
    {c : Real} {depth n : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed) :
    Real.log
        (centralAnchorDivisor n (centralAnchorCutoff depth n)
          certificate.q : Real) =
      ∑ p ∈ primesUpTo (2 * depth + 1),
        ((centralAnchorDivisor n (centralAnchorCutoff depth n)
            certificate.q).factorization p : Real) *
          Real.log (p : Real) := by
  classical
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  have hdivisorPos : 0 < divisor := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  rw [Real.log_nat_eq_sum_factorization]
  change
    (∑ p ∈ divisor.factorization.support,
        (divisor.factorization p : Real) * Real.log (p : Real)) =
      ∑ p ∈ primesUpTo (2 * depth + 1),
        (divisor.factorization p : Real) * Real.log (p : Real)
  apply Finset.sum_subset
  · intro p hpSupport
    have hpNonzero : divisor.factorization p ≠ 0 :=
      Finsupp.mem_support_iff.mp hpSupport
    have hpPrime : p.Prime :=
      Not.imp_symm divisor.factorization_eq_zero_of_not_prime hpNonzero
    have hpDvd : p ∣ divisor := by
      apply (hpPrime.dvd_iff_one_le_factorization hdivisorPos.ne').mpr
      exact Nat.one_le_iff_ne_zero.mpr hpNonzero
    exact certificate.divisor_prime_support p hpPrime
      (by simpa only [divisor] using hpDvd)
  · intro p _hpPrefix hpNotSupport
    have hpZero : divisor.factorization p = 0 :=
      Finsupp.notMem_support_iff.mp hpNotSupport
    simp only [hpZero, Nat.cast_zero, zero_mul]

end GuardedCentralAnchorCertificate

/-! ## The fixed-prime asymptotic bound -/

/-- The fixed-prime valuation limits give one simultaneous upper bound on
the complete anchor support. -/
theorem eventually_upperTailValuation_le_add_one_mul_secondOrderScale_on_primesUpTo
    {c : Real} (hc : 0 < c) (depth : Nat) :
    ∀ᶠ n : Nat in atTop, ∀ p ∈ primesUpTo (2 * depth + 1),
      (upperTailValuation c n p : Real) <=
        (c / ((p - 1 : Nat) : Real) + 1) *
          secondOrderScale n := by
  have hratio :
      ∀ᶠ n : Nat in atTop, ∀ p ∈ primesUpTo (2 * depth + 1),
        (upperTailValuation c n p : Real) / secondOrderScale n <=
          c / ((p - 1 : Nat) : Real) + 1 := by
    rw [Finset.eventually_all]
    intro p hp
    have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
    exact
      (upperTailValuation_normalized_tendsto hc hpPrime).eventually
        (eventually_le_nhds (by linarith))
  filter_upwards [hratio, eventually_secondOrderScale_pos] with
      n hn hscale
  intro p hp
  exact (div_le_iff₀ hscale).mp (hn p hp)

/-- A convenient explicit nonnegative constant for the fixed anchor-log
bound. -/
def bankPaperCanonicalAnchorLogBigOConstant
    (c : Real) (depth : Nat) : Real :=
  ∑ p ∈ primesUpTo (2 * depth + 1),
    (c / ((p - 1 : Nat) : Real) + 1) * Real.log (p : Real)

theorem bankPaperCanonicalAnchorLogBigOConstant_nonneg
    {c : Real} (hc : 0 < c) (depth : Nat) :
    0 <= bankPaperCanonicalAnchorLogBigOConstant c depth := by
  apply Finset.sum_nonneg
  intro p hp
  have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
  have hpPredPos : (0 : Real) < ((p - 1 : Nat) : Real) := by
    exact_mod_cast Nat.sub_pos_of_lt hpPrime.one_lt
  have hpLogNonneg : 0 <= Real.log (p : Real) :=
    Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
  exact mul_nonneg (add_nonneg (div_nonneg hc.le hpPredPos.le)
    (by norm_num)) hpLogNonneg

namespace BankPaperCanonicalGuardedTailFamily

/-- Uniformly over every coherent guarded tail family, the removed
central-anchor logarithm is `O(n / log n)`.  The proof uses fixed prime
support and fixed-prime valuation asymptotics, rather than the much too
coarse numerical inequality `divisor <= tail`. -/
theorem extendedCentralAnchorDivisorLog_isBigO_secondOrderScale
    {c : Real} {depth N : Nat} (hc : 0 < c)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    F.extendedCentralAnchorDivisorLog =O[atTop] secondOrderScale := by
  apply IsBigO.of_bound (bankPaperCanonicalAnchorLogBigOConstant c depth)
  filter_upwards [eventually_ge_atTop N,
      eventually_upperTailValuation_le_add_one_mul_secondOrderScale_on_primesUpTo
        hc depth,
      eventually_secondOrderScale_pos] with n hnTail hvaluation hscale
  let certificate := F.certificate n hnTail
  let divisor :=
    centralAnchorDivisor n (centralAnchorCutoff depth n) certificate.q
  have hdivisorPos : 0 < divisor := by
    exact centralAnchorDivisor_pos certificate.isCofactorChoice
  have hlogNonneg : 0 <= Real.log (divisor : Real) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hdivisorPos.ne'
  rw [extendedCentralAnchorDivisorLog_eq F hnTail,
    Real.norm_eq_abs, abs_of_nonneg hlogNonneg,
    Real.norm_eq_abs, abs_of_pos hscale,
    certificate.centralAnchorDivisorLog_eq_sum_primesUpTo]
  calc
    (∑ p ∈ primesUpTo (2 * depth + 1),
        (divisor.factorization p : Real) * Real.log (p : Real)) <=
      ∑ p ∈ primesUpTo (2 * depth + 1),
        ((c / ((p - 1 : Nat) : Real) + 1) * secondOrderScale n) *
          Real.log (p : Real) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime : p.Prime := (mem_primesUpTo.mp hp).1
        have hpLogNonneg : 0 <= Real.log (p : Real) :=
          Real.log_nonneg (by exact_mod_cast hpPrime.one_le)
        apply mul_le_mul_of_nonneg_right _ hpLogNonneg
        exact
          (certificate.centralAnchorDivisor_factorization_le_upperTailValuation
            (p := p)).trans (hvaluation p hp)
    _ = ∑ p ∈ primesUpTo (2 * depth + 1),
        ((c / ((p - 1 : Nat) : Real) + 1) *
          Real.log (p : Real)) * secondOrderScale n := by
        apply Finset.sum_congr rfl
        intro p _hp
        ring
    _ = bankPaperCanonicalAnchorLogBigOConstant c depth *
          secondOrderScale n := by
        rw [bankPaperCanonicalAnchorLogBigOConstant, Finset.sum_mul]

/-- The paper's precharged logarithmic target retains the same centered
`O(n / log n)` estimate as the complete central tail. -/
theorem extendedPrechargedTailLogTarget_sub_height_mul_L_isBigO
    {c : Real} {depth N : Nat} (hc : 0 < c)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    (fun n => F.extendedPrechargedTailLogTarget n -
      bankPaperCanonicalUpperTailHeight c n * L n) =O[atTop]
        secondOrderScale := by
  have hcentral :=
    bankPaperCanonicalCentralTailLogTarget_sub_height_mul_L_isBigO hc
  have hanchor :=
    F.extendedCentralAnchorDivisorLog_isBigO_secondOrderScale hc
  exact (hcentral.sub hanchor).congr_left fun n => by
    rw [← F.extendedPrechargedTailLogTarget_add_extendedCentralAnchorDivisorLog
      n]
    ring

end BankPaperCanonicalGuardedTailFamily

/-! ## Adapter for an already-constructed Section 8 ledger -/

/-- Replace the old complete-central-tail logarithm in an existing Section 8
analytic ledger by the paper's precharged logarithm.  The active-mass field
is unchanged; the height defect changes by exactly the anchor-divisor log,
which is already `O(secondOrderScale)`. -/
theorem bankPaperCanonicalSectionEightAnalyticLedger_precharged_of_centralTail
    {c : Real} {depth N : Nat} (hc : 0 < c)
    (F : BankPaperCanonicalGuardedTailFamily c depth N)
    (rawBase qTilde Lambda0 mFrozen : Nat -> Real)
    (Hcentral : BankPaperCanonicalSectionEightAnalyticLedger
      rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        (bankPaperCanonicalCentralTailLogTarget c)
        Lambda0 mFrozen qTilde)) :
    BankPaperCanonicalSectionEightAnalyticLedger
      rawBase qTilde
      (bankPaperCanonicalSmoothA0Family
        F.extendedPrechargedTailLogTarget
        Lambda0 mFrozen qTilde) := by
  constructor
  · exact Hcentral.1
  · have hanchor :=
      F.extendedCentralAnchorDivisorLog_isBigO_secondOrderScale hc
    have hheight := Hcentral.2.sub hanchor
    exact hheight.congr_left fun n => by
      unfold bankPaperCanonicalSmoothA0Family
      unfold bankPaperCanonicalSmoothFrozenHeightDefect
      rw [← F.extendedPrechargedTailLogTarget_add_extendedCentralAnchorDivisorLog
        n]
      ring

end

end Erdos390.WholePaper
