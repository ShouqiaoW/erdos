import Erdos390.WholePaper.BankPaperPrechargedTailTarget

/-!
# The residual selector target after all base charges

The guarded central anchors are charged before `prechargedTailTarget` is
formed.  Fractional selection starts only after an independently fixed
factor set and the literal state-zero exactification bank have also been
charged.  This file names that second quotient and records the exact
division-free and valuation interfaces used by the post-tangent
certificate.
-/

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel

noncomputable section

namespace BankPaperRealization

/-- The complete factor product already present before fractional selector
weights are introduced: the caller's fixed factors and the actual
state-zero exactification bank. -/
def selectorTailCharge
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ) : ℕ :=
  fixed.prod id * (baseBankFactors R.exactificationState).prod id

/-- The generic exactification notation for the selector charge is exactly
the concrete precharged bank product. -/
theorem selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ) :
    R.selectorTailCharge fixed =
      fixed.prod id * R.prechargeBaseStateProduct := by
  rw [selectorTailCharge,
    R.baseExactificationBank_prod_eq_prechargeBaseStateProduct]

/-- Positivity of the selector charge follows from positivity of the
caller's fixed factors and interval positivity of every actual precharged
bank factor. -/
theorem selectorTailCharge_pos
    {n M : ℕ} (R : BankPaperRealization n M)
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a) :
    0 < R.selectorTailCharge fixed := by
  rw [R.selectorTailCharge_eq_fixed_mul_prechargeBaseStateProduct]
  apply Nat.mul_pos
  · exact Finset.prod_pos fun a ha ↦ by
      simpa only [id_eq] using hfixedPositive a ha
  · rw [prechargeBaseStateProduct]
    apply Finset.prod_pos
    intro factor hfactor
    have hinterval := R.prechargeBaseState_subset_factorInterval hfactor
    exact Nat.zero_lt_of_lt (Finset.mem_Ioc.mp hinterval).1

end BankPaperRealization

namespace GuardedCentralAnchorCertificate

/-- The natural-number product left for fractional selection after the
central anchors, fixed factors, and actual base exactification bank have all
been charged. -/
def selectorTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ) : ℕ :=
  certificate.prechargedTailTarget / R.selectorTailCharge fixed

/-- A positive divisor of the positive precharged tail leaves a positive
selector target. -/
theorem selectorTailTarget_pos
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    0 < certificate.selectorTailTarget R fixed := by
  apply Nat.div_pos
  · exact Nat.le_of_dvd certificate.prechargedTailTarget_pos hchargeDvd
  · exact R.selectorTailCharge_pos fixed hfixedPositive

/-- Division-free recovery of the precharged tail from the residual
selector target and its complete base charge. -/
theorem selectorTailTarget_mul_selectorTailCharge
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    certificate.selectorTailTarget R fixed *
        R.selectorTailCharge fixed =
      certificate.prechargedTailTarget := by
  rw [selectorTailTarget]
  exact Nat.div_mul_cancel hchargeDvd

/-- Exact coordinatewise valuation subtraction for the residual selector
target.  The subtraction is natural truncated subtraction, with
divisibility supplying the required coordinatewise inequality. -/
theorem selectorTailTarget_factorization_eq_sub
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget)
    (q : ℕ) :
    (certificate.selectorTailTarget R fixed).factorization q =
      certificate.prechargedTailTarget.factorization q -
        (R.selectorTailCharge fixed).factorization q := by
  rw [selectorTailTarget]
  simpa only [Finsupp.sub_apply] using
    congrArg (fun factorization : ℕ →₀ ℕ ↦ factorization q)
      (Nat.factorization_div hchargeDvd)

/-- The post-tangent valuation certificate can equivalently be stated with
all fixed and base-bank valuations removed from its target.  This is an
exact equivalence for an arbitrary real-valued selector ledger. -/
theorem valuationCertificate_iff_selectorTailTarget
    {c : ℝ} {depth n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (fixed : Finset ℕ) (weighted : ℕ → ℝ)
    (hfixedPositive : ∀ a ∈ fixed, 0 < a)
    (hchargeDvd : R.selectorTailCharge fixed ∣
      certificate.prechargedTailTarget) :
    (∀ q,
      ((fixed.prod id *
          (baseBankFactors R.exactificationState).prod id).factorization q :
            ℝ) + weighted q =
        (certificate.prechargedTailTarget.factorization q : ℝ)) ↔
      (∀ q, weighted q =
        ((certificate.selectorTailTarget R fixed).factorization q : ℝ)) := by
  have hchargePos : 0 < R.selectorTailCharge fixed :=
    R.selectorTailCharge_pos fixed hfixedPositive
  have hchargeLe : ∀ q,
      (R.selectorTailCharge fixed).factorization q ≤
        certificate.prechargedTailTarget.factorization q :=
    (Nat.factorization_le_iff_dvd hchargePos.ne'
      certificate.prechargedTailTarget_pos.ne').mpr hchargeDvd
  constructor
  · intro hcharged q
    have hchargedQ :
        ((R.selectorTailCharge fixed).factorization q : ℝ) + weighted q =
          (certificate.prechargedTailTarget.factorization q : ℝ) := by
      simpa only [BankPaperRealization.selectorTailCharge] using hcharged q
    rw [certificate.selectorTailTarget_factorization_eq_sub
      R fixed hchargeDvd q, Nat.cast_sub (hchargeLe q)]
    linarith
  · intro hresidual q
    have hresidualQ := hresidual q
    rw [certificate.selectorTailTarget_factorization_eq_sub
      R fixed hchargeDvd q, Nat.cast_sub (hchargeLe q)] at hresidualQ
    change ((R.selectorTailCharge fixed).factorization q : ℝ) +
      weighted q =
        (certificate.prechargedTailTarget.factorization q : ℝ)
    linarith

end GuardedCentralAnchorCertificate

end

end Erdos390.WholePaper
