import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightSourceFirstMassAlgebra

/-!
# Statement audit for the source-first post-height mass algebra

The examples repeat the explicit fixed coefficients and, most importantly,
place the exponent before every later frozen-log family and analytic ledger.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

example
    (q0 d : Nat → Real) {a : Real} (ha : 0 < a)
    (hq0 : ∀ᶠ n : Nat in atTop,
      a * secondOrderScale n ≤ q0 n)
    (hd : d =o[atTop] secondOrderScale) :
    ∀ᶠ n : Nat in atTop,
      (a / 2) * secondOrderScale n ≤ q0 n - d n :=
  eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_isLittleO
    q0 d ha hq0 hd

example
    (W K : Nat) {c betaAct mu cSource : Real}
    (hmu : 0 < mu) (hcSource : 0 < cSource)
    (qTilde : Nat → Real)
    (hsourceLower : ∀ᶠ n : Nat in atTop,
      cSource * secondOrderScale n ≤ qTilde n)
    (logY Lambda0 mFrozen : Nat → Real)
    (Hledger : BankPaperCanonicalSectionEightAnalyticLedger
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalSmoothA0Family
        logY Lambda0 mFrozen qTilde)) :
    ∀ᶠ n : Nat in atTop,
      (cSource / 4) * secondOrderScale n ≤
        bankPaperCanonicalSmoothFinalActiveMassFamily
          mu logY Lambda0 mFrozen qTilde n :=
  eventually_bankPaperCanonicalSectionNinePostHeight_finalActiveMass_ge_quarter_sourceCoefficient
    W K hmu hcSource qTilde hsourceLower
      logY Lambda0 mFrozen Hledger

example
    {c betaAct : Real} {N : Nat}
    (depth W K : Nat) (hc : 0 < c) (hbeta : 0 < betaAct)
    (deltaStar : Real)
    (F : BankPaperCanonicalGuardedTailFamily c depth N) :
    ∃ cSource cUpper : Real, ∃ E : Nat,
      0 < cSource ∧
        0 < cUpper ∧
        0 < E ∧
        2 *
              (∑ p : {p : Nat // p ∈ primesUpTo W},
                bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient
                  c p.1) ≤
            (E : Real) * (cSource / 4) ∧
        ∀ᶠ n : Nat in atTop,
          cSource * secondOrderScale n ≤
              F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n ∧
            F.extendedGuardedSmoothBaseMass
                W K betaAct deltaStar n ≤
              cUpper * secondOrderScale n :=
  exists_eventually_bankPaperCanonicalSectionNinePostHeight_preledgerSourceMassExponent
    depth W K hc hbeta deltaStar F

#check eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_isLittleO
#check eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_logScale_isBigO
#check
  eventually_bankPaperCanonicalSectionNinePostHeight_finalActiveMass_ge_quarter_sourceCoefficient
#check
  exists_eventually_bankPaperCanonicalSectionNinePostHeight_preledgerSourceMassExponent

end

end Erdos390.WholePaper
