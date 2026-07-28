import Erdos390.WholePaper.BankPaperCanonicalSectionNinePostHeightCoherentTargetConstructor
import Erdos390.WholePaper.BankPaperCanonicalSectionEightActiveMassScaleLowerConnector

/-!
# Source-first mass algebra for the post-height bridge

This module removes the apparent quantifier loop between the Section 8
analytic ledger and the Section 9 head exponent.

The guarded source mass has a positive paper-scale lower bound and an
`O(secondOrderScale)` upper bound before any frozen-log family or analytic
ledger is chosen.  We therefore choose the head exponent against one quarter
of that fixed lower coefficient.  Later, for any exact Section 8 ledger, the
nearest-integer initialization consumes at most one half of the coefficient
and the logarithmically smaller height adjustment consumes at most one more
half.  Thus the already chosen exponent is valid for the final post-height
mass as well.

All estimates are exposed as theorem conclusions.  No conclusion-bearing
record or analytic contract is introduced.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-! ## Fixed-coefficient lower-bound transfer -/

/-- If `q0` is eventually above the fixed coefficient `a` on the paper
scale and `d = o(secondOrderScale)`, then `q0 - d` is eventually above the
explicit coefficient `a / 2`.  Unlike the existential paper-scale wrapper,
this theorem retains the input coefficient in its conclusion. -/
theorem eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_isLittleO
    (q0 d : Nat → Real) {a : Real} (ha : 0 < a)
    (hq0 : ∀ᶠ n : Nat in atTop,
      a * secondOrderScale n ≤ q0 n)
    (hd : d =o[atTop] secondOrderScale) :
    ∀ᶠ n : Nat in atTop,
      (a / 2) * secondOrderScale n ≤ q0 n - d n := by
  have hdBound := hd.bound (half_pos ha)
  filter_upwards [hq0, hdBound, eventually_secondOrderScale_pos] with
      n hq0n hdn hscale
  have hdn' :
      |d n| ≤ (a / 2) * secondOrderScale n := by
    simpa only [Real.norm_eq_abs, abs_of_pos hscale] using hdn
  have hdle :
      d n ≤ (a / 2) * secondOrderScale n :=
    (le_abs_self (d n)).trans hdn'
  calc
    (a / 2) * secondOrderScale n =
        a * secondOrderScale n -
          (a / 2) * secondOrderScale n := by
      ring
    _ ≤ q0 n - (a / 2) * secondOrderScale n :=
      sub_le_sub_right hq0n _
    _ ≤ q0 n - d n :=
      sub_le_sub_left hdle _

/-- An `O(secondOrderScale / L)` change gives the same explicit half
coefficient, because that scale is little-o of `secondOrderScale`. -/
theorem eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_logScale_isBigO
    (q0 d : Nat → Real) {a : Real} (ha : 0 < a)
    (hq0 : ∀ᶠ n : Nat in atTop,
      a * secondOrderScale n ≤ q0 n)
    (hd : d =O[atTop]
      (fun n : Nat => secondOrderScale n / L n)) :
    ∀ᶠ n : Nat in atTop,
      (a / 2) * secondOrderScale n ≤ q0 n - d n := by
  exact
    eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_isLittleO
      q0 d ha hq0
        (hd.trans_isLittleO
          secondOrderScale_div_L_isLittleO_secondOrderScale)

/-! ## The fixed quarter retained by the final active mass -/

/-- Starting with an explicit lower coefficient for the guarded source
mass, the literal nearest-integer `q0` and the Section 8 integer height
adjustment leave the explicit coefficient `cSource / 4` in the final active
mass.

The coefficient and source lower bound may be selected before `logY`,
`Lambda0`, `mFrozen`, and the analytic ledger. -/
theorem
    eventually_bankPaperCanonicalSectionNinePostHeight_finalActiveMass_ge_quarter_sourceCoefficient
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
          mu logY Lambda0 mFrozen qTilde n := by
  let q0 : Nat → Real :=
    bankPaperCanonicalSmoothQ0Family mFrozen qTilde
  have hroundForward :
      (fun n => q0 n - qTilde n) =o[atTop]
        secondOrderScale := by
    simpa only [q0] using
      bankPaperCanonicalSmoothQ0Family_sub_qTilde_isLittleO
        mFrozen qTilde
  have hroundBackward :
      (fun n => qTilde n - q0 n) =o[atTop]
        secondOrderScale := by
    exact hroundForward.neg_left.congr_left (fun n => by ring)
  have hq0LowerRaw :=
    eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_isLittleO
      qTilde (fun n => qTilde n - q0 n)
        hcSource hsourceLower hroundBackward
  have hq0Lower :
      ∀ᶠ n : Nat in atTop,
        (cSource / 2) * secondOrderScale n ≤ q0 n := by
    filter_upwards [hq0LowerRaw] with n hn
    convert hn using 1
    all_goals ring
  let d : Nat → Real :=
    bankPaperCanonicalSmoothDRealFamily
      mu logY Lambda0 mFrozen qTilde
  have hd :
      d =O[atTop]
        (fun n : Nat => secondOrderScale n / L n) := by
    simpa only [d] using
      bankPaperCanonicalSectionEight_d_isBigO
        W K c betaAct hmu logY Lambda0 mFrozen qTilde Hledger
  have hfinalRaw :=
    eventually_bankPaperCanonical_fixedHalfScaleLower_sub_of_logScale_isBigO
      q0 d (half_pos hcSource) hq0Lower hd
  filter_upwards [hfinalRaw] with n hn
  change
    (cSource / 4) * secondOrderScale n ≤ q0 n - d n
  convert hn using 1
  all_goals ring

/-! ## Choosing the exponent before the ledger -/

/-- Before any frozen-log family or Section 8 analytic ledger is supplied,
choose:

* one explicit positive lower coefficient `cSource` for the guarded source
  mass;
* one positive upper coefficient `cUpper`;
* and one positive head exponent `E`, already large enough for the future
  final-mass coefficient `cSource / 4`.

The eventual source envelope and exponent inequality are stated literally
in the conclusion. -/
theorem
    exists_eventually_bankPaperCanonicalSectionNinePostHeight_preledgerSourceMassExponent
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
              cUpper * secondOrderScale n := by
  let qTilde : Nat → Real :=
    F.extendedGuardedSmoothBaseMass W K betaAct deltaStar
  have hsourceLower :
      BankPaperCanonicalActiveMassPaperScaleLower qTilde := by
    simpa only [qTilde] using
      bankPaperCanonicalExtendedGuardedSmoothBaseMass_paperScaleLower
        depth W K hc hbeta deltaStar F
  have hguard :
      (fun n =>
        bankPaperCanonicalRawSmoothBaseMass W n
              (upperTailLength c n) K betaAct -
            qTilde n) =o[atTop] secondOrderScale := by
    simpa only [qTilde] using
      bankPaperCanonicalRawSmoothBase_sub_extendedGuardedSmoothBase_isLittleO
        depth W K betaAct deltaStar F
  have hsourceUpper :
      qTilde =O[atTop] secondOrderScale :=
    bankPaperCanonicalPostGuardSmoothMass_isBigO
      (fun n => bankPaperCanonicalRawSmoothBaseMass W n
        (upperTailLength c n) K betaAct)
      qTilde
      (bankPaperCanonicalRawSmoothBaseMass_isBigO W K c betaAct)
      hguard
  rcases hsourceLower with
    ⟨cSource, hcSource, hsourceLowerEventually⟩
  obtain ⟨cUpper, hcUpper, hsourceUpperBound⟩ :=
    hsourceUpper.exists_pos
  obtain ⟨E, hE, hElarge⟩ :=
    exists_bankPaperCanonicalSectionNinePostHeight_headExponent_large
      (fun p : {p : Nat // p ∈ primesUpTo W} =>
        bankPaperCanonicalSectionNinePostHeightHeadUpperCoefficient c p.1)
      (cSource / 4) (by positivity)
  refine
    ⟨cSource, cUpper, E, hcSource, hcUpper, hE, hElarge, ?_⟩
  filter_upwards [hsourceLowerEventually, hsourceUpperBound.bound,
      eventually_secondOrderScale_pos] with
      n hlower hupper hscale
  refine ⟨?_, ?_⟩
  · simpa only [qTilde] using hlower
  · calc
      F.extendedGuardedSmoothBaseMass W K betaAct deltaStar n =
          qTilde n := rfl
      _ ≤ |qTilde n| := le_abs_self _
      _ = ‖qTilde n‖ := (Real.norm_eq_abs _).symm
      _ ≤ cUpper * ‖secondOrderScale n‖ := hupper
      _ = cUpper * secondOrderScale n := by
        rw [Real.norm_eq_abs, abs_of_pos hscale]

end

end Erdos390.WholePaper
