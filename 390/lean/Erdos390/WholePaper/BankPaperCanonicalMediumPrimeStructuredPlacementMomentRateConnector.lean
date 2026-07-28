import Erdos390.WholePaper.BankPaperCanonicalSelectorDeficitPaperRateClosureConnector
import Erdos390.Full.PaperBridgePhysicalValuationRow

/-!
# Medium-prime rate for the structured two-zero-cell placement moment

The literal two-zero-cell rebalance spreads each requested mass uniformly
inside one guarded structured cell.  Consequently its medium-prime moment is
controlled by the valuation mean of the *uniform guarded-cell law*.  It is not
unconditionally controlled for arbitrary `minusMass` and `plusMass`, and the
uniform law must not be silently replaced by the generally tilted
`cellMediumLaw`.

This connector first proves the exact finite expectation identity.  It then
combines:

* a reciprocal valuation-mean bound in each of the two zero-head cells; and
* an `O(secondOrderScale / L)` bound for the sum of the absolute mass changes.

The resulting estimate is exactly on the
`secondOrderScale / (p * L)` scale required by the third conjunct of
`BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.Scale

noncomputable section

namespace BankPaperRealization

/-! ## Exact uniform-cell expectation algebra -/

/-- A uniform mass increment in one structured cell has valuation moment
equal to the requested mass times the valuation expectation under the
literal uniform guarded-cell probability. -/
theorem
    sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band) (cell : Cell Head)
    (mass : Real) (p : Nat) :
    (∑ m : B.sampleData.Sample,
        bankPaperCanonicalUniformCellIncrement
            B.sampleData cell mass m *
          valuation p (B.sampleData.value m)) =
      mass * (B.guardedCellProbability cell).expect
        (fun m ↦ valuation p (m : Nat)) := by
  classical
  rw [Fintype.sum_sigma, Finset.sum_eq_single cell]
  · simp only [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, if_true, StructuredSampleData.value,
      Fintype.card_coe]
    unfold BridgeData.guardedCellProbability
    rw [Erdos390.Full.FiniteProbability.uniformOnFinset_expect_eq]
    rw [← Finset.mul_sum]
    ring
  · intro other _hother hne
    apply Finset.sum_eq_zero
    intro m _hm
    simp [bankPaperCanonicalUniformCellIncrement,
      StructuredSampleData.cellOf, hne]
  · intro hnot
    exact (hnot (Finset.mem_univ cell)).elim

/-- Exact medium-prime placement identity for the actual global corrected
source.  Support of every structured value in the guarded smooth row is the
only geometric premise needed to reindex the ambient sum back to tagged
samples. -/
theorem
    bankPaperCanonicalGlobalCorrectedStructuredPlacementValuationMoment_twoZeroHeadCells_eq
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass : Real)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (p : Nat) :
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p =
      minusMass *
          (B.guardedCellProbability (none, .minus)).expect
            (fun m ↦ valuation p (m : Nat)) +
        plusMass *
          (B.guardedCellProbability (none, .plus)).expect
            (fun m ↦ valuation p (m : Nat)) := by
  classical
  have houtsideActive : forall a,
      a ∈ bankPaperCanonicalStructuredActiveValues B.sampleData ->
      a ∉ R.roughCanonicalGuardedBroadCorrectionPool certificate
        deltaStar B.sampleData.W K 1 ->
      bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
          B R certificate deltaStar alpha beta oldSeed a =
        bankPaperCanonicalActiveSeedAmbientWeight
          B.sampleData oldSeed a := by
    intro a haActive _haPool
    exact
      bankPaperCanonicalGlobalCorrectedOutsideSelector_eq_ambient_of_mem_smoothRow
        B R certificate oldSeed (hactiveSmooth haActive)
  have hdiff (a : Nat) :
      bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
            B R certificate deltaStar betaProt
            (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
              B R certificate deltaStar betaProt alpha beta oldSeed)
            (bankPaperCanonicalTwoZeroHeadCellRebalance
              B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
            B R certificate deltaStar betaProt alpha beta oldSeed a =
        bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a := by
    simpa only [bankPaperCanonicalGlobalCorrectedSourceSelector] using
      (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector_twoZeroHeadCells_sub_source_of_active
        (K := K) B R certificate deltaStar betaProt oldSeed
          (bankPaperCanonicalGlobalCorrectedOutsideSelector (K := K)
            B R certificate deltaStar alpha beta oldSeed)
          houtsideActive minusMass plusMass a)
  have hvalues (m : B.sampleData.Sample) :
      B.sampleData.value m ∈
        R.roughCanonicalGuardedRow certificate deltaStar K 1 :=
    hactiveSmooth
      (mem_bankPaperCanonicalStructuredActiveValues.mpr ⟨m, rfl⟩)
  unfold
    bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
  calc
    (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalGuardedStructuredAdditivePlacementSelector (K := K)
              B R certificate deltaStar betaProt
              (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
                B R certificate deltaStar betaProt alpha beta oldSeed)
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
            B R certificate deltaStar betaProt alpha beta oldSeed a) *
          (a.factorization p : Real)) =
      ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
        (bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass) a -
          bankPaperCanonicalActiveSeedAmbientWeight
            B.sampleData oldSeed a) * valuation p a := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [hdiff a]
        rfl
    _ =
        (∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight B.sampleData
                (bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass) a *
              valuation p a) -
          ∑ a ∈ R.roughCanonicalGuardedRow certificate deltaStar K 1,
            bankPaperCanonicalActiveSeedAmbientWeight
              B.sampleData oldSeed a * valuation p a := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro a _ha
        ring
    _ =
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass m *
              valuation p (B.sampleData.value m)) -
          ∑ m : B.sampleData.Sample,
            oldSeed m * valuation p (B.sampleData.value m) := by
        rw [
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData
              (bankPaperCanonicalTwoZeroHeadCellRebalance
                B.sampleData oldSeed minusMass plusMass)
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues p,
          sum_bankPaperCanonicalActiveSeedAmbientWeight_mul_valuation_eq_tagged
            B.sampleData oldSeed
              (R.roughCanonicalGuardedRow certificate deltaStar K 1)
              hvalues p]
    _ =
        (∑ m : B.sampleData.Sample,
            bankPaperCanonicalUniformCellIncrement
                B.sampleData (none, .minus) minusMass m *
              valuation p (B.sampleData.value m)) +
          ∑ m : B.sampleData.Sample,
            bankPaperCanonicalUniformCellIncrement
                B.sampleData (none, .plus) plusMass m *
              valuation p (B.sampleData.value m) := by
        rw [show
          (∑ m : B.sampleData.Sample,
              bankPaperCanonicalTwoZeroHeadCellRebalance
                  B.sampleData oldSeed minusMass plusMass m *
                valuation p (B.sampleData.value m)) =
            (∑ m : B.sampleData.Sample,
                oldSeed m * valuation p (B.sampleData.value m)) +
              (∑ m : B.sampleData.Sample,
                bankPaperCanonicalUniformCellIncrement
                    B.sampleData (none, .minus) minusMass m *
                  valuation p (B.sampleData.value m)) +
              ∑ m : B.sampleData.Sample,
                bankPaperCanonicalUniformCellIncrement
                    B.sampleData (none, .plus) plusMass m *
                  valuation p (B.sampleData.value m) by
            rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro m _hm
            unfold bankPaperCanonicalTwoZeroHeadCellRebalance
            ring]
        ring
    _ =
      minusMass *
          (B.guardedCellProbability (none, .minus)).expect
            (fun m ↦ valuation p (m : Nat)) +
        plusMass *
          (B.guardedCellProbability (none, .plus)).expect
            (fun m ↦ valuation p (m : Nat)) := by
        rw [
          sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
            B (none, .minus) minusMass p,
          sum_bankPaperCanonicalUniformCellIncrement_mul_valuation_eq_mass_mul_guardedCellProbability_expect
            B (none, .plus) plusMass p]

/-! ## Quantitative paper-rate closure -/

/-- The exact identity plus reciprocal uniform-cell valuation means and an
absolute two-cell mass budget give the required medium-prime paper rate.
There is deliberately no unconditional assertion for arbitrary masses. -/
theorem
    abs_bankPaperCanonicalGlobalCorrectedStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth K : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt alpha beta : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass Aval Cmass : Real) (p : Nat)
    (hp : p.Prime)
    (hAval : 0 <= Aval) (_hCmass : 0 <= Cmass)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar K 1)
    (hmean : forall sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) <= Aval / (p : Real))
    (hmass :
      |minusMass| + |plusMass| <=
        Cmass * secondOrderScale B.sampleData.n / B.L) :
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K) B R certificate deltaStar betaProt
        (bankPaperCanonicalGlobalCorrectedSourceSelector (K := K)
          B R certificate deltaStar betaProt alpha beta oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p) <=
      Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := by
  let meanMinus : Real :=
    (B.guardedCellProbability (none, .minus)).expect
      (fun m ↦ valuation p (m : Nat))
  let meanPlus : Real :=
    (B.guardedCellProbability (none, .plus)).expect
      (fun m ↦ valuation p (m : Nat))
  have hmeanMinusNonneg : 0 <= meanMinus := by
    exact
      (B.guardedCellProbability (none, .minus)).expect_nonneg _
        (fun m ↦ valuation_nonneg p (m : Nat))
  have hmeanPlusNonneg : 0 <= meanPlus := by
    exact
      (B.guardedCellProbability (none, .plus)).expect_nonneg _
        (fun m ↦ valuation_nonneg p (m : Nat))
  have hmeanMinus : meanMinus <= Aval / (p : Real) :=
    hmean .minus
  have hmeanPlus : meanPlus <= Aval / (p : Real) :=
    hmean .plus
  have hpReal : 0 < (p : Real) := by
    exact_mod_cast hp.pos
  have hrateNonneg : 0 <= Aval / (p : Real) :=
    div_nonneg hAval hpReal.le
  rw [
    bankPaperCanonicalGlobalCorrectedStructuredPlacementValuationMoment_twoZeroHeadCells_eq
      B R certificate deltaStar betaProt alpha beta oldSeed
        minusMass plusMass hactiveSmooth p]
  change abs (minusMass * meanMinus + plusMass * meanPlus) <= _
  calc
    abs (minusMass * meanMinus + plusMass * meanPlus) <=
        abs (minusMass * meanMinus) + abs (plusMass * meanPlus) :=
      abs_add_le _ _
    _ = |minusMass| * meanMinus + |plusMass| * meanPlus := by
      rw [abs_mul, abs_mul, abs_of_nonneg hmeanMinusNonneg,
        abs_of_nonneg hmeanPlusNonneg]
    _ <= |minusMass| * (Aval / (p : Real)) +
        |plusMass| * (Aval / (p : Real)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hmeanMinus (abs_nonneg minusMass))
        (mul_le_mul_of_nonneg_left hmeanPlus (abs_nonneg plusMass))
    _ = (|minusMass| + |plusMass|) * (Aval / (p : Real)) := by
      ring
    _ <= (Cmass * secondOrderScale B.sampleData.n / B.L) *
        (Aval / (p : Real)) :=
      mul_le_mul_of_nonneg_right hmass hrateNonneg
    _ = Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := by
      field_simp [hpReal.ne', B.L_pos.ne']

/-- Specialization of the preceding theorem to the balanced Post-Hfit global
source used by the selector-deficit closure. -/
theorem
    abs_bankPaperCanonicalPostHfitStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass Aval Cmass : Real) (p : Nat)
    (hp : p.Prime)
    (hAval : 0 <= Aval) (hCmass : 0 <= Cmass)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hmean : forall sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) <= Aval / (p : Real))
    (hmass :
      |minusMass| + |plusMass| <=
        Cmass * secondOrderScale B.sampleData.n / B.L) :
    abs
      (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
        (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitGlobalSourceSelector
          B K0 R certificate deltaStar betaProt betaAct oldSeed)
        (bankPaperCanonicalTwoZeroHeadCellRebalance
          B.sampleData oldSeed minusMass plusMass) p) <=
      Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := by
  simpa only [bankPaperCanonicalPostHfitGlobalSourceSelector] using
    (abs_bankPaperCanonicalGlobalCorrectedStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
      (K := K0 + 1) B R certificate deltaStar betaProt
        (bankPaperCanonicalPostHfitBalancedAlpha
          B c K0 betaProt betaAct)
        (betaProt + betaAct) oldSeed minusMass plusMass Aval Cmass p hp
        hAval hCmass hactiveSmooth hmean hmass)

/-- Constructor for the complete implementation-rate package once the two
non-placement defects are already bounded.  The placement constant is
exactly `Cmass * Aval`. -/
theorem
    bankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs_of_twoZeroHeadCellMean
    {P : Finset Nat} {Band : Type*}
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData (PaperHeadSimplex.Tag P) Band)
    {c : Real} {depth : Nat} (K0 : Nat)
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (deltaStar betaProt betaAct : Real)
    (oldSeed : B.sampleData.Sample -> Real)
    (minusMass plusMass Aval Cmass Csource CguardedRaw : Real) (p : Nat)
    (hp : p.Prime)
    (hAval : 0 <= Aval) (hCmass : 0 <= Cmass)
    (hactiveSmooth :
      bankPaperCanonicalStructuredActiveValues B.sampleData ⊆
        R.roughCanonicalGuardedRow certificate deltaStar (K0 + 1) 1)
    (hmean : forall sigma : PhysicalSign,
      (B.guardedCellProbability (none, sigma)).expect
          (fun m ↦ valuation p (m : Nat)) <= Aval / (p : Real))
    (hmass :
      |minusMass| + |plusMass| <=
        Cmass * secondOrderScale B.sampleData.n / B.L)
    (hsource :
      abs
        (roughCanonicalPostHfitGlobalSourceToGuardedCorrectionValuationDefect
          B K0 R certificate deltaStar betaProt betaAct oldSeed p) <=
        Csource *
          (secondOrderScale B.sampleData.n / ((p : Real) * B.L)))
    (hguardedRaw :
      abs
        (R.roughCanonicalAggregateGuardedRawCorrectionValuationDefect
          certificate deltaStar B.sampleData.W (K0 + 1)
          (bankPaperCanonicalPostHfitBalancedAlpha
            B c K0 betaProt betaAct)
          (betaProt + betaAct) B.L p) <=
        CguardedRaw *
          (secondOrderScale B.sampleData.n / ((p : Real) * B.L))) :
    BankPaperCanonicalPostHfitMediumPrimeImplementationRateInputs
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass p
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L))
        Csource CguardedRaw (Cmass * Aval) := by
  refine ⟨hsource, hguardedRaw, ?_⟩
  have hplacement :=
    abs_bankPaperCanonicalPostHfitStructuredPlacementValuationMoment_twoZeroHeadCells_le_paperRate
      B K0 R certificate deltaStar betaProt betaAct oldSeed
        minusMass plusMass Aval Cmass p hp hAval hCmass
        hactiveSmooth hmean hmass
  calc
    abs
        (bankPaperCanonicalGuardedStructuredAdditivePlacementValuationMoment
          (K := K0 + 1) B R certificate deltaStar betaProt
          (bankPaperCanonicalPostHfitGlobalSourceSelector
            B K0 R certificate deltaStar betaProt betaAct oldSeed)
          (bankPaperCanonicalTwoZeroHeadCellRebalance
            B.sampleData oldSeed minusMass plusMass) p) <=
      Cmass * Aval * secondOrderScale B.sampleData.n /
        ((p : Real) * B.L) := hplacement
    _ = (Cmass * Aval) *
        (secondOrderScale B.sampleData.n / ((p : Real) * B.L)) := by
      ring

end BankPaperRealization

end

end Erdos390.WholePaper
