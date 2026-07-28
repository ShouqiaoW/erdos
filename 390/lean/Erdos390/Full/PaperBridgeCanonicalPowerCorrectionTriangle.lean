import Erdos390.Full.PaperBridgePhysicalPowerCorrectionRow
import Erdos390.Full.PaperBridgeCanonicalGuardPowerCorrection
import Erdos390.Full.PaperBridgeCanonicalRawLemma75
import Erdos390.Full.PaperBridgeCanonicalPhysicalPowerCorrectionEventually

/-!
# The terminal canonical prime-power correction triangle

This module joins the two independently proved finite comparisons used in
Lemma 8.4:

* the residual physical tilt compares the actual bridge law with the
  medium-only law; and
* literal guard deletion compares that same medium-only law with the raw
  unguarded canonical reference law.

The intermediate laws are definitionally equal and carry exactly the same
post-tilt component weights.  The triangle therefore retains all
between-component covariance terms and produces the literal weighted
`VV-II` row required by the full-versus-squarefree connector.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus GuardedUniformCell
open StructuredCells ValuationScoreDomination PrimeSums

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The intermediate law in the physical comparison is literally the
guarded medium law in the canonical guard comparison. -/
theorem physicalMediumReferenceLaw_eq_canonicalGuardedMediumReferenceLaw
    [Nonempty Head] (xi : B.ParamSpace) :
    B.physicalMediumReferenceLaw xi =
      B.canonicalGuardedMediumReferenceLaw xi := by
  rfl

/-- Algebraic weighted-row triangle through the literal medium reference
law.  This connector is useful when the two finite sides have already been
instantiated by their respective eventual constructor theorems. -/
theorem actual_powerCorrection_reference_weightedRow_le_of_two_sides
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {rhoPhysical rhoReference : ℝ}
    (hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1)| ≤
        rhoPhysical)
    (hreference : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤
        rhoReference) :
    ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤
        rhoPhysical + rhoReference := by
  intro p
  have hpoint (q : BandPrime B.sampleData.n B.sampleData.W) :
      |((B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1) -
        (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| ≤
      |((B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1) -
        ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.physicalMediumReferenceLaw xi).covII p.1 q.1)| +
      |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
        (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| := by
    let a := (B.actualValuationLaw xi).covVV p.1 q.1 -
      (B.actualValuationLaw xi).covII p.1 q.1
    let b := (B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
      (B.physicalMediumReferenceLaw xi).covII p.1 q.1
    let c := referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1
    change |a - c| ≤ |a - b| + |b - c|
    rw [show a - c = (a - b) + (b - c) by ring]
    exact abs_add_le _ _
  have hsum :
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| ≤
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) +
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| := by
    calc
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (|((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1)| +
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)|) :=
        Finset.sum_le_sum fun q hq ↦ hpoint q
      _ = _ := Finset.sum_add_distrib
  have hp0 : 0 ≤ (p.1 : ℝ) := by positivity
  calc
    (p.1 : ℝ) * ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| ≤
      (p.1 : ℝ) *
        ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) +
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)|) :=
      mul_le_mul_of_nonneg_left hsum hp0
    _ = (p.1 : ℝ) *
          (∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 q.1 -
                (B.actualValuationLaw xi).covII p.1 q.1) -
              ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
                (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) +
        (p.1 : ℝ) *
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
                (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
              (referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1)| := by
      ring
    _ ≤ rhoPhysical + rhoReference := add_le_add (hphysical p) (hreference p)

/-- Exact finite weighted-row triangle from the actual bridge law to the
raw unguarded canonical reference law.

Every hypothesis is a finite arithmetic or pointwise estimate used by one
of the two already-audited sides.  In particular, `hcanonical` is the sole
identification of abstract bridge data with the canonical guarded
constructor, and both comparisons retain the actual post-tilt component
weights. -/
theorem actual_powerCorrection_canonicalRaw_weightedRow_le
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) {Cprom Cbank : ℕ}
    (ledger : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ ledger.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W)
        P I ledger hsep hremaining)
    (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (rho : Cell Head → ℝ)
    {A Aphys Kphys Gphys Kscore Cenv : ℝ}
    (hA : 0 ≤ A) (hAphys0 : 0 ≤ Aphys)
    (hKphys0 : 0 ≤ Kphys) (hGphys : 0 ≤ Gphys)
    (hCenv : 0 ≤ Cenv) (hW : 1 < B.sampleData.W)
    (hrho : ∀ c, 0 < rho c)
    (hcard : ∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hphysicalSmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hGdom : ∀ c,
      Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c ≤ Gphys)
    (hscore : ∀ c : Cell Head,
      ∀ m : rawCell P I B.sampleData.n c,
        |valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore)
    (hsmallCensus : ∀ c : Cell Head,
      Real.exp (2 * Kscore) * (ledger.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (hdensity : ∀ c : Cell Head,
      PaperScaleMarkedCell.paperCellDensity
          (P c.1) (I.lower c.2) (I.upper c.2) *
          (B.sampleData.n : ℝ) / 2 ≤
        (rawCell P I B.sampleData.n c).card)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
        Cenv * Scale.L B.sampleData.n)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (p.1 : ℝ) *
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          ((B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
              (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covVV p.1 q.1 -
            (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
              (fun c ↦ (hremaining c).mono Finset.sdiff_subset)).covII p.1 q.1)| ≤
      physicalPowerCorrectionRowError
          (Aphys * Kphys / B.L) Gphys
            B.sampleData.n B.sampleData.W +
        guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
          (canonicalGuardPerturbationConstant P I Kscore)
          B.sampleData.n := by
  let rawReference := B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
    (fun c ↦ (hremaining c).mono Finset.sdiff_subset)
  let mediumReference := B.physicalMediumReferenceLaw xi
  have hphysical :=
    B.actual_powerCorrection_physicalMedium_weightedRow_le
      xi rho hA hAphys0 hKphys0 hGphys hW hrho hcard heta hAphys hKphys
        hphysicalSmall hGdom p
  have hguardRaw :=
    B.weighted_sum_abs_physicalMediumReference_powerCorrection_sub_canonicalRaw_le
      P I Cmax ledger hsep hremaining hcanonical xi hC_le hW hCenv
        hscore hsmallCensus hdensity hEnvelope p
  have hguard :
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((mediumReference).covVV p.1 q.1 -
              (mediumReference).covII p.1 q.1) -
            ((rawReference).covVV p.1 q.1 -
              (rawReference).covII p.1 q.1)| ≤
        guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
          (canonicalGuardPerturbationConstant P I Kscore)
          B.sampleData.n := by
    simpa only [mediumReference, rawReference,
      physicalMediumReferenceLaw_eq_canonicalGuardedMediumReferenceLaw] using
        hguardRaw
  have htriangle :
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          ((rawReference).covVV p.1 q.1 -
            (rawReference).covII p.1 q.1)| ≤
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          ((mediumReference).covVV p.1 q.1 -
            (mediumReference).covII p.1 q.1)|) +
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((mediumReference).covVV p.1 q.1 -
            (mediumReference).covII p.1 q.1) -
          ((rawReference).covVV p.1 q.1 -
            (rawReference).covII p.1 q.1)| := by
    calc
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (|((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((mediumReference).covVV p.1 q.1 -
              (mediumReference).covII p.1 q.1)| +
          |((mediumReference).covVV p.1 q.1 -
              (mediumReference).covII p.1 q.1) -
            ((rawReference).covVV p.1 q.1 -
              (rawReference).covII p.1 q.1)|) := by
        apply Finset.sum_le_sum
        intro q _hq
        let a := (B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1
        let b := (mediumReference).covVV p.1 q.1 -
          (mediumReference).covII p.1 q.1
        let c := (rawReference).covVV p.1 q.1 -
          (rawReference).covII p.1 q.1
        change |a - c| ≤ |a - b| + |b - c|
        rw [show a - c = (a - b) + (b - c) by ring]
        exact abs_add_le _ _
      _ = _ := Finset.sum_add_distrib
  have hp0 : 0 ≤ (p.1 : ℝ) := by positivity
  calc
    (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((rawReference).covVV p.1 q.1 -
              (rawReference).covII p.1 q.1)| ≤
      (p.1 : ℝ) *
        ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            ((mediumReference).covVV p.1 q.1 -
              (mediumReference).covII p.1 q.1)|) +
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((mediumReference).covVV p.1 q.1 -
              (mediumReference).covII p.1 q.1) -
            ((rawReference).covVV p.1 q.1 -
              (rawReference).covII p.1 q.1)|) :=
        mul_le_mul_of_nonneg_left htriangle hp0
    _ = (p.1 : ℝ) *
          (∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 q.1 -
                (B.actualValuationLaw xi).covII p.1 q.1) -
              ((mediumReference).covVV p.1 q.1 -
                (mediumReference).covII p.1 q.1)|) +
        (p.1 : ℝ) *
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((mediumReference).covVV p.1 q.1 -
                (mediumReference).covII p.1 q.1) -
              ((rawReference).covVV p.1 q.1 -
                (rawReference).covII p.1 q.1)| := by ring
    _ ≤ physicalPowerCorrectionRowError
          (Aphys * Kphys / B.L) Gphys
            B.sampleData.n B.sampleData.W +
        guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
          (canonicalGuardPerturbationConstant P I Kscore)
          B.sampleData.n := add_le_add hphysical hguard
    _ = _ := by rfl

/-- Terminal finite full-versus-squarefree estimate with the raw canonical
reference law.  Lemma 7.5 is supplied for that raw law, while the actual/raw
power-correction row is discharged by the exact two-stage triangle above. -/
theorem abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_canonicalRaw
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) {Cprom Cbank : ℕ}
    (ledger : Ledger B.sampleData.n Cprom Cbank)
    (hsep : physicalBound (I.upper .minus) B.sampleData.n <
      physicalBound (I.lower .plus) B.sampleData.n)
    (hremaining : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c \ ledger.guards).Nonempty)
    (hcanonical : B.sampleData =
      canonicalSampleData (W := B.sampleData.W)
        P I ledger hsep hremaining)
    (xi : B.ParamSpace)
    (hC_le : ∀ sigma, I.upper sigma ≤ Cmax)
    (rho : Cell Head → ℝ)
    {A Aphys Kphys Gphys Kscore Cenv Cpow epsilon75 : ℝ}
    (hA : 0 ≤ A) (hAphys0 : 0 ≤ Aphys)
    (hKphys0 : 0 ≤ Kphys) (hGphys : 0 ≤ Gphys)
    (hCenv : 0 ≤ Cenv) (hCpow : 0 ≤ Cpow)
    (hepsilon75 : 0 ≤ epsilon75)
    (hW : 1 < B.sampleData.W)
    (hrho : ∀ c, 0 < rho c)
    (hcard : ∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hphysicalSmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hGdom : ∀ c,
      Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c ≤ Gphys)
    (hscore : ∀ c : Cell Head,
      ∀ m : rawCell P I B.sampleData.n c,
        |valuationScore
          (primeBand B.sampleData.n B.sampleData.W)
          (B.effectiveNatCoefficient xi) B.L (m : ℕ)| ≤ Kscore)
    (hsmallCensus : ∀ c : Cell Head,
      Real.exp (2 * Kscore) * (ledger.guards.card : ℝ) /
        ((rawCell P I B.sampleData.n c).card : ℝ) ≤ (1 : ℝ) / 2)
    (hdensity : ∀ c : Cell Head,
      PaperScaleMarkedCell.paperCellDensity
          (P c.1) (I.lower c.2) (I.upper c.2) *
          (B.sampleData.n : ℝ) / 2 ≤
        (rawCell P I B.sampleData.n c).card)
    (hEnvelope : ∀ c : Cell Head,
      valuationEnvelope I B.sampleData.n B.sampleData.W c ≤
        Cenv * Scale.L B.sampleData.n)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds
      (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
        (fun c ↦ (hremaining c).mono Finset.sdiff_subset))
      B.sampleData.n B.sampleData.W Cpow epsilon75)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤
      3 * Cpow *
          (bandTReciprocalSum B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon75 *
          (bandTReciprocalSum B.sampleData.n B.sampleData.W /
              B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        (physicalPowerCorrectionRowError
            (Aphys * Kphys / B.L) Gphys
              B.sampleData.n B.sampleData.W +
          guardPowerCorrectionWeightedMajorant Cprom Cbank Cenv
            (canonicalGuardPerturbationConstant P I Kscore)
            B.sampleData.n) /
          B.partition.center i := by
  exact B.abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referencePowerCorrectionRow
    xi (B.canonicalRawMediumReferenceLaw P I Cmax xi hC_le
      (fun c ↦ (hremaining c).mono Finset.sdiff_subset))
    hCpow hepsilon75 hW h75
    (B.actual_powerCorrection_canonicalRaw_weightedRow_le
      P I Cmax ledger hsep hremaining hcanonical xi hC_le rho
      hA hAphys0 hKphys0 hGphys hCenv hW hrho hcard heta hAphys hKphys
      hphysicalSmall hGdom hscore hsmallCensus hdensity hEnvelope)
    q hq i

/-- Box-independent eventual terminal for the canonical raw reference.

This theorem automatically instantiates both non-algebraic reference inputs:
the literal Lemma 7.5 certificate for the raw unguarded mixture and the
canonical guard-deletion row.  The remaining hypotheses are exactly the
genuine finite inputs of the residual physical comparison (`rho`, the cell
cardinality lower bound, the physical coordinate/score box, and its divisor
fallback domination).  No `h75` or `hpowerRow` assumption remains. -/
theorem exists_boxIndependent_canonicalRaw_fullSharp_of_physicalInputs
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hupperOne : ∀ sigma, 1 ≤ I.upper sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, Ledger n Cprom Cbank) :
    ∃ Cpow : ℝ, 0 < Cpow ∧
      ∀ W : ℕ, 1 < W → (∀ h, (P h).modulus ≤ W) →
      ∀ Acoef : ℝ, 0 ≤ Acoef →
      ∃ epsilon75 : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon75 n) ∧
        Filter.Tendsto epsilon75 Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n : ℕ ↦ epsilon75 n * Real.log (Scale.L n))
          Filter.atTop (nhds 0) ∧
        ∃ N₀ : ℕ,
          ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
            (B : BridgeData Head Band) (xi : B.ParamSpace),
            N₀ ≤ B.sampleData.n →
            B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell P I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = canonicalSampleData (W := B.sampleData.W)
                  P I (ledger B.sampleData.n) hsep hremaining →
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              ∀ (rho : Cell Head → ℝ)
                {Aphys Kphys Gphys : ℝ},
                0 ≤ Aphys → 0 ≤ Kphys → 0 ≤ Gphys →
                (∀ c, 0 < rho c) →
                (∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
                  ((B.sampleData.cellFinset c).card : ℝ)) →
                |xi MomentCoord.physical| ≤ Aphys →
                (∀ c (m : B.sampleData.SampleAt c),
                  |B.physicalScore ⟨c, m⟩| ≤ Kphys) →
                8 * (Aphys * Kphys / B.L) ≤ 1 →
                (∀ c,
                  Real.exp (2 * ((Acoef / B.L) *
                    (Real.log (B.sampleData.hi c.2 : ℝ) /
                      Real.log (B.sampleData.W : ℝ)))) / rho c ≤ Gphys) →
                ∀ (q : Band → ℝ) (_hq : ∀ j, |q j| ≤ 1) (i : Band),
                  |PrimePowerSharpBandTransfer.fullSharpRow
                        (B.actualValuationLaw xi) B.partition q i -
                      SquarefreeSharpBandTransfer.squarefreeSharpRow
                        (B.actualValuationLaw xi) B.partition q i| ≤
                    3 * Cpow *
                        (bandTReciprocalSum
                          B.sampleData.n B.sampleData.W + 1) *
                          (1 / (B.sampleData.W : ℝ)) +
                      3 * epsilon75 B.sampleData.n *
                        (bandTReciprocalSum
                            B.sampleData.n B.sampleData.W /
                              B.partition.center i + 1) *
                          (1 / (B.sampleData.W : ℝ)) +
                      (physicalPowerCorrectionRowError
                          (Aphys * Kphys / B.L) Gphys
                            B.sampleData.n B.sampleData.W +
                        guardPowerCorrectionWeightedMajorant Cprom Cbank
                          (PaperStatisticNorm.valuationLogCoefficient Cmax W)
                          (canonicalGuardPerturbationConstant P I
                            (Acoef *
                              PaperStatisticNorm.valuationLogCoefficient
                                Cmax W))
                          B.sampleData.n) /
                        B.partition.center i := by
  obtain ⟨Cpow, hCpow, h75main⟩ :=
    exists_boxIndependent_canonicalRaw_primePower_transfer
      P I Cmax hupperMax
  refine ⟨Cpow, hCpow, ?_⟩
  intro W hW hmod Acoef hAcoef
  obtain ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
      N75, hN75⟩ := h75main W hW
        (fun h p hp ↦
          PaperPrimePowerAuxiliaryPrime.headPrime_le_cutoff_of_modulus_le
            (P h) (hmod h) p hp)
        Acoef hAcoef
  obtain ⟨Nguard, hNguard⟩ :=
    exists_eventually_canonicalGuardPowerCorrection_reference_bound
      P I Cmax hupperOne hupperMax Cprom Cbank ledger W hW Acoef hAcoef
  refine ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
    max N75 Nguard, ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta rho Aphys Kphys Gphys hAphys0 hKphys0 hGphys
    hrho hcard hAphys hKphys hphysicalSmall hGdom q hq i
  have hN75' : N75 ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNguard' : Nguard ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans hN
  let hS : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let referenceLaw :=
    B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax hS
  have h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds
      referenceLaw B.sampleData.n B.sampleData.W Cpow
        (epsilon75 B.sampleData.n) := by
    simpa only [referenceLaw, hS] using
      hN75 B xi hN75' hBW heta hS
  have hphysical : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 r.1 -
              (B.actualValuationLaw xi).covII p.1 r.1) -
            ((B.physicalMediumReferenceLaw xi).covVV p.1 r.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 r.1)| ≤
        physicalPowerCorrectionRowError
          (Aphys * Kphys / B.L) Gphys
            B.sampleData.n B.sampleData.W := by
    intro p
    exact B.actual_powerCorrection_physicalMedium_weightedRow_le
      xi rho hAcoef hAphys0 hKphys0 hGphys
      (by simpa only [hBW] using hW) hrho hcard heta hAphys hKphys
      hphysicalSmall hGdom p
  have hguardRaw := hNguard B xi hNguard' hBW hsep hremaining
    hcanonical heta
  have hguard : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 r.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 r.1) -
            (referenceLaw.covVV p.1 r.1 -
              referenceLaw.covII p.1 r.1)| ≤
        guardPowerCorrectionWeightedMajorant Cprom Cbank
          (PaperStatisticNorm.valuationLogCoefficient Cmax W)
          (canonicalGuardPerturbationConstant P I
            (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W))
          B.sampleData.n := by
    intro p
    simpa only [referenceLaw, hS,
      physicalMediumReferenceLaw_eq_canonicalGuardedMediumReferenceLaw] using
        hguardRaw p
  have hpowerRow :=
    B.actual_powerCorrection_reference_weightedRow_le_of_two_sides
      xi referenceLaw hphysical hguard
  exact B.abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referencePowerCorrectionRow
    xi referenceLaw hCpow.le (hepsilon0 B.sampleData.n)
    (by simpa only [hBW] using hW) h75 hpowerRow q hq i

/-- Fully discharged eventual prime-power terminal for the canonical bridge.

The only hypotheses after the uniform threshold are the exact canonical
constructor equality and the genuine effective/physical coefficient-box
bounds.  Raw Lemma 7.5, guard deletion, the residual physical row, and the
two sharp moving-low rates are all constructed internally. -/
theorem boxIndependent_canonicalRaw_fullSharp
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperMax : ∀ sigma, I.upper sigma ≤ Cmax)
    (Cprom Cbank : ℕ)
    (ledger : ∀ n, Ledger n Cprom Cbank) :
    0 < FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant ∧
      ∀ W : ℕ, 1 < W →
        (∀ h, ∀ p ∈ (P h).primes, p ≤ W) →
      ∀ Acoef : ℝ, 0 ≤ Acoef →
      ∀ Aphys : ℝ, 0 ≤ Aphys →
      ∃ epsilon75 : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon75 n) ∧
        Filter.Tendsto epsilon75 Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n : ℕ ↦ epsilon75 n * Real.log (Scale.L n))
          Filter.atTop (nhds 0) ∧
        Filter.Tendsto
          (fun n : ℕ ↦
            (physicalPowerCorrectionRowError
                (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
                (canonicalPhysicalPowerCorrectionConstant
                  P I Cmax W Acoef) n W +
              guardPowerCorrectionWeightedMajorant Cprom Cbank
                (PaperStatisticNorm.valuationLogCoefficient Cmax W)
                (canonicalGuardPerturbationConstant P I
                  (Acoef * PaperStatisticNorm.valuationLogCoefficient
                    Cmax W)) n) *
              Real.log (Scale.L n))
          Filter.atTop (nhds 0) ∧
        ∃ N₀ : ℕ,
          ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
            (B : BridgeData Head Band) (xi : B.ParamSpace),
            N₀ ≤ B.sampleData.n →
            B.sampleData.W = W →
            ∀ (hsep : physicalBound (I.upper .minus) B.sampleData.n <
                physicalBound (I.lower .plus) B.sampleData.n)
              (hremaining : ∀ c : Cell Head,
                (rawCell P I B.sampleData.n c \
                  (ledger B.sampleData.n).guards).Nonempty),
              B.sampleData = canonicalSampleData (W := B.sampleData.W)
                  P I (ledger B.sampleData.n) hsep hremaining →
              (∀ p : BandPrime B.sampleData.n B.sampleData.W,
                |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
              |xi MomentCoord.physical| ≤ Aphys →
              ∀ (q : Band → ℝ) (_hq : ∀ j, |q j| ≤ 1) (i : Band),
                |PrimePowerSharpBandTransfer.fullSharpRow
                      (B.actualValuationLaw xi) B.partition q i -
                    SquarefreeSharpBandTransfer.squarefreeSharpRow
                      (B.actualValuationLaw xi) B.partition q i| ≤
                  3 * FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant *
                      (bandTReciprocalSum
                        B.sampleData.n B.sampleData.W + 1) *
                        (1 / (B.sampleData.W : ℝ)) +
                    3 * epsilon75 B.sampleData.n *
                      (bandTReciprocalSum
                          B.sampleData.n B.sampleData.W /
                            B.partition.center i + 1) *
                        (1 / (B.sampleData.W : ℝ)) +
                    (physicalPowerCorrectionRowError
                        (canonicalPhysicalPowerCorrectionEpsilon
                          Aphys Cmax B.sampleData.n)
                        (canonicalPhysicalPowerCorrectionConstant
                          P I Cmax W Acoef)
                        B.sampleData.n B.sampleData.W +
                      guardPowerCorrectionWeightedMajorant Cprom Cbank
                        (PaperStatisticNorm.valuationLogCoefficient Cmax W)
                        (canonicalGuardPerturbationConstant P I
                          (Acoef *
                            PaperStatisticNorm.valuationLogCoefficient
                              Cmax W))
                        B.sampleData.n) /
                      B.partition.center i := by
  obtain ⟨hCpow, h75main⟩ :=
    boxIndependent_canonicalRaw_primePower_transfer
      P I Cmax hupperMax
  let Cpow : ℝ :=
    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
  refine ⟨hCpow, ?_⟩
  intro W hW hsupport Acoef hAcoef Aphys hAphys0
  obtain ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
      N75, hN75⟩ := h75main W hW hsupport Acoef hAcoef
  have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := fun sigma ↦
    (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
  obtain ⟨Nguard, hNguard⟩ :=
    exists_eventually_canonicalGuardPowerCorrection_reference_bound
      P I Cmax hupperOne hupperMax Cprom Cbank ledger W hW Acoef hAcoef
  have hphysicalMain :=
    exists_eventually_canonicalPhysical_powerCorrection_row
      P I Cmax hlowerOne hupperMax Cprom Cbank ledger W hW
        Acoef Aphys hAcoef hAphys0
  dsimp only at hphysicalMain
  obtain ⟨_hGphys, hphysicalRate, Nphysical, hNphysical⟩ := hphysicalMain
  have hCmax : 1 ≤ Cmax :=
    (hupperOne .minus).trans (hupperMax .minus)
  have hCenv : 0 ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax W :=
    PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hDguard : 0 ≤ canonicalGuardPerturbationConstant P I
      (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W) :=
    canonicalGuardPerturbationConstant_nonneg P I _
  have hguardRate :=
    tendsto_guardPowerCorrectionWeightedMajorant_mul_logL_zero
      Cprom Cbank hCenv hDguard
  have htotalRate : Filter.Tendsto
      (fun n : ℕ ↦
        (physicalPowerCorrectionRowError
            (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
            (canonicalPhysicalPowerCorrectionConstant
              P I Cmax W Acoef) n W +
          guardPowerCorrectionWeightedMajorant Cprom Cbank
            (PaperStatisticNorm.valuationLogCoefficient Cmax W)
            (canonicalGuardPerturbationConstant P I
              (Acoef * PaperStatisticNorm.valuationLogCoefficient
                Cmax W)) n) * Real.log (Scale.L n))
      Filter.atTop (nhds 0) := by
    simpa only [add_mul, zero_add] using hphysicalRate.add hguardRate
  refine ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
    htotalRate, max N75 (max Nguard Nphysical), ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta hphys q hq i
  have hN75' : N75 ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans hN
  have hNguard' : Nguard ≤ B.sampleData.n :=
    (Nat.le_max_left _ _).trans
      ((Nat.le_max_right N75 _).trans hN)
  have hNphysical' : Nphysical ≤ B.sampleData.n :=
    (Nat.le_max_right _ _).trans
      ((Nat.le_max_right N75 _).trans hN)
  let hS : ∀ c : Cell Head,
      (rawCell P I B.sampleData.n c).Nonempty :=
    fun c ↦ (hremaining c).mono Finset.sdiff_subset
  let referenceLaw :=
    B.canonicalRawMediumReferenceLaw P I Cmax xi hupperMax hS
  have h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds
      referenceLaw B.sampleData.n B.sampleData.W Cpow
        (epsilon75 B.sampleData.n) := by
    simpa only [referenceLaw, hS] using
      hN75 B xi hN75' hBW heta hS
  have hphysical := hNphysical B xi hNphysical' hBW hsep hremaining
    hcanonical heta hphys
  have hguardRaw := hNguard B xi hNguard' hBW hsep hremaining
    hcanonical heta
  have hguard : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 r.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 r.1) -
            (referenceLaw.covVV p.1 r.1 -
              referenceLaw.covII p.1 r.1)| ≤
        guardPowerCorrectionWeightedMajorant Cprom Cbank
          (PaperStatisticNorm.valuationLogCoefficient Cmax W)
          (canonicalGuardPerturbationConstant P I
            (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W))
          B.sampleData.n := by
    intro p
    simpa only [referenceLaw, hS,
      physicalMediumReferenceLaw_eq_canonicalGuardedMediumReferenceLaw] using
        hguardRaw p
  have hpowerRow :=
    B.actual_powerCorrection_reference_weightedRow_le_of_two_sides
      xi referenceLaw hphysical hguard
  exact B.abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referencePowerCorrectionRow
    xi referenceLaw hCpow.le (hepsilon0 B.sampleData.n)
    (by simpa only [hBW] using hW) h75 hpowerRow q hq i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
