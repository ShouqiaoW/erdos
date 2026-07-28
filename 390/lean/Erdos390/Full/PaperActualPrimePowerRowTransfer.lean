import Erdos390.Full.PaperBridgeCanonicalPowerCorrectionTriangle
import Erdos390.Full.PaperActualPrimePowerRelative

/-!
# Actual prime-power transfer from a reference row

The canonical raw Lemma 7.5 certificate is proved for an unguarded reference
law, whereas Lemma 8.6 uses the genuinely guarded and physically tilted law.
This file records the exact finite triangle needed to pass between them.

Only the weighted `VV-II` row is used.  This is deliberate: the compensated
slow coefficient contains the within-band deviation and therefore is not a
lift of a band vector.  A sharp band-operator estimate alone does not control
that coefficient.  The row below does, without postulating a full
`PrimePowerTransferBounds` package for the actual law.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75 PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- If a reference law satisfies Lemma 7.5 and the actual/reference
power-correction rows are small, then the actual `VV-II` row is small.  The
statement is on the literal prime subtype, so it can be used both in the
slow quadratic and in marked-prime estimates. -/
theorem actual_fullSquarefree_weightedRow_le_of_reference
    [Nonempty Head]
    {OmegaRef : Type*} [Fintype OmegaRef] {MRef : ℕ}
    (xi : B.ParamSpace)
    (referenceLaw : BoundedValuationLaw OmegaRef MRef)
    {Cpow epsilon rhoPower : ℝ}
    (h75 : PrimePowerTransferBounds referenceLaw
      B.sampleData.n B.sampleData.W Cpow epsilon)
    (hpower : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤ rhoPower) :
    ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1| ≤
        Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon + rhoPower := by
  intro p
  have href :
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1| ≤
        Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon := by
    have hrefNat := h75.row p.1 p.2
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W)
      (fun q ↦ |referenceLaw.covVV p.1 q -
        referenceLaw.covII p.1 q|)
    rw [← hattach] at hrefNat
    change (p.1 : ℝ) *
      (∑ q ∈ (primeBand B.sampleData.n B.sampleData.W).attach,
        |referenceLaw.covVV p.1 q.1 - referenceLaw.covII p.1 q.1|) ≤
      Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon at hrefNat
    simpa only using hrefNat
  have hpoint (q : BandPrime B.sampleData.n B.sampleData.W) :
      |(B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1| ≤
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          (referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1)| +
        |referenceLaw.covVV p.1 q.1 -
          referenceLaw.covII p.1 q.1| := by
    let a := (B.actualValuationLaw xi).covVV p.1 q.1 -
      (B.actualValuationLaw xi).covII p.1 q.1
    let b := referenceLaw.covVV p.1 q.1 -
      referenceLaw.covII p.1 q.1
    change |a| ≤ |a - b| + |b|
    calc
      |a| = |(a - b) + b| := by congr 1; ring
      _ ≤ |a - b| + |b| := abs_add_le (a - b : ℝ) b
  have hsum :
      ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1| ≤
        (∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)|) +
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1| := by
    calc
      _ ≤ ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          (|((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| +
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1|) :=
        Finset.sum_le_sum fun q _hq ↦ hpoint q
      _ = _ := Finset.sum_add_distrib
  have hp0 : 0 ≤ (p.1 : ℝ) := by positivity
  calc
    (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1| ≤
      (p.1 : ℝ) *
        ((∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.actualValuationLaw xi).covVV p.1 q.1 -
              (B.actualValuationLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)|) +
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |referenceLaw.covVV p.1 q.1 -
            referenceLaw.covII p.1 q.1|) :=
        mul_le_mul_of_nonneg_left hsum hp0
    _ = (p.1 : ℝ) *
          (∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |((B.actualValuationLaw xi).covVV p.1 q.1 -
                (B.actualValuationLaw xi).covII p.1 q.1) -
              (referenceLaw.covVV p.1 q.1 -
                referenceLaw.covII p.1 q.1)|) +
        (p.1 : ℝ) *
          ∑ q : BandPrime B.sampleData.n B.sampleData.W,
            |referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1| := by ring
    _ ≤ rhoPower +
        (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) :=
      add_le_add (hpower p) href
    _ = Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon +
        rhoPower := by ring

/-- Relative compensated slow-quadratic transfer from a literal actual-law
weighted row.  No other field of Lemma 7.5 is used. -/
theorem actual_primePower_relative_variance_bound_of_row
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w) (hR : 0 ≤ R)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R) :
    |(B.tiltedLaw xi).covariance
        (B.postBandPrimeScore q) (B.postBandPrimeScore q) -
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q)| ≤
      ((1 + C) * (7 + C * K)) * R * w ^ 2 := by
  have hthree :=
    B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2
  have hcSup := hthree.1
  have hcL1 := hthree.2.1
  have hnatSup : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q p| ≤ (1 + C) * w := by
    intro p hp
    rw [B.actualCompensatedNatCoefficient_of_mem q hp]
    rw [← B.partition_compensatedCoefficient_eq q ⟨p, hp⟩]
    exact hcSup ⟨p, hp⟩
  have hnatL1 :
      (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ))) ≤
        (7 + C * K) * w := by
    rw [B.compensatedNatL1_eq_partition]
    exact hcL1
  have hrowNat : ∀ p ∈ primeBand B.sampleData.n B.sampleData.W,
      (p : ℝ) * ∑ r ∈ primeBand B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV p r -
          (B.actualValuationLaw xi).covII p r| ≤ R := by
    intro p hp
    have hrowSubtype := hrow ⟨p, hp⟩
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W)
      (fun r ↦ |(B.actualValuationLaw xi).covVV p r -
        (B.actualValuationLaw xi).covII p r|)
    change (p : ℝ) *
      (∑ r ∈ (primeBand B.sampleData.n B.sampleData.W).attach,
        |(B.actualValuationLaw xi).covVV p r.1 -
          (B.actualValuationLaw xi).covII p r.1|) ≤ R at hrowSubtype
    rw [hattach] at hrowSubtype
    simpa only using hrowSubtype
  have hquad := abs_full_sub_squarefree_le_of_row
    (B.actualValuationLaw xi) (B.actualCompensatedNatCoefficient q)
    (show 0 ≤ 1 + C by linarith)
    (show 0 ≤ 7 + C * K by positivity) hw hR
    hnatSup hnatL1 hrowNat
  obtain ⟨hfull, hsf⟩ := B.actualQuadratics_eq_covariances xi q
  rw [hfull, hsf] at hquad
  simpa only [mul_assoc] using hquad

/-- Marked-prime counterpart of
`actual_primePower_relative_variance_bound_of_row`. -/
theorem actual_primePower_relative_markedRow_bound_of_row
    [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w R : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (hrow : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ r : BandPrime B.sampleData.n B.sampleData.W,
          |(B.actualValuationLaw xi).covVV p.1 r.1 -
            (B.actualValuationLaw xi).covII p.1 r.1| ≤ R)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.postBandPrimeScore q) -
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
      (1 + C) * w * R * (1 / (p : ℝ)) := by
  have hcSup :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).1
  have hnatSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ (1 + C) * w := by
    intro r hr
    rw [B.actualCompensatedNatCoefficient_of_mem q hr]
    rw [← B.partition_compensatedCoefficient_eq q ⟨r, hr⟩]
    exact hcSup ⟨r, hr⟩
  have hrowNat : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      (r : ℝ) * ∑ s ∈ primeBand B.sampleData.n B.sampleData.W,
        |(B.actualValuationLaw xi).covVV r s -
          (B.actualValuationLaw xi).covII r s| ≤ R := by
    intro r hr
    have hrowSubtype := hrow ⟨r, hr⟩
    have hattach := Finset.sum_attach
      (primeBand B.sampleData.n B.sampleData.W)
      (fun s ↦ |(B.actualValuationLaw xi).covVV r s -
        (B.actualValuationLaw xi).covII r s|)
    change (r : ℝ) *
      (∑ s ∈ (primeBand B.sampleData.n B.sampleData.W).attach,
        |(B.actualValuationLaw xi).covVV r s.1 -
          (B.actualValuationLaw xi).covII r s.1|) ≤ R at hrowSubtype
    rw [hattach] at hrowSubtype
    simpa only using hrowSubtype
  have hmarked := abs_fullMarked_sub_squarefree_le_of_row
    (B.actualValuationLaw xi) (B.actualCompensatedNatCoefficient q)
    (show 0 ≤ 1 + C by linarith) hw hnatSup hrowNat hp
  obtain ⟨hfull, hsf⟩ := B.actualMarkedRows_eq_covariances xi q p
  rw [hfull, hsf] at hmarked
  simpa only [mul_assoc] using hmarked

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
