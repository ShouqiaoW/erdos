import Erdos390.Full.PaperPrimePowerRelativeQuadratic

/-!
# Actual bridge specialization of the relative prime-power transfer

This file constructs the bounded valuation law directly from the genuine
guard-deleted tilted bridge sample.  It then applies the weighted row theorem
to the literal post-regression coefficients from Lemma 8.6.
-/

open scoped BigOperators

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75
open PaperPrimePowerRelativeQuadratic
open PaperWeightedInverseExport

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- One literal finite endpoint for both physical pools. -/
def sampleEndpoint : ℕ :=
  max (B.sampleData.hi .minus) (B.sampleData.hi .plus)

theorem sample_value_le_endpoint (m : B.sampleData.Sample) :
    B.sampleData.value m ≤ B.sampleEndpoint := by
  have hvalue := B.sampleData.value_le_hi m
  cases hsign : (B.sampleData.cellOf m).2 with
  | minus =>
      have hvalue' : B.sampleData.value m ≤ B.sampleData.hi .minus := by
        simpa only [hsign] using hvalue
      exact hvalue'.trans (Nat.le_max_left _ _)
  | plus =>
      have hvalue' : B.sampleData.value m ≤ B.sampleData.hi .plus := by
        simpa only [hsign] using hvalue
      exact hvalue'.trans (Nat.le_max_right _ _)

/-- The actual tilted bounded valuation law used by Lemmas 7.5 and 8.6. -/
def actualValuationLaw [Nonempty Head] (xi : B.ParamSpace) :
    BoundedValuationLaw B.sampleData.Sample B.sampleEndpoint where
  probability := B.tiltedLaw xi
  value := B.sampleData.value
  value_pos := B.sampleData.value_pos
  value_le := B.sample_value_le_endpoint

/-- Extend the literal subtype coefficient by zero outside the actual prime
band.  Every quadratic form below immediately restricts it back to the band. -/
def actualCompensatedNatCoefficient
    (q : B.RawBandGauge) (p : ℕ) : ℝ :=
  if hp : p ∈ primeBand B.sampleData.n B.sampleData.W then
    B.actualCompensatedCoefficient q ⟨p, hp⟩
  else 0

@[simp]
theorem actualCompensatedNatCoefficient_of_mem
    (q : B.RawBandGauge) {p : ℕ}
    (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    B.actualCompensatedNatCoefficient q p =
      B.actualCompensatedCoefficient q ⟨p, hp⟩ := by
  simp only [actualCompensatedNatCoefficient, dif_pos hp]

/-- The subtype and natural-prime `L¹` sums are exactly the same finite sum. -/
theorem compensatedNatL1_eq_partition
    (q : B.RawBandGauge) :
    (∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ))) =
      B.partition.compensatedL1 q := by
  unfold ArithmeticBandGeometry.Partition.compensatedL1
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ |B.actualCompensatedNatCoefficient q p| * (1 / (p : ℝ)))
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]
  rw [B.partition_compensatedCoefficient_eq q p]
  ring

/-- The primewise post-band score is the full-valuation score of the actual
bounded valuation law. -/
theorem postBandPrimeScore_eq_actualValuationSum [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    (m : B.sampleData.Sample) :
    B.postBandPrimeScore q m =
      ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
        B.actualCompensatedNatCoefficient q p *
          (B.actualValuationLaw xi).V p m := by
  unfold postBandPrimeScore actualValuationLaw
    PrimePowerCovariance.BoundedValuationLaw.V
  have hattach := Finset.sum_attach
    (primeBand B.sampleData.n B.sampleData.W)
    (fun p ↦ B.actualCompensatedNatCoefficient q p *
      valuation p (B.sampleData.value m))
  rw [← hattach]
  apply Finset.sum_congr rfl
  intro p hp
  rw [B.actualCompensatedNatCoefficient_of_mem q p.2]

/-- Literal squarefree companion to the post-band prime score. -/
def postBandSquarefreeScore
    (q : B.RawBandGauge) (m : B.sampleData.Sample) : ℝ :=
  ∑ p ∈ primeBand B.sampleData.n B.sampleData.W,
    B.actualCompensatedNatCoefficient q p *
      divInd p (B.sampleData.value m)

/-- Exact identification of the two finite covariance quadratic forms with
the actual full-valuation and squarefree scores. -/
theorem actualQuadratics_eq_covariances [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) :
    fullValuationQuadratic (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) =
      (B.tiltedLaw xi).covariance
        (B.postBandPrimeScore q) (B.postBandPrimeScore q) ∧
    squarefreeQuadratic (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) =
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q) := by
  constructor
  · rw [fullValuationQuadratic_eq_covariance]
    congr 1 <;> funext m <;>
      exact (B.postBandPrimeScore_eq_actualValuationSum xi q m).symm
  · rw [squarefreeQuadratic_eq_covariance]
    rfl

/-- Exact marked-row identification for the actual full and squarefree
post-band scores. -/
theorem actualMarkedRows_eq_covariances [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge) (p : ℕ) :
    fullMarkedRow (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) p =
      (B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.postBandPrimeScore q) ∧
    squarefreeMarkedRow (B.actualValuationLaw xi)
        (primeBand B.sampleData.n B.sampleData.W)
        (B.actualCompensatedNatCoefficient q) p =
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q) := by
  constructor
  · unfold fullMarkedRow actualValuationLaw
      PrimePowerCovariance.BoundedValuationLaw.V
    congr 1
    funext m
    exact (B.postBandPrimeScore_eq_actualValuationSum xi q m).symm
  · rfl

/-- The exact actual-prime relative prime-power estimate.  Its only analytic
input is the already exported Lemma 7.5 row bound; all coefficient constants
are conclusions of the canonical-mesh moment and weighted-regression bounds. -/
theorem actual_primePower_relative_variance_bound [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon : ℝ}
    (hC : 0 ≤ C) (hK : 0 ≤ K) (hw : 0 ≤ w)
    (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation p| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon) :
    |(B.tiltedLaw xi).covariance
        (B.postBandPrimeScore q) (B.postBandPrimeScore q) -
      (B.tiltedLaw xi).covariance
        (B.postBandSquarefreeScore q) (B.postBandSquarefreeScore q)| ≤
      ((1 + C) * (7 + C * K)) *
        (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) * w ^ 2 := by
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
  have hCsup : 0 ≤ 1 + C := by linarith
  have hCL1 : 0 ≤ 7 + C * K := by positivity
  have hquad := abs_full_sub_squarefree_le_of_lemma75
    (B.actualValuationLaw xi) (B.actualCompensatedNatCoefficient q)
    hCsup hCL1 hw hCpow hepsilon hnatSup hnatL1 h75
  obtain ⟨hfull, hsf⟩ := B.actualQuadratics_eq_covariances xi q
  rw [hfull, hsf] at hquad
  exact hquad

/-- The marked-prime component of the same actual relative transfer. -/
theorem actual_primePower_relative_markedRow_bound [Nonempty Head]
    (xi : B.ParamSpace) (q : B.RawBandGauge)
    {C K w Cpow epsilon : ℝ}
    (hC : 0 ≤ C) (hw : 0 ≤ w)
    (hsharp : paperSharpNorm B.harmonicMass B.bandCenter
      (B.partition.center_ne_zero B.n_gt_one) q ≤ C * w)
    (hbandT : PrimeSums.bandTReciprocalSum
      B.sampleData.n B.sampleData.W ≤ K)
    (hdevSup : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.partition.deviation r| ≤ w)
    (hdevL1 : B.partition.totalL1 ≤ 7 * w)
    (hdevL2 : B.partition.variance ≤ 4 * w ^ 2)
    (h75 : PrimePowerTransferBounds (B.actualValuationLaw xi)
      B.sampleData.n B.sampleData.W Cpow epsilon)
    {p : ℕ} (hp : p ∈ primeBand B.sampleData.n B.sampleData.W) :
    |(B.tiltedLaw xi).covariance
        (fun m ↦ valuation p (B.sampleData.value m))
        (B.postBandPrimeScore q) -
      (B.tiltedLaw xi).covariance
        (fun m ↦ divInd p (B.sampleData.value m))
        (B.postBandSquarefreeScore q)| ≤
      (1 + C) * w *
        (Cpow * (1 / (B.sampleData.W : ℝ)) + epsilon) *
          (1 / (p : ℝ)) := by
  have hcSup :=
    (B.partition.compensatedCoefficient_three_bounds B.n_gt_one q
      hC hw hsharp hbandT hdevSup hdevL1 hdevL2).1
  have hnatSup : ∀ r ∈ primeBand B.sampleData.n B.sampleData.W,
      |B.actualCompensatedNatCoefficient q r| ≤ (1 + C) * w := by
    intro r hr
    rw [B.actualCompensatedNatCoefficient_of_mem q hr]
    rw [← B.partition_compensatedCoefficient_eq q ⟨r, hr⟩]
    exact hcSup ⟨r, hr⟩
  have hCsup : 0 ≤ 1 + C := by linarith
  have hmarked := abs_fullMarked_sub_squarefree_le_of_lemma75
    (B.actualValuationLaw xi) (B.actualCompensatedNatCoefficient q)
    hCsup hw hnatSup h75 hp
  obtain ⟨hfull, hsf⟩ := B.actualMarkedRows_eq_covariances xi q p
  rw [hfull, hsf] at hmarked
  exact hmarked

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
