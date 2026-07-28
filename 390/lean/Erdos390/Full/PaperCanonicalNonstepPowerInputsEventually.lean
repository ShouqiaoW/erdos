import Erdos390.Full.PaperBridgeCanonicalPowerCorrectionTriangle

/-!
# Canonical inputs for the non-step full slow row

This file exports the two objects that the literal non-step ledger needs,
rather than only their earlier step-function contraction:

* Lemma 7.5 for the unguarded canonical raw reference law; and
* the reciprocal weighted `VV-II` row comparing the final actual law with
  that same reference law.

The prime-power constant is chosen before `W` and the later coefficient
box.  Both analytic remainders retain the sharp moving-low rate after
multiplication by `log L`.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- Exact sum of the residual-physical and guard-deletion row errors used
to compare the actual valuation law with the raw canonical law. -/
def canonicalNonstepPowerCorrection
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    (Cmax : ℝ) (Cprom Cbank W : ℕ) (Acoef Aphys : ℝ)
    (n : ℕ) : ℝ :=
  physicalPowerCorrectionRowError
      (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
      (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W +
    guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n

omit [DecidableEq Head] in
/-- The canonical combined row error is nonnegative on the range used by
the bridge construction. -/
theorem canonicalNonstepPowerCorrection_nonneg
    [Nonempty Head]
    (P : Head → HeadPattern.Pattern) (I : PhysicalIntervals)
    {Cmax Acoef Aphys : ℝ} {Cprom Cbank W n : ℕ}
    (hCmax : 1 ≤ Cmax) (hAphys : 0 ≤ Aphys)
    (hW : 1 < W) (hn : 1 < n) :
    0 ≤ canonicalNonstepPowerCorrection
      P I Cmax Cprom Cbank W Acoef Aphys n := by
  have hLpos : 0 < Scale.L n := Scale.L_pos hn
  have hlogCmax : 0 ≤ Real.log Cmax := Real.log_nonneg hCmax
  have hepsilon : 0 ≤
      canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n := by
    unfold canonicalPhysicalPowerCorrectionEpsilon
    exact div_nonneg (mul_nonneg hAphys hlogCmax) hLpos.le
  have hG : 0 ≤
      canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef :=
    canonicalPhysicalPowerCorrectionConstant_nonneg P I Cmax W Acoef
  have hphysical : 0 ≤
      physicalPowerCorrectionRowError
        (canonicalPhysicalPowerCorrectionEpsilon Aphys Cmax n)
        (canonicalPhysicalPowerCorrectionConstant P I Cmax W Acoef) n W :=
    physicalPowerCorrectionRowError_nonneg hepsilon hG
  have hCenv : 0 ≤
      PaperStatisticNorm.valuationLogCoefficient Cmax W :=
    PaperStatisticNorm.valuationLogCoefficient_nonneg hCmax hW
  have hD : 0 ≤ canonicalGuardPerturbationConstant P I
      (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W) :=
    canonicalGuardPerturbationConstant_nonneg P I _
  have hcensus : 0 ≤
      PaperGuardCensus.censusRatioMajorant Cprom Cbank n := by
    unfold PaperGuardCensus.censusRatioMajorant
    have hcoef : 0 ≤ (Cprom : ℝ) +
        3 * (Cbank : ℝ) * (Scale.L n + 2) := by positivity
    exact div_nonneg
      (mul_nonneg hcoef (Scale.y_pos (Nat.zero_lt_of_lt hn)).le)
      (by positivity)
  have hguard : 0 ≤ guardPowerCorrectionWeightedMajorant Cprom Cbank
      (PaperStatisticNorm.valuationLogCoefficient Cmax W)
      (canonicalGuardPerturbationConstant P I
        (Acoef * PaperStatisticNorm.valuationLogCoefficient Cmax W)) n := by
    unfold guardPowerCorrectionWeightedMajorant
    exact mul_nonneg (Nat.cast_nonneg _)
      (PaperGuardCensus.guardPowerCorrectionRowError_nonneg
        (mul_nonneg hCenv hLpos.le) (mul_nonneg hD hcensus))
  unfold canonicalNonstepPowerCorrection
  exact add_nonneg hphysical hguard

/-- Box-independent canonical raw inputs for the exact non-step slow-row
ledgers.  The eventual threshold is uniform in the band type, bridge data,
tilt point, and component weights. -/
theorem boxIndependent_canonicalRaw_nonstepPower_inputs
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
        Tendsto epsilon75 atTop (nhds 0) ∧
        Tendsto
          (fun n : ℕ ↦ epsilon75 n * Real.log (Scale.L n))
          atTop (nhds 0) ∧
        Tendsto
          (fun n : ℕ ↦
            canonicalNonstepPowerCorrection
              P I Cmax Cprom Cbank W Acoef Aphys n *
                Real.log (Scale.L n))
          atTop (nhds 0) ∧
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
              let hS : ∀ c : Cell Head,
                  (rawCell P I B.sampleData.n c).Nonempty :=
                fun c ↦ (hremaining c).mono Finset.sdiff_subset
              let referenceLaw :=
                B.canonicalRawMediumReferenceLaw
                  P I Cmax xi hupperMax hS
              PaperPrimePowerLemma75.PrimePowerTransferBounds
                  referenceLaw B.sampleData.n B.sampleData.W
                    FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
                    (epsilon75 B.sampleData.n) ∧
                ∀ p : BandPrime B.sampleData.n B.sampleData.W,
                  (p.1 : ℝ) *
                    ∑ q : BandPrime B.sampleData.n B.sampleData.W,
                      |((B.actualValuationLaw xi).covVV p.1 q.1 -
                          (B.actualValuationLaw xi).covII p.1 q.1) -
                        (referenceLaw.covVV p.1 q.1 -
                          referenceLaw.covII p.1 q.1)| ≤
                    canonicalNonstepPowerCorrection
                      P I Cmax Cprom Cbank W Acoef Aphys
                        B.sampleData.n := by
  obtain ⟨hCpow, h75main⟩ :=
    boxIndependent_canonicalRaw_primePower_transfer P I Cmax hupperMax
  refine ⟨hCpow, ?_⟩
  intro W hW hsupport Acoef hAcoef Aphys hAphys0
  obtain ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
      N75, hN75⟩ := h75main W hW hsupport Acoef hAcoef
  have hupperOne : ∀ sigma, 1 ≤ I.upper sigma := fun sigma ↦
    (hlowerOne sigma).trans (I.lower_lt_upper sigma).le
  obtain ⟨Nguard, hNguard⟩ :=
    exists_eventually_canonicalGuardPowerCorrection_reference_bound
      P I Cmax hupperOne hupperMax Cprom Cbank ledger
        W hW Acoef hAcoef
  have hphysicalMain :=
    exists_eventually_canonicalPhysical_powerCorrection_row
      P I Cmax hlowerOne hupperMax Cprom Cbank ledger
        W hW Acoef Aphys hAcoef hAphys0
  dsimp only at hphysicalMain
  obtain ⟨_hGphys, hphysicalRate, Nphysical, hNphysical⟩ :=
    hphysicalMain
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
  have htotalRate : Tendsto
      (fun n : ℕ ↦
        canonicalNonstepPowerCorrection
          P I Cmax Cprom Cbank W Acoef Aphys n *
            Real.log (Scale.L n)) atTop (nhds 0) := by
    simpa only [canonicalNonstepPowerCorrection, add_mul, zero_add] using
      hphysicalRate.add hguardRate
  refine ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
    htotalRate, max N75 (max Nguard Nphysical), ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta hphys
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
      referenceLaw B.sampleData.n B.sampleData.W
        FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
        (epsilon75 B.sampleData.n) := by
    simpa only [referenceLaw, hS] using
      hN75 B xi hN75' hBW heta hS
  have hphysical := hNphysical B xi hNphysical' hBW hsep hremaining
    hcanonical heta hphys
  have hguardRaw := hNguard B xi hNguard' hBW hsep hremaining
    hcanonical heta
  have hguard : ∀ p : BandPrime B.sampleData.n B.sampleData.W,
      (p.1 : ℝ) *
        ∑ q : BandPrime B.sampleData.n B.sampleData.W,
          |((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
              (B.physicalMediumReferenceLaw xi).covII p.1 q.1) -
            (referenceLaw.covVV p.1 q.1 -
              referenceLaw.covII p.1 q.1)| ≤
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
  exact ⟨h75, by
    simpa only [referenceLaw, hS,
      canonicalNonstepPowerCorrection, hBW] using hpowerRow⟩

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
