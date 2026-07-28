import Erdos390.Full.PaperActualPrimePowerRowTransfer

/-!
# Canonical eventual actual weighted prime-power row

This is the scalar/marked-row companion to the sharp band-operator terminal.
It keeps the literal weighted prime row because the Lemma 8.6 slow
coefficient contains a within-band deviation which is not a lifted band
vector.  The box-independent raw Lemma 7.5 term is selected before the ODE
box; every box-dependent term is confined to a remainder whose product with
`log L` tends to zero.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperGuardCensus GuardedUniformCell
open StructuredCells ValuationScoreDomination PrimeSums

namespace BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

/-- Fully discharged actual-law weighted `VV-II` row on the canonical
bridge.  `Cpow` is independent of the later coefficient boxes.  The raw-law
remainder and the actual/raw correction are displayed separately, together
with the exact rates needed for the moving-low argument. -/
theorem boxIndependent_canonicalRaw_actualWeightedRow
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
              ∀ p : BandPrime B.sampleData.n B.sampleData.W,
                (p.1 : ℝ) *
                    ∑ r : BandPrime B.sampleData.n B.sampleData.W,
                      |(B.actualValuationLaw xi).covVV p.1 r.1 -
                        (B.actualValuationLaw xi).covII p.1 r.1| ≤
                  FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant *
                      (1 / (B.sampleData.W : ℝ)) +
                    epsilon75 B.sampleData.n +
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
                        B.sampleData.n) := by
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
  have htotalRate : Tendsto
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
      atTop (nhds 0) := by
    simpa only [add_mul, zero_add] using hphysicalRate.add hguardRate
  refine ⟨epsilon75, hepsilon0, hepsilonT, hepsilonRate,
    htotalRate, max N75 (max Nguard Nphysical), ?_⟩
  intro Band _instBand _instBandDec B xi hN hBW hsep hremaining
    hcanonical heta hphys p
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
    intro r
    simpa only [referenceLaw, hS,
      physicalMediumReferenceLaw_eq_canonicalGuardedMediumReferenceLaw] using
        hguardRaw r
  have hpowerRow :=
    B.actual_powerCorrection_reference_weightedRow_le_of_two_sides
      xi referenceLaw hphysical hguard
  exact B.actual_fullSquarefree_weightedRow_le_of_reference
    xi referenceLaw h75 hpowerRow p

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
