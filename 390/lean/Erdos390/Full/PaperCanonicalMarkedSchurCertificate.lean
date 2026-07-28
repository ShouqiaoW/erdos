import Erdos390.Full.PaperCanonicalMarkedNuisanceRows
import Erdos390.Full.PaperSelectedMeshSchurEventually

/-!
# Canonical marked rows inserted into the arithmetic Schur certificate

This file removes the last displayed `hmarked` premise from the eventual
arithmetic Schur connector.  The selected prime cutoff and the effective
ball are fixed first; the sharp global marked-row rate is then constructed
from the canonical arithmetic laws and inserted into the finite Schur
argument.
-/

open Filter Topology Metric Set

namespace Erdos390.Full.PaperCanonicalMarkedSchurCertificate

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit PaperWeightedInverseExport
open FiniteProbability PaperGuardCensus
open PaperCanonicalMarkedNuisanceRows

noncomputable section

namespace PaperBridgeFit.BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]

/-- Canonical certificate connector with no marked-row premise.  The
remaining `fullEquiv` and center-envelope inputs are precisely the two mesh
transfer outputs and are discharged by the arbitrary-permitted-mesh Lemma
8.4 wrapper. -/
theorem exists_eventually_actualBandSchurCertificate_canonical
    [Nonempty Head] [Nonempty Band]
    (P : Head → Pattern) (I : PhysicalIntervals) (U : ℝ)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W) (hmod : ∀ h, (P h).modulus ≤ W)
    (a : NNReal)
    (marginFloor centerScale Cfull : ℝ)
    (hmarginFloor : 0 < marginFloor)
    (hcenterScale : 0 < centerScale) (hCfull : 0 < Cfull) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∀ (B : BridgeData Head Band)
          (hBn : B.sampleData.n = n) (hBW : B.sampleData.W = W)
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n)
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \
              (G B.sampleData.n).guards).Nonempty)
          (hcanonical : B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining)
          (T : BarycentricTarget B.sampleData)
          (hTmargin : marginFloor ≤ T.cellMassMargin)
          (hbaseline : B.baseline = T.baseline)
          (fullEquiv : ∀ (z : B.EffectiveParamSpace),
            z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
              SharpGaugeSpace B.partition.mass B.partition.center ≃L[ℝ]
                SharpGaugeSpace B.partition.mass B.partition.center)
          (hfull : ∀ (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) q,
            fullEquiv z hz q =
              B.actualFullProjectedCLM (B.effectiveParamEquiv z) q)
          (hinvFull : ∀ (z : B.EffectiveParamSpace)
              (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ)) v,
            ‖(fullEquiv z hz).symm v‖ ≤ Cfull * ‖v‖)
          (hcenter : ∀ i : Band,
            centerScale / Real.log (L B.sampleData.n) ≤ B.bandCenter i),
          let hlo : ∀ sigma, B.sampleData.lo sigma =
              physicalBound (I.lower sigma) B.sampleData.n := by
            intro sigma
            rw [hcanonical]
            rfl
          let hhi : ∀ sigma, B.sampleData.hi sigma =
              physicalBound (I.upper sigma) B.sampleData.n := by
            intro sigma
            rw [hcanonical]
            rfl
          Erdos390.Full.PaperBridgeFit.BridgeData.ActualBandSchurCertificate
            B I U a T Cfull centerScale
            (epsilon B.sampleData.n) hU hlowerOne hupperU hlo hhi
            hbaseline (by omega) := by
  obtain ⟨epsilon, hepsilon0, hepsilonRate, Nmarked, hmarked⟩ :=
    Erdos390.Full.PaperCanonicalMarkedNuisanceRows.PaperBridgeFit.BridgeData.exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
      P I U hU hlowerOne hupperU Cprom Cbank G W hW
        (fun h p hp ↦
          PaperPrimePowerAuxiliaryPrime.headPrime_le_cutoff_of_modulus_le
            (P h) (hmod h) p hp)
        a
  have hschur :=
    Erdos390.Full.PaperBridgeFit.BridgeData.eventually_actualBandSchurCertificate
    (Head := Head) (Band := Band)
    I hU hlowerOne hupperU W hW a marginFloor centerScale Cfull
      hmarginFloor hcenterScale hCfull epsilon hepsilon0 hepsilonRate
  refine ⟨epsilon, hepsilon0, hepsilonRate, ?_⟩
  filter_upwards [eventually_ge_atTop Nmarked, hschur] with n hn hschurN
  intro B hBn hBW hsep hremaining hcanonical T hTmargin hbaseline
    fullEquiv hfull hinvFull hcenter
  have hlo : ∀ sigma, B.sampleData.lo sigma =
      physicalBound (I.lower sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hhi : ∀ sigma, B.sampleData.hi sigma =
      physicalBound (I.upper sigma) B.sampleData.n := by
    intro sigma
    rw [hcanonical]
    rfl
  have hmarkedBall : ∀ (z : B.EffectiveParamSpace)
      (hz : z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ))
      (c : NuisanceCoord B.HeadIndex)
      (p : BandPrime B.sampleData.n B.sampleData.W),
      |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
        (fun m ↦ B.nuisanceStatistic m c)
        (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
          epsilon B.sampleData.n * (1 / (p.1 : ℝ)) := by
    intro z hz c p
    exact hmarked B z hz (by omega) hBW hsep hremaining hcanonical c p
  exact hschurN B hBn hBW T hTmargin hbaseline hlo hhi fullEquiv
    hfull hinvFull hcenter hmarkedBall

end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalMarkedSchurCertificate
