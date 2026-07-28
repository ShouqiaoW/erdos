import Erdos390.Full.PaperCanonicalMarkedNuisanceRows

open Filter Topology Metric Set

namespace Erdos390.Full.PaperCanonicalMarkedNuisanceRows

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability PaperGuardCensus

noncomputable section

namespace PaperBridgeFit.BridgeData

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

example [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals) (U : ℝ)
    (hU : 1 ≤ U)
    (hlowerOne : ∀ sigma, 1 ≤ I.lower sigma)
    (hupperU : ∀ sigma, I.upper sigma ≤ U)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ p ∈ (P h).primes, p ≤ W)
    (a : NNReal) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (z : B.EffectiveParamSpace),
          z ∈ closedBall (0 : B.EffectiveParamSpace) (a : ℝ) →
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \
              (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (c : NuisanceCoord B.HeadIndex)
            (p : BandPrime B.sampleData.n B.sampleData.W),
            |(B.tiltedLaw (B.effectiveParamEquiv z)).covariance
                (fun m ↦ B.nuisanceStatistic m c)
                (fun m ↦ valuation p.1 (B.sampleData.value m))| ≤
              epsilon B.sampleData.n * (1 / (p.1 : ℝ)) := by
  exact exists_uniform_canonical_tiltedLaw_nuisance_valuation_rate_on_effectiveBall
    P I U hU hlowerOne hupperU Cprom Cbank G W hW hHeadLe a

end PaperBridgeFit.BridgeData

end

end Erdos390.Full.PaperCanonicalMarkedNuisanceRows
