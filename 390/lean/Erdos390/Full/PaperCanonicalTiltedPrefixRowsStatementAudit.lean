import Erdos390.Full.PaperCanonicalTiltedPrefixRows

/-! # Independent statement-shape audit: canonical marked nuisance rows

These examples expose that both terminal rates are nonnegative, are
`o(1 / log L)`, and have no moving-prefix, guard, density, Taylor, or raw
profile assumptions.
-/

open Filter Topology

namespace Erdos390.Full.PaperCanonicalTiltedPrefixRowsStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability ValuationTiltCell PaperGuardCensus
open PaperCanonicalTiltedPrefixRows
open PaperCanonicalTiltedPrefixRows.PaperBridgeFit

noncomputable section

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

example [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \ (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
            (c : Cell Head) (k : ℕ),
            |(B.cellMediumLaw xi c).covariance
                (fun m ↦ (valuation p.1 (m : ℕ) : ℝ))
                (fun m ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
              epsilon B.sampleData.n / (p.1 : ℝ) :=
  PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_tilted_valuation_prefix_rate_unrestricted
    P I Cprom Cbank G W hW hHeadLe Acoef hAcoef

example [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ q ∈ (P h).primes, q ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ epsilon : ℕ → ℝ,
      (∀ n, 0 ≤ epsilon n) ∧
      Tendsto (fun n : ℕ ↦ epsilon n * Real.log (L n))
        atTop (nhds 0) ∧
      ∃ N₀ : ℕ,
        ∀ {Band : Type*} [Fintype Band] [DecidableEq Band]
          (B : BridgeData Head Band) (xi : B.ParamSpace),
          N₀ ≤ B.sampleData.n → B.sampleData.W = W →
          (∀ p : BandPrime B.sampleData.n B.sampleData.W,
            |B.effectivePrimeCoefficient xi p| ≤ Acoef) →
          (hsep : physicalBound (I.upper .minus) B.sampleData.n <
            physicalBound (I.lower .plus) B.sampleData.n) →
          (hremaining : ∀ c : Cell Head,
            (rawCell P I B.sampleData.n c \ (G B.sampleData.n).guards).Nonempty) →
          B.sampleData = canonicalSampleData
            (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
          ∀ (p : BandPrime B.sampleData.n B.sampleData.W)
            (c : Cell Head),
            |(B.cellMediumLaw xi c).covariance
                (fun m ↦ valuation p.1 (m : ℕ))
                (fun m ↦ B.physicalScore ⟨c, m⟩)| ≤
              epsilon B.sampleData.n / (p.1 : ℝ) :=
  PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_physical_valuation_rate_unrestricted
    P I Cprom Cbank G W hW hHeadLe Acoef hAcoef

end

end Erdos390.Full.PaperCanonicalTiltedPrefixRowsStatementAudit
