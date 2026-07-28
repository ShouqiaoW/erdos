import Erdos390.Full.PaperCanonicalTiltedValuationMeanRows

/-! # Statement-shape audit: canonical valuation mean profiles

The terminal theorem exposes a fixed reciprocal first-moment constant and a
pairwise `o(1 / log L)/p` error.  Its coefficient box is arbitrary after
`W`; no box-size condition on `W` or unproved density/guard/profile premise
occurs in the exported statement.
-/

open Filter Topology

namespace Erdos390.Full.PaperCanonicalTiltedValuationMeanRowsStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open ArithmeticBandGeometry PaperBridgeFit
open FiniteProbability PaperGuardCensus
open PaperCanonicalTiltedValuationMeanRows
open PaperCanonicalTiltedValuationMeanRows.PaperBridgeFit

noncomputable section

variable {Head : Type*} [Fintype Head] [DecidableEq Head]

example [Nonempty Head]
    (P : Head → Pattern) (I : PhysicalIntervals)
    (Cprom Cbank : ℕ) (G : ∀ n, Ledger n Cprom Cbank)
    (W : ℕ) (hW : 1 < W)
    (hHeadLe : ∀ h, ∀ p ∈ (P h).primes, p ≤ W)
    (Acoef : ℝ) (hAcoef : 0 ≤ Acoef) :
    ∃ Aval : ℝ, 0 ≤ Aval ∧
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
              (rawCell P I B.sampleData.n c \
                (G B.sampleData.n).guards).Nonempty) →
            B.sampleData = canonicalSampleData
              (W := B.sampleData.W) P I (G B.sampleData.n) hsep hremaining →
            ∀ p : BandPrime B.sampleData.n B.sampleData.W,
              (∀ c : Cell Head,
                (B.cellMediumLaw xi c).expect
                    (fun m ↦ valuation p.1 (m : ℕ)) ≤
                  Aval / (p.1 : ℝ)) ∧
              (∀ c c' : Cell Head,
                |(B.cellMediumLaw xi c).expect
                      (fun m ↦ valuation p.1 (m : ℕ)) -
                  (B.cellMediumLaw xi c').expect
                      (fun m ↦ valuation p.1 (m : ℕ))| ≤
                    epsilon B.sampleData.n / (p.1 : ℝ)) :=
  PaperBridgeFit.BridgeData.exists_uniform_canonical_cellMediumLaw_valuation_mean_profiles_rate_unrestricted
    P I Cprom Cbank G W hW hHeadLe Acoef hAcoef

end

end Erdos390.Full.PaperCanonicalTiltedValuationMeanRowsStatementAudit
