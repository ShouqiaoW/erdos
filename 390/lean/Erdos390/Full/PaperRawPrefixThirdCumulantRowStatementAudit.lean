import Erdos390.Full.PaperRawPrefixThirdCumulantRow

/-!
# Independent statement-shape audit: valuation-score third-cumulant row

The finite-law example exposes the sole probabilistic input, the reciprocal
divisor expectation bound.  The structured-cell specialization then removes
that input by proving it from the cell census.  Thus the final example does
not assume the third-cumulant estimate that it concludes.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperRawPrefixThirdCumulantRowStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerTaylorLedger ValuationScoreDomination
open PaperRawPrefixThirdCumulantRow

noncomputable section

set_option maxHeartbeats 800000 in

example {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) (P : Finset ℕ) (eta : ℕ → ℝ)
    (M p : ℕ) {B G L : ℝ}
    (hpP : p ∈ P) (hB : 0 ≤ B) (hG : 0 ≤ G) (hL : 0 < L)
    (hprime : ∀ q ∈ P, q.Prime)
    (hvaluePos : ∀ omega, 0 < value omega)
    (hvalueLe : ∀ omega, value omega ≤ M)
    (heta : ∀ q ∈ P, |eta q| ≤ B)
    (hpref0 : ∀ omega, 0 ≤ pref omega)
    (hpref1 : ∀ omega, pref omega ≤ 1)
    (hdiv : ∀ D : ℕ, 0 < D →
      mu.expect (fun omega ↦ divInd D (value omega)) ≤ G / (D : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ valuation p (value omega)) pref
        (fun omega ↦ valuationScore P eta L (value omega))| ≤
      (B / L) *
        (((8 * G + 16 * G ^ 2) * (∑ q ∈ P, 1 / (q : ℝ)) +
          2 * G * positivePrimePowerLcmConstant) / (p : ℝ)) :=
  mu.abs_covarianceThirdCentered_valuation_prefix_valuationScore_fallback_le
    value pref P eta M p hpP hB hG hL hprime hvaluePos hvalueLe
      heta hpref0 hpref1 hdiv

example
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ, ∀ {n W p k : ℕ}
      {B : ℝ} (eta : ℕ → ℝ),
      N₀ ≤ n → p ∈ primeBand n W → 0 ≤ B →
      (∀ q ∈ primeBand n W, |eta q| ≤ B) →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covarianceThirdCentered
            (fun m : S ↦ valuation p (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
            (fun m : S ↦ valuationScore (primeBand n W) eta (L n)
              (m : ℕ))| ≤
          (B / L n) *
            (((8 * G + 16 * G ^ 2) *
                (∑ q ∈ primeBand n W, 1 / (q : ℝ)) +
              2 * G * positivePrimePowerLcmConstant) / (p : ℝ)) :=
  exists_uniform_rawCell_valuationScore_thirdCumulant_bound
    H hA hAC hC

example (B G : ℝ) (W : ℕ) (hB : 0 ≤ B) (hG : 0 ≤ G) :
    ∀ᶠ n : ℕ in atTop,
      (B / L n) *
          ((8 * G + 16 * G ^ 2) *
              (∑ q ∈ primeBand n W, 1 / (q : ℝ)) +
            2 * G * positivePrimePowerLcmConstant) ≤
        rawThirdCumulantRateMajorant B G n :=
  eventually_rawThirdCumulantCoefficient_le B G W hB hG

example (B G : ℝ) :
    Tendsto (fun n : ℕ ↦
      rawThirdCumulantRateMajorant B G n * Real.log (L n))
      atTop (nhds 0) :=
  tendsto_rawThirdCumulantRateMajorant_mul_logL_zero B G

end

end Erdos390.Full.PaperRawPrefixThirdCumulantRowStatementAudit
