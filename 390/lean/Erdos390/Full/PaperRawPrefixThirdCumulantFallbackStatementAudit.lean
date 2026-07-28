import Erdos390.Full.PaperRawPrefixThirdCumulantFallback

/-! Independent statement-shape audit for the raw moving-prefix fallback. -/

open Filter

namespace Erdos390.Full.PaperRawPrefixThirdCumulantFallbackStatementAudit

open Erdos390.Full
open ArithmeticModel Scale HeadPattern StructuredCells
open DivisibilityMomentBounds FiniteProbability

noncomputable section

example
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ, ∀ {n : ℕ}, N₀ ≤ n →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty, ∀ D : ℕ, 0 < D →
        (uniformOnFinset S hS).expect
            (fun m : S ↦ divInd D (m : ℕ)) ≤ G / (D : ℝ) :=
  PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_divInd_fallback
    H hA hAC hC

example
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) (W : ℕ) (hHW : H.modulus ≤ W) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k p r s : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      p ∈ primeBand n W → 1 ≤ r → 1 ≤ s →
      p ^ max r s ≤ yNat n ^ 4 →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covarianceThirdCentered
            (fun m : S ↦ divInd (p ^ r) (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
            (fun m : S ↦ divInd (p ^ s) (m : ℕ))| ≤
          K / (((p ^ max r s : ℕ) : ℝ) * L n) +
            (G / ((p ^ s : ℕ) : ℝ)) *
              (K / (((p ^ r : ℕ) : ℝ) * L n)) +
            (G / ((p ^ r : ℕ) : ℝ)) *
              (K / (((p ^ s : ℕ) : ℝ) * L n)) :=
  PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_samePrime_thirdCumulant_chamber
    H hA hAC hC W hHW

example
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 0 < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ G : ℝ, 0 < G ∧ ∃ N₀ : ℕ,
      ∀ {n k D E : ℕ}, N₀ ≤ n →
      physicalBound A n < k → k ≤ physicalBound C n →
      0 < D → 0 < E → D * E ≤ yNat n ^ 4 →
      D ∈ Nat.smoothNumbers (yNat n + 1) →
      E ∈ Nat.smoothNumbers (yNat n + 1) →
      D * E ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime D E → Nat.Coprime D H.modulus →
      Nat.Coprime E H.modulus → Nat.Coprime (D * E) H.modulus →
      let S := structuredCell H (physicalBound A n) (physicalBound C n)
        (yNat n)
      ∀ hS : S.Nonempty,
        |(uniformOnFinset S hS).covarianceThirdCentered
            (fun m : S ↦ divInd D (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)
            (fun m : S ↦ divInd E (m : ℕ))| ≤
          (K * (1 + 2 * G)) /
            (((D : ℝ) * (E : ℝ)) * L n) :=
  PaperRawPrefixThirdCumulantFallback.exists_uniform_rawCell_coprime_thirdCumulant_chamber
    H hA hAC hC

example {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (value : Omega → ℕ)
    (pref : Omega → ℝ) {D E : ℕ} {G : ℝ}
    (hD : 0 < D) (hE : 0 < E) (hcop : Nat.Coprime D E)
    (hG : 0 ≤ G)
    (hpref0 : ∀ omega, 0 ≤ pref omega)
    (hpref1 : ∀ omega, pref omega ≤ 1)
    (hdiv : ∀ d : ℕ, 0 < d →
      mu.expect (fun omega ↦ divInd d (value omega)) ≤ G / (d : ℝ)) :
    |mu.covarianceThirdCentered
        (fun omega ↦ divInd D (value omega)) pref
        (fun omega ↦ divInd E (value omega))| ≤
      (2 * G + 4 * G ^ 2) / ((D : ℝ) * (E : ℝ)) :=
  mu.abs_covarianceThirdCentered_divInd_prefix_divInd_coprime_fallback_le
    value pref hD hE hcop hG hpref0 hpref1 hdiv

end

end Erdos390.Full.PaperRawPrefixThirdCumulantFallbackStatementAudit
