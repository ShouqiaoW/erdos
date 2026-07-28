import Erdos390.Full.PaperLemma75LiteralSeries

/-!
# Independent statement audit for paper Lemma 7.5

The public theorem packages its five conclusions in
`LiteralPrimePowerTransferBounds`.  This audit deliberately expands that
package: it checks the order `C_pow`, `W`, coefficient box, remainder,
ambient threshold, tilt and mixture weight, and it restates all three
unrestricted prime-power series, the diagonal estimate, and the relative
row estimate explicitly.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperLemma75LiteralSeriesStatementAudit

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open Erdos390.Full.PaperLemma75LiteralSeries
open Erdos390.Full.FixedFiniteMixtureGlobalTiltLemma75

noncomputable section

variable {Cell : Type*} [Fintype Cell]

example
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hCmax : 0 < Cmax)
    (hC_le : ∀ c, C c ≤ Cmax) :
    let C_pow :=
      FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
    0 < C_pow ∧
      ∀ W : ℕ, 1 < W →
      (∀ c, ∀ p ∈ (H c).primes, p ≤ W) →
      ∀ B : ℝ, 0 ≤ B →
      ∃ epsilon_BW : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon_BW n) ∧
        Tendsto epsilon_BW atTop (nhds 0) ∧
        Tendsto (fun n : ℕ ↦ epsilon_BW n * Real.log (L n))
          atTop (nhds 0) ∧
        ∃ N₀ : ℕ, ∀ {n : ℕ} (eta : ℕ → ℝ), N₀ ≤ n →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := fun c ↦ structuredCell (H c)
            (physicalBound (A c) n) (physicalBound (C c) n) (yNat n)
          (∀ c, (S c).Nonempty) ∧
            ∀ hS : ∀ c, (S c).Nonempty,
            ∀ weight : FiniteProbability Cell,
              let law := globallyTiltedStructuredMixtureLaw H A C Cmax
                n W eta hC_le hS weight
              (∀ p ∈ primeBand n W,
                ∀ q ∈ (primeBand n W).erase p,
                  (∑' k : ℕ, if 2 ≤ k then
                    |law.probability.covariance (law.Ip p k) (law.I q)|
                    else 0) ≤
                    (C_pow * tPrime n p * tPrime n q + epsilon_BW n) *
                      (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ))) ∧
              (∀ p ∈ primeBand n W,
                ∀ q ∈ (primeBand n W).erase p,
                  (∑' l : ℕ, if 2 ≤ l then
                    |law.probability.covariance (law.I p) (law.Ip q l)|
                    else 0) ≤
                    (C_pow * tPrime n p * tPrime n q + epsilon_BW n) *
                      (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2) ∧
              (∀ p ∈ primeBand n W,
                ∀ q ∈ (primeBand n W).erase p,
                  (∑' kl : ℕ × ℕ, if 2 ≤ kl.1 ∧ 2 ≤ kl.2 then
                    |law.probability.covariance
                      (law.Ip p kl.1) (law.Ip q kl.2)| else 0) ≤
                    (C_pow * tPrime n p * tPrime n q + epsilon_BW n) *
                      (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2) ∧
              (∀ p ∈ primeBand n W,
                law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
                  (C_pow + epsilon_BW n) * (1 / (p : ℝ)) ^ 2) ∧
              (∀ p ∈ primeBand n W,
                (p : ℝ) * ∑ q ∈ primeBand n W,
                  |law.covVV p q - law.covII p q| ≤
                    C_pow * (1 / (W : ℝ)) + epsilon_BW n) := by
  dsimp only
  obtain ⟨hCpow, hmain⟩ :=
    boxIndependent_globalTilt_primePower_transfer_literal
      H A C Cmax hA hAC hC hCmax hC_le
  refine ⟨hCpow, ?_⟩
  intro W hW hHW B hB
  obtain ⟨epsilon_BW, hepsilon0, hepsilonT, hepsilonRate, N₀, hN₀⟩ :=
    hmain W hW hHW B hB
  refine ⟨epsilon_BW, hepsilon0, hepsilonT, hepsilonRate, N₀, ?_⟩
  intro n eta hn heta
  obtain ⟨hS, hbounds⟩ := hN₀ eta hn heta
  refine ⟨hS, ?_⟩
  intro hS weight
  let law := globallyTiltedStructuredMixtureLaw H A C Cmax
    n W eta hC_le hS weight
  have h := hbounds hS weight
  exact ⟨h.ji, h.ij, h.jj, h.diagonal, h.row⟩

end

end Erdos390.Full.PaperLemma75LiteralSeriesStatementAudit
