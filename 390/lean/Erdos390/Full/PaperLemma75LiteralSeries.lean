import Erdos390.Full.FixedFiniteMixtureGlobalTiltLemma75

/-!
# Literal unrestricted-series form of paper Lemma 7.5

The paper writes the three prime-power displays with `k,l >= 2`, without an
explicit upper cutoff.  The finite arithmetic development uses the exact
logarithmic cutoff `valuationCutoff p M`.  This file closes the small statement
fidelity gap between those two presentations: every divisibility column above
the logarithmic cutoff is identically zero on a positive integer-valued law
bounded by `M`, so the unrestricted `tsum`s are exactly the finite sums already
proved in `PrimePowerTransferBounds`.

No summability hypothesis is needed: the relevant functions have finite
support, and that fact is proved below from the literal divisibility columns.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.PaperLemma75LiteralSeries

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PrimePowerCovariance.BoundedValuationLaw
open ValuationCutoff PaperPrimePowerLemma75
open FixedFiniteMixtureGlobalTiltLemma75

noncomputable section

/-- Above the logarithmic arithmetic cutoff, the literal `p^k` divisibility
column vanishes pointwise on every positive sample bounded by `M`. -/
theorem BoundedValuationLaw.Ip_eq_zero_of_cutoff_lt
    {Omega : Type*} [Fintype Omega] {M p k : ℕ}
    (law : BoundedValuationLaw Omega M) (hp : p.Prime)
    (hk : valuationCutoff p M < k) :
    law.Ip p k = 0 := by
  funext omega
  unfold BoundedValuationLaw.Ip ArithmeticModel.divInd
  have hnot : ¬ p ^ k ∣ law.value omega := by
    intro hdvd
    have hkfac : k ≤ (law.value omega).factorization p :=
      (hp.pow_dvd_iff_le_factorization (law.value_pos omega).ne').mp hdvd
    have hfacCut : (law.value omega).factorization p ≤
        valuationCutoff p M :=
      factorization_le_valuationCutoff hp (law.value_pos omega)
        (law.value_le omega)
    omega
  simp only [hnot, if_false, Pi.zero_apply]

/-- The unrestricted `k >= 2` absolute `JI` series is exactly the finite
logarithmic-cutoff sum used by the arithmetic proof. -/
theorem BoundedValuationLaw.tsum_abs_covIpI_eq_cutoff_sum
    {Omega : Type*} [Fintype Omega] {M p q : ℕ}
    (law : BoundedValuationLaw Omega M) (hp : p.Prime) :
    (∑' k : ℕ, if 2 ≤ k then
        |law.probability.covariance (law.Ip p k) (law.I q)| else 0) =
      ∑ k ∈ highExponents (valuationCutoff p M),
        |law.probability.covariance (law.Ip p k) (law.I q)| := by
  rw [tsum_eq_sum (s := highExponents (valuationCutoff p M))]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos (mem_highExponents.mp hk).1]
  · intro k hk
    rw [mem_highExponents] at hk
    by_cases hk2 : 2 ≤ k
    · have hcut : valuationCutoff p M < k := by omega
      rw [if_pos hk2, Ip_eq_zero_of_cutoff_lt law hp hcut]
      simp [FiniteProbability.covariance, FiniteProbability.expect]
    · simp [hk2]

/-- The unrestricted `l >= 2` absolute `IJ` series is exactly its finite
logarithmic-cutoff sum. -/
theorem BoundedValuationLaw.tsum_abs_covIIp_eq_cutoff_sum
    {Omega : Type*} [Fintype Omega] {M p q : ℕ}
    (law : BoundedValuationLaw Omega M) (hq : q.Prime) :
    (∑' l : ℕ, if 2 ≤ l then
        |law.probability.covariance (law.I p) (law.Ip q l)| else 0) =
      ∑ l ∈ highExponents (valuationCutoff q M),
        |law.probability.covariance (law.I p) (law.Ip q l)| := by
  rw [tsum_eq_sum (s := highExponents (valuationCutoff q M))]
  · apply Finset.sum_congr rfl
    intro l hl
    rw [if_pos (mem_highExponents.mp hl).1]
  · intro l hl
    rw [mem_highExponents] at hl
    by_cases hl2 : 2 ≤ l
    · have hcut : valuationCutoff q M < l := by omega
      rw [if_pos hl2, Ip_eq_zero_of_cutoff_lt law hq hcut]
      simp [FiniteProbability.covariance, FiniteProbability.expect]
    · simp [hl2]

/-- The unrestricted two-index `k,l >= 2` absolute `JJ` series is exactly
the product of the two finite logarithmic-cutoff ranges. -/
theorem BoundedValuationLaw.tsum_abs_covIpIp_eq_cutoff_sum
    {Omega : Type*} [Fintype Omega] {M p q : ℕ}
    (law : BoundedValuationLaw Omega M) (hp : p.Prime) (hq : q.Prime) :
    (∑' kl : ℕ × ℕ, if 2 ≤ kl.1 ∧ 2 ≤ kl.2 then
        |law.probability.covariance (law.Ip p kl.1) (law.Ip q kl.2)| else 0) =
      ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          |law.probability.covariance (law.Ip p k) (law.Ip q l)| := by
  rw [tsum_eq_sum
    (s := (highExponents (valuationCutoff p M)).product
      (highExponents (valuationCutoff q M)))]
  · calc
      _ = ∑ kl ∈ (highExponents (valuationCutoff p M)).product
            (highExponents (valuationCutoff q M)),
            |law.probability.covariance
              (law.Ip p kl.1) (law.Ip q kl.2)| := by
          apply Finset.sum_congr rfl
          intro kl hkl
          obtain ⟨hk, hl⟩ := Finset.mem_product.mp hkl
          rw [if_pos ⟨(mem_highExponents.mp hk).1,
            (mem_highExponents.mp hl).1⟩]
      _ = _ := by
          simpa only using Finset.sum_product
            (highExponents (valuationCutoff p M))
            (highExponents (valuationCutoff q M))
            (fun kl : ℕ × ℕ ↦
              |law.probability.covariance
                (law.Ip p kl.1) (law.Ip q kl.2)|)
  · intro kl hkl
    have houtside : ¬
        (kl.1 ∈ highExponents (valuationCutoff p M) ∧
          kl.2 ∈ highExponents (valuationCutoff q M)) := by
      intro hin
      exact hkl (Finset.mem_product.mpr hin)
    by_cases hk2 : 2 ≤ kl.1
    · by_cases hl2 : 2 ≤ kl.2
      · rw [if_pos ⟨hk2, hl2⟩]
        rcases not_and_or.mp houtside with hk | hl
        · rw [mem_highExponents] at hk
          have hcut : valuationCutoff p M < kl.1 := by omega
          rw [Ip_eq_zero_of_cutoff_lt law hp hcut]
          simp [FiniteProbability.covariance, FiniteProbability.expect]
        · rw [mem_highExponents] at hl
          have hcut : valuationCutoff q M < kl.2 := by omega
          rw [Ip_eq_zero_of_cutoff_lt law hq hcut]
          simp [FiniteProbability.covariance, FiniteProbability.expect]
      · simp [hl2]
    · simp [hk2]

/-- The five conclusions of Lemma 7.5 with the paper's unrestricted
`k,l >= 2` notation.  The endpoint terms have already been absorbed into
the single common vanishing remainder, which is a stronger formulation of
the displayed `O_{B,W}` endpoint errors. -/
structure LiteralPrimePowerTransferBounds
    {Omega : Type*} [Fintype Omega] {M : ℕ}
    (law : BoundedValuationLaw Omega M) (n W : ℕ)
    (C_pow epsilon_BW : ℝ) : Prop where
  ji : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑' k : ℕ, if 2 ≤ k then
      |law.probability.covariance (law.Ip p k) (law.I q)| else 0) ≤
        (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ))
  ij : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑' l : ℕ, if 2 ≤ l then
      |law.probability.covariance (law.I p) (law.Ip q l)| else 0) ≤
        (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
          (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2
  jj : ∀ p ∈ primeBand n W, ∀ q ∈ (primeBand n W).erase p,
    (∑' kl : ℕ × ℕ, if 2 ≤ kl.1 ∧ 2 ≤ kl.2 then
      |law.probability.covariance (law.Ip p kl.1) (law.Ip q kl.2)| else 0) ≤
        (C_pow * tPrime n p * tPrime n q + epsilon_BW) *
          (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2
  diagonal : ∀ p ∈ primeBand n W,
    law.probability.expect (fun omega ↦ law.J p omega ^ 2) ≤
      (C_pow + epsilon_BW) * (1 / (p : ℝ)) ^ 2
  row : ∀ p ∈ primeBand n W,
    (p : ℝ) * ∑ q ∈ primeBand n W,
      |law.covVV p q - law.covII p q| ≤
        C_pow * (1 / (W : ℝ)) + epsilon_BW

/-- The cutoff-form result already proved in the arithmetic development
implies the literal unrestricted-series statement, with no change of any
constant or remainder. -/
theorem PrimePowerTransferBounds.toLiteral
    {Omega : Type*} [Fintype Omega] {M n W : ℕ}
    {law : BoundedValuationLaw Omega M} {C_pow epsilon_BW : ℝ}
    (h : PrimePowerTransferBounds law n W C_pow epsilon_BW) :
    LiteralPrimePowerTransferBounds law n W C_pow epsilon_BW := by
  refine {
    ji := ?_
    ij := ?_
    jj := ?_
    diagonal := h.diagonal
    row := h.row }
  · intro p hp q hq
    rw [Erdos390.Full.PaperLemma75LiteralSeries.BoundedValuationLaw.tsum_abs_covIpI_eq_cutoff_sum law
      (prime_of_mem_primeBand hp)]
    exact h.ji p hp q hq
  · intro p hp q hq
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hq).2
    rw [Erdos390.Full.PaperLemma75LiteralSeries.BoundedValuationLaw.tsum_abs_covIIp_eq_cutoff_sum law
      (prime_of_mem_primeBand hqBand)]
    exact h.ij p hp q hq
  · intro p hp q hq
    have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hq).2
    rw [Erdos390.Full.PaperLemma75LiteralSeries.BoundedValuationLaw.tsum_abs_covIpIp_eq_cutoff_sum law
      (prime_of_mem_primeBand hp) (prime_of_mem_primeBand hqBand)]
    exact h.jj p hp q hq

variable {Cell : Type*} [Fintype Cell]

/-- **Paper Lemma 7.5, literal unrestricted-series global-tilt export.**

This has the same parameter order and the same literal globally tilted finite
mixture as `exists_boxIndependent_globalTilt_primePower_transfer`, but its
three prime-power conclusions are now written exactly with unrestricted
`k,l >= 2` series as in the paper. -/
theorem boxIndependent_globalTilt_primePower_transfer_literal
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hCmax : 0 < Cmax)
    (hC_le : ∀ c, C c ≤ Cmax) :
    0 < FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant ∧
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
              LiteralPrimePowerTransferBounds
                (globallyTiltedStructuredMixtureLaw H A C Cmax n W eta
                  hC_le hS weight)
                n W FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant
                  (epsilon_BW n) := by
  obtain ⟨hCpow, hmain⟩ :=
    boxIndependent_globalTilt_primePower_transfer
      H A C Cmax hA hAC hC hCmax hC_le
  refine ⟨hCpow, ?_⟩
  intro W hW hsupport B hB
  obtain ⟨epsilon_BW, hepsilon0, hepsilonT, hepsilonRate, N₀, hN₀⟩ :=
    hmain W hW hsupport B hB
  refine ⟨epsilon_BW, hepsilon0, hepsilonT, hepsilonRate, N₀, ?_⟩
  intro n eta hn heta
  obtain ⟨hS, hbounds⟩ := hN₀ eta hn heta
  refine ⟨hS, ?_⟩
  intro hS weight
  exact PrimePowerTransferBounds.toLiteral (hbounds hS weight)

/-- Existential form of the literal result.  Its witness is the named
universal constant above, so this wrapper does not weaken the formal
dependency order. -/
theorem exists_boxIndependent_globalTilt_primePower_transfer_literal
    (H : Cell → Pattern) (A C : Cell → ℝ) (Cmax : ℝ)
    (hA : ∀ c, 0 < A c) (hAC : ∀ c, A c < C c)
    (hC : ∀ c, 0 < C c) (hCmax : 0 < Cmax)
    (hC_le : ∀ c, C c ≤ Cmax) :
    ∃ C_pow : ℝ, 0 < C_pow ∧
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
              LiteralPrimePowerTransferBounds
                (globallyTiltedStructuredMixtureLaw H A C Cmax n W eta
                  hC_le hS weight)
                n W C_pow (epsilon_BW n) := by
  obtain ⟨hCpow, hmain⟩ :=
    boxIndependent_globalTilt_primePower_transfer_literal
      H A C Cmax hA hAC hC hCmax hC_le
  exact ⟨FixedFiniteMixtureFullUniform.boxIndependentPrimePowerConstant,
    hCpow, hmain⟩

end

end Erdos390.Full.PaperLemma75LiteralSeries
