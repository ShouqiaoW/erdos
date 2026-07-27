import Erdos536.AlternativeBandCubeLaw
import Erdos536.OneCubeReduction

/-!
# Alternative-band certificates as one-coordinate approximations

This file packages the exact output required from the prime-band estimates.
The finite variance, pushforward, balance, tensor, cap-set, and arithmetic
reductions then turn such certificates into Erdős 536 automatically.
-/

namespace Erdos536

theorem FiniteCubeLaw.multiplicativelyBalanced_mono
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    {L : FiniteCubeLaw α H R} {δ η : ℝ}
    (hL : L.MultiplicativelyBalanced δ) (hδη : δ ≤ η) :
    L.MultiplicativelyBalanced η := by
  intro a ha ω τ
  have hbase := hL a ha ω τ
  have hprod :
      0 ≤
        (primeProduct ((L.cube a).wordSupport ω) : ℝ) :=
    Nat.cast_nonneg _
  exact hbase.trans
    (mul_le_mul_of_nonneg_right (by linarith : 1 + δ ≤ 1 + η) hprod)

/-- All finite data and estimates needed from a family of alternative prime
bands. -/
structure AlternativeBandCertificate
    (A M : ℕ) (η K : ℝ) where
  M_pos : 0 < M
  bands : Fin M → Finset ℕ
  events : ∀ j, FiveConfiguration (bands j) → Bool
  bands_prime : ∀ j, IsPrimeSupport (bands j)
  bands_above : ∀ j p, p ∈ bands j → A < p
  bands_disjoint : PairwiseDisjointBands bands
  events_havePetals : ∀ j, FiveEventHasPetals (bands j) (events j)
  events_positive :
    ∀ j, 0 < fiveEventMass (bands j) reciprocalBernoulli (events j)
  events_logBalanced :
    ∀ j, FiveEventPetalLogBalanced (bands j) (events j) η
  K_nonneg : 0 ≤ K
  rooted_secondMoment :
    ∀ j (s : Fin 3),
      rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight (bands j) reciprocalBernoulli)
        (rootedBayesDensity
          (fiveEventMass (bands j) reciprocalBernoulli (events j))
          (fiveRootLikelihood
            (bands j) reciprocalBernoulli (events j) s)) ≤ K

/-- A certificate supported above a larger cutoff is also a certificate
above any smaller cutoff. -/
def AlternativeBandCertificate.lowerCutoff_mono
    {A A' M : ℕ} {η K : ℝ}
    (hAA' : A ≤ A')
    (C : AlternativeBandCertificate A' M η K) :
    AlternativeBandCertificate A M η K where
  M_pos := C.M_pos
  bands := C.bands
  events := C.events
  bands_prime := C.bands_prime
  bands_above := by
    intro j p hp
    exact hAA'.trans_lt (C.bands_above j p hp)
  bands_disjoint := C.bands_disjoint
  events_havePetals := C.events_havePetals
  events_positive := C.events_positive
  events_logBalanced := C.events_logBalanced
  K_nonneg := C.K_nonneg
  rooted_secondMoment := C.rooted_secondMoment

/-- A certificate gives a one-coordinate approximation whenever its
variance and logarithmic errors meet the requested tolerances. -/
noncomputable def AlternativeBandCertificate.toBalancedCubeApproximation
    {A M : ℕ} {η K ε δ : ℝ}
    (C : AlternativeBandCertificate A M η K)
    (hε : Real.sqrt (K / (M : ℝ)) ≤ ε)
    (hδ : Real.exp η - 1 ≤ δ) :
    BalancedCubeApproximation 1 A ε δ where
  Sample := AlternativeBandSample C.bands C.events
  sampleDecidableEq :=
    alternativeBandSampleDecidableEq C.bands C.events
  primes := allBandSupport C.bands
  primes_prime :=
    isPrimeSupport_allBandSupport C.bands_prime
  primes_above := by
    intro p hp
    rw [allBandSupport, Finset.mem_biUnion] at hp
    obtain ⟨j, _hj, hpj⟩ := hp
    exact C.bands_above j p hpj
  law :=
    alternativeBandCubeLaw C.M_pos C.bands C.events
      C.bands_prime C.events_havePetals C.events_positive
      C.bands_disjoint
  marginal_close := by
    intro ω
    exact
      (alternativeBandCubeLaw_wordSupportDistance_le_all
        C.M_pos C.bands C.events C.bands_prime
        C.events_havePetals C.events_positive C.bands_disjoint
        C.K_nonneg C.rooted_secondMoment ω).trans hε
  balanced := by
    apply FiniteCubeLaw.multiplicativelyBalanced_mono
      (alternativeBandCubeLaw_multiplicativelyBalanced_exp_sub_one
        C.M_pos C.bands C.events C.bands_prime
        C.events_havePetals C.events_positive C.bands_disjoint
        C.events_logBalanced)
      hδ

/-- Existence of alternative-band certificates meeting every requested
one-coordinate tolerance. -/
def HasArbitrarilyGoodAlternativeBandCertificates : Prop :=
  ∀ (A : ℕ) (ε δ : ℝ), 0 < ε → 0 < δ →
    ∃ (M : ℕ) (η K : ℝ),
      Nonempty (AlternativeBandCertificate A M η K) ∧
      Real.sqrt (K / (M : ℝ)) ≤ ε ∧
      Real.exp η - 1 ≤ δ

theorem oneCubeApproximations_of_alternativeBandCertificates
    (hcert : HasArbitrarilyGoodAlternativeBandCertificates) :
    HasArbitrarilyGoodOneCubeApproximations := by
  intro A ε δ hε hδ
  obtain ⟨M, η, K, ⟨C⟩, hclose, hbalance⟩ :=
    hcert A ε δ hε hδ
  exact ⟨C.toBalancedCubeApproximation hclose hbalance⟩

/-- This is the final finite interface: proving the prime-band certificates
with their displayed first/second-moment estimates proves Erdős 536. -/
theorem mainTheorem_of_alternativeBandCertificates
    (hcert : HasArbitrarilyGoodAlternativeBandCertificates) :
    MainTheorem :=
  mainTheorem_of_oneCubeApproximations
    (oneCubeApproximations_of_alternativeBandCertificates hcert)

end Erdos536
