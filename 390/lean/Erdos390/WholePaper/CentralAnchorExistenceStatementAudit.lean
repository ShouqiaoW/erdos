import Erdos390.WholePaper.CentralAnchorExistence

/-! # Expanded statement audit for eventual central-anchor existence -/

open Filter
open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

example {c : ℝ} (hc : C0 < c) :
    ∃ R : ℕ, 201 ≤ R ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ q : ℕ → ℕ, ∃ anchors : Finset ℕ,
          IsLargeCentralCofactorChoice n (n / (R + 1)) q ∧
          anchors = fullCentralAnchors n (n / (R + 1)) q ∧
          anchors ⊆ Finset.Ioc n (2 * n) ∧
          anchors.prod id =
            Nat.choose (2 * n) n *
              centralAnchorDivisor n (n / (R + 1)) q ∧
          (∀ ℓ : ℕ, ℓ.Prime →
            ℓ ∣ centralAnchorDivisor n (n / (R + 1)) q →
              ℓ ∈ primesUpTo (2 * R + 1)) ∧
          (∀ ℓ ∈ primesUpTo (2 * R + 1),
            (c - C0) / (3 * (((ℓ - 1 : ℕ) : ℝ))) *
                  ((n : ℝ) / Real.log (n : ℝ)) +
                ((centralAnchorDivisor n
                  (n / (R + 1)) q).factorization ℓ : ℝ) ≤
              (upperTailValuation c n ℓ : ℝ)) ∧
          centralAnchorDivisor n (n / (R + 1)) q ∣
            centralTailProduct n
              (Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ)))) := by
  obtain ⟨R, hR, hcertificates⟩ :=
    exists_eventually_centralAnchorCertificate hc
  refine ⟨R, hR, ?_⟩
  filter_upwards [hcertificates] with n hcertificate
  obtain ⟨certificate⟩ := hcertificate
  refine ⟨certificate.q, certificate.anchors,
    ?_, ?_, certificate.anchors_subset, ?_, ?_, ?_, ?_⟩
  · simpa only [centralAnchorCutoff] using certificate.isCofactorChoice
  · simpa only [centralAnchorCutoff] using certificate.anchors_eq
  · simpa only [centralAnchorCutoff] using certificate.anchors_prod
  · simpa only [centralAnchorCutoff] using
      certificate.divisor_prime_support
  · simpa only [centralAnchorCutoff, secondOrderScale] using
      certificate.divisor_reserve
  · simpa only [centralAnchorCutoff, upperTailLength,
      secondOrderScale] using certificate.divisor_dvd_tail

end

end Erdos390.WholePaper
