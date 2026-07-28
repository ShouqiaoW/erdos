import Erdos390.WholePaper.CentralAnchorGuardedCertificate

namespace Erdos390.WholePaper

example
    {c : ℝ} {R n : ℕ} {left right : ℕ → ℕ}
    {changed : Finset ℕ}
    (hc : C0 < c) (hR : 1 ≤ R)
    (hnCutoff : centralAnchorCutoffThreshold R ≤ n)
    (certificate : CentralAnchorCertificate c R n)
    (hchanged : changed ⊆ largeCentralPrimes n (n / (R + 1)))
    (hchangedLe : ∀ p ∈ changed, p ≤ n)
    (hrowOneAvoid : ∀ p ∈ changed, n / p = 1 →
      3 ≠ left p ∧ 3 ≠ right p)
    (hchangeCost : ∀ ℓ ∈ primesUpTo (2 * R + 1),
      ((changed.card * Nat.log 2 (2 * R + 1) : ℕ) : ℝ) ≤
        (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
          secondOrderScale n) :
    ∃ q' : ℕ → ℕ, ∃ anchors' : Finset ℕ,
      IsLargeCentralCofactorChoice n (n / (R + 1)) q' ∧
      anchors' = fullCentralAnchors n (n / (R + 1)) q' ∧
      anchors' ⊆ Finset.Ioc n (2 * n) ∧
      anchors'.prod id = Nat.choose (2 * n) n *
        centralAnchorDivisor n (n / (R + 1)) q' ∧
      (∀ ℓ : ℕ, ℓ.Prime →
        ℓ ∣ centralAnchorDivisor n (n / (R + 1)) q' →
          ℓ ∈ primesUpTo (2 * R + 1)) ∧
      (∀ ℓ ∈ primesUpTo (2 * R + 1),
        (c - C0) / (6 * (((ℓ - 1 : ℕ) : ℝ))) *
              secondOrderScale n +
            ((centralAnchorDivisor n
              (n / (R + 1)) q').factorization ℓ : ℝ) ≤
          (upperTailValuation c n ℓ : ℝ)) ∧
      centralAnchorDivisor n (n / (R + 1)) q' ∣
        centralTailProduct n (upperTailLength c n) ∧
      ∀ p ∈ changed, q' p ≠ left p ∧ q' p ≠ right p := by
  obtain ⟨cert⟩ := guardedCentralAnchorCertificate_of_changeCost
    hc hR hnCutoff certificate hchanged hchangedLe hrowOneAvoid hchangeCost
  exact ⟨cert.q, cert.anchors, cert.isCofactorChoice, cert.anchors_eq,
    cert.anchors_subset, cert.anchors_prod, cert.divisor_prime_support,
    cert.divisor_reserve, cert.divisor_dvd_tail,
    cert.guarded_incident_cores⟩

end Erdos390.WholePaper
