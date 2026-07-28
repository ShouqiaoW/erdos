import Erdos390.WholePaper.BankGuardedCentralAnchorExistence

open Filter Topology

namespace Erdos390.WholePaper

example {c : ℝ} (hc : (4029639598 : ℝ) / 25970038185 < c) :
    ∃ depth : ℕ, 201 ≤ depth ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ bank : BankPaperRealization n
            (2 * n + Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ)))),
          ∃ q' : ℕ → ℕ, ∃ anchors' : Finset ℕ,
            IsLargeCentralCofactorChoice n (n / (depth + 1)) q' ∧
            anchors' = fullCentralAnchors n (n / (depth + 1)) q' ∧
            anchors' ⊆ Finset.Ioc n (2 * n) ∧
            anchors'.prod id = Nat.choose (2 * n) n *
              centralAnchorDivisor n (n / (depth + 1)) q' ∧
            (∀ ℓ : ℕ, ℓ.Prime →
              ℓ ∣ centralAnchorDivisor n (n / (depth + 1)) q' →
                ℓ ∈ primesUpTo (2 * depth + 1)) ∧
            (∀ ℓ ∈ primesUpTo (2 * depth + 1),
              (c - (4029639598 : ℝ) / 25970038185) /
                    (6 * (((ℓ - 1 : ℕ) : ℝ))) *
                    ((n : ℝ) / Real.log (n : ℝ)) +
                  ((centralAnchorDivisor n
                    (n / (depth + 1)) q').factorization ℓ : ℝ) ≤
                (upperTailValuation c n ℓ : ℝ)) ∧
            centralAnchorDivisor n (n / (depth + 1)) q' ∣
              centralTailProduct n
                (Nat.ceil (c * ((n : ℝ) / Real.log (n : ℝ)))) ∧
            ∀ p ∈ bank.allMarkers ∩
                largeCentralPrimes n (n / (depth + 1)),
              q' p ≠ (bank.anchorGuardIncidentCores p).1 ∧
                q' p ≠ (bank.anchorGuardIncidentCores p).2 := by
  obtain ⟨depth, hdepth, hterminal⟩ :=
    exists_eventually_bankGuardedCentralAnchorCertificate
      (by simpa only [C0] using hc)
  refine ⟨depth, hdepth, ?_⟩
  filter_upwards [hterminal] with n hn
  obtain ⟨bank, ⟨certificate⟩⟩ := hn
  refine ⟨bank, certificate.q, certificate.anchors,
    certificate.isCofactorChoice, certificate.anchors_eq,
    certificate.anchors_subset, certificate.anchors_prod,
    certificate.divisor_prime_support, ?_, certificate.divisor_dvd_tail,
    certificate.guarded_incident_cores⟩
  simpa only [C0, secondOrderScale, centralAnchorCutoff,
    upperTailLength, upperEndpoint,
    BankPaperRealization.centralChangedMarkers,
    BankPaperRealization.anchorGuardLeftCore,
    BankPaperRealization.anchorGuardRightCore] using
      certificate.divisor_reserve

end Erdos390.WholePaper
