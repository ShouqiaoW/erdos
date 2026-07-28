import Erdos390.WholePaper.SafeShortIntervalPrimeCounting

/-! # Expanded statement audit for safe moving short-interval prime counting -/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

example (n : ℕ) :
    SafePrimeCounting.shortIntervalPrimeScale n =
      ((n : ℝ) / Real.log (n : ℝ)) / Real.log (n : ℝ) := rfl

example {lower upper : ℕ → ℕ} {a delta : ℝ} (ha : 0 < a)
    (hlower : Tendsto
      (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hupper : Tendsto
      (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hgap : Tendsto
      (fun n : ℕ ↦ ((upper n : ℝ) - (lower n : ℝ)) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds delta))
    (horder : ∀ᶠ n : ℕ in atTop, lower n ≤ upper n) :
    Tendsto
      (fun n : ℕ ↦
        (((Finset.Ioc (lower n) (upper n)).filter Nat.Prime).card : ℝ) /
          (((n : ℝ) / Real.log (n : ℝ)) / Real.log (n : ℝ)))
      atTop (nhds delta) := by
  simpa only [SafePrimeCounting.shortIntervalPrimeScale,
    secondOrderScale] using
      SafePrimeCounting.prime_Ioc_shortMovingInterval_normalized_tendsto
        ha hlower hupper (by simpa only [secondOrderScale] using hgap) horder

example {lower upper : ℕ → ℕ} {a delta : ℝ} (ha : 0 < a)
    (hlower : Tendsto
      (fun n : ℕ ↦ (lower n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hupper : Tendsto
      (fun n : ℕ ↦ (upper n : ℝ) / (n : ℝ)) atTop (nhds a))
    (hgap : Tendsto
      (fun n : ℕ ↦ ((upper n : ℝ) - (lower n : ℝ)) /
        ((n : ℝ) / Real.log (n : ℝ))) atTop (nhds delta))
    (horder : ∀ᶠ n : ℕ in atTop, lower n ≤ upper n) :
    Tendsto
      (fun n : ℕ ↦
        ((Nat.primeCounting (upper n) - Nat.primeCounting (lower n) : ℕ) : ℝ) /
          (((n : ℝ) / Real.log (n : ℝ)) / Real.log (n : ℝ)))
      atTop (nhds delta) := by
  simpa only [SafePrimeCounting.shortIntervalPrimeScale,
    secondOrderScale] using
      SafePrimeCounting.primeCounting_sub_shortMovingInterval_normalized_tendsto
        ha hlower hupper (by simpa only [secondOrderScale] using hgap) horder

end

end Erdos390.WholePaper
