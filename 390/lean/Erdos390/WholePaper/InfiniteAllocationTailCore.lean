import Erdos390.WholePaper.LeastPrimeTail
import Erdos390.WholePaper.Constants

/-!
# Finite-support algebra for the least-prime allocation tail

This module contains the part of Lemma 4.2 that is independent of the
large finite certificate.  Keeping that certificate out of this import
chain materially reduces elaboration memory for the reusable tail lemmas.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The least-prime tail used from row `201` onward. -/
def tailAllocation (r q : ℕ) : ℚ :=
  if 201 ≤ r ∧ q = leastPrimeAbove r then alpha r else 0

/-- One row's contribution to the valuation load at `ℓ`. -/
def allocationPrimeRowLoad (x : ℕ → ℕ → ℚ) (ℓ r : ℕ) : ℚ :=
  ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
    (q.factorization ℓ : ℚ) * x r q

/-- The full valuation load of an infinite allocation. -/
def allocationPrimeLoad (x : ℕ → ℕ → ℚ) (ℓ : ℕ) : ℚ :=
  ∑' r : ℕ, allocationPrimeRowLoad x ℓ r

def tailPrimeRowLoad (ℓ r : ℕ) : ℚ :=
  allocationPrimeRowLoad tailAllocation ℓ r

theorem alpha_pos (r : ℕ) : 0 < alpha r := by
  rw [alpha]
  positivity

theorem tailAllocation_nonneg (r q : ℕ) :
    0 ≤ tailAllocation r q := by
  by_cases htail : 201 ≤ r ∧ q = leastPrimeAbove r
  · simp only [tailAllocation, if_pos htail]
    exact (alpha_pos r).le
  · simp [tailAllocation, htail]

/-- A tail row contributes only to the prime selected by its least-prime
route. -/
theorem tailPrimeRowLoad_eq (ℓ r : ℕ) :
    tailPrimeRowLoad ℓ r =
      if 201 ≤ r ∧ leastPrimeAbove r = ℓ then alpha r else 0 := by
  classical
  by_cases hr : 201 ≤ r
  · have hr1 : 1 ≤ r := by omega
    have hleastMem := leastPrimeAbove_mem_allocationRange hr1
    rw [tailPrimeRowLoad, allocationPrimeRowLoad]
    calc
      (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          (q.factorization ℓ : ℚ) * tailAllocation r q) =
          ((leastPrimeAbove r).factorization ℓ : ℚ) * alpha r := by
        rw [Finset.sum_eq_single (leastPrimeAbove r)]
        · simp [tailAllocation, hr]
        · intro q _hq hqne
          simp [tailAllocation, hqne]
        · exact fun hnot ↦ (hnot hleastMem).elim
      _ = if 201 ≤ r ∧ leastPrimeAbove r = ℓ then alpha r else 0 := by
        rw [(leastPrimeAbove_prime r).factorization]
        by_cases hℓ : leastPrimeAbove r = ℓ
        · simp [hr, hℓ]
        · simp [hr, hℓ]
  · simp [tailPrimeRowLoad, allocationPrimeRowLoad, tailAllocation, hr]

/-- For a fixed prime coordinate, all tail rows outside
`[201, ℓ - 1]` vanish. -/
theorem tsum_tailPrimeRowLoad_eq (ℓ : ℕ) :
    (∑' r : ℕ, tailPrimeRowLoad ℓ r) =
      ∑ r ∈ Finset.Icc 201 (ℓ - 1),
        if leastPrimeAbove r = ℓ then alpha r else 0 := by
  rw [tsum_eq_sum (s := Finset.Icc 201 (ℓ - 1))]
  · apply Finset.sum_congr rfl
    intro r hr
    have hr201 := (Finset.mem_Icc.mp hr).1
    rw [tailPrimeRowLoad_eq]
    simp [hr201]
  · intro r hr
    rw [tailPrimeRowLoad_eq]
    by_cases hr201 : 201 ≤ r
    · have hroute : leastPrimeAbove r ≠ ℓ := by
        intro hroute
        apply hr
        exact Finset.mem_Icc.mpr ⟨hr201, by
          have := lt_leastPrimeAbove r
          omega⟩
      simp [hr201, hroute]
    · simp [hr201]

theorem summable_tailPrimeRowLoad (ℓ : ℕ) :
    Summable (tailPrimeRowLoad ℓ) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 201 (ℓ - 1))
  intro r hr
  rw [tailPrimeRowLoad_eq]
  by_cases hr201 : 201 ≤ r
  · have hroute : leastPrimeAbove r ≠ ℓ := by
      intro hroute
      apply hr
      exact Finset.mem_Icc.mpr ⟨hr201, by
        have := lt_leastPrimeAbove r
        omega⟩
    simp [hr201, hroute]
  · simp [hr201]

/-- Consecutive-prime routing turns the tail `tsum` into the literal block
used by the finite overlap certificate and the Nagura estimate. -/
theorem tsum_tailPrimeRowLoad_eq_consecutiveBlock
    {pPrev p : ℕ} (hpPrev : pPrev.Prime) (hp : p.Prime)
    (hPrevP : pPrev < p)
    (hNoBetween : ∀ q : ℕ, q.Prime → pPrev < q → q < p → False) :
    (∑' r : ℕ, tailPrimeRowLoad p r) =
      ∑ r ∈ Finset.Icc (max 201 pPrev) (p - 1), alpha r := by
  rw [tsum_tailPrimeRowLoad_eq]
  have hfilter :
      (Finset.Icc 201 (p - 1)).filter
          (fun r ↦ leastPrimeAbove r = p) =
        Finset.Icc (max 201 pPrev) (p - 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc,
      leastPrimeAbove_eq_of_consecutivePrimes hpPrev hp hPrevP hNoBetween]
    omega
  have hsum := congrArg (fun s : Finset ℕ ↦ ∑ r ∈ s, alpha r) hfilter
  simpa only [Finset.sum_filter] using hsum

end

end Erdos390.WholePaper
