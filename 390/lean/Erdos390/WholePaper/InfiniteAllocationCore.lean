import Erdos390.WholePaper.AllocationCertificate
import Erdos390.WholePaper.InfiniteAllocationTailCore

/-!
# The exact infinite cofactor array: structural layer

This file splices the 200 finite certificate rows to the least-prime tail.
It proves nonnegativity, the permitted cofactor support, every exact row
identity, and finite-support formulas for each prime load.  The capacity
inequalities are instantiated in `InfiniteAllocation.lean`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The literal infinite array in Lemma 4.2 of the paper. -/
def infiniteAllocation (r q : ℕ) : ℚ :=
  finiteAllocation r q + tailAllocation r q

def finitePrimeRowLoad (ℓ r : ℕ) : ℚ :=
  allocationPrimeRowLoad finiteAllocation ℓ r


theorem finiteAllocation_nonneg (r q : ℕ) :
    0 ≤ finiteAllocation r q := by
  classical
  by_cases hrq : (r, q) ∈ finiteAllocationSupport
  · exact (finiteAllocation_pos_of_mem hrq).le
  · rw [finiteAllocation_eq_zero_of_not_mem hrq]

theorem infiniteAllocation_nonneg (r q : ℕ) :
    0 ≤ infiniteAllocation r q := by
  exact add_nonneg (finiteAllocation_nonneg r q)
    (tailAllocation_nonneg r q)

/-- Every nonzero coordinate lies in the cofactor interval prescribed by
the paper. -/
theorem infiniteAllocation_eq_zero_of_not_mem_allocationRange
    {r q : ℕ} (hr : 1 ≤ r)
    (hq : q ∉ Finset.Icc (r + 1) (2 * r + 1)) :
    infiniteAllocation r q = 0 := by
  have hfinite : finiteAllocation r q = 0 := by
    apply finiteAllocation_eq_zero_of_not_mem
    intro hrq
    exact hq (Finset.mem_Icc.mpr
      ⟨(finiteAllocation_support_valid hrq).2.2.1,
        (finiteAllocation_support_valid hrq).2.2.2⟩)
  have htail : ¬(201 ≤ r ∧ q = leastPrimeAbove r) := by
    rintro ⟨_, rfl⟩
    exact hq (leastPrimeAbove_mem_allocationRange hr)
  simp [infiniteAllocation, tailAllocation, hfinite, htail]

/-- Every row has exactly the mass `alpha r`. -/
theorem infiniteAllocation_row_identity {r : ℕ} (hr : 1 ≤ r) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        infiniteAllocation r q) = alpha r := by
  classical
  by_cases hr200 : r ≤ 200
  · have hnot201 : ¬201 ≤ r := by omega
    simpa [infiniteAllocation, tailAllocation, hnot201] using
      finiteAllocation_row_identity hr hr200
  · have h201 : 201 ≤ r := by omega
    have hfiniteZero (q : ℕ) : finiteAllocation r q = 0 := by
      apply finiteAllocation_eq_zero_of_not_mem
      intro hrq
      exact hr200 (finiteAllocation_support_valid hrq).2.1
    have hleastMem := leastPrimeAbove_mem_allocationRange hr
    calc
      (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          infiniteAllocation r q) =
          ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
            if q = leastPrimeAbove r then alpha r else 0 := by
        apply Finset.sum_congr rfl
        intro q _hq
        rw [infiniteAllocation, hfiniteZero q, zero_add, tailAllocation]
        simp [h201]
      _ = alpha r := by
        rw [Finset.sum_eq_single (leastPrimeAbove r)]
        · simp
        · intro q _hq hqne
          simp [hqne]
        · exact fun hnot ↦ (hnot hleastMem).elim

/-- The finite part of a fixed prime load is literally the checked finite
certificate load. -/
theorem tsum_finitePrimeRowLoad_eq ( ℓ : ℕ) :
    (∑' r : ℕ, finitePrimeRowLoad ℓ r) = finitePrimeLoad ℓ := by
  rw [tsum_eq_sum (s := Finset.Icc 1 200)]
  · exact (finitePrimeLoad_eq_coordinate_sum ℓ).symm
  · intro r hr
    rw [finitePrimeRowLoad, allocationPrimeRowLoad]
    apply Finset.sum_eq_zero
    intro q _hq
    rw [finiteAllocation_eq_zero_of_not_mem]
    · simp
    · intro hrq
      exact hr (Finset.mem_Icc.mpr
        ⟨(finiteAllocation_support_valid hrq).1,
          (finiteAllocation_support_valid hrq).2.1⟩)

theorem summable_finitePrimeRowLoad (ℓ : ℕ) :
    Summable (finitePrimeRowLoad ℓ) := by
  apply summable_of_ne_finset_zero (s := Finset.Icc 1 200)
  intro r hr
  rw [finitePrimeRowLoad, allocationPrimeRowLoad]
  apply Finset.sum_eq_zero
  intro q _hq
  rw [finiteAllocation_eq_zero_of_not_mem]
  · simp
  · intro hrq
    exact hr (Finset.mem_Icc.mpr
      ⟨(finiteAllocation_support_valid hrq).1,
        (finiteAllocation_support_valid hrq).2.1⟩)

theorem infinitePrimeRowLoad_eq_add (ℓ r : ℕ) :
    allocationPrimeRowLoad infiniteAllocation ℓ r =
      finitePrimeRowLoad ℓ r + tailPrimeRowLoad ℓ r := by
  simp only [allocationPrimeRowLoad, finitePrimeRowLoad, tailPrimeRowLoad,
    infiniteAllocation, mul_add, Finset.sum_add_distrib]

/-- The full load splits exactly into the finite certificate load and the
least-prime tail load. -/
theorem allocationPrimeLoad_infiniteAllocation_eq (ℓ : ℕ) :
    allocationPrimeLoad infiniteAllocation ℓ =
      finitePrimeLoad ℓ + ∑' r : ℕ, tailPrimeRowLoad ℓ r := by
  rw [allocationPrimeLoad]
  simp_rw [infinitePrimeRowLoad_eq_add]
  rw [(summable_finitePrimeRowLoad ℓ).tsum_add
      (summable_tailPrimeRowLoad ℓ),
    tsum_finitePrimeRowLoad_eq]

end

end Erdos390.WholePaper
