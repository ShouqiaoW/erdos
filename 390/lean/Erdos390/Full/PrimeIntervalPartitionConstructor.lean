import Erdos390.Full.PositiveCellTransfer

/-!
# Constructing the arithmetic prime partition from ordered cutoffs

This module removes the set-theoretic part of the interval certificate.
Given a finite monotone sequence of natural cutoffs from `W` to `floor y`
and one prime in every consecutive interval, it constructs the actual
`ArithmeticBandGeometry.Partition` and proves its `IntervalCertificate`.
The remaining analytic task for a concrete mesh is therefore exactly the
prime-existence statement for its explicit cutoffs.
-/

namespace Erdos390.Full.PrimeIntervalPartitionConstructor

noncomputable section

open ArithmeticModel ArithmeticBandGeometry PositiveCellTransfer

/-- A point strictly above the first cutoff and no larger than the last one
belongs to some consecutive interval. -/
theorem exists_fin_cell_of_endpoints
    {K p : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
    (hstart : cut 0 < p) (hend : p ≤ cut K) :
    ∃ j : Fin K, cut j.1 < p ∧ p ≤ cut (j.1 + 1) := by
  have hexists : ∃ k : ℕ, k < K ∧ p ≤ cut (k + 1) := by
    have hKone : 1 ≤ K := hK
    have heq : K - 1 + 1 = K := Nat.sub_add_cancel hKone
    refine ⟨K - 1, by omega, ?_⟩
    rw [heq]
    exact hend
  let k : ℕ := Nat.find hexists
  have hk := Nat.find_spec hexists
  refine ⟨⟨k, hk.1⟩, ?_, hk.2⟩
  by_cases hkzero : k = 0
  · simpa only [hkzero] using hstart
  · have hpred : k - 1 < k := by omega
    have hminimal := Nat.find_min hexists hpred
    by_contra hnot
    apply hminimal
    constructor
    · omega
    · have hp : p ≤ cut k := Nat.le_of_not_gt hnot
      have hkone : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hkzero
      have heq : k - 1 + 1 = k := Nat.sub_add_cancel hkone
      rw [heq]
      exact hp

/-- Consecutive cells of a monotone cutoff sequence are disjoint, so the
cell supplied above is unique. -/
theorem existsUnique_fin_cell_of_monotone_endpoints
    {K p : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
    (hcut : Monotone cut) (hstart : cut 0 < p) (hend : p ≤ cut K) :
    ∃! j : Fin K, cut j.1 < p ∧ p ≤ cut (j.1 + 1) := by
  obtain ⟨j, hj⟩ := exists_fin_cell_of_endpoints hK cut hstart hend
  refine ⟨j, hj, ?_⟩
  intro i hi
  apply Fin.ext
  by_contra hne
  rcases lt_or_gt_of_ne hne with hij | hji
  · have hsucc : i.1 + 1 ≤ j.1 := by omega
    have hbetween := hcut hsucc
    exact (Nat.not_lt_of_ge (hi.2.trans hbetween)) hj.1
  · have hsucc : j.1 + 1 ≤ i.1 := by omega
    have hbetween := hcut hsucc
    exact (Nat.not_lt_of_ge (hj.2.trans hbetween)) hi.1

section Constructor

variable {n W K : ℕ} (hK : 0 < K) (cut : ℕ → ℕ)
  (hcut : Monotone cut) (hcutZero : cut 0 = W)
  (hcutLast : cut K = yNat n)

include hK cut hcut hcutZero hcutLast

private theorem prime_has_unique_cell
    (p : BandPrime n W) :
    ∃! j : Fin K, cut j.1 < p.1 ∧ p.1 ≤ cut (j.1 + 1) := by
  apply existsUnique_fin_cell_of_monotone_endpoints hK cut hcut
  · rw [hcutZero]
    exact cutoff_lt_of_mem_primeBand p.2
  · rw [hcutLast]
    exact le_yNat_of_mem_primeBand p.2

/-- The unique interval index of an actual band prime. -/
def intervalBand (p : BandPrime n W) : Fin K :=
  Classical.choose (prime_has_unique_cell hK cut hcut hcutZero hcutLast p)

theorem intervalBand_spec (p : BandPrime n W) :
    cut (intervalBand hK cut hcut hcutZero hcutLast p).1 < p.1 ∧
      p.1 ≤ cut ((intervalBand hK cut hcut hcutZero hcutLast p).1 + 1) :=
  (Classical.choose_spec
    (prime_has_unique_cell hK cut hcut hcutZero hcutLast p)).1

theorem intervalBand_eq_iff (p : BandPrime n W) (j : Fin K) :
    intervalBand hK cut hcut hcutZero hcutLast p = j ↔
      cut j.1 < p.1 ∧ p.1 ≤ cut (j.1 + 1) := by
  let H := prime_has_unique_cell hK cut hcut hcutZero hcutLast p
  constructor
  · intro h
    rw [← h]
    exact intervalBand_spec hK cut hcut hcutZero hcutLast p
  · intro hj
    have hunique := (Classical.choose_spec H).2 j hj
    exact hunique.symm

omit hK in
/-- Every cutoff is between the first and last cutoffs. -/
theorem cutoff_bounds (j : Fin K) :
    W ≤ cut j.1 ∧ cut (j.1 + 1) ≤ yNat n := by
  constructor
  · rw [← hcutZero]
    exact hcut (Nat.zero_le j.1)
  · rw [← hcutLast]
    exact hcut (Nat.succ_le_iff.mpr j.2)

/-- Construct the arithmetic partition.  The only additional input is the
genuine prime-existence statement for every consecutive cutoff interval. -/
def partition
    (hprime : ∀ j : Fin K, ∃ p : ℕ,
      p.Prime ∧ cut j.1 < p ∧ p ≤ cut (j.1 + 1)) :
    ArithmeticBandGeometry.Partition n W (Fin K) where
  band := intervalBand hK cut hcut hcutZero hcutLast
  fiber_nonempty := by
    intro j
    obtain ⟨p, hpPrime, hpLower, hpUpper⟩ := hprime j
    have hb := cutoff_bounds cut hcut hcutZero hcutLast j
    have hpBand : p ∈ primeBand n W := mem_primeBand.mpr
      ⟨hpPrime, hb.1.trans_lt hpLower, hpUpper.trans hb.2⟩
    let q : BandPrime n W := ⟨p, hpBand⟩
    refine ⟨q, ?_⟩
    exact (intervalBand_eq_iff hK cut hcut hcutZero hcutLast q j).2
      ⟨hpLower, hpUpper⟩

/-- The interval certificate of the constructed partition is a theorem, not
an independent input. -/
def intervalCertificate
    (hprime : ∀ j : Fin K, ∃ p : ℕ,
      p.Prime ∧ cut j.1 < p ∧ p ≤ cut (j.1 + 1)) :
    IntervalCertificate
      (partition hK cut hcut hcutZero hcutLast hprime) where
  lower := fun j ↦ cut j.1
  upper := fun j ↦ cut (j.1 + 1)
  lower_le_upper := fun j ↦ hcut (Nat.le_succ j.1)
  cutoff_le_lower := fun j ↦
    (cutoff_bounds cut hcut hcutZero hcutLast j).1
  upper_le_yNat := fun j ↦
    (cutoff_bounds cut hcut hcutZero hcutLast j).2
  band_eq_iff := by
    intro p j
    exact intervalBand_eq_iff hK cut hcut hcutZero hcutLast p j

end Constructor

end

end Erdos390.Full.PrimeIntervalPartitionConstructor
