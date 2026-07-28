import Erdos390.WholePaper.FloatingRounding

/-!
# Prime-power columns for floating rounding

The columns used in the paper are indexed by prime powers `p^j ≤ M`.  A
positive integer `a ≤ M` belongs to exactly one column for each prime-factor
occurrence, and hence to at most `Nat.log 2 M` columns.
-/

namespace Erdos390.WholePaper

noncomputable section

def primePowerColumns (M : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 2 M).product (Finset.Icc 1 M)).filter fun q ↦
    q.1.Prime ∧ q.1 ^ q.2 ≤ M

@[simp]
theorem mem_primePowerColumns {M p j : ℕ} :
    (p, j) ∈ primePowerColumns M ↔
      2 ≤ p ∧ p ≤ M ∧ 1 ≤ j ∧ j ≤ M ∧ p.Prime ∧ p ^ j ≤ M := by
  classical
  simp [primePowerColumns, and_assoc, and_left_comm, and_comm]

def primePowerInc (M : ℕ) (q : ↥(primePowerColumns M)) (a : ℕ) : Prop :=
  q.1.1 ^ q.1.2 ∣ a

def divisorPrimePowerPairs (a : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact a.primeFactors.biUnion fun p ↦
    (Finset.Icc 1 (a.factorization p)).image fun j ↦ (p, j)

private theorem two_pow_length_le_prod
    (l : List ℕ) (hl : ∀ q ∈ l, 2 ≤ q) :
    2 ^ l.length ≤ l.prod := by
  induction l with
  | nil => simp
  | cons q l ih =>
      have hq : 2 ≤ q := hl q (by simp)
      have htail : ∀ r ∈ l, 2 ≤ r := by
        intro r hr
        exact hl r (by simp [hr])
      have hi := ih htail
      simp only [List.length_cons, List.prod_cons, pow_succ]
      calc
        2 ^ l.length * 2 ≤ l.prod * q := Nat.mul_le_mul hi hq
        _ = q * l.prod := Nat.mul_comm _ _

theorem primeFactorsList_length_le_log_two {a : ℕ} (ha : 0 < a) :
    a.primeFactorsList.length ≤ Nat.log 2 a := by
  apply Nat.le_log_of_pow_le Nat.one_lt_two
  calc
    2 ^ a.primeFactorsList.length ≤ a.primeFactorsList.prod :=
      two_pow_length_le_prod a.primeFactorsList fun q hq ↦
        (Nat.prime_of_mem_primeFactorsList hq).two_le
    _ = a := Nat.prod_primeFactorsList ha.ne'

private theorem card_divisorPrimePowerPairs_le_length {a : ℕ} :
    (divisorPrimePowerPairs a).card ≤ a.primeFactorsList.length := by
  classical
  calc
    (divisorPrimePowerPairs a).card ≤
        ∑ p ∈ a.primeFactors,
          ((Finset.Icc 1 (a.factorization p)).image fun j ↦ (p, j)).card := by
      exact Finset.card_biUnion_le
    _ ≤ ∑ p ∈ a.primeFactors,
          (Finset.Icc 1 (a.factorization p)).card := by
      apply Finset.sum_le_sum
      intro p _
      exact Finset.card_image_le
    _ = ∑ p ∈ a.primeFactors, a.factorization p := by simp
    _ = a.factorization.sum (fun _ e ↦ e) := by rfl
    _ = a.primeFactorsList.length := by
      rw [Nat.factorization_eq_primeFactorsList_multiset]
      exact Multiset.toFinsupp_sum_eq _

/-- The exact logarithmic column-degree estimate needed by floating
rounding. -/
theorem primePowerColumns_degree_le_log
    {M a : ℕ} (ha : 0 < a) (haM : a ≤ M) :
    (columnsContaining (Finset.univ : Finset ↥(primePowerColumns M))
      (primePowerInc M) a).card ≤ Nat.log 2 M := by
  classical
  have hmap : Set.MapsTo
      (fun q : ↥(primePowerColumns M) ↦ q.1)
      (columnsContaining (Finset.univ : Finset ↥(primePowerColumns M))
        (primePowerInc M) a)
      (divisorPrimePowerPairs a) := by
    intro q hq
    have hdiv : q.1.1 ^ q.1.2 ∣ a :=
      (mem_columnsContaining.mp hq).2
    have hqData := mem_primePowerColumns.mp q.2
    have hp : q.1.1.Prime := hqData.2.2.2.2.1
    have hj : 1 ≤ q.1.2 := hqData.2.2.1
    have hpDvd : q.1.1 ∣ a :=
      (dvd_pow_self q.1.1 (Nat.ne_of_gt (zero_lt_one.trans_le hj))).trans hdiv
    have hpMem : q.1.1 ∈ a.primeFactors :=
      hp.mem_primeFactors hpDvd ha.ne'
    have hjle : q.1.2 ≤ a.factorization q.1.1 :=
      (hp.pow_dvd_iff_le_factorization ha.ne').mp hdiv
    exact Finset.mem_biUnion.mpr ⟨q.1.1, hpMem,
      Finset.mem_image.mpr ⟨q.1.2, Finset.mem_Icc.mpr ⟨hj, hjle⟩, rfl⟩⟩
  have hdegreeLocal :
      (columnsContaining (Finset.univ : Finset ↥(primePowerColumns M))
        (primePowerInc M) a).card ≤ (divisorPrimePowerPairs a).card := by
    exact Finset.card_le_card_of_injOn
      (fun q : ↥(primePowerColumns M) ↦ q.1) hmap
      Subtype.val_injective.injOn
  exact hdegreeLocal.trans <|
    card_divisorPrimePowerPairs_le_length.trans <|
      (primeFactorsList_length_le_log_two ha).trans
        (Nat.log_mono_right haM)

end

end Erdos390.WholePaper
