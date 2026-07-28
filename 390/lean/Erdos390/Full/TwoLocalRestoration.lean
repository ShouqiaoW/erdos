import Erdos390.Full.OmittedTiltMarkedProbability
import Erdos390.Full.PaperValuationCutoff
import Erdos390.Full.LocalFugacityRestoration

/-!
# Exact restoration of two omitted local primes

The omitted-score marked law is reweighted by the two literal local
valuation fugacities.  This file proves the exact finite identity connecting
that sequential reweighting to the full valuation tilt and then expands both
the marked numerator and the normalizer into prime-power indicators.
-/

open scoped BigOperators

namespace Erdos390.Full

open ArithmeticModel FiniteProbability ValuationScoreDomination
open LocalFugacity LocalFugacityRestoration ValuationCutoff

noncomputable section

namespace FiniteProbability

variable {Omega : Type*} [Fintype Omega]

/-- Two finite probability objects are equal when their mass functions are
equal.  The remaining structure fields are propositions. -/
theorem eq_of_mass_eq (mu nu : FiniteProbability Omega)
    (h : mu.mass = nu.mass) : mu = nu := by
  cases mu with
  | mk muMass muNonneg muSum =>
      cases nu with
      | mk nuMass nuNonneg nuSum =>
          simp only [FiniteProbability.mk.injEq]
          exact h

/-- Exponential tilting first by `S` and then by `T` is exactly tilting once
by their sum. -/
theorem exponentialTilt_add (mu : FiniteProbability Omega)
    (S T : Omega → ℝ) :
    (mu.exponentialTilt S).exponentialTilt T =
      mu.exponentialTilt (fun omega ↦ S omega + T omega) := by
  apply eq_of_mass_eq
  funext omega
  have hpart :
      (mu.exponentialTilt S).expPartition T =
        mu.expPartition (fun x ↦ S x + T x) / mu.expPartition S := by
    unfold expPartition
    rw [mu.exponentialTilt_expect_eq (fun x ↦ Real.exp (T x)) S]
    congr 1
    unfold expect
    apply Finset.sum_congr rfl
    intro x hx
    dsimp only
    rw [Real.exp_add]
    ring
  change
    (mu.mass omega * Real.exp (S omega) / mu.expPartition S) *
          Real.exp (T omega) /
        (mu.exponentialTilt S).expPartition T =
      mu.mass omega * Real.exp (S omega + T omega) /
        mu.expPartition (fun x ↦ S x + T x)
  rw [hpart]
  rw [Real.exp_add]
  field_simp [ne_of_gt (mu.expPartition_pos S),
    ne_of_gt (mu.expPartition_pos (fun x ↦ S x + T x))]

/-- Sequential-tilt expectation as one exact quotient under the first law. -/
theorem exponentialTilt_add_expect_eq
    (mu : FiniteProbability Omega) (S T A : Omega → ℝ) :
    (mu.exponentialTilt (fun omega ↦ S omega + T omega)).expect A =
      (mu.exponentialTilt S).expect
          (fun omega ↦ A omega * Real.exp (T omega)) /
        (mu.exponentialTilt S).expect (fun omega ↦ Real.exp (T omega)) := by
  rw [← mu.exponentialTilt_add S T]
  rw [(mu.exponentialTilt S).exponentialTilt_expect_eq A T]
  rfl

end FiniteProbability

namespace TwoLocalRestoration

/-- Remove two distinct local primes from a finite score set. -/
def erasePair (P : Finset ℕ) (p q : ℕ) : Finset ℕ :=
  (P.erase p).erase q

theorem erasePair_subset (P : Finset ℕ) (p q : ℕ) :
    erasePair P p q ⊆ P :=
  (Finset.erase_subset q (P.erase p)).trans (Finset.erase_subset p P)

/-- Literal decomposition of the full valuation score into the omitted
score and two local valuation coordinates. -/
theorem valuationScore_eq_erasePair_add
    (P : Finset ℕ) (eta : ℕ → ℝ) (L : ℝ) {p q m : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q) :
    valuationScore P eta L m =
      valuationScore (erasePair P p q) eta L m +
        (eta p / L) * valuation p m + (eta q / L) * valuation q m := by
  have hqErase : q ∈ P.erase p := Finset.mem_erase.mpr ⟨hpq.symm, hqP⟩
  unfold valuationScore erasePair
  let f : ℕ → ℝ := fun r ↦ (eta r / L) * valuation r m
  change (∑ r ∈ P, f r) =
    (∑ r ∈ (P.erase p).erase q, f r) + f p + f q
  calc
    (∑ r ∈ P, f r) = (∑ r ∈ P.erase p, f r) + f p :=
      (Finset.sum_erase_add P f hpP).symm
    _ = ((∑ r ∈ (P.erase p).erase q, f r) + f q) + f p := by
      rw [Finset.sum_erase_add (P.erase p) f hqErase]
    _ = (∑ r ∈ (P.erase p).erase q, f r) + f p + f q := by ring

/-- On a bounded positive cell, the two local factors are exactly the
exponential of the omitted local score. -/
theorem twoLocalFactor_valuationCutoff_eq_exp
    {p q m M : ℕ} (eta : ℕ → ℝ) (L : ℝ)
    (hp : p.Prime) (hq : q.Prime) (hm : 0 < m) (hmM : m ≤ M) :
    localFactor p (valuationCutoff p M) (Real.exp (eta p / L)) m *
        localFactor q (valuationCutoff q M) (Real.exp (eta q / L)) m =
      Real.exp ((eta p / L) * valuation p m +
        (eta q / L) * valuation q m) := by
  rw [localFactor_valuationCutoff_exp_eq (eta p) L hp hm hmM,
    localFactor_valuationCutoff_exp_eq (eta q) L hq hm hmM,
    ← Real.exp_add]

section Cell

variable {S : Finset ℕ}

/-- Exact two-local restored quotient for the full valuation tilt on an
actual finite set of positive integers with common endpoint `M`. -/
theorem fullTilt_divInd_eq_twoLocal_quotient
    (hS : S.Nonempty) (P : Finset ℕ) (eta : ℕ → ℝ)
    {L : ℝ} {M p q D : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (hp : p.Prime) (hq : q.Prime)
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    let mu := uniformOnFinset S hS
    let omitted := mu.exponentialTilt
      (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    (mu.exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) =
      omitted.expect (fun m : S ↦
          divInd D m *
            localFactor p (valuationCutoff p M) (Real.exp (eta p / L)) m *
            localFactor q (valuationCutoff q M) (Real.exp (eta q / L)) m) /
        omitted.expect (fun m : S ↦
            localFactor p (valuationCutoff p M) (Real.exp (eta p / L)) m *
            localFactor q (valuationCutoff q M) (Real.exp (eta q / L)) m) := by
  dsimp only
  let mu := uniformOnFinset S hS
  let omitted := mu.exponentialTilt
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
  let localScore : S → ℝ := fun m ↦
    (eta p / L) * valuation p m + (eta q / L) * valuation q m
  have hscore : (fun m : S ↦ valuationScore P eta L m) =
      fun m : S ↦ valuationScore (erasePair P p q) eta L m + localScore m := by
    funext m
    rw [valuationScore_eq_erasePair_add P eta L (m := (m : ℕ))
      hpP hqP hpq]
    dsimp only [localScore]
    ring
  rw [hscore]
  have hadd := mu.exponentialTilt_add_expect_eq
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    localScore (fun m : S ↦ divInd D m)
  rw [hadd]
  congr 1
  · congr 1
    funext m
    rw [← twoLocalFactor_valuationCutoff_eq_exp eta L hp hq
      (hSpos m m.property) (hSle m m.property)]
    ring
  · congr 1
    funext m
    rw [← twoLocalFactor_valuationCutoff_eq_exp eta L hp hq
      (hSpos m m.property) (hSle m m.property)]

/-- The same exact quotient with both local factors expanded into finite
prime-power indicator sums. -/
theorem fullTilt_divInd_eq_twoLocal_indicator_ratio
    (hS : S.Nonempty) (P : Finset ℕ) (eta : ℕ → ℝ)
    {L : ℝ} {M p q D : ℕ}
    (hpP : p ∈ P) (hqP : q ∈ P) (hpq : p ≠ q)
    (hp : p.Prime) (hq : q.Prime)
    (hSpos : ∀ m ∈ S, 0 < m) (hSle : ∀ m ∈ S, m ≤ M) :
    let omitted := (uniformOnFinset S hS).exponentialTilt
      (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
    ((uniformOnFinset S hS).exponentialTilt
        (fun m : S ↦ valuationScore P eta L m)).expect
          (fun m : S ↦ divInd D m) =
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦
                divInd D m * divInd (p ^ a * q ^ b) m)) /
      (∑ a ∈ Finset.Icc 0 (valuationCutoff p M),
        ∑ b ∈ Finset.Icc 0 (valuationCutoff q M),
          coefficient (Real.exp (eta p / L)) a *
            coefficient (Real.exp (eta q / L)) b *
              omitted.expect (fun m : S ↦
                divInd (p ^ a * q ^ b) m)) := by
  dsimp only
  let omitted := (uniformOnFinset S hS).exponentialTilt
    (fun m : S ↦ valuationScore (erasePair P p q) eta L m)
  rw [fullTilt_divInd_eq_twoLocal_quotient hS P eta hpP hqP hpq hp hq
    hSpos hSle]
  rw [expect_two_restored_indicator omitted (fun m : S ↦ (m : ℕ))
    hpq hp hq, expect_two_restored omitted (fun m : S ↦ (m : ℕ))
    hpq hp hq]

end Cell

end TwoLocalRestoration

end

end Erdos390.Full
