import Erdos536.FiveStateBalance

/-!
# The finite prime-band target event

This file packages the target event used for the five-state construction.
The four active labels are represented by `Option (Fin 3)`: `none` is the
common label, while `some s` is petal `s`.  Prefix conditions are imposed
only at a supplied finite set of depths, so the event is an explicit
Boolean predicate on the finite configuration space.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- The four active labels: one common label and three petal labels. -/
abbrev ActiveFiveLabel := Option (Fin 3)

/-- Embed the four active labels in the five-state label type. -/
def activeFiveLabel : ActiveFiveLabel → FiveLabel
  | none => 1
  | some s => petalLabel s

/-- The normalized logarithmic weight `log p / T` of an integer `p`. -/
noncomputable def normalizedLogWeight (T : ℝ) (p : ℕ) : ℝ :=
  Real.log (p : ℝ) / T

/-- The depth `-log(log p / T)` associated with the normalized weight. -/
noncomputable def normalizedLogDepth (T : ℝ) (p : ℕ) : ℝ :=
  -Real.log (normalizedLogWeight T p)

/-- The primes carrying one specified active label. -/
def fiveActiveLabelSubtype
    (R : Finset ℕ) (c : FiveConfiguration R) (l : ActiveFiveLabel) :
    Finset ↥R :=
  Finset.univ.filter fun p ↦ c p = activeFiveLabel l

/-- The primes of an active label whose normalized depth is at most `d`. -/
noncomputable def fiveLabelDepthPrefix
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    (l : ActiveFiveLabel) (d : ℝ) : Finset ↥R :=
  Finset.univ.filter fun p ↦
    c p = activeFiveLabel l ∧ normalizedLogDepth T p.1 ≤ d

/-- The number of primes of label `l` in the depth prefix ending at `d`. -/
noncomputable def fiveLabelPrefixCount
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    (l : ActiveFiveLabel) (d : ℝ) : ℕ :=
  (fiveLabelDepthPrefix R T c l d).card

/-- The total normalized logarithmic weight of one active label. -/
noncomputable def fiveActiveLabelNormalizedTotal
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    (l : ActiveFiveLabel) : ℝ :=
  ∑ p ∈ fiveActiveLabelSubtype R c l, normalizedLogWeight T p.1

/-- The normalized logarithmic total of petal `s`. -/
noncomputable def fivePetalNormalizedTotal
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    (s : Fin 3) : ℝ :=
  fiveActiveLabelNormalizedTotal R T c (some s)

@[simp]
theorem fiveActiveLabelSubtype_some
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) :
    fiveActiveLabelSubtype R c (some s) = fivePetalSubtype R c s := by
  ext p
  simp [fiveActiveLabelSubtype, activeFiveLabel]

@[simp]
theorem mem_fiveLabelDepthPrefix
    {R : Finset ℕ} {T : ℝ} {c : FiveConfiguration R}
    {l : ActiveFiveLabel} {d : ℝ} {p : ↥R} :
    p ∈ fiveLabelDepthPrefix R T c l d ↔
      c p = activeFiveLabel l ∧ normalizedLogDepth T p.1 ≤ d := by
  simp [fiveLabelDepthPrefix]

/-- The propositional specification underlying the Boolean target event. -/
def FivePrimeBandEventSpec
    (R : Finset ℕ) (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (c : FiveConfiguration R) : Prop :=
  (∀ s : Fin 3,
      lower ≤ fivePetalNormalizedTotal R T c s ∧
        fivePetalNormalizedTotal R T c s ≤ upper) ∧
  (∀ s t : Fin 3,
      |fivePetalNormalizedTotal R T c s -
        fivePetalNormalizedTotal R T c t| ≤ w) ∧
  (∀ l : ActiveFiveLabel, ∀ d : ↥depths,
      threshold d.1 ≤ fiveLabelPrefixCount R T c l d.1)

/-- The finite symmetric target event.  It requires all three petal totals
to lie in `[lower, upper]`, their pairwise range to be at most `w`, and
all four active labels to satisfy the supplied lower prefix profile at
each depth in `depths`. -/
noncomputable def fivePrimeBandEvent
    (R : Finset ℕ) (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ) :
    FiveConfiguration R → Bool :=
  fun c ↦ by
    classical
    exact decide (FivePrimeBandEventSpec
      R T lower upper w depths threshold c)

@[simp]
theorem fivePrimeBandEvent_iff
    {R : Finset ℕ} {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {c : FiveConfiguration R} :
    fivePrimeBandEvent R T lower upper w depths threshold c ↔
      FivePrimeBandEventSpec
        R T lower upper w depths threshold c := by
  classical
  simp [fivePrimeBandEvent]

/-- Read off the prefix-profile part of the target event. -/
theorem fivePrimeBandEvent_prefix
    {R : Finset ℕ} {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {c : FiveConfiguration R}
    (hc : fivePrimeBandEvent
      R T lower upper w depths threshold c)
    (l : ActiveFiveLabel) {d : ℝ} (hd : d ∈ depths) :
    threshold d ≤ fiveLabelPrefixCount R T c l d :=
  (fivePrimeBandEvent_iff.mp hc).2.2 l ⟨d, hd⟩

/-- Read off the pairwise petal-balance part of the target event. -/
theorem fivePrimeBandEvent_petalBalance
    {R : Finset ℕ} {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {c : FiveConfiguration R}
    (hc : fivePrimeBandEvent
      R T lower upper w depths threshold c)
    (s t : Fin 3) :
    |fivePetalNormalizedTotal R T c s -
      fivePetalNormalizedTotal R T c t| ≤ w :=
  (fivePrimeBandEvent_iff.mp hc).2.1 s t

/-- A positive lower prefix requirement forces every accepted
configuration to have all three petals nonempty. -/
theorem fivePrimeBandEvent_hasPetals
    {R : Finset ℕ} {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths) (hthreshold : 1 ≤ threshold d₀) :
    FiveEventHasPetals R
      (fivePrimeBandEvent R T lower upper w depths threshold) := by
  intro c hc s
  have hcount :
      1 ≤ fiveLabelPrefixCount R T c (some s) d₀ :=
    hthreshold.trans
      (fivePrimeBandEvent_prefix hc (some s) hd₀)
  have hnonempty :
      (fiveLabelDepthPrefix R T c (some s) d₀).Nonempty := by
    rw [← Finset.card_pos]
    exact Nat.zero_lt_one.trans_le hcount
  obtain ⟨p, hp⟩ := hnonempty
  refine ⟨p, ?_⟩
  rw [mem_fivePetalSubtype]
  exact (mem_fiveLabelDepthPrefix.mp hp).1

/-- Scaling normalized weights by `T` recovers the actual petal log-sum. -/
theorem fivePetalLogSum_eq_mul_normalizedTotal
    {R : Finset ℕ} {T : ℝ} (hT : T ≠ 0)
    (c : FiveConfiguration R) (s : Fin 3) :
    fivePetalLogSum R c s =
      T * fivePetalNormalizedTotal R T c s := by
  rw [fivePetalLogSum, fivePetalNormalizedTotal,
    fiveActiveLabelNormalizedTotal, fiveActiveLabelSubtype_some]
  rw [fivePetalValues, underlyingValues]
  rw [Finset.sum_image]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _hp
    rw [normalizedLogWeight]
    field_simp
  · intro p hp q hq hpq
    exact Subtype.ext hpq

/-- The pairwise normalized balance in the target event gives the
event-level petal-log balance with tolerance `T * w`. -/
theorem fivePrimeBandEvent_petalLogBalanced
    {R : Finset ℕ} {T lower upper w : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    (hT : 0 < T) :
    FiveEventPetalLogBalanced R
      (fivePrimeBandEvent R T lower upper w depths threshold)
      (T * w) := by
  intro c hc s t
  rw [fivePetalLogSum_eq_mul_normalizedTotal hT.ne',
    fivePetalLogSum_eq_mul_normalizedTotal hT.ne', ← mul_sub, abs_mul,
    abs_of_pos hT]
  exact mul_le_mul_of_nonneg_left
    (fivePrimeBandEvent_petalBalance hc s t) hT.le

/-- Recover the petal index of a non-common, non-unused label.  Its values
on labels `0` and `1` are harmless defaults. -/
def fivePetalIndex (l : FiveLabel) : Fin 3 :=
  ⟨(l.1 + 1) % 3, Nat.mod_lt _ (by decide)⟩

@[simp]
theorem fivePetalIndex_petal (s : Fin 3) :
    fivePetalIndex (petalLabel s) = s := by
  fin_cases s <;> simp [fivePetalIndex, petalLabel]

theorem petalLabel_fivePetalIndex
    {l : FiveLabel} (hzero : l ≠ 0) (hone : l ≠ 1) :
    petalLabel (fivePetalIndex l) = l := by
  fin_cases l <;> simp_all [fivePetalIndex, petalLabel]

/-- Relabel the three petals by a permutation, fixing the unused and
common labels. -/
def permuteFivePetalLabel (σ : Equiv.Perm (Fin 3))
    (l : FiveLabel) : FiveLabel :=
  if l = 0 then 0
  else if l = 1 then 1
  else petalLabel (σ (fivePetalIndex l))

@[simp]
theorem permuteFivePetalLabel_zero (σ : Equiv.Perm (Fin 3)) :
    permuteFivePetalLabel σ 0 = 0 := by
  simp [permuteFivePetalLabel]

@[simp]
theorem permuteFivePetalLabel_one (σ : Equiv.Perm (Fin 3)) :
    permuteFivePetalLabel σ 1 = 1 := by
  simp [permuteFivePetalLabel]

@[simp]
theorem permuteFivePetalLabel_petal
    (σ : Equiv.Perm (Fin 3)) (s : Fin 3) :
    permuteFivePetalLabel σ (petalLabel s) = petalLabel (σ s) := by
  fin_cases s <;>
    simp [permuteFivePetalLabel, petalLabel, fivePetalIndex]

@[simp]
theorem permuteFivePetalLabel_active
    (σ : Equiv.Perm (Fin 3)) (l : ActiveFiveLabel) :
    permuteFivePetalLabel σ (activeFiveLabel l) =
      activeFiveLabel (l.map σ) := by
  cases l with
  | none => simp [activeFiveLabel]
  | some s => simp [activeFiveLabel]

@[simp]
theorem permuteFivePetalLabel_symm_apply
    (σ : Equiv.Perm (Fin 3)) (l : FiveLabel) :
    permuteFivePetalLabel σ.symm (permuteFivePetalLabel σ l) = l := by
  by_cases hzero : l = 0
  · subst l
    simp
  by_cases hone : l = 1
  · subst l
    simp
  have hin :
      permuteFivePetalLabel σ l =
        petalLabel (σ (fivePetalIndex l)) := by
    simp [permuteFivePetalLabel, hzero, hone]
  calc
    permuteFivePetalLabel σ.symm (permuteFivePetalLabel σ l) =
        permuteFivePetalLabel σ.symm
          (petalLabel (σ (fivePetalIndex l))) := by
            exact congrArg (permuteFivePetalLabel σ.symm) hin
    _ = petalLabel (fivePetalIndex l) := by simp
    _ = l := petalLabel_fivePetalIndex hzero hone

theorem permuteFivePetalLabel_eq_active_iff
    (σ : Equiv.Perm (Fin 3)) (l : FiveLabel)
    (a : ActiveFiveLabel) :
    permuteFivePetalLabel σ l = activeFiveLabel a ↔
      l = activeFiveLabel (a.map σ.symm) := by
  constructor
  · intro h
    have h' := congrArg (permuteFivePetalLabel σ.symm) h
    simpa using h'
  · intro h
    rw [h]
    simp

/-- Apply a petal permutation pointwise to a configuration. -/
def permuteFiveConfiguration
    {R : Finset ℕ} (σ : Equiv.Perm (Fin 3))
    (c : FiveConfiguration R) : FiveConfiguration R :=
  fun p ↦ permuteFivePetalLabel σ (c p)

theorem fiveActiveLabelSubtype_permute
    {R : Finset ℕ} (σ : Equiv.Perm (Fin 3))
    (c : FiveConfiguration R) (l : ActiveFiveLabel) :
    fiveActiveLabelSubtype R (permuteFiveConfiguration σ c) l =
      fiveActiveLabelSubtype R c (l.map σ.symm) := by
  ext p
  simp [fiveActiveLabelSubtype, permuteFiveConfiguration,
    permuteFivePetalLabel_eq_active_iff]

theorem fiveLabelDepthPrefix_permute
    {R : Finset ℕ} (T : ℝ) (σ : Equiv.Perm (Fin 3))
    (c : FiveConfiguration R) (l : ActiveFiveLabel) (d : ℝ) :
    fiveLabelDepthPrefix R T (permuteFiveConfiguration σ c) l d =
      fiveLabelDepthPrefix R T c (l.map σ.symm) d := by
  ext p
  simp [fiveLabelDepthPrefix, permuteFiveConfiguration,
    permuteFivePetalLabel_eq_active_iff]

theorem fiveLabelPrefixCount_permute
    {R : Finset ℕ} (T : ℝ) (σ : Equiv.Perm (Fin 3))
    (c : FiveConfiguration R) (l : ActiveFiveLabel) (d : ℝ) :
    fiveLabelPrefixCount R T (permuteFiveConfiguration σ c) l d =
      fiveLabelPrefixCount R T c (l.map σ.symm) d := by
  rw [fiveLabelPrefixCount, fiveLabelPrefixCount,
    fiveLabelDepthPrefix_permute]

theorem fivePetalNormalizedTotal_permute
    {R : Finset ℕ} (T : ℝ) (σ : Equiv.Perm (Fin 3))
    (c : FiveConfiguration R) (s : Fin 3) :
    fivePetalNormalizedTotal R T (permuteFiveConfiguration σ c) s =
      fivePetalNormalizedTotal R T c (σ.symm s) := by
  rw [fivePetalNormalizedTotal, fivePetalNormalizedTotal,
    fiveActiveLabelNormalizedTotal, fiveActiveLabelNormalizedTotal,
    fiveActiveLabelSubtype_permute]
  simp

/-- The target event is invariant under every permutation of its three
petal labels. -/
theorem fivePrimeBandEvent_permute_iff
    {R : Finset ℕ} (T lower upper w : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (σ : Equiv.Perm (Fin 3)) (c : FiveConfiguration R) :
    fivePrimeBandEvent R T lower upper w depths threshold
        (permuteFiveConfiguration σ c) ↔
      fivePrimeBandEvent R T lower upper w depths threshold c := by
  rw [fivePrimeBandEvent_iff, fivePrimeBandEvent_iff]
  constructor
  · rintro ⟨hinterval, hbalance, hprefix⟩
    refine ⟨?_, ?_, ?_⟩
    · intro s
      simpa [fivePetalNormalizedTotal_permute] using hinterval (σ s)
    · intro s t
      simpa [fivePetalNormalizedTotal_permute] using
        hbalance (σ s) (σ t)
    · intro l d
      simpa [fiveLabelPrefixCount_permute] using
        hprefix (l.map σ) d
  · rintro ⟨hinterval, hbalance, hprefix⟩
    refine ⟨?_, ?_, ?_⟩
    · intro s
      simpa [fivePetalNormalizedTotal_permute] using
        hinterval (σ.symm s)
    · intro s t
      simpa [fivePetalNormalizedTotal_permute] using
        hbalance (σ.symm s) (σ.symm t)
    · intro l d
      rw [fiveLabelPrefixCount_permute]
      exact hprefix (l.map σ.symm) d

end Erdos536
