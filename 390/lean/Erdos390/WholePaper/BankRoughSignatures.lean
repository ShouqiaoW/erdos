import Erdos390.WholePaper.Definitions

/-!
# Complete rough signatures and bank path row counts

The complete rough signature keeps every prime-power exponent above a fixed
cutoff.  Its integer label is the corresponding product of prime powers.
Unique factorization proves that the vector and integer labels induce exactly
the same partition.  Separately, componentwise equality of signatures is
used to derive full path-state multiplicity invariance; it is not stored as a
field or assumed for the completed path.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- The vector convention `S(a)=(v_P(a))_{P>y}` for a complete rough
signature. -/
def completeRoughSignature (y a : ℕ) : ℕ →₀ ℕ :=
  a.factorization.filter (fun p ↦ y < p)

/-- Coordinate description of the complete rough signature. -/
theorem completeRoughSignature_apply (y a p : ℕ) :
    completeRoughSignature y a p =
      if y < p then a.factorization p else 0 := rfl

/-- The integer convention `R_y(a)`, retaining the same prime-power
multiplicities as the vector convention. -/
def completeRoughLabel (y a : ℕ) : ℕ :=
  (completeRoughSignature y a).prod (fun p e ↦ p ^ e)

private theorem completeRoughSignature_support_prime (y a : ℕ) :
    ∀ p : ℕ, p ∈ (completeRoughSignature y a).support → p.Prime := by
  intro p hp
  rw [Finsupp.mem_support_iff] at hp
  have hpCut : y < p := by
    by_contra hcut
    simp [completeRoughSignature, hcut] at hp
  have hpValue : a.factorization p ≠ 0 := by
    simpa [completeRoughSignature, Finsupp.filter_apply, hpCut] using hp
  have hpSupport : p ∈ a.factorization.support :=
    Finsupp.mem_support_iff.mpr hpValue
  exact Nat.prime_of_mem_primeFactors (by
    simpa only [Nat.support_factorization] using hpSupport)

/-- Factoring the integer rough label recovers the complete vector
signature exactly. -/
theorem completeRoughLabel_factorization (y a : ℕ) :
    (completeRoughLabel y a).factorization = completeRoughSignature y a := by
  exact Nat.prod_pow_factorization_eq_self
    (completeRoughSignature_support_prime y a)

/-- Vector and integer conventions partition factors into exactly the same
rough rows. -/
theorem completeRoughSignature_eq_iff_label_eq {y a b : ℕ} :
    completeRoughSignature y a = completeRoughSignature y b ↔
      completeRoughLabel y a = completeRoughLabel y b := by
  constructor
  · intro h
    exact congrArg (fun s : ℕ →₀ ℕ ↦ s.prod (fun p e ↦ p ^ e)) h
  · intro h
    have hfactorization := congrArg Nat.factorization h
    simpa only [completeRoughLabel_factorization] using hfactorization

/-- Number of factors in a finite state having one specified complete
signature. -/
def completeSignatureMultiplicity
    (y : ℕ) (state : Finset ℕ) (signature : ℕ →₀ ℕ) : ℕ :=
  (state.filter (fun a ↦ completeRoughSignature y a = signature)).card

/-- Number of factors in a finite state having one specified integer rough
label. -/
def completeLabelMultiplicity
    (y : ℕ) (state : Finset ℕ) (label : ℕ) : ℕ :=
  (state.filter (fun a ↦ completeRoughLabel y a = label)).card

/-- The two row-count conventions agree for the row containing any given
factor. -/
theorem completeSignatureMultiplicity_eq_labelMultiplicity
    (y : ℕ) (state : Finset ℕ) (a : ℕ) :
    completeSignatureMultiplicity y state (completeRoughSignature y a) =
      completeLabelMultiplicity y state (completeRoughLabel y a) := by
  rw [completeSignatureMultiplicity, completeLabelMultiplicity]
  apply congrArg Finset.card
  ext b
  simp only [Finset.mem_filter]
  exact and_congr_right fun _hb ↦
    completeRoughSignature_eq_iff_label_eq

/-- A full path state contains one token for each component index. -/
def indexedPathState {C : Type*} [Fintype C] [DecidableEq C]
    (state : C → ℕ) : Finset ℕ :=
  Finset.univ.image state

private theorem filter_indexedPathState_eq_image_filter
    {C : Type*} [Fintype C] [DecidableEq C]
    (state : C → ℕ) (predicate : ℕ → Prop) [DecidablePred predicate] :
    (indexedPathState state).filter predicate =
      (Finset.univ.filter (fun c ↦ predicate (state c))).image state := by
  ext a
  constructor
  · intro ha
    rw [Finset.mem_filter] at ha
    obtain ⟨haImage, haPredicate⟩ := ha
    rw [indexedPathState, Finset.mem_image] at haImage
    obtain ⟨c, hc, hca⟩ := haImage
    rw [Finset.mem_image]
    refine ⟨c, ?_, hca⟩
    rw [Finset.mem_filter]
    exact ⟨hc, by simpa only [hca] using haPredicate⟩
  · intro ha
    rw [Finset.mem_image] at ha
    obtain ⟨c, hc, hca⟩ := ha
    rw [Finset.mem_filter] at hc
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [indexedPathState, Finset.mem_image]
      exact ⟨c, hc.1, hca⟩
    · simpa only [hca] using hc.2

private theorem card_filter_indexedPathState_eq_component
    {C : Type*} [Fintype C] [DecidableEq C]
    (state : C → ℕ) (hstate : Function.Injective state)
    (predicate : ℕ → Prop) [DecidablePred predicate] :
    ((indexedPathState state).filter predicate).card =
      (Finset.univ.filter (fun c ↦ predicate (state c))).card := by
  rw [filter_indexedPathState_eq_image_filter,
    Finset.card_image_of_injective _ hstate]

/-- Signature multiplicity before forgetting component indices. -/
def componentSignatureMultiplicity
    {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (state : C → ℕ) (signature : ℕ →₀ ℕ) : ℕ :=
  (Finset.univ.filter
    (fun c ↦ completeRoughSignature y (state c) = signature)).card

/-- For an injectively marked path state, factor multiplicity is exactly
component-index multiplicity. -/
theorem completeSignatureMultiplicity_indexedPathState
    {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (state : C → ℕ) (hstate : Function.Injective state)
    (signature : ℕ →₀ ℕ) :
    completeSignatureMultiplicity y (indexedPathState state) signature =
      componentSignatureMultiplicity y state signature := by
  exact card_filter_indexedPathState_eq_component state hstate
    (fun a ↦ completeRoughSignature y a = signature)

/-- Componentwise equal complete signatures force equality of the entire
path's row counts, before any asymptotic donor or collision argument. -/
theorem componentwise_signature_eq_implies_path_multiplicity_eq
    {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (stateZero stateOne : C → ℕ)
    (hzero : Function.Injective stateZero)
    (hone : Function.Injective stateOne)
    (hsignature : ∀ c,
      completeRoughSignature y (stateZero c) =
        completeRoughSignature y (stateOne c)) :
    ∀ signature : ℕ →₀ ℕ,
      completeSignatureMultiplicity y (indexedPathState stateZero) signature =
        completeSignatureMultiplicity y (indexedPathState stateOne) signature := by
  intro signature
  rw [completeSignatureMultiplicity_indexedPathState y stateZero hzero,
    completeSignatureMultiplicity_indexedPathState y stateOne hone]
  unfold componentSignatureMultiplicity
  apply congrArg Finset.card
  ext c
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hsignature c]

/-- The same derived path-state invariance expressed with integer rough
labels. -/
theorem componentwise_label_eq_implies_path_multiplicity_eq
    {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (stateZero stateOne : C → ℕ)
    (hzero : Function.Injective stateZero)
    (hone : Function.Injective stateOne)
    (hlabel : ∀ c,
      completeRoughLabel y (stateZero c) =
        completeRoughLabel y (stateOne c)) :
    ∀ label : ℕ,
      completeLabelMultiplicity y (indexedPathState stateZero) label =
        completeLabelMultiplicity y (indexedPathState stateOne) label := by
  intro label
  calc
    completeLabelMultiplicity y (indexedPathState stateZero) label =
        (Finset.univ.filter
          (fun c ↦ completeRoughLabel y (stateZero c) = label)).card := by
      exact card_filter_indexedPathState_eq_component stateZero hzero
        (fun a ↦ completeRoughLabel y a = label)
    _ = (Finset.univ.filter
          (fun c ↦ completeRoughLabel y (stateOne c) = label)).card := by
      apply congrArg Finset.card
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hlabel c]
    _ = completeLabelMultiplicity y (indexedPathState stateOne) label := by
      exact (card_filter_indexedPathState_eq_component stateOne hone
        (fun a ↦ completeRoughLabel y a = label)).symm

end

end Erdos390.WholePaper
