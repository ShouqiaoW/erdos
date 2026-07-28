import Erdos390.WholePaper.BankRoughSignatures

/-!
# Expanded statement audit for complete rough signatures

This audit exposes the factorization filter, its integer prime-power product,
and the full finite row counts used by the path invariance theorems.
-/

namespace Erdos390.WholePaper

noncomputable section

example (y a p : ℕ) :
    completeRoughSignature y a p =
      if y < p then a.factorization p else 0 :=
  completeRoughSignature_apply y a p

example (y a p : ℕ) :
    (a.factorization.filter (fun q ↦ y < q)) p =
      if y < p then a.factorization p else 0 := rfl

example (y a : ℕ) :
    completeRoughLabel y a =
      (a.factorization.filter (fun p ↦ y < p)).prod
        (fun p e ↦ p ^ e) := rfl

example (y a : ℕ) :
    ((a.factorization.filter (fun p ↦ y < p)).prod
        (fun p e ↦ p ^ e)).factorization =
      a.factorization.filter (fun p ↦ y < p) := by
  simpa only [completeRoughLabel, completeRoughSignature] using
    completeRoughLabel_factorization y a

example {y a b : ℕ} :
    a.factorization.filter (fun p ↦ y < p) =
        b.factorization.filter (fun p ↦ y < p) ↔
      (a.factorization.filter (fun p ↦ y < p)).prod
          (fun p e ↦ p ^ e) =
        (b.factorization.filter (fun p ↦ y < p)).prod
          (fun p e ↦ p ^ e) := by
  simpa only [completeRoughSignature, completeRoughLabel] using
    (completeRoughSignature_eq_iff_label_eq (y := y) (a := a) (b := b))

example (y : ℕ) (state : Finset ℕ) (a : ℕ) :
    (state.filter (fun b ↦
        b.factorization.filter (fun p ↦ y < p) =
          a.factorization.filter (fun p ↦ y < p))).card =
      (state.filter (fun b ↦
        (b.factorization.filter (fun p ↦ y < p)).prod
            (fun p e ↦ p ^ e) =
          (a.factorization.filter (fun p ↦ y < p)).prod
            (fun p e ↦ p ^ e))).card := by
  simpa only [completeSignatureMultiplicity, completeLabelMultiplicity,
    completeRoughSignature, completeRoughLabel] using
      completeSignatureMultiplicity_eq_labelMultiplicity y state a

example {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (state : C → ℕ) (hstate : Function.Injective state)
    (signature : ℕ →₀ ℕ) :
    ((Finset.univ.image state).filter (fun a ↦
        a.factorization.filter (fun p ↦ y < p) = signature)).card =
      (Finset.univ.filter (fun c ↦
        (state c).factorization.filter (fun p ↦ y < p) =
          signature)).card := by
  simpa only [completeSignatureMultiplicity, componentSignatureMultiplicity,
    indexedPathState, completeRoughSignature] using
      completeSignatureMultiplicity_indexedPathState
        y state hstate signature

example {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (stateZero stateOne : C → ℕ)
    (hzero : Function.Injective stateZero)
    (hone : Function.Injective stateOne)
    (hsignature : ∀ c,
      (stateZero c).factorization.filter (fun p ↦ y < p) =
        (stateOne c).factorization.filter (fun p ↦ y < p)) :
    ∀ signature : ℕ →₀ ℕ,
      ((Finset.univ.image stateZero).filter (fun a ↦
        a.factorization.filter (fun p ↦ y < p) = signature)).card =
      ((Finset.univ.image stateOne).filter (fun a ↦
        a.factorization.filter (fun p ↦ y < p) = signature)).card := by
  simpa only [completeRoughSignature, completeSignatureMultiplicity,
    indexedPathState] using
      componentwise_signature_eq_implies_path_multiplicity_eq
        y stateZero stateOne hzero hone hsignature

example {C : Type*} [Fintype C] [DecidableEq C]
    (y : ℕ) (stateZero stateOne : C → ℕ)
    (hzero : Function.Injective stateZero)
    (hone : Function.Injective stateOne)
    (hlabel : ∀ c,
      ((stateZero c).factorization.filter (fun p ↦ y < p)).prod
          (fun p e ↦ p ^ e) =
        ((stateOne c).factorization.filter (fun p ↦ y < p)).prod
          (fun p e ↦ p ^ e)) :
    ∀ label : ℕ,
      ((Finset.univ.image stateZero).filter (fun a ↦
        (a.factorization.filter (fun p ↦ y < p)).prod
          (fun p e ↦ p ^ e) = label)).card =
      ((Finset.univ.image stateOne).filter (fun a ↦
        (a.factorization.filter (fun p ↦ y < p)).prod
          (fun p e ↦ p ^ e) = label)).card := by
  simpa only [completeRoughSignature, completeRoughLabel,
    completeLabelMultiplicity, indexedPathState] using
      componentwise_label_eq_implies_path_multiplicity_eq
        y stateZero stateOne hzero hone hlabel

end

end Erdos390.WholePaper
