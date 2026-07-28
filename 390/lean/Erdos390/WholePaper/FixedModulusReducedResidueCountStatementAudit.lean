import Erdos390.WholePaper.FixedModulusReducedResidueCount

/-! # Expanded statement audit for fixed-modulus residue counts -/

namespace Erdos390.WholePaper

noncomputable section

/-! ## Exact periodic decomposition -/

example (M start first second : ℕ) :
    ((Finset.Ico start (start + (first + second))).filter
      (fun a ↦ Nat.Coprime a M)) =
      ((Finset.Ico start (start + first)).filter
          (fun a ↦ Nat.Coprime a M)) ∪
        ((Finset.Ico (start + first) (start + first + second)).filter
          (fun a ↦ Nat.Coprime a M)) := by
  simpa only [reducedResidueSegment] using
    reducedResidueSegment_add M start first second

example (M start first second : ℕ) :
    Disjoint
      ((Finset.Ico start (start + first)).filter
        (fun a ↦ Nat.Coprime a M))
      ((Finset.Ico (start + first) (start + first + second)).filter
        (fun a ↦ Nat.Coprime a M)) := by
  simpa only [reducedResidueSegment] using
    reducedResidueSegment_disjoint M start first second

example (M start first second : ℕ) :
    ((Finset.Ico start (start + (first + second))).filter
        (fun a ↦ Nat.Coprime a M)).card =
      ((Finset.Ico start (start + first)).filter
          (fun a ↦ Nat.Coprime a M)).card +
        ((Finset.Ico (start + first) (start + first + second)).filter
          (fun a ↦ Nat.Coprime a M)).card := by
  simpa only [reducedResidueSegment] using
    reducedResidueSegment_card_add M start first second

example (M start : ℕ) :
    ((Finset.Ico start (start + M)).filter
      (fun a ↦ Nat.Coprime a M)).card = M.totient := by
  simpa only [reducedResidueSegment] using
    reducedResidueSegment_card_period M start

example (M start q : ℕ) :
    ((Finset.Ico start (start + q * M)).filter
      (fun a ↦ Nat.Coprime a M)).card = q * M.totient := by
  simpa only [reducedResidueSegment] using
    reducedResidueSegment_card_fullBlocks M start q

example (M start length : ℕ) :
    (((Finset.Ico start (start + length)).filter
      (fun a ↦ Nat.Coprime a M)).card) =
      (length / M) * M.totient +
        (((Finset.Ico
            (start + (length / M) * M)
            (start + (length / M) * M + length % M)).filter
          (fun a ↦ Nat.Coprime a M)).card) := by
  simpa only [reducedResidueSegment] using
    reducedResidueSegment_card_eq_fullBlocks_add_remainder
      M start length

example (M start length : ℕ) :
    ((Finset.Ico start (start + length)).filter
      (fun a ↦ Nat.Coprime a M)).card ≤ length := by
  simpa only [reducedResidueSegment] using
    reducedResidueSegment_card_le_length M start length

example {M lo hi : ℕ} (hlohi : lo ≤ hi) :
    (Finset.Ioc lo hi).filter (fun a ↦ Nat.Coprime a M) =
      (Finset.Ico (lo + 1) (lo + 1 + (hi - lo))).filter
        (fun a ↦ Nat.Coprime a M) := by
  simpa only [reducedResidueIoc, reducedResidueSegment] using
    reducedResidueIoc_eq_segment (M := M) hlohi

/-! ## Explicit fixed-period error -/

example {M : ℕ} (hM : 0 < M) (start length : ℕ) :
    |((((Finset.Ico start (start + length)).filter
          (fun a ↦ Nat.Coprime a M)).card : ℕ) : ℝ) -
        ((M.totient : ℝ) / (M : ℝ)) * (length : ℝ)| ≤
      ((length % M : ℕ) : ℝ) := by
  simpa only [reducedResidueSegment,
    fixedModulusReducedResidueDensity] using
    reducedResidueSegment_card_error_le_mod hM start length

example {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((((Finset.Ioc lo hi).filter
          (fun a ↦ Nat.Coprime a M)).card : ℕ) : ℝ) -
        ((M.totient : ℝ) / (M : ℝ)) *
          (((hi - lo : ℕ) : ℝ))| ≤
      ((((hi - lo) % M : ℕ) : ℝ)) := by
  simpa only [reducedResidueIoc,
    fixedModulusReducedResidueDensity] using
    reducedResidueIoc_card_error_le_mod hM hlohi

example {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((((Finset.Ioc lo hi).filter
          (fun a ↦ Nat.Coprime a M)).card : ℕ) : ℝ) -
        ((M.totient : ℝ) / (M : ℝ)) *
          ((hi - lo : ℕ) : ℝ)| ≤
      (M : ℝ) := by
  simpa only [reducedResidueIoc,
    fixedModulusReducedResidueDensity] using
    reducedResidueIoc_card_error_le_modulus hM hlohi

/-! ## Exact CRT reindexing and multiplier-independent error -/

example {M D lo hi : ℕ} (hD : 0 < D)
    (hDM : Nat.Coprime D M) :
    (((Finset.Ioc lo hi).filter
        (fun a ↦ D ∣ a ∧ Nat.Coprime a M)).card) =
      (((Finset.Ioc (lo / D) (hi / D)).filter
        (fun b ↦ Nat.Coprime b M)).card) := by
  simpa only [coprimeMultipleIoc, reducedResidueIoc] using
    coprimeMultipleIoc_card_eq_reducedResidueIoc hD hDM

example {D lo hi : ℕ} (hD : 0 < D) (hlohi : lo ≤ hi) :
    |(((hi / D - lo / D : ℕ) : ℝ)) -
        ((hi - lo : ℕ) : ℝ) / (D : ℝ)| < 1 := by
  exact quotientIocLength_sub_realLengthDiv_abs_lt_one hD hlohi

example {M D lo hi : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hDM : Nat.Coprime D M) (hlohi : lo ≤ hi) :
    |((((Finset.Ioc lo hi).filter
          (fun a ↦ D ∣ a ∧ Nat.Coprime a M)).card : ℕ) : ℝ) -
        ((M.totient : ℝ) / (M : ℝ)) *
          ((((hi - lo : ℕ) : ℝ) / (D : ℝ)))| ≤
      (M : ℝ) + 1 := by
  simpa only [coprimeMultipleIoc,
    fixedModulusReducedResidueDensity] using
    coprimeMultipleIoc_card_error_le hM hD hDM hlohi

/-! ## Paper-head specializations -/

example {W lo hi : ℕ} (hlohi : lo ≤ hi) :
    |((((Finset.Ioc lo hi).filter
          (fun a ↦
            Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) : ℝ) -
        (((((primesUpTo W).prod id).totient : ℕ) : ℝ) /
          (((primesUpTo W).prod id : ℕ) : ℝ)) *
          ((hi - lo : ℕ) : ℝ)| ≤
      (((primesUpTo W).prod id : ℕ) : ℝ) := by
  simpa only [roughHeadFree, roughHeadModulus,
    roughHeadDensity] using
    roughHeadFree_Ioc_card_error_le (W := W) hlohi

example {W D lo hi : ℕ} (hD : 0 < D)
    (hDHead : Nat.Coprime D ((primesUpTo W).prod id))
    (hlohi : lo ≤ hi) :
    |((((Finset.Ioc lo hi).filter
          (fun a ↦ D ∣ a ∧
            Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) : ℝ) -
        (((((primesUpTo W).prod id).totient : ℕ) : ℝ) /
          (((primesUpTo W).prod id : ℕ) : ℝ)) *
          ((((hi - lo : ℕ) : ℝ) / (D : ℝ)))| ≤
      (((primesUpTo W).prod id : ℕ) : ℝ) + 1 := by
  simpa only [coprimeMultipleIoc, roughHeadModulus,
    roughHeadDensity] using
    roughHeadCoprimeMultipleIoc_card_error_le hD hDHead hlohi

example {W p : ℕ} (hp : p.Prime) (hWp : W < p) :
    Nat.Coprime p ((primesUpTo W).prod id) := by
  simpa only [roughHeadModulus] using
    prime_coprime_roughHeadModulus_of_cutoff_lt hp hWp

example {W p k lo hi : ℕ} (hp : p.Prime) (hWp : W < p)
    (hlohi : lo ≤ hi) :
    |((((Finset.Ioc lo hi).filter
          (fun a ↦ p ^ k ∣ a ∧
            Nat.Coprime a ((primesUpTo W).prod id))).card : ℕ) : ℝ) -
        (((((primesUpTo W).prod id).totient : ℕ) : ℝ) /
          (((primesUpTo W).prod id : ℕ) : ℝ)) *
          ((((hi - lo : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ)))| ≤
      (((primesUpTo W).prod id : ℕ) : ℝ) + 1 := by
  simpa only [coprimeMultipleIoc, roughHeadModulus,
    roughHeadDensity] using
    roughHeadPrimePowerMultipleIoc_card_error_le hp hWp hlohi

end

end Erdos390.WholePaper
