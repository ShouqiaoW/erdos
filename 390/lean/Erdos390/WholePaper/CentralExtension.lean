import Erdos390.WholePaper.FactorizationIncidence

/-!
# Extension to the central binomial endpoint

This is the exact preliminary construction in the first lower-bound lemma:
a complement representation ending at `M ≤ 2n` is extended by every integer
in `(M,2n]`, producing a distinct-factor representation of `choose (2n) n`.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

def extendComplementToTwoN (n M : ℕ) (selected : Finset ℕ) : Finset ℕ :=
  selected ∪ factorInterval M (2 * n)

theorem selected_disjoint_tail {n M : ℕ} {selected : Finset ℕ}
    (hselected : selected ⊆ factorInterval n M) :
    Disjoint selected (factorInterval M (2 * n)) := by
  rw [Finset.disjoint_left]
  intro a ha htail
  have haM : a ≤ M := (Finset.mem_Ioc.mp (hselected ha)).2
  have hMa : M < a := (Finset.mem_Ioc.mp htail).1
  omega

theorem extendComplementToTwoN_subset {n M : ℕ} {selected : Finset ℕ}
    (hnM : n ≤ M) (hM2 : M ≤ 2 * n)
    (hselected : selected ⊆ factorInterval n M) :
    extendComplementToTwoN n M selected ⊆ factorInterval n (2 * n) := by
  intro a ha
  rcases Finset.mem_union.mp ha with hs | ht
  · have hi := Finset.mem_Ioc.mp (hselected hs)
    exact Finset.mem_Ioc.mpr ⟨hi.1, hi.2.trans hM2⟩
  · have hi := Finset.mem_Ioc.mp ht
    exact Finset.mem_Ioc.mpr ⟨hnM.trans_lt hi.1, hi.2⟩

/-- Cross-multiplied form of the extension identity. -/
theorem extendComplementToTwoN_prod_mul_factorial_sq
    {n M : ℕ} {selected : Finset ℕ}
    (hM2 : M ≤ 2 * n)
    (hselected : selected ⊆ factorInterval n M)
    (hprod : selected.prod id * n.factorial ^ 2 = M.factorial) :
    (extendComplementToTwoN n M selected).prod id * n.factorial ^ 2 =
      (2 * n).factorial := by
  have hdisjoint := selected_disjoint_tail hselected
  have htail := factorInterval_prod_mul_factorial hM2
  rw [extendComplementToTwoN, Finset.prod_union hdisjoint]
  calc
    (selected.prod id * (factorInterval M (2 * n)).prod id) *
        n.factorial ^ 2 =
      (factorInterval M (2 * n)).prod id *
        (selected.prod id * n.factorial ^ 2) := by ac_rfl
    _ = (factorInterval M (2 * n)).prod id * M.factorial := by rw [hprod]
    _ = (2 * n).factorial := htail

theorem centralChoose_mul_factorial_sq (n : ℕ) :
    Nat.choose (2 * n) n * n.factorial ^ 2 = (2 * n).factorial := by
  have h := Nat.choose_mul_factorial_mul_factorial (show n ≤ 2 * n by omega)
  have hsub : 2 * n - n = n := by omega
  simpa [hsub, pow_two, mul_assoc] using h

/-- Literal product identity `prod B' = binom(2n,n)`. -/
theorem extendComplementToTwoN_prod_eq_centralChoose
    {n M : ℕ} {selected : Finset ℕ}
    (hM2 : M ≤ 2 * n)
    (hselected : selected ⊆ factorInterval n M)
    (hprod : selected.prod id * n.factorial ^ 2 = M.factorial) :
    (extendComplementToTwoN n M selected).prod id = Nat.choose (2 * n) n := by
  apply (mul_right_cancel_iff_of_pos (pow_pos (Nat.factorial_pos n) 2)).mp
  exact (extendComplementToTwoN_prod_mul_factorial_sq hM2 hselected hprod).trans
    (centralChoose_mul_factorial_sq n).symm

theorem admissibleEndpoint_gt {n M : ℕ} (hn : 3 ≤ n)
    (h : IsAdmissibleEndpoint n M) : n < M := by
  obtain ⟨factors, hfactors, hfactorProd⟩ := h
  by_contra hnM
  have hMn : M ≤ n := Nat.le_of_not_gt hnM
  have hfactorEmpty : factors = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    have hi := Finset.mem_Ioc.mp (hfactors ha)
    omega
  have hfacOne : n.factorial = 1 := by
    rw [← hfactorProd, hfactorEmpty]
    simp
  have hfacGt : 1 < n.factorial := by
    exact Nat.one_lt_factorial.mpr (by omega)
  omega

/-- Paper's exact central extension, directly from an admissible endpoint at
or below `2n`. -/
theorem exists_centralExtension_of_admissible
    {n M : ℕ} (hn : 3 ≤ n) (hM2 : M ≤ 2 * n)
    (h : IsAdmissibleEndpoint n M) :
    ∃ extended : Finset ℕ,
      extended ⊆ factorInterval n (2 * n) ∧
        extended.prod id = Nat.choose (2 * n) n := by
  have hnM : n < M := admissibleEndpoint_gt hn h
  obtain ⟨selected, hselected, hselectedQ⟩ :=
    (complement_formulation hnM).mp h
  have hcross : selected.prod id * n.factorial ^ 2 = M.factorial :=
    prod_eq_complementQuotient_iff.mp hselectedQ
  refine ⟨extendComplementToTwoN n M selected,
    extendComplementToTwoN_subset hnM.le hM2 hselected, ?_⟩
  exact extendComplementToTwoN_prod_eq_centralChoose hM2 hselected hcross

end

end Erdos390.WholePaper
