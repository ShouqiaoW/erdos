import Erdos390.WholePaper.Definitions

/-!
# Exact complement formulation

This proves the complement lemma immediately following the main theorem in
the paper.  All divisions occur in `ℚ`; the proof also exports the integral
cross-multiplication form used by later valuation arguments.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- The paper's quotient `Q(n,M) = M! / (n!)²`, interpreted exactly. -/
def complementQuotient (n M : ℕ) : ℚ :=
  (M.factorial : ℚ) / (n.factorial : ℚ) ^ 2

/-- A subset of `(n,M]` whose product is the exact complement quotient. -/
def HasComplementProduct (n M : ℕ) : Prop :=
  ∃ selected : Finset ℕ,
    selected ⊆ factorInterval n M ∧
      ((selected.prod id : ℕ) : ℚ) = complementQuotient n M

/-- Product of every integer in `(n,M]`, without truncated division. -/
theorem factorInterval_prod_mul_factorial {n M : ℕ} (hnM : n ≤ M) :
    (factorInterval n M).prod id * n.factorial = M.factorial := by
  induction M, hnM using Nat.le_induction with
  | base => simp [factorInterval]
  | succ M hnM ih =>
      rw [factorInterval, Finset.prod_Ioc_succ_top hnM, Nat.factorial_succ]
      change ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
        (M + 1) * M.factorial
      calc
        ((Finset.Ioc n M).prod id * (M + 1)) * n.factorial =
            (M + 1) * ((Finset.Ioc n M).prod id * n.factorial) := by
              ac_rfl
        _ = (M + 1) * M.factorial := by
          rw [show (Finset.Ioc n M).prod id * n.factorial = M.factorial by
            simpa [factorInterval] using ih]

/-- Equality with the rational quotient is equivalent to the exact integral
valuation/product identity. -/
theorem prod_eq_complementQuotient_iff {n M q : ℕ} :
    (q : ℚ) = complementQuotient n M ↔
      q * n.factorial ^ 2 = M.factorial := by
  rw [complementQuotient]
  have hfac : (n.factorial : ℚ) ^ 2 ≠ 0 := by positivity
  constructor
  · intro h
    have h' : (q : ℚ) * (n.factorial : ℚ) ^ 2 = (M.factorial : ℚ) :=
      (eq_div_iff hfac).mp h
    exact_mod_cast h'
  · intro h
    apply (eq_div_iff hfac).mpr
    exact_mod_cast h

theorem prod_factorial_sq_eq_of_admissible {n M : ℕ} (hnM : n ≤ M)
    (h : IsAdmissibleEndpoint n M) :
    ∃ selected : Finset ℕ,
      selected ⊆ factorInterval n M ∧
        selected.prod id * n.factorial ^ 2 = M.factorial := by
  obtain ⟨factors, hfactors, hfactorProd⟩ := h
  let selected := factorInterval n M \ factors
  refine ⟨selected, Finset.sdiff_subset, ?_⟩
  have hsplit := Finset.prod_sdiff hfactors (f := id)
  have hinterval := factorInterval_prod_mul_factorial hnM
  dsimp [selected]
  calc
    (factorInterval n M \ factors).prod id * n.factorial ^ 2 =
        ((factorInterval n M \ factors).prod id * factors.prod id) *
          n.factorial := by rw [hfactorProd, pow_two, mul_assoc]
    _ = (factorInterval n M).prod id * n.factorial := by rw [hsplit]
    _ = M.factorial := hinterval

/-- The paper's complement formulation, with exact hypotheses and domains. -/
theorem complement_formulation {n M : ℕ} (hnM : n < M) :
    IsAdmissibleEndpoint n M ↔ HasComplementProduct n M := by
  constructor
  · intro h
    obtain ⟨selected, hselected, hprod⟩ :=
      prod_factorial_sq_eq_of_admissible hnM.le h
    exact ⟨selected, hselected, prod_eq_complementQuotient_iff.mpr hprod⟩
  · rintro ⟨selected, hselected, hprod⟩
    let factors := factorInterval n M \ selected
    refine ⟨factors, Finset.sdiff_subset, ?_⟩
    have hselectedCross :
        selected.prod id * n.factorial ^ 2 = M.factorial :=
      prod_eq_complementQuotient_iff.mp hprod
    have hsplit := Finset.prod_sdiff hselected (f := id)
    have hinterval := factorInterval_prod_mul_factorial hnM.le
    have hcancel :
        selected.prod id * (factors.prod id * n.factorial) =
          selected.prod id * (n.factorial * n.factorial) := by
      calc
        selected.prod id * (factors.prod id * n.factorial) =
            (factorInterval n M).prod id * n.factorial := by
              dsimp [factors]
              rw [← hsplit]
              ac_rfl
        _ = M.factorial := hinterval
        _ = selected.prod id * n.factorial ^ 2 := hselectedCross.symm
        _ = selected.prod id * (n.factorial * n.factorial) := by rw [pow_two]
    have hselectedPos : 0 < selected.prod id := by
      exact Finset.prod_pos fun a ha =>
        Nat.zero_lt_of_lt (Finset.mem_Ioc.mp (hselected ha)).1
    have hfactorial : factors.prod id * n.factorial =
        n.factorial * n.factorial :=
      (mul_left_cancel_iff_of_pos hselectedPos).mp hcancel
    exact (mul_left_cancel_iff_of_pos (Nat.factorial_pos n)).mp (by
      simpa [mul_comm] using hfactorial)

end

end Erdos390.WholePaper
