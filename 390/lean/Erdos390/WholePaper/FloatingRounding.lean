import Erdos390.WholePaper.FloatingRoundingRows
import Erdos390.WholePaper.FloatingRoundingDiscrepancy

/-!
# Column-sparse floating rounding

This is the deterministic floating-rounding lemma used in the final assembly
of the paper.  The proof iterates `exists_floating_step`, retaining all active
row equations and all columns that are still heavy.  A stronger internal
statement records that coordinates which were already integral never move.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

/-- Floating rounding with the freezing invariant made explicit. -/
theorem floating_rounding_with_frozen_coordinates
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (row : A → R) (inc : C → A → Prop) (d : ℕ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ a, x a = 0 ∨ x a = 1 → X a = x a) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ c, |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤ (4 * d : ℝ) := by
  classical
  generalize hm : (fractionalSupport x).card = m
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
      by_cases hF : (fractionalSupport x).Nonempty
      · let F : Finset A := fractionalSupport x
        let AR : Finset R := activeRows F row
        let HC : Finset C := heavyColumns F inc d
        let E : Type _ := Sum ↥AR ↥HC
        let w : E → A → ℝ := fun e a ↦ match e with
          | Sum.inl r => zeroOneColumn (fun r' a' ↦ row a' = r') r.1 a
          | Sum.inr c => zeroOneColumn inc c.1 a
        have htwo : ∀ r ∈ activeRows F row,
            2 ≤ (rowFiber F row r).card := by
          simpa only [F] using
            two_le_card_rowFiber_of_integer_rowSums row x hx hrowInt
        have hcount : AR.card + HC.card < F.card := by
          simpa only [AR, HC] using
            card_activeRows_add_heavyColumns_lt F row inc d
              (by simpa only [F] using hF) htwo hsparse
        have hEcard : Fintype.card E < (fractionalSupport x).card := by
          simpa only [E, Fintype.card_sum, Fintype.card_coe, F] using hcount
        obtain ⟨x', hx', hfreezeStep, hpreserve, hdecrease⟩ :=
          exists_floating_step w x hx hEcard
        have hrowWeight (v : A → ℝ) (r : R) :
            (∑ a, zeroOneColumn (fun r' a' ↦ row a' = r') r a * v a) =
              ∑ a ∈ rowSet row r, v a := by
          simp [zeroOneColumn, rowSet, Finset.sum_filter]
        have hrowStep : ∀ r, ∑ a ∈ rowSet row r, x' a =
            ∑ a ∈ rowSet row r, x a := by
          intro r
          by_cases hr : r ∈ AR
          · have hp := hpreserve (Sum.inl (⟨r, hr⟩ : ↥AR))
            rw [← hrowWeight x' r, ← hrowWeight x r]
            simpa only [w] using hp
          · apply Finset.sum_congr rfl
            intro a ha
            have harow : row a = r := mem_rowSet.mp ha
            have haNotF : a ∉ F := by
              intro haF
              exact hr (by
                simpa only [AR, mem_activeRows] using ⟨a, haF, harow⟩)
            have haInt : x a = 0 ∨ x a = 1 := by
              by_contra hnot
              push_neg at hnot
              exact haNotF (by
                simpa only [F, mem_fractionalSupport] using hnot)
            exact hfreezeStep a haInt
        have hrowInt' : ∀ r, ∃ k : ℤ,
            ∑ a ∈ rowSet row r, x' a = (k : ℝ) := by
          intro r
          obtain ⟨k, hk⟩ := hrowInt r
          exact ⟨k, (hrowStep r).trans hk⟩
        have hcolStep (c : C) (hc : c ∈ HC) :
            (∑ a, zeroOneColumn inc c a * x' a) =
              ∑ a, zeroOneColumn inc c a * x a := by
          have hp := hpreserve (Sum.inr (⟨c, hc⟩ : ↥HC))
          simpa only [w] using hp
        have hlt : (fractionalSupport x').card < m := by
          rw [← hm]
          exact hdecrease
        obtain ⟨X, hXInt, hfreezeIH, hrowIH, hcolIH⟩ :=
          ih (fractionalSupport x').card hlt x' hx' hrowInt'
            (rfl : (fractionalSupport x').card =
              (fractionalSupport x').card)
        have hXbounds : ∀ a, 0 ≤ X a ∧ X a ≤ 1 := by
          intro a
          rcases hXInt a with hzero | hone
          · simp [hzero]
          · simp [hone]
        have hfreeze : ∀ a, x a = 0 ∨ x a = 1 → X a = x a := by
          intro a ha
          have hstep : x' a = x a := hfreezeStep a ha
          have ha' : x' a = 0 ∨ x' a = 1 := by
            rw [hstep]
            exact ha
          exact (hfreezeIH a ha').trans hstep
        refine ⟨X, hXInt, hfreeze, ?_, ?_⟩
        · intro r
          exact (hrowIH r).trans (hrowStep r)
        · intro c
          by_cases hc : c ∈ HC
          · have hdiff :
                (∑ a, (X a - x a) * zeroOneColumn inc c a) =
                  ∑ a, (X a - x' a) * zeroOneColumn inc c a := by
              simp only [sub_mul, Finset.sum_sub_distrib]
              have hcstep := hcolStep c hc
              simpa only [mul_comm] using
                (congrArg
                  (fun y : ℝ ↦ (∑ a, X a * zeroOneColumn inc c a) - y)
                  hcstep).symm
            rw [hdiff]
            exact hcolIH c
          · have houtside : ∀ a ∉ F, X a = x a := by
              intro a haF
              have haInt : x a = 0 ∨ x a = 1 := by
                by_contra hnot
                push_neg at hnot
                exact haF (by
                  simpa only [F, mem_fractionalSupport] using hnot)
              exact hfreeze a haInt
            have hlight : (columnSupportIn F inc c).card ≤ 4 * d := by
              have : ¬ 4 * d < (columnSupportIn F inc c).card := by
                simpa only [HC, mem_heavyColumns] using hc
              omega
            calc
              |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤
                  ((columnSupportIn F inc c).card : ℝ) :=
                abs_column_discrepancy_le_card F inc c x X hx hXbounds houtside
              _ ≤ (4 * d : ℝ) := by exact_mod_cast hlight
      · have hnotMem : ∀ a, a ∉ fractionalSupport x := by
          intro a ha
          exact hF ⟨a, ha⟩
        have hInt : ∀ a, x a = 0 ∨ x a = 1 := by
          intro a
          by_contra hnot
          push_neg at hnot
          exact hnotMem a (mem_fractionalSupport.mpr hnot)
        refine ⟨x, hInt, ?_, ?_, ?_⟩
        · intro a _
          rfl
        · intro r
          rfl
        · intro c
          simp

/-- The paper's floating-rounding lemma: all row sums are retained exactly
and every zero-one column incurs discrepancy at most `4*d`. -/
theorem floating_rounding
    {A R C : Type*} [Fintype A] [Fintype R] [Fintype C]
    (row : A → R) (inc : C → A → Prop) (d : ℕ) (x : A → ℝ)
    (hx : ∀ a, 0 ≤ x a ∧ x a ≤ 1)
    (hrowInt : ∀ r, ∃ k : ℤ,
      ∑ a ∈ rowSet row r, x a = (k : ℝ))
    (hsparse : ∀ a,
      (columnsContaining Finset.univ inc a).card ≤ d) :
    ∃ X : A → ℝ,
      (∀ a, X a = 0 ∨ X a = 1) ∧
      (∀ r, ∑ a ∈ rowSet row r, X a =
        ∑ a ∈ rowSet row r, x a) ∧
      ∀ c, |∑ a, (X a - x a) * zeroOneColumn inc c a| ≤ (4 * d : ℝ) := by
  obtain ⟨X, hX, _, hrow, hcol⟩ :=
    floating_rounding_with_frozen_coordinates row inc d x hx hrowInt hsparse
  exact ⟨X, hX, hrow, hcol⟩

end

end Erdos390.WholePaper
