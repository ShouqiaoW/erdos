import Erdos390.WholePaper.BankPaperFourFiveLebesgueCellAggregationBound

/-!
# Exact common physical domain for the real last-prime endpoint

For a fixed prime prefix `q`, put `Q = prod_i q_i`.  The exact real
last-prime substitution has physical interval

`(max (Q*y) A, B]`.

This file rewrites that interval as the common outer interval `(A,B]`, with
the literal support cutoff `Q*y < t`.  The logarithmic identity

`log (t / Q) = log y * (log_y t - sum_i log_y q_i)`

then identifies the prefix summand with the moving-simplex kernel.  Finally,
finite prefix sums are commuted with the outer integral and, in dimensions
one, two, and three, the `Fin m` prefix sum is expanded into the nested
finite products already used by the product-measure telescope.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open MeasureTheory

/-! ## A fixed-domain cutoff for one prefix -/

/-- The exposed last-prime kernel, extended by zero from its moving physical
interval to the common outer interval. -/
def fourFiveRealPrefixCutoffKernel
    (Q : Real) (y : Nat) (t : Real) : Real :=
  if Q * (y : Real) < t then
    1 / Real.log (t / Q)
  else 0

private theorem intervalIntegrable_of_measurable_of_abs_le_const_commonDomain
    {F : Real -> Real} {a b C : Real}
    (hF : Measurable F) (hbound : ∀ t ∈ Set.uIcc a b, |F t| <= C) :
    IntervalIntegrable F volume a b := by
  refine (intervalIntegrable_const (c := C)).mono_fun' ?_ ?_
  · exact hF.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    simpa only [Real.norm_eq_abs] using hbound t (Set.uIoc_subset_uIcc ht)

private theorem measurable_fourFiveRealPrefixCutoffKernel
    (Q : Real) (y : Nat) :
    Measurable (fourFiveRealPrefixCutoffKernel Q y) := by
  have hactive : MeasurableSet {t : Real | Q * (y : Real) < t} :=
    measurableSet_lt measurable_const measurable_id
  have hquot : Measurable (fun t : Real => t / Q) :=
    measurable_id.div_const Q
  have hkernel : Measurable (fun t : Real => 1 / Real.log (t / Q)) :=
    measurable_const.div (Real.measurable_log.comp hquot)
  unfold fourFiveRealPrefixCutoffKernel
  exact Measurable.ite hactive hkernel measurable_const

private theorem abs_fourFiveRealPrefixCutoffKernel_le
    {Q : Real} {y : Nat} (hQ : 0 < Q) (hy : 2 <= y) (t : Real) :
    |fourFiveRealPrefixCutoffKernel Q y t| <=
      1 / Real.log (y : Real) := by
  have hy1 : (1 : Real) < (y : Real) := by
    exact_mod_cast (show 1 < y by omega)
  have hlogy : 0 < Real.log (y : Real) := Real.log_pos hy1
  unfold fourFiveRealPrefixCutoffKernel
  split_ifs with ht
  · have hyquot : (y : Real) < t / Q := by
      exact (lt_div_iff₀ hQ).2 (by simpa [mul_comm] using ht)
    have hlogquot : Real.log (y : Real) < Real.log (t / Q) :=
      Real.log_lt_log (by positivity) hyquot
    have hquotpos : 0 < Real.log (t / Q) := hlogy.trans hlogquot
    rw [abs_of_pos (one_div_pos.mpr hquotpos)]
    exact one_div_le_one_div_of_le hlogy hlogquot.le
  · rw [abs_zero]
    exact one_div_nonneg.mpr hlogy.le

private theorem intervalIntegrable_fourFiveRealPrefixCutoffKernel
    {Q : Real} {y A B : Nat} (hQ : 0 < Q) (hy : 2 <= y) :
    IntervalIntegrable (fourFiveRealPrefixCutoffKernel Q y)
      volume (A : Real) (B : Real) := by
  apply intervalIntegrable_of_measurable_of_abs_le_const_commonDomain
    (measurable_fourFiveRealPrefixCutoffKernel Q y)
  intro t _ht
  exact abs_fourFiveRealPrefixCutoffKernel_le hQ hy t

private theorem fourFiveRealPrefixCutoffKernel_zero_left
    {Q : Real} {y A : Nat} (_hQ : 0 < Q) :
    (∫ t in (A : Real)..
        max (Q * (y : Real)) (A : Real),
      fourFiveRealPrefixCutoffKernel Q y t) = 0 := by
  by_cases hQA : Q * (y : Real) <= (A : Real)
  · rw [max_eq_right hQA]
    simp
  · have hAQ : (A : Real) <= Q * (y : Real) := le_of_not_ge hQA
    rw [max_eq_left hAQ]
    calc
      (∫ t in (A : Real)..(Q * (y : Real)),
          fourFiveRealPrefixCutoffKernel Q y t) =
        ∫ _t in (A : Real)..(Q * (y : Real)), (0 : Real) := by
          apply intervalIntegral.integral_congr
          intro t ht
          have htIcc :
              t ∈ Set.Icc (A : Real) (Q * (y : Real)) := by
            rw [← Set.uIcc_of_le hAQ]
            exact ht
          unfold fourFiveRealPrefixCutoffKernel
          rw [if_neg]
          exact not_lt_of_ge htIcc.2
      _ = 0 := by simp

/-- A real last-prime physical integral is exactly its common-domain cutoff
integral.  No endpoint rounding remains. -/
theorem fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral
    {m y A B : Nat} {q : Fin m -> Nat}
    (hy : 2 <= y) (_hyA : y <= A) (hAB : A <= B)
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealPhysicalIntegral q y A B =
      (fourFiveRealPrefixProduct q)⁻¹ *
        ∫ t in (A : Real)..(B : Real),
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t := by
  have hQ : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  rw [fourFiveLastPrimeRealPhysicalIntegral_eq_maxIntegral hq]
  by_cases hLU : fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B
  · rw [if_pos hLU]
    have hLB : max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) <=
        (B : Real) := by
      calc
        max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) =
            fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealLower q y A :=
          (fourFiveRealPrefixProduct_mul_realLower hq).symm
        _ <= fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealUpper q B :=
          mul_le_mul_of_nonneg_left hLU hQ.le
        _ = (B : Real) := fourFiveRealPrefixProduct_mul_realUpper hq
    let L : Real :=
      max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real)
    have hAL : (A : Real) <= L := le_max_right _ _
    have hcut := intervalIntegrable_fourFiveRealPrefixCutoffKernel
      (Q := fourFiveRealPrefixProduct q) (A := A) (B := B) hQ hy
    have hparts := (IntervalIntegrable.trans_iff
      (a := (A : Real)) (b := L) (c := (B : Real))
      (Set.mem_uIcc_of_le hAL hLB)).mp hcut
    have hright :
        (∫ t in L..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) =
          ∫ t in L..(B : Real),
            1 / Real.log (t / fourFiveRealPrefixProduct q) := by
      apply intervalIntegral.integral_congr_ae'
      · filter_upwards with t
        intro ht
        unfold fourFiveRealPrefixCutoffKernel
        rw [if_pos]
        exact (le_max_left _ _).trans_lt ht.1
      · filter_upwards with t
        intro ht
        exact (not_lt_of_ge (ht.2.trans hLB) ht.1).elim
    have hleft :
        (∫ t in (A : Real)..L,
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t) = 0 := by
      simpa [L] using fourFiveRealPrefixCutoffKernel_zero_left
        (Q := fourFiveRealPrefixProduct q) (y := y) (A := A) hQ
    calc
      (fourFiveRealPrefixProduct q)⁻¹ *
          (∫ t in L..(B : Real),
            1 / Real.log (t / fourFiveRealPrefixProduct q)) =
        (fourFiveRealPrefixProduct q)⁻¹ *
          (∫ t in L..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) := by rw [hright]
      _ = (fourFiveRealPrefixProduct q)⁻¹ *
          (∫ t in (A : Real)..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) := by
        rw [← intervalIntegral.integral_add_adjacent_intervals
          hparts.1 hparts.2, hleft, zero_add]
  · rw [if_neg hLU]
    have hnotLB : ¬ (max (fourFiveRealPrefixProduct q * (y : Real))
        (A : Real) <= (B : Real)) := by
      intro hLB
      have hmul : fourFiveRealPrefixProduct q *
          fourFiveLastPrimeRealLower q y A <=
          fourFiveRealPrefixProduct q *
            fourFiveLastPrimeRealUpper q B := by
        simpa [fourFiveRealPrefixProduct_mul_realLower hq,
          fourFiveRealPrefixProduct_mul_realUpper hq] using hLB
      exact hLU ((mul_le_mul_iff_of_pos_left hQ).mp hmul)
    have hBy : (B : Real) <= fourFiveRealPrefixProduct q * (y : Real) := by
      have : (B : Real) <
          max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) :=
        lt_of_not_ge hnotLB
      rcases lt_max_iff.mp this with h | h
      · exact h.le
      · exact (not_lt_of_ge hAB' h).elim
    have hzero :
        (∫ t in (A : Real)..(B : Real),
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t) = 0 := by
      calc
        (∫ t in (A : Real)..(B : Real),
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t) =
          ∫ _t in (A : Real)..(B : Real), (0 : Real) := by
            apply intervalIntegral.integral_congr
            intro t ht
            have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
              rw [← Set.uIcc_of_le hAB']
              exact ht
            unfold fourFiveRealPrefixCutoffKernel
            rw [if_neg]
            exact not_lt_of_ge (htIcc.2.trans hBy)
        _ = 0 := by simp
    rw [hzero, mul_zero]

/-! ## Logarithmic cancellation inside one prefix summand -/

/-- The common-domain moving-simplex summand attached to one prime prefix. -/
def fourFivePrimePrefixMovingTerm
    {m : Nat} (q : Fin m -> Nat) (y : Nat) (t : Real) : Real :=
  (∏ i, ((q i : Nat) : Real)⁻¹) *
    if (∑ i, fourFiveLogCoordinate y (q i)) <
        fourFiveRealLogCoordinate y t - 1 then
      (fourFiveRealLogCoordinate y t -
        ∑ i, fourFiveLogCoordinate y (q i))⁻¹
    else 0

private theorem fourFiveRealPrefixProduct_eq_prod_natCast
    {m : Nat} (q : Fin m -> Nat) :
    fourFiveRealPrefixProduct q = ∏ i, ((q i : Nat) : Real) := by
  unfold fourFiveRealPrefixProduct
  rw [Nat.cast_prod]

private theorem fourFiveRealPrefixProduct_inv_eq_prod_inv
    {m : Nat} (q : Fin m -> Nat) :
    (fourFiveRealPrefixProduct q)⁻¹ =
      ∏ i, ((q i : Nat) : Real)⁻¹ := by
  unfold fourFiveRealPrefixProduct
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib]

private theorem fourFiveRealPrefixProduct_logCoordinate
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    Real.log (fourFiveRealPrefixProduct q) / Real.log (y : Real) =
      ∑ i, fourFiveLogCoordinate y (q i) := by
  have hqi : ∀ i : Fin m, ((q i : Nat) : Real) ≠ 0 := by
    intro i
    exact_mod_cast (mem_fourFiveOrderedPrimePrefixSet.mp hq i).2.2.ne_zero
  unfold fourFiveRealPrefixProduct fourFiveLogCoordinate
  rw [Nat.cast_prod, Real.log_prod]
  · exact Finset.sum_div (Finset.univ : Finset (Fin m))
      (fun i => Real.log ((q i : Nat) : Real)) (Real.log (y : Real))
  · intro i _hi
    exact hqi i

private theorem fourFiveRealPrefix_support_iff
    {m y B : Nat} {q : Fin m -> Nat}
    (hy : 2 <= y) (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B)
    {t : Real} (ht : 0 < t) :
    fourFiveRealPrefixProduct q * (y : Real) < t ↔
      (∑ i, fourFiveLogCoordinate y (q i)) <
        fourFiveRealLogCoordinate y t - 1 := by
  have hQ : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hypos : (0 : Real) < (y : Real) := by positivity
  have hyne : (y : Real) ≠ 0 := hypos.ne'
  have hlogy : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hcoord := fourFiveRealPrefixProduct_logCoordinate hq
  rw [← hcoord, lt_sub_iff_add_lt]
  constructor
  · intro hprod
    have hlogprod :
        Real.log (fourFiveRealPrefixProduct q * (y : Real)) <
          Real.log t :=
      Real.log_lt_log (mul_pos hQ hypos) hprod
    rw [Real.log_mul hQ.ne' hyne] at hlogprod
    have hdiv := (div_lt_div_iff_of_pos_right hlogy).2 hlogprod
    simpa [fourFiveRealLogCoordinate, add_div, hlogy.ne'] using hdiv
  · intro hcoordlt
    have hdiv :
        (Real.log (fourFiveRealPrefixProduct q) + Real.log (y : Real)) /
            Real.log (y : Real) <
          Real.log t / Real.log (y : Real) := by
      simpa [fourFiveRealLogCoordinate, add_div, hlogy.ne'] using hcoordlt
    have hlogprod := (div_lt_div_iff_of_pos_right hlogy).1 hdiv
    apply (Real.log_lt_log_iff (mul_pos hQ hypos) ht).1
    rw [Real.log_mul hQ.ne' hyne]
    exact hlogprod

private theorem fourFiveRealPrefix_log_div
    {m y B : Nat} {q : Fin m -> Nat}
    (hy : 2 <= y) (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B)
    {t : Real} (ht : 0 < t) :
    Real.log (t / fourFiveRealPrefixProduct q) =
      Real.log (y : Real) *
        (fourFiveRealLogCoordinate y t -
          ∑ i, fourFiveLogCoordinate y (q i)) := by
  have hQ : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hlogy : Real.log (y : Real) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (show 1 < y by omega))).ne'
  have hcoord := fourFiveRealPrefixProduct_logCoordinate hq
  rw [Real.log_div ht.ne' hQ.ne']
  unfold fourFiveRealLogCoordinate
  rw [← hcoord]
  field_simp [hlogy]

private theorem fourFivePrimePrefixMovingTerm_eq_scaledCutoff
    {m y B : Nat} {q : Fin m -> Nat}
    (hy : 2 <= y) (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B)
    {t : Real} (ht : 0 < t) :
    fourFivePrimePrefixMovingTerm q y t =
      Real.log (y : Real) * (fourFiveRealPrefixProduct q)⁻¹ *
        fourFiveRealPrefixCutoffKernel
          (fourFiveRealPrefixProduct q) y t := by
  have hQ : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hlogy : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hsupport := fourFiveRealPrefix_support_iff hy hq ht
  have hlogdiv := fourFiveRealPrefix_log_div hy hq ht
  unfold fourFivePrimePrefixMovingTerm fourFiveRealPrefixCutoffKernel
  by_cases hactive :
      fourFiveRealPrefixProduct q * (y : Real) < t
  · have hactiveLog :
        (∑ i, fourFiveLogCoordinate y (q i)) <
          fourFiveRealLogCoordinate y t - 1 :=
      hsupport.mp hactive
    rw [if_pos hactiveLog, if_pos hactive]
    have hden : 0 < fourFiveRealLogCoordinate y t -
        ∑ i, fourFiveLogCoordinate y (q i) := by
      linarith
    rw [← fourFiveRealPrefixProduct_inv_eq_prod_inv, hlogdiv]
    field_simp [hQ.ne', hlogy.ne', hden.ne']
  · have hactiveLog :
        ¬ ((∑ i, fourFiveLogCoordinate y (q i)) <
          fourFiveRealLogCoordinate y t - 1) := by
      intro h
      exact hactive (hsupport.mpr h)
    rw [if_neg hactiveLog, if_neg hactive]
    ring

theorem intervalIntegrable_fourFivePrimePrefixMovingTerm
    {m y A B : Nat} {q : Fin m -> Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    IntervalIntegrable (fourFivePrimePrefixMovingTerm q y)
      volume (A : Real) (B : Real) := by
  have hQ : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hcut := intervalIntegrable_fourFiveRealPrefixCutoffKernel
    (Q := fourFiveRealPrefixProduct q) (A := A) (B := B) hQ hy
  have hscaled :=
    (hcut.const_mul (fourFiveRealPrefixProduct q)⁻¹).const_mul
      (Real.log (y : Real))
  apply hscaled.congr
  intro t ht
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
    simpa [Set.uIcc_of_le hAB'] using (Set.uIoc_subset_uIcc ht)
  have htpos : 0 < t := by
    have hypos : (0 : Real) < (y : Real) := by positivity
    have hyA' : (y : Real) <= (A : Real) := by exact_mod_cast hyA
    exact hypos.trans_le (hyA'.trans (htIcc.1))
  simpa [mul_assoc] using
    (fourFivePrimePrefixMovingTerm_eq_scaledCutoff hy hq htpos).symm

/-- One prefix summand after the exact real endpoint substitution, now on
the common physical interval and in the moving-simplex normalization. -/
theorem fourFiveLastPrimeRealPhysicalIntegral_eq_prefixMovingTerm
    {m y A B : Nat} {q : Fin m -> Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealPhysicalIntegral q y A B =
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFivePrimePrefixMovingTerm q y t := by
  have hQ : fourFiveRealPrefixProduct q ≠ 0 :=
    (fourFiveRealPrefixProduct_pos hq).ne'
  rw [fourFiveLastPrimeRealPhysicalIntegral_eq_cutoffIntegral
    hy hyA hAB hq]
  calc
    (fourFiveRealPrefixProduct q)⁻¹ *
        (∫ t in (A : Real)..(B : Real),
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t) =
      ∫ t in (A : Real)..(B : Real),
        (fourFiveRealPrefixProduct q)⁻¹ *
          fourFiveRealPrefixCutoffKernel
            (fourFiveRealPrefixProduct q) y t := by
      rw [intervalIntegral.integral_const_mul]
    _ = ∫ t in (A : Real)..(B : Real),
        (1 / Real.log (y : Real)) *
          fourFivePrimePrefixMovingTerm q y t := by
      apply intervalIntegral.integral_congr
      intro t ht
      have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
      have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
        simpa [Set.uIcc_of_le hAB'] using ht
      have htpos : 0 < t := by
        have hypos : (0 : Real) < (y : Real) := by positivity
        have hyA' : (y : Real) <= (A : Real) := by exact_mod_cast hyA
        exact hypos.trans_le (hyA'.trans htIcc.1)
      have hterm :=
        fourFivePrimePrefixMovingTerm_eq_scaledCutoff hy hq htpos
      have hlogy : Real.log (y : Real) ≠ 0 :=
        (Real.log_pos
          (by exact_mod_cast (show 1 < y by omega))).ne'
      calc
        (fourFiveRealPrefixProduct q)⁻¹ *
            fourFiveRealPrefixCutoffKernel
              (fourFiveRealPrefixProduct q) y t =
          (1 / Real.log (y : Real)) *
            (Real.log (y : Real) *
              (fourFiveRealPrefixProduct q)⁻¹ *
                fourFiveRealPrefixCutoffKernel
                  (fourFiveRealPrefixProduct q) y t) := by
            field_simp [hlogy]
        _ = (1 / Real.log (y : Real)) *
            fourFivePrimePrefixMovingTerm q y t :=
          congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
            hterm.symm
    _ = (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          fourFivePrimePrefixMovingTerm q y t := by
      rw [intervalIntegral.integral_const_mul]

/-! ## Finite prefix sums in dimensions one, two, and three -/

private theorem sum_piFinset_const_succ
    {α β : Type*} [DecidableEq α] [AddCommMonoid β]
    (n : Nat) (S : Finset α) (F : (Fin (n + 1) -> α) -> β) :
    (∑ q ∈ Fintype.piFinset (fun _ : Fin (n + 1) => S), F q) =
      ∑ a ∈ S,
        ∑ r ∈ Fintype.piFinset (fun _ : Fin n => S), F (Fin.cons a r) := by
  rw [← Finset.sum_product']
  apply Finset.sum_equiv
    (Fin.consEquiv (fun _ : Fin (n + 1) => α)).symm
  · intro q
    simp only [Fintype.mem_piFinset, Finset.mem_product]
    change
      (∀ i : Fin (n + 1), q i ∈ S) ↔
        q 0 ∈ S ∧ ∀ i : Fin n, q i.succ ∈ S
    exact Fin.forall_iff_succ
  · intro q _hq
    simp

private theorem sum_Ioc_anchoredReciprocal_eq_primeBand
    (y B : Nat) (K : Nat -> Real) :
    (∑ n ∈ Finset.Ioc y B,
        fourFiveAnchoredReciprocalPrimeAtom y n * K n) =
      ∑ n ∈ fourFivePrimeCoordinateBand y B,
        (n : Real)⁻¹ * K n := by
  unfold fourFivePrimeCoordinateBand
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hyn := (Finset.mem_Ioc.mp hn).1
  simp [fourFiveAnchoredReciprocalPrimeAtom,
    fourFiveReciprocalPrimeAtom, hyn, one_div]

private theorem fourFiveActualReciprocalProductOne_eq_primeBand
    (K : Nat -> Real) (y B : Nat) :
    fourFiveActualReciprocalProductOne K y B =
      ∑ p ∈ fourFivePrimeCoordinateBand y B,
        (p : Real)⁻¹ * K p := by
  unfold fourFiveActualReciprocalProductOne fourFiveFiniteProductOne
  exact sum_Ioc_anchoredReciprocal_eq_primeBand y B K

private theorem fourFiveActualReciprocalProductTwo_eq_primeBand
    (K : Nat -> Nat -> Real) (y B : Nat) :
    fourFiveActualReciprocalProductTwo K y B =
      ∑ p ∈ fourFivePrimeCoordinateBand y B, (p : Real)⁻¹ *
        ∑ q ∈ fourFivePrimeCoordinateBand y B, (q : Real)⁻¹ * K p q := by
  unfold fourFiveActualReciprocalProductTwo fourFiveFiniteProductTwo
  calc
    (∑ p ∈ Finset.Ioc y B,
        fourFiveAnchoredReciprocalPrimeAtom y p *
          ∑ q ∈ Finset.Ioc y B,
            fourFiveAnchoredReciprocalPrimeAtom y q * K p q) =
      ∑ p ∈ Finset.Ioc y B,
        fourFiveAnchoredReciprocalPrimeAtom y p *
          ∑ q ∈ fourFivePrimeCoordinateBand y B,
            (q : Real)⁻¹ * K p q := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [sum_Ioc_anchoredReciprocal_eq_primeBand]
    _ = ∑ p ∈ fourFivePrimeCoordinateBand y B, (p : Real)⁻¹ *
        ∑ q ∈ fourFivePrimeCoordinateBand y B,
          (q : Real)⁻¹ * K p q :=
      sum_Ioc_anchoredReciprocal_eq_primeBand y B _

private theorem fourFiveActualReciprocalProductThree_eq_primeBand
    (K : Nat -> Nat -> Nat -> Real) (y B : Nat) :
    fourFiveActualReciprocalProductThree K y B =
      ∑ p ∈ fourFivePrimeCoordinateBand y B, (p : Real)⁻¹ *
        ∑ q ∈ fourFivePrimeCoordinateBand y B, (q : Real)⁻¹ *
          ∑ r ∈ fourFivePrimeCoordinateBand y B,
            (r : Real)⁻¹ * K p q r := by
  unfold fourFiveActualReciprocalProductThree fourFiveFiniteProductThree
  calc
    (∑ p ∈ Finset.Ioc y B,
        fourFiveAnchoredReciprocalPrimeAtom y p *
          ∑ q ∈ Finset.Ioc y B,
            fourFiveAnchoredReciprocalPrimeAtom y q *
              ∑ r ∈ Finset.Ioc y B,
                fourFiveAnchoredReciprocalPrimeAtom y r * K p q r) =
      ∑ p ∈ Finset.Ioc y B,
        fourFiveAnchoredReciprocalPrimeAtom y p *
          ∑ q ∈ Finset.Ioc y B,
            fourFiveAnchoredReciprocalPrimeAtom y q *
              ∑ r ∈ fourFivePrimeCoordinateBand y B,
                (r : Real)⁻¹ * K p q r := by
      apply Finset.sum_congr rfl
      intro p _hp
      apply congrArg (fun z : Real =>
        fourFiveAnchoredReciprocalPrimeAtom y p * z)
      apply Finset.sum_congr rfl
      intro q _hq
      rw [sum_Ioc_anchoredReciprocal_eq_primeBand]
    _ = ∑ p ∈ Finset.Ioc y B,
        fourFiveAnchoredReciprocalPrimeAtom y p *
          ∑ q ∈ fourFivePrimeCoordinateBand y B, (q : Real)⁻¹ *
            ∑ r ∈ fourFivePrimeCoordinateBand y B,
              (r : Real)⁻¹ * K p q r := by
      apply Finset.sum_congr rfl
      intro p _hp
      rw [sum_Ioc_anchoredReciprocal_eq_primeBand]
    _ = ∑ p ∈ fourFivePrimeCoordinateBand y B, (p : Real)⁻¹ *
        ∑ q ∈ fourFivePrimeCoordinateBand y B, (q : Real)⁻¹ *
          ∑ r ∈ fourFivePrimeCoordinateBand y B,
            (r : Real)⁻¹ * K p q r :=
      sum_Ioc_anchoredReciprocal_eq_primeBand y B _

private theorem sum_fourFivePrimePrefixMovingTerm_one
    (y B : Nat) (t : Real) :
    (∑ q ∈ fourFiveOrderedPrimePrefixSet 1 y B,
        fourFivePrimePrefixMovingTerm q y t) =
      fourFiveActualReciprocalProductOne
        (fourFiveMovingSimplexKernelOne y y
          (fourFiveRealLogCoordinate y t)) y B := by
  rw [fourFiveActualReciprocalProductOne_eq_primeBand]
  unfold fourFiveOrderedPrimePrefixSet
  rw [sum_piFinset_const_succ]
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := mem_fourFivePrimeCoordinateBand.mp hp
  simp [fourFivePrimePrefixMovingTerm, fourFiveMovingSimplexKernelOne,
    fourFiveMovingFaceKernel,
    hpData.1]

private theorem sum_fourFivePrimePrefixMovingTerm_two
    (y B : Nat) (t : Real) :
    (∑ r ∈ fourFiveOrderedPrimePrefixSet 2 y B,
        fourFivePrimePrefixMovingTerm r y t) =
      fourFiveActualReciprocalProductTwo
        (fourFiveMovingSimplexKernelTwo y y
          (fourFiveRealLogCoordinate y t)) y B := by
  rw [fourFiveActualReciprocalProductTwo_eq_primeBand]
  unfold fourFiveOrderedPrimePrefixSet
  rw [sum_piFinset_const_succ]
  apply Finset.sum_congr rfl
  intro p hp
  rw [sum_piFinset_const_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  have hpData := mem_fourFivePrimeCoordinateBand.mp hp
  have hqData := mem_fourFivePrimeCoordinateBand.mp hq
  simp [fourFivePrimePrefixMovingTerm, fourFiveMovingSimplexKernelTwo,
    Fin.sum_univ_two, Fin.prod_univ_two, hpData.1, hqData.1] ;
    split_ifs <;> ring

private theorem sum_fourFivePrimePrefixMovingTerm_three
    (y B : Nat) (t : Real) :
    (∑ s ∈ fourFiveOrderedPrimePrefixSet 3 y B,
        fourFivePrimePrefixMovingTerm s y t) =
      fourFiveActualReciprocalProductThree
        (fourFiveMovingSimplexKernelThree y y
          (fourFiveRealLogCoordinate y t)) y B := by
  rw [fourFiveActualReciprocalProductThree_eq_primeBand]
  unfold fourFiveOrderedPrimePrefixSet
  rw [sum_piFinset_const_succ]
  apply Finset.sum_congr rfl
  intro p hp
  rw [sum_piFinset_const_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [sum_piFinset_const_succ]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hcons (r0 : Fin 0 -> Nat) :
      (Fin.cons p (Fin.cons q (Fin.cons r r0)) : Fin 3 -> Nat) =
        fun i => if i = (0 : Fin 3) then p else if i = (1 : Fin 3) then q else r := by
    funext i
    fin_cases i <;> rfl
  simp_rw [hcons]
  have hpData := mem_fourFivePrimeCoordinateBand.mp hp
  have hqData := mem_fourFivePrimeCoordinateBand.mp hq
  have hrData := mem_fourFivePrimeCoordinateBand.mp hr
  simp [fourFivePrimePrefixMovingTerm, fourFiveMovingSimplexKernelThree,
    Fin.sum_univ_three, Fin.prod_univ_three,
    hpData.1, hqData.1, hrData.1] ; split_ifs <;> ring

/-! ## Commuting the finite prefix sum with the outer integral -/

private theorem fourFiveOrderedLastPrimeRealPhysicalLayer_eq_prefixIntegral
    {m y A B : Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveOrderedLastPrimeRealPhysicalLayer m y A B =
      (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
            fourFivePrimePrefixMovingTerm q y t := by
  unfold fourFiveOrderedLastPrimeRealPhysicalLayer
  calc
    (∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        fourFiveLastPrimeRealPhysicalIntegral q y A B) =
      ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (1 / Real.log (y : Real)) *
          ∫ t in (A : Real)..(B : Real),
            fourFivePrimePrefixMovingTerm q y t := by
      apply Finset.sum_congr rfl
      intro q hq
      exact fourFiveLastPrimeRealPhysicalIntegral_eq_prefixMovingTerm
        hy hyA hAB hq
    _ = (1 / Real.log (y : Real)) *
        ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
          ∫ t in (A : Real)..(B : Real),
            fourFivePrimePrefixMovingTerm q y t := by
      rw [Finset.mul_sum]
    _ = (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
            fourFivePrimePrefixMovingTerm q y t := by
      rw [intervalIntegral.integral_finset_sum]
      intro q hq
      exact intervalIntegrable_fourFivePrimePrefixMovingTerm
        hy hyA hAB hq

theorem fourFiveOrderedLastPrimeRealPhysicalLayer_zero_eq_physicalActualMoving
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveOrderedLastPrimeRealPhysicalLayer 0 y A B =
      fourFivePhysicalActualMovingLayer 0 y A B := by
  have hyA' : (y : Real) <= (A : Real) := by exact_mod_cast hyA
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hlayer : fourFiveOrderedLastPrimeRealPhysicalLayer 0 y A B =
      ∫ t in (A : Real)..(B : Real), 1 / Real.log t := by
    unfold fourFiveOrderedLastPrimeRealPhysicalLayer
      fourFiveOrderedPrimePrefixSet
      fourFiveLastPrimeRealPhysicalIntegral
      fourFiveLastPrimeRealLower fourFiveLastPrimeRealUpper
      fourFiveRealPrefixProduct
    simp [hyA', hAB']
  rw [hlayer]
  unfold fourFivePhysicalActualMovingLayer
  calc
    (∫ t in (A : Real)..(B : Real), 1 / Real.log t) =
      ∫ t in (A : Real)..(B : Real),
        (1 / Real.log (y : Real)) *
          (fourFiveRealLogCoordinate y t)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro t ht
      have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
        simpa [Set.uIcc_of_le hAB'] using ht
      have htpos : 0 < t := by
        have hypos : (0 : Real) < (y : Real) := by positivity
        exact hypos.trans_le (hyA'.trans htIcc.1)
      have ht1 : (1 : Real) < t := by
        have hy1 : (1 : Real) < (y : Real) := by
          exact_mod_cast (show 1 < y by omega)
        exact hy1.trans_le (hyA'.trans htIcc.1)
      have hlogy : Real.log (y : Real) ≠ 0 :=
        (Real.log_pos
          (by exact_mod_cast (show 1 < y by omega))).ne'
      have hlogt : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
      unfold fourFiveRealLogCoordinate
      field_simp [hlogy, hlogt]
    _ = (1 / Real.log (y : Real)) *
        ∫ t in (A : Real)..(B : Real),
          (fourFiveRealLogCoordinate y t)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]

theorem fourFiveOrderedLastPrimeRealPhysicalLayer_one_eq_physicalActualMoving
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveOrderedLastPrimeRealPhysicalLayer 1 y A B =
      fourFivePhysicalActualMovingLayer 1 y A B := by
  rw [fourFiveOrderedLastPrimeRealPhysicalLayer_eq_prefixIntegral
    hy hyA hAB]
  unfold fourFivePhysicalActualMovingLayer
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t _ht
  exact sum_fourFivePrimePrefixMovingTerm_one y B t

theorem fourFiveOrderedLastPrimeRealPhysicalLayer_two_eq_physicalActualMoving
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveOrderedLastPrimeRealPhysicalLayer 2 y A B =
      fourFivePhysicalActualMovingLayer 2 y A B := by
  rw [fourFiveOrderedLastPrimeRealPhysicalLayer_eq_prefixIntegral
    hy hyA hAB]
  unfold fourFivePhysicalActualMovingLayer
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t _ht
  exact sum_fourFivePrimePrefixMovingTerm_two y B t

theorem fourFiveOrderedLastPrimeRealPhysicalLayer_three_eq_physicalActualMoving
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveOrderedLastPrimeRealPhysicalLayer 3 y A B =
      fourFivePhysicalActualMovingLayer 3 y A B := by
  rw [fourFiveOrderedLastPrimeRealPhysicalLayer_eq_prefixIntegral
    hy hyA hAB]
  unfold fourFivePhysicalActualMovingLayer
  apply congrArg (fun z : Real => (1 / Real.log (y : Real)) * z)
  apply intervalIntegral.integral_congr
  intro t _ht
  exact sum_fourFivePrimePrefixMovingTerm_three y B t

/-- Exact common-domain identification for every layer in the ordered
four/five mixture. -/
theorem fourFiveOrderedLastPrimeRealPhysicalLayer_eq_physicalActualMovingLayer
    {m y A B : Nat} (hm : m <= 3)
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveOrderedLastPrimeRealPhysicalLayer m y A B =
      fourFivePhysicalActualMovingLayer m y A B := by
  interval_cases m
  · exact fourFiveOrderedLastPrimeRealPhysicalLayer_zero_eq_physicalActualMoving
      hy hyA hAB
  · exact fourFiveOrderedLastPrimeRealPhysicalLayer_one_eq_physicalActualMoving
      hy hyA hAB
  · exact fourFiveOrderedLastPrimeRealPhysicalLayer_two_eq_physicalActualMoving
      hy hyA hAB
  · exact fourFiveOrderedLastPrimeRealPhysicalLayer_three_eq_physicalActualMoving
      hy hyA hAB

/-- The exact real-endpoint physical/common-domain residual is zero. -/
theorem abs_fourFiveOrderedLastPrimeRealPhysicalLayer_sub_physicalActualMovingLayer
    {m y A B : Nat} (hm : m <= 3)
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    |fourFiveOrderedLastPrimeRealPhysicalLayer m y A B -
        fourFivePhysicalActualMovingLayer m y A B| = 0 := by
  rw [fourFiveOrderedLastPrimeRealPhysicalLayer_eq_physicalActualMovingLayer
    hm hy hyA hAB, sub_self, abs_zero]

/-- Real-endpoint analogue of the physical-change residual used by the
earlier quotient-endpoint decomposition. -/
def fourFiveLastPrimeRealPhysicalChangeError
    (m y A B : Nat) : Real :=
  |fourFiveOrderedLastPrimeRealIntegralLayer m y A B -
    fourFivePhysicalActualMovingLayer m y A B|

theorem fourFiveLastPrimeRealPhysicalChangeError_eq_zero
    {m y A B : Nat} (hm : m <= 3)
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    fourFiveLastPrimeRealPhysicalChangeError m y A B = 0 := by
  unfold fourFiveLastPrimeRealPhysicalChangeError
  rw [fourFiveOrderedLastPrimeRealIntegralLayer_eq_physicalLayer,
    fourFiveOrderedLastPrimeRealPhysicalLayer_eq_physicalActualMovingLayer
      hm hy hyA hAB,
    sub_self, abs_zero]

/-! ## Integrated product replacement and vanishing overrun -/

/-- The one-dimensional BV discrepancy after the common outer integration
has been applied. -/
def fourFivePhysicalOuterScaledBVError
    (y A B : Nat) : Real :=
  (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
    fourFiveReciprocalBVError y

private theorem intervalIntegrable_fourFivePhysicalActualProductOne
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    IntervalIntegrable
      (fun t => fourFiveActualReciprocalProductOne
        (fourFiveMovingSimplexKernelOne y y
          (fourFiveRealLogCoordinate y t)) y B)
      volume (A : Real) (B : Real) := by
  have hsum : IntervalIntegrable
      (fun t => ∑ q ∈ fourFiveOrderedPrimePrefixSet 1 y B,
        fourFivePrimePrefixMovingTerm q y t)
      volume (A : Real) (B : Real) := by
    apply (IntervalIntegrable.sum (fourFiveOrderedPrimePrefixSet 1 y B)
      (fun q hq => intervalIntegrable_fourFivePrimePrefixMovingTerm
        hy hyA hAB hq)).congr
    intro t _ht
    simp only [Finset.sum_apply]
  apply hsum.congr
  intro t _ht
  exact sum_fourFivePrimePrefixMovingTerm_one y B t

private theorem intervalIntegrable_fourFivePhysicalActualProductTwo
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    IntervalIntegrable
      (fun t => fourFiveActualReciprocalProductTwo
        (fourFiveMovingSimplexKernelTwo y y
          (fourFiveRealLogCoordinate y t)) y B)
      volume (A : Real) (B : Real) := by
  have hsum : IntervalIntegrable
      (fun t => ∑ q ∈ fourFiveOrderedPrimePrefixSet 2 y B,
        fourFivePrimePrefixMovingTerm q y t)
      volume (A : Real) (B : Real) := by
    apply (IntervalIntegrable.sum (fourFiveOrderedPrimePrefixSet 2 y B)
      (fun q hq => intervalIntegrable_fourFivePrimePrefixMovingTerm
        hy hyA hAB hq)).congr
    intro t _ht
    simp only [Finset.sum_apply]
  apply hsum.congr
  intro t _ht
  exact sum_fourFivePrimePrefixMovingTerm_two y B t

private theorem intervalIntegrable_fourFivePhysicalActualProductThree
    {y A B : Nat} (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    IntervalIntegrable
      (fun t => fourFiveActualReciprocalProductThree
        (fourFiveMovingSimplexKernelThree y y
          (fourFiveRealLogCoordinate y t)) y B)
      volume (A : Real) (B : Real) := by
  have hsum : IntervalIntegrable
      (fun t => ∑ q ∈ fourFiveOrderedPrimePrefixSet 3 y B,
        fourFivePrimePrefixMovingTerm q y t)
      volume (A : Real) (B : Real) := by
    apply (IntervalIntegrable.sum (fourFiveOrderedPrimePrefixSet 3 y B)
      (fun q hq => intervalIntegrable_fourFivePrimePrefixMovingTerm
        hy hyA hAB hq)).congr
    intro t _ht
    simp only [Finset.sum_apply]
  apply hsum.congr
  intro t _ht
  exact sum_fourFivePrimePrefixMovingTerm_three y B t

private theorem intervalIntegrable_fourFivePhysicalContinuumProductOne
    {y A B : Nat} (hy : 2 <= y) :
    IntervalIntegrable
      (fun t => fourFiveContinuumLogLogProductOne
        (fourFiveMovingSimplexKernelOne y y
          (fourFiveRealLogCoordinate y t)) y B)
      volume (A : Real) (B : Real) := by
  have hendpoint :=
    intervalIntegrable_fourFiveLebesgueCellEndpointOne
      y B (A : Real) (B : Real)
  apply hendpoint.congr
  intro t _ht
  unfold fourFiveLebesgueCellEndpointOne
  exact (fourFiveContinuumLogLogProductOne_eq_lebesgueCells
    (fourFiveMovingSimplexKernelOne y y
      (fourFiveRealLogCoordinate y t)) hy).symm

private theorem intervalIntegrable_fourFivePhysicalContinuumProductTwo
    {y A B : Nat} (hy : 2 <= y) :
    IntervalIntegrable
      (fun t => fourFiveContinuumLogLogProductTwo
        (fourFiveMovingSimplexKernelTwo y y
          (fourFiveRealLogCoordinate y t)) y B)
      volume (A : Real) (B : Real) := by
  have hendpoint :=
    intervalIntegrable_fourFiveLebesgueCellEndpointTwo
      y B (A : Real) (B : Real)
  apply hendpoint.congr
  intro t _ht
  unfold fourFiveLebesgueCellEndpointTwo
  exact (fourFiveContinuumLogLogProductTwo_eq_lebesgueCells
    (fourFiveMovingSimplexKernelTwo y y
      (fourFiveRealLogCoordinate y t)) hy).symm

private theorem intervalIntegrable_fourFivePhysicalContinuumProductThree
    {y A B : Nat} (hy : 2 <= y) :
    IntervalIntegrable
      (fun t => fourFiveContinuumLogLogProductThree
        (fourFiveMovingSimplexKernelThree y y
          (fourFiveRealLogCoordinate y t)) y B)
      volume (A : Real) (B : Real) := by
  have hendpoint :=
    intervalIntegrable_fourFiveLebesgueCellEndpointThree
      y B (A : Real) (B : Real)
  apply hendpoint.congr
  intro t _ht
  unfold fourFiveLebesgueCellEndpointThree
  exact (fourFiveContinuumLogLogProductThree_eq_lebesgueCells
    (fourFiveMovingSimplexKernelThree y y
      (fourFiveRealLogCoordinate y t)) hy).symm

private theorem abs_scaled_intervalIntegral_sub_le_commonDomain
    {F G : Real -> Real} {a b c C : Real}
    (hab : a <= b) (hc : 0 <= c)
    (hF : IntervalIntegrable F volume a b)
    (hG : IntervalIntegrable G volume a b)
    (hdiff : ∀ t ∈ Set.uIcc a b, |F t - G t| <= C) :
    |c * (∫ t in a..b, F t) - c * (∫ t in a..b, G t)| <=
      c * (b - a) * C := by
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t => F t - G t)
    (fun t ht => by
      simpa only [Real.norm_eq_abs] using
        hdiff t (Set.uIoc_subset_uIcc ht))
  have habs : |∫ t in a..b, F t - G t| <= C * |b - a| := by
    simpa only [Real.norm_eq_abs] using hnorm
  rw [← mul_sub, ← intervalIntegral.integral_sub hF hG,
    abs_mul, abs_of_nonneg hc]
  calc
    c * |∫ t in a..b, F t - G t| <= c * (C * |b - a|) :=
      mul_le_mul_of_nonneg_left habs hc
    _ = c * (b - a) * C := by
      rw [abs_of_nonneg (sub_nonneg.mpr hab)]
      ring

theorem fourFivePhysicalProductReplacementError_one_le_outer
    {y A B : Nat}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y) :
    fourFivePhysicalProductReplacementError 1 y A B <=
      (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
        (2 * fourFiveReciprocalBVError y) := by
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hc : 0 <= 1 / Real.log (y : Real) :=
    one_div_nonneg.mpr
      (Real.log_pos
        (by exact_mod_cast (show 1 < y by omega))).le
  unfold fourFivePhysicalProductReplacementError
    fourFivePhysicalActualMovingLayer fourFivePhysicalContinuumCellLayer
  exact abs_scaled_intervalIntegral_sub_le_commonDomain hAB' hc
    (intervalIntegrable_fourFivePhysicalActualProductOne hy hyA hAB)
    (intervalIntegrable_fourFivePhysicalContinuumProductOne hy)
    (fun t _ht => abs_fourFivePhysicalMovingProductOne_sub_cell_le
      hy hcut (hyA.trans hAB))

theorem fourFivePhysicalProductReplacementError_two_le_outer
    {y A B : Nat} {M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M) :
    fourFivePhysicalProductReplacementError 2 y A B <=
      (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
        (4 * fourFiveReciprocalBVError y * M) := by
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hc : 0 <= 1 / Real.log (y : Real) :=
    one_div_nonneg.mpr
      (Real.log_pos
        (by exact_mod_cast (show 1 < y by omega))).le
  unfold fourFivePhysicalProductReplacementError
    fourFivePhysicalActualMovingLayer fourFivePhysicalContinuumCellLayer
  exact abs_scaled_intervalIntegral_sub_le_commonDomain hAB' hc
    (intervalIntegrable_fourFivePhysicalActualProductTwo hy hyA hAB)
    (intervalIntegrable_fourFivePhysicalContinuumProductTwo hy)
    (fun t _ht => abs_fourFivePhysicalMovingProductTwo_sub_cell_le
      hy hcut (hyA.trans hAB) hactualMass hcontinuumMass)

theorem fourFivePhysicalProductReplacementError_three_le_outer
    {y A B : Nat} {M : Real}
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M) :
    fourFivePhysicalProductReplacementError 3 y A B <=
      (1 / Real.log (y : Real)) * ((B : Real) - (A : Real)) *
        (6 * fourFiveReciprocalBVError y * M ^ 2) := by
  have hAB' : (A : Real) <= (B : Real) := by exact_mod_cast hAB
  have hc : 0 <= 1 / Real.log (y : Real) :=
    one_div_nonneg.mpr
      (Real.log_pos
        (by exact_mod_cast (show 1 < y by omega))).le
  unfold fourFivePhysicalProductReplacementError
    fourFivePhysicalActualMovingLayer fourFivePhysicalContinuumCellLayer
  exact abs_scaled_intervalIntegral_sub_le_commonDomain hAB' hc
    (intervalIntegrable_fourFivePhysicalActualProductThree hy hyA hAB)
    (intervalIntegrable_fourFivePhysicalContinuumProductThree hy)
    (fun t _ht => abs_fourFivePhysicalMovingProductThree_sub_cell_le
      hy hcut (hyA.trans hAB) hactualMass hcontinuumMass)

theorem fourFivePhysicalProductReplacementError_le_movingFaceBudget
    {m y A B : Nat} {M : Real} (hm : m <= 3)
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M) :
    fourFivePhysicalProductReplacementError m y A B <=
      fourFiveMovingFaceProductError m
        (fourFivePhysicalOuterScaledBVError y A B) M := by
  interval_cases m
  · simp [fourFivePhysicalProductReplacementError_zero,
      fourFiveMovingFaceProductError]
  · have h := fourFivePhysicalProductReplacementError_one_le_outer
      hy hyA hAB hcut
    convert h using 1 ;
      simp [fourFivePhysicalOuterScaledBVError,
        fourFiveMovingFaceProductError] ; ring
  · have h := fourFivePhysicalProductReplacementError_two_le_outer
      hy hyA hAB hcut hactualMass hcontinuumMass
    convert h using 1 ;
      simp [fourFivePhysicalOuterScaledBVError,
        fourFiveMovingFaceProductError] ; ring
  · have h := fourFivePhysicalProductReplacementError_three_le_outer
      hy hyA hAB hcut hactualMass hcontinuumMass
    convert h using 1 ;
      simp [fourFivePhysicalOuterScaledBVError,
        fourFiveMovingFaceProductError] ; ring

/-- With the outer-scaled one-dimensional BV error chosen as the assembly
parameter, the positive product-budget overrun vanishes in all four layers. -/
theorem fourFivePhysicalProductBudgetOverrun_eq_zero_outerScaled
    {m y A B : Nat} {M : Real} (hm : m <= 3)
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M) :
    fourFivePhysicalProductBudgetOverrun m y A B
      (fourFivePhysicalOuterScaledBVError y A B) M = 0 := by
  have hbudget := fourFivePhysicalProductReplacementError_le_movingFaceBudget
    hm hy hyA hAB hcut hactualMass hcontinuumMass
  unfold fourFivePhysicalProductBudgetOverrun
  rw [max_eq_left (sub_nonpos.mpr hbudget)]

/-! ## Fully bounded real-endpoint bridge and factorial assembly -/

private theorem sum_abs_anchoredLogLogCell_eq_lebesgueCell
    {y B : Nat} (hy : 2 <= y) :
    (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) =
      ∑ i ∈ Finset.Ioc y B,
        |fourFiveLogLogLebesgueCellAtom i| := by
  apply Finset.sum_congr rfl
  intro i hi
  rw [fourFiveAnchoredLogLogCellAtom_eq_lebesgueCell hy,
    if_pos (Finset.mem_Ioc.mp hi).1]

private theorem abs_sub_le_three_stage_commonDomain
    (a b c d e : Real) (hbc : b = c) :
    |a - e| <= |a - b| + |c - d| + |d - e| := by
  have hsplit : a - e = (a - b) + (c - d) + (d - e) := by
    rw [← hbc]
    ring
  rw [hsplit]
  calc
    |(a - b) + (c - d) + (d - e)| <=
        |(a - b) + (c - d)| + |d - e| := abs_add_le _ _
    _ <= (|a - b| + |c - d|) + |d - e| :=
      add_le_add_left (abs_add_le _ _) _

private theorem abs_fourFiveRealLastPrimeLayer_sub_fixed_decomposition
    {m y A B : Nat} (hm : m <= 3)
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B) :
    |fourFiveOrderedLastPrimeRealIntegralLayer m y A B -
        fourFiveFixedContinuumLayer m y A B| <=
      fourFivePhysicalProductReplacementError m y A B +
        fourFiveLebesgueCellAggregationError m y A B +
        fourFiveMovingToFixedSimplexError m y A B := by
  have hrealActual :
      fourFiveOrderedLastPrimeRealIntegralLayer m y A B =
        fourFivePhysicalActualMovingLayer m y A B :=
    (fourFiveOrderedLastPrimeRealIntegralLayer_eq_physicalLayer m y A B).trans
      (fourFiveOrderedLastPrimeRealPhysicalLayer_eq_physicalActualMovingLayer
        hm hy hyA hAB)
  have hcell : fourFivePhysicalContinuumCellLayer m y A B =
      fourFivePhysicalLebesgueCellLayer m y A B := by
    interval_cases m
    · exact fourFivePhysicalContinuumCellLayer_zero_eq_lebesgue y A B
    · exact fourFivePhysicalContinuumCellLayer_one_eq_lebesgue hy
    · exact fourFivePhysicalContinuumCellLayer_two_eq_lebesgue hy
    · exact fourFivePhysicalContinuumCellLayer_three_eq_lebesgue hy
  rw [hrealActual]
  simpa only [fourFivePhysicalProductReplacementError,
    fourFiveLebesgueCellAggregationError,
    fourFiveMovingToFixedSimplexError] using
      abs_sub_le_three_stage_commonDomain
        (fourFivePhysicalActualMovingLayer m y A B)
        (fourFivePhysicalContinuumCellLayer m y A B)
        (fourFivePhysicalLebesgueCellLayer m y A B)
        (fourFivePhysicalMovingSimplexLayer m y A B)
        (fourFiveFixedContinuumLayer m y A B) hcell

/-- Every residual between the exact real last-prime integral and the fixed
continuum layer is now either zero or bounded by an explicit displayed
budget. -/
theorem abs_fourFiveRealLastPrimeIntegralLayer_sub_fixed_le_fullyBounded
    {m y A B : Nat} {M : Real} (hm : m <= 3)
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M)
    (hu1 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t)
    (hu2 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t)
    (hu3 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t) :
    |fourFiveOrderedLastPrimeRealIntegralLayer m y A B -
        fourFiveFixedContinuumLayer m y A B| <=
      fourFiveMovingFaceProductError m
          (fourFivePhysicalOuterScaledBVError y A B) M +
        fourFiveLebesgueCellAggregationBudget m y A B M := by
  have hlebesgueMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveLogLogLebesgueCellAtom i|) <= M := by
    rw [← sum_abs_anchoredLogLogCell_eq_lebesgueCell hy]
    exact hcontinuumMass
  have hdecomp := abs_fourFiveRealLastPrimeLayer_sub_fixed_decomposition
    (m := m) (y := y) (A := A) (B := B) hm hy hyA hAB
  have hproduct := fourFivePhysicalProductReplacementError_le_movingFaceBudget
    (m := m) (y := y) (A := A) (B := B) (M := M)
    hm hy hyA hAB hcut hactualMass hcontinuumMass
  have haggregation := fourFiveLebesgueCellAggregationError_le_budget
    (m := m) (y := y) (A := A) (B := B) (M := M)
    hm hy hyA hAB hlebesgueMass
  have hmove : fourFiveMovingToFixedSimplexError m y A B = 0 := by
    interval_cases m
    · exact fourFiveMovingToFixedSimplexError_zero y A B
    · exact fourFiveMovingToFixedSimplexError_one_eq_zero hu1
    · exact fourFiveMovingToFixedSimplexError_two_eq_zero hu2
    · exact fourFiveMovingToFixedSimplexError_three_eq_zero hu3
  calc
    |fourFiveOrderedLastPrimeRealIntegralLayer m y A B -
        fourFiveFixedContinuumLayer m y A B| <=
      fourFivePhysicalProductReplacementError m y A B +
        fourFiveLebesgueCellAggregationError m y A B +
        fourFiveMovingToFixedSimplexError m y A B := hdecomp
    _ <= fourFiveMovingFaceProductError m
          (fourFivePhysicalOuterScaledBVError y A B) M +
        fourFiveLebesgueCellAggregationBudget m y A B M + 0 :=
      add_le_add (add_le_add hproduct haggregation) (le_of_eq hmove)
    _ = fourFiveMovingFaceProductError m
          (fourFivePhysicalOuterScaledBVError y A B) M +
        fourFiveLebesgueCellAggregationBudget m y A B M := by ring

/-- The fully explicit real-endpoint error ledger.  The physical-domain and
moving/fixed errors are absent because they are exact equalities, while the
product overrun has been proved zero. -/
def fourFiveRealEndpointFullyBoundedAssemblyError
    (C : Real) (y A B : Nat) (M : Real) : Real :=
  fourFiveFactorialErrorLedger
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 0 y A B +
      fourFiveMovingFaceProductError 0
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 0 y A B M)
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 1 y A B +
      fourFiveMovingFaceProductError 1
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 1 y A B M)
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 2 y A B +
      fourFiveMovingFaceProductError 2
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 2 y A B M)
    (fourFiveOrderedLastPrimeRealEndpointErrorLayer C 3 y A B +
      fourFiveMovingFaceProductError 3
        (fourFivePhysicalOuterScaledBVError y A B) M +
      fourFiveLebesgueCellAggregationBudget 3 y A B M)

private theorem abs_fourFiveOrderedPrimeLayerMass_sub_fixed_le_realEndpoint
    {m y A B : Nat} {C X0 M : Real} (hm : m <= 3)
    (hC : 0 < C) (hX0 : 3 <= X0) (hyX0 : X0 <= (y : Real))
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M)
    (hu1 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t)
    (hu2 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t)
    (hu3 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t)
    (hPNT : ∀ a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    |(fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
        fourFiveFixedContinuumLayer m y A B| <=
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B +
        fourFiveMovingFaceProductError m
          (fourFivePhysicalOuterScaledBVError y A B) M +
        fourFiveLebesgueCellAggregationBudget m y A B M := by
  have hend := abs_fourFiveOrderedPrimeLayerMass_sub_realLastPrimeIntegral_le
    (m := m) (y := y) (A := A) (B := B) (C := C) (X0 := X0)
    hC hX0 hyX0 hPNT
  have hbridge :=
    abs_fourFiveRealLastPrimeIntegralLayer_sub_fixed_le_fullyBounded
      (m := m) (y := y) (A := A) (B := B) (M := M)
      hm hy hyA hAB hcut hactualMass hcontinuumMass hu1 hu2 hu3
  calc
    |(fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
        fourFiveFixedContinuumLayer m y A B| <=
      |(fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
        fourFiveOrderedLastPrimeRealIntegralLayer m y A B| +
      |fourFiveOrderedLastPrimeRealIntegralLayer m y A B -
        fourFiveFixedContinuumLayer m y A B| := by
      rw [show
        (fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
            fourFiveFixedContinuumLayer m y A B =
          ((fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
            fourFiveOrderedLastPrimeRealIntegralLayer m y A B) +
          (fourFiveOrderedLastPrimeRealIntegralLayer m y A B -
            fourFiveFixedContinuumLayer m y A B) by ring]
      exact abs_add_le _ _
    _ <= fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B +
        (fourFiveMovingFaceProductError m
          (fourFivePhysicalOuterScaledBVError y A B) M +
          fourFiveLebesgueCellAggregationBudget m y A B M) :=
      add_le_add hend hbridge
    _ = fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B +
        fourFiveMovingFaceProductError m
          (fourFivePhysicalOuterScaledBVError y A B) M +
        fourFiveLebesgueCellAggregationBudget m y A B M := by ring

/-- Final ordered-mixture estimate assembled directly from the exact
real-endpoint PNT branch.  Every continuum residual is explicit, bounded,
or proved zero. -/
theorem fourFiveOrderedPrimeMixtureEstimate_realEndpoint_fullyBounded
    {y A B : Nat} {C X0 M : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hyX0 : X0 <= (y : Real))
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M)
    (hu1 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t)
    (hu2 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t)
    (hu3 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t)
    (hPNT : ∀ a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (fourFiveContinuumOrderedMixtureMain y A B)
      (fourFiveRealEndpointFullyBoundedAssemblyError C y A B M) := by
  have h0 := abs_fourFiveOrderedPrimeLayerMass_sub_fixed_le_realEndpoint
    (m := 0) (y := y) (A := A) (B := B) (C := C) (X0 := X0) (M := M)
    (by norm_num) hC hX0 hyX0 hy hyA hAB hcut
      hactualMass hcontinuumMass hu1 hu2 hu3 hPNT
  have h1 := abs_fourFiveOrderedPrimeLayerMass_sub_fixed_le_realEndpoint
    (m := 1) (y := y) (A := A) (B := B) (C := C) (X0 := X0) (M := M)
    (by norm_num) hC hX0 hyX0 hy hyA hAB hcut
      hactualMass hcontinuumMass hu1 hu2 hu3 hPNT
  have h2 := abs_fourFiveOrderedPrimeLayerMass_sub_fixed_le_realEndpoint
    (m := 2) (y := y) (A := A) (B := B) (C := C) (X0 := X0) (M := M)
    (by norm_num) hC hX0 hyX0 hy hyA hAB hcut
      hactualMass hcontinuumMass hu1 hu2 hu3 hPNT
  have h3 := abs_fourFiveOrderedPrimeLayerMass_sub_fixed_le_realEndpoint
    (m := 3) (y := y) (A := A) (B := B) (C := C) (X0 := X0) (M := M)
    (by norm_num) hC hX0 hyX0 hy hyA hAB hcut
      hactualMass hcontinuumMass hu1 hu2 hu3 hPNT
  unfold fourFiveContinuumOrderedMixtureMain
    fourFiveRealEndpointFullyBoundedAssemblyError
  exact fourFiveOrderedPrimeMixtureEstimate_of_layerBounds
    (y := y) (A := A) (B := B)
    (by simpa [fourFiveFixedContinuumLayer,
      fourFiveMovingFaceProductError,
      fourFiveLebesgueCellAggregationBudget] using h0)
    (by simpa [fourFiveFixedContinuumLayer] using h1)
    (by simpa [fourFiveFixedContinuumLayer] using h2)
    (by simpa [fourFiveFixedContinuumLayer] using h3)

/-- Paper-facing one-integral form of the fully bounded real-endpoint
assembly.  The padded four/five range both supplies the three strict
moving-simplex face inequalities and identifies the factorial layerwise main
with the integral of `fourFiveContinuumMixtureKernel`. -/
theorem
    fourFiveOrderedPrimeMixtureEstimate_realEndpoint_fullyBounded_mixtureIntegral
    {y A B : Nat} {C X0 M : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hyX0 : X0 <= (y : Real))
    (hy : 2 <= y) (hyA : y <= A) (hAB : A <= B)
    (hcut : fourFiveReciprocalBVSafeCutoff <= y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredReciprocalPrimeAtom y i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc y B,
        |fourFiveAnchoredLogLogCellAtom y i|) <= M)
    (hrange : ∀ t ∈ Set.Icc (A : Real) (B : Real),
      fourFiveRealLogCoordinate y t ∈
        Set.Icc ((41 : Real) / 10) ((47 : Real) / 10))
    (hPNT : ∀ a b : Real, X0 <= a -> a <= b ->
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    FourFiveOrderedPrimeMixtureEstimate y A B
      (fourFiveContinuumMixtureIntegralMain y A B)
      (fourFiveRealEndpointFullyBoundedAssemblyError C y A B M) := by
  have hAB' : (A : Real) <= (B : Real) := by
    exact_mod_cast hAB
  have hu3 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      4 < fourFiveRealLogCoordinate y t := by
    intro t ht
    have htIcc : t ∈ Set.Icc (A : Real) (B : Real) := by
      simpa [Set.uIcc_of_le hAB'] using ht
    linarith [(hrange t htIcc).1]
  have hu2 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      3 < fourFiveRealLogCoordinate y t := by
    intro t ht
    linarith [hu3 t ht]
  have hu1 : ∀ t ∈ Set.uIcc (A : Real) (B : Real),
      2 < fourFiveRealLogCoordinate y t := by
    intro t ht
    linarith [hu3 t ht]
  have hordered :=
    fourFiveOrderedPrimeMixtureEstimate_realEndpoint_fullyBounded
      (y := y) (A := A) (B := B) (C := C) (X0 := X0) (M := M)
      hC hX0 hyX0 hy hyA hAB hcut hactualMass hcontinuumMass
      hu1 hu2 hu3 hPNT
  have hrange' :
      ∀ t ∈ Set.Icc (A : Real) (B : Real),
        Real.log t / Real.log (y : Real) ∈
          Set.Icc ((41 : Real) / 10) ((47 : Real) / 10) := by
    simpa only [fourFiveRealLogCoordinate] using hrange
  have hmain :=
    fourFiveContinuumOrderedMixtureMain_eq_mixtureIntegralMain_of_paperRange
      (y := y) (A := A) (B := B) hy hyA hAB hrange'
  rw [hmain] at hordered
  exact hordered

end Erdos390.WholePaper.BankPaperRealization
