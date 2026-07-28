import Erdos390.WholePaper.AllocationCertificateStructuralChecks
import Erdos390.WholePaper.AllocationCertificateArithmeticChecks

/-!
# Kernel-checked finite allocation certificate

This file internalizes the exact rational checker accompanying Section 4 of
the paper.  The finite computations use ordinary kernel reduction through
`decide`; in particular, no native-code decision procedure is used.
-/

open scoped BigOperators

namespace Erdos390.WholePaper

noncomputable section

open AllocationEntry

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

/-- The 211 records as a finite set.  Record-level duplicates are absent. -/
def finiteAllocationEntrySet : Finset AllocationEntry :=
  finiteAllocationEntries.toFinset

/-- The set of the 211 nonzero coordinates. -/
def finiteAllocationSupport : Finset (ℕ × ℕ) :=
  (finiteAllocationEntries.map coordinate).toFinset

/-- The sparse finite array `x^{fin}_{r,q}`.  Every coordinate not listed in
`finiteAllocationSupport` is zero by construction. -/
def finiteAllocation (r q : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    if e.row = r ∧ e.cofactor = q then e.value else 0

/-- A computationally sparse form of a row sum. -/
def finiteRowEntryMass (r : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    if e.row = r then e.value else 0

/-- The paper's finite valuation load, summed over the explicit nonzero
coordinates. -/
def finitePrimeLoad (ℓ : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    (e.cofactor.factorization ℓ : ℚ) * e.value

/-- Since every listed cofactor happens to be prime, this indicator sum is an
efficient exact checker for `finitePrimeLoad`. -/
def finitePrimeIndicatorLoad (ℓ : ℕ) : ℚ :=
  ∑ e ∈ finiteAllocationEntrySet,
    if e.cofactor = ℓ then e.value else 0

/-- A fully computable list form of `finiteRowEntryMass`, used only by the
kernel decision procedure. -/
def finiteRowListMass (r : ℕ) : ℚ :=
  (finiteAllocationRowEntries r |>.map fun e => e.value).sum

/-- A fully computable list form of `finitePrimeIndicatorLoad`. -/
def finitePrimeIndicatorListLoad (ℓ : ℕ) : ℚ :=
  (finiteAllocationPrimeEntries ℓ |>.map fun e => e.value).sum

/-! ## Exact structural checks -/

private abbrev keyLabeled (key : AllocationEntry → ℕ)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  allocationKeyLabeled key buckets

private abbrev innerOutputNodup {β : Type*} (output : AllocationEntry → β)
    (buckets : List (ℕ × List AllocationEntry)) : Prop :=
  allocationInnerOutputNodup output buckets

private theorem keyLabeled_append {key : AllocationEntry → ℕ}
    {left right : List (ℕ × List AllocationEntry)}
    (hleft : keyLabeled key left) (hright : keyLabeled key right) :
    keyLabeled key (left ++ right) := by
  exact List.forall_append.mpr ⟨hleft, hright⟩

private theorem innerOutputNodup_append {β : Type*}
    {output : AllocationEntry → β}
    {left right : List (ℕ × List AllocationEntry)}
    (hleft : innerOutputNodup output left)
    (hright : innerOutputNodup output right) :
    innerOutputNodup output (left ++ right) := by
  exact List.forall_append.mpr ⟨hleft, hright⟩

private theorem flattenBucketsMap_nodup {β : Type*}
    (output : AllocationEntry → β) (key : β → ℕ)
    (buckets : List (ℕ × List AllocationEntry))
    (hkeys : (buckets.map fun bucket => bucket.1).Nodup)
    (hlabeled : keyLabeled (fun e => key (output e)) buckets)
    (hinner : innerOutputNodup output buckets) :
    ((buckets.flatMap fun bucket => bucket.2).map output).Nodup := by
  induction buckets with
  | nil => simp
  | cons bucket buckets ih =>
      rcases bucket with ⟨q, entries⟩
      simp only [List.map_cons, List.nodup_cons] at hkeys
      simp only [keyLabeled, allocationKeyLabeled,
        List.forall_cons] at hlabeled
      simp only [innerOutputNodup, allocationInnerOutputNodup,
        List.forall_cons] at hinner
      simp only [List.flatMap_cons, List.map_append]
      apply List.Nodup.append hinner.1
        (ih hkeys.2 hlabeled.2 hinner.2)
      rw [List.disjoint_left]
      intro x hxEntries hxBuckets
      simp only [List.mem_map] at hxEntries hxBuckets
      obtain ⟨e, heEntries, rfl⟩ := hxEntries
      obtain ⟨e', he'Buckets, hout⟩ := hxBuckets
      simp only [List.mem_flatMap] at he'Buckets
      obtain ⟨bucket, hbucket, he'Bucket⟩ := he'Buckets
      rcases bucket with ⟨q', entries'⟩
      have heLabel :=
        (List.forall_iff_forall_mem.mp hlabeled.1) e heEntries
      have hbucketLabels :=
        (List.forall_iff_forall_mem.mp hlabeled.2)
          (q', entries') hbucket
      have he'Label :=
        (List.forall_iff_forall_mem.mp hbucketLabels) e' he'Bucket
      apply hkeys.1
      simp only [List.mem_map]
      refine ⟨(q', entries'), hbucket, ?_⟩
      calc
        q' = key (output e') := he'Label.symm
        _ = key (output e) := congrArg key hout
        _ = q := heLabel

private theorem sum_map_eq_of_perm {α : Type*} {l₁ l₂ : List α}
    (h : l₁.Perm l₂) (f : α → ℚ) :
    (l₁.map f).sum = (l₂.map f).sum := by
  exact (h.map f).foldr_eq 0

private theorem indicator_sum_buckets (key : AllocationEntry → ℕ)
    (p : ℕ) (buckets : List (ℕ × List AllocationEntry))
    (hlabeled : keyLabeled key buckets) :
    ((buckets.flatMap fun bucket => bucket.2).map fun e =>
        if key e = p then e.value else 0).sum =
      ((selectPrimeEntries p buckets).map fun e => e.value).sum := by
  induction buckets with
  | nil => simp [selectPrimeEntries]
  | cons bucket buckets ih =>
      rcases bucket with ⟨q, entries⟩
      simp only [keyLabeled, allocationKeyLabeled,
        List.forall_cons] at hlabeled
      have hentries := List.forall_iff_forall_mem.mp hlabeled.1
      have htail := ih hlabeled.2
      simp only [List.flatMap_cons, List.map_append, List.sum_append]
      rw [htail]
      by_cases hqp : q = p
      · subst q
        rw [selectPrimeEntries, if_pos rfl]
        change
          (entries.map fun e => if key e = p then e.value else 0).sum +
              ((selectPrimeEntries p buckets).map fun e => e.value).sum =
            ((entries ++ selectPrimeEntries p buckets).map fun e => e.value).sum
        rw [List.map_append, List.sum_append]
        congr 1
        apply congrArg List.sum
        apply List.map_congr_left
        intro e he
        simp [hentries e he]
      · simp only [selectPrimeEntries, if_neg hqp]
        have hzero :
            (entries.map fun e => if key e = p then e.value else 0).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          simp only [List.mem_map] at hx
          obtain ⟨e, he, rfl⟩ := hx
          simp [hentries e he, hqp]
        rw [hzero, zero_add]

private theorem selectPrimeEntries_map (p : ℕ) (keys : List ℕ)
    (f : ℕ → List AllocationEntry) (hkeys : keys.Nodup) :
    selectPrimeEntries p (keys.map fun q => (q, f q)) =
      if p ∈ keys then f p else [] := by
  induction keys with
  | nil => simp [selectPrimeEntries]
  | cons q keys ih =>
      rw [List.nodup_cons] at hkeys
      simp only [List.map_cons]
      by_cases hqp : q = p
      · subst q
        rw [selectPrimeEntries, if_pos rfl, ih hkeys.2]
        simp [hkeys.1]
      · rw [selectPrimeEntries, if_neg hqp, ih hkeys.2]
        have hpq : p ≠ q := Ne.symm hqp
        simp [hpq]

private theorem selectPrimeEntries_append (p : ℕ)
    (left right : List (ℕ × List AllocationEntry)) :
    selectPrimeEntries p (left ++ right) =
      selectPrimeEntries p left ++ selectPrimeEntries p right := by
  induction left with
  | nil => rfl
  | cons bucket left ih =>
      rcases bucket with ⟨q, entries⟩
      simp only [List.cons_append, selectPrimeEntries]
      split <;> simp [ih]

private theorem rowBlockFlat {b : ℕ} (hb : b ≤ 9) :
    finiteAllocationRowBlockEntries b =
      (finiteAllocationRowBlockBuckets b).flatMap fun bucket => bucket.2 := by
  exact allocationRowBlockFlat hb

private theorem primeBlockPerm {b : ℕ} (hb : b ≤ 9) :
    (finiteAllocationRowBlockEntries b).Perm
      ((finiteAllocationPrimeBlockBuckets b).flatMap fun bucket => bucket.2) := by
  exact allocationPrimeBlockPerm hb

private theorem rowLabels {b : ℕ} (hb : b ≤ 9) :
    keyLabeled (fun e => e.row) (finiteAllocationRowBlockBuckets b) := by
  exact allocationRowLabels hb

private theorem primeLabels {b : ℕ} (hb : b ≤ 9) :
    keyLabeled (fun e => e.cofactor) (finiteAllocationPrimeBlockBuckets b) := by
  exact allocationPrimeLabels hb

private theorem rowRanges_eq :
    List.range' 1 200 =
      List.range' 1 20 ++ List.range' 21 20 ++
      List.range' 41 20 ++ List.range' 61 20 ++
      List.range' 81 20 ++ List.range' 101 20 ++
      List.range' 121 20 ++ List.range' 141 20 ++
      List.range' 161 20 ++ List.range' 181 20 := by
  rw [show List.range' 1 200 =
      List.range' 1 20 ++ List.range' 21 180 by
    simpa using (List.range'_append_1 (s := 1) (m := 20) (n := 180)).symm]
  rw [show List.range' 21 180 =
      List.range' 21 20 ++ List.range' 41 160 by
    simpa using (List.range'_append_1 (s := 21) (m := 20) (n := 160)).symm]
  rw [show List.range' 41 160 =
      List.range' 41 20 ++ List.range' 61 140 by
    simpa using (List.range'_append_1 (s := 41) (m := 20) (n := 140)).symm]
  rw [show List.range' 61 140 =
      List.range' 61 20 ++ List.range' 81 120 by
    simpa using (List.range'_append_1 (s := 61) (m := 20) (n := 120)).symm]
  rw [show List.range' 81 120 =
      List.range' 81 20 ++ List.range' 101 100 by
    simpa using (List.range'_append_1 (s := 81) (m := 20) (n := 100)).symm]
  rw [show List.range' 101 100 =
      List.range' 101 20 ++ List.range' 121 80 by
    simpa using (List.range'_append_1 (s := 101) (m := 20) (n := 80)).symm]
  rw [show List.range' 121 80 =
      List.range' 121 20 ++ List.range' 141 60 by
    simpa using (List.range'_append_1 (s := 121) (m := 20) (n := 60)).symm]
  rw [show List.range' 141 60 =
      List.range' 141 20 ++ List.range' 161 40 by
    simpa using (List.range'_append_1 (s := 141) (m := 20) (n := 40)).symm]
  rw [show List.range' 161 40 =
      List.range' 161 20 ++ List.range' 181 20 by
    simpa using (List.range'_append_1 (s := 161) (m := 20) (n := 20)).symm]
  simp only [List.append_assoc]

private def finiteAllocationRowBuckets :
    List (ℕ × List AllocationEntry) :=
  (List.range' 1 200).map fun r => (r, finiteAllocationRowEntries r)

private theorem finiteAllocationRowBuckets_eq_blocks :
    finiteAllocationRowBuckets =
      finiteAllocationRowBlockBuckets 0 ++
      finiteAllocationRowBlockBuckets 1 ++
      finiteAllocationRowBlockBuckets 2 ++
      finiteAllocationRowBlockBuckets 3 ++
      finiteAllocationRowBlockBuckets 4 ++
      finiteAllocationRowBlockBuckets 5 ++
      finiteAllocationRowBlockBuckets 6 ++
      finiteAllocationRowBlockBuckets 7 ++
      finiteAllocationRowBlockBuckets 8 ++
      finiteAllocationRowBlockBuckets 9 := by
  unfold finiteAllocationRowBuckets finiteAllocationRowBlockBuckets
  rw [rowRanges_eq]
  simp only [List.map_append]

private theorem rowCoordinateInnerNodup {b : ℕ} (hb : b ≤ 9) :
    innerOutputNodup coordinate (finiteAllocationRowBlockBuckets b) := by
  exact allocationRowCoordinateInnerNodup hb

private theorem finiteAllocationRowBuckets_labeled :
    keyLabeled (fun e => e.row) finiteAllocationRowBuckets := by
  rw [finiteAllocationRowBuckets_eq_blocks]
  exact keyLabeled_append
    (keyLabeled_append
      (keyLabeled_append
        (keyLabeled_append
          (keyLabeled_append
            (keyLabeled_append
              (keyLabeled_append
                (keyLabeled_append
                  (keyLabeled_append
                    (rowLabels (b := 0) (by omega))
                    (rowLabels (b := 1) (by omega)))
                  (rowLabels (b := 2) (by omega)))
                (rowLabels (b := 3) (by omega)))
              (rowLabels (b := 4) (by omega)))
            (rowLabels (b := 5) (by omega)))
          (rowLabels (b := 6) (by omega)))
        (rowLabels (b := 7) (by omega)))
      (rowLabels (b := 8) (by omega)))
    (rowLabels (b := 9) (by omega))

private theorem finiteAllocationRowBuckets_coordinate_inner_nodup :
    innerOutputNodup coordinate finiteAllocationRowBuckets := by
  rw [finiteAllocationRowBuckets_eq_blocks]
  exact innerOutputNodup_append
    (innerOutputNodup_append
      (innerOutputNodup_append
        (innerOutputNodup_append
          (innerOutputNodup_append
            (innerOutputNodup_append
              (innerOutputNodup_append
                (innerOutputNodup_append
                  (innerOutputNodup_append
                    (rowCoordinateInnerNodup (b := 0) (by omega))
                    (rowCoordinateInnerNodup (b := 1) (by omega)))
                  (rowCoordinateInnerNodup (b := 2) (by omega)))
                (rowCoordinateInnerNodup (b := 3) (by omega)))
              (rowCoordinateInnerNodup (b := 4) (by omega)))
            (rowCoordinateInnerNodup (b := 5) (by omega)))
          (rowCoordinateInnerNodup (b := 6) (by omega)))
        (rowCoordinateInnerNodup (b := 7) (by omega)))
      (rowCoordinateInnerNodup (b := 8) (by omega)))
    (rowCoordinateInnerNodup (b := 9) (by omega))

private theorem finiteAllocationEntries_eq_rowBuckets :
    finiteAllocationEntries =
      (finiteAllocationRowBuckets.flatMap fun bucket => bucket.2) := by
  rw [finiteAllocationEntries, finiteAllocationRowBuckets_eq_blocks]
  simp only [List.flatMap_append]
  rw [← rowBlockFlat (b := 0) (by omega),
    ← rowBlockFlat (b := 1) (by omega),
    ← rowBlockFlat (b := 2) (by omega),
    ← rowBlockFlat (b := 3) (by omega),
    ← rowBlockFlat (b := 4) (by omega),
    ← rowBlockFlat (b := 5) (by omega),
    ← rowBlockFlat (b := 6) (by omega),
    ← rowBlockFlat (b := 7) (by omega),
    ← rowBlockFlat (b := 8) (by omega),
    ← rowBlockFlat (b := 9) (by omega)]

theorem finiteAllocationCoordinates_nodup :
    (finiteAllocationEntries.map coordinate).Nodup := by
  rw [finiteAllocationEntries_eq_rowBuckets]
  apply flattenBucketsMap_nodup coordinate Prod.fst
  · simpa [finiteAllocationRowBuckets] using
      (List.nodup_range' : (List.range' 1 200).Nodup)
  · exact finiteAllocationRowBuckets_labeled
  · exact finiteAllocationRowBuckets_coordinate_inner_nodup

theorem finiteAllocationEntries_nodup :
    finiteAllocationEntries.Nodup :=
  finiteAllocationCoordinates_nodup.of_map coordinate

private theorem selectedRows_eq {r : ℕ} (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    finiteAllocationSelectedRowEntries r = finiteAllocationRowEntries r := by
  rw [finiteAllocationSelectedRowEntries,
    selectPrimeEntries_map r (List.range' 1 200)
      finiteAllocationRowEntries List.nodup_range']
  simp only [List.mem_range'_1]
  rw [if_pos (by omega)]

private def rowBlockSelectedEntries (r : ℕ) : List AllocationEntry :=
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 0) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 1) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 2) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 3) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 4) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 5) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 6) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 7) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 8) ++
  selectPrimeEntries r (finiteAllocationRowBlockBuckets 9)

private theorem rowBlockSelectedEntries_eq (r : ℕ) :
    rowBlockSelectedEntries r = finiteAllocationSelectedRowEntries r := by
  unfold rowBlockSelectedEntries finiteAllocationSelectedRowEntries
  rw [rowRanges_eq]
  simp only [List.map_append, selectPrimeEntries_append]
  rfl

private theorem rowBlockIndicatorSum {b r : ℕ} (hb : b ≤ 9) :
    ((finiteAllocationRowBlockEntries b).map fun e =>
        if e.row = r then e.value else 0).sum =
      ((selectPrimeEntries r (finiteAllocationRowBlockBuckets b)).map
        fun e => e.value).sum := by
  rw [rowBlockFlat hb]
  exact indicator_sum_buckets (fun e => e.row) r _ (rowLabels hb)

private theorem primeBlockIndicatorSum {b p : ℕ} (hb : b ≤ 9) :
    ((finiteAllocationRowBlockEntries b).map fun e =>
        if e.cofactor = p then e.value else 0).sum =
      ((selectPrimeEntries p (finiteAllocationPrimeBlockBuckets b)).map
        fun e => e.value).sum := by
  calc
    _ = (((finiteAllocationPrimeBlockBuckets b).flatMap fun bucket => bucket.2).map
          fun e => if e.cofactor = p then e.value else 0).sum :=
      sum_map_eq_of_perm (primeBlockPerm hb) _
    _ = _ := indicator_sum_buckets (fun e => e.cofactor) p _ (primeLabels hb)

private theorem finiteRowIndicatorListMass_eq {r : ℕ}
    (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    (finiteAllocationEntries.map fun e =>
        if e.row = r then e.value else 0).sum = finiteRowListMass r := by
  calc
    _ = ((rowBlockSelectedEntries r).map fun e => e.value).sum := by
      rw [finiteAllocationEntries]
      simp only [List.map_append, List.sum_append]
      rw [rowBlockIndicatorSum (b := 0) (by omega),
        rowBlockIndicatorSum (b := 1) (by omega),
        rowBlockIndicatorSum (b := 2) (by omega),
        rowBlockIndicatorSum (b := 3) (by omega),
        rowBlockIndicatorSum (b := 4) (by omega),
        rowBlockIndicatorSum (b := 5) (by omega),
        rowBlockIndicatorSum (b := 6) (by omega),
        rowBlockIndicatorSum (b := 7) (by omega),
        rowBlockIndicatorSum (b := 8) (by omega),
        rowBlockIndicatorSum (b := 9) (by omega)]
      simp only [rowBlockSelectedEntries, List.map_append, List.sum_append]
    _ = _ := by
      rw [rowBlockSelectedEntries_eq, selectedRows_eq hr1 hr200]
      rfl

private theorem finitePrimeIndicatorListMass_eq (p : ℕ) :
    (finiteAllocationEntries.map fun e =>
        if e.cofactor = p then e.value else 0).sum =
      finitePrimeIndicatorListLoad p := by
  rw [finiteAllocationEntries, finitePrimeIndicatorListLoad,
    finiteAllocationPrimeEntries]
  simp only [List.map_append, List.sum_append]
  rw [primeBlockIndicatorSum (b := 0) (by omega),
    primeBlockIndicatorSum (b := 1) (by omega),
    primeBlockIndicatorSum (b := 2) (by omega),
    primeBlockIndicatorSum (b := 3) (by omega),
    primeBlockIndicatorSum (b := 4) (by omega),
    primeBlockIndicatorSum (b := 5) (by omega),
    primeBlockIndicatorSum (b := 6) (by omega),
    primeBlockIndicatorSum (b := 7) (by omega),
    primeBlockIndicatorSum (b := 8) (by omega),
    primeBlockIndicatorSum (b := 9) (by omega)]

theorem finiteRowEntryMass_eq_list {r : ℕ}
    (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    finiteRowEntryMass r = finiteRowListMass r := by
  calc
    finiteRowEntryMass r =
        (finiteAllocationEntries.map fun e =>
          if e.row = r then e.value else 0).sum := by
      simpa [finiteRowEntryMass, finiteAllocationEntrySet] using
        (List.sum_toFinset
          (fun e : AllocationEntry => if e.row = r then e.value else 0)
          finiteAllocationEntries_nodup)
    _ = finiteRowListMass r := finiteRowIndicatorListMass_eq hr1 hr200

theorem finitePrimeIndicatorLoad_eq_list (ℓ : ℕ) :
    finitePrimeIndicatorLoad ℓ = finitePrimeIndicatorListLoad ℓ := by
  calc
    finitePrimeIndicatorLoad ℓ =
        (finiteAllocationEntries.map fun e =>
          if e.cofactor = ℓ then e.value else 0).sum := by
      simpa [finitePrimeIndicatorLoad, finiteAllocationEntrySet] using
        (List.sum_toFinset
          (fun e : AllocationEntry => if e.cofactor = ℓ then e.value else 0)
          finiteAllocationEntries_nodup)
    _ = finitePrimeIndicatorListLoad ℓ := finitePrimeIndicatorListMass_eq ℓ

theorem RawFraction.add_denominator_pos {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator) :
    0 < (a.add b).denominator := by
  exact Nat.mul_pos ha hb

theorem RawFraction.sum_denominator_pos {α : Type*} (l : List α)
    (f : α → RawFraction) (hf : ∀ x ∈ l, 0 < (f x).denominator) :
    0 < (RawFraction.sum l f).denominator := by
  induction l with
  | nil => simp [RawFraction.sum, RawFraction.zero]
  | cons x xs ih =>
      apply RawFraction.add_denominator_pos
      · exact hf x (by simp)
      · exact ih (fun y hy => hf y (by simp [hy]))

theorem RawFraction.toRat_add {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator) :
    (a.add b).toRat = a.toRat + b.toRat := by
  have ha0 : (a.denominator : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have hb0 : (b.denominator : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hb)
  simp only [RawFraction.add, RawFraction.toRat, Nat.cast_add, Nat.cast_mul]
  field_simp [ha0, hb0]

theorem RawFraction.sum_toRat {α : Type*} (l : List α)
    (f : α → RawFraction) (hf : ∀ x ∈ l, 0 < (f x).denominator) :
    (RawFraction.sum l f).toRat =
      (l.map fun x => (f x).toRat).sum := by
  induction l with
  | nil => norm_num [RawFraction.sum, RawFraction.zero, RawFraction.toRat]
  | cons x xs ih =>
      have hx : 0 < (f x).denominator := hf x (by simp)
      have hxs : ∀ y ∈ xs, 0 < (f y).denominator :=
        fun y hy => hf y (by simp [hy])
      rw [RawFraction.sum, List.map_cons, List.sum_cons,
        RawFraction.toRat_add hx (RawFraction.sum_denominator_pos xs f hxs),
        ih hxs]

theorem RawFraction.toRat_eq_of_crossEq {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator)
    (hcross : a.CrossEq b) : a.toRat = b.toRat := by
  apply (div_eq_div_iff (by exact_mod_cast (ne_of_gt ha))
    (by exact_mod_cast (ne_of_gt hb))).2
  exact_mod_cast hcross

theorem RawFraction.toRat_le_of_crossLE {a b : RawFraction}
    (ha : 0 < a.denominator) (hb : 0 < b.denominator)
    (hcross : a.CrossLE b) : a.toRat ≤ b.toRat := by
  exact (div_le_div_iff₀ (by exact_mod_cast ha) (by exact_mod_cast hb)).2
    (by exact_mod_cast hcross)

theorem rawRowMass_denominator_pos (r : ℕ) :
    0 < (rawRowMass r).denominator := by
  apply RawFraction.sum_denominator_pos
  intro e _
  simp [RawFraction.ofEntry]

theorem rawPrimeLoad_denominator_pos (p : ℕ) :
    0 < (rawPrimeLoad p).denominator := by
  apply RawFraction.sum_denominator_pos
  intro e _
  simp [RawFraction.ofEntry]

theorem rawAlpha_denominator_pos (r : ℕ) :
    0 < (rawAlpha r).denominator := by
  simp [rawAlpha]

theorem rawCapacity_denominator_pos {p : ℕ} (hp : 1 < p) :
    0 < (rawCapacity p).denominator := by
  simp [rawCapacity]
  omega

theorem rawTailOverlap_denominator_pos (p : ℕ) :
    0 < (rawTailOverlap p).denominator := by
  apply RawFraction.sum_denominator_pos
  intro r _
  exact rawAlpha_denominator_pos r

theorem rawRowMass_toRat (r : ℕ) :
    (rawRowMass r).toRat = finiteRowListMass r := by
  rw [rawRowMass, RawFraction.sum_toRat]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    rfl
  · intro e _
    simp [RawFraction.ofEntry]

theorem rawPrimeLoad_toRat (p : ℕ) :
    (rawPrimeLoad p).toRat = finitePrimeIndicatorListLoad p := by
  rw [rawPrimeLoad, RawFraction.sum_toRat]
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e _
    rfl
  · intro e _
    simp [RawFraction.ofEntry]

theorem rawAlpha_toRat (r : ℕ) :
    (rawAlpha r).toRat = alpha r := by
  norm_num [rawAlpha, RawFraction.toRat, alpha]

theorem rawCapacity_toRat {p : ℕ} (hp : 1 < p) :
    (rawCapacity p).toRat = C0Rat / (((p - 1 : ℕ) : ℚ)) := by
  rw [C0Rat_eq]
  norm_num [rawCapacity, RawFraction.toRat]
  push_cast [Nat.one_le_iff_ne_zero.mpr (by omega : p ≠ 0)]
  field_simp

theorem rawTailOverlap_toRat {p : ℕ} (hp201 : 201 < p) :
    (rawTailOverlap p).toRat = finiteTailOverlap p := by
  let lo := max 201 (previousPrime p)
  let rows := List.range' lo ((p - 1) + 1 - lo)
  have hlo : lo ≤ p - 1 := by
    dsimp [lo]
    have hprev : previousPrime p ≤ p - 1 := Nat.findGreatest_le (p - 1)
    omega
  have hrows : rows.toFinset = Finset.Icc lo (p - 1) := by
    ext r
    simp only [rows, List.mem_toFinset, List.mem_range'_1, Finset.mem_Icc]
    omega
  rw [rawTailOverlap, show max 201 (previousPrime p) = lo by rfl,
    show List.range' lo ((p - 1) + 1 - lo) = rows by rfl,
    RawFraction.sum_toRat]
  · calc
      (rows.map fun r => (rawAlpha r).toRat).sum =
          (rows.map alpha).sum := by
            apply congrArg List.sum
            apply List.map_congr_left
            intro r _
            exact rawAlpha_toRat r
      _ = ∑ r ∈ rows.toFinset, alpha r := by
            symm
            exact List.sum_toFinset alpha List.nodup_range'
      _ = finiteTailOverlap p := by
            rw [hrows]
            rfl
  · intro r _
    exact rawAlpha_denominator_pos r

theorem finiteAllocationEntrySet_mem_iff {e : AllocationEntry} :
    e ∈ finiteAllocationEntrySet ↔ e ∈ finiteAllocationEntries := by
  simp [finiteAllocationEntrySet]

theorem finiteAllocationEntrySet_valid {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) : e.Valid :=
  finiteAllocationEntries_valid (finiteAllocationEntrySet_mem_iff.mp he)

theorem finiteAllocationEntrySet_cofactor_prime {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) : e.cofactor.Prime :=
  finiteAllocationEntries_cofactor_prime
    (finiteAllocationEntrySet_mem_iff.mp he)

theorem finiteAllocationEntry_value_pos {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) : 0 < e.value := by
  have hvalid := finiteAllocationEntrySet_valid he
  exact div_pos (by exact_mod_cast hvalid.2.2.2.2.1)
    (by positivity)

theorem finiteAllocationSupport_card :
    finiteAllocationSupport.card = 211 := by
  rw [finiteAllocationSupport,
    List.toFinset_card_of_nodup finiteAllocationCoordinates_nodup]
  simpa using finiteAllocationEntries_length

theorem finiteAllocation_support_valid {r q : ℕ}
    (hrq : (r, q) ∈ finiteAllocationSupport) :
    1 ≤ r ∧ r ≤ 200 ∧ r + 1 ≤ q ∧ q ≤ 2 * r + 1 := by
  simp only [finiteAllocationSupport, List.mem_toFinset, List.mem_map] at hrq
  obtain ⟨e, he, hcoordinate⟩ := hrq
  have hvalid := finiteAllocationEntries_valid he
  have hr : e.row = r := congrArg Prod.fst hcoordinate
  have hq : e.cofactor = q := congrArg Prod.snd hcoordinate
  subst r
  subst q
  exact ⟨hvalid.1, hvalid.2.1, hvalid.2.2.1, hvalid.2.2.2.1⟩

theorem finiteAllocation_eq_zero_of_not_mem {r q : ℕ}
    (hrq : (r, q) ∉ finiteAllocationSupport) :
    finiteAllocation r q = 0 := by
  classical
  rw [finiteAllocation]
  apply Finset.sum_eq_zero
  intro e he
  simp only [ite_eq_right_iff]
  intro hmatch
  exfalso
  apply hrq
  have heList : e ∈ finiteAllocationEntries :=
    finiteAllocationEntrySet_mem_iff.mp he
  simp only [finiteAllocationSupport, List.mem_toFinset, List.mem_map]
  refine ⟨e, heList, ?_⟩
  exact Prod.ext hmatch.1 hmatch.2

private theorem finiteAllocationEntrySet_coordinate_injective
    {e₁ e₂ : AllocationEntry}
    (he₁ : e₁ ∈ finiteAllocationEntrySet)
    (he₂ : e₂ ∈ finiteAllocationEntrySet)
    (hcoord : e₁.coordinate = e₂.coordinate) : e₁ = e₂ := by
  exact List.inj_on_of_nodup_map finiteAllocationCoordinates_nodup
    (finiteAllocationEntrySet_mem_iff.mp he₁)
    (finiteAllocationEntrySet_mem_iff.mp he₂) hcoord

theorem finiteAllocation_eq_entry_value {e : AllocationEntry}
    (he : e ∈ finiteAllocationEntrySet) :
    finiteAllocation e.row e.cofactor = e.value := by
  classical
  rw [finiteAllocation]
  calc
    (∑ e' ∈ finiteAllocationEntrySet,
        if e'.row = e.row ∧ e'.cofactor = e.cofactor then e'.value else 0) =
        (if e.row = e.row ∧ e.cofactor = e.cofactor then e.value else 0) := by
      apply Finset.sum_eq_single e
      · intro e' he' hne
        rw [if_neg]
        intro hmatch
        apply hne
        apply finiteAllocationEntrySet_coordinate_injective he' he
        exact Prod.ext hmatch.1 hmatch.2
      · exact fun hnot => (hnot he).elim
    _ = e.value := by simp

theorem finiteAllocation_pos_of_mem {r q : ℕ}
    (hrq : (r, q) ∈ finiteAllocationSupport) :
    0 < finiteAllocation r q := by
  simp only [finiteAllocationSupport, List.mem_toFinset, List.mem_map] at hrq
  obtain ⟨e, heList, hcoordinate⟩ := hrq
  have he : e ∈ finiteAllocationEntrySet :=
    finiteAllocationEntrySet_mem_iff.mpr heList
  have hr : e.row = r := congrArg Prod.fst hcoordinate
  have hq : e.cofactor = q := congrArg Prod.snd hcoordinate
  rw [← hr, ← hq, finiteAllocation_eq_entry_value he]
  exact finiteAllocationEntry_value_pos he

/-! ## Sparse sums equal the literal coordinate sums -/

private theorem finiteAllocation_weighted_row_sum
    (w : ℕ → ℚ) (r : ℕ) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
        w q * finiteAllocation r q) =
      ∑ e ∈ finiteAllocationEntrySet,
        if e.row = r then w e.cofactor * e.value else 0 := by
  classical
  simp_rw [finiteAllocation, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  by_cases her : e.row = r
  · have hvalid := finiteAllocationEntrySet_valid he
    have hqmem : e.cofactor ∈ Finset.Icc (r + 1) (2 * r + 1) := by
      simp only [Finset.mem_Icc]
      constructor
      · simpa [her] using hvalid.2.2.1
      · simpa [her] using hvalid.2.2.2.1
    rw [Finset.sum_eq_single e.cofactor]
    · simp [her]
    · intro q hq hne
      have hneq : ¬(e.row = r ∧ e.cofactor = q) := by
        intro h
        exact hne h.2.symm
      simp [hneq]
    · exact fun hnot => (hnot hqmem).elim
  · simp [her]

theorem finiteAllocation_row_sum (r : ℕ) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1), finiteAllocation r q) =
      finiteRowEntryMass r := by
  simpa [finiteRowEntryMass] using
    finiteAllocation_weighted_row_sum (fun _ => 1) r

/-- The literal double coordinate sum in the definition of
`lambda_ell^{fin}` equals the sparse entry sum checked below. -/
theorem finitePrimeLoad_eq_coordinate_sum (ℓ : ℕ) :
    finitePrimeLoad ℓ =
      ∑ r ∈ Finset.Icc 1 200,
        ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          (q.factorization ℓ : ℚ) * finiteAllocation r q := by
  classical
  symm
  calc
    (∑ r ∈ Finset.Icc 1 200,
        ∑ q ∈ Finset.Icc (r + 1) (2 * r + 1),
          (q.factorization ℓ : ℚ) * finiteAllocation r q) =
        ∑ r ∈ Finset.Icc 1 200,
          ∑ e ∈ finiteAllocationEntrySet,
            if e.row = r then
              (e.cofactor.factorization ℓ : ℚ) * e.value else 0 := by
          apply Finset.sum_congr rfl
          intro r _
          exact finiteAllocation_weighted_row_sum
            (fun q => (q.factorization ℓ : ℚ)) r
    _ = ∑ e ∈ finiteAllocationEntrySet,
          (e.cofactor.factorization ℓ : ℚ) * e.value := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro e he
          have hvalid := finiteAllocationEntrySet_valid he
          have hrmem : e.row ∈ Finset.Icc 1 200 := by
            exact Finset.mem_Icc.mpr ⟨hvalid.1, hvalid.2.1⟩
          rw [Finset.sum_eq_single e.row]
          · simp
          · intro r hr hne
            simp [hne.symm]
          · exact fun hnot => (hnot hrmem).elim
    _ = finitePrimeLoad ℓ := rfl

theorem finitePrimeLoad_eq_indicator (ℓ : ℕ) :
    finitePrimeLoad ℓ = finitePrimeIndicatorLoad ℓ := by
  classical
  rw [finitePrimeLoad, finitePrimeIndicatorLoad]
  apply Finset.sum_congr rfl
  intro e he
  have hp := finiteAllocationEntrySet_cofactor_prime he
  rw [hp.factorization]
  simp [Finsupp.single_apply]

/-- No listed cofactor exceeds `401`, so larger primes have zero finite load. -/
theorem finitePrimeLoad_eq_zero_of_gt_401 {ℓ : ℕ} (hℓ401 : 401 < ℓ) :
    finitePrimeLoad ℓ = 0 := by
  classical
  rw [finitePrimeLoad_eq_indicator, finitePrimeIndicatorLoad]
  apply Finset.sum_eq_zero
  intro e he
  rw [if_neg]
  intro heq
  have hvalid := finiteAllocationEntrySet_valid he
  have hr200 : e.row ≤ 200 := hvalid.2.1
  have hqbound : e.cofactor ≤ 2 * e.row + 1 := hvalid.2.2.2.1
  have hcofactor : e.cofactor ≤ 401 := by omega
  omega

/-! ## Kernel-checked rational identities and inequalities -/


private theorem rawRowCrossEq {r : ℕ} (hr1 : 1 ≤ r) (hr200 : r ≤ 200) :
    (rawRowMass r).CrossEq (rawAlpha r) := by
  by_cases h20 : r ≤ 20
  · interval_cases r <;> simp only [rawRowCrossEq_1, rawRowCrossEq_2, rawRowCrossEq_3, rawRowCrossEq_4, rawRowCrossEq_5, rawRowCrossEq_6, rawRowCrossEq_7, rawRowCrossEq_8, rawRowCrossEq_9, rawRowCrossEq_10, rawRowCrossEq_11, rawRowCrossEq_12, rawRowCrossEq_13, rawRowCrossEq_14, rawRowCrossEq_15, rawRowCrossEq_16, rawRowCrossEq_17, rawRowCrossEq_18, rawRowCrossEq_19, rawRowCrossEq_20]
  by_cases h40 : r ≤ 40
  · interval_cases r <;> simp only [rawRowCrossEq_21, rawRowCrossEq_22, rawRowCrossEq_23, rawRowCrossEq_24, rawRowCrossEq_25, rawRowCrossEq_26, rawRowCrossEq_27, rawRowCrossEq_28, rawRowCrossEq_29, rawRowCrossEq_30, rawRowCrossEq_31, rawRowCrossEq_32, rawRowCrossEq_33, rawRowCrossEq_34, rawRowCrossEq_35, rawRowCrossEq_36, rawRowCrossEq_37, rawRowCrossEq_38, rawRowCrossEq_39, rawRowCrossEq_40]
  by_cases h60 : r ≤ 60
  · interval_cases r <;> simp only [rawRowCrossEq_41, rawRowCrossEq_42, rawRowCrossEq_43, rawRowCrossEq_44, rawRowCrossEq_45, rawRowCrossEq_46, rawRowCrossEq_47, rawRowCrossEq_48, rawRowCrossEq_49, rawRowCrossEq_50, rawRowCrossEq_51, rawRowCrossEq_52, rawRowCrossEq_53, rawRowCrossEq_54, rawRowCrossEq_55, rawRowCrossEq_56, rawRowCrossEq_57, rawRowCrossEq_58, rawRowCrossEq_59, rawRowCrossEq_60]
  by_cases h80 : r ≤ 80
  · interval_cases r <;> simp only [rawRowCrossEq_61, rawRowCrossEq_62, rawRowCrossEq_63, rawRowCrossEq_64, rawRowCrossEq_65, rawRowCrossEq_66, rawRowCrossEq_67, rawRowCrossEq_68, rawRowCrossEq_69, rawRowCrossEq_70, rawRowCrossEq_71, rawRowCrossEq_72, rawRowCrossEq_73, rawRowCrossEq_74, rawRowCrossEq_75, rawRowCrossEq_76, rawRowCrossEq_77, rawRowCrossEq_78, rawRowCrossEq_79, rawRowCrossEq_80]
  by_cases h100 : r ≤ 100
  · interval_cases r <;> simp only [rawRowCrossEq_81, rawRowCrossEq_82, rawRowCrossEq_83, rawRowCrossEq_84, rawRowCrossEq_85, rawRowCrossEq_86, rawRowCrossEq_87, rawRowCrossEq_88, rawRowCrossEq_89, rawRowCrossEq_90, rawRowCrossEq_91, rawRowCrossEq_92, rawRowCrossEq_93, rawRowCrossEq_94, rawRowCrossEq_95, rawRowCrossEq_96, rawRowCrossEq_97, rawRowCrossEq_98, rawRowCrossEq_99, rawRowCrossEq_100]
  by_cases h120 : r ≤ 120
  · interval_cases r <;> simp only [rawRowCrossEq_101, rawRowCrossEq_102, rawRowCrossEq_103, rawRowCrossEq_104, rawRowCrossEq_105, rawRowCrossEq_106, rawRowCrossEq_107, rawRowCrossEq_108, rawRowCrossEq_109, rawRowCrossEq_110, rawRowCrossEq_111, rawRowCrossEq_112, rawRowCrossEq_113, rawRowCrossEq_114, rawRowCrossEq_115, rawRowCrossEq_116, rawRowCrossEq_117, rawRowCrossEq_118, rawRowCrossEq_119, rawRowCrossEq_120]
  by_cases h140 : r ≤ 140
  · interval_cases r <;> simp only [rawRowCrossEq_121, rawRowCrossEq_122, rawRowCrossEq_123, rawRowCrossEq_124, rawRowCrossEq_125, rawRowCrossEq_126, rawRowCrossEq_127, rawRowCrossEq_128, rawRowCrossEq_129, rawRowCrossEq_130, rawRowCrossEq_131, rawRowCrossEq_132, rawRowCrossEq_133, rawRowCrossEq_134, rawRowCrossEq_135, rawRowCrossEq_136, rawRowCrossEq_137, rawRowCrossEq_138, rawRowCrossEq_139, rawRowCrossEq_140]
  by_cases h160 : r ≤ 160
  · interval_cases r <;> simp only [rawRowCrossEq_141, rawRowCrossEq_142, rawRowCrossEq_143, rawRowCrossEq_144, rawRowCrossEq_145, rawRowCrossEq_146, rawRowCrossEq_147, rawRowCrossEq_148, rawRowCrossEq_149, rawRowCrossEq_150, rawRowCrossEq_151, rawRowCrossEq_152, rawRowCrossEq_153, rawRowCrossEq_154, rawRowCrossEq_155, rawRowCrossEq_156, rawRowCrossEq_157, rawRowCrossEq_158, rawRowCrossEq_159, rawRowCrossEq_160]
  by_cases h180 : r ≤ 180
  · interval_cases r <;> simp only [rawRowCrossEq_161, rawRowCrossEq_162, rawRowCrossEq_163, rawRowCrossEq_164, rawRowCrossEq_165, rawRowCrossEq_166, rawRowCrossEq_167, rawRowCrossEq_168, rawRowCrossEq_169, rawRowCrossEq_170, rawRowCrossEq_171, rawRowCrossEq_172, rawRowCrossEq_173, rawRowCrossEq_174, rawRowCrossEq_175, rawRowCrossEq_176, rawRowCrossEq_177, rawRowCrossEq_178, rawRowCrossEq_179, rawRowCrossEq_180]
  · interval_cases r <;> simp only [rawRowCrossEq_181, rawRowCrossEq_182, rawRowCrossEq_183, rawRowCrossEq_184, rawRowCrossEq_185, rawRowCrossEq_186, rawRowCrossEq_187, rawRowCrossEq_188, rawRowCrossEq_189, rawRowCrossEq_190, rawRowCrossEq_191, rawRowCrossEq_192, rawRowCrossEq_193, rawRowCrossEq_194, rawRowCrossEq_195, rawRowCrossEq_196, rawRowCrossEq_197, rawRowCrossEq_198, rawRowCrossEq_199, rawRowCrossEq_200]

private theorem finiteRowListMass_identity {r : ℕ} (hr1 : 1 ≤ r)
    (hr200 : r ≤ 200) : finiteRowListMass r = alpha r := by
  have hcross := rawRowCrossEq hr1 hr200
  calc
    finiteRowListMass r = (rawRowMass r).toRat := (rawRowMass_toRat r).symm
    _ = (rawAlpha r).toRat :=
      RawFraction.toRat_eq_of_crossEq (rawRowMass_denominator_pos r)
        (rawAlpha_denominator_pos r) hcross
    _ = alpha r := rawAlpha_toRat r

theorem finiteAllocation_row_identity {r : ℕ} (hr1 : 1 ≤ r)
    (hr200 : r ≤ 200) :
    (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1), finiteAllocation r q) =
      alpha r := by
  rw [finiteAllocation_row_sum r]
  rw [finiteRowEntryMass_eq_list hr1 hr200]
  exact finiteRowListMass_identity hr1 hr200


private theorem rawCapacityCrossLE {p : ℕ} (hp : p.Prime) (hp401 : p ≤ 401) :
    (rawPrimeLoad p).CrossLE (rawCapacity p) := by
  by_cases h21 : p ≤ 21
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_2, rawCapacityCrossLE_3, rawCapacityCrossLE_5, rawCapacityCrossLE_7, rawCapacityCrossLE_11, rawCapacityCrossLE_13, rawCapacityCrossLE_17, rawCapacityCrossLE_19]
  by_cases h41 : p ≤ 41
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_23, rawCapacityCrossLE_29, rawCapacityCrossLE_31, rawCapacityCrossLE_37, rawCapacityCrossLE_41]
  by_cases h61 : p ≤ 61
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_43, rawCapacityCrossLE_47, rawCapacityCrossLE_53, rawCapacityCrossLE_59, rawCapacityCrossLE_61]
  by_cases h81 : p ≤ 81
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_67, rawCapacityCrossLE_71, rawCapacityCrossLE_73, rawCapacityCrossLE_79]
  by_cases h101 : p ≤ 101
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_83, rawCapacityCrossLE_89, rawCapacityCrossLE_97, rawCapacityCrossLE_101]
  by_cases h121 : p ≤ 121
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_103, rawCapacityCrossLE_107, rawCapacityCrossLE_109, rawCapacityCrossLE_113]
  by_cases h141 : p ≤ 141
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_127, rawCapacityCrossLE_131, rawCapacityCrossLE_137, rawCapacityCrossLE_139]
  by_cases h161 : p ≤ 161
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_149, rawCapacityCrossLE_151, rawCapacityCrossLE_157]
  by_cases h181 : p ≤ 181
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_163, rawCapacityCrossLE_167, rawCapacityCrossLE_173, rawCapacityCrossLE_179, rawCapacityCrossLE_181]
  by_cases h201 : p ≤ 201
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_191, rawCapacityCrossLE_193, rawCapacityCrossLE_197, rawCapacityCrossLE_199]
  by_cases h221 : p ≤ 221
  · have hpEq : p = 211 := by
      interval_cases p <;> norm_num at hp
      rfl
    subst p
    exact rawCapacityCrossLE_211
  by_cases h241 : p ≤ 241
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_223, rawCapacityCrossLE_227, rawCapacityCrossLE_229, rawCapacityCrossLE_233, rawCapacityCrossLE_239, rawCapacityCrossLE_241]
  by_cases h261 : p ≤ 261
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_251, rawCapacityCrossLE_257]
  by_cases h281 : p ≤ 281
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_263, rawCapacityCrossLE_269, rawCapacityCrossLE_271, rawCapacityCrossLE_277, rawCapacityCrossLE_281]
  by_cases h301 : p ≤ 301
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_283, rawCapacityCrossLE_293]
  by_cases h321 : p ≤ 321
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_307, rawCapacityCrossLE_311, rawCapacityCrossLE_313, rawCapacityCrossLE_317]
  by_cases h341 : p ≤ 341
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_331, rawCapacityCrossLE_337]
  by_cases h361 : p ≤ 361
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_347, rawCapacityCrossLE_349, rawCapacityCrossLE_353, rawCapacityCrossLE_359]
  by_cases h381 : p ≤ 381
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_367, rawCapacityCrossLE_373, rawCapacityCrossLE_379]
  · interval_cases p <;> norm_num at hp <;> simp only [rawCapacityCrossLE_383, rawCapacityCrossLE_389, rawCapacityCrossLE_397, rawCapacityCrossLE_401]

private theorem finitePrimeIndicatorListLoad_capacity {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓ401 : ℓ ≤ 401) :
    finitePrimeIndicatorListLoad ℓ ≤
      C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  have hcross := rawCapacityCrossLE hℓ hℓ401
  have hle := RawFraction.toRat_le_of_crossLE
    (rawPrimeLoad_denominator_pos ℓ)
    (rawCapacity_denominator_pos hℓ.one_lt) hcross
  rw [rawPrimeLoad_toRat, rawCapacity_toRat hℓ.one_lt] at hle
  exact hle

theorem finiteAllocation_prime_capacity {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hℓ401 : ℓ ≤ 401) :
    finitePrimeLoad ℓ ≤ C0Rat / (((ℓ - 1 : ℕ) : ℚ)) := by
  rw [finitePrimeLoad_eq_indicator]
  rw [finitePrimeIndicatorLoad_eq_list]
  exact finitePrimeIndicatorListLoad_capacity hℓ hℓ401

theorem previousPrime_spec {p : ℕ} (hp2 : 2 < p) :
    (previousPrime p).Prime ∧ previousPrime p < p ∧
      ∀ q, q.Prime → previousPrime p < q → q < p → False := by
  have htwo : 2 ≤ p - 1 := by omega
  have hprevPrime : (previousPrime p).Prime := by
    exact Nat.findGreatest_spec (P := Nat.Prime) htwo Nat.prime_two
  have hprevLe : previousPrime p ≤ p - 1 := by
    exact Nat.findGreatest_le (p - 1)
  refine ⟨hprevPrime, by omega, ?_⟩
  intro q hq hprevq hqp
  exact (Nat.findGreatest_is_greatest (P := Nat.Prime) hprevq (by omega)) hq


private theorem rawOverlapCrossLE {p : ℕ} (hp : p.Prime)
    (hp201 : 201 < p) (hp401 : p ≤ 401) :
    (RawFraction.add (rawPrimeLoad p) (rawTailOverlap p)).CrossLE
      (rawCapacity p) := by
  by_cases h221 : p ≤ 221
  · have hpEq : p = 211 := by
      interval_cases p <;> norm_num at hp
      rfl
    subst p
    exact rawOverlapCrossLE_211
  by_cases h241 : p ≤ 241
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_223, rawOverlapCrossLE_227, rawOverlapCrossLE_229, rawOverlapCrossLE_233, rawOverlapCrossLE_239, rawOverlapCrossLE_241]
  by_cases h261 : p ≤ 261
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_251, rawOverlapCrossLE_257]
  by_cases h281 : p ≤ 281
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_263, rawOverlapCrossLE_269, rawOverlapCrossLE_271, rawOverlapCrossLE_277, rawOverlapCrossLE_281]
  by_cases h301 : p ≤ 301
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_283, rawOverlapCrossLE_293]
  by_cases h321 : p ≤ 321
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_307, rawOverlapCrossLE_311, rawOverlapCrossLE_313, rawOverlapCrossLE_317]
  by_cases h341 : p ≤ 341
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_331, rawOverlapCrossLE_337]
  by_cases h361 : p ≤ 361
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_347, rawOverlapCrossLE_349, rawOverlapCrossLE_353, rawOverlapCrossLE_359]
  by_cases h381 : p ≤ 381
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_367, rawOverlapCrossLE_373, rawOverlapCrossLE_379]
  · interval_cases p <;> norm_num at hp <;> simp only [rawOverlapCrossLE_383, rawOverlapCrossLE_389, rawOverlapCrossLE_397, rawOverlapCrossLE_401]

private theorem finitePrimeIndicatorListLoad_overlap {p : ℕ}
    (hp : p.Prime) (hp201 : 201 < p) (hp401 : p ≤ 401) :
    finitePrimeIndicatorListLoad p + finiteTailOverlap p ≤
      C0Rat / (((p - 1 : ℕ) : ℚ)) := by
  have hcross := rawOverlapCrossLE hp hp201 hp401
  have hle := RawFraction.toRat_le_of_crossLE
    (RawFraction.add_denominator_pos (rawPrimeLoad_denominator_pos p)
      (rawTailOverlap_denominator_pos p))
    (rawCapacity_denominator_pos hp.one_lt) hcross
  rw [RawFraction.toRat_add (rawPrimeLoad_denominator_pos p)
      (rawTailOverlap_denominator_pos p),
    rawPrimeLoad_toRat, rawTailOverlap_toRat hp201,
    rawCapacity_toRat hp.one_lt] at hle
  exact hle

theorem finiteAllocation_prime_overlap {p : ℕ} (hp : p.Prime)
    (hp201 : 201 < p) (hp401 : p ≤ 401) :
    finitePrimeLoad p +
        (∑ r ∈ Finset.Icc (max 201 (previousPrime p)) (p - 1), alpha r) ≤
      C0Rat / (((p - 1 : ℕ) : ℚ)) := by
  rw [finitePrimeLoad_eq_indicator]
  rw [finitePrimeIndicatorLoad_eq_list]
  change finitePrimeIndicatorListLoad p + finiteTailOverlap p ≤ _
  exact finitePrimeIndicatorListLoad_overlap hp hp201 hp401

/-! ## Literal paper-level certificate -/

/--
Lemma 4.1 of the paper (`Finite allocation certificate`), with the explicit
array exposed as `finiteAllocation`.  The first conjunct records that exactly
211 coordinates are nonzero; the following conjuncts state positivity and
the permitted cofactor range, followed by the three numbered conclusions in
the paper.
-/
theorem finite_allocation_certificate :
    finiteAllocationSupport.card = 211 ∧
    (∀ r q, (r, q) ∈ finiteAllocationSupport →
      0 < finiteAllocation r q ∧
        1 ≤ r ∧ r ≤ 200 ∧ r + 1 ≤ q ∧ q ≤ 2 * r + 1) ∧
    (∀ r q, (r, q) ∉ finiteAllocationSupport →
      finiteAllocation r q = 0) ∧
    (∀ r, 1 ≤ r → r ≤ 200 →
      (∑ q ∈ Finset.Icc (r + 1) (2 * r + 1), finiteAllocation r q) =
        alpha r) ∧
    (∀ ℓ, ℓ.Prime → ℓ ≤ 401 →
      finitePrimeLoad ℓ ≤ C0Rat / (((ℓ - 1 : ℕ) : ℚ))) ∧
    (∀ p, p.Prime → 201 < p → p ≤ 401 →
      finitePrimeLoad p +
          (∑ r ∈ Finset.Icc (max 201 (previousPrime p)) (p - 1), alpha r) ≤
        C0Rat / (((p - 1 : ℕ) : ℚ))) := by
  refine ⟨finiteAllocationSupport_card, ?_, ?_, ?_, ?_, ?_⟩
  · intro r q hrq
    exact ⟨finiteAllocation_pos_of_mem hrq,
      finiteAllocation_support_valid hrq⟩
  · exact fun r q => finiteAllocation_eq_zero_of_not_mem
  · intro r hr1 hr200
    exact finiteAllocation_row_identity hr1 hr200
  · intro ℓ hℓ hℓ401
    exact finiteAllocation_prime_capacity hℓ hℓ401
  · intro p hp hp201 hp401
    exact finiteAllocation_prime_overlap hp hp201 hp401

end

end Erdos390.WholePaper
