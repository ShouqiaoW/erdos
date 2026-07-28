import Erdos390.WholePaper.CompleteRoughDecomposition

/-!
# Finite common-multiplier lists for the tangent absorber

This file begins the literal common-list construction of Section 9.  It
defines the integer interval

`(n / v, (2 * n - K * h) / u]`

and applies exactly the five tests appearing in the paper: head
coprimality, the exceptional-row cutoff, exclusion of dedicated rows, and
the two numerical endpoint guards.  The resulting list is finite by
construction.

The uniform positive-density lower bound still needs the paper's reduced
residue-class count and exceptional-row Selberg-sieve estimate.  Everything
around those two analytic inputs is proved here: endpoint location, the
complete-rough-row identity, the exact finite deletion ledger, and the
paper's combinatorial fact that an exhaustive guard set deletes at most two
multipliers per guard.
-/

namespace Erdos390.WholePaper

noncomputable section

/-! ## Literal interval and cleanliness predicates -/

/-- The upper endpoint `2n-Kh` of the broad interval used by the tangent. -/
def tangentBroadUpper (n K h : ℕ) : ℕ :=
  2 * n - K * h

/-- Paper notation `X_{R_y(a)}=2n/R_y(a)`. -/
def tangentRoughScale (n y a : ℕ) : ℕ :=
  2 * n / completeRoughLabel y a

/-- The literal integer common-multiplier interval
`I_uv=(n/v,(2n-Kh)/u]`. -/
def tangentCommonMultiplierInterval
    (n K h u v : ℕ) : Finset ℕ :=
  Finset.Ioc (n / v) (tangentBroadUpper n K h / u)

/-- Multipliers failing the fixed head-coprimality test. -/
def tangentHeadBadMultipliers
    (Phead : ℕ) (multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ ¬Nat.Coprime a Phead

/-- Multipliers in terminal exceptional rough rows, i.e. with
`X_{R_y(a)} < X0`. -/
def tangentExceptionalMultipliers
    (n X0 y : ℕ) (multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ tangentRoughScale n y a < X0

/-- Multipliers whose complete rough label is a fully dedicated row. -/
def tangentDedicatedRowMultipliers
    (y : ℕ) (dedicatedRows multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ completeRoughLabel y a ∈ dedicatedRows

/-- Multipliers whose endpoint at one fixed label hits the exhaustive
numerical guard set. -/
def tangentLabelGuardDeletedMultipliers
    (label : ℕ) (numericalGuards multipliers : Finset ℕ) : Finset ℕ :=
  multipliers.filter fun a ↦ label * a ∈ numericalGuards

/-- Multipliers for which either of the two common-list endpoints is
numerically guarded. -/
def tangentEndpointGuardDeletedMultipliers
    (u v : ℕ) (numericalGuards multipliers : Finset ℕ) : Finset ℕ :=
  tangentLabelGuardDeletedMultipliers u numericalGuards multipliers ∪
    tangentLabelGuardDeletedMultipliers v numericalGuards multipliers

/-- The union of all four deletion classes in the common-list proof.  The
last class incorporates both numerical endpoints. -/
def tangentCommonMultiplierBadSet
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) : Finset ℕ :=
  let interval := tangentCommonMultiplierInterval n K h u v
  tangentHeadBadMultipliers Phead interval ∪
    tangentExceptionalMultipliers n X0 y interval ∪
    tangentDedicatedRowMultipliers y dedicatedRows interval ∪
    tangentEndpointGuardDeletedMultipliers u v numericalGuards interval

/-- The literal clean common list `L^+_{uv}` from Section 9. -/
def tangentCleanCommonMultiplierList
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) : Finset ℕ :=
  (tangentCommonMultiplierInterval n K h u v).filter fun a ↦
    Nat.Coprime a Phead ∧
      X0 ≤ tangentRoughScale n y a ∧
      completeRoughLabel y a ∉ dedicatedRows ∧
      u * a ∉ numericalGuards ∧
      v * a ∉ numericalGuards

@[simp]
theorem mem_tangentCommonMultiplierInterval
    {n K h u v a : ℕ} :
    a ∈ tangentCommonMultiplierInterval n K h u v ↔
      n / v < a ∧ a ≤ tangentBroadUpper n K h / u := by
  simp [tangentCommonMultiplierInterval]

@[simp]
theorem card_tangentCommonMultiplierInterval
    (n K h u v : ℕ) :
    (tangentCommonMultiplierInterval n K h u v).card =
      tangentBroadUpper n K h / u - n / v := by
  simp [tangentCommonMultiplierInterval]

@[simp]
theorem mem_tangentCleanCommonMultiplierList
    {n K h Phead X0 y u v a : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ} :
    a ∈ tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards ↔
      (n / v < a ∧ a ≤ tangentBroadUpper n K h / u) ∧
      Nat.Coprime a Phead ∧
      X0 ≤ tangentRoughScale n y a ∧
      completeRoughLabel y a ∉ dedicatedRows ∧
      u * a ∉ numericalGuards ∧
      v * a ∉ numericalGuards := by
  simp [tangentCleanCommonMultiplierList]

/-! ## Endpoint location and complete rough rows -/

/-- Membership in `I_uv`, together with `0<v≤u`, puts both numerical
endpoints in the broad interval `(n,2n-Kh]`. -/
theorem tangentCommonMultiplierInterval_endpoints
    {n K h u v a : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (ha : a ∈ tangentCommonMultiplierInterval n K h u v) :
    u * a ∈ Finset.Ioc n (tangentBroadUpper n K h) ∧
      v * a ∈ Finset.Ioc n (tangentBroadUpper n K h) := by
  have haBounds := mem_tangentCommonMultiplierInterval.mp ha
  have hvLower : n < v * a := by
    have h := (Nat.div_lt_iff_lt_mul hv).mp haBounds.1
    simpa only [Nat.mul_comm] using h
  have huLower : n < u * a := by
    exact hvLower.trans_le (Nat.mul_le_mul_right a hvu)
  have huUpper : u * a ≤ tangentBroadUpper n K h := by
    have h := (Nat.le_div_iff_mul_le hu).mp haBounds.2
    simpa only [Nat.mul_comm] using h
  have hvUpper : v * a ≤ tangentBroadUpper n K h :=
    (Nat.mul_le_mul_right a hvu).trans huUpper
  exact ⟨Finset.mem_Ioc.mpr ⟨huLower, huUpper⟩,
    Finset.mem_Ioc.mpr ⟨hvLower, hvUpper⟩⟩

/-- Multiplying by a positive integer at most the cutoff changes no
prime-power coordinate above the cutoff. -/
theorem completeRoughSignature_small_left_mul
    {y label a : ℕ} (hlabel : 0 < label) (hlabelLe : label ≤ y)
    (ha : 0 < a) :
    completeRoughSignature y (label * a) =
      completeRoughSignature y a := by
  ext p
  rw [completeRoughSignature_apply, completeRoughSignature_apply]
  by_cases hp : y < p
  · rw [if_pos hp, if_pos hp,
      Nat.factorization_mul hlabel.ne' ha.ne']
    simp only [Finsupp.add_apply,
      Nat.factorization_eq_zero_of_lt (hlabelLe.trans_lt hp), zero_add]
  · simp only [if_neg hp]

/-- Integer-label version of the complete-rough-row identity. -/
theorem completeRoughLabel_small_left_mul
    {y label a : ℕ} (hlabel : 0 < label) (hlabelLe : label ≤ y)
    (ha : 0 < a) :
    completeRoughLabel y (label * a) = completeRoughLabel y a :=
  completeRoughSignature_eq_iff_label_eq.mp
    (completeRoughSignature_small_left_mul hlabel hlabelLe ha)

/-- Full finite certificate supplied by one member of the literal clean
list for a paper-permitted prime pair.  The ratio hypotheses are recorded in
their paper order even though the exact endpoint and row identities only use
positivity, `v≤u`, and `u≤y`. -/
theorem tangentCleanCommonMultiplier_mem_certificate
    {W n K h Phead X0 y u v a : ℕ} {r0 : ℝ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (_hr0Lower : 1 < r0) (_hr0Upper : r0 < 3 / 2)
    (huPrime : u.Prime) (hvPrime : v.Prime) (huv : u ≠ v)
    (_hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (_hratio : (u : ℝ) / (v : ℝ) ≤ r0)
    (ha : a ∈ tangentCleanCommonMultiplierList
      n K h Phead X0 y u v dedicatedRows numericalGuards) :
    Nat.Coprime a Phead ∧
      X0 ≤ tangentRoughScale n y a ∧
      completeRoughLabel y a ∉ dedicatedRows ∧
      u * a ∈ Finset.Ioc n (tangentBroadUpper n K h) ∧
      v * a ∈ Finset.Ioc n (tangentBroadUpper n K h) ∧
      u * a ∉ numericalGuards ∧
      v * a ∉ numericalGuards ∧
      u * a ≠ v * a ∧
      completeRoughSignature y (u * a) =
        completeRoughSignature y a ∧
      completeRoughSignature y a =
        completeRoughSignature y (v * a) ∧
      completeRoughLabel y (u * a) = completeRoughLabel y a ∧
      completeRoughLabel y a = completeRoughLabel y (v * a) := by
  have haData := mem_tangentCleanCommonMultiplierList.mp ha
  have haPos : 0 < a := by
    have hnonneg : 0 ≤ n / v := Nat.zero_le _
    omega
  have hendpoints := tangentCommonMultiplierInterval_endpoints
    huPrime.pos hvPrime.pos hvu
    (mem_tangentCommonMultiplierInterval.mpr haData.1)
  have huSignature := completeRoughSignature_small_left_mul
    huPrime.pos huy haPos
  have hvLe : v ≤ y := hvu.trans huy
  have hvSignature := completeRoughSignature_small_left_mul
    hvPrime.pos hvLe haPos
  have huLabel := completeRoughLabel_small_left_mul
    huPrime.pos huy haPos
  have hvLabel := completeRoughLabel_small_left_mul
    hvPrime.pos hvLe haPos
  have hendpointNe : u * a ≠ v * a := by
    intro heq
    exact huv (mul_right_cancel₀ haPos.ne' heq)
  exact ⟨haData.2.1, haData.2.2.1, haData.2.2.2.1,
    hendpoints.1, hendpoints.2, haData.2.2.2.2.1,
    haData.2.2.2.2.2, hendpointNe, huSignature,
    hvSignature.symm, huLabel, hvLabel.symm⟩

/-! ## Exact finite deletion counts -/

/-- For a nonzero label, each numerical guard deletes at most one
multiplier.  This is the injectivity argument `a=g/label` used in the paper. -/
theorem card_tangentLabelGuardDeletedMultipliers_le
    {label : ℕ} (hlabel : 0 < label)
    (numericalGuards multipliers : Finset ℕ) :
    (tangentLabelGuardDeletedMultipliers
      label numericalGuards multipliers).card ≤
        numericalGuards.card := by
  classical
  let deleted := tangentLabelGuardDeletedMultipliers
    label numericalGuards multipliers
  have hmulInjective : Function.Injective (fun a : ℕ ↦ label * a) := by
    intro a b hab
    exact mul_left_cancel₀ hlabel.ne' hab
  calc
    deleted.card = (deleted.image (fun a : ℕ ↦ label * a)).card :=
      (Finset.card_image_of_injective deleted hmulInjective).symm
    _ ≤ numericalGuards.card := by
      apply Finset.card_le_card
      intro endpoint hendpoint
      obtain ⟨a, ha, hvalue⟩ := Finset.mem_image.mp hendpoint
      rw [← hvalue]
      exact (Finset.mem_filter.mp ha).2

/-- The two endpoints of a common pair therefore delete at most twice the
size of the exhaustive numerical guard set. -/
theorem card_tangentEndpointGuardDeletedMultipliers_le
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (numericalGuards multipliers : Finset ℕ) :
    (tangentEndpointGuardDeletedMultipliers
      u v numericalGuards multipliers).card ≤
        2 * numericalGuards.card := by
  rw [tangentEndpointGuardDeletedMultipliers]
  calc
    (tangentLabelGuardDeletedMultipliers
          u numericalGuards multipliers ∪
        tangentLabelGuardDeletedMultipliers
          v numericalGuards multipliers).card ≤
        (tangentLabelGuardDeletedMultipliers
          u numericalGuards multipliers).card +
        (tangentLabelGuardDeletedMultipliers
          v numericalGuards multipliers).card :=
      Finset.card_union_le _ _
    _ ≤ numericalGuards.card + numericalGuards.card :=
      Nat.add_le_add
        (card_tangentLabelGuardDeletedMultipliers_le
          hu numericalGuards multipliers)
        (card_tangentLabelGuardDeletedMultipliers_le
          hv numericalGuards multipliers)
    _ = 2 * numericalGuards.card := by omega

/-- Every declared bad class is a subset of the raw interval. -/
theorem tangentCommonMultiplierBadSet_subset_interval
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCommonMultiplierBadSet
        n K h Phead X0 y u v dedicatedRows numericalGuards ⊆
      tangentCommonMultiplierInterval n K h u v := by
  unfold tangentCommonMultiplierBadSet
    tangentHeadBadMultipliers tangentExceptionalMultipliers
    tangentDedicatedRowMultipliers
    tangentEndpointGuardDeletedMultipliers
    tangentLabelGuardDeletedMultipliers
  exact Finset.union_subset
    (Finset.union_subset
      (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))
      (Finset.filter_subset _ _))
    (Finset.union_subset
      (Finset.filter_subset _ _) (Finset.filter_subset _ _))

/-- The direct clean-list filter is exactly the raw interval minus the union
of the four bad classes. -/
theorem tangentCleanCommonMultiplierList_eq_sdiff_badSet
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards =
      tangentCommonMultiplierInterval n K h u v \
        tangentCommonMultiplierBadSet
          n K h Phead X0 y u v dedicatedRows numericalGuards := by
  classical
  ext a
  by_cases ha : a ∈ tangentCommonMultiplierInterval n K h u v
  · simp [tangentCleanCommonMultiplierList,
      tangentCommonMultiplierBadSet, tangentHeadBadMultipliers,
      tangentExceptionalMultipliers, tangentDedicatedRowMultipliers,
      tangentEndpointGuardDeletedMultipliers,
      tangentLabelGuardDeletedMultipliers, ha, not_lt]
  · simp [tangentCleanCommonMultiplierList,
      tangentCommonMultiplierBadSet, tangentHeadBadMultipliers,
      tangentExceptionalMultipliers, tangentDedicatedRowMultipliers,
      tangentEndpointGuardDeletedMultipliers,
      tangentLabelGuardDeletedMultipliers, ha]

/-- Exact cardinality after all declared common-list deletions. -/
theorem card_tangentCleanCommonMultiplierList
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    (tangentCleanCommonMultiplierList
      n K h Phead X0 y u v dedicatedRows numericalGuards).card =
      (tangentCommonMultiplierInterval n K h u v).card -
        (tangentCommonMultiplierBadSet
          n K h Phead X0 y u v dedicatedRows numericalGuards).card := by
  rw [tangentCleanCommonMultiplierList_eq_sdiff_badSet,
    Finset.card_sdiff_of_subset
      (tangentCommonMultiplierBadSet_subset_interval
        n K h Phead X0 y u v dedicatedRows numericalGuards)]

/-- Union bound for the four bad classes before inserting any analytic
estimate for the head or exceptional loss. -/
theorem card_tangentCommonMultiplierBadSet_le
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    (tangentCommonMultiplierBadSet
      n K h Phead X0 y u v dedicatedRows numericalGuards).card ≤
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentDedicatedRowMultipliers y dedicatedRows
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentEndpointGuardDeletedMultipliers u v numericalGuards
        (tangentCommonMultiplierInterval n K h u v)).card := by
  rw [tangentCommonMultiplierBadSet]
  have hHeadExceptional := Finset.card_union_le
    (tangentHeadBadMultipliers Phead
      (tangentCommonMultiplierInterval n K h u v))
    (tangentExceptionalMultipliers n X0 y
      (tangentCommonMultiplierInterval n K h u v))
  have hDedicated := Finset.card_union_le
    (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v) ∪
      tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v))
    (tangentDedicatedRowMultipliers y dedicatedRows
      (tangentCommonMultiplierInterval n K h u v))
  have hGuard := Finset.card_union_le
    (tangentHeadBadMultipliers Phead
          (tangentCommonMultiplierInterval n K h u v) ∪
        tangentExceptionalMultipliers n X0 y
          (tangentCommonMultiplierInterval n K h u v) ∪
        tangentDedicatedRowMultipliers y dedicatedRows
          (tangentCommonMultiplierInterval n K h u v))
    (tangentEndpointGuardDeletedMultipliers u v numericalGuards
      (tangentCommonMultiplierInterval n K h u v))
  omega

/-- Strong finite lower-bound ledger for the clean list.  It proves all
combinatorial losses, including the factor `2` for endpoint guards, while
leaving the two genuine analytic counts visible as cardinalities. -/
theorem tangentCommonMultiplier_finite_deletion_ledger
    {n K h Phead X0 y u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (dedicatedRows numericalGuards : Finset ℕ) :
    (tangentCommonMultiplierInterval n K h u v).card ≤
      (tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards).card +
      (tangentHeadBadMultipliers Phead
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentExceptionalMultipliers n X0 y
        (tangentCommonMultiplierInterval n K h u v)).card +
      (tangentDedicatedRowMultipliers y dedicatedRows
        (tangentCommonMultiplierInterval n K h u v)).card +
      2 * numericalGuards.card := by
  let interval := tangentCommonMultiplierInterval n K h u v
  let bad := tangentCommonMultiplierBadSet
    n K h Phead X0 y u v dedicatedRows numericalGuards
  let clean := tangentCleanCommonMultiplierList
    n K h Phead X0 y u v dedicatedRows numericalGuards
  have hpartition : clean.card + bad.card = interval.card := by
    dsimp only [clean, bad, interval]
    rw [tangentCleanCommonMultiplierList_eq_sdiff_badSet]
    exact Finset.card_sdiff_add_card_eq_card
      (tangentCommonMultiplierBadSet_subset_interval
        n K h Phead X0 y u v dedicatedRows numericalGuards)
  have hbad := card_tangentCommonMultiplierBadSet_le
    n K h Phead X0 y u v dedicatedRows numericalGuards
  have hguard := card_tangentEndpointGuardDeletedMultipliers_le
    hu hv numericalGuards interval
  dsimp only [interval, bad, clean] at hpartition hguard ⊢
  omega

end

end Erdos390.WholePaper
