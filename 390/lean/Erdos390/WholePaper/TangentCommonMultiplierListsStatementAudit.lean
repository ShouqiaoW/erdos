import Erdos390.WholePaper.TangentCommonMultiplierLists

/-! # Expanded statement audit for tangent common-multiplier lists -/

namespace Erdos390.WholePaper

noncomputable section

example (n K h : ℕ) :
    tangentBroadUpper n K h = 2 * n - K * h := rfl

example (n y a : ℕ) :
    tangentRoughScale n y a =
      2 * n / completeRoughLabel y a := rfl

example (n K h u v : ℕ) :
    tangentCommonMultiplierInterval n K h u v =
      Finset.Ioc (n / v) ((2 * n - K * h) / u) := rfl

example (Phead : ℕ) (multipliers : Finset ℕ) :
    tangentHeadBadMultipliers Phead multipliers =
      multipliers.filter fun a ↦ ¬Nat.Coprime a Phead := rfl

example (n X0 y : ℕ) (multipliers : Finset ℕ) :
    tangentExceptionalMultipliers n X0 y multipliers =
      multipliers.filter fun a ↦
        2 * n / completeRoughLabel y a < X0 := rfl

example (y : ℕ) (dedicatedRows multipliers : Finset ℕ) :
    tangentDedicatedRowMultipliers y dedicatedRows multipliers =
      multipliers.filter fun a ↦
        completeRoughLabel y a ∈ dedicatedRows := rfl

example (label : ℕ) (numericalGuards multipliers : Finset ℕ) :
    tangentLabelGuardDeletedMultipliers
        label numericalGuards multipliers =
      multipliers.filter fun a ↦ label * a ∈ numericalGuards := rfl

example (u v : ℕ) (numericalGuards multipliers : Finset ℕ) :
    tangentEndpointGuardDeletedMultipliers
        u v numericalGuards multipliers =
      tangentLabelGuardDeletedMultipliers
          u numericalGuards multipliers ∪
        tangentLabelGuardDeletedMultipliers
          v numericalGuards multipliers := rfl

example
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCommonMultiplierBadSet
        n K h Phead X0 y u v dedicatedRows numericalGuards =
      let interval := tangentCommonMultiplierInterval n K h u v
      tangentHeadBadMultipliers Phead interval ∪
        tangentExceptionalMultipliers n X0 y interval ∪
        tangentDedicatedRowMultipliers y dedicatedRows interval ∪
        tangentEndpointGuardDeletedMultipliers
          u v numericalGuards interval := rfl

example
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards =
      (Finset.Ioc (n / v) ((2 * n - K * h) / u)).filter
        (fun a ↦ Nat.Coprime a Phead ∧
          X0 ≤ 2 * n / completeRoughLabel y a ∧
          completeRoughLabel y a ∉ dedicatedRows ∧
          u * a ∉ numericalGuards ∧
          v * a ∉ numericalGuards) := rfl

example
    {n K h Phead X0 y u v a : ℕ}
    {dedicatedRows numericalGuards : Finset ℕ} :
    a ∈ tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards ↔
      (n / v < a ∧ a ≤ (2 * n - K * h) / u) ∧
      Nat.Coprime a Phead ∧
      X0 ≤ 2 * n / completeRoughLabel y a ∧
      completeRoughLabel y a ∉ dedicatedRows ∧
      u * a ∉ numericalGuards ∧
      v * a ∉ numericalGuards := by
  simpa only [tangentBroadUpper, tangentRoughScale] using
    (mem_tangentCleanCommonMultiplierList
      (n := n) (K := K) (h := h) (Phead := Phead) (X0 := X0)
      (y := y) (u := u) (v := v) (a := a)
      (dedicatedRows := dedicatedRows)
      (numericalGuards := numericalGuards))

example {n K h u v a : ℕ} :
    a ∈ Finset.Ioc (n / v) ((2 * n - K * h) / u) ↔
      n / v < a ∧ a ≤ (2 * n - K * h) / u := by
  simpa only [tangentCommonMultiplierInterval, tangentBroadUpper] using
    (mem_tangentCommonMultiplierInterval
      (n := n) (K := K) (h := h) (u := u) (v := v) (a := a))

example (n K h u v : ℕ) :
    (Finset.Ioc (n / v) ((2 * n - K * h) / u)).card =
      (2 * n - K * h) / u - n / v := by
  simpa only [tangentCommonMultiplierInterval, tangentBroadUpper] using
    card_tangentCommonMultiplierInterval n K h u v

example
    {n K h u v a : ℕ}
    (hu : 0 < u) (hv : 0 < v) (hvu : v ≤ u)
    (ha : a ∈ Finset.Ioc (n / v) ((2 * n - K * h) / u)) :
    u * a ∈ Finset.Ioc n (2 * n - K * h) ∧
      v * a ∈ Finset.Ioc n (2 * n - K * h) := by
  exact tangentCommonMultiplierInterval_endpoints hu hv hvu ha

example
    {y label a : ℕ} (hlabel : 0 < label) (hlabelLe : label ≤ y)
    (ha : 0 < a) :
    completeRoughSignature y (label * a) =
        completeRoughSignature y a ∧
      completeRoughLabel y (label * a) = completeRoughLabel y a :=
  ⟨completeRoughSignature_small_left_mul hlabel hlabelLe ha,
    completeRoughLabel_small_left_mul hlabel hlabelLe ha⟩

example
    {W n K h Phead X0 y u v a : ℕ} {r0 : ℝ}
    {dedicatedRows numericalGuards : Finset ℕ}
    (hr0Lower : 1 < r0) (hr0Upper : r0 < 3 / 2)
    (huPrime : u.Prime) (hvPrime : v.Prime) (huv : u ≠ v)
    (hWv : W < v) (hvu : v ≤ u) (huy : u ≤ y)
    (hratio : (u : ℝ) / (v : ℝ) ≤ r0)
    (ha : a ∈ (Finset.Ioc (n / v) ((2 * n - K * h) / u)).filter
      (fun multiplier ↦ Nat.Coprime multiplier Phead ∧
        X0 ≤ 2 * n / completeRoughLabel y multiplier ∧
        completeRoughLabel y multiplier ∉ dedicatedRows ∧
        u * multiplier ∉ numericalGuards ∧
        v * multiplier ∉ numericalGuards)) :
    Nat.Coprime a Phead ∧
      X0 ≤ 2 * n / completeRoughLabel y a ∧
      completeRoughLabel y a ∉ dedicatedRows ∧
      u * a ∈ Finset.Ioc n (2 * n - K * h) ∧
      v * a ∈ Finset.Ioc n (2 * n - K * h) ∧
      u * a ∉ numericalGuards ∧
      v * a ∉ numericalGuards ∧
      u * a ≠ v * a ∧
      completeRoughSignature y (u * a) =
        completeRoughSignature y a ∧
      completeRoughSignature y a =
        completeRoughSignature y (v * a) ∧
      completeRoughLabel y (u * a) = completeRoughLabel y a ∧
      completeRoughLabel y a = completeRoughLabel y (v * a) := by
  exact tangentCleanCommonMultiplier_mem_certificate
    hr0Lower hr0Upper huPrime hvPrime huv hWv hvu huy hratio ha

example
    {label : ℕ} (hlabel : 0 < label)
    (numericalGuards multipliers : Finset ℕ) :
    (multipliers.filter
      (fun a ↦ label * a ∈ numericalGuards)).card ≤
        numericalGuards.card :=
  card_tangentLabelGuardDeletedMultipliers_le
    hlabel numericalGuards multipliers

example
    {u v : ℕ} (hu : 0 < u) (hv : 0 < v)
    (numericalGuards multipliers : Finset ℕ) :
    ((multipliers.filter (fun a ↦ u * a ∈ numericalGuards)) ∪
      multipliers.filter (fun a ↦ v * a ∈ numericalGuards)).card ≤
        2 * numericalGuards.card :=
  card_tangentEndpointGuardDeletedMultipliers_le
    hu hv numericalGuards multipliers

example
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCommonMultiplierBadSet
        n K h Phead X0 y u v dedicatedRows numericalGuards ⊆
      Finset.Ioc (n / v) ((2 * n - K * h) / u) := by
  simpa only [tangentCommonMultiplierInterval, tangentBroadUpper] using
    tangentCommonMultiplierBadSet_subset_interval
      n K h Phead X0 y u v dedicatedRows numericalGuards

example
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards =
      Finset.Ioc (n / v) ((2 * n - K * h) / u) \
        tangentCommonMultiplierBadSet
          n K h Phead X0 y u v dedicatedRows numericalGuards := by
  simpa only [tangentCommonMultiplierInterval, tangentBroadUpper] using
    tangentCleanCommonMultiplierList_eq_sdiff_badSet
      n K h Phead X0 y u v dedicatedRows numericalGuards

example
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    (tangentCleanCommonMultiplierList
      n K h Phead X0 y u v dedicatedRows numericalGuards).card =
      (Finset.Ioc (n / v) ((2 * n - K * h) / u)).card -
        (tangentCommonMultiplierBadSet
          n K h Phead X0 y u v dedicatedRows numericalGuards).card := by
  simpa only [tangentCommonMultiplierInterval, tangentBroadUpper] using
    card_tangentCleanCommonMultiplierList
      n K h Phead X0 y u v dedicatedRows numericalGuards

example
    (n K h Phead X0 y u v : ℕ)
    (dedicatedRows numericalGuards : Finset ℕ) :
    (tangentCommonMultiplierBadSet
      n K h Phead X0 y u v dedicatedRows numericalGuards).card ≤
      (tangentHeadBadMultipliers Phead
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      (tangentExceptionalMultipliers n X0 y
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      (tangentDedicatedRowMultipliers y dedicatedRows
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      (tangentEndpointGuardDeletedMultipliers u v numericalGuards
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card := by
  simpa only [tangentCommonMultiplierInterval, tangentBroadUpper] using
    card_tangentCommonMultiplierBadSet_le
      n K h Phead X0 y u v dedicatedRows numericalGuards

example
    {n K h Phead X0 y u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (dedicatedRows numericalGuards : Finset ℕ) :
    (Finset.Ioc (n / v) ((2 * n - K * h) / u)).card ≤
      (tangentCleanCommonMultiplierList
        n K h Phead X0 y u v dedicatedRows numericalGuards).card +
      (tangentHeadBadMultipliers Phead
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      (tangentExceptionalMultipliers n X0 y
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      (tangentDedicatedRowMultipliers y dedicatedRows
        (Finset.Ioc (n / v) ((2 * n - K * h) / u))).card +
      2 * numericalGuards.card := by
  simpa only [tangentCommonMultiplierInterval, tangentBroadUpper] using
    tangentCommonMultiplier_finite_deletion_ledger
      hu hv dedicatedRows numericalGuards

end

end Erdos390.WholePaper
