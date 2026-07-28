import Erdos390.WholePaper.BankPaperFourFiveOrderedLastPrimeExpansion

/-!
# Real moving endpoints for the exposed last prime

The natural quotient endpoints used for the first exact cardinal expansion
are convenient combinatorially, but they introduce an avoidable unit-cell
rounding loss before the physical substitution `t = qv`.  The prime-counting
endpoint theorem accepts arbitrary real endpoints.  We therefore apply it at

`a = max y (A/q)` and `b = B/q`

in the real field.  Their natural floors are exactly the earlier quotient
endpoints, so the prime fibre is unchanged.  After this refinement the
physical substitution has the exact endpoints `max (q*y) A` and `B`.
-/

open scoped BigOperators
open Set

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

/-- A prefix product embedded in `Real`. -/
def fourFiveRealPrefixProduct
    {m : Nat} (q : Fin m -> Nat) : Real :=
  ((∏ i, q i : Nat) : Real)

theorem fourFiveRealPrefixProduct_pos
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    0 < fourFiveRealPrefixProduct q := by
  unfold fourFiveRealPrefixProduct
  exact_mod_cast fourFiveOrderedPrimePrefix_prod_pos hq

/-- Exact real lower endpoint of the exposed last prime. -/
def fourFiveLastPrimeRealLower
    {m : Nat} (q : Fin m -> Nat) (y A : Nat) : Real :=
  max (y : Real) ((A : Real) / fourFiveRealPrefixProduct q)

/-- Exact real upper endpoint of the exposed last prime. -/
def fourFiveLastPrimeRealUpper
    {m : Nat} (q : Fin m -> Nat) (B : Nat) : Real :=
  (B : Real) / fourFiveRealPrefixProduct q

theorem floor_fourFiveLastPrimeRealUpper
    {m : Nat} (q : Fin m -> Nat) (B : Nat) :
    ⌊fourFiveLastPrimeRealUpper q B⌋₊ =
      fourFiveLastPrimeUpper q B := by
  unfold fourFiveLastPrimeRealUpper fourFiveRealPrefixProduct
    fourFiveLastPrimeUpper
  exact Nat.floor_div_eq_div B (∏ i, q i)

theorem floor_fourFiveLastPrimeRealLower
    {m : Nat} (q : Fin m -> Nat) (y A : Nat) :
    ⌊fourFiveLastPrimeRealLower q y A⌋₊ =
      fourFiveLastPrimeLower q y A := by
  unfold fourFiveLastPrimeRealLower fourFiveRealPrefixProduct
    fourFiveLastPrimeLower
  by_cases hright : (y : Real) <=
      (A : Real) / ((∏ i, q i : Nat) : Real)
  · have hrightNat : y <= A / ∏ i, q i := by
      rw [← Nat.floor_div_eq_div (K := Real)]
      exact Nat.le_floor hright
    rw [max_eq_right hright, Nat.floor_div_eq_div,
      max_eq_right hrightNat]
  · have hleft : (A : Real) / ((∏ i, q i : Nat) : Real) <=
        (y : Real) := le_of_not_ge hright
    have hleftNat : A / ∏ i, q i <= y := by
      rw [← Nat.floor_div_eq_div (K := Real)]
      exact Nat.floor_le_of_le hleft
    rw [max_eq_left hleft, Nat.floor_natCast,
      max_eq_left hleftNat]

/-- Real-endpoint logarithmic integral for one last-prime fibre. -/
def fourFiveLastPrimeRealIntegral
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Real :=
  if fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B then
    ∫ v in fourFiveLastPrimeRealLower q y A..
      fourFiveLastPrimeRealUpper q B, 1 / Real.log v
  else 0

/-- Fifth-log PNT loss at the exact real moving endpoints. -/
def fourFiveLastPrimeRealEndpointError
    {m : Nat} (C : Real) (q : Fin m -> Nat)
    (y A B : Nat) : Real :=
  if fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B then
    3 * C * fourFiveLastPrimeRealUpper q B /
      Real.log (fourFiveLastPrimeRealLower q y A) ^ 5
  else 0

/-- The real-endpoint main after the exact physical substitution `t=qv`. -/
def fourFiveLastPrimeRealPhysicalIntegral
    {m : Nat} (q : Fin m -> Nat) (y A B : Nat) : Real :=
  if fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B then
    (fourFiveRealPrefixProduct q)⁻¹ *
      ∫ t in
          fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealLower q y A..
          fourFiveRealPrefixProduct q *
              fourFiveLastPrimeRealUpper q B,
        1 / Real.log (t / fourFiveRealPrefixProduct q)
  else 0

theorem fourFiveLastPrimeRealLower_ge_y
    {m y A : Nat} (q : Fin m -> Nat) :
    (y : Real) <= fourFiveLastPrimeRealLower q y A := by
  exact le_max_left _ _

theorem fourFiveRealPrefixProduct_mul_realUpper
    {m y B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveRealPrefixProduct q * fourFiveLastPrimeRealUpper q B =
      (B : Real) := by
  unfold fourFiveLastPrimeRealUpper
  exact mul_div_cancel₀ (B : Real) (fourFiveRealPrefixProduct_pos hq).ne'

theorem fourFiveRealPrefixProduct_mul_realLower
    {m y A B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveRealPrefixProduct q * fourFiveLastPrimeRealLower q y A =
      max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real) := by
  have hQnonneg : 0 <= fourFiveRealPrefixProduct q :=
    (fourFiveRealPrefixProduct_pos hq).le
  unfold fourFiveLastPrimeRealLower
  rw [mul_max_of_nonneg _ _ hQnonneg,
    mul_div_cancel₀ (A : Real) (fourFiveRealPrefixProduct_pos hq).ne']

/-- Exact linear change of variables at the real moving endpoints. -/
theorem fourFiveLastPrimeRealIntegral_eq_physicalIntegral
    {m y A B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealIntegral q y A B =
      fourFiveLastPrimeRealPhysicalIntegral q y A B := by
  have hQne : fourFiveRealPrefixProduct q ≠ 0 :=
    (fourFiveRealPrefixProduct_pos hq).ne'
  by_cases hLU : fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B
  · simp only [fourFiveLastPrimeRealIntegral,
      fourFiveLastPrimeRealPhysicalIntegral, hLU, if_true]
    have hsubst := intervalIntegral.integral_comp_mul_left
      (fun t : Real =>
        1 / Real.log (t / fourFiveRealPrefixProduct q)) hQne
      (a := fourFiveLastPrimeRealLower q y A)
      (b := fourFiveLastPrimeRealUpper q B)
    calc
      (∫ v in fourFiveLastPrimeRealLower q y A..
          fourFiveLastPrimeRealUpper q B, 1 / Real.log v) =
          ∫ v in fourFiveLastPrimeRealLower q y A..
            fourFiveLastPrimeRealUpper q B,
            1 / Real.log
              (fourFiveRealPrefixProduct q * v /
                fourFiveRealPrefixProduct q) := by
        apply intervalIntegral.integral_congr
        intro v _hv
        change 1 / Real.log v =
          1 / Real.log
            (fourFiveRealPrefixProduct q * v /
              fourFiveRealPrefixProduct q)
        rw [mul_div_cancel_left₀ v hQne]
      _ = (fourFiveRealPrefixProduct q)⁻¹ *
          ∫ t in
              fourFiveRealPrefixProduct q *
                  fourFiveLastPrimeRealLower q y A..
              fourFiveRealPrefixProduct q *
                  fourFiveLastPrimeRealUpper q B,
            1 / Real.log (t / fourFiveRealPrefixProduct q) := by
        simpa only [smul_eq_mul] using hsubst
  · simp [fourFiveLastPrimeRealIntegral,
      fourFiveLastPrimeRealPhysicalIntegral, hLU]

/-- Endpoint-simplified form of the exact physical integral. -/
theorem fourFiveLastPrimeRealPhysicalIntegral_eq_maxIntegral
    {m y A B : Nat} {q : Fin m -> Nat}
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealPhysicalIntegral q y A B =
      if fourFiveLastPrimeRealLower q y A <=
          fourFiveLastPrimeRealUpper q B then
        (fourFiveRealPrefixProduct q)⁻¹ *
          ∫ t in
              max (fourFiveRealPrefixProduct q * (y : Real)) (A : Real)..
              (B : Real),
            1 / Real.log (t / fourFiveRealPrefixProduct q)
      else 0 := by
  unfold fourFiveLastPrimeRealPhysicalIntegral
  rw [fourFiveRealPrefixProduct_mul_realLower hq,
    fourFiveRealPrefixProduct_mul_realUpper hq]

/-- Sum of the exactly transformed real-endpoint physical integrals. -/
def fourFiveOrderedLastPrimeRealIntegralLayer
    (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeRealIntegral q y A B

/-- Sum of the exactly transformed real-endpoint physical integrals. -/
def fourFiveOrderedLastPrimeRealPhysicalLayer
    (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeRealPhysicalIntegral q y A B

theorem fourFiveOrderedLastPrimeRealIntegralLayer_eq_physicalLayer
    (m y A B : Nat) :
    fourFiveOrderedLastPrimeRealIntegralLayer m y A B =
      fourFiveOrderedLastPrimeRealPhysicalLayer m y A B := by
  unfold fourFiveOrderedLastPrimeRealIntegralLayer
    fourFiveOrderedLastPrimeRealPhysicalLayer
  apply Finset.sum_congr rfl
  intro q hq
  exact fourFiveLastPrimeRealIntegral_eq_physicalIntegral hq

/-- The same exact prime fibre, estimated directly at its real endpoints. -/
theorem abs_fourFiveLastPrimeFiber_card_sub_realIntegral_le
    {m y A B : Nat} {q : Fin m -> Nat} {C X0 : Real}
    (_hC : 0 < C) (_hX0 : 3 <= X0) (hy : X0 <= (y : Real))
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B)
    (hPNT : ∀ a b : Real, X0 <= a → a <= b →
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    abs (((fourFiveLastPrimeFiber q y A B).card : Real) -
        fourFiveLastPrimeRealIntegral q y A B) <=
      fourFiveLastPrimeRealEndpointError C q y A B := by
  by_cases hLU : fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B
  · have hnatLU : fourFiveLastPrimeLower q y A <=
        fourFiveLastPrimeUpper q B := by
      rw [← floor_fourFiveLastPrimeRealLower,
        ← floor_fourFiveLastPrimeRealUpper]
      exact Nat.floor_mono hLU
    have hcountNat :=
      fourFiveLastPrimeFiber_card_eq_primeCounting_sub hq hnatLU
    have hpiMono :
        Nat.primeCounting (fourFiveLastPrimeLower q y A) <=
          Nat.primeCounting (fourFiveLastPrimeUpper q B) :=
      Nat.monotone_primeCounting hnatLU
    have hcountReal :
        ((fourFiveLastPrimeFiber q y A B).card : Real) =
          (Nat.primeCounting (fourFiveLastPrimeUpper q B) : Real) -
            (Nat.primeCounting (fourFiveLastPrimeLower q y A) : Real) := by
      rw [hcountNat, Nat.cast_sub hpiMono]
    have hlowerX : X0 <= fourFiveLastPrimeRealLower q y A :=
      hy.trans (fourFiveLastPrimeRealLower_ge_y q)
    have hbound := hPNT
      (fourFiveLastPrimeRealLower q y A)
      (fourFiveLastPrimeRealUpper q B) hlowerX hLU
    rw [floor_fourFiveLastPrimeRealLower,
      floor_fourFiveLastPrimeRealUpper] at hbound
    simpa only [fourFiveLastPrimeRealIntegral,
      fourFiveLastPrimeRealEndpointError, hLU, if_true,
      hcountReal] using hbound
  · have hfloor :
        ⌊fourFiveLastPrimeRealUpper q B⌋₊ <=
          ⌊fourFiveLastPrimeRealLower q y A⌋₊ := by
      exact Nat.floor_mono (le_of_not_ge hLU)
    have hnat : fourFiveLastPrimeUpper q B <=
        fourFiveLastPrimeLower q y A := by
      simpa only [floor_fourFiveLastPrimeRealUpper,
        floor_fourFiveLastPrimeRealLower] using hfloor
    have hempty :
        Finset.Ioc (fourFiveLastPrimeLower q y A)
          (fourFiveLastPrimeUpper q B) = ∅ := by
      exact Finset.Ioc_eq_empty_of_le hnat
    rw [fourFiveLastPrimeFiber_eq_primeInterval
      (fourFiveOrderedPrimePrefix_prod_pos hq), hempty]
    simp [fourFiveLastPrimeRealIntegral,
      fourFiveLastPrimeRealEndpointError, hLU]

/-- Layer sum of the exact real-endpoint fifth-log losses. -/
def fourFiveOrderedLastPrimeRealEndpointErrorLayer
    (C : Real) (m y A B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    fourFiveLastPrimeRealEndpointError C q y A B

/-! ## Quantitative fifth-log ledger -/

/-- Literal reciprocal mass of the prime coordinate band `(y,B]`. -/
def fourFivePrimeCoordinateReciprocalMass (y B : Nat) : Real :=
  ∑ p ∈ fourFivePrimeCoordinateBand y B, (p : Real)⁻¹

/-- Literal reciprocal mass of all ordered `m`-coordinate prefixes. -/
def fourFiveOrderedPrimePrefixReciprocalMass
    (m y B : Nat) : Real :=
  ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
    (fourFiveRealPrefixProduct q)⁻¹

/-- Ordered prefix reciprocal mass is exactly the `m`th power of the
one-coordinate prime-band mass. -/
theorem fourFiveOrderedPrimePrefixReciprocalMass_eq_pow
    (m y B : Nat) :
    fourFiveOrderedPrimePrefixReciprocalMass m y B =
      fourFivePrimeCoordinateReciprocalMass y B ^ m := by
  unfold fourFiveOrderedPrimePrefixReciprocalMass
    fourFiveOrderedPrimePrefixSet
    fourFivePrimeCoordinateReciprocalMass
  rw [Finset.sum_pow']
  apply Finset.sum_congr rfl
  intro q _hq
  unfold fourFiveRealPrefixProduct
  rw [Nat.cast_prod, ← Finset.prod_inv_distrib]

theorem fourFivePrimeCoordinateReciprocalMass_nonneg
    (y B : Nat) :
    0 <= fourFivePrimeCoordinateReciprocalMass y B := by
  unfold fourFivePrimeCoordinateReciprocalMass
  positivity

/-- One fibre's real-endpoint PNT loss is its reciprocal-prefix weight times
the common fifth-log factor at `y`. -/
theorem fourFiveLastPrimeRealEndpointError_le_reciprocalWeight
    {m y A B : Nat} {q : Fin m -> Nat} {C : Real}
    (hC : 0 <= C) (hy : 2 <= y)
    (hq : q ∈ fourFiveOrderedPrimePrefixSet m y B) :
    fourFiveLastPrimeRealEndpointError C q y A B <=
      (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        (fourFiveRealPrefixProduct q)⁻¹ := by
  have hQpos : 0 < fourFiveRealPrefixProduct q :=
    fourFiveRealPrefixProduct_pos hq
  have hlogy : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hyRealPos : (0 : Real) < (y : Real) := by
    exact_mod_cast (show 0 < y by omega)
  have hyRealOne : (1 : Real) < (y : Real) := by
    exact_mod_cast (show 1 < y by omega)
  by_cases hLU : fourFiveLastPrimeRealLower q y A <=
      fourFiveLastPrimeRealUpper q B
  · have hLowerPos : 0 < fourFiveLastPrimeRealLower q y A :=
      hyRealPos.trans_le
        (fourFiveLastPrimeRealLower_ge_y q)
    have hlogLower : 0 < Real.log (fourFiveLastPrimeRealLower q y A) :=
      Real.log_pos (hyRealOne.trans_le
        (fourFiveLastPrimeRealLower_ge_y q))
    have hlogLe : Real.log (y : Real) <=
        Real.log (fourFiveLastPrimeRealLower q y A) :=
      Real.log_le_log (by exact_mod_cast (show 0 < y by omega))
        (fourFiveLastPrimeRealLower_ge_y q)
    have hpow : Real.log (y : Real) ^ 5 <=
        Real.log (fourFiveLastPrimeRealLower q y A) ^ 5 :=
      pow_le_pow_left₀ hlogy.le hlogLe 5
    have hUpperNonneg : 0 <= fourFiveLastPrimeRealUpper q B := by
      unfold fourFiveLastPrimeRealUpper
      positivity
    unfold fourFiveLastPrimeRealEndpointError
    rw [if_pos hLU]
    calc
      3 * C * fourFiveLastPrimeRealUpper q B /
          Real.log (fourFiveLastPrimeRealLower q y A) ^ 5 <=
        3 * C * fourFiveLastPrimeRealUpper q B /
          Real.log (y : Real) ^ 5 :=
        div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (by norm_num) hC) hUpperNonneg)
          (pow_pos hlogy 5) hpow
      _ = (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
          (fourFiveRealPrefixProduct q)⁻¹ := by
        unfold fourFiveLastPrimeRealUpper
        field_simp [hQpos.ne', hlogy.ne']
  · unfold fourFiveLastPrimeRealEndpointError
    rw [if_neg hLU]
    positivity

/-- Summed real-endpoint loss with the exact prefix reciprocal mass. -/
theorem fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_prefixMass
    {C : Real} (hC : 0 <= C) {m y A B : Nat} (hy : 2 <= y) :
    fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B <=
      (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        fourFiveOrderedPrimePrefixReciprocalMass m y B := by
  unfold fourFiveOrderedLastPrimeRealEndpointErrorLayer
    fourFiveOrderedPrimePrefixReciprocalMass
  calc
    (∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        fourFiveLastPrimeRealEndpointError C q y A B) <=
      ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
          (fourFiveRealPrefixProduct q)⁻¹ := by
      apply Finset.sum_le_sum
      intro q hq
      exact fourFiveLastPrimeRealEndpointError_le_reciprocalWeight
        hC hy hq
    _ = (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
          (fourFiveRealPrefixProduct q)⁻¹ := by
      rw [Finset.mul_sum]

/-- If the one-coordinate reciprocal mass is at most `M`, the layer endpoint
loss is at most `3 C B M^m / log(y)^5`. -/
theorem fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_massPow
    {C M : Real} (hC : 0 <= C) {m y A B : Nat} (hy : 2 <= y)
    (hmass : fourFivePrimeCoordinateReciprocalMass y B <= M) :
    fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B <=
      (3 * C * (B : Real) / Real.log (y : Real) ^ 5) * M ^ m := by
  have hcoeff : 0 <=
      3 * C * (B : Real) / Real.log (y : Real) ^ 5 := by
    positivity
  have hmassPow : fourFivePrimeCoordinateReciprocalMass y B ^ m <= M ^ m :=
    pow_le_pow_left₀ (fourFivePrimeCoordinateReciprocalMass_nonneg y B)
      hmass m
  calc
    fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B <=
        (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
          fourFiveOrderedPrimePrefixReciprocalMass m y B :=
      fourFiveOrderedLastPrimeRealEndpointErrorLayer_le_prefixMass hC hy
    _ = (3 * C * (B : Real) / Real.log (y : Real) ^ 5) *
        fourFivePrimeCoordinateReciprocalMass y B ^ m := by
      rw [fourFiveOrderedPrimePrefixReciprocalMass_eq_pow]
    _ <= (3 * C * (B : Real) / Real.log (y : Real) ^ 5) * M ^ m :=
      mul_le_mul_of_nonneg_left hmassPow hcoeff

/-- The ordered layer estimated at exact real moving endpoints. -/
theorem abs_fourFiveOrderedPrimeLayerMass_sub_realLastPrimeIntegral_le
    {m y A B : Nat} {C X0 : Real}
    (hC : 0 < C) (hX0 : 3 <= X0) (hy : X0 <= (y : Real))
    (hPNT : ∀ a b : Real, X0 <= a → a <= b →
      abs (((Nat.primeCounting ⌊b⌋₊ : Real) -
          (Nat.primeCounting ⌊a⌋₊ : Real)) -
          (∫ v in a..b, 1 / Real.log v)) <=
        3 * C * b / Real.log a ^ 5) :
    abs ((fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
        fourFiveOrderedLastPrimeRealIntegralLayer m y A B) <=
      fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B := by
  have hcardNat :=
    fourFiveOrderedPrimeLayerMass_eq_sum_lastPrimeFibers m y A B
  have hcardReal :
      (fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) =
        ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
          ((fourFiveLastPrimeFiber q y A B).card : Real) := by
    exact_mod_cast hcardNat
  rw [hcardReal]
  unfold fourFiveOrderedLastPrimeRealIntegralLayer
    fourFiveOrderedLastPrimeRealEndpointErrorLayer
  rw [← Finset.sum_sub_distrib]
  calc
    abs (∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        (((fourFiveLastPrimeFiber q y A B).card : Real) -
          fourFiveLastPrimeRealIntegral q y A B)) <=
        ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
          abs (((fourFiveLastPrimeFiber q y A B).card : Real) -
            fourFiveLastPrimeRealIntegral q y A B) :=
      Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ q ∈ fourFiveOrderedPrimePrefixSet m y B,
        fourFiveLastPrimeRealEndpointError C q y A B := by
      apply Finset.sum_le_sum
      intro q hq
      exact abs_fourFiveLastPrimeFiber_card_sub_realIntegral_le
        hC hX0 hy hq hPNT

/-- One real-endpoint PNT witness works for every ordered layer. -/
theorem exists_abs_fourFiveOrderedPrimeLayerMass_sub_realLastPrimeIntegral_le :
    ∃ C : Real, 0 < C ∧ ∃ X0 : Real, 3 <= X0 ∧
      ∀ {m y A B : Nat}, X0 <= (y : Real) →
        abs ((fourFiveOrderedPrimeLayerMass (m + 1) y A B : Real) -
            fourFiveOrderedLastPrimeRealIntegralLayer m y A B) <=
          fourFiveOrderedLastPrimeRealEndpointErrorLayer C m y A B := by
  obtain ⟨C, hC, X0, hX0, hPNT⟩ :=
    exists_abs_fourFivePrimeCounting_sub_integral_inv_log_le
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro m y A B hy
  exact abs_fourFiveOrderedPrimeLayerMass_sub_realLastPrimeIntegral_le
    hC hX0 hy hPNT

end Erdos390.WholePaper.BankPaperRealization
