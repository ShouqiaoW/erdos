import Erdos390.Full.GuardedUniformCell
import Erdos390.Full.PaperScaleMarkedCell
import Erdos390.Full.ValuationTiltCell

/-!
# The concrete numerical-guard census used by the smooth bridge

The rough construction has only two kinds of numerical occurrences which can
meet one of the active smooth cells:

* promoted smooth anchors, in `O(y)` slots;
* endpoints (and the possible donor occurrence) of an `O(y)` family of bank
  paths, with at most one component at each geometric scale.

This file represents those occurrences by a literal finite slot type and
defines the numerical guard set as the image of its value map.  Consequently
the guard-cardinality estimate is a theorem about `Finset.image`; it is not a
field of a contract and it is not assumed about an arbitrary finset.

The number of geometric slots is fixed here to `ceil(log n)+1`.  This is a
harmless enlargement of the paper's geometric-scale list and makes the
`O(y log n)` census completely explicit.  Multiple slots are allowed to map to
the same integer; this only makes the proved image-cardinality bound stronger.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperGuardCensus

open ArithmeticModel Scale StructuredCells HeadPattern
open FiniteProbability GuardedUniformCell ValuationTiltCell

noncomputable section

/-- A concrete upper bound for the number of geometric bank scales. -/
def scaleSlots (n : ℕ) : ℕ := ⌈L n⌉₊ + 1

/-- The three bank occurrences which are guarded at one component: its two
states and its designated backing donor.  A donor lying above the physical
cells simply has empty intersection with those cells. -/
inductive BankGuardRole
  | stateZero
  | stateOne
  | donor
  deriving DecidableEq, Fintype

/-- Literal occurrence slots in the bridge-relevant guard census.  The fixed
natural constants `Cprom` and `Cbank` are the construction's absolute path
multiplicities. -/
abbrev GuardSlot (n Cprom Cbank : ℕ) :=
  Fin (Cprom * yNat n) ⊕
    (Fin (Cbank * yNat n) × Fin (scaleSlots n) × BankGuardRole)

/-- The data retained from the bank/anchor construction: the actual integer
owned by every concrete occurrence slot.  There is deliberately no
cardinality field. -/
structure Ledger (n Cprom Cbank : ℕ) where
  value : GuardSlot n Cprom Cbank → ℕ

/-- The exhaustive numerical guards which can meet an active smooth cell. -/
def Ledger.guards {n Cprom Cbank : ℕ} (G : Ledger n Cprom Cbank) : Finset ℕ :=
  Finset.univ.image G.value

/-- Exact number of occurrence slots before possible collisions of their
integer values. -/
theorem card_guardSlot (n Cprom Cbank : ℕ) :
    Fintype.card (GuardSlot n Cprom Cbank) =
      Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 := by
  simp only [GuardSlot, Fintype.card_sum, Fintype.card_fin,
    Fintype.card_prod]
  have hrole : Fintype.card BankGuardRole = 3 := by decide
  rw [hrole]
  ring

/-- The global bridge-relevant guard census, derived from the image
construction rather than postulated. -/
theorem Ledger.card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) :
    G.guards.card ≤
      Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 := by
  calc
    G.guards.card ≤ (Finset.univ : Finset (GuardSlot n Cprom Cbank)).card :=
      Finset.card_image_le
    _ = Fintype.card (GuardSlot n Cprom Cbank) := Finset.card_univ
    _ = _ := card_guardSlot n Cprom Cbank

/-- The concrete ceiling has the advertised logarithmic size. -/
theorem cast_scaleSlots_lt {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) < L n + 2 := by
  have hL : 0 ≤ L n := by
    unfold L
    exact Real.log_nonneg (by exact_mod_cast hn)
  unfold scaleSlots
  push_cast
  have hceil := Nat.ceil_lt_add_one hL
  linarith

/-- A weak inequality convenient in multiplicative census estimates. -/
theorem cast_scaleSlots_le {n : ℕ} (hn : 1 ≤ n) :
    (scaleSlots n : ℝ) ≤ L n + 2 :=
  (cast_scaleSlots_lt hn).le

/-- Real-cast form of the image census. -/
theorem Ledger.cast_card_guards_le {n Cprom Cbank : ℕ}
    (G : Ledger n Cprom Cbank) (hn : 1 ≤ n) :
    (G.guards.card : ℝ) ≤
      (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by
  have hcard : (G.guards.card : ℝ) ≤
      (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := by
    exact_mod_cast G.card_guards_le
  have hy0 : (0 : ℝ) ≤ (yNat n : ℝ) := by positivity
  have hscale := cast_scaleSlots_le hn
  calc
    (G.guards.card : ℝ) ≤
        (Cprom * yNat n + Cbank * yNat n * scaleSlots n * 3 : ℕ) := hcard
    _ = ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (scaleSlots n : ℝ)) *
          (yNat n : ℝ) := by
      push_cast
      ring
    _ ≤ ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
          (yNat n : ℝ) := by
      gcongr
    _ = (Cprom + 3 * Cbank * (L n + 2)) * (yNat n : ℝ) := by ring

/-- Explicit real majorant for the ratio `#guards / n`. -/
def censusRatioMajorant (Cprom Cbank : ℕ) (n : ℕ) : ℝ :=
  ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n / (n : ℝ)

private theorem tendsto_L_pow_zero_div_nat_rpow_zero (a : ℝ)
    (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ 1 / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (0 : ℝ) / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (0 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, Real.rpow_zero]

private theorem tendsto_L_div_nat_rpow_zero (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ ↦ L n / (n : ℝ) ^ a) atTop (𝓝 0) := by
  have hreal : Tendsto
      (fun x : ℝ ↦ Real.log x ^ (1 : ℝ) / x ^ a) atTop (𝓝 0) :=
    (isLittleO_log_rpow_rpow_atTop (1 : ℝ) ha).tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  apply hnat.congr'
  filter_upwards [eventually_gt_atTop 1] with n hn
  simp only [Function.comp_apply, L, Real.rpow_one]

private theorem y_div_nat_eq_inv_rpow {n : ℕ} (hn : 0 < n) :
    y n / (n : ℝ) = 1 / (n : ℝ) ^ (7 / 9 : ℝ) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hpow :
      (n : ℝ) ^ (2 / 9 : ℝ) * (n : ℝ) ^ (7 / 9 : ℝ) = (n : ℝ) := by
    rw [← Real.rpow_add hnR]
    norm_num [Real.rpow_one]
  unfold y
  field_simp [(Real.rpow_pos_of_pos hnR (7 / 9 : ℝ)).ne', hnR.ne']
  nlinarith

/-- The concrete `O(y log n)` census is `o(n)`. -/
theorem tendsto_censusRatioMajorant_zero (Cprom Cbank : ℕ) :
    Tendsto (censusRatioMajorant Cprom Cbank) atTop (𝓝 0) := by
  let a : ℝ := (7 / 9 : ℝ)
  have ha : 0 < a := by norm_num [a]
  have hzero := tendsto_L_pow_zero_div_nat_rpow_zero a ha
  have hlog := tendsto_L_div_nat_rpow_zero a ha
  have hsum : Tendsto
      (fun n : ℕ ↦
        (Cprom : ℝ) * (1 / (n : ℝ) ^ a) +
          3 * (Cbank : ℝ) *
            (L n / (n : ℝ) ^ a + 2 * (1 / (n : ℝ) ^ a)))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hzero.const_mul (Cprom : ℝ)).add
        ((hlog.add (hzero.const_mul 2)).const_mul (3 * (Cbank : ℝ)))
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  rw [censusRatioMajorant]
  rw [show
    ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) * y n / (n : ℝ) =
      ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
        (y n / (n : ℝ)) by ring]
  rw [y_div_nat_eq_inv_rpow hn]
  dsimp only [a]
  ring

/-- The literal guard set has vanishing relative cardinality, with no
cardinality premise on the ledger. -/
theorem Ledger.tendsto_card_div_nat_zero {Cprom Cbank : ℕ}
    (G : ∀ n, Ledger n Cprom Cbank) :
    Tendsto (fun n : ℕ ↦ ((G n).guards.card : ℝ) / (n : ℝ))
      atTop (𝓝 0) := by
  apply squeeze_zero'
  · filter_upwards with n
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hcard := (G n).cast_card_guards_le hn
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
    have hyfloor : (yNat n : ℝ) ≤ y n :=
      Nat.floor_le (Scale.y_pos (by omega : 0 < n)).le
    calc
      ((G n).guards.card : ℝ) / (n : ℝ) ≤
          ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
            (yNat n : ℝ) / (n : ℝ) := by
        exact div_le_div_of_nonneg_right hcard hn0
      _ ≤ ((Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2)) *
            y n / (n : ℝ) := by
        have hcoef : 0 ≤ (Cprom : ℝ) + 3 * (Cbank : ℝ) * (L n + 2) := by
          have hL : 0 ≤ L n := by
            exact Real.log_nonneg (by exact_mod_cast hn)
          positivity
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hyfloor hcoef) hn0
      _ = censusRatioMajorant Cprom Cbank n := rfl
  · exact tendsto_censusRatioMajorant_zero Cprom Cbank

end

end Erdos390.Full.PaperGuardCensus
