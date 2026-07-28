import Erdos390.Full.Scale
import Erdos390.WholePaper.BankBottomMarkerPoolScale
import Erdos390.WholePaper.GuardedBankSelection

/-!
# Concrete request demand for the eight bottom bank pools

The formal floating-rounding theorem produces the sharper floor-log error box
`4 * log_2(M) * log_p(M)`.  We reserve the paper's ceiling-log,
endpoint-free box at `3n`.  A request is an actual signed bank
slot together with one of the four bottom moves; its sign selects the fixed
orientation pool.  Thus every one of the eight pool fibers has exactly
`sum_{p <= floor(n^(2/9))} beta_p` requests.

The analytic count is also proved here.  Primes below `(3n)^(1/5)` are
bounded trivially; their contribution is `o(n^(2/9))`.  Above that cutoff,
`clog_p(3n) <= 5`, while the safe PNT gives `pi(y) = O(y / log y)`.  Since
`log y` is a fixed positive fraction of `log n`, the total demand is
`O(y)`, hence negligible compared with `n / (log n)^2`.
-/

open Filter Topology Asymptotics
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full.ArithmeticModel
open Erdos390.Full.Scale

noncomputable section

/-- The actual finite prime support of the rounding error box. -/
def bankRoundingPrimeSupport (n : ℕ) : Finset ℕ :=
  (yNat n + 1).primesBelow

/-- Common binary logarithmic degree, with the eventual endpoint already
majorized by `3n`. -/
def bankRoundingDepth (n : ℕ) : ℕ :=
  Nat.clog 2 (3 * n)

/-- Number of copies of each sign reserved at a supported prime.  Both
logarithmic factors are literal natural ceilings, as in the paper. -/
def bankRoundingBeta (n p : ℕ) : ℕ :=
  4 * bankRoundingDepth n * Nat.clog p (3 * n)

/-- The binary depth is exactly the natural ceiling used in the paper. -/
theorem bankRoundingDepth_eq_paperCeil (n : ℕ) :
    bankRoundingDepth n = ⌈Real.logb 2 (3 * n)⌉₊ := by
  rw [bankRoundingDepth,
    ← Real.natCeil_logb_natCast 2 (3 * n)]
  norm_num

/-- Literal identification of the reserved multiplicity with the paper's
product of two ceiling logarithms. -/
theorem bankRoundingBeta_eq_paperCeil (n p : ℕ) :
    bankRoundingBeta n p =
      4 * ⌈Real.logb 2 (3 * n)⌉₊ * ⌈Real.logb p (3 * n)⌉₊ := by
  rw [bankRoundingBeta, bankRoundingDepth,
    ← Real.natCeil_logb_natCast 2 (3 * n),
    ← Real.natCeil_logb_natCast p (3 * n)]
  norm_num

/-- The same copy count on the subtype used by `SignedBankSlot`. -/
def bankRoundingBetaOnSupport (n : ℕ) : ↑(bankRoundingPrimeSupport n) → ℕ :=
  fun p ↦ bankRoundingBeta n p.1

theorem bankRoundingPrimeSupport_prime
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) : p.Prime := by
  exact Nat.prime_of_mem_primesBelow hp

theorem bankRoundingPrimeSupport_le_yNat
    {n p : ℕ} (hp : p ∈ bankRoundingPrimeSupport n) : p ≤ yNat n := by
  exact Nat.lt_succ_iff.mp (Nat.lt_of_mem_primesBelow hp)

/-- The paper's ceiling-log box at `3n` majorizes the sharper formal
floating-rounding box used by `guarded_integral_exactification`. -/
theorem roundingErrorBox_le_bankRoundingBeta
    {n M p : ℕ} (hM : M ≤ 3 * n) :
    4 * Nat.log 2 M * Nat.log p M ≤ bankRoundingBeta n p := by
  have htwo : Nat.log 2 M ≤ Nat.clog 2 (3 * n) :=
    (Nat.log_le_clog 2 M).trans (Nat.clog_mono_right 2 hM)
  have hp : Nat.log p M ≤ Nat.clog p (3 * n) :=
    (Nat.log_le_clog p M).trans (Nat.clog_mono_right p hM)
  rw [bankRoundingBeta, bankRoundingDepth]
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 htwo) hp

/-- One concrete request is a signed prime-copy slot together with one of
the four bottom moves traversed by that signed path. -/
abbrev BankBottomPaperRequest (n : ℕ) :=
  SignedBankSlot (bankRoundingBetaOnSupport n) × BankBottomMove

/-- The sign of a reserved slot chooses one of the two midpoint halves. -/
def bankSignedSlotOrientation
    {P : Type*} {β : P → ℕ} (slot : SignedBankSlot β) :
    BankBottomOrientation :=
  match slot.2 with
  | .inl _copy => .downward
  | .inr _copy => .upward

/-- Literal routing of a path request to one of the eight pools. -/
def bankBottomPaperRequestPool (n : ℕ) :
    BankBottomPaperRequest n → BankBottomOrientationPool :=
  fun request ↦ (request.2, bankSignedSlotOrientation request.1)

/-- The actual finite family containing every signed-copy/move request. -/
def bankBottomPaperRequests (n : ℕ) : Finset (BankBottomPaperRequest n) :=
  Finset.univ

/-- Total demand in each fixed move/orientation fiber. -/
def bankBottomPaperDemand (n : ℕ) : ℕ :=
  ∑ p ∈ bankRoundingPrimeSupport n, bankRoundingBeta n p

private def bankBottomPaperRequestFiberEquiv
    (n : ℕ) (pool : BankBottomOrientationPool) :
    ↑(bankBottomRequestsInPool (bankBottomPaperRequests n)
        (bankBottomPaperRequestPool n) pool) ≃
      Σ p : ↑(bankRoundingPrimeSupport n),
        Fin (bankRoundingBetaOnSupport n p) where
  toFun request :=
    ⟨request.1.1.1, match request.1.1.2 with
      | .inl copy => copy
      | .inr copy => copy⟩
  invFun indexed :=
    ⟨(⟨indexed.1, match pool.2 with
        | .downward => Sum.inl indexed.2
        | .upward => Sum.inr indexed.2⟩, pool.1), by
      rcases pool with ⟨move, orientation⟩
      cases orientation <;>
      simp [bankBottomRequestsInPool, bankBottomPaperRequests,
        bankBottomPaperRequestPool, bankSignedSlotOrientation]⟩
  left_inv request := by
    rcases pool with ⟨poolMove, poolOrientation⟩
    rcases request with ⟨⟨⟨prime, signedCopy⟩, move⟩, hrequest⟩
    have hpool :
        (move, bankSignedSlotOrientation ⟨prime, signedCopy⟩) =
          (poolMove, poolOrientation) := by
      simpa only [bankBottomRequestsInPool, bankBottomPaperRequests,
        bankBottomPaperRequestPool, Finset.mem_filter, Finset.mem_univ,
        true_and] using hrequest
    cases signedCopy with
    | inl copy =>
        simp only [bankSignedSlotOrientation] at hpool
        cases hpool
        rfl
    | inr copy =>
        simp only [bankSignedSlotOrientation] at hpool
        cases hpool
        rfl
  right_inv indexed := by
    rcases pool with ⟨move, orientation⟩
    rcases indexed with ⟨prime, copy⟩
    cases orientation <;> rfl

/-- Every one of the eight actual request fibers has the same exact demand. -/
theorem bankBottomPaperPoolDemand_eq
    (n : ℕ) (pool : BankBottomOrientationPool) :
    bankBottomPoolDemand (bankBottomPaperRequests n)
        (bankBottomPaperRequestPool n) pool =
      bankBottomPaperDemand n := by
  rw [bankBottomPoolDemand]
  rw [← Fintype.card_coe]
  rw [Fintype.card_congr (bankBottomPaperRequestFiberEquiv n pool),
    Fintype.card_sigma]
  simp only [Fintype.card_fin, bankRoundingBetaOnSupport,
    bankBottomPaperDemand]
  simpa only using
    (Finset.sum_attach (bankRoundingPrimeSupport n)
      (fun p ↦ bankRoundingBeta n p))

/-- Fifth-root cutoff used only to count the small head of the beta sum. -/
def bankRoundingHeadCutoff (n : ℕ) : ℕ :=
  ⌊(3 * (n : ℝ)) ^ (1 / 5 : ℝ)⌋₊

/-- A convenient explicit natural majorant for the common pool demand. -/
def bankBottomPaperDemandMajorant (n : ℕ) : ℕ :=
  4 * bankRoundingDepth n * bankRoundingDepth n *
      (bankRoundingHeadCutoff n + 1) +
    20 * bankRoundingDepth n * Nat.primeCounting (yNat n)

private theorem bankRoundingBeta_le_head
    {n p : ℕ} (hp : p.Prime) :
    bankRoundingBeta n p ≤
      4 * bankRoundingDepth n * bankRoundingDepth n := by
  have hclog : Nat.clog p (3 * n) ≤ Nat.clog 2 (3 * n) :=
    Nat.clog_anti_left Nat.one_lt_two hp.two_le
  rw [bankRoundingBeta, bankRoundingDepth]
  exact Nat.mul_le_mul_left (4 * Nat.clog 2 (3 * n)) hclog

private theorem bankRoundingBeta_le_tail
    {n p : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hcut : bankRoundingHeadCutoff n < p) :
    bankRoundingBeta n p ≤ 20 * bankRoundingDepth n := by
  let root : ℝ := (3 * (n : ℝ)) ^ (1 / 5 : ℝ)
  have hrootPos : 0 < root := by
    dsimp [root]
    positivity
  have hrootLt : root < (p : ℝ) := by
    have hfloor : root < (bankRoundingHeadCutoff n : ℝ) + 1 := by
      simpa only [root, bankRoundingHeadCutoff] using
        (Nat.lt_floor_add_one root)
    have hsucc : bankRoundingHeadCutoff n + 1 ≤ p := by omega
    have hsuccR : (bankRoundingHeadCutoff n : ℝ) + 1 ≤ (p : ℝ) := by
      exact_mod_cast hsucc
    exact hfloor.trans_le hsuccR
  have hrootPow : root ^ (5 : ℕ) = 3 * (n : ℝ) := by
    dsimp [root]
    calc
      ((3 * (n : ℝ)) ^ (1 / 5 : ℝ)) ^ (5 : ℕ) =
          (3 * (n : ℝ)) ^ ((1 / 5 : ℝ) * (5 : ℕ)) :=
        (Real.rpow_mul_natCast (by positivity) _ _).symm
      _ = 3 * (n : ℝ) := by norm_num [Real.rpow_one]
  have hpowR : 3 * (n : ℝ) < (p : ℝ) ^ (5 : ℕ) := by
    rw [← hrootPow]
    exact pow_lt_pow_left₀ hrootLt hrootPos.le (by omega)
  have hpow : 3 * n < p ^ 5 := by exact_mod_cast hpowR
  have hclog : Nat.clog p (3 * n) ≤ 5 :=
    (Nat.clog_le_iff_le_pow hp.one_lt).2 hpow.le
  calc
    bankRoundingBeta n p =
        4 * bankRoundingDepth n * Nat.clog p (3 * n) := rfl
    _ ≤ 4 * bankRoundingDepth n * 5 :=
      Nat.mul_le_mul_left _ hclog
    _ = 20 * bankRoundingDepth n := by ring

/-- Exact finite beta-sum estimate underlying the asymptotic demand bound. -/
theorem bankBottomPaperDemand_le_majorant (n : ℕ) :
    bankBottomPaperDemand n ≤ bankBottomPaperDemandMajorant n := by
  classical
  let P := bankRoundingPrimeSupport n
  let head := P.filter (fun p ↦ p ≤ bankRoundingHeadCutoff n)
  let tail := P.filter (fun p ↦ ¬p ≤ bankRoundingHeadCutoff n)
  have hsplit :
      (∑ p ∈ P, bankRoundingBeta n p) =
        (∑ p ∈ head, bankRoundingBeta n p) +
          ∑ p ∈ tail, bankRoundingBeta n p := by
    simpa only [head, tail] using
      (P.sum_filter_add_sum_filter_not
        (fun p ↦ p ≤ bankRoundingHeadCutoff n)
        (fun p ↦ bankRoundingBeta n p)).symm
  have hheadPoint : ∀ p ∈ head,
      bankRoundingBeta n p ≤
        4 * bankRoundingDepth n * bankRoundingDepth n := by
    intro p hp
    exact bankRoundingBeta_le_head
      (bankRoundingPrimeSupport_prime (Finset.mem_filter.mp hp).1)
  have hheadCard : head.card ≤ bankRoundingHeadCutoff n + 1 := by
    have hsubset : head ⊆ Finset.range (bankRoundingHeadCutoff n + 1) := by
      intro p hp
      exact Finset.mem_range.mpr
        (Nat.lt_succ_of_le (Finset.mem_filter.mp hp).2)
    simpa using Finset.card_le_card hsubset
  have hhead :
      (∑ p ∈ head, bankRoundingBeta n p) ≤
        (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) := by
    calc
      (∑ p ∈ head, bankRoundingBeta n p) ≤
          head.card *
            (4 * bankRoundingDepth n * bankRoundingDepth n) := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul head (fun p ↦ bankRoundingBeta n p)
            (4 * bankRoundingDepth n * bankRoundingDepth n) hheadPoint
      _ ≤ (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) :=
        Nat.mul_le_mul_right _ hheadCard
  have htailPoint : ∀ p ∈ tail,
      bankRoundingBeta n p ≤ 20 * bankRoundingDepth n := by
    intro p hp
    by_cases hn : n = 0
    · subst n
      simp [bankRoundingBeta, bankRoundingDepth]
    · apply bankRoundingBeta_le_tail (Nat.pos_of_ne_zero hn)
        (bankRoundingPrimeSupport_prime (Finset.mem_filter.mp hp).1)
      exact Nat.lt_of_not_ge (Finset.mem_filter.mp hp).2
  have hPcard : P.card = Nat.primeCounting (yNat n) := by
    simpa only [P, bankRoundingPrimeSupport, Nat.primeCounting] using
      Nat.primesBelow_card_eq_primeCounting' (yNat n + 1)
  have htailCard : tail.card ≤ Nat.primeCounting (yNat n) := by
    rw [← hPcard]
    exact Finset.card_filter_le _ _
  have htail :
      (∑ p ∈ tail, bankRoundingBeta n p) ≤
        Nat.primeCounting (yNat n) * (20 * bankRoundingDepth n) := by
    calc
      (∑ p ∈ tail, bankRoundingBeta n p) ≤
          tail.card * (20 * bankRoundingDepth n) := by
        simpa only [nsmul_eq_mul] using
          Finset.sum_le_card_nsmul tail (fun p ↦ bankRoundingBeta n p)
            (20 * bankRoundingDepth n) htailPoint
      _ ≤ Nat.primeCounting (yNat n) *
          (20 * bankRoundingDepth n) :=
        Nat.mul_le_mul_right _ htailCard
  rw [bankBottomPaperDemand, bankBottomPaperDemandMajorant]
  change (∑ p ∈ P, bankRoundingBeta n p) ≤ _
  rw [hsplit]
  calc
    (∑ p ∈ head, bankRoundingBeta n p) +
        ∑ p ∈ tail, bankRoundingBeta n p ≤
      (bankRoundingHeadCutoff n + 1) *
          (4 * bankRoundingDepth n * bankRoundingDepth n) +
        Nat.primeCounting (yNat n) *
          (20 * bankRoundingDepth n) := Nat.add_le_add hhead htail
    _ = 4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) +
        20 * bankRoundingDepth n * Nat.primeCounting (yNat n) := by ring

private theorem yNat_tendsto_atTop : Tendsto yNat atTop atTop := by
  have hy : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  exact tendsto_nat_floor_atTop.comp hy

private theorem eventually_y_half_le_yNat :
    ∀ᶠ n : ℕ in atTop, y n / 2 ≤ (yNat n : ℝ) := by
  have hyTop : Tendsto (fun n : ℕ ↦ y n) atTop atTop := by
    simpa [y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  filter_upwards [hyTop.eventually (eventually_ge_atTop (2 : ℝ))] with n hyn
  have hfloor : y n < (yNat n : ℝ) + 1 := Nat.lt_floor_add_one _
  linarith

private theorem bankRoundingDepth_le_two_mul_log2
    {n : ℕ} (hn : 0 < n) :
    bankRoundingDepth n ≤ 2 * Nat.log2 (3 * n) := by
  have hX : 3 * n ≠ 0 := by omega
  have hone : 1 ≤ Nat.log 2 (3 * n) :=
    (Nat.le_log_iff_pow_le Nat.one_lt_two hX).2 (by
      simpa only [pow_one] using (show 2 ≤ 3 * n by omega))
  have hceil : Nat.clog 2 (3 * n) ≤ (Nat.log 2 (3 * n)).succ :=
    Nat.clog_le_of_le_pow
      (Nat.lt_pow_succ_log_self Nat.one_lt_two (3 * n)).le
  rw [bankRoundingDepth, Nat.log2_eq_log_two]
  omega

private theorem bankRoundingDepth_cast_le_two_logb
    {n : ℕ} (hn : 0 < n) :
    (bankRoundingDepth n : ℝ) ≤
      2 * (Real.log (3 * (n : ℝ)) / Real.log 2) := by
  have hnat := bankRoundingDepth_le_two_mul_log2 hn
  have hcast : (bankRoundingDepth n : ℝ) ≤
      2 * (Nat.log2 (3 * n) : ℝ) := by exact_mod_cast hnat
  have hfloor : (Nat.log2 (3 * n) : ℝ) ≤
      Real.logb 2 ((3 * n : ℕ) : ℝ) := Real.log2_le_logb (3 * n)
  calc
    (bankRoundingDepth n : ℝ) ≤ 2 * (Nat.log2 (3 * n) : ℝ) := hcast
    _ ≤ 2 * Real.logb 2 ((3 * n : ℕ) : ℝ) := by gcongr
    _ = 2 * (Real.log (3 * (n : ℝ)) / Real.log 2) := by
      norm_num [Real.logb]

private theorem bankRoundingDepth_isBigO_log_natCast :
    (fun n : ℕ ↦ (bankRoundingDepth n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (n : ℝ)) := by
  apply IsBigO.of_bound (4 / Real.log 2)
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogn : 0 ≤ Real.log (n : ℝ) :=
    (Real.log_pos (by exact_mod_cast (show 1 < n by omega))).le
  have hlogThree : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogMul : Real.log (3 * (n : ℝ)) =
      Real.log 3 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) hnPos.ne'
  have hdepth := bankRoundingDepth_cast_le_two_logb
    (show 0 < n by omega)
  rw [hlogMul] at hdepth
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ bankRoundingDepth n),
    Real.norm_eq_abs, abs_of_nonneg hlogn]
  have hsum : Real.log 3 + Real.log (n : ℝ) ≤
      2 * Real.log (n : ℝ) := by linarith
  calc
    (bankRoundingDepth n : ℝ) ≤
        2 * ((Real.log 3 + Real.log (n : ℝ)) / Real.log 2) := hdepth
    _ ≤ 2 * ((2 * Real.log (n : ℝ)) / Real.log 2) := by
      exact mul_le_mul_of_nonneg_left
        ((div_le_div_iff_of_pos_right hlogTwo).2 hsum) (by norm_num)
    _ = (4 / Real.log 2) * Real.log (n : ℝ) := by ring

private theorem bankRoundingDepth_isBigO_log_yNat :
    (fun n : ℕ ↦ (bankRoundingDepth n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ Real.log (yNat n : ℝ)) := by
  apply IsBigO.of_bound (20 / Real.log 2)
  filter_upwards [eventually_ge_atTop 3,
      Erdos390.Full.FriableAsymptotic.eventually_one_fifth_L_le_log_yNat]
      with n hn hyLog
  have hnPos : (0 : ℝ) < n := by positivity
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogY : 0 < Real.log (yNat n : ℝ) := by
    have : 0 < (1 / 5 : ℝ) * L n := mul_pos (by norm_num) (by simpa [L])
    exact this.trans_le hyLog
  have hlogThree : Real.log 3 ≤ Real.log (n : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hlogMul : Real.log (3 * (n : ℝ)) =
      Real.log 3 + Real.log (n : ℝ) :=
    Real.log_mul (by norm_num) hnPos.ne'
  have hdepth := bankRoundingDepth_cast_le_two_logb
    (show 0 < n by omega)
  rw [hlogMul] at hdepth
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hLn : L n ≤ 5 * Real.log (yNat n : ℝ) := by linarith
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      (0 : ℝ) ≤ bankRoundingDepth n),
    Real.norm_eq_abs, abs_of_nonneg hlogY.le]
  have hsum : Real.log 3 + Real.log (n : ℝ) ≤
      2 * Real.log (n : ℝ) := by linarith
  have hbase : (bankRoundingDepth n : ℝ) ≤
      (4 / Real.log 2) * L n := by
    calc
      (bankRoundingDepth n : ℝ) ≤
          2 * ((Real.log 3 + Real.log (n : ℝ)) / Real.log 2) := hdepth
      _ ≤ 2 * ((2 * Real.log (n : ℝ)) / Real.log 2) := by
        exact mul_le_mul_of_nonneg_left
          ((div_le_div_iff_of_pos_right hlogTwo).2 hsum) (by norm_num)
      _ = (4 / Real.log 2) * L n := by
        rw [L]
        ring
  calc
    (bankRoundingDepth n : ℝ) ≤
        (4 / Real.log 2) * L n := hbase
    _ ≤ (4 / Real.log 2) * (5 * Real.log (yNat n : ℝ)) :=
      mul_le_mul_of_nonneg_left hLn (by positivity)
    _ = (20 / Real.log 2) * Real.log (yNat n : ℝ) := by ring

private theorem bankRoundingHeadMajorant_isLittleO_yNat :
    (fun n : ℕ ↦
      ((4 * bankRoundingDepth n * bankRoundingDepth n *
        (bankRoundingHeadCutoff n + 1) : ℕ) : ℝ)) =o[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ)) := by
  let headModel : ℕ → ℝ := fun n ↦
    (3 * (n : ℝ)) ^ (1 / 5 : ℝ) * Real.log (3 * (n : ℝ)) ^ 2
  have hheadO :
      (fun n : ℕ ↦
        ((4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) : ℕ) : ℝ)) =O[atTop]
        headModel := by
    apply IsBigO.of_bound (32 / Real.log 2 ^ 2)
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hroot : 1 ≤ (3 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Real.one_le_rpow
        (by exact_mod_cast (show 1 ≤ 3 * n by omega)) (by norm_num)
    have hcutCast : (bankRoundingHeadCutoff n : ℝ) ≤
        (3 * (n : ℝ)) ^ (1 / 5 : ℝ) :=
      Nat.floor_le (Real.rpow_nonneg (by positivity) _)
    have hcut : (bankRoundingHeadCutoff n : ℝ) + 1 ≤
        2 * (3 * (n : ℝ)) ^ (1 / 5 : ℝ) := by linarith
    have hdepth := bankRoundingDepth_cast_le_two_logb hn
    have hlogNonneg : 0 ≤ Real.log (3 * (n : ℝ)) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * n by omega))
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ (4 * bankRoundingDepth n * bankRoundingDepth n *
          (bankRoundingHeadCutoff n + 1) : ℕ)),
      Real.norm_eq_abs, abs_of_nonneg (by
        exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (sq_nonneg _))]
    push_cast
    calc
      (4 : ℝ) * bankRoundingDepth n * bankRoundingDepth n *
          ((bankRoundingHeadCutoff n : ℝ) + 1) ≤
        4 * (2 * (Real.log (3 * (n : ℝ)) / Real.log 2)) *
          (2 * (Real.log (3 * (n : ℝ)) / Real.log 2)) *
            (2 * (3 * (n : ℝ)) ^ (1 / 5 : ℝ)) := by gcongr
      _ = (32 / Real.log 2 ^ 2) * headModel n := by
        dsimp [headModel]
        ring
  have hreal0 :
      (fun x : ℝ ↦ Real.log x ^ (2 : ℕ) * x ^ (1 / 5 : ℝ)) =o[atTop]
        (fun x : ℝ ↦ x ^ (1 / 45 : ℝ) * x ^ (1 / 5 : ℝ)) := by
    simpa only [Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < 1 / 45)).mul_isBigO
          (isBigO_refl (fun x : ℝ ↦ x ^ (1 / 5 : ℝ)) atTop)
  have hreal :
      (fun x : ℝ ↦ x ^ (1 / 5 : ℝ) * Real.log x ^ 2) =o[atTop]
        (fun x : ℝ ↦ x ^ (2 / 9 : ℝ)) := by
    apply hreal0.congr'
    · exact Eventually.of_forall fun x ↦ by
        change Real.log x ^ (2 : ℕ) * x ^ (1 / 5 : ℝ) =
          x ^ (1 / 5 : ℝ) * Real.log x ^ (2 : ℕ)
        exact mul_comm (Real.log x ^ (2 : ℕ)) (x ^ (1 / 5 : ℝ))
    · filter_upwards [eventually_gt_atTop 0] with x hx
      rw [← Real.rpow_add hx]
      norm_num
  have hthreeTop : Tendsto (fun n : ℕ ↦ 3 * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hmodel : headModel =o[atTop]
      (fun n : ℕ ↦ (3 * (n : ℝ)) ^ (2 / 9 : ℝ)) := by
    simpa only [headModel] using hreal.comp_tendsto hthreeTop
  have hscaledY :
      (fun n : ℕ ↦ (3 * (n : ℝ)) ^ (2 / 9 : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    apply IsBigO.of_bound (2 * 3 ^ (2 / 9 : ℝ))
    filter_upwards [eventually_y_half_le_yNat,
        eventually_gt_atTop 0] with n hyFloor hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hthree :
        (3 * (n : ℝ)) ^ (2 / 9 : ℝ) =
          3 ^ (2 / 9 : ℝ) * y n := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hnR.le]
      rfl
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _),
      Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ yNat n),
      hthree]
    have hyScaled : y n ≤ 2 * (yNat n : ℝ) := by linarith
    calc
      3 ^ (2 / 9 : ℝ) * y n ≤
          3 ^ (2 / 9 : ℝ) * (2 * (yNat n : ℝ)) :=
        mul_le_mul_of_nonneg_left hyScaled
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
      _ = (2 * 3 ^ (2 / 9 : ℝ)) * (yNat n : ℝ) := by ring
  exact (hheadO.trans_isLittleO hmodel).trans_isBigO hscaledY

private theorem bankRoundingTailMajorant_isBigO_yNat :
    (fun n : ℕ ↦
      ((20 * bankRoundingDepth n * Nat.primeCounting (yNat n) : ℕ) : ℝ))
      =O[atTop] (fun n : ℕ ↦ (yNat n : ℝ)) := by
  have hpnt0 :=
    SafePrimeCounting.primeCounting_nat_isEquivalent.comp_tendsto
      yNat_tendsto_atTop
  have hpnt :
      (fun n : ℕ ↦ (Nat.primeCounting (yNat n) : ℝ)) =O[atTop]
        (fun n : ℕ ↦
          (yNat n : ℝ) / Real.log (yNat n : ℝ)) := by
    simpa only [Function.comp_apply] using hpnt0.isBigO
  have hmul := bankRoundingDepth_isBigO_log_yNat.mul hpnt
  have hcore :
      (fun n : ℕ ↦
        (bankRoundingDepth n : ℝ) * Nat.primeCounting (yNat n)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    apply hmul.congr' (Eventually.of_forall fun _n ↦ rfl)
    filter_upwards [yNat_tendsto_atTop.eventually (eventually_gt_atTop 1)]
        with n hY
    have hlog : Real.log (yNat n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hY)).ne'
    field_simp
  have h20 := hcore.const_mul_left (20 : ℝ)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using h20

/-- The exact common request demand is `O(floor(n^(2/9)))`. -/
theorem bankBottomPaperDemand_isBigO_yNat :
    (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ (yNat n : ℝ)) := by
  have hmajorantPoint :
      (fun n : ℕ ↦ (bankBottomPaperDemand n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (bankBottomPaperDemandMajorant n : ℝ)) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemand n),
      Real.norm_eq_abs, abs_of_nonneg (by positivity :
        (0 : ℝ) ≤ bankBottomPaperDemandMajorant n), one_mul]
    exact_mod_cast bankBottomPaperDemand_le_majorant n
  have hmajorant :
      (fun n : ℕ ↦ (bankBottomPaperDemandMajorant n : ℝ)) =O[atTop]
        (fun n : ℕ ↦ (yNat n : ℝ)) := by
    have hadd := (bankRoundingHeadMajorant_isLittleO_yNat.isBigO).add
      bankRoundingTailMajorant_isBigO_yNat
    apply hadd.congr'
    · exact Eventually.of_forall fun n ↦ by
        unfold bankBottomPaperDemandMajorant
        push_cast
        ring
    · exact Eventually.of_forall fun _n ↦ rfl
  exact hmajorantPoint.trans hmajorant

private theorem yNat_isLittleO_bankBottomPrimeScale :
    (fun n : ℕ ↦ (yNat n : ℝ)) =o[atTop] bankBottomPrimeScale := by
  have hY : (fun n : ℕ ↦ (yNat n : ℝ)) =O[atTop]
      (fun n : ℕ ↦ y n) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with n
    have hyNonneg : 0 ≤ y n := Real.rpow_nonneg (by positivity) _
    have hfloor : (yNat n : ℝ) ≤ y n := Nat.floor_le hyNonneg
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ yNat n),
      Real.norm_eq_abs, abs_of_nonneg hyNonneg, one_mul]
    exact hfloor
  have hratio0 : Tendsto
      (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 /
        (n : ℝ) ^ (7 / 9 : ℝ)) atTop (nhds 0) := by
    simpa only [Function.comp_apply, Real.rpow_two] using
      (isLittleO_log_rpow_rpow_atTop 2
        (by norm_num : (0 : ℝ) < 7 / 9)).tendsto_div_nhds_zero.comp
          tendsto_natCast_atTop_atTop
  have hyRatio : Tendsto
      (fun n : ℕ ↦ y n / bankBottomPrimeScale n)
      atTop (nhds 0) := by
    apply hratio0.congr'
    filter_upwards [eventually_gt_atTop 1] with n hn
    have hnR : 0 < (n : ℝ) := by positivity
    have hn0 : (n : ℝ) ≠ 0 := hnR.ne'
    have hlog : Real.log (n : ℝ) ≠ 0 :=
      (Real.log_pos (by exact_mod_cast hn)).ne'
    have hpow :
        (n : ℝ) ^ (2 / 9 : ℝ) * (n : ℝ) ^ (7 / 9 : ℝ) =
          (n : ℝ) := by
      rw [← Real.rpow_add hnR]
      norm_num [Real.rpow_one]
    rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale,
      secondOrderScale, y]
    field_simp
    nlinarith
  have hyLittle : (fun n : ℕ ↦ y n) =o[atTop]
      bankBottomPrimeScale := by
    apply (isLittleO_iff_tendsto' ?_).mpr hyRatio
    filter_upwards [eventually_gt_atTop 1] with n hn hzero
    have hscale : 0 < bankBottomPrimeScale n := by
      rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale]
      exact div_pos (secondOrderScale_pos (by omega))
        (Real.log_pos (by exact_mod_cast hn))
    exact (hscale.ne' hzero).elim
  exact hY.trans_isLittleO hyLittle

/-- Consequently every concrete orientation demand is negligible on the
finer bottom-prime scale. -/
theorem bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        (bankBottomPaperDemand n : ℝ) / bankBottomPrimeScale n)
      atTop (nhds 0) :=
  (bankBottomPaperDemand_isBigO_yNat.trans_isLittleO
    yNat_isLittleO_bankBottomPrimeScale).tendsto_div_nhds_zero

/-- For every one of the eight pools, its concrete paper demand eventually
fits into its actual prime-marker capacity. -/
theorem eventually_bankBottomPaper_poolDemand_le_capacity
    {c : ℝ} (hc : 0 < c) (pool : BankBottomOrientationPool) :
    ∀ᶠ n : ℕ in atTop,
      bankBottomPoolDemand (bankBottomPaperRequests n)
          (bankBottomPaperRequestPool n) pool ≤
        bankBottomPoolCapacity
          (fun pool' ↦ bankBottomOrientedMarkerPrimes n
            (upperEndpoint n (upperTailLength c n)) pool') pool := by
  have hdemand := bankBottomPaperDemand_div_bankBottomPrimeScale_tendsto_zero
  have hsupply :=
    bankBottomOrientedMarkerPrimes_card_div_bankBottomPrimeScale_tendsto
      hc pool
  have hconstant := bankBottomOrientedPrimeConstant_pos hc pool
  have hdemandSmall := hdemand.eventually
    (eventually_lt_nhds (half_pos hconstant))
  have hsupplyLarge := hsupply.eventually
    (eventually_gt_nhds (half_lt_self hconstant))
  filter_upwards [hdemandSmall, hsupplyLarge,
      eventually_gt_atTop 1] with n hdemandN hsupplyN hn
  rw [bankBottomPaperPoolDemand_eq]
  unfold bankBottomPoolCapacity
  have hscale : 0 < bankBottomPrimeScale n := by
    rw [bankBottomPrimeScale, SafePrimeCounting.shortIntervalPrimeScale]
    exact div_pos (secondOrderScale_pos (by omega))
      (Real.log_pos (by exact_mod_cast hn))
  have hratio :
      (bankBottomPaperDemand n : ℝ) / bankBottomPrimeScale n <
        ((bankBottomOrientedMarkerPrimes n
          (upperEndpoint n (upperTailLength c n)) pool).card : ℝ) /
            bankBottomPrimeScale n := hdemandN.trans hsupplyN
  have hcast : (bankBottomPaperDemand n : ℝ) <
      ((bankBottomOrientedMarkerPrimes n
        (upperEndpoint n (upperTailLength c n)) pool).card : ℝ) :=
    (div_lt_div_iff_of_pos_right hscale).mp hratio
  exact_mod_cast hcast.le

/-- All eight capacity inequalities hold simultaneously. -/
theorem eventually_bankBottomPaper_all_poolDemands_le_capacity
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ pool : BankBottomOrientationPool,
      bankBottomPoolDemand (bankBottomPaperRequests n)
          (bankBottomPaperRequestPool n) pool ≤
        bankBottomPoolCapacity
          (fun pool' ↦ bankBottomOrientedMarkerPrimes n
            (upperEndpoint n (upperTailLength c n)) pool') pool := by
  rw [Filter.eventually_all]
  exact fun pool ↦ eventually_bankBottomPaper_poolDemand_le_capacity hc pool

/-- Terminal concrete allocation: eventually all signed-copy/move requests
receive globally distinct actual prime markers in their prescribed pools. -/
theorem eventually_exists_bankBottomPaper_injective_assignment
    {c : ℝ} (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop,
      ∃ matching : BankBottomPoolMatching
          (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
          (fun pool ↦ bankBottomOrientedMarkerPrimes n
            (upperEndpoint n (upperTailLength c n)) pool),
        Function.Injective matching.matchedSlot ∧
          ∀ request : ↑(bankBottomPaperRequests n),
            matching.matchedSlot request ∈
              bankBottomOrientedMarkerPrimes n
                (upperEndpoint n (upperTailLength c n))
                (bankBottomPaperRequestPool n request.1) := by
  filter_upwards [eventually_bankBottomPaper_all_poolDemands_le_capacity hc,
      eventually_bankBottom_scaledEndpoint_narrow hc] with n hcapacity hnarrow
  exact exists_bankBottomPool_injective_assignment
    (bankBottomPaperRequests n) (bankBottomPaperRequestPool n)
    (fun pool ↦ bankBottomOrientedMarkerPrimes n
      (upperEndpoint n (upperTailLength c n)) pool)
    hcapacity
    (fun {_pool _pool'} hpools ↦
      bankBottomOrientedMarkerPrimes_disjoint
        (two_mul_le_upperEndpoint n (upperTailLength c n)) hnarrow hpools)

end

end Erdos390.WholePaper
