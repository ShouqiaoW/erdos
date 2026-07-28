import Erdos390.WholePaper.BankPaperCanonicalP87OrdinaryLogCompatibilityConnector
import Erdos390.WholePaper.BankPaperCanonicalSmoothQuotaHeightAsymptotic

/-!
# Target envelopes with an approximate ordinary-log ledger

The exact ordinary-log hypothesis in the first P87 target-envelope connector
is stronger than the finite compensated estimate actually needs.  If

`Elog = sum_p t_p r_p`,

then the exact algebra is

`sum_j alpha_j Delta_j =
    sum_p (alpha_{j(p)} - t_p) r_p + Elog`.

Thus an error of size

`|Elog| <= (q / L) * Cordinary * w`

is absorbed by enlarging the target constant from `7 * Cinitial` to
`7 * Cinitial + Cordinary`.

The second part of this file records why nearest-integer height centering is
compatible with that weaker interface.  Its normalized residual is eventually
bounded by the absolute constant `9 / 2`, while a paper-scale active mass
satisfies `q / L -> infinity`.  Hence every fixed mesh width absorbs the
rounding residual with `Cordinary = 1`.

What is deliberately not asserted here is the source-specific identification
of the weighted selector residual with the normalized height-centering
residual.  That is a finite ledger identity about the chosen physical split,
not a consequence of nearest-integer rounding alone.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.WholePaper

open Erdos390.Full
open Erdos390.Full.ArithmeticModel
open Erdos390.Full.ArithmeticBandGeometry
open Erdos390.Full.PaperBridgeFit
open Erdos390.Full.PaperGuardCensus
open Erdos390.Full.Scale

noncomputable section

/-! ## Approximate ordinary-log compatibility -/

/-- Quantitative replacement for exact ordinary-log compatibility.  The
parameter `E` is an absolute normalized logarithmic error, not a relative
error. -/
def BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (E : Real) : Prop :=
  abs (∑ p : BankPaperCanonicalTangentPrime n W,
      tPrime n p.1 *
        bankPaperCanonicalTangentResidual
          R certificate fixed candidates selector p) <= E

/-- Exact compatibility implies approximate compatibility at every
nonnegative error threshold. -/
theorem
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo.of_exact
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    {E : Real} (hE : 0 <= E)
    (hordinary : BankPaperCanonicalSelectorOrdinaryLogCompatible
      (W := W) R certificate fixed candidates selector) :
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
      (W := W) R certificate fixed candidates selector E := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatible at hordinary
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
  rw [hordinary, abs_zero]
  exact hE

/-- The P87 prime-log invariant propagates a quantitative compatibility
bound exactly as it propagates the zero-error special case. -/
theorem
    bankPaperCanonicalActualP87EndpointSelector_ordinaryLogCompatibleUpTo
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (path : Real -> B.ParamSpace)
    (hprimeLog :
      B.paperMoment B.primeLogScore (path 1) =
        B.paperMoment B.primeLogScore 0)
    (E : Real)
    (hinitial :
      BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
        (W := B.sampleData.W)
        R certificate fixed candidates preSelector E) :
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
      (W := B.sampleData.W) R certificate fixed candidates
        (bankPaperCanonicalActualP87EndpointSelector
          B candidates preSelector activeSeed path) E := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo at hinitial ⊢
  rw [
    bankPaperCanonicalActualP87EndpointSelector_weightedResidual_eq_initial
      B R certificate fixed candidates preSelector activeSeed
        Hmeasure hseed path hprimeLog]
  exact hinitial

/-! ## Finite compensated algebra with a visible defect -/

/-- Without setting the ordinary-log defect to zero, the band-center sum is
the prime-deviation sum plus that defect. -/
theorem
    bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual_add_ordinaryDefect
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p) :
    (∑ j : Band, B.bandCenter j * Delta j) =
      (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        B.primeDeviation p * residual p) +
      ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p := by
  have hcenter :
      (∑ j : Band, B.bandCenter j * Delta j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := by
    calc
      (∑ j : Band, B.bandCenter j * Delta j) =
          ∑ j : Band, B.bandCenter j *
            (∑ p ∈ B.partition.data.fiber j, residual p) := by
        apply Finset.sum_congr rfl
        intro j _hj
        rw [hDelta j]
      _ = ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := by
        rw [← Finset.sum_fiberwise Finset.univ B.partition.band
          (fun p : BandPrime B.sampleData.n B.sampleData.W =>
            B.bandCenter (B.partition.band p) * residual p)]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        have hpj : B.partition.band p = j :=
          (Erdos390.Lemma84.WeightedBandData.mem_fiber_iff
            B.partition.data).mp hp
        rw [hpj]
  calc
    (∑ j : Band, B.bandCenter j * Delta j) =
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.bandCenter (B.partition.band p) * residual p := hcenter
    _ = ∑ p : BandPrime B.sampleData.n B.sampleData.W,
        (B.primeDeviation p * residual p +
          tPrime B.sampleData.n p.1 * residual p) := by
      apply Finset.sum_congr rfl
      intro p _hp
      unfold BridgeData.primeDeviation
      ring
    _ =
        (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation p * residual p) +
        ∑ p : BandPrime B.sampleData.n B.sampleData.W,
          tPrime B.sampleData.n p.1 * residual p := by
      rw [Finset.sum_add_distrib]

/-- Pointwise residual control, the literal prime-deviation `L¹` estimate,
and a scaled ordinary-log defect imply the target envelopes.  The only cost
of replacing exact compatibility is the additive constant `Cordinary`. -/
theorem
    bankPaperCanonicalHasTargetEnvelopes_seven_add_of_primeResidual
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    (Delta : Band -> Real)
    (residual : BandPrime B.sampleData.n B.sampleData.W -> Real)
    (Cinitial Cordinary : Real)
    (hCinitial : 0 <= Cinitial) (hCordinary : 0 <= Cordinary)
    (hDelta : forall j,
      Delta j =
        ∑ p ∈ B.partition.data.fiber j, residual p)
    (hpointwise : forall p,
      abs (residual p) <=
        Cinitial * B.q / ((p.1 : Real) * B.L))
    (hordinary :
      abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) <=
        (B.q / B.L) * Cordinary * B.w)
    (hdeviation : B.primeDeviationL1 <= 7 * B.w) :
    B.HasTargetEnvelopes (7 * Cinitial + Cordinary) Delta := by
  have hqL : 0 <= B.q / B.L :=
    (div_pos B.q_pos B.L_pos).le
  have hCtarget :
      Cinitial <= 7 * Cinitial + Cordinary := by
    linarith
  constructor
  · intro j
    have hrateSum :
        (∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L)) =
            (B.q / B.L) * Cinitial * B.harmonicMass j := by
      unfold BridgeData.harmonicMass
      change
        (∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L)) =
            (B.q / B.L) * Cinitial *
              (∑ p ∈ B.partition.data.fiber j,
                1 / (p.1 : Real))
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hpPos : (0 : Real) < (p.1 : Real) := by
        exact_mod_cast (prime_of_mem_primeBand p.2).pos
      field_simp [ne_of_gt hpPos, ne_of_gt B.L_pos]
    calc
      abs (Delta j) =
          abs (∑ p ∈ B.partition.data.fiber j, residual p) := by
        rw [hDelta j]
      _ <= ∑ p ∈ B.partition.data.fiber j, abs (residual p) :=
        Finset.abs_sum_le_sum_abs _ _
      _ <= ∑ p ∈ B.partition.data.fiber j,
          Cinitial * B.q / ((p.1 : Real) * B.L) := by
        exact Finset.sum_le_sum fun p _hp => hpointwise p
      _ = (B.q / B.L) * Cinitial * B.harmonicMass j :=
        hrateSum
      _ = (B.q / B.L) * Cinitial * abs (B.harmonicMass j) := by
        rw [abs_of_pos (B.harmonicMass_pos j)]
      _ <= (B.q / B.L) * (7 * Cinitial + Cordinary) *
          abs (B.harmonicMass j) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hCtarget hqL) (abs_nonneg _)
  · rw [
      bankPaperCanonicalBandCenterResidual_eq_primeDeviationResidual_add_ordinaryDefect
        B Delta residual hDelta]
    have hweightedRate :
        (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          abs (B.primeDeviation p) *
            (Cinitial * B.q / ((p.1 : Real) * B.L))) =
          (B.q / B.L) * Cinitial * B.primeDeviationL1 := by
      unfold BridgeData.primeDeviationL1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      have hpPos : (0 : Real) < (p.1 : Real) := by
        exact_mod_cast (prime_of_mem_primeBand p.2).pos
      field_simp [ne_of_gt hpPos, ne_of_gt B.L_pos]
    have hfactor : 0 <= (B.q / B.L) * Cinitial :=
      mul_nonneg hqL hCinitial
    have hprimeDeviation :
        abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation p * residual p) <=
            (B.q / B.L) * (7 * Cinitial) * B.w := by
      calc
        abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation p * residual p) <=
            ∑ p : BandPrime B.sampleData.n B.sampleData.W,
              abs (B.primeDeviation p * residual p) :=
          Finset.abs_sum_le_sum_abs _ _
        _ <= ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            abs (B.primeDeviation p) *
              (Cinitial * B.q / ((p.1 : Real) * B.L)) := by
          apply Finset.sum_le_sum
          intro p _hp
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left
            (hpointwise p) (abs_nonneg _)
        _ = (B.q / B.L) * Cinitial * B.primeDeviationL1 :=
          hweightedRate
        _ <= (B.q / B.L) * Cinitial * (7 * B.w) :=
          mul_le_mul_of_nonneg_left hdeviation hfactor
        _ = (B.q / B.L) * (7 * Cinitial) * B.w := by
          ring
    calc
      abs ((∑ p : BandPrime B.sampleData.n B.sampleData.W,
          B.primeDeviation p * residual p) +
          ∑ p : BandPrime B.sampleData.n B.sampleData.W,
            tPrime B.sampleData.n p.1 * residual p) <=
          abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
            B.primeDeviation p * residual p) +
          abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
            tPrime B.sampleData.n p.1 * residual p) :=
        abs_add_le _ _
      _ <= (B.q / B.L) * (7 * Cinitial) * B.w +
          (B.q / B.L) * Cordinary * B.w :=
        add_le_add hprimeDeviation hordinary
      _ = (B.q / B.L) * (7 * Cinitial + Cordinary) * B.w := by
        ring

/-! ## Literal initial-selector specialization -/

/-- The actual initial marked-band target has the enlarged target envelopes
under quantitative, rather than exact, ordinary-log compatibility. -/
theorem
    bankPaperCanonicalActualInitialHasTargetEnvelopes_of_selectorDeficit_of_approximateOrdinaryLog
    {Head Band : Type*} [Fintype Head] [DecidableEq Head]
    [Fintype Band] [DecidableEq Band] [Nonempty Head]
    (B : BridgeData Head Band)
    {c : Real} {depth : Nat}
    (R : BankPaperRealization B.sampleData.n
      (upperEndpoint B.sampleData.n
        (upperTailLength c B.sampleData.n)))
    (certificate : GuardedCentralAnchorCertificate c depth B.sampleData.n
      R.anchorGuardLeftCore R.anchorGuardRightCore
      (R.centralChangedMarkers depth))
    (fixed candidates : Finset Nat) (preSelector : Nat -> Real)
    (activeSeed : B.sampleData.Sample -> Real)
    {T : BarycentricTarget B.sampleData}
    (Hmeasure : BankPaperCanonicalActualActiveMeasureConstructor
      B.sampleData T candidates preSelector activeSeed)
    (hseed : forall m, B.baseline.baseWeight m = activeSeed m)
    (Cinitial Cordinary : Real)
    (hCinitial : 0 <= Cinitial) (hCordinary : 0 <= Cordinary)
    (hdeficit : ∀ p ∈
      primeBand B.sampleData.n B.sampleData.W,
      abs (bankPaperCanonicalSelectorValuationDeficit
        R certificate fixed candidates preSelector p) <=
          Cinitial * B.q / ((p : Real) * B.L))
    (hordinary :
      BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
        (W := B.sampleData.W) R certificate fixed candidates preSelector
        ((B.q / B.L) * Cordinary * B.w))
    (hdeviation : B.primeDeviationL1 <= 7 * B.w) :
    B.HasTargetEnvelopes (7 * Cinitial + Cordinary)
      (fun j => B.markedBandResidual
        (bankPaperCanonicalActualActiveMarkedTarget
          B R certificate fixed candidates preSelector activeSeed) 0 j) := by
  let markedTarget : Nat -> Real :=
    bankPaperCanonicalActualActiveMarkedTarget
      B R certificate fixed candidates preSelector activeSeed
  let residual : BandPrime B.sampleData.n B.sampleData.W -> Real :=
    fun p =>
      bankPaperCanonicalTangentResidual
        R certificate fixed candidates preSelector p
  have hDelta : forall j : Band,
      B.markedBandResidual markedTarget 0 j =
        ∑ p ∈ B.partition.data.fiber j, residual p := by
    intro j
    unfold BridgeData.markedBandResidual
    apply Finset.sum_congr rfl
    intro p _hp
    dsimp only [markedTarget, residual,
      bankPaperCanonicalTangentResidual]
    exact (bankPaperCanonicalActualInitial_deficit_eq_activeResidual
      B R certificate fixed candidates preSelector activeSeed
        Hmeasure hseed p.1).symm
  have hpointwise : forall p,
      abs (residual p) <=
        Cinitial * B.q / ((p.1 : Real) * B.L) := by
    intro p
    simpa only [residual, bankPaperCanonicalTangentResidual] using
      hdeficit p.1 p.2
  have hordinaryResidual :
      abs (∑ p : BandPrime B.sampleData.n B.sampleData.W,
        tPrime B.sampleData.n p.1 * residual p) <=
          (B.q / B.L) * Cordinary * B.w := by
    simpa only [
      BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo,
      residual] using hordinary
  exact
    bankPaperCanonicalHasTargetEnvelopes_seven_add_of_primeResidual
      B
      (fun j => B.markedBandResidual markedTarget 0 j)
      residual Cinitial Cordinary hCinitial hCordinary
        hDelta hpointwise hordinaryResidual hdeviation

/-! ## The nearest-integer height residual is a bounded ordinary defect -/

/-- The normalized residual left by the nearest-integer height center.  Its
denominator is exactly the denominator in `tPrime = log p / log y`. -/
def bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
    (n : Nat) (mu q0 A0 : Real) : Real :=
  (A0 +
      (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real) * L n -
    mu * (q0 -
      (bankPaperCanonicalSmoothHeightAdjustment n mu q0 A0 : Real))) /
    Real.log (y n)

/-- Finite adapter for a source-specific height ledger.  It isolates the
only identification still needed from the Section 8 construction: the
weighted selector residual must equal the displayed normalized rounding
defect. -/
theorem
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo.of_eq_normalizedHeightRoundingDefect
    {c : Real} {depth n W : Nat} {left right : Nat -> Nat}
    {changed : Finset Nat}
    (R : BankPaperRealization n
      (upperEndpoint n (upperTailLength c n)))
    (certificate : GuardedCentralAnchorCertificate c depth n
      left right changed)
    (fixed candidates : Finset Nat) (selector : Nat -> Real)
    (mu q0 A0 E : Real)
    (hidentify :
      (∑ p : BankPaperCanonicalTangentPrime n W,
        tPrime n p.1 *
          bankPaperCanonicalTangentResidual
            R certificate fixed candidates selector p) =
        bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
          n mu q0 A0)
    (hround :
      abs (bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
        n mu q0 A0) <= E) :
    BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
      (W := W) R certificate fixed candidates selector E := by
  unfold BankPaperCanonicalSelectorOrdinaryLogCompatibleUpTo
  rw [hidentify]
  exact hround

/-- Pointwise normalized form of the existing half-unit height-rounding
bound. -/
theorem
    bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le
    {n : Nat} (hn : 1 < n) (mu q0 A0 : Real)
    (hdenom : L n + mu ≠ 0) :
    abs (bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
      n mu q0 A0) <=
      ((1 / 2) * abs (L n + mu)) / Real.log (y n) := by
  have hlogY : 0 < Real.log (y n) := by
    rw [Scale.log_y (Nat.zero_lt_of_lt hn)]
    exact mul_pos (by norm_num) (L_pos hn)
  unfold bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
  rw [abs_div, abs_of_pos hlogY]
  exact div_le_div_of_nonneg_right
    (bankPaperCanonicalSmoothHeightAdjustment_centered_residual_bound
      n mu q0 A0 hdenom)
    hlogY.le

/-- For a fixed nonnegative center `mu`, the normalized rounding defect is
eventually at most `9 / 2`.  No estimate on `q0` or `A0` is needed. -/
theorem
    eventually_bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le_nine_halves
    (mu : Real) (hmu : 0 <= mu)
    (q0 A0 : Nat -> Real) :
    ∀ᶠ n : Nat in atTop,
      abs (bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
        n mu (q0 n) (A0 n)) <= 9 / 2 := by
  have hLTop : Tendsto (fun n : Nat => L n) atTop atTop := by
    simpa [L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hmuLe : ∀ᶠ n : Nat in atTop, mu <= L n :=
    hLTop.eventually (eventually_ge_atTop mu)
  filter_upwards [eventually_gt_atTop 1, hmuLe] with n hn hmuLeN
  have hL : 0 < L n := L_pos hn
  have hdenom : L n + mu ≠ 0 :=
    (add_pos_of_pos_of_nonneg hL hmu).ne'
  have hround :=
    bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le
      hn mu (q0 n) (A0 n) hdenom
  calc
    abs (bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
        n mu (q0 n) (A0 n)) <=
        ((1 / 2) * abs (L n + mu)) / Real.log (y n) :=
      hround
    _ <= 9 / 2 := by
      rw [Scale.log_y (Nat.zero_lt_of_lt hn),
        abs_of_nonneg (add_nonneg hL.le hmu)]
      apply (div_le_iff₀ (mul_pos (by norm_num) hL)).2
      nlinarith

/-- Every fixed absolute defect is eventually absorbed by `(q / L) * w`
when `q` has the paper-scale lower bound and `w` is fixed and positive. -/
theorem eventually_constant_le_activeMass_div_L_mul_mesh
    (q : Nat -> Real)
    (Hq : BankPaperCanonicalActiveMassPaperScaleLower q)
    {w : Real} (hw : 0 < w) (E : Real) :
    ∀ᶠ n : Nat in atTop, E <= q n / L n * w := by
  rcases Hq with ⟨c, hc, hq⟩
  have hcw : 0 < c * w := mul_pos hc hw
  have hgrowth :
      Tendsto
        (fun n : Nat => (c * w) * (secondOrderScale n / L n))
        atTop atTop :=
    secondOrderScale_div_L_tendsto_atTop.const_mul_atTop hcw
  have hlarge : ∀ᶠ n : Nat in atTop,
      E <= (c * w) * (secondOrderScale n / L n) :=
    hgrowth.eventually (eventually_ge_atTop E)
  filter_upwards [hq, hlarge, eventually_gt_atTop 1]
      with n hqN hlargeN hn
  have hL : 0 < L n := L_pos hn
  calc
    E <= (c * w) * (secondOrderScale n / L n) := hlargeN
    _ = (c * secondOrderScale n / L n) * w := by ring
    _ <= (q n / L n) * w := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hqN hL.le) hw.le

/-- Consequently the normalized nearest-integer height defect is eventually
small enough for the approximate target-envelope theorem with
`Cordinary = 1`. -/
theorem
    eventually_bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le_activeMass_div_L_mul_mesh
    (mu : Real) (hmu : 0 <= mu)
    (q0 A0 q : Nat -> Real)
    (Hq : BankPaperCanonicalActiveMassPaperScaleLower q)
    {w : Real} (hw : 0 < w) :
    ∀ᶠ n : Nat in atTop,
      abs (bankPaperCanonicalSmoothNormalizedHeightRoundingDefect
        n mu (q0 n) (A0 n)) <= q n / L n * w := by
  have hround :=
    eventually_bankPaperCanonicalSmoothNormalizedHeightRoundingDefect_abs_le_nine_halves
      mu hmu q0 A0
  have habsorb :=
    eventually_constant_le_activeMass_div_L_mul_mesh
      q Hq hw (9 / 2)
  filter_upwards [hround, habsorb] with n hroundN habsorbN
  exact hroundN.trans habsorbN

end

end Erdos390.WholePaper
