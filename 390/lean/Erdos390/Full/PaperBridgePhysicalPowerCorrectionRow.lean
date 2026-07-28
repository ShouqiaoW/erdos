import Erdos390.Full.PaperBridgePhysicalDivisorCovariance
import Erdos390.Full.FiniteProbabilityPowerCorrectionMixturePerturbation
import Erdos390.Full.PaperBridgeMediumValuationMixture
import Erdos390.Full.PaperActualSquarefreeReference
import Erdos390.Full.LocalFugacityBounds
import Erdos390.Full.PrimePowerLcmGeometry

/-!
# The prime-power correction row through the residual physical tilt

This file keeps the actual partition-function-reweighted component weights
fixed and compares the residual physical tilt component by component.  The
high prime-power columns are summed geometrically before the tagged-mixture
covariance algebra is applied.  Consequently the final comparison is for the
literal `VV-II` row, including all between-component covariance terms.
-/

open scoped BigOperators
open Filter Topology

namespace Erdos390.Full.PaperBridgeFit

noncomputable section

open ArithmeticModel ArithmeticBandGeometry FiniteProbability
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PrimePowerCutoffCovariance ValuationCutoff LocalFugacityBounds
open PrimeSums
open PrimePowerLcmGeometry

namespace BridgeData

variable {Head Band : Type*} [Fintype Head] [DecidableEq Head]
  [Fintype Band] [DecidableEq Band]
  (B : BridgeData Head Band)

/-- The medium-only comparison law uses exactly the component weights of the
actual full bridge law.  Thus this comparison never changes the tagged-cell
mixture weights. -/
def physicalMediumReferenceLaw [Nonempty Head]
    (xi : B.ParamSpace) :
    BoundedValuationLaw B.sampleData.Sample B.sampleEndpoint :=
  sigmaMixture
    (tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi))
    (B.mediumComponentValuationLaw xi)

/-- Explicit weighted-row loss for deleting the residual physical tilt.
The only moving arithmetic quantity is the harmonic prime-band mass. -/
def physicalPowerCorrectionRowError
    (epsilon G : ℝ) (n W : ℕ) : ℝ :=
  200 * (8 * epsilon) * (1 + quadraticHalfMass) * (1 + G) ^ 2 *
    (bandReciprocalSum n W + 1) * (1 / (W : ℝ))

/-- The exact budget supplied to the tagged-mixture perturbation identity for
one marked prime.  It is kept as a definition so every source term remains
auditable. -/
def physicalPowerCorrectionMixtureBudget
    (epsilon G : ℝ) (n W p : ℕ) : ℝ :=
  let e := 8 * epsilon
  let H := bandReciprocalSum n W
  let S₂ := bandReciprocalSquareSum n W
  let w₁ := 1 / (W : ℝ)
  let p₁ := 1 / (p : ℝ)
  let AIp := G * p₁
  let AJp := 2 * G * p₁ ^ 2
  let AIrow := G * H
  let AJrow := 2 * G * w₁
  let dIp := e * G * p₁
  let dJp := 2 * e * G * p₁ ^ 2
  let dIrow := e * G * H
  let dJrow := 2 * e * G * w₁
  let dJI := e * (2 * G + 6 * G ^ 2) * p₁ ^ 2 * H +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dIJ := e * (2 * G + 6 * G ^ 2) * p₁ * S₂ +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dJJ := e * (4 * G + 12 * G ^ 2) * p₁ ^ 2 * S₂ +
    e * (G * quadraticHalfMass * p₁ ^ 2 + 12 * G ^ 2 * p₁ ^ 4)
  (dJI + 2 * ((AJp + dJp) * dIrow + AIrow * dJp)) +
    (dIJ + 2 * ((AIp + dIp) * dJrow + AJrow * dIp)) +
    (dJJ + 2 * ((AJp + dJp) * dJrow + AJrow * dJp))

theorem physicalPowerCorrectionRowError_nonneg
    {epsilon G : ℝ} {n W : ℕ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) :
    0 ≤ physicalPowerCorrectionRowError epsilon G n W := by
  unfold physicalPowerCorrectionRowError bandReciprocalSum
  have hQ : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  positivity

/-- The residual-physical prime-power row retains the sharp moving-low-cell
rate.  The hypothesis is deliberately the two-harmonic rate: one logarithm
is spent in the prime-row sum and the displayed factor spends the second.
Thus this theorem does not silently promote a bare `o(1)` bound to the
`o(alpha_0)` bound needed in Lemma 8.5. -/
theorem tendsto_physicalPowerCorrectionRowError_mul_logL_zero
    (epsilon : ℕ → ℝ) (G : ℝ) (W : ℕ)
    (hepsilon0 : ∀ n, 0 ≤ epsilon n) (hG : 0 ≤ G)
    (hepsilonRateSq : Tendsto
      (fun n : ℕ ↦ epsilon n * Real.log (Scale.L n) ^ 2)
        atTop (nhds 0)) :
    Tendsto (fun n : ℕ ↦
      physicalPowerCorrectionRowError (epsilon n) G n W *
        Real.log (Scale.L n)) atTop (nhds 0) := by
  let C : ℝ :=
    200 * 8 * (1 + quadraticHalfMass) * (1 + G) ^ 2 *
      (1 / (W : ℝ))
  let upper : ℕ → ℝ := fun n ↦
    (13 * C) * (epsilon n * Real.log (Scale.L n) ^ 2)
  have hQ : 0 ≤ quadraticHalfMass := quadraticHalfMass_nonneg
  have hC : 0 ≤ C := by
    dsimp only [C]
    positivity
  have hupperT : Tendsto upper atTop (nhds 0) := by
    have hconst : Tendsto (fun _n : ℕ ↦ 13 * C) atTop (nhds (13 * C)) :=
      tendsto_const_nhds
    have hraw := hconst.mul hepsilonRateSq
    simpa only [upper, mul_zero] using hraw
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ physicalPowerCorrectionRowError (epsilon n) G n W *
        Real.log (Scale.L n) := by
    filter_upwards [hLTop.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hL
    exact mul_nonneg
      (physicalPowerCorrectionRowError_nonneg (hepsilon0 n) hG)
      (Real.log_nonneg hL)
  have hmajor : ∀ᶠ n : ℕ in atTop,
      physicalPowerCorrectionRowError (epsilon n) G n W *
          Real.log (Scale.L n) ≤ upper n := by
    filter_upwards [eventually_bandReciprocalSum_le_logL W,
      hLTop.eventually (eventually_ge_atTop (Real.exp 1))]
      with n hband hL
    have hlog : 1 ≤ Real.log (Scale.L n) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hL
    have hlog0 : 0 ≤ Real.log (Scale.L n) := le_trans (by norm_num) hlog
    have hband0 : 0 ≤ bandReciprocalSum n W := by
      unfold bandReciprocalSum
      positivity
    have hbandOne : bandReciprocalSum n W + 1 ≤
        13 * Real.log (Scale.L n) := by linarith
    have hscale : 0 ≤ C * epsilon n := mul_nonneg hC (hepsilon0 n)
    have hscaled := mul_le_mul_of_nonneg_left hbandOne hscale
    dsimp only [upper]
    unfold physicalPowerCorrectionRowError
    dsimp only [C]
    calc
      (200 * (8 * epsilon n) * (1 + quadraticHalfMass) *
          (1 + G) ^ 2 * (bandReciprocalSum n W + 1) *
            (1 / (W : ℝ))) * Real.log (Scale.L n) =
          (C * epsilon n) * (bandReciprocalSum n W + 1) *
            Real.log (Scale.L n) := by ring
      _ ≤ (C * epsilon n) * (13 * Real.log (Scale.L n)) *
            Real.log (Scale.L n) :=
        mul_le_mul_of_nonneg_right hscaled hlog0
      _ = (13 * C) *
          (epsilon n * Real.log (Scale.L n) ^ 2) := by ring
  exact squeeze_zero' hnonneg hmajor hupperT

/-- Paper-scale specialization of the sharp rate: a fixed physical score
box gives `epsilon = C / L`, and hence the weighted row is still
`o(1 / log L)`. -/
theorem tendsto_physicalPowerCorrectionRowError_const_div_L_mul_logL_zero
    (C G : ℝ) (W : ℕ) (hC : 0 ≤ C) (hG : 0 ≤ G) :
    Tendsto (fun n : ℕ ↦
      physicalPowerCorrectionRowError (C / Scale.L n) G n W *
        Real.log (Scale.L n)) atTop (nhds 0) := by
  have hL0 (n : ℕ) : 0 ≤ Scale.L n := by
    cases n with
    | zero => norm_num [Scale.L]
    | succ n =>
        exact Real.log_nonneg (by
          exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
  have hLTop : Tendsto Scale.L atTop atTop := by
    simpa only [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto
      (fun n : ℕ ↦ Real.log (Scale.L n) ^ 2 / Scale.L n)
        atTop (nhds 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero.comp hLTop
  have hconst : Tendsto (fun _n : ℕ ↦ C) atTop (nhds C) :=
    tendsto_const_nhds
  have hrateRaw := hconst.mul hratio
  have hrate : Tendsto
      (fun n : ℕ ↦ (C / Scale.L n) * Real.log (Scale.L n) ^ 2)
        atTop (nhds 0) := by
    have hzero : Tendsto (fun n : ℕ ↦
        C * (Real.log (Scale.L n) ^ 2 / Scale.L n))
          atTop (nhds 0) := by
      simpa only [mul_zero] using hrateRaw
    apply hzero.congr'
    filter_upwards with n
    ring
  exact tendsto_physicalPowerCorrectionRowError_mul_logL_zero
    (fun n ↦ C / Scale.L n) G W
      (fun n ↦ div_nonneg hC (hL0 n)) hG hrate

set_option maxHeartbeats 2000000 in
/-- The exact tagged-mixture budget is one marked-prime factor smaller than
the public weighted-row error.  All estimates are finite and pointwise; in
particular, no asymptotic `O`-constant or change of mixture weights is hidden
in this contraction. -/
theorem physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
    {epsilon G : ℝ} {n W p : ℕ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1)
    (hG : 0 ≤ G) (hW : 1 < W) (hp : p ∈ primeBand n W) :
    physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
      (1 / (p : ℝ)) * physicalPowerCorrectionRowError epsilon G n W := by
  let e : ℝ := 8 * epsilon
  let H : ℝ := bandReciprocalSum n W
  let S : ℝ := bandReciprocalSquareSum n W
  let w : ℝ := 1 / (W : ℝ)
  let x : ℝ := 1 / (p : ℝ)
  let Q : ℝ := quadraticHalfMass
  let R : ℝ := (1 + Q) * (1 + G) ^ 2
  let F : ℝ := e * R * (H + 1) * w
  have he0 : 0 ≤ e := by dsimp only [e]; positivity
  have he1 : e ≤ 1 := by simpa only [e] using hsmall
  have hH0 : 0 ≤ H := by
    dsimp only [H, bandReciprocalSum]
    positivity
  have hS0 : 0 ≤ S := by
    dsimp only [S, bandReciprocalSquareSum]
    positivity
  have hW0 : 0 < (W : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hW)
  have hw0 : 0 ≤ w := by dsimp only [w]; positivity
  have hw1 : w ≤ 1 := by
    dsimp only [w]
    exact (div_le_one hW0).2 (by exact_mod_cast hW.le)
  have hpPrime := prime_of_mem_primeBand hp
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpPrime.pos
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hxp : x ≤ w := by
    dsimp only [x, w]
    exact one_div_le_one_div_of_le hW0
      (by exact_mod_cast (cutoff_lt_of_mem_primeBand hp).le)
  have hx1 : x ≤ 1 := hxp.trans hw1
  have hSle : S ≤ w := by
    dsimp only [S, w]
    exact bandReciprocalSquareSum_le n W hW.le
  have hQ0 : 0 ≤ Q := by
    dsimp only [Q]
    exact quadraticHalfMass_nonneg
  have hR0 : 0 ≤ R := by dsimp only [R]; positivity
  have hF0 : 0 ≤ F := by dsimp only [F]; positivity
  have hGone : G ≤ (1 + G) ^ 2 := by nlinarith [sq_nonneg G]
  have hGtwo : G ^ 2 ≤ (1 + G) ^ 2 := by nlinarith
  have hGle : G ≤ R := by
    dsimp only [R]
    calc
      G ≤ (1 + G) ^ 2 := hGone
      _ ≤ (1 + Q) * (1 + G) ^ 2 := by
        nlinarith [mul_nonneg hQ0 (sq_nonneg (1 + G))]
  have hGtwoLe : G ^ 2 ≤ R := by
    dsimp only [R]
    calc
      G ^ 2 ≤ (1 + G) ^ 2 := hGtwo
      _ ≤ (1 + Q) * (1 + G) ^ 2 := by
        nlinarith [mul_nonneg hQ0 (sq_nonneg (1 + G))]
  have hGQLe : G * Q ≤ R := by
    dsimp only [R]
    have hprod := mul_le_mul hGone (show Q ≤ 1 + Q by linarith)
      hQ0 (sq_nonneg (1 + G))
    nlinarith
  have hHle : H ≤ H + 1 := by linarith
  have honeH : (1 : ℝ) ≤ H + 1 := by linarith
  have hxSqW : x ^ 2 ≤ w := by
    have hxx : x * x ≤ x * 1 := mul_le_mul_of_nonneg_left hx1 hx0
    nlinarith [hxp]
  have hxCubeW : x ^ 3 ≤ w := by
    have hmul := mul_le_mul hx1 hxSqW (sq_nonneg x)
      (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith
  have hxwW : x * w ≤ w := by nlinarith [mul_le_mul_of_nonneg_right hx1 hw0]
  have hexe : e * x ≤ w := by
    have hex : e * x ≤ 1 * x := mul_le_mul_of_nonneg_right he1 hx0
    nlinarith [hxp]
  have hexw : e * (x * w) ≤ w := by
    calc
      e * (x * w) ≤ 1 * (x * w) :=
        mul_le_mul_of_nonneg_right he1 (mul_nonneg hx0 hw0)
      _ = x * w := one_mul _
      _ ≤ w := hxwW
  have hmono (a b c : ℝ) (ha0 : 0 ≤ a) (ha : a ≤ R)
      (hb0 : 0 ≤ b) (hb : b ≤ H + 1)
      (hc0 : 0 ≤ c) (hc : c ≤ w) :
      x * e * a * b * c ≤ x * F := by
    dsimp only [F]
    have hxe : 0 ≤ x * e := mul_nonneg hx0 he0
    calc
      x * e * a * b * c ≤ x * e * R * b * c := by gcongr
      _ ≤ x * e * R * (H + 1) * c := by gcongr
      _ ≤ x * e * R * (H + 1) * w := by gcongr
      _ = x * (e * R * (H + 1) * w) := by ring
  have mGHx : e * G * x ^ 2 * H ≤ x * F := by
    (convert hmono G H x hG hGle hH0 hHle hx0 hxp using 1; ring_nf)
  have mGtwoHx : e * G ^ 2 * x ^ 2 * H ≤ x * F := by
    (convert hmono (G ^ 2) H x (sq_nonneg G) hGtwoLe hH0 hHle hx0 hxp
      using 1; ring_nf)
  have meGtwoHx : e ^ 2 * G ^ 2 * x ^ 2 * H ≤ x * F := by
    (convert hmono (G ^ 2) H (e * x) (sq_nonneg G) hGtwoLe hH0 hHle
      (mul_nonneg he0 hx0) hexe using 1; ring_nf)
  have mGx : e * G * x ^ 2 ≤ x * F := by
    (convert hmono G 1 x hG hGle (by norm_num) honeH hx0 hxp using 1; ring_nf)
  have mGtwoXsq : e * G ^ 2 * x ^ 3 ≤ x * F := by
    (convert hmono (G ^ 2) 1 (x ^ 2) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (sq_nonneg x) hxSqW using 1; ring_nf)
  have mGS : e * G * x * S ≤ x * F := by
    (convert hmono G 1 S hG hGle (by norm_num) honeH hS0 hSle using 1; ring_nf)
  have mGtwoS : e * G ^ 2 * x * S ≤ x * F := by
    (convert hmono (G ^ 2) 1 S (sq_nonneg G) hGtwoLe
      (by norm_num) honeH hS0 hSle using 1; ring_nf)
  have mGxS : e * G * x ^ 2 * S ≤ x * F := by
    have hxs0 : 0 ≤ x * S := mul_nonneg hx0 hS0
    have hxsW : x * S ≤ w := by
      have := mul_le_mul hx1 hSle hS0 (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    (convert hmono G 1 (x * S) hG hGle (by norm_num) honeH hxs0 hxsW
      using 1; ring_nf)
  have mGtwoXS : e * G ^ 2 * x ^ 2 * S ≤ x * F := by
    have hxs0 : 0 ≤ x * S := mul_nonneg hx0 hS0
    have hxsW : x * S ≤ w := by
      have := mul_le_mul hx1 hSle hS0 (by norm_num : (0 : ℝ) ≤ 1)
      nlinarith
    (convert hmono (G ^ 2) 1 (x * S) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH hxs0 hxsW using 1; ring_nf)
  have mGQx : e * (G * Q) * x ^ 2 ≤ x * F := by
    (convert hmono (G * Q) 1 x (mul_nonneg hG hQ0) hGQLe
      (by norm_num) honeH hx0 hxp using 1; ring_nf)
  have mGtwoXcube : e * G ^ 2 * x ^ 4 ≤ x * F := by
    (convert hmono (G ^ 2) 1 (x ^ 3) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (by positivity) hxCubeW using 1; ring_nf)
  have mGtwoW : e * G ^ 2 * x * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 w (sq_nonneg G) hGtwoLe
      (by norm_num) honeH hw0 le_rfl using 1; ring_nf)
  have meGtwoW : e ^ 2 * G ^ 2 * x * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 (e * w) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (mul_nonneg he0 hw0)
      (by nlinarith [mul_le_mul_of_nonneg_right he1 hw0]) using 1; ring_nf)
  have mGtwoXW : e * G ^ 2 * x ^ 2 * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 (x * w) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (mul_nonneg hx0 hw0) hxwW using 1; ring_nf)
  have meGtwoXW : e ^ 2 * G ^ 2 * x ^ 2 * w ≤ x * F := by
    (convert hmono (G ^ 2) 1 (e * (x * w)) (sq_nonneg G) hGtwoLe
      (by norm_num) honeH (by positivity) hexw using 1; ring_nf)
  change
    physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
      (1 / (p : ℝ)) * physicalPowerCorrectionRowError epsilon G n W
  unfold physicalPowerCorrectionMixtureBudget physicalPowerCorrectionRowError
  dsimp only
  change _ ≤ x * (200 * e * (1 + Q) * (1 + G) ^ 2 * (H + 1) * w)
  have htarget : x * (200 * e * (1 + Q) * (1 + G) ^ 2 *
      (H + 1) * w) = 200 * (x * F) := by
    dsimp only [F, R]
    ring
  rw [htarget]
  nlinarith [mGHx, mGtwoHx, meGtwoHx, mGx, mGtwoXsq,
    mGS, mGtwoS, mGxS, mGtwoXS, mGQx, mGtwoXcube,
    mGtwoW, meGtwoW, mGtwoXW, meGtwoXW]

/-- Weighted-row form of the preceding exact contraction. -/
theorem physicalPowerCorrectionMixtureBudget_mul_le_rowError
    {epsilon G : ℝ} {n W p : ℕ}
    (hepsilon : 0 ≤ epsilon) (hsmall : 8 * epsilon ≤ 1)
    (hG : 0 ≤ G) (hW : 1 < W) (hp : p ∈ primeBand n W) :
    (p : ℝ) * physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
      physicalPowerCorrectionRowError epsilon G n W := by
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hpne : (p : ℝ) ≠ 0 := by
    exact_mod_cast (prime_of_mem_primeBand hp).ne_zero
  calc
    (p : ℝ) * physicalPowerCorrectionMixtureBudget epsilon G n W p ≤
        (p : ℝ) * ((1 / (p : ℝ)) *
          physicalPowerCorrectionRowError epsilon G n W) :=
      mul_le_mul_of_nonneg_left
        (physicalPowerCorrectionMixtureBudget_le_inv_mul_rowError
          hepsilon hsmall hG hW hp) hp0
    _ = physicalPowerCorrectionRowError epsilon G n W := by
      field_simp

private theorem expect_finset_sum
    {Omega : Type*} [Fintype Omega]
    (mu : FiniteProbability Omega) (S : Finset ℕ)
    (f : ℕ → Omega → ℝ) :
    mu.expect (fun x ↦ ∑ k ∈ S, f k x) =
      ∑ k ∈ S, mu.expect (f k) := by
  induction S using Finset.induction_on with
  | empty => simp [FiniteProbability.expect_zero]
  | @insert k S hk ih =>
      simp only [Finset.sum_insert hk]
      rw [mu.expect_add, ih]

private theorem sum_pair_linear
    {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (T : Finset J)
    (a b : I → J → ℝ) (c d : ℝ) :
    (∑ i ∈ S, ∑ j ∈ T, (c * a i j + d * b i j)) =
      c * (∑ i ∈ S, ∑ j ∈ T, a i j) +
        d * (∑ i ∈ S, ∑ j ∈ T, b i j) := by
  calc
    (∑ i ∈ S, ∑ j ∈ T, (c * a i j + d * b i j)) =
        ∑ i ∈ S,
          (c * (∑ j ∈ T, a i j) + d * (∑ j ∈ T, b i j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]
    _ = _ := by
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_add_distrib]

private theorem sum_bandPrime_inv_eq (n W : ℕ) :
    (∑ p : BandPrime n W, 1 / (p.1 : ℝ)) =
      bandReciprocalSum n W := by
  unfold bandReciprocalSum
  simpa only using (Finset.sum_attach (primeBand n W)
    (fun p ↦ 1 / (p : ℝ)))

private theorem sum_bandPrime_inv_sq_eq (n W : ℕ) :
    (∑ p : BandPrime n W, 1 / (p.1 : ℝ) ^ 2) =
      bandReciprocalSquareSum n W := by
  unfold bandReciprocalSquareSum
  simpa only using (Finset.sum_attach (primeBand n W)
    (fun p ↦ 1 / (p : ℝ) ^ 2))

/-- A reciprocal divisor fallback geometrically sums to the natural
`p^{-2}` first-moment scale of the higher-valuation column. -/
theorem expect_J_le_of_divisor_fallback
    {Omega : Type*} [Fintype Omega] {M p : ℕ}
    (law : BoundedValuationLaw Omega M) (hp : p.Prime)
    {G : ℝ} (hG : 0 ≤ G)
    (hdiv : ∀ D : ℕ, 0 < D →
      law.probability.expect (fun x ↦ divInd D (law.value x)) ≤
        G * (1 / (D : ℝ))) :
    law.probability.expect (law.J p) ≤ 2 * G * (1 / (p : ℝ)) ^ 2 := by
  rw [J_eq_valuationCutoff_sum law hp]
  rw [expect_finset_sum]
  calc
    (∑ k ∈ highExponents (valuationCutoff p M),
        law.probability.expect (law.Ip p k)) ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          G * (1 / ((p ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [BoundedValuationLaw.Ip] using
        hdiv (p ^ k) (pow_pos hp.pos k)
    _ = G * (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ G * (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hG
      simpa only [highExponents] using
        (sum_inv_pow_tail_le (p := p) (r := 1)
          (A := valuationCutoff p M) hp.two_le)
    _ = 2 * G * (1 / (p : ℝ)) ^ 2 := by ring

/-- The same geometric summation applies to a difference of two divisor
profiles. -/
theorem abs_expect_J_sub_le_of_divisor_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {d : ℝ} (hd : 0 ≤ d)
    (hdiv : ∀ D : ℕ, 0 < D →
      |nu.probability.expect (fun x ↦ divInd D (nu.value x)) -
        mu.probability.expect (fun x ↦ divInd D (mu.value x))| ≤
          d * (1 / (D : ℝ))) :
    |nu.probability.expect (nu.J p) -
      mu.probability.expect (mu.J p)| ≤
        2 * d * (1 / (p : ℝ)) ^ 2 := by
  rw [J_eq_valuationCutoff_sum nu hp, J_eq_valuationCutoff_sum mu hp]
  rw [expect_finset_sum, expect_finset_sum, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.expect (nu.Ip p k) -
          mu.probability.expect (mu.Ip p k))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.expect (nu.Ip p k) -
            mu.probability.expect (mu.Ip p k)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
          d * (1 / ((p ^ k : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [BoundedValuationLaw.Ip] using
        hdiv (p ^ k) (pow_pos hp.pos k)
    _ = d * (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by rw [Finset.mul_sum]
    _ ≤ d * (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hd
      simpa only [highExponents] using
        (sum_inv_pow_tail_le (p := p) (r := 1)
          (A := valuationCutoff p M) hp.two_le)
    _ = 2 * d * (1 / (p : ℝ)) ^ 2 := by ring

/-- Off the diagonal, the `JI` residual-tilt covariance sums on the literal
`p^{-2}q^{-1}` scale. -/
theorem abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJI p q - mu.covJI p q| ≤
      e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by
  rw [covJI_eq_valuationCutoff_sum nu hp,
    covJI_eq_valuationCutoff_sum mu hp, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.covariance (nu.Ip p k) (nu.I q) -
          mu.probability.covariance (mu.Ip p k) (mu.I q))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.covariance (nu.Ip p k) (nu.I q) -
            mu.probability.covariance (mu.Ip p k) (mu.I q)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        e * (G + 3 * G ^ 2) *
          (1 / ((p ^ k : ℕ) : ℝ)) * (1 / (q : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      have hcop : Nat.Coprime (p ^ k) (q ^ 1) :=
        Nat.coprime_pow_primes k 1 hp hq hpq
      have hlcm : Nat.lcm (p ^ k) q = p ^ k * q := by
        simpa only [pow_one] using hcop.lcm_eq_mul
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.I q) -
            mu.probability.covariance (mu.Ip p k) (mu.I q)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) q : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / (q : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip, BoundedValuationLaw.I] using
            hcov (p ^ k) q (pow_pos hp.pos k) hq.pos
        _ = e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) * (1 / (q : ℝ)) := by
          rw [hlcm, Nat.cast_mul]
          ring
    _ = (e * (G + 3 * G ^ 2) * (1 / (q : ℝ))) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ (e * (G + 3 * G ^ 2) * (1 / (q : ℝ))) *
        (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1)
            (A := valuationCutoff p M) hp.two_le)
      · positivity
    _ = e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) := by ring

/-- On the diagonal, `J_p` against `I_p` retains the same `p^{-2}` scale. -/
theorem abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJI p p - mu.covJI p p| ≤
      e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by
  rw [covJI_eq_valuationCutoff_sum nu hp,
    covJI_eq_valuationCutoff_sum mu hp, ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        (nu.probability.covariance (nu.Ip p k) (nu.I p) -
          mu.probability.covariance (mu.Ip p k) (mu.I p))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |nu.probability.covariance (nu.Ip p k) (nu.I p) -
            mu.probability.covariance (mu.Ip p k) (mu.I p)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        e * (G * (1 / ((p ^ k : ℕ) : ℝ)) +
          3 * G ^ 2 * (1 / ((p ^ k : ℕ) : ℝ)) *
            (1 / (p : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      have hk2 : 2 ≤ k := (mem_highExponents.mp hk).1
      have hlcm : Nat.lcm (p ^ k) p = p ^ k :=
        Nat.lcm_eq_left_iff_dvd.mpr (dvd_pow_self p (by omega))
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.I p) -
            mu.probability.covariance (mu.Ip p k) (mu.I p)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) p : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / (p : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip, BoundedValuationLaw.I] using
            hcov (p ^ k) p (pow_pos hp.pos k) hp.pos
        _ = e * (G * (1 / ((p ^ k : ℕ) : ℝ)) +
            3 * G ^ 2 * (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / (p : ℝ))) := by rw [hlcm]; ring
    _ = e * (G + 3 * G ^ 2 * (1 / (p : ℝ))) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring
    _ ≤ e * (G + 3 * G ^ 2 * (1 / (p : ℝ))) *
        (2 / (p : ℝ) ^ 2) := by
      apply mul_le_mul_of_nonneg_left
      · simpa only [highExponents] using
          (sum_inv_pow_tail_le (p := p) (r := 1)
            (A := valuationCutoff p M) hp.two_le)
      · positivity
    _ = e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by ring

/-- The `IJ` orientation is the transpose of the preceding `JI` estimate. -/
theorem abs_covIJ_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covIJ p q - mu.covIJ p q| ≤
      e * (2 * G + 6 * G ^ 2) *
        (1 / (p : ℝ)) * (1 / (q : ℝ)) ^ 2 := by
  have hcovSwap : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ)))) := by
    exact hcov
  have hraw := abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
    nu mu hq hp hpq.symm he hG hcovSwap
  have hnu : nu.covIJ p q = nu.covJI q p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact nu.probability.covariance_comm _ _
  have hmu : mu.covIJ p q = mu.covJI q p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact mu.probability.covariance_comm _ _
  rw [hnu, hmu]
  convert hraw using 1
  ring

theorem abs_covIJ_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covIJ p p - mu.covIJ p p| ≤
      e * (2 * G * (1 / (p : ℝ)) ^ 2 +
        6 * G ^ 2 * (1 / (p : ℝ)) ^ 3) := by
  have hraw := abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
    nu mu hp he hG hcov
  have hnu : nu.covIJ p p = nu.covJI p p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact nu.probability.covariance_comm _ _
  have hmu : mu.covIJ p p = mu.covJI p p := by
    unfold BoundedValuationLaw.covIJ BoundedValuationLaw.covJI
    exact mu.probability.covariance_comm _ _
  simpa only [hnu, hmu] using hraw

/-- For distinct primes both higher-valuation tails factor geometrically. -/
theorem abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p q : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJJ p q - mu.covJJ p q| ≤
      e * (4 * G + 12 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by
  rw [covJJ_eq_valuationCutoff_sum nu hp hq,
    covJJ_eq_valuationCutoff_sum mu hp hq,
    ← Finset.sum_sub_distrib]
  calc
    |∑ k ∈ highExponents (valuationCutoff p M),
        ((∑ l ∈ highExponents (valuationCutoff q M),
            nu.probability.covariance (nu.Ip p k) (nu.Ip q l)) -
          ∑ l ∈ highExponents (valuationCutoff q M),
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l))| ≤
        ∑ k ∈ highExponents (valuationCutoff p M),
          |∑ l ∈ highExponents (valuationCutoff q M),
              nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            ∑ l ∈ highExponents (valuationCutoff q M),
              mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ highExponents (valuationCutoff p M),
          |∑ l ∈ highExponents (valuationCutoff q M),
            (nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
              mu.probability.covariance (mu.Ip p k) (mu.Ip q l))| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          |nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ highExponents (valuationCutoff p M),
        ∑ l ∈ highExponents (valuationCutoff q M),
          e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((q ^ l : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      have hcop : Nat.Coprime (p ^ k) (q ^ l) :=
        Nat.coprime_pow_primes k l hp hq hpq
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.Ip q l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip q l)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) (q ^ l) : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / ((q ^ l : ℕ) : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip] using
            hcov (p ^ k) (q ^ l) (pow_pos hp.pos k) (pow_pos hq.pos l)
        _ = e * (G + 3 * G ^ 2) *
            (1 / ((p ^ k : ℕ) : ℝ)) *
              (1 / ((q ^ l : ℕ) : ℝ)) := by
          rw [hcop.lcm_eq_mul, Nat.cast_mul]
          ring
    _ = (e * (G + 3 * G ^ 2)) *
        (∑ k ∈ highExponents (valuationCutoff p M),
          1 / ((p ^ k : ℕ) : ℝ)) *
        (∑ l ∈ highExponents (valuationCutoff q M),
          1 / ((q ^ l : ℕ) : ℝ)) := by
      calc
        (∑ k ∈ highExponents (valuationCutoff p M),
          ∑ l ∈ highExponents (valuationCutoff q M),
            e * (G + 3 * G ^ 2) *
              (1 / ((p ^ k : ℕ) : ℝ)) *
                (1 / ((q ^ l : ℕ) : ℝ))) =
            ∑ k ∈ highExponents (valuationCutoff p M),
              (e * (G + 3 * G ^ 2) *
                (1 / ((p ^ k : ℕ) : ℝ))) *
                (∑ l ∈ highExponents (valuationCutoff q M),
                  1 / ((q ^ l : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.mul_sum]
        _ = (∑ k ∈ highExponents (valuationCutoff p M),
              e * (G + 3 * G ^ 2) *
                (1 / ((p ^ k : ℕ) : ℝ))) *
              (∑ l ∈ highExponents (valuationCutoff q M),
                1 / ((q ^ l : ℕ) : ℝ)) := by
            rw [Finset.sum_mul]
        _ = _ := by
            rw [← Finset.mul_sum]
    _ ≤ (e * (G + 3 * G ^ 2)) *
        (2 / (p : ℝ) ^ 2) * (2 / (q : ℝ) ^ 2) := by
      have hpTail := sum_inv_pow_tail_le (p := p) (r := 1)
        (A := valuationCutoff p M) hp.two_le
      have hqTail := sum_inv_pow_tail_le (p := q) (r := 1)
        (A := valuationCutoff q M) hq.two_le
      have hcoef : 0 ≤ e * (G + 3 * G ^ 2) := by positivity
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (by simpa only [highExponents] using hpTail)
          hcoef)
        (by simpa only [highExponents] using hqTail)
        (by positivity) (by positivity)
    _ = e * (4 * G + 12 * G ^ 2) *
        (1 / (p : ℝ)) ^ 2 * (1 / (q : ℝ)) ^ 2 := by ring

/-- On the diagonal, the exact lcm shell multiplicity gives a fixed
`p^{-2}` bound; no logarithmic exponent-counting loss is introduced. -/
theorem abs_covJJ_sub_le_of_divisor_covariance_difference_diagonal
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M p : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M) (hp : p.Prime)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    |nu.covJJ p p - mu.covJJ p p| ≤
      e * (G * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p : ℝ)) ^ 4) := by
  rw [covJJ_eq_valuationCutoff_sum nu hp hp,
    covJJ_eq_valuationCutoff_sum mu hp hp,
    ← Finset.sum_sub_distrib]
  let S := highExponents (valuationCutoff p M)
  calc
    |∑ k ∈ S,
        ((∑ l ∈ S, nu.probability.covariance (nu.Ip p k) (nu.Ip p l)) -
          ∑ l ∈ S,
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l))| ≤
        ∑ k ∈ S,
          |∑ l ∈ S,
              nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            ∑ l ∈ S,
              mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k ∈ S,
          |∑ l ∈ S,
            (nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
              mu.probability.covariance (mu.Ip p k) (mu.Ip p l))| := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_sub_distrib]
    _ ≤ ∑ k ∈ S, ∑ l ∈ S,
          |nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| := by
      apply Finset.sum_le_sum
      intro k hk
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ S, ∑ l ∈ S,
        e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
          3 * G ^ 2 * (1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Finset.sum_le_sum
      intro l hl
      calc
        |nu.probability.covariance (nu.Ip p k) (nu.Ip p l) -
            mu.probability.covariance (mu.Ip p k) (mu.Ip p l)| ≤
            e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
              3 * (G * (1 / ((p ^ k : ℕ) : ℝ))) *
                (G * (1 / ((p ^ l : ℕ) : ℝ)))) := by
          simpa only [BoundedValuationLaw.Ip] using
            hcov (p ^ k) (p ^ l) (pow_pos hp.pos k) (pow_pos hp.pos l)
        _ = e * (G * (1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
            3 * G ^ 2 * (1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
          rw [Nat.cast_mul]
          ring
    _ = e * (G *
          (∑ k ∈ S, ∑ l ∈ S,
            1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ)) +
        3 * G ^ 2 *
          (∑ k ∈ S, ∑ l ∈ S,
            1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))) := by
      have hlin := sum_pair_linear S S
        (fun k l ↦ 1 / (Nat.lcm (p ^ k) (p ^ l) : ℝ))
        (fun k l ↦ 1 / (((p ^ k) * (p ^ l) : ℕ) : ℝ))
        (e * G) (e * (3 * G ^ 2))
      convert hlin using 1 <;> ring
    _ ≤ e * (G * (quadraticHalfMass / (p : ℝ) ^ 2) +
        3 * G ^ 2 * (4 / (p : ℝ) ^ 4)) := by
      apply mul_le_mul_of_nonneg_left
      · apply add_le_add
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [S] using
              (sum_highExponents_pair_inv_lcm_le
                (p := p) (A := valuationCutoff p M) hp)) hG
        · exact mul_le_mul_of_nonneg_left
            (by simpa only [S] using
              (sum_highExponents_pair_inv_product_le
                (p := p) (A := valuationCutoff p M) hp)) (by positivity)
      · exact he
    _ = e * (G * quadraticHalfMass * (1 / (p : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p : ℝ)) ^ 4) := by ring

/-- The pointwise `JI` estimates aggregate over the actual prime band, with
the diagonal retained separately. -/
theorem sum_abs_covJI_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covJI p.1 q.1 - mu.covJI p.1 q.1|) ≤
      e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSum n W +
        e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
          6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covJI p.1 q.1 - mu.covJI p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (2 * G + 6 * G ^ 2) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covJI_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤ e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
      6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
    exact abs_covJI_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
              (1 / (q.1 : ℝ)) :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ)) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 2 * G + 6 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

/-- Transposing the same argument gives the `IJ` prime-band sum. -/
theorem sum_abs_covIJ_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covIJ p.1 q.1 - mu.covIJ p.1 q.1|) ≤
      e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
          bandReciprocalSquareSum n W +
        e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
          6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covIJ p.1 q.1 - mu.covIJ p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (2 * G + 6 * G ^ 2) *
        (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covIJ_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤ e * (2 * G * (1 / (p.1 : ℝ)) ^ 2 +
      6 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 3) := by
    exact abs_covIJ_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
          bandReciprocalSquareSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ)) *
              (1 / (q.1 : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ))) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (e * (2 * G + 6 * G ^ 2) * (1 / (p.1 : ℝ))) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 2 * G + 6 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_sq_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

/-- The `JJ` prime-band sum combines the distinct-prime product tail with
the exact diagonal lcm shell ledger. -/
theorem sum_abs_covJJ_sub_le_of_divisor_covariance_difference
    {Omega Theta : Type*} [Fintype Omega] [Fintype Theta]
    {M n W : ℕ}
    (nu : BoundedValuationLaw Omega M)
    (mu : BoundedValuationLaw Theta M)
    (p : BandPrime n W)
    {e G : ℝ} (he : 0 ≤ e) (hG : 0 ≤ G)
    (hcov : ∀ D E : ℕ, 0 < D → 0 < E →
      |nu.probability.covariance
            (fun x ↦ divInd D (nu.value x))
            (fun x ↦ divInd E (nu.value x)) -
        mu.probability.covariance
            (fun x ↦ divInd D (mu.value x))
            (fun x ↦ divInd E (mu.value x))| ≤
        e * (G * (1 / (Nat.lcm D E : ℝ)) +
          3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    (∑ q : BandPrime n W, |nu.covJJ p.1 q.1 - mu.covJJ p.1 q.1|) ≤
      e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSquareSum n W +
        e * (G * quadraticHalfMass * (1 / (p.1 : ℝ)) ^ 2 +
          12 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 4) := by
  let f : BandPrime n W → ℝ := fun q ↦
    |nu.covJJ p.1 q.1 - mu.covJJ p.1 q.1|
  have hoff (q : BandPrime n W) (hq : q ∈
      (Finset.univ : Finset (BandPrime n W)).erase p) :
      f q ≤ e * (4 * G + 12 * G ^ 2) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 := by
    have hne : p.1 ≠ q.1 := by
      intro hpq
      exact (Finset.mem_erase.mp hq).1 (Subtype.ext hpq.symm)
    exact abs_covJJ_sub_le_of_divisor_covariance_difference_of_ne
      nu mu (prime_of_mem_primeBand p.2) (prime_of_mem_primeBand q.2)
        hne he hG hcov
  have hdiag : f p ≤
      e * (G * quadraticHalfMass * (1 / (p.1 : ℝ)) ^ 2 +
        12 * G ^ 2 * (1 / (p.1 : ℝ)) ^ 4) := by
    exact abs_covJJ_sub_le_of_divisor_covariance_difference_diagonal
      nu mu (prime_of_mem_primeBand p.2) he hG hcov
  have herase :
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
        e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
          bandReciprocalSquareSum n W := by
    calc
      (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) ≤
          ∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2 *
              (1 / (q.1 : ℝ)) ^ 2 :=
        Finset.sum_le_sum fun q hq ↦ hoff q hq
      _ = (e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p,
            1 / (q.1 : ℝ) ^ 2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro q hq
        ring
      _ ≤ (e * (4 * G + 12 * G ^ 2) * (1 / (p.1 : ℝ)) ^ 2) *
          (∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left
        · exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) (fun _ _ _ ↦ by positivity)
        · have hcoef : 0 ≤ 4 * G + 12 * G ^ 2 := by
            nlinarith [sq_nonneg G]
          positivity
      _ = _ := by rw [sum_bandPrime_inv_sq_eq]
  change (∑ q : BandPrime n W, f q) ≤ _
  calc
    (∑ q : BandPrime n W, f q) =
        (∑ q ∈ (Finset.univ : Finset (BandPrime n W)).erase p, f q) +
          f p := (Finset.sum_erase_add _ _ (Finset.mem_univ p)).symm
    _ ≤ _ := add_le_add herase hdiag

/-- Component divisor estimates, after geometric aggregation, pass through
an arbitrary common tagged mixture.  This is the finite exact core of the
physical residual-tilt row comparison. -/
theorem sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
    {Cell : Type*} [Fintype Cell]
    {Omega : Cell → Type*} [∀ c, Fintype (Omega c)]
    {M n W : ℕ}
    (weight : FiniteProbability Cell)
    (mu nu : ∀ c, BoundedValuationLaw (Omega c) M)
    (p : BandPrime n W)
    {epsilon G : ℝ} (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G)
    (hW : 1 < W)
    (hbase : ∀ c D, 0 < D →
      (mu c).probability.expect
          (fun x ↦ divInd D ((mu c).value x)) ≤
        G * (1 / (D : ℝ)))
    (hdiff : ∀ c D, 0 < D →
      |(nu c).probability.expect
            (fun x ↦ divInd D ((nu c).value x)) -
        (mu c).probability.expect
            (fun x ↦ divInd D ((mu c).value x))| ≤
          (8 * epsilon) * G * (1 / (D : ℝ)))
    (hcov : ∀ c D E, 0 < D → 0 < E →
      |(nu c).probability.covariance
            (fun x ↦ divInd D ((nu c).value x))
            (fun x ↦ divInd E ((nu c).value x)) -
        (mu c).probability.covariance
            (fun x ↦ divInd D ((mu c).value x))
            (fun x ↦ divInd E ((mu c).value x))| ≤
        (8 * epsilon) *
          (G * (1 / (Nat.lcm D E : ℝ)) +
            3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))))) :
    let Mu := sigmaMixture weight mu
    let Nu := sigmaMixture weight nu
    (∑ q : BandPrime n W,
      |(Nu.covVV p.1 q.1 - Nu.covII p.1 q.1) -
        (Mu.covVV p.1 q.1 - Mu.covII p.1 q.1)|) ≤
      physicalPowerCorrectionMixtureBudget epsilon G n W p.1 := by
  dsimp only
  let e : ℝ := 8 * epsilon
  let H : ℝ := bandReciprocalSum n W
  let S₂ : ℝ := bandReciprocalSquareSum n W
  let w₁ : ℝ := 1 / (W : ℝ)
  let p₁ : ℝ := 1 / (p.1 : ℝ)
  let AIp := G * p₁
  let AJp := 2 * G * p₁ ^ 2
  let AIrow := G * H
  let AJrow := 2 * G * w₁
  let dIp := e * G * p₁
  let dJp := 2 * e * G * p₁ ^ 2
  let dIrow := e * G * H
  let dJrow := 2 * e * G * w₁
  let dJI := e * (2 * G + 6 * G ^ 2) * p₁ ^ 2 * H +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dIJ := e * (2 * G + 6 * G ^ 2) * p₁ * S₂ +
    e * (2 * G * p₁ ^ 2 + 6 * G ^ 2 * p₁ ^ 3)
  let dJJ := e * (4 * G + 12 * G ^ 2) * p₁ ^ 2 * S₂ +
    e * (G * quadraticHalfMass * p₁ ^ 2 + 12 * G ^ 2 * p₁ ^ 4)
  have he : 0 ≤ e := by dsimp only [e]; positivity
  have hH : 0 ≤ H := by dsimp only [H, bandReciprocalSum]; positivity
  have hS₂ : 0 ≤ S₂ := by
    dsimp only [S₂, bandReciprocalSquareSum]
    positivity
  have hw₁ : 0 ≤ w₁ := by dsimp only [w₁]; positivity
  have hp₁ : 0 ≤ p₁ := by dsimp only [p₁]; positivity
  have hAIp : 0 ≤ AIp := by dsimp only [AIp]; positivity
  have hAJp : 0 ≤ AJp := by dsimp only [AJp]; positivity
  have hAIrow : 0 ≤ AIrow := by dsimp only [AIrow]; positivity
  have hAJrow : 0 ≤ AJrow := by dsimp only [AJrow]; positivity
  have hdIp0 : 0 ≤ dIp := by dsimp only [dIp]; positivity
  have hdJp0 : 0 ≤ dJp := by dsimp only [dJp]; positivity
  have hIpBase (c : Cell) :
      |(mu c).probability.expect ((mu c).I p.1)| ≤ AIp := by
    have hnonneg := (mu c).probability.expect_nonneg ((mu c).I p.1)
      ((mu c).I_nonneg p.1)
    rw [abs_of_nonneg hnonneg]
    simpa only [BoundedValuationLaw.I, AIp, p₁, mul_assoc] using
      hbase c p.1 (prime_of_mem_primeBand p.2).pos
  have hJpBase (c : Cell) :
      |(mu c).probability.expect ((mu c).J p.1)| ≤ AJp := by
    have hpPrime := prime_of_mem_primeBand p.2
    have hnonneg := (mu c).probability.expect_nonneg ((mu c).J p.1)
      ((mu c).J_nonneg hpPrime)
    rw [abs_of_nonneg hnonneg]
    simpa only [AJp, p₁] using
      expect_J_le_of_divisor_fallback (mu c) hpPrime hG (hbase c)
  have hIqBase (c : Cell) :
      (∑ q : BandPrime n W,
        |(mu c).probability.expect ((mu c).I q.1)|) ≤ AIrow := by
    calc
      _ = ∑ q : BandPrime n W,
          (mu c).probability.expect ((mu c).I q.1) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [abs_of_nonneg ((mu c).probability.expect_nonneg _
          ((mu c).I_nonneg q.1))]
      _ ≤ ∑ q : BandPrime n W, G * (1 / (q.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [BoundedValuationLaw.I] using
          hbase c q.1 (prime_of_mem_primeBand q.2).pos
      _ = AIrow := by
        dsimp only [AIrow, H]
        rw [← Finset.mul_sum, sum_bandPrime_inv_eq]
  have hJqBase (c : Cell) :
      (∑ q : BandPrime n W,
        |(mu c).probability.expect ((mu c).J q.1)|) ≤ AJrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          2 * G * (1 / (q.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        have hqPrime := prime_of_mem_primeBand q.2
        rw [abs_of_nonneg ((mu c).probability.expect_nonneg _
          ((mu c).J_nonneg hqPrime))]
        exact expect_J_le_of_divisor_fallback
          (mu c) hqPrime hG (hbase c)
      _ = 2 * G * (∑ q : BandPrime n W,
          (1 / (q.1 : ℝ)) ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * G * S₂ := by
        dsimp only [S₂]
        apply congrArg (fun z : ℝ ↦ 2 * G * z)
        calc
          (∑ q : BandPrime n W, (1 / (q.1 : ℝ)) ^ 2) =
              ∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            ring
          _ = bandReciprocalSquareSum n W := sum_bandPrime_inv_sq_eq n W
      _ ≤ AJrow := by
        dsimp only [AJrow, w₁]
        exact mul_le_mul_of_nonneg_left
          (bandReciprocalSquareSum_le n W hW.le) (by positivity)
  have hIpDiff (c : Cell) :
      |(nu c).probability.expect ((nu c).I p.1) -
        (mu c).probability.expect ((mu c).I p.1)| ≤ dIp := by
    simpa only [BoundedValuationLaw.I, dIp, e, p₁, mul_assoc] using
      hdiff c p.1 (prime_of_mem_primeBand p.2).pos
  have hJpDiff (c : Cell) :
      |(nu c).probability.expect ((nu c).J p.1) -
        (mu c).probability.expect ((mu c).J p.1)| ≤ dJp := by
    have hraw := abs_expect_J_sub_le_of_divisor_difference
        (nu c) (mu c) (prime_of_mem_primeBand p.2)
          (mul_nonneg he hG) (by
            intro D hD
            dsimp only [e]
            simpa only [mul_assoc] using hdiff c D hD)
    dsimp only [dJp, e, p₁]
    convert hraw using 1
    ring
  have hIqDiff (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).probability.expect ((nu c).I q.1) -
          (mu c).probability.expect ((mu c).I q.1)|) ≤ dIrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          e * G * (1 / (q.1 : ℝ)) := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [BoundedValuationLaw.I, e, mul_assoc] using
          hdiff c q.1 (prime_of_mem_primeBand q.2).pos
      _ = dIrow := by
        dsimp only [dIrow, H]
        rw [← Finset.mul_sum, sum_bandPrime_inv_eq]
  have hJqDiff (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).probability.expect ((nu c).J q.1) -
          (mu c).probability.expect ((mu c).J q.1)|) ≤ dJrow := by
    calc
      _ ≤ ∑ q : BandPrime n W,
          2 * e * G * (1 / (q.1 : ℝ)) ^ 2 := by
        apply Finset.sum_le_sum
        intro q hq
        simpa only [mul_assoc] using
          abs_expect_J_sub_le_of_divisor_difference
            (nu c) (mu c) (prime_of_mem_primeBand q.2)
              (mul_nonneg he hG) (by
                intro D hD
                dsimp only [e]
                simpa only [mul_assoc] using hdiff c D hD)
      _ = 2 * e * G * (∑ q : BandPrime n W,
          (1 / (q.1 : ℝ)) ^ 2) := by rw [Finset.mul_sum]
      _ = 2 * e * G * S₂ := by
        dsimp only [S₂]
        apply congrArg (fun z : ℝ ↦ 2 * e * G * z)
        calc
          (∑ q : BandPrime n W, (1 / (q.1 : ℝ)) ^ 2) =
              ∑ q : BandPrime n W, 1 / (q.1 : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro q hq
            ring
          _ = bandReciprocalSquareSum n W := sum_bandPrime_inv_sq_eq n W
      _ ≤ dJrow := by
        dsimp only [dJrow, w₁]
        exact mul_le_mul_of_nonneg_left
          (bandReciprocalSquareSum_le n W hW.le) (by positivity)
  have hJI (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covJI p.1 q.1 - (mu c).covJI p.1 q.1|) ≤ dJI := by
    simpa only [dJI, e, H, p₁] using
      sum_abs_covJI_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hIJ (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covIJ p.1 q.1 - (mu c).covIJ p.1 q.1|) ≤ dIJ := by
    simpa only [dIJ, e, S₂, p₁] using
      sum_abs_covIJ_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hJJ (c : Cell) :
      (∑ q : BandPrime n W,
        |(nu c).covJJ p.1 q.1 - (mu c).covJJ p.1 q.1|) ≤ dJJ := by
    simpa only [dJJ, e, S₂, p₁] using
      sum_abs_covJJ_sub_le_of_divisor_covariance_difference
        (nu c) (mu c) p he hG (hcov c)
  have hmix :=
    FiniteProbability.sum_abs_boundedValuationSigmaMixture_powerCorrection_sub_le
      weight mu nu p.1 (fun q : BandPrime n W ↦ q.1)
      hAIp hAJp hAIrow hAJrow hdIp0 hdJp0
      hIpBase hJpBase hIqBase hJqBase hIpDiff hJpDiff
      hIqDiff hJqDiff hJI hIJ hJJ
  simpa only [physicalPowerCorrectionMixtureBudget, e, H, S₂, w₁,
    p₁, AIp, AJp, AIrow, AJrow, dIp, dJp, dIrow, dJrow,
    dJI, dIJ, dJJ] using hmix

/-- Concrete bridge specialization: the actual law is compared with the
medium-only law under exactly the actual post-tilt cell weights. -/
theorem sum_abs_actual_powerCorrection_sub_physicalMedium_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    (rho : Cell Head → ℝ)
    {A Aphys Kphys G : ℝ}
    (hA : 0 ≤ A) (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hG : 0 ≤ G) (hW : 1 < B.sampleData.W)
    (hrho : ∀ c, 0 < rho c)
    (hcard : ∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hGdom : ∀ c,
      Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c ≤ G)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (∑ q : BandPrime B.sampleData.n B.sampleData.W,
      |((B.actualValuationLaw xi).covVV p.1 q.1 -
          (B.actualValuationLaw xi).covII p.1 q.1) -
        ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
          (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) ≤
      physicalPowerCorrectionMixtureBudget
        (Aphys * Kphys / B.L) G
          B.sampleData.n B.sampleData.W p.1 := by
  let weight : FiniteProbability (Cell Head) :=
    tiltedSigmaWeight B.baselineCellProbability
      B.guardedCellProbability (B.scaledBridgeScore xi)
  let mu := B.mediumComponentValuationLaw xi
  let nu := B.actualComponentValuationLaw xi
  let epsilon := Aphys * Kphys / B.L
  have hepsilon : 0 ≤ epsilon := by
    dsimp only [epsilon]
    exact div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hbase (c : Cell Head) (D : ℕ) (hD : 0 < D) :
      (mu c).probability.expect (fun x ↦ divInd D ((mu c).value x)) ≤
        G * (1 / (D : ℝ)) := by
    have hraw := B.cellMediumLaw_expect_divInd_le xi c
      hD hA hW (hrho c) (hcard c) heta
    have hGc0 : 0 ≤ Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c := by
      exact div_nonneg (Real.exp_pos _).le (hrho c).le
    change (B.cellMediumLaw xi c).expect (fun x ↦ divInd D (x : ℕ)) ≤ _
    calc
      _ ≤ Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) /
            (rho c * (D : ℝ)) := hraw
      _ = (Real.exp (2 * ((A / B.L) *
          (Real.log (B.sampleData.hi c.2 : ℝ) /
            Real.log (B.sampleData.W : ℝ)))) / rho c) *
            (1 / (D : ℝ)) := by ring
      _ ≤ G * (1 / (D : ℝ)) :=
        mul_le_mul_of_nonneg_right (hGdom c) (by positivity)
  have hdiff (c : Cell Head) (D : ℕ) (hD : 0 < D) :
      |(nu c).probability.expect (fun x ↦ divInd D ((nu c).value x)) -
        (mu c).probability.expect (fun x ↦ divInd D ((mu c).value x))| ≤
          8 * epsilon * G * (1 / (D : ℝ)) := by
    have hraw := B.abs_guardedCell_fullTilt_expect_divInd_sub_medium_le
      xi c hD hA hW (hrho c) (hcard c) heta hAphys0 hKphys0
        hAphys (hKphys c) hsmall
    have hfactor0 : 0 ≤ 8 * epsilon * (1 / (D : ℝ)) := by positivity
    simpa only [nu, mu, actualComponentValuationLaw_probability,
      actualComponentValuationLaw_value,
      mediumComponentValuationLaw_probability,
      mediumComponentValuationLaw_value, epsilon, mul_assoc] using
      hraw.trans (by
        nlinarith [mul_le_mul_of_nonneg_left (hGdom c) hfactor0])
  have hcov (c : Cell Head) (D E : ℕ) (hD : 0 < D) (hE : 0 < E) :
      |(nu c).probability.covariance
            (fun x ↦ divInd D ((nu c).value x))
            (fun x ↦ divInd E ((nu c).value x)) -
        (mu c).probability.covariance
            (fun x ↦ divInd D ((mu c).value x))
            (fun x ↦ divInd E ((mu c).value x))| ≤
        8 * epsilon *
          (G * (1 / (Nat.lcm D E : ℝ)) +
            3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ)))) := by
    have hraw := B.abs_guardedCell_fullTilt_divIndCovariance_sub_medium_le
      xi c hD hE hA hW (hrho c) (hcard c) heta hAphys0 hKphys0
        hAphys (hKphys c) hsmall
    let Gc := Real.exp (2 * ((A / B.L) *
      (Real.log (B.sampleData.hi c.2 : ℝ) /
        Real.log (B.sampleData.W : ℝ)))) / rho c
    have hGc0 : 0 ≤ Gc := by
      dsimp only [Gc]
      exact div_nonneg (Real.exp_pos _).le (hrho c).le
    have hinside :
        Gc * (1 / (Nat.lcm D E : ℝ)) +
            3 * (Gc * (1 / (D : ℝ))) * (Gc * (1 / (E : ℝ))) ≤
          G * (1 / (Nat.lcm D E : ℝ)) +
            3 * (G * (1 / (D : ℝ))) * (G * (1 / (E : ℝ))) := by
      have hGcG : Gc ≤ G := by simpa only [Gc] using hGdom c
      have hlinear := mul_le_mul_of_nonneg_right hGcG (by positivity :
        0 ≤ (1 / (Nat.lcm D E : ℝ)))
      have hDmul := mul_le_mul_of_nonneg_right hGcG
        (by positivity : 0 ≤ (1 / (D : ℝ)))
      have hEmul := mul_le_mul_of_nonneg_right hGcG
        (by positivity : 0 ≤ (1 / (E : ℝ)))
      have hprod := mul_le_mul hDmul hEmul
        (mul_nonneg hGc0 (by positivity)) (mul_nonneg hG (by positivity))
      linarith
    have hscale0 : 0 ≤ 8 * epsilon := by positivity
    simpa only [nu, mu, actualComponentValuationLaw_probability,
      actualComponentValuationLaw_value,
      mediumComponentValuationLaw_probability,
      mediumComponentValuationLaw_value, epsilon, Gc] using
      hraw.trans (mul_le_mul_of_nonneg_left hinside hscale0)
  have hmix := sum_abs_sameWeight_powerCorrection_sub_le_of_divisor_bounds
    weight mu nu p hepsilon hG hW hbase hdiff hcov
  have hactual := B.sigmaMixture_actualComponentValuationLaw_eq_actualValuationLaw xi
  dsimp only at hactual
  simpa only [weight, mu, nu, epsilon, physicalMediumReferenceLaw,
    hactual] using hmix

/-- Literal weighted prime row for the residual physical tilt.  This is the
concrete `rhoPower` input used by the full-versus-squarefree bridge theorem. -/
theorem actual_powerCorrection_physicalMedium_weightedRow_le
    [Nonempty Head]
    (xi : B.ParamSpace)
    (rho : Cell Head → ℝ)
    {A Aphys Kphys G : ℝ}
    (hA : 0 ≤ A) (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hG : 0 ≤ G) (hW : 1 < B.sampleData.W)
    (hrho : ∀ c, 0 < rho c)
    (hcard : ∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hGdom : ∀ c,
      Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c ≤ G)
    (p : BandPrime B.sampleData.n B.sampleData.W) :
    (p.1 : ℝ) *
      (∑ q : BandPrime B.sampleData.n B.sampleData.W,
        |((B.actualValuationLaw xi).covVV p.1 q.1 -
            (B.actualValuationLaw xi).covII p.1 q.1) -
          ((B.physicalMediumReferenceLaw xi).covVV p.1 q.1 -
            (B.physicalMediumReferenceLaw xi).covII p.1 q.1)|) ≤
      physicalPowerCorrectionRowError
        (Aphys * Kphys / B.L) G
          B.sampleData.n B.sampleData.W := by
  have hepsilon : 0 ≤ Aphys * Kphys / B.L :=
    div_nonneg (mul_nonneg hAphys0 hKphys0) B.L_pos.le
  have hsum := B.sum_abs_actual_powerCorrection_sub_physicalMedium_le
    xi rho hA hAphys0 hKphys0 hG hW hrho hcard heta hAphys hKphys
      hsmall hGdom p
  have hscaled := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ (p.1 : ℝ) by positivity)
  exact hscaled.trans
    (physicalPowerCorrectionMixtureBudget_mul_le_rowError
      hepsilon hsmall hG hW p.2)

/-- Concrete specialization of the sharp full-versus-squarefree row theorem
to the residual-physical comparison law.  The reference Lemma 7.5
certificate and the actual/reference correction row are kept as visibly
separate inputs. -/
theorem abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_physicalMedium
    [Nonempty Head]
    (xi : B.ParamSpace)
    (rho : Cell Head → ℝ)
    {A Aphys Kphys G Cpow epsilon75 : ℝ}
    (hA : 0 ≤ A) (hAphys0 : 0 ≤ Aphys) (hKphys0 : 0 ≤ Kphys)
    (hG : 0 ≤ G) (hCpow : 0 ≤ Cpow) (hepsilon75 : 0 ≤ epsilon75)
    (hW : 1 < B.sampleData.W)
    (hrho : ∀ c, 0 < rho c)
    (hcard : ∀ c, rho c * (B.sampleData.hi c.2 : ℝ) ≤
      ((B.sampleData.cellFinset c).card : ℝ))
    (heta : ∀ r : BandPrime B.sampleData.n B.sampleData.W,
      |B.effectivePrimeCoefficient xi r| ≤ A)
    (hAphys : |xi MomentCoord.physical| ≤ Aphys)
    (hKphys : ∀ c (m : B.sampleData.SampleAt c),
      |B.physicalScore ⟨c, m⟩| ≤ Kphys)
    (hsmall : 8 * (Aphys * Kphys / B.L) ≤ 1)
    (hGdom : ∀ c,
      Real.exp (2 * ((A / B.L) *
        (Real.log (B.sampleData.hi c.2 : ℝ) /
          Real.log (B.sampleData.W : ℝ)))) / rho c ≤ G)
    (h75 : PaperPrimePowerLemma75.PrimePowerTransferBounds
      (B.physicalMediumReferenceLaw xi) B.sampleData.n B.sampleData.W
        Cpow epsilon75)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |PrimePowerSharpBandTransfer.fullSharpRow
          (B.actualValuationLaw xi) B.partition q i -
        SquarefreeSharpBandTransfer.squarefreeSharpRow
          (B.actualValuationLaw xi) B.partition q i| ≤
      3 * Cpow *
          (bandTReciprocalSum B.sampleData.n B.sampleData.W + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        3 * epsilon75 *
          (bandTReciprocalSum B.sampleData.n B.sampleData.W /
              B.partition.center i + 1) *
            (1 / (B.sampleData.W : ℝ)) +
        physicalPowerCorrectionRowError
            (Aphys * Kphys / B.L) G
              B.sampleData.n B.sampleData.W /
          B.partition.center i := by
  exact B.abs_actual_fullSharpRow_sub_squarefreeSharpRow_le_of_referencePowerCorrectionRow
    xi (B.physicalMediumReferenceLaw xi) hCpow hepsilon75 hW h75
      (B.actual_powerCorrection_physicalMedium_weightedRow_le
        xi rho hA hAphys0 hKphys0 hG hW hrho hcard heta hAphys hKphys
          hsmall hGdom)
      q hq i

end BridgeData

end

end Erdos390.Full.PaperBridgeFit
