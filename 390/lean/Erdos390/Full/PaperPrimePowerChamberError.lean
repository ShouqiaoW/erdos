import Erdos390.Full.FullTiltPrimePowerFallback
import Erdos390.Full.PaperValuationCutoff

/-!
# Explicit chamber-error majorants for prime-power aggregation

This file replaces the nested restoration ledger by one scalar remainder at
the natural product-reciprocal scale.  The scalar is explicit, uniform over
all moving primes and exponents, and retains the vanishing omitted-score and
`1 / log n` factors needed before the harmonic prime sum is taken.
-/

namespace Erdos390.Full.PaperPrimePowerChamberError

open ArithmeticModel Scale HeadPattern
open OmittedTiltPairChamber FullTiltPairChamber
open LocalFugacityBounds TwoLocalRestorationBound
open PaperTwoLocalRestorationBound PaperScaleMarkedCell
open FullTiltPrimePowerCovariance

noncomputable section

/-- The uniform pointwise coefficient-tail scalar. -/
def coefficientScale (B : ℝ) (W n : ℕ) : ℝ :=
  (2 * B / L n) * Real.exp (2 * B / Real.log (W : ℝ))

/-- The common reciprocal weight for an exponent pair. -/
def pairWeight (p q r s : ℕ) : ℝ :=
  (((r : ℝ) + 1) * ((s : ℝ) + 1)) /
    ((p : ℝ) ^ r * (q : ℝ) ^ s)

/-- The one-prime factor of `pairWeight`. -/
def singleWeight (p r : ℕ) : ℝ :=
  ((r : ℝ) + 1) / (p : ℝ) ^ r

theorem singleWeight_nonneg (p r : ℕ) : 0 ≤ singleWeight p r := by
  unfold singleWeight
  positivity

theorem pairWeight_eq_single_mul (p q r s : ℕ) :
    pairWeight p q r s = singleWeight p r * singleWeight q s := by
  unfold pairWeight singleWeight
  ring

theorem pairWeight_nonneg (p q r s : ℕ) :
    0 ≤ pairWeight p q r s := by
  unfold pairWeight
  positivity

/-- Scalar bounding every local-restoration numerator error. -/
def localRestorationScale (G k : ℝ) : ℝ :=
  G * (2 * k + k ^ 2)

/-- Scalar bounding one restored marked probability. -/
def pairProbabilityScale (epsilon G k : ℝ) : ℝ :=
  2 * (localRestorationScale G k + epsilon +
    (1 / DickmanBasic.rho DickmanBasic.U) * localRestorationScale G k)

/-- Scalar bounding the covariance perturbation formed from one joint and
two marginal probability errors. -/
def pairCovarianceScale (E : ℝ) : ℝ :=
  E * (1 + 2 * (1 / DickmanBasic.rho DickmanBasic.U)) + E ^ 2

/-- One remainder large enough for the `JI`, `IJ`, `JJ`, and diagonal
pointwise inputs of the finite aggregation theorem. -/
def aggregateChamberScale (epsilon G k : ℝ) : ℝ :=
  2 * pairCovarianceScale (pairProbabilityScale epsilon G k) +
    pairProbabilityScale epsilon G k

theorem localRestorationScale_nonneg {G k : ℝ}
    (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ localRestorationScale G k := by
  unfold localRestorationScale
  positivity

theorem pairProbabilityScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ pairProbabilityScale epsilon G k := by
  unfold pairProbabilityScale
  have hlocal := localRestorationScale_nonneg hG hk
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem pairCovarianceScale_nonneg {E : ℝ} (hE : 0 ≤ E) :
    0 ≤ pairCovarianceScale E := by
  unfold pairCovarianceScale
  have hrho : 0 ≤ 1 / DickmanBasic.rho DickmanBasic.U := by
    exact one_div_nonneg.mpr DickmanBasic.rho_U_pos.le
  positivity

theorem aggregateChamberScale_nonneg {epsilon G k : ℝ}
    (hepsilon : 0 ≤ epsilon) (hG : 0 ≤ G) (hk : 0 ≤ k) :
    0 ≤ aggregateChamberScale epsilon G k := by
  unfold aggregateChamberScale
  have hE := pairProbabilityScale_nonneg hepsilon hG hk
  exact add_nonneg (mul_nonneg (by norm_num) (pairCovarianceScale_nonneg hE)) hE

/-- Two pointwise coefficient-tail bounds imply a product-weighted bound
for the complete two-local restoration error. -/
theorem pairRestorationError_le_pairWeight
    {p q Ap Aq r s : ℕ} {etaP etaQ L₀ G G₀ k : ℝ}
    (hG : G ≤ G₀) (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hpTail : coefficientTail p Ap r etaP L₀ ≤
      k * (((r : ℝ) + 1) / (p : ℝ) ^ r))
    (hqTail : coefficientTail q Aq s etaQ L₀ ≤
      k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :
    pairRestorationError p q Ap Aq r s etaP etaQ L₀ G ≤
      localRestorationScale G₀ k * pairWeight p q r s := by
  let dp := coefficientTail p Ap r etaP L₀
  let dq := coefficientTail q Aq s etaQ L₀
  have hdp0 : 0 ≤ dp := coefficientTail_nonneg _ _ _ _ _
  have hdq0 : 0 ≤ dq := coefficientTail_nonneg _ _ _ _ _
  have hpden0 : 0 ≤ (p : ℝ) ^ r := by positivity
  have hqden0 : 0 ≤ (q : ℝ) ^ s := by positivity
  have hpInv0 : 0 ≤ 1 / (p : ℝ) ^ r := by positivity
  have hqInv0 : 0 ≤ 1 / (q : ℝ) ^ s := by positivity
  have hdp : dp ≤ k * (((r : ℝ) + 1) / (p : ℝ) ^ r) := hpTail
  have hdq : dq ≤ k * (((s : ℝ) + 1) / (q : ℝ) ^ s) := hqTail
  have hGdp : G * dp ≤
      G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r)) :=
    mul_le_mul hG hdp hdp0 hG₀
  have hGdq : G * dq ≤
      G₀ * (k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :=
    mul_le_mul hG hdq hdq0 hG₀
  have htermP : G * dp * (1 / (q : ℝ) ^ s) ≤
      G₀ * k * pairWeight p q r s := by
    calc
      G * dp * (1 / (q : ℝ) ^ s) ≤
          (G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r))) *
            (1 / (q : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_right hGdp hqInv0
      _ = (G₀ * k * ((r : ℝ) + 1) *
          (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s)) := by ring
      _ ≤ (G₀ * k * ((r : ℝ) + 1) *
          (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s)) *
            ((s : ℝ) + 1) := by
        have hbase : 0 ≤ G₀ * k * ((r : ℝ) + 1) *
            (1 / (p : ℝ) ^ r) * (1 / (q : ℝ) ^ s) := by positivity
        nlinarith
      _ = G₀ * k * pairWeight p q r s := by
        unfold pairWeight
        ring
  have htermQ : G * (1 / (p : ℝ) ^ r) * dq ≤
      G₀ * k * pairWeight p q r s := by
    calc
      G * (1 / (p : ℝ) ^ r) * dq = (G * dq) *
          (1 / (p : ℝ) ^ r) := by ring
      _ ≤ (G₀ * (k * (((s : ℝ) + 1) / (q : ℝ) ^ s))) *
          (1 / (p : ℝ) ^ r) :=
        mul_le_mul_of_nonneg_right hGdq hpInv0
      _ = (G₀ * k * ((s : ℝ) + 1) *
          (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r)) := by ring
      _ ≤ (G₀ * k * ((s : ℝ) + 1) *
          (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r)) *
            ((r : ℝ) + 1) := by
        have hbase : 0 ≤ G₀ * k * ((s : ℝ) + 1) *
            (1 / (q : ℝ) ^ s) * (1 / (p : ℝ) ^ r) := by positivity
        nlinarith
      _ = G₀ * k * pairWeight p q r s := by
        unfold pairWeight
        ring
  have htermPQ : G * dp * dq ≤
      G₀ * k ^ 2 * pairWeight p q r s := by
    calc
      G * dp * dq ≤
          (G₀ * (k * (((r : ℝ) + 1) / (p : ℝ) ^ r))) *
            (k * (((s : ℝ) + 1) / (q : ℝ) ^ s)) :=
        mul_le_mul hGdp hdq hdq0 (by positivity)
      _ = G₀ * k ^ 2 * pairWeight p q r s := by
        unfold pairWeight
        ring
  unfold pairRestorationError localRestorationScale
  dsimp only [dp, dq] at htermP htermQ htermPQ
  calc
    _ ≤ G₀ * k * pairWeight p q r s +
        G₀ * k * pairWeight p q r s +
          G₀ * k ^ 2 * pairWeight p q r s :=
      add_le_add_three htermP htermQ htermPQ
    _ = G₀ * (2 * k + k ^ 2) * pairWeight p q r s := by ring

/-- A small algebraic adapter used for the main-times-restoration term.
Keeping this estimate separate makes all sign assumptions explicit. -/
theorem abs_mul_le_scaled_weight
    {a b R E dInv w : ℝ}
    (ha : |a| ≤ R * dInv) (hb₀ : 0 ≤ b) (hb : b ≤ E)
    (hR : 0 ≤ R) (hE : 0 ≤ E) (hdInv : 0 ≤ dInv)
    (hdInvw : dInv ≤ w) :
    |a| * b ≤ (R * E) * w := by
  have hprod : |a| * b ≤ (R * dInv) * E :=
    mul_le_mul ha hb hb₀ (mul_nonneg hR hdInv)
  have hscale : 0 ≤ R * E := mul_nonneg hR hE
  calc
    |a| * b ≤ (R * dInv) * E := hprod
    _ = (R * E) * dInv := by ring
    _ ≤ (R * E) * w := mul_le_mul_of_nonneg_left hdInvw hscale

/-- Algebraic closure of a joint-probability error and two marginal errors
into the covariance-error scalar used below. -/
theorem covariance_error_algebra
    {E R sp sq Ers Er Es Mr Ms : ℝ}
    (hE : 0 ≤ E) (hsp : 0 ≤ sp) (hsq : 0 ≤ sq)
    (hEs₀ : 0 ≤ Es)
    (hErs : Ers ≤ E * (sp * sq))
    (hEr : Er ≤ E * sp) (hEs : Es ≤ E * sq)
    (hMr : |Mr| ≤ R * sp) (hMs : |Ms| ≤ R * sq) :
    Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
      (E * (1 + 2 * R) + E ^ 2) * (sp * sq) := by
  have hErMs : Er * |Ms| ≤ (E * sp) * (R * sq) :=
    mul_le_mul hEr hMs (abs_nonneg Ms) (mul_nonneg hE hsp)
  have hEsMr : Es * |Mr| ≤ (E * sq) * (R * sp) :=
    mul_le_mul hEs hMr (abs_nonneg Mr) (mul_nonneg hE hsq)
  have hErEs : Er * Es ≤ (E * sp) * (E * sq) :=
    mul_le_mul hEr hEs hEs₀ (mul_nonneg hE hsp)
  calc
    Ers + Er * |Ms| + Es * |Mr| + Er * Es ≤
        E * (sp * sq) + (E * sp) * (R * sq) +
          (E * sq) * (R * sp) + (E * sp) * (E * sq) := by
      exact add_le_add (add_le_add (add_le_add hErs hErMs) hEsMr) hErEs
    _ = (E * (1 + 2 * R) + E ^ 2) * (sp * sq) := by ring

/-- The reciprocal main term is controlled by the natural one-prime weight. -/
theorem abs_paperDivisibilityMain_pow_le_singleWeight
    {n p r : ℕ} (hn : 1 < n) (hp : Nat.Prime p)
    (hD4 : p ^ r ≤ yNat n ^ 4) :
    |paperDivisibilityMain n (p ^ r)| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
  have hDpos : 0 < p ^ r := pow_pos hp.pos r
  have hraw := paperDivisibilityMain_nonneg_le hn hDpos hD4
  rw [abs_of_nonneg hraw.1]
  have hinv : 1 / (p : ℝ) ^ r ≤ singleWeight p r := by
    unfold singleWeight
    have hden : 0 ≤ (p : ℝ) ^ r := by positivity
    have hnum : (1 : ℝ) ≤ (r : ℝ) + 1 := by
      nlinarith [show (0 : ℝ) ≤ r by positivity]
    exact div_le_div_of_nonneg_right hnum hden
  calc
    paperDivisibilityMain n (p ^ r) ≤
        1 / (DickmanBasic.rho DickmanBasic.U * (p ^ r : ℕ)) := hraw.2
    _ = (1 / DickmanBasic.rho DickmanBasic.U) *
        (1 / (p : ℝ) ^ r) := by
      norm_num only [Nat.cast_pow]
      ring
    _ ≤ (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r :=
      mul_le_mul_of_nonneg_left hinv
        (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)

/-- The explicit full-pair probability error is bounded by one scalar times
the natural product weight. -/
theorem fullPairChamberError_le_pairWeight
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) {G₀ k : ℝ}
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4)
    (hepsilon : 0 ≤ epsilon n)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hG : paperPairFallbackConstant B C (pairFallbackDensity H A C) W n ≤ G₀)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
      coefficientTail z (ValuationCutoff.valuationCutoff z (physicalBound C n))
        u (eta z) (L n) ≤
          k * (((u : ℝ) + 1) / (z : ℝ) ^ u)) :
    fullPairChamberError H A C B W n p q r s eta epsilon ≤
      pairProbabilityScale (epsilon n) G₀ k * pairWeight p q r s := by
  let G := paperPairFallbackConstant B C (pairFallbackDensity H A C) W n
  let Ap := ValuationCutoff.valuationCutoff p (physicalBound C n)
  let Aq := ValuationCutoff.valuationCutoff q (physicalBound C n)
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hG0 : 0 ≤ G := paperPairFallbackConstant_nonneg _ _ _ _ _ hc
  have hrs := pairRestorationError_le_pairWeight hG hG₀ hk
    (hcoef p hpBand r) (hcoef q hqBand s)
  have h00raw := pairRestorationError_le_pairWeight hG hG₀ hk
    (hcoef p hpBand 0) (hcoef q hqBand 0)
  have hweight00 : pairWeight p q 0 0 = 1 := by
    simp [pairWeight]
  have h00 : pairRestorationError p q Ap Aq 0 0
      (eta p) (eta q) (L n) G ≤ localRestorationScale G₀ k := by
    simpa only [Ap, Aq, G, hweight00, mul_one] using h00raw
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hmainRaw := paperDivisibilityMain_nonneg_le hn hDpos hD4
  have hmain : |paperDivisibilityMain n (pairPower p q r s)| ≤
      (1 / DickmanBasic.rho DickmanBasic.U) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
    rw [abs_of_nonneg hmainRaw.1]
    convert hmainRaw.2 using 1
    all_goals
      simp only [pairPower, Nat.cast_mul, Nat.cast_pow]
      ring
  have hweightOne :
      1 / ((p : ℝ) ^ r * (q : ℝ) ^ s) ≤ pairWeight p q r s := by
    unfold pairWeight
    have hden0 : 0 ≤ (p : ℝ) ^ r * (q : ℝ) ^ s := by positivity
    have hnum : (1 : ℝ) ≤ ((r : ℝ) + 1) * ((s : ℝ) + 1) := by
      nlinarith [show (0 : ℝ) ≤ r by positivity,
        show (0 : ℝ) ≤ s by positivity]
    exact div_le_div_of_nonneg_right hnum hden0
  have heps : epsilon n / (pairPower p q r s : ℝ) ≤
      epsilon n * pairWeight p q r s := by
    norm_num only [pairPower, Nat.cast_mul, Nat.cast_pow]
    have hmul := mul_le_mul_of_nonneg_left hweightOne hepsilon
    simpa [div_eq_mul_inv] using hmul
  calc
    fullPairChamberError H A C B W n p q r s eta epsilon =
        2 * (pairRestorationError p q Ap Aq r s
            (eta p) (eta q) (L n) G +
          epsilon n / (pairPower p q r s : ℝ) +
          |paperDivisibilityMain n (pairPower p q r s)| *
            pairRestorationError p q Ap Aq 0 0
              (eta p) (eta q) (L n) G) := by
      rfl
    _ ≤ 2 * (localRestorationScale G₀ k * pairWeight p q r s +
        epsilon n * pairWeight p q r s +
        ((1 / DickmanBasic.rho DickmanBasic.U) *
          localRestorationScale G₀ k) * pairWeight p q r s) := by
      exact mul_le_mul_of_nonneg_left
        (add_le_add_three hrs heps
          (abs_mul_le_scaled_weight
            (by simpa [div_eq_mul_inv] using hmain)
            (pairRestorationError_nonneg _ _ _ _ _ _ _ _ _ _ hG0) h00
            (one_div_nonneg.mpr DickmanBasic.rho_U_pos.le)
            (localRestorationScale_nonneg hG₀ hk) (by positivity)
            hweightOne))
        (by norm_num)
    _ = pairProbabilityScale (epsilon n) G₀ k *
        pairWeight p q r s := by
      unfold pairProbabilityScale
      ring

/-- The complete explicit covariance ledger is bounded by the scalar
`pairCovarianceScale` at the natural product-reciprocal weight.  The chamber
hypothesis is the literal arithmetic cutoff; the two marginal cutoffs are
deduced by divisibility. -/
theorem fullPrimePowerCovarianceError_le_pairWeight
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) {G₀ k : ℝ}
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqBand : q ∈ primeBand n W)
    (hD4 : pairPower p q r s ≤ yNat n ^ 4)
    (hepsilon : 0 ≤ epsilon n)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hG : paperPairFallbackConstant B C (pairFallbackDensity H A C) W n ≤ G₀)
    (hG₀ : 0 ≤ G₀) (hk : 0 ≤ k)
    (hcoef : ∀ z ∈ primeBand n W, ∀ u : ℕ,
      coefficientTail z (ValuationCutoff.valuationCutoff z (physicalBound C n))
        u (eta z) (L n) ≤
          k * (((u : ℝ) + 1) / (z : ℝ) ^ u)) :
    fullPrimePowerCovarianceError H A C B W n p q r s eta epsilon ≤
      pairCovarianceScale (pairProbabilityScale (epsilon n) G₀ k) *
        pairWeight p q r s := by
  let E := pairProbabilityScale (epsilon n) G₀ k
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have hDpos : 0 < pairPower p q r s := pairPower_pos hp hq
  have hdivP : pairPower p q r 0 ∣ pairPower p q r s := by
    refine ⟨q ^ s, ?_⟩
    simp only [pairPower, pow_zero, mul_one]
  have hdivQ : pairPower p q 0 s ∣ pairPower p q r s := by
    refine ⟨p ^ r, ?_⟩
    simp only [pairPower, pow_zero, one_mul]
    exact (mul_comm (q ^ s) (p ^ r)).symm
  have hD4P : pairPower p q r 0 ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivP).trans hD4
  have hD4Q : pairPower p q 0 s ≤ yNat n ^ 4 :=
    (Nat.le_of_dvd hDpos hdivQ).trans hD4
  have hE : 0 ≤ E := pairProbabilityScale_nonneg hepsilon hG₀ hk
  have hErs := fullPairChamberError_le_pairWeight H eta epsilon hn hpBand
    hqBand hD4 hepsilon hc hG hG₀ hk hcoef
  have hErRaw := fullPairChamberError_le_pairWeight H eta epsilon hn hpBand
    hqBand hD4P hepsilon hc hG hG₀ hk hcoef
  have hEsRaw := fullPairChamberError_le_pairWeight H eta epsilon hn hpBand
    hqBand hD4Q hepsilon hc hG hG₀ hk hcoef
  have hEr :
      fullPairChamberError H A C B W n p q r 0 eta epsilon ≤
        E * singleWeight p r := by
    simpa only [E, pairWeight_eq_single_mul, singleWeight, Nat.cast_zero,
      zero_add, pow_zero, div_one, mul_one] using hErRaw
  have hEs :
      fullPairChamberError H A C B W n p q 0 s eta epsilon ≤
        E * singleWeight q s := by
    simpa only [E, pairWeight_eq_single_mul, singleWeight, Nat.cast_zero,
      zero_add, pow_zero, div_one, one_mul] using hEsRaw
  have hMr :
      |paperDivisibilityMain n (pairPower p q r 0)| ≤
        (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight p r := by
    simpa only [pairPower, pow_zero, mul_one] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hp
        (by simpa only [pairPower, pow_zero, mul_one] using hD4P)
  have hMs :
      |paperDivisibilityMain n (pairPower p q 0 s)| ≤
        (1 / DickmanBasic.rho DickmanBasic.U) * singleWeight q s := by
    simpa only [pairPower, pow_zero, one_mul] using
      abs_paperDivisibilityMain_pow_le_singleWeight hn hq
        (by simpa only [pairPower, pow_zero, one_mul] using hD4Q)
  have hEs₀ : 0 ≤ fullPairChamberError H A C B W n p q 0 s eta epsilon :=
    fullPairChamberError_nonneg H A C B W n p q 0 s eta epsilon hc hepsilon
  unfold fullPrimePowerCovarianceError
  dsimp only
  rw [pairWeight_eq_single_mul]
  unfold pairCovarianceScale
  exact covariance_error_algebra hE
    (singleWeight_nonneg p r) (singleWeight_nonneg q s) hEs₀
    (by simpa only [E, pairWeight_eq_single_mul] using hErs)
    hEr hEs hMr hMs

end

end Erdos390.Full.PaperPrimePowerChamberError
