import Erdos390.Full.FullTiltPairChamber
import Erdos390.Full.DickmanFourMarkProductKernel
import Erdos390.Full.StructuredCellValuationLaw
import Erdos390.Full.PaperPrimePowerRow

/-!
# Genuine full-tilt prime-power covariance in the four-mark chamber

This module converts the actual full-tilt divisor-probability theorem into a
covariance estimate.  The product-error algebra keeps both marginal divisor
scales; it does not use the lossy bound `P(D) <= 1`.  The deterministic main
covariance is then controlled by the proved box-independent Dickman product
kernel.
-/

open Filter Topology
open scoped BigOperators

namespace Erdos390.Full.FullTiltPrimePowerCovariance

open ArithmeticModel Scale HeadPattern StructuredCells
open FiniteProbability PrimePowerCovariance
open PaperScaleMarkedCell
open OmittedTiltPairChamber TwoLocalPairRestoration
open FullTiltPairChamber DickmanFourMarkProductKernel
open StructuredCellValuationLaw

noncomputable section

/-- The paper main term for `p^r q^s`, in the normalized Dickman-profile
form used by the product-kernel estimate. -/
theorem paperDivisibilityMain_pairPower_eq_profile
    {n p q r s : ℕ} (hn : 1 < n) (hp : p.Prime) (hq : q.Prime) :
    paperDivisibilityMain n (pairPower p q r s) =
      fourMarkProfile
          ((r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hylog : Real.log (y n) ≠ 0 := by
    have hypos : 0 < Real.log (y n) := by
      rw [log_y (Nat.zero_lt_of_lt hn)]
      exact mul_pos (by norm_num) (L_pos hn)
    exact hypos.ne'
  have hcast : ((pairPower p q r s : ℕ) : ℝ) =
      (p : ℝ) ^ r * (q : ℝ) ^ s := by
    simp [pairPower]
  have hlog : Real.log ((pairPower p q r s : ℕ) : ℝ) =
      (r : ℝ) * Real.log (p : ℝ) +
        (s : ℝ) * Real.log (q : ℝ) := by
    rw [hcast, Real.log_mul (pow_ne_zero r hpR) (pow_ne_zero s hqR),
      Real.log_pow, Real.log_pow]
  have hcoord : paperDivisorCoordinate n (pairPower p q r s) =
      DickmanBasic.U -
        ((r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q) := by
    unfold paperDivisorCoordinate tPrime
    rw [hlog]
    field_simp [hylog]
  unfold paperDivisibilityMain fourMarkProfile
  rw [hcoord, hcast]

/-- Exact algebraic relation between a two-prime divisor covariance and the
three corresponding divisor probabilities. -/
theorem covariance_primePowers_eq_pairProbability_sub
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime) :
    mu.covariance
        (fun omega ↦ divInd (p ^ r) (value omega))
        (fun omega ↦ divInd (q ^ s) (value omega)) =
      mu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)) -
        mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) *
          mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) := by
  unfold FiniteProbability.covariance
  congr 2
  funext omega
  simpa only [pairPower, pow_zero, mul_one, one_mul,
    max_eq_left (Nat.zero_le _), max_eq_right (Nat.zero_le _)] using
    (divInd_pairPower_mul (m := value omega)
      (r := r) (s := 0) (a := 0) (b := s) hpq hp hq)

/-- Stable product perturbation.  The cross term `Er*Es` is retained, so
each marginal error keeps the reciprocal scale of the other prime. -/
theorem abs_primePower_covariance_sub_mainCov_le
    {Omega : Type*} [Fintype Omega] (mu : FiniteProbability Omega)
    (value : Omega → ℕ) {p q r s : ℕ}
    (hpq : p ≠ q) (hp : p.Prime) (hq : q.Prime)
    {Mrs Mr Ms Ers Er Es : ℝ}
    (hEr : 0 ≤ Er)
    (hpair : |mu.expect (fun omega ↦
        divInd (pairPower p q r s) (value omega)) - Mrs| ≤ Ers)
    (hpr : |mu.expect (fun omega ↦ divInd (p ^ r) (value omega)) - Mr| ≤ Er)
    (hqs : |mu.expect (fun omega ↦ divInd (q ^ s) (value omega)) - Ms| ≤ Es) :
    |mu.covariance
          (fun omega ↦ divInd (p ^ r) (value omega))
          (fun omega ↦ divInd (q ^ s) (value omega)) -
        (Mrs - Mr * Ms)| ≤
      Ers + Er * |Ms| + Es * |Mr| + Er * Es := by
  let Prs := mu.expect (fun omega ↦
    divInd (pairPower p q r s) (value omega))
  let Pr := mu.expect (fun omega ↦ divInd (p ^ r) (value omega))
  let Ps := mu.expect (fun omega ↦ divInd (q ^ s) (value omega))
  have hcov := covariance_primePowers_eq_pairProbability_sub
    mu value hpq hp hq (r := r) (s := s)
  have hPs : |Ps| ≤ |Ms| + Es := by
    calc
      |Ps| = |(Ps - Ms) + Ms| := by ring_nf
      _ ≤ |Ps - Ms| + |Ms| := abs_add_le _ _
      _ ≤ Es + |Ms| := add_le_add hqs le_rfl
      _ = |Ms| + Es := by ring
  have hprod : |Pr * Ps - Mr * Ms| ≤
      Er * |Ms| + Es * |Mr| + Er * Es := by
    have hid : Pr * Ps - Mr * Ms = (Pr - Mr) * Ps + Mr * (Ps - Ms) := by
      ring
    rw [hid]
    calc
      |(Pr - Mr) * Ps + Mr * (Ps - Ms)| ≤
          |(Pr - Mr) * Ps| + |Mr * (Ps - Ms)| := abs_add_le _ _
      _ = |Pr - Mr| * |Ps| + |Mr| * |Ps - Ms| := by
        rw [abs_mul, abs_mul]
      _ ≤ Er * (|Ms| + Es) + |Mr| * Es := by
        exact add_le_add
          (mul_le_mul hpr hPs (abs_nonneg _) hEr)
          (mul_le_mul_of_nonneg_left hqs (abs_nonneg Mr))
      _ = Er * |Ms| + Es * |Mr| + Er * Es := by ring
  rw [hcov]
  change |(Prs - Pr * Ps) - (Mrs - Mr * Ms)| ≤ _
  have hid : (Prs - Pr * Ps) - (Mrs - Mr * Ms) =
      (Prs - Mrs) - (Pr * Ps - Mr * Ms) := by ring
  rw [hid]
  calc
    |(Prs - Mrs) - (Pr * Ps - Mr * Ms)| ≤
        |Prs - Mrs| + |Pr * Ps - Mr * Ms| := abs_sub _ _
    _ ≤ Ers + (Er * |Ms| + Es * |Mr| + Er * Es) :=
      add_le_add hpair hprod
    _ = Ers + Er * |Ms| + Es * |Mr| + Er * Es := by ring

/-- Exact deterministic covariance of the three paper main terms. -/
theorem paperMainCovariance_eq_profileKernel
    {n p q r s : ℕ} (hn : 1 < n) (hp : p.Prime) (hq : q.Prime) :
    paperDivisibilityMain n (pairPower p q r s) -
        paperDivisibilityMain n (pairPower p q r 0) *
          paperDivisibilityMain n (pairPower p q 0 s) =
      (fourMarkProfile
          ((r : ℝ) * tPrime n p + (s : ℝ) * tPrime n q) -
        fourMarkProfile ((r : ℝ) * tPrime n p) *
          fourMarkProfile ((s : ℝ) * tPrime n q)) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  rw [paperDivisibilityMain_pairPower_eq_profile hn hp hq,
    paperDivisibilityMain_pairPower_eq_profile (r := r) (s := 0) hn hp hq,
    paperDivisibilityMain_pairPower_eq_profile (r := 0) (s := s) hn hp hq]
  simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, pow_zero, mul_one,
    one_mul]
  ring

/-- The deterministic paper-main covariance has the desired `xz/(p^r q^s)`
bound throughout the complete four-mark simplex. -/
theorem abs_paperMainCovariance_le
    {C_K : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) -
          fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z)
    {n W p q r s : ℕ} (hn : 1 < n)
    (hpBand : p ∈ primeBand n W) (hqBand : q ∈ primeBand n W)
    (hrs : r + s ≤ 4) :
    |paperDivisibilityMain n (pairPower p q r s) -
        paperDivisibilityMain n (pairPower p q r 0) *
          paperDivisibilityMain n (pairPower p q 0 s)| ≤
      C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
        ((p : ℝ) ^ r * (q : ℝ) ^ s) := by
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  have htp0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hpBand
  have htq0 := PaperPrimePowerRow.tPrime_nonneg_of_mem_primeBand hn hqBand
  have htp1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn hpBand
  have htq1 := PaperPrimePowerRow.tPrime_le_one_of_mem_primeBand hn hqBand
  let x : ℝ := (r : ℝ) * tPrime n p
  let z : ℝ := (s : ℝ) * tPrime n q
  have hx0 : 0 ≤ x := by dsimp only [x]; positivity
  have hz0 : 0 ≤ z := by dsimp only [z]; positivity
  have hxle : x ≤ (r : ℝ) := by
    dsimp only [x]
    nlinarith [mul_le_mul_of_nonneg_left htp1 (show 0 ≤ (r : ℝ) by positivity)]
  have hzle : z ≤ (s : ℝ) := by
    dsimp only [z]
    nlinarith [mul_le_mul_of_nonneg_left htq1 (show 0 ≤ (s : ℝ) by positivity)]
  have hrsR : (r : ℝ) + (s : ℝ) ≤ 4 := by exact_mod_cast hrs
  have hxz4 : x + z ≤ 4 := by linarith
  rw [paperMainCovariance_eq_profileKernel hn hp hq]
  rw [abs_div]
  have hpRpos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hqRpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq.pos
  have hdenpos : 0 < (p : ℝ) ^ r * (q : ℝ) ^ s :=
    mul_pos (pow_pos hpRpos r) (pow_pos hqRpos s)
  rw [abs_of_pos hdenpos]
  exact div_le_div_of_nonneg_right (hkernel x z hx0 hz0 hxz4) hdenpos.le

/-- The explicit covariance-error ledger formed from the three genuine
full-tilt probability errors. -/
def fullPrimePowerCovarianceError
    (H : Pattern) (A C B : ℝ) (W n p q r s : ℕ)
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ) : ℝ :=
  let Ers := fullPairChamberError H A C B W n p q r s eta epsilon
  let Er := fullPairChamberError H A C B W n p q r 0 eta epsilon
  let Es := fullPairChamberError H A C B W n p q 0 s eta epsilon
  Ers + Er * |paperDivisibilityMain n (pairPower p q 0 s)| +
    Es * |paperDivisibilityMain n (pairPower p q r 0)| + Er * Es

theorem fullPrimePowerCovarianceError_nonneg
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ)
    (hc : 0 ≤ pairFallbackDensity H A C) (hepsilon : 0 ≤ epsilon n) :
    0 ≤ fullPrimePowerCovarianceError H A C B W n p q r s eta epsilon := by
  unfold fullPrimePowerCovarianceError
  dsimp only
  have hrs := fullPairChamberError_nonneg H A C B W n p q r s eta epsilon
    hc hepsilon
  have hr := fullPairChamberError_nonneg H A C B W n p q r 0 eta epsilon
    hc hepsilon
  have hs := fullPairChamberError_nonneg H A C B W n p q 0 s eta epsilon
    hc hepsilon
  positivity

/-- Fixed-parameter conversion of three actual full-tilt probability bounds
into the pointwise prime-power covariance bound. -/
theorem fullTilt_primePower_covariance_le
    {C_K : ℝ}
    (hkernel : ∀ x z : ℝ, 0 ≤ x → 0 ≤ z → x + z ≤ 4 →
      |fourMarkProfile (x + z) -
          fourMarkProfile x * fourMarkProfile z| ≤ C_K * x * z)
    (H : Pattern) {A C B : ℝ} {W n p q r s : ℕ}
    (eta : ℕ → ℝ) (epsilon : ℕ → ℝ)
    (hn : 1 < n) (hpBand : p ∈ primeBand n W)
    (hqErase : q ∈ (primeBand n W).erase p) (hrs : r + s ≤ 4)
    (hS : (structuredCell H (physicalBound A n) (physicalBound C n)
      (yNat n)).Nonempty)
    (hc : 0 ≤ pairFallbackDensity H A C)
    (hepsilon : 0 ≤ epsilon n)
    (hpair : |(valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q r s) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q r s)| ≤
      fullPairChamberError H A C B W n p q r s eta epsilon)
    (hpr : |(valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q r 0) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q r 0)| ≤
      fullPairChamberError H A C B W n p q r 0 eta epsilon)
    (hqs : |(valuationTilt H (physicalBound A n) (physicalBound C n)
        (yNat n) hS (primeBand n W) eta (L n)).probability.expect
          (fun m ↦ divInd (pairPower p q 0 s) (m : ℕ)) -
        paperDivisibilityMain n (pairPower p q 0 s)| ≤
      fullPairChamberError H A C B W n p q 0 s eta epsilon) :
    let law := valuationTilt H (physicalBound A n) (physicalBound C n)
      (yNat n) hS (primeBand n W) eta (L n)
    |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
      C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
          ((p : ℝ) ^ r * (q : ℝ) ^ s) +
        fullPrimePowerCovarianceError H A C B W n p q r s eta epsilon := by
  dsimp only
  let law := valuationTilt H (physicalBound A n) (physicalBound C n)
    (yNat n) hS (primeBand n W) eta (L n)
  have hqBand : q ∈ primeBand n W := (Finset.mem_erase.mp hqErase).2
  have hpq : p ≠ q := (Finset.mem_erase.mp hqErase).1.symm
  have hp := prime_of_mem_primeBand hpBand
  have hq := prime_of_mem_primeBand hqBand
  let Ers := fullPairChamberError H A C B W n p q r s eta epsilon
  let Er := fullPairChamberError H A C B W n p q r 0 eta epsilon
  let Es := fullPairChamberError H A C B W n p q 0 s eta epsilon
  have hEr : 0 ≤ Er := fullPairChamberError_nonneg
    H A C B W n p q r 0 eta epsilon hc hepsilon
  have hprob := abs_primePower_covariance_sub_mainCov_le
    law.probability law.value hpq hp hq hEr
    (Mrs := paperDivisibilityMain n (pairPower p q r s))
    (Mr := paperDivisibilityMain n (pairPower p q r 0))
    (Ms := paperDivisibilityMain n (pairPower p q 0 s))
    (by simpa only [law, StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hpair)
    (by simpa only [law, pairPower, pow_zero, mul_one,
      StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hpr)
    (by simpa only [law, pairPower, pow_zero, one_mul,
      StructuredCellValuationLaw.valuationTilt_probability,
      StructuredCellValuationLaw.valuationTilt_value] using hqs)
  have hmain := abs_paperMainCovariance_le hkernel hn hpBand hqBand hrs
  have htriangle :
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        |law.probability.covariance (law.Ip p r) (law.Ip q s) -
          (paperDivisibilityMain n (pairPower p q r s) -
            paperDivisibilityMain n (pairPower p q r 0) *
              paperDivisibilityMain n (pairPower p q 0 s))| +
        |paperDivisibilityMain n (pairPower p q r s) -
          paperDivisibilityMain n (pairPower p q r 0) *
            paperDivisibilityMain n (pairPower p q 0 s)| := by
    have := abs_add_le
      (law.probability.covariance (law.Ip p r) (law.Ip q s) -
        (paperDivisibilityMain n (pairPower p q r s) -
          paperDivisibilityMain n (pairPower p q r 0) *
            paperDivisibilityMain n (pairPower p q 0 s)))
      (paperDivisibilityMain n (pairPower p q r s) -
        paperDivisibilityMain n (pairPower p q r 0) *
          paperDivisibilityMain n (pairPower p q 0 s))
    simpa only [sub_add_cancel] using this
  exact htriangle.trans (by
    have := add_le_add hprob hmain
    simpa only [fullPrimePowerCovarianceError, Ers, Er, Es, law,
      add_comm, add_left_comm, add_assoc] using this)

/-- **Uniform actual four-mark covariance theorem.**

One box-independent Dickman constant and one nonnegative vanishing
omitted-score remainder control every genuine full-tilt prime-power
covariance in the complete four-mark simplex. -/
theorem exists_uniform_fullTilt_primePower_covariance_bound
    (H : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C)
    (hC : 1 ≤ C) (B : ℝ) (W : ℕ) (hB : 0 ≤ B) (hW : 1 < W) :
    ∃ C_K : ℝ, 0 < C_K ∧
      ∃ epsilon : ℕ → ℝ,
        (∀ n, 0 ≤ epsilon n) ∧ Tendsto epsilon atTop (𝓝 0) ∧
        ∃ N₀ : ℕ, ∀ {n p q r s : ℕ} (eta : ℕ → ℝ),
          N₀ ≤ n → p ∈ primeBand n W →
          q ∈ (primeBand n W).erase p → r + s ≤ 4 →
          Nat.Coprime p H.modulus → Nat.Coprime q H.modulus →
          (∀ z ∈ primeBand n W, |eta z| ≤ B) →
          let S := structuredCell H (physicalBound A n) (physicalBound C n)
            (yNat n)
          S.Nonempty ∧ ∀ hS : S.Nonempty,
            let law := valuationTilt H (physicalBound A n)
              (physicalBound C n) (yNat n) hS (primeBand n W) eta (L n)
            |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
              C_K * ((r : ℝ) * tPrime n p) *
                  ((s : ℝ) * tPrime n q) /
                    ((p : ℝ) ^ r * (q : ℝ) ^ s) +
                fullPrimePowerCovarianceError
                  H A C B W n p q r s eta epsilon := by
  obtain ⟨C_K, hCK, hkernel⟩ :=
    exists_boxIndependent_fourMark_productKernel_bound
  obtain ⟨epsilon, hepsilon0, hepsilonT, Npair, hpair⟩ :=
    exists_uniform_fullTilt_pairPower_paper_bound
      H hA hAC hC B W hB hW
  let N₀ := max Npair 2
  refine ⟨C_K, hCK, epsilon, hepsilon0, hepsilonT, N₀, ?_⟩
  intro n p q r s eta hN hpBand hqErase hrs hpHead hqHead heta
  have hNpair : Npair ≤ n := by dsimp only [N₀] at hN; omega
  have hn : 1 < n := by dsimp only [N₀] at hN; omega
  have hrs0 : r + 0 ≤ 4 := by omega
  have h0s : 0 + s ≤ 4 := by omega
  have hpairData := hpair eta hNpair hpBand hqErase hrs
    hpHead hqHead heta
  have hprData := hpair (r := r) (s := 0) eta hNpair hpBand hqErase hrs0
    hpHead hqHead heta
  have hqsData := hpair (r := 0) (s := s) eta hNpair hpBand hqErase h0s
    hpHead hqHead heta
  let S := structuredCell H (physicalBound A n) (physicalBound C n) (yNat n)
  change S.Nonempty ∧ ∀ hS : S.Nonempty,
      let law := valuationTilt H (physicalBound A n)
        (physicalBound C n) (yNat n) hS (primeBand n W) eta (L n)
      |law.probability.covariance (law.Ip p r) (law.Ip q s)| ≤
        C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s) +
          fullPrimePowerCovarianceError H A C B W n p q r s eta epsilon
  change S.Nonempty ∧ ∀ hS : S.Nonempty,
      |(valuationTilt H (physicalBound A n) (physicalBound C n)
          (yNat n) hS (primeBand n W) eta (L n)).probability.covariance
          ((valuationTilt H (physicalBound A n) (physicalBound C n)
            (yNat n) hS (primeBand n W) eta (L n)).Ip p r)
          ((valuationTilt H (physicalBound A n) (physicalBound C n)
            (yNat n) hS (primeBand n W) eta (L n)).Ip q s)| ≤
        C_K * ((r : ℝ) * tPrime n p) * ((s : ℝ) * tPrime n q) /
            ((p : ℝ) ^ r * (q : ℝ) ^ s) +
          fullPrimePowerCovarianceError H A C B W n p q r s eta epsilon
  obtain ⟨hSnonempty, hpairAll⟩ := hpairData
  obtain ⟨_, hprAll⟩ := hprData
  obtain ⟨_, hqsAll⟩ := hqsData
  refine ⟨by simpa only [S] using hSnonempty, ?_⟩
  intro hS
  have hc : 0 ≤ pairFallbackDensity H A C :=
    (pairFallbackDensity_pos H hAC hC).le
  apply fullTilt_primePower_covariance_le hkernel H eta epsilon hn
    hpBand hqErase hrs hS hc (hepsilon0 n)
  · simpa only [StructuredCellValuationLaw.valuationTilt_probability,
      S] using hpairAll hS
  · simpa only [StructuredCellValuationLaw.valuationTilt_probability,
      pairPower, pow_zero, mul_one, S] using hprAll hS
  · simpa only [StructuredCellValuationLaw.valuationTilt_probability,
      pairPower, pow_zero, one_mul, S] using hqsAll hS

end

end Erdos390.Full.FullTiltPrimePowerCovariance
