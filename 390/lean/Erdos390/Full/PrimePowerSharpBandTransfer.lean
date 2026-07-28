import Erdos390.Full.SquarefreeSharpBandTransfer
import Erdos390.Full.PaperPrimePowerLemma75
import Erdos390.Full.PrimePowerCutoffCovariance

/-!
# Prime-power transfer in the moving-low sharp band norm

The already-proved row field of `PrimePowerTransferBounds` is sufficient for
fixed positive bands, but dividing that collapsed row bound by the moving low
centre would incorrectly charge the box-independent `C_pow / W` term by
`1 / alpha_0`.  This file retains the first four fields of the certificate
until after band averaging.  The factors `t_p t_q` then cancel the output
centre exactly; only the genuine analytic remainder is divided by that
centre.
-/

open scoped BigOperators

namespace Erdos390.Full.PrimePowerSharpBandTransfer

set_option maxHeartbeats 2400000

open ArithmeticModel ArithmeticBandGeometry PrimeSums
open PrimePowerCovariance PrimePowerCovariance.BoundedValuationLaw
open PaperPrimePowerLemma75 PaperPrimePowerRow
open PrimePowerCutoffCovariance
open SquarefreeSharpBandTransfer

noncomputable section

variable {Omega Band : Type*} [Fintype Omega]
  [Fintype Band] [DecidableEq Band]
  {M n W : ℕ}

/-- Full-valuation analogue of the normalized squarefree band row. -/
def fullBandRow
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (b : Band → ℝ) (i : Band) : ℝ :=
  (1 / P.mass i) *
    ∑ p ∈ P.data.fiber i,
      ∑ q : BandPrime n W, b (P.band q) * law.covVV p.1 q.1

def fullSharpRow
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (q : Band → ℝ) (i : Band) : ℝ :=
  fullBandRow law P (fun j ↦ P.center j * q j) i / P.center i

/-- The three off-diagonal prime-power displays imply the corresponding
entrywise full-versus-squarefree covariance estimate. -/
theorem abs_covVV_sub_covII_le_of_transferBounds_of_ne
    (law : BoundedValuationLaw Omega M)
    {Cpow epsilon : ℝ}
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon)
    (p q : BandPrime n W) (hpq : p ≠ q) :
    |law.covVV p.1 q.1 - law.covII p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
          (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) +
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
          (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 +
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
          (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 := by
  have hqErase : q.1 ∈ (primeBand n W).erase p.1 :=
    Finset.mem_erase.mpr ⟨fun h ↦ hpq (Subtype.ext h.symm), q.2⟩
  have hji : |law.covJI p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) := by
    rw [covJI_eq_valuationCutoff_sum law (prime_of_mem_primeBand p.2)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (h75.ji p.1 p.2 q.1 hqErase)
  have hij : |law.covIJ p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
        (1 / (p.1 : ℝ)) * (1 / (q.1 : ℝ)) ^ 2 := by
    rw [covIJ_eq_valuationCutoff_sum law p.1
      (prime_of_mem_primeBand q.2)]
    exact (Finset.abs_sum_le_sum_abs _ _).trans (h75.ij p.1 p.2 q.1 hqErase)
  have hjj : |law.covJJ p.1 q.1| ≤
      (Cpow * tPrime n p.1 * tPrime n q.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (q.1 : ℝ)) ^ 2 := by
    rw [covJJ_eq_valuationCutoff_sum law (prime_of_mem_primeBand p.2)
      (prime_of_mem_primeBand q.2)]
    calc
      |∑ r ∈ highExponents (ValuationCutoff.valuationCutoff p.1 M),
          ∑ s ∈ highExponents (ValuationCutoff.valuationCutoff q.1 M),
          law.probability.covariance (law.Ip p.1 r) (law.Ip q.1 s)| ≤
          ∑ r ∈ highExponents (ValuationCutoff.valuationCutoff p.1 M),
            |∑ s ∈ highExponents (ValuationCutoff.valuationCutoff q.1 M),
              law.probability.covariance (law.Ip p.1 r)
                (law.Ip q.1 s)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ r ∈ highExponents (ValuationCutoff.valuationCutoff p.1 M),
          ∑ s ∈ highExponents (ValuationCutoff.valuationCutoff q.1 M),
          |law.probability.covariance (law.Ip p.1 r)
            (law.Ip q.1 s)| := by
        apply Finset.sum_le_sum
        intro r hr
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := h75.jj p.1 p.2 q.1 hqErase
  exact (law.abs_covVV_sub_covII_le p.1 q.1).trans (by linarith)

/-- Diagonal specialization of the fourth transfer display. -/
theorem abs_covVV_sub_covII_le_of_transferBounds_diagonal
    (law : BoundedValuationLaw Omega M)
    {Cpow epsilon : ℝ}
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon)
    (p : BandPrime n W) :
    |law.covVV p.1 p.1 - law.covII p.1 p.1| ≤
      3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 := by
  exact (law.abs_covVV_sub_covII_diagonal_le
      (prime_of_mem_primeBand p.2)).trans (by
    have h := h75.diagonal p.1 p.2
    nlinarith)

/-- The five displays of Lemma 7.5 aggregated in the genuine moving-low
sharp norm.  The box-independent term is *not* divided by the low centre;
only `epsilon / center i` remains. -/
theorem abs_fullSharpRow_sub_squarefreeSharpRow_le
    (law : BoundedValuationLaw Omega M) (P : Partition n W Band)
    (hn : 1 < n) (hW : 1 < W)
    {Cpow epsilon : ℝ} (hCpow : 0 ≤ Cpow) (hepsilon : 0 ≤ epsilon)
    (h75 : PrimePowerTransferBounds law n W Cpow epsilon)
    (q : Band → ℝ) (hq : ∀ j, |q j| ≤ 1) (i : Band) :
    |fullSharpRow law P q i - squarefreeSharpRow law P q i| ≤
      3 * Cpow * (bandTReciprocalSum n W + 1) * (1 / (W : ℝ)) +
        3 * epsilon *
          (bandTReciprocalSum n W / P.center i + 1) *
            (1 / (W : ℝ)) := by
  let T := bandTReciprocalSum n W
  have hmass : 0 < P.mass i := P.data.mass_pos i
  have hcenter : 0 < P.center i := P.center_pos hn i
  have hWpos : (0 : ℝ) < W := by exact_mod_cast Nat.zero_lt_of_lt hW
  have hWinvNonneg : 0 ≤ (1 / (W : ℝ)) := by positivity
  have hWinvOne : (1 / (W : ℝ)) ≤ 1 := by
    have hWone : (1 : ℝ) ≤ W := by exact_mod_cast hW.le
    simpa only [one_div_one] using one_div_le_one_div_of_le
      (by norm_num : (0 : ℝ) < 1) hWone
  have hT : 0 ≤ T := by
    dsimp only [T]
    unfold bandTReciprocalSum
    apply Finset.sum_nonneg
    intro p hp
    exact div_nonneg (tPrime_nonneg_of_mem_primeBand hn hp)
      (by positivity)
  have hprimePos (p : BandPrime n W) : (0 : ℝ) < p.1 := by
    exact_mod_cast (prime_of_mem_primeBand p.2).pos
  have hprimeInvNonneg (p : BandPrime n W) :
      0 ≤ (1 / (p.1 : ℝ)) := by positivity
  have hprimeInvW (p : BandPrime n W) :
      (1 / (p.1 : ℝ)) ≤ 1 / (W : ℝ) := by
    exact one_div_le_one_div_of_le hWpos
      (by exact_mod_cast (cutoff_lt_of_mem_primeBand p.2).le)
  have htNonneg (p : BandPrime n W) : 0 ≤ tPrime n p.1 :=
    tPrime_nonneg_of_mem_primeBand hn p.2
  have htOne (p : BandPrime n W) : tPrime n p.1 ≤ 1 :=
    tPrime_le_one_of_mem_primeBand hn p.2
  have hcenterNonneg (j : Band) : 0 ≤ P.center j :=
    (P.center_pos hn j).le
  have hcenterOne (j : Band) : P.center j ≤ 1 :=
    (P.center_mem_zero_one hn j).2
  have hcoeff (j : Band) : |P.center j * q j| ≤ P.center j := by
    rw [abs_mul, abs_of_nonneg (hcenterNonneg j)]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (hq j) (hcenterNonneg j)
  have htotal :
      (∑ r : BandPrime n W, P.center (P.band r) / (r.1 : ℝ)) = T := by
    calc
      (∑ r : BandPrime n W, P.center (P.band r) / (r.1 : ℝ)) =
          ∑ j : Band, P.mass j * P.center j := by
        rw [← Finset.sum_fiberwise Finset.univ P.band
          (fun r : BandPrime n W ↦ P.center (P.band r) / (r.1 : ℝ))]
        apply Finset.sum_congr rfl
        intro j hj
        change (∑ r ∈ P.data.fiber j,
          P.center (P.band r) / (r.1 : ℝ)) = P.mass j * P.center j
        calc
          _ = ∑ r ∈ P.data.fiber j,
              (1 / (r.1 : ℝ)) * P.center j := by
            apply Finset.sum_congr rfl
            intro r hr
            have hrj : P.band r = j := by
              simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff]
                using hr
            rw [hrj]
            ring
          _ = P.mass j * P.center j := by
            rw [← Finset.sum_mul]
            rfl
      _ = T := by
        exact P.sum_mass_mul_center_eq_bandTReciprocalSum
  have hentry (p r : BandPrime n W) :
      |law.covVV p.1 r.1 - law.covII p.1 r.1| ≤
        (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) +
        (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
            (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) ^ 2 +
        (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) ^ 2 +
        (if p = r then
          3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2
        else 0) := by
    by_cases hpr : p = r
    · subst r
      rw [if_pos rfl]
      have hdiag :=
        abs_covVV_sub_covII_le_of_transferBounds_diagonal law h75 p
      have hoffNonneg : 0 ≤
          (Cpow * tPrime n p.1 * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) +
          (Cpow * tPrime n p.1 * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) ^ 2 +
          (Cpow * tPrime n p.1 * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (p.1 : ℝ)) ^ 2 := by
        have hc : 0 ≤ Cpow * tPrime n p.1 * tPrime n p.1 + epsilon := by
          exact add_nonneg
            (mul_nonneg (mul_nonneg hCpow (htNonneg p)) (htNonneg p))
            hepsilon
        positivity
      linarith
    · rw [if_neg hpr, add_zero]
      exact abs_covVV_sub_covII_le_of_transferBounds_of_ne law h75 p r hpr
  have hbase (p : BandPrime n W) : 0 ≤
      (Cpow * tPrime n p.1 + epsilon) * T *
        (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
    have hc : 0 ≤ Cpow * tPrime n p.1 + epsilon :=
      add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon
    positivity
  have hinner (p : BandPrime n W) :
      (∑ r : BandPrime n W,
        |P.center (P.band r) * q (P.band r)| *
          |law.covVV p.1 r.1 - law.covII p.1 r.1|) ≤
        3 * ((Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) +
        3 * (Cpow + epsilon) * P.center (P.band p) *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
    let JI : BandPrime n W → ℝ := fun r ↦
      (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ))
    let IJ : BandPrime n W → ℝ := fun r ↦
      (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
        (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) ^ 2
    let JJ : BandPrime n W → ℝ := fun r ↦
      (Cpow * tPrime n p.1 * tPrime n r.1 + epsilon) *
        (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) ^ 2
    let D : BandPrime n W → ℝ := fun r ↦
      if p = r then 3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2 else 0
    have hraw :
        (∑ r : BandPrime n W,
          |P.center (P.band r) * q (P.band r)| *
            |law.covVV p.1 r.1 - law.covII p.1 r.1|) ≤
          ∑ r : BandPrime n W,
            P.center (P.band r) * (JI r + IJ r + JJ r + D r) := by
      apply Finset.sum_le_sum
      intro r hr
      exact mul_le_mul (hcoeff (P.band r)) (by
          simpa only [JI, IJ, JJ, D] using hentry p r)
        (abs_nonneg _) (hcenterNonneg (P.band r))
    have hcoef (r : BandPrime n W) :
        Cpow * tPrime n p.1 * tPrime n r.1 + epsilon ≤
          Cpow * tPrime n p.1 + epsilon := by
      have hcp : 0 ≤ Cpow * tPrime n p.1 := mul_nonneg hCpow (htNonneg p)
      nlinarith [htOne r]
    have hJI : (∑ r : BandPrime n W,
        P.center (P.band r) * JI r) ≤
        (Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      calc
        _ ≤ ∑ r : BandPrime n W,
            (Cpow * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 *
                (P.center (P.band r) / (r.1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hfac : 0 ≤ P.center (P.band r) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) :=
            mul_nonneg
              (mul_nonneg (hcenterNonneg (P.band r)) (sq_nonneg _))
              (hprimeInvNonneg r)
          have hm := mul_le_mul_of_nonneg_right (hcoef r) hfac
          simpa only [JI] using (show
            P.center (P.band r) * JI r ≤
              (Cpow * tPrime n p.1 + epsilon) *
                (1 / (p.1 : ℝ)) ^ 2 *
                  (P.center (P.band r) / (r.1 : ℝ)) by
            dsimp only [JI]
            convert hm using 1 <;> ring)
        _ = (Cpow * tPrime n p.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * T := by
          rw [← Finset.mul_sum, htotal]
        _ ≤ (Cpow * tPrime n p.1 + epsilon) * T *
            (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
          have hcT : 0 ≤ (Cpow * tPrime n p.1 + epsilon) * T :=
            mul_nonneg
              (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon) hT
          have hpSq : (1 / (p.1 : ℝ)) ^ 2 ≤
              (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
            calc
              (1 / (p.1 : ℝ)) ^ 2 =
                  (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by ring
              _ ≤ (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hprimeInvW p)
                  (hprimeInvNonneg p)
          nlinarith [mul_le_mul_of_nonneg_left hpSq hcT]
    have hIJ : (∑ r : BandPrime n W,
        P.center (P.band r) * IJ r) ≤
        (Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      calc
        _ ≤ ∑ r : BandPrime n W,
            (Cpow * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) * (1 / (W : ℝ)) *
                (P.center (P.band r) / (r.1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hfac : 0 ≤ P.center (P.band r) *
              (1 / (p.1 : ℝ)) * (1 / (r.1 : ℝ)) ^ 2 :=
            mul_nonneg
              (mul_nonneg (hcenterNonneg (P.band r)) (hprimeInvNonneg p))
              (sq_nonneg _)
          have hm := mul_le_mul_of_nonneg_right (hcoef r) hfac
          have hrsq : (1 / (r.1 : ℝ)) ^ 2 ≤
              (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) := by
            calc
              (1 / (r.1 : ℝ)) ^ 2 =
                  (1 / (r.1 : ℝ)) * (1 / (r.1 : ℝ)) := by ring
              _ ≤ (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hprimeInvW r)
                  (hprimeInvNonneg r)
          have hc : 0 ≤ (Cpow * tPrime n p.1 + epsilon) *
              P.center (P.band r) * (1 / (p.1 : ℝ)) :=
            mul_nonneg
              (mul_nonneg
                (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon)
                (hcenterNonneg (P.band r)))
              (hprimeInvNonneg p)
          dsimp only [IJ]
          calc
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) *
                  (1 / (r.1 : ℝ)) ^ 2 := by nlinarith [hm]
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) *
                  ((1 / (W : ℝ)) * (1 / (r.1 : ℝ))) :=
              mul_le_mul_of_nonneg_left hrsq hc
            _ = _ := by ring
        _ = _ := by
          rw [← Finset.mul_sum, htotal]
          ring
    have hJJ : (∑ r : BandPrime n W,
        P.center (P.band r) * JJ r) ≤
        (Cpow * tPrime n p.1 + epsilon) * T *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      calc
        _ ≤ ∑ r : BandPrime n W,
            (Cpow * tPrime n p.1 + epsilon) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (W : ℝ)) *
                (P.center (P.band r) / (r.1 : ℝ)) := by
          apply Finset.sum_le_sum
          intro r hr
          have hfac : 0 ≤ P.center (P.band r) *
              (1 / (p.1 : ℝ)) ^ 2 * (1 / (r.1 : ℝ)) ^ 2 := by
            exact mul_nonneg
              (mul_nonneg (hcenterNonneg (P.band r)) (sq_nonneg _))
              (sq_nonneg _)
          have hm := mul_le_mul_of_nonneg_right (hcoef r) hfac
          have hrsq : (1 / (r.1 : ℝ)) ^ 2 ≤
              (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) := by
            calc
              (1 / (r.1 : ℝ)) ^ 2 =
                  (1 / (r.1 : ℝ)) * (1 / (r.1 : ℝ)) := by ring
              _ ≤ (1 / (W : ℝ)) * (1 / (r.1 : ℝ)) :=
                mul_le_mul_of_nonneg_right (hprimeInvW r)
                  (hprimeInvNonneg r)
          have hc : 0 ≤ (Cpow * tPrime n p.1 + epsilon) *
              P.center (P.band r) * (1 / (p.1 : ℝ)) ^ 2 :=
            mul_nonneg
              (mul_nonneg
                (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon)
                (hcenterNonneg (P.band r)))
              (sq_nonneg _)
          dsimp only [JJ]
          calc
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) ^ 2 *
                  (1 / (r.1 : ℝ)) ^ 2 := by nlinarith [hm]
            _ ≤ (Cpow * tPrime n p.1 + epsilon) *
                P.center (P.band r) * (1 / (p.1 : ℝ)) ^ 2 *
                  ((1 / (W : ℝ)) * (1 / (r.1 : ℝ))) :=
              mul_le_mul_of_nonneg_left hrsq hc
            _ = _ := by ring
        _ = (Cpow * tPrime n p.1 + epsilon) *
            (1 / (p.1 : ℝ)) ^ 2 * (1 / (W : ℝ)) * T := by
          rw [← Finset.mul_sum, htotal]
        _ ≤ _ := by
          have hcTW : 0 ≤ (Cpow * tPrime n p.1 + epsilon) *
              T * (1 / (W : ℝ)) :=
            mul_nonneg
              (mul_nonneg
                (add_nonneg (mul_nonneg hCpow (htNonneg p)) hepsilon) hT)
              hWinvNonneg
          have hpSq : (1 / (p.1 : ℝ)) ^ 2 ≤
              1 / (p.1 : ℝ) := by
            have hpOne : (1 / (p.1 : ℝ)) ≤ 1 :=
              (hprimeInvW p).trans hWinvOne
            nlinarith [hprimeInvNonneg p]
          nlinarith [mul_le_mul_of_nonneg_left hpSq hcTW]
    have hD : (∑ r : BandPrime n W,
        P.center (P.band r) * D r) ≤
        3 * (Cpow + epsilon) * P.center (P.band p) *
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
      have hsum : (∑ r : BandPrime n W,
          P.center (P.band r) * D r) =
          3 * (Cpow + epsilon) * P.center (P.band p) *
            (1 / (p.1 : ℝ)) ^ 2 := by
        dsimp only [D]
        calc
          _ = ∑ r : BandPrime n W,
              if r = p then
                P.center (P.band r) *
                  (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2)
              else 0 := by
            apply Finset.sum_congr rfl
            intro r hr
            by_cases hpr : p = r
            · subst r; simp
            · have hrp : r ≠ p := fun h ↦ hpr h.symm
              simp [hpr, hrp]
          _ = P.center (P.band p) *
              (3 * (Cpow + epsilon) * (1 / (p.1 : ℝ)) ^ 2) := by
            simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
          _ = _ := by ring
      rw [hsum]
      have hc : 0 ≤ 3 * (Cpow + epsilon) * P.center (P.band p) := by
        exact mul_nonneg
          (mul_nonneg (by norm_num)
            (add_nonneg hCpow hepsilon))
          (hcenterNonneg (P.band p))
      have hpSq : (1 / (p.1 : ℝ)) ^ 2 ≤
          (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
        calc
          (1 / (p.1 : ℝ)) ^ 2 =
              (1 / (p.1 : ℝ)) * (1 / (p.1 : ℝ)) := by ring
          _ ≤ (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) :=
            mul_le_mul_of_nonneg_right (hprimeInvW p) (hprimeInvNonneg p)
      nlinarith [mul_le_mul_of_nonneg_left hpSq hc]
    calc
      _ ≤ ∑ r : BandPrime n W,
          P.center (P.band r) * (JI r + IJ r + JJ r + D r) := hraw
      _ = (∑ r : BandPrime n W, P.center (P.band r) * JI r) +
          (∑ r : BandPrime n W, P.center (P.band r) * IJ r) +
          (∑ r : BandPrime n W, P.center (P.band r) * JJ r) +
          (∑ r : BandPrime n W, P.center (P.band r) * D r) := by
        simp_rw [mul_add]
        simp only [Finset.sum_add_distrib]
      _ ≤ _ := by linarith [hJI, hIJ, hJJ, hD]
  have hfiberBand (p : BandPrime n W) (hp : p ∈ P.data.fiber i) :
      P.band p = i := by
    simpa only [Erdos390.Lemma84.WeightedBandData.mem_fiber_iff] using hp
  have hmoment :
      (∑ p ∈ P.data.fiber i,
        tPrime n p.1 * (1 / (p.1 : ℝ))) = P.mass i * P.center i := by
    change (∑ p ∈ P.data.fiber i,
        tPrime n p.1 * (1 / (p.1 : ℝ))) =
      P.mass i *
        ((∑ p ∈ P.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime n p.1) / P.mass i)
    have hreorder : (∑ p ∈ P.data.fiber i,
        tPrime n p.1 * (1 / (p.1 : ℝ))) =
        ∑ p ∈ P.data.fiber i,
          (1 / (p.1 : ℝ)) * tPrime n p.1 := by
      apply Finset.sum_congr rfl
      intro p hp
      ring
    rw [hreorder]
    field_simp [hmass.ne']
  unfold fullSharpRow squarefreeSharpRow fullBandRow squarefreeBandRow
  rw [← sub_div]
  have hraw :
      |(1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covVV p.1 r.1) -
        (1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covII p.1 r.1)| ≤
        3 * (Cpow * P.center i + epsilon) * T * (1 / (W : ℝ)) +
          3 * (Cpow + epsilon) * P.center i * (1 / (W : ℝ)) := by
    let A : ℝ := ∑ p ∈ P.data.fiber i,
      ∑ r : BandPrime n W,
        P.center (P.band r) * q (P.band r) * law.covVV p.1 r.1
    let R : ℝ := ∑ p ∈ P.data.fiber i,
      ∑ r : BandPrime n W,
        P.center (P.band r) * q (P.band r) * law.covII p.1 r.1
    have hdiff : A - R = ∑ p ∈ P.data.fiber i,
        ∑ r : BandPrime n W,
          P.center (P.band r) * q (P.band r) *
            (law.covVV p.1 r.1 - law.covII p.1 r.1) := by
      dsimp only [A, R]
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro r hr
      ring
    have hsum : |A - R| ≤
        (3 * (Cpow * P.center i + epsilon) * T * (1 / (W : ℝ)) +
          3 * (Cpow + epsilon) * P.center i * (1 / (W : ℝ))) *
            P.mass i := by
      rw [hdiff]
      calc
        _ ≤ ∑ p ∈ P.data.fiber i,
            |∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) *
                (law.covVV p.1 r.1 - law.covII p.1 r.1)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ P.data.fiber i,
            (3 * ((Cpow * tPrime n p.1 + epsilon) * T *
              (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) +
            3 * (Cpow + epsilon) * P.center (P.band p) *
              (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) := by
          apply Finset.sum_le_sum
          intro p hp
          calc
            _ ≤ ∑ r : BandPrime n W,
                |P.center (P.band r) * q (P.band r)| *
                  |law.covVV p.1 r.1 - law.covII p.1 r.1| := by
              calc
                _ ≤ ∑ r : BandPrime n W,
                    |P.center (P.band r) * q (P.band r) *
                      (law.covVV p.1 r.1 - law.covII p.1 r.1)| :=
                  Finset.abs_sum_le_sum_abs _ _
                _ = _ := by
                  apply Finset.sum_congr rfl
                  intro r hr
                  rw [abs_mul]
            _ ≤ _ := hinner p
        _ = (3 * (Cpow * P.center i + epsilon) * T *
              (1 / (W : ℝ)) +
            3 * (Cpow + epsilon) * P.center i *
              (1 / (W : ℝ))) * P.mass i := by
          have hmassDef : (∑ p ∈ P.data.fiber i,
              1 / (p.1 : ℝ)) = P.mass i := rfl
          have hdiagFiber :
              (∑ p ∈ P.data.fiber i,
                3 * (Cpow + epsilon) * P.center (P.band p) *
                  (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) =
              ∑ p ∈ P.data.fiber i,
                3 * (Cpow + epsilon) * P.center i *
                  (1 / (W : ℝ)) * (1 / (p.1 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro p hp
            rw [hfiberBand p hp]
          rw [Finset.sum_add_distrib]
          rw [hdiagFiber]
          rw [show (∑ p ∈ P.data.fiber i,
              3 * ((Cpow * tPrime n p.1 + epsilon) * T *
                (1 / (W : ℝ)) * (1 / (p.1 : ℝ)))) =
              3 * (Cpow * P.center i + epsilon) * T *
                (1 / (W : ℝ)) * P.mass i by
            have hbaseSum : (∑ p ∈ P.data.fiber i,
                (Cpow * tPrime n p.1 + epsilon) *
                  (1 / (p.1 : ℝ))) =
                Cpow * (P.mass i * P.center i) + epsilon * P.mass i := by
              have hCsum : (∑ p ∈ P.data.fiber i,
                  Cpow * tPrime n p.1 * (1 / (p.1 : ℝ))) =
                  Cpow * (P.mass i * P.center i) := by
                calc
                  _ = Cpow * (∑ p ∈ P.data.fiber i,
                      tPrime n p.1 * (1 / (p.1 : ℝ))) := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro p hp
                    ring
                  _ = _ := by rw [hmoment]
              have hEsum : (∑ p ∈ P.data.fiber i,
                  epsilon * (1 / (p.1 : ℝ))) =
                  epsilon * P.mass i := by
                calc
                  _ = epsilon * (∑ p ∈ P.data.fiber i,
                      1 / (p.1 : ℝ)) := by rw [Finset.mul_sum]
                  _ = _ := by rw [hmassDef]
              simp_rw [add_mul]
              rw [Finset.sum_add_distrib, hCsum, hEsum]
            calc
              _ = 3 * T * (1 / (W : ℝ)) *
                  (∑ p ∈ P.data.fiber i,
                    (Cpow * tPrime n p.1 + epsilon) *
                      (1 / (p.1 : ℝ))) := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro p hp
                ring
              _ = _ := by rw [hbaseSum]; ring]
          rw [show (∑ p ∈ P.data.fiber i,
              3 * (Cpow + epsilon) * P.center i *
                (1 / (W : ℝ)) * (1 / (p.1 : ℝ))) =
              3 * (Cpow + epsilon) * P.center i *
                (1 / (W : ℝ)) * P.mass i by
            rw [← Finset.mul_sum, hmassDef]]
          ring
    have hscaled : |(1 / P.mass i) * A - (1 / P.mass i) * R| =
        (1 / P.mass i) * |A - R| := by
      rw [← mul_sub, abs_mul, abs_of_pos (one_div_pos.mpr hmass)]
    change |(1 / P.mass i) * A - (1 / P.mass i) * R| ≤ _
    rw [hscaled]
    calc
      _ ≤ (1 / P.mass i) *
          ((3 * (Cpow * P.center i + epsilon) * T *
              (1 / (W : ℝ)) +
            3 * (Cpow + epsilon) * P.center i *
              (1 / (W : ℝ))) * P.mass i) :=
        mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr hmass.le)
      _ = _ := by field_simp [hmass.ne']
  change
    |((1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covVV p.1 r.1) -
        (1 / P.mass i) *
          (∑ p ∈ P.data.fiber i,
            ∑ r : BandPrime n W,
              P.center (P.band r) * q (P.band r) * law.covII p.1 r.1)) /
        P.center i| ≤ _
  rw [abs_div, abs_of_pos hcenter]
  calc
    _ ≤ (3 * (Cpow * P.center i + epsilon) * T *
          (1 / (W : ℝ)) +
        3 * (Cpow + epsilon) * P.center i *
          (1 / (W : ℝ))) / P.center i :=
      div_le_div_of_nonneg_right hraw hcenter.le
    _ = 3 * Cpow * (T + 1) * (1 / (W : ℝ)) +
        3 * epsilon * (T / P.center i + 1) *
          (1 / (W : ℝ)) := by
      field_simp [hcenter.ne']
      ring
    _ = 3 * Cpow * (bandTReciprocalSum n W + 1) *
          (1 / (W : ℝ)) +
        3 * epsilon *
          (bandTReciprocalSum n W / P.center i + 1) *
            (1 / (W : ℝ)) := by rfl

end

end Erdos390.Full.PrimePowerSharpBandTransfer
