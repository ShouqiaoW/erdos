import Erdos390.Full.PaperScaleMarkedCell
import Erdos390.Full.UniformFiniteProbability

/-!
# Uniform moving-prefix endpoint bookkeeping

For a prefix endpoint `k` inside a fixed physical interval, put
`D = k / n`.  Then `physicalBound D n = k` exactly.  Moreover `D` stays
in the original fixed compact physical interval.  These elementary facts
allow the marked-cell endpoint theorem to be applied without pretending
that the moving endpoint is fixed as `n` varies.
-/

namespace Erdos390.Full.PaperMovingPrefixMarkedCell

open ArithmeticModel PaperScaleMarkedCell
open HeadPattern StructuredCells MarkedFriableAsymptotic
open StructuredCellAsymptotic
open scoped BigOperators

noncomputable section

/-- The physical scale represented by an integer moving endpoint. -/
def prefixScale (n k : ℕ) : ℝ := (k : ℝ) / (n : ℝ)

theorem prefixScale_pos {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    0 < prefixScale n k := by
  exact div_pos (by exact_mod_cast hk) (by exact_mod_cast hn)

/-- Re-encoding an integer prefix as a physical scale loses no endpoint:
the floor operation returns the original integer exactly. -/
@[simp] theorem physicalBound_prefixScale_eq {n k : ℕ} (hn : 0 < n) :
    physicalBound (prefixScale n k) n = k := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold physicalBound prefixScale
  rw [div_mul_cancel₀ _ hnR]
  simp

/-- A prefix strictly above `floor(A n)` has scale strictly above `A`. -/
theorem lt_prefixScale_of_physicalBound_lt
    {A : ℝ} {n k : ℕ} (hn : 0 < n)
    (hk : physicalBound A n < k) :
    A < prefixScale n k := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hfloor : A * (n : ℝ) < (physicalBound A n : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (A * (n : ℝ))
  have hkCast : (physicalBound A n : ℝ) + 1 ≤ (k : ℝ) := by
    exact_mod_cast hk
  apply (lt_div_iff₀ hnR).2
  exact hfloor.trans_le hkCast

/-- A prefix below `floor(C n)` has scale at most `C`. -/
theorem prefixScale_le_of_le_physicalBound
    {C : ℝ} {n k : ℕ} (hC : 0 ≤ C) (hn : 0 < n)
    (hk : k ≤ physicalBound C n) :
    prefixScale n k ≤ C := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hkFloor : (k : ℝ) ≤ (physicalBound C n : ℝ) := by
    exact_mod_cast hk
  have hfloor : (physicalBound C n : ℝ) ≤ C * (n : ℝ) := by
    exact Nat.floor_le (mul_nonneg hC hnR.le)
  apply (div_le_iff₀ hnR).2
  exact hkFloor.trans hfloor

/-- Combined compact containment for every moving prefix used by Abel
summation. -/
theorem prefixScale_mem_compact
    {A C : ℝ} {n k : ℕ} (hC : 0 ≤ C) (hn : 0 < n)
    (hlow : physicalBound A n < k)
    (hhigh : k ≤ physicalBound C n) :
    A < prefixScale n k ∧ prefixScale n k ≤ C :=
  ⟨lt_prefixScale_of_physicalBound_lt hn hlow,
    prefixScale_le_of_le_physicalBound hC hn hhigh⟩

/-- A coarse but fixed endpoint coefficient valid uniformly for every
moving physical scale in `[A,C]`. -/
def compactEndpointCoefficient (A C : ℝ) (g : ℕ) : ℝ :=
  2 + 5 * (Real.log 2 + |Real.log A| + |Real.log C| +
      |Real.log (g : ℝ)|) +
    (45 / 2 : ℝ) * Real.log 2

theorem endpointCoefficient_le_compactEndpointCoefficient
    {A C D : ℝ} (g : ℕ) (hA : 0 < A)
    (hAD : A ≤ D) (hDC : D ≤ C) :
    endpointCoefficient D g ≤ compactEndpointCoefficient A C g := by
  have hD : 0 < D := hA.trans_le hAD
  have hC : 0 < C := hD.trans_le hDC
  have hlogAD : Real.log A ≤ Real.log D :=
    Real.log_le_log hA hAD
  have hlogDC : Real.log D ≤ Real.log C :=
    Real.log_le_log hD hDC
  have hlogDabs : |Real.log D| ≤ |Real.log A| + |Real.log C| := by
    rw [abs_le]
    constructor
    · calc
        -(|Real.log A| + |Real.log C|) ≤ -|Real.log A| := by
          linarith [abs_nonneg (Real.log C)]
        _ ≤ Real.log A := neg_abs_le (Real.log A)
        _ ≤ Real.log D := hlogAD
    · calc
        Real.log D ≤ Real.log C := hlogDC
        _ ≤ |Real.log C| := le_abs_self (Real.log C)
        _ ≤ |Real.log A| + |Real.log C| := by
          linarith [abs_nonneg (Real.log A)]
  have hdiff : |Real.log D - Real.log (g : ℝ)| ≤
      |Real.log A| + |Real.log C| + |Real.log (g : ℝ)| := by
    calc
      |Real.log D - Real.log (g : ℝ)| ≤
          |Real.log D| + |Real.log (g : ℝ)| := abs_sub _ _
      _ ≤ (|Real.log A| + |Real.log C|) +
          |Real.log (g : ℝ)| := by linarith
  unfold endpointCoefficient compactEndpointCoefficient
  linarith

theorem compactEndpointCoefficient_nonneg (A C : ℝ) (g : ℕ) :
    0 ≤ compactEndpointCoefficient A C g := by
  unfold compactEndpointCoefficient
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  positivity

/-- Uniform version of the complete finite head endpoint ledger. -/
def compactEndpointFamilyCoefficient
    (P : HeadPattern.Pattern) (A C : ℝ) : ℝ :=
  ∑ a ∈ P.modulus.divisors,
    |(ArithmeticFunction.moebius a : ℝ)| *
      (compactEndpointCoefficient A C (P.factor * a) *
        C / ((P.factor * a : ℕ) : ℝ))

theorem compactEndpointFamilyCoefficient_nonneg
    (P : HeadPattern.Pattern) {A C : ℝ} (hC : 0 ≤ C) :
    0 ≤ compactEndpointFamilyCoefficient P A C := by
  unfold compactEndpointFamilyCoefficient
  apply Finset.sum_nonneg
  intro a ha
  exact mul_nonneg (abs_nonneg _)
    (div_nonneg
      (mul_nonneg (compactEndpointCoefficient_nonneg A C _) hC)
      (by positivity))

theorem endpointFamilyCoefficient_le_compact
    (P : HeadPattern.Pattern) {A C D : ℝ}
    (hA : 0 < A) (hAD : A ≤ D) (hDC : D ≤ C) :
    endpointFamilyCoefficient P D ≤
      compactEndpointFamilyCoefficient P A C := by
  have hD : 0 < D := hA.trans_le hAD
  have hC : 0 < C := hD.trans_le hDC
  unfold endpointFamilyCoefficient compactEndpointFamilyCoefficient
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hcoef := endpointCoefficient_le_compactEndpointCoefficient
    (A := A) (C := C) (D := D) (P.factor * a) hA hAD hDC
  have hcoef0 := endpointCoefficient_nonneg D (P.factor * a)
  have hcompact0 := compactEndpointCoefficient_nonneg A C (P.factor * a)
  have hden : (0 : ℝ) < ((P.factor * a : ℕ) : ℝ) := by
    exact_mod_cast mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
      (Nat.pos_of_mem_divisors ha)
  calc
    endpointCoefficient D (P.factor * a) * D /
        ((P.factor * a : ℕ) : ℝ) ≤
      compactEndpointCoefficient A C (P.factor * a) * D /
        ((P.factor * a : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcoef hD.le) hden.le
    _ ≤ compactEndpointCoefficient A C (P.factor * a) * C /
        ((P.factor * a : ℕ) : ℝ) := by
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_left hDC hcompact0) hden.le

/-- The paper-scale marked count, uniformly in every integer upper prefix
inside one fixed physical interval.  The common main term is evaluated at
the exact moving scale `k/n`; the error constant and threshold do not depend
on `k`. -/
theorem exists_uniform_movingUpper_markedCell_paper_main_bound
    (P : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n k d : ℕ},
      N₀ ≤ n → physicalBound A n < k → k ≤ physicalBound C n →
      0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      |((markedCell P (physicalBound A n) k (yNat n) d).card : ℝ) -
          paperMarkedMain P A (prefixScale n k) n d| ≤
        K * (n : ℝ) / ((d : ℝ) * Scale.L n) := by
  obtain ⟨Kraw, hKraw, Y₀, hraw⟩ :=
    exists_uniform_markedCell_dickman_sum_bound
  obtain ⟨NmarginA, hmarginA₀⟩ := exists_endpoint_margin_threshold P hA
  obtain ⟨NlogA, hlogA₀⟩ := exists_physicalBound_log_range hA
  obtain ⟨NlogC, hlogC₀⟩ :=
    exists_physicalBound_log_range (hA.trans hAC)
  let H : ℕ := max Y₀ (max P.modulus 2)
  have hyTop : Filter.Tendsto (fun n : ℕ => ArithmeticModel.y n)
      Filter.atTop Filter.atTop := by
    simpa [ArithmeticModel.y] using
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 9)).comp
        tendsto_natCast_atTop_atTop)
  have hyEvent : ∀ᶠ n : ℕ in Filter.atTop, (H : ℝ) ≤ y n :=
    hyTop.eventually (Filter.eventually_ge_atTop (H : ℝ))
  have hlogEvent := FriableAsymptotic.eventually_one_fifth_L_le_log_yNat
  have hscaleAll : ∀ᶠ n : ℕ in Filter.atTop,
      1 < n ∧ (H : ℝ) ≤ y n ∧
        (1 / 5 : ℝ) * Scale.L n ≤ Real.log (yNat n : ℝ) := by
    filter_upwards [Filter.eventually_gt_atTop 1, hyEvent, hlogEvent] with
      n hn hy hlog
    exact ⟨hn, hy, hlog⟩
  obtain ⟨Nscale, hNscale⟩ := Filter.eventually_atTop.mp hscaleAll
  let N₀ := max NmarginA (max NlogA (max NlogC Nscale))
  let K : ℝ :=
    1 + 5 * Kraw * (C + A) * headMoebiusMass P +
      compactEndpointFamilyCoefficient P A C +
      endpointFamilyCoefficient P A
  have hC : 0 < C := hA.trans hAC
  have hrawCoeff0 :
      0 ≤ 5 * Kraw * (C + A) * headMoebiusMass P := by
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg (by norm_num) hKraw.le) (add_nonneg hC.le hA.le))
      (headMoebiusMass_nonneg P)
  have hcompactCoeff0 :
      0 ≤ compactEndpointFamilyCoefficient P A C :=
    compactEndpointFamilyCoefficient_nonneg P hC.le
  have hAcoeff0 : 0 ≤ endpointFamilyCoefficient P A :=
    endpointFamilyCoefficient_nonneg P hA.le
  have hK : 0 < K := by
    dsimp only [K]
    linarith
  refine ⟨K, hK, N₀, ?_⟩
  intro n k d hN hlow hhigh hd hd4 hdsmooth hcop
  have hNmA : NmarginA ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNlA : NlogA ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNlC : NlogC ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNs : Nscale ≤ n := by
    dsimp only [N₀] at hN
    omega
  obtain ⟨hn, hyH, hlogLower⟩ := hNscale n hNs
  have hnpos : 0 < n := by omega
  have hL : 0 < Scale.L n := Scale.L_pos hn
  have hDcompact := prefixScale_mem_compact hC.le hnpos hlow hhigh
  let D : ℝ := prefixScale n k
  have hAD : A ≤ D := by
    exact (by simpa only [D] using hDcompact.1.le)
  have hDC : D ≤ C := by
    simpa only [D] using hDcompact.2
  have hD : 0 < D := hA.trans_le hAD
  have hDend : physicalBound D n = k := by
    simpa only [D] using physicalBound_prefixScale_eq hnpos
  have hHy : H ≤ yNat n := Nat.le_floor hyH
  have hY₀ : Y₀ ≤ yNat n :=
    (le_max_left Y₀ (max P.modulus 2)).trans hHy
  have hmodY : P.modulus ≤ yNat n :=
    (le_max_left P.modulus 2).trans
      ((le_max_right Y₀ (max P.modulus 2)).trans hHy)
  have hyNat2 : 2 ≤ yNat n :=
    (le_max_right P.modulus 2).trans
      ((le_max_right Y₀ (max P.modulus 2)).trans hHy)
  have hy2 : (2 : ℝ) ≤ y n := by
    exact (by exact_mod_cast hyNat2 : (2 : ℝ) ≤ (yNat n : ℝ)).trans
      (Nat.floor_le (Scale.y_pos hnpos).le)
  have hhead : ∀ p ∈ P.primes, p ≤ yNat n := by
    intro p hp
    have hpDvd : p ∣ P.modulus := by
      unfold Pattern.modulus
      exact Finset.dvd_prod_of_mem (fun q : ℕ => q) hp
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero P.modulus_ne_zero) hpDvd).trans
      hmodY
  have hlohi : physicalBound A n ≤ physicalBound D n := by
    rw [hDend]
    exact hlow.le
  have hmarginA : ∀ a ∈ P.modulus.divisors,
      4 ≤ A * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      Scale.L n ≤ A * (n : ℝ) /
        ((P.factor * a * d : ℕ) : ℝ) := by
    intro a ha
    exact hmarginA₀ hNmA ha hd hd4
  have hmarginD : ∀ a ∈ P.modulus.divisors,
      4 ≤ D * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) ∧
      Scale.L n ≤ D * (n : ℝ) /
        ((P.factor * a * d : ℕ) : ℝ) := by
    intro a ha
    have hden : (0 : ℝ) ≤ ((P.factor * a * d : ℕ) : ℝ) := by positivity
    have hnum : A * (n : ℝ) ≤ D * (n : ℝ) :=
      mul_le_mul_of_nonneg_right hAD (by positivity)
    have hratio : A * (n : ℝ) /
          ((P.factor * a * d : ℕ) : ℝ) ≤
        D * (n : ℝ) / ((P.factor * a * d : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hnum hden
    exact ⟨(hmarginA a ha).1.trans hratio,
      (hmarginA a ha).2.trans hratio⟩
  have hlogA : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound A n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ) := by
    intro a ha
    exact hlogA₀ hNlA (mul_pos
      (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
        (Nat.pos_of_mem_divisors ha)) hd)
  have hlogD : ∀ a ∈ P.modulus.divisors,
      Real.log (((physicalBound D n) / (P.factor * a * d) : ℕ) : ℝ) ≤
        5 * Real.log (yNat n : ℝ) := by
    intro a ha
    let q : ℕ := P.factor * a * d
    have hq : 0 < q := by
      dsimp only [q]
      exact mul_pos
        (mul_pos (Nat.pos_of_ne_zero P.factor_ne_zero)
          (Nat.pos_of_mem_divisors ha)) hd
    have hlogC := hlogC₀ hNlC hq
    have hquot : physicalBound D n / q ≤ physicalBound C n / q := by
      apply Nat.div_le_div_right
      rw [hDend]
      exact hhigh
    by_cases hz : physicalBound D n / q = 0
    · rw [hz]
      have hylog0 : 0 ≤ Real.log (yNat n : ℝ) := by
        exact (by positivity : 0 < (1 / 5 : ℝ) * Scale.L n).le.trans
          hlogLower
      simpa only [Nat.cast_zero, Real.log_zero] using
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 5) hylog0)
    · have hleft : (0 : ℝ) < ((physicalBound D n / q : ℕ) : ℝ) := by
        positivity
      have hlogMono :
          Real.log ((physicalBound D n / q : ℕ) : ℝ) ≤
            Real.log ((physicalBound C n / q : ℕ) : ℝ) := by
        exact Real.log_le_log hleft (by exact_mod_cast hquot)
      exact hlogMono.trans hlogC
  have hraw₀ := hraw P hY₀ hlohi hhead hd hdsmooth hcop hlogA hlogD
  have hraw₁ :
      |((markedCell P (physicalBound A n) (physicalBound D n)
            (yNat n) d).card : ℝ) -
        ∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a| ≤
      (5 * Kraw * (D + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * Scale.L n) :=
    hraw₀.trans
      (raw_head_error_sum_le P hA.le hD.le hKraw.le hn hd hlogLower)
  have hscale : 0 ≤ (n : ℝ) / ((d : ℝ) * Scale.L n) := by positivity
  have hraw₁u :
      |((markedCell P (physicalBound A n) (physicalBound D n)
            (yNat n) d).card : ℝ) -
        ∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a| ≤
      (5 * Kraw * (C + A) * headMoebiusMass P) *
        (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    refine hraw₁.trans ?_
    rw [show
      (5 * Kraw * (D + A) * headMoebiusMass P) * (n : ℝ) /
          ((d : ℝ) * Scale.L n) =
        (5 * Kraw * (D + A) * headMoebiusMass P) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    rw [show
      (5 * Kraw * (C + A) * headMoebiusMass P) * (n : ℝ) /
          ((d : ℝ) * Scale.L n) =
        (5 * Kraw * (C + A) * headMoebiusMass P) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    apply mul_le_mul_of_nonneg_right _ hscale
    have hmass0 := headMoebiusMass_nonneg P
    nlinarith
  have hcommon := headDivisorMain_sum_sub_common_le P hA hD hn hd hd4
    hy2 hlogLower hmarginA hmarginD hlogA hlogD
  have hcollapse := common_endpoint_sum_eq_paperMarkedMain P A D
    (DickmanBasic.rho (paperDivisorCoordinate n d)) (n := n) (d := d) hd
  have hcommon' :
      |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a) - paperMarkedMain P A D n d| ≤
        (endpointFamilyCoefficient P D + endpointFamilyCoefficient P A) *
          (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    unfold paperMarkedMain
    rw [← hcollapse]
    exact hcommon
  have hfamilyD : endpointFamilyCoefficient P D ≤
      compactEndpointFamilyCoefficient P A C :=
    endpointFamilyCoefficient_le_compact P hA hAD hDC
  have hcommonU :
      |(∑ a ∈ P.modulus.divisors,
          headDivisorMain P (physicalBound A n) (physicalBound D n)
            (yNat n) d a) - paperMarkedMain P A D n d| ≤
        (compactEndpointFamilyCoefficient P A C +
          endpointFamilyCoefficient P A) *
        (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    refine hcommon'.trans ?_
    rw [show
      (endpointFamilyCoefficient P D + endpointFamilyCoefficient P A) *
          (n : ℝ) / ((d : ℝ) * Scale.L n) =
        (endpointFamilyCoefficient P D + endpointFamilyCoefficient P A) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    rw [show
      (compactEndpointFamilyCoefficient P A C +
          endpointFamilyCoefficient P A) * (n : ℝ) /
          ((d : ℝ) * Scale.L n) =
        (compactEndpointFamilyCoefficient P A C +
          endpointFamilyCoefficient P A) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) by ring]
    apply mul_le_mul_of_nonneg_right _ hscale
    linarith
  have htotal :
      |((markedCell P (physicalBound A n) (physicalBound D n)
            (yNat n) d).card : ℝ) - paperMarkedMain P A D n d| ≤
        K * (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    calc
      _ ≤
        |((markedCell P (physicalBound A n) (physicalBound D n)
              (yNat n) d).card : ℝ) -
          ∑ a ∈ P.modulus.divisors,
            headDivisorMain P (physicalBound A n) (physicalBound D n)
              (yNat n) d a| +
        |(∑ a ∈ P.modulus.divisors,
            headDivisorMain P (physicalBound A n) (physicalBound D n)
              (yNat n) d a) - paperMarkedMain P A D n d| :=
          abs_sub_le _ _ _
      _ ≤ (5 * Kraw * (C + A) * headMoebiusMass P) *
            (n : ℝ) / ((d : ℝ) * Scale.L n) +
          (compactEndpointFamilyCoefficient P A C +
            endpointFamilyCoefficient P A) *
            (n : ℝ) / ((d : ℝ) * Scale.L n) :=
        add_le_add hraw₁u hcommonU
      _ = (5 * Kraw * (C + A) * headMoebiusMass P +
            compactEndpointFamilyCoefficient P A C +
            endpointFamilyCoefficient P A) *
          ((n : ℝ) / ((d : ℝ) * Scale.L n)) := by ring
      _ ≤ K * ((n : ℝ) / ((d : ℝ) * Scale.L n)) := by
        apply mul_le_mul_of_nonneg_right _ hscale
        dsimp only [K]
        linarith
      _ = K * (n : ℝ) / ((d : ℝ) * Scale.L n) := by ring
  simpa only [D, hDend] using htotal

/-! ## Exact prefix normalization identities -/

theorem structuredCell_filter_le_eq
    (P : Pattern) {lo hi y k : ℕ} (hk : k ≤ hi) :
    (structuredCell P lo hi y).filter (fun m ↦ m ≤ k) =
      structuredCell P lo k y := by
  ext m
  simp only [Finset.mem_filter, mem_structuredCell, mem_smoothInterval]
  constructor
  · rintro ⟨⟨⟨hlom, hmhi, hsmooth⟩, hmatch⟩, hmk⟩
    exact ⟨⟨hlom, hmk, hsmooth⟩, hmatch⟩
  · rintro ⟨⟨hlom, hmk, hsmooth⟩, hmatch⟩
    exact ⟨⟨⟨hlom, hmk.trans hk, hsmooth⟩, hmatch⟩, hmk⟩

/-- The joint divisor/prefix counting average is literally the normalized
moving marked-cell cardinality. -/
theorem uniformAverage_divInd_mul_prefix_eq_markedCell_ratio
    (P : Pattern) {lo hi y k d : ℕ} (hk : k ≤ hi) :
    DivisibilityMomentBounds.uniformAverage
        (structuredCell P lo hi y)
        (fun m ↦ divInd d m * if m ≤ k then 1 else 0) =
      ((markedCell P lo k y d).card : ℝ) /
        ((structuredCell P lo hi y).card : ℝ) := by
  unfold DivisibilityMomentBounds.uniformAverage
  have hsum :
      (∑ m ∈ structuredCell P lo hi y,
          (divInd d m * if m ≤ k then 1 else 0)) =
        ∑ m ∈ (structuredCell P lo hi y).filter (fun m ↦ m ≤ k),
          divInd d m := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m hm
    by_cases hmk : m ≤ k <;> simp [hmk]
  rw [hsum, structuredCell_filter_le_eq P hk,
    DivisibilityMomentBounds.sum_divInd_eq_card_filter]
  rfl

/-- Exact identification of the centered counting expression with the
finite-probability covariance used by the bridge. -/
theorem uniformOnFinset_covariance_divInd_prefix_eq
    (S : Finset ℕ) (hS : S.Nonempty) (d k : ℕ) :
    (FiniteProbability.uniformOnFinset S hS).covariance
        (fun m : S ↦ divInd d (m : ℕ))
        (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0) =
      DivisibilityMomentBounds.uniformAverage S
          (fun m ↦ divInd d m * if m ≤ k then 1 else 0) -
        DivisibilityMomentBounds.uniformAverage S (divInd d) *
          DivisibilityMomentBounds.uniformAverage S
            (fun m ↦ if m ≤ k then 1 else 0) := by
  unfold FiniteProbability.covariance
  rw [FiniteProbability.uniformOnFinset_expect_eq,
    FiniteProbability.uniformOnFinset_expect_eq,
    FiniteProbability.uniformOnFinset_expect_eq]
  rw [show
    (∑ x : S, divInd d (x : ℕ) *
        if (x : ℕ) ≤ k then (1 : ℝ) else 0) =
      ∑ m ∈ S, divInd d m * if m ≤ k then (1 : ℝ) else 0 by
        simpa only using FiniteProbability.sum_subtype_eq_sum_filter S
          (fun m : ℕ ↦ divInd d m * if m ≤ k then (1 : ℝ) else 0)]
  rw [show (∑ x : S, divInd d (x : ℕ)) =
      ∑ m ∈ S, divInd d m by
        simpa only using FiniteProbability.sum_subtype_eq_sum_filter S
          (fun m : ℕ ↦ divInd d m)]
  rw [show (∑ x : S, if (x : ℕ) ≤ k then (1 : ℝ) else 0) =
      ∑ m ∈ S, if m ≤ k then (1 : ℝ) else 0 by
        simpa only using FiniteProbability.sum_subtype_eq_sum_filter S
          (fun m : ℕ ↦ if m ≤ k then (1 : ℝ) else 0)]
  unfold DivisibilityMomentBounds.uniformAverage
  rfl

/-- Quantitative normalization with an arbitrary nonnegative target. -/
theorem abs_normalized_ratio_sub_le
    {x y q z E F : ℝ} (hq : 0 < q) (hyhalf : q / 2 ≤ y)
    (hx : |x - q * z| ≤ E) (hy : |y - q| ≤ F) (hz : 0 ≤ z) :
    |x / y - z| ≤ 2 * (E + z * F) / q := by
  have hypos : 0 < y := (half_pos hq).trans_le hyhalf
  have hE : 0 ≤ E := (abs_nonneg (x - q * z)).trans hx
  have hF : 0 ≤ F := (abs_nonneg (y - q)).trans hy
  have hnum : 0 ≤ E + z * F := add_nonneg hE (mul_nonneg hz hF)
  have hinv : 1 / y ≤ 2 / q := by
    apply (div_le_div_iff₀ hypos hq).2
    linarith
  have hid : x / y - z = (x - q * z + z * (q - y)) / y := by
    field_simp [hypos.ne']
    ring
  rw [hid, abs_div, abs_of_pos hypos]
  calc
    |x - q * z + z * (q - y)| / y ≤
        (|x - q * z| + |z * (q - y)|) / y := by
      exact div_le_div_of_nonneg_right (abs_add_le _ _) hypos.le
    _ = (|x - q * z| + z * |y - q|) / y := by
      rw [abs_mul, abs_of_nonneg hz, abs_sub_comm q y]
    _ ≤ (E + z * F) / y := by
      apply div_le_div_of_nonneg_right _ hypos.le
      exact add_le_add hx (mul_le_mul_of_nonneg_left hy hz)
    _ = (E + z * F) * (1 / y) := by ring
    _ ≤ (E + z * F) * (2 / q) :=
      mul_le_mul_of_nonneg_left hinv hnum
    _ = 2 * (E + z * F) / q := by ring

/-- Relative physical length of a moving prefix. -/
def prefixFraction (A C : ℝ) (n k : ℕ) : ℝ :=
  (prefixScale n k - A) / (C - A)

theorem prefixFraction_nonneg_le_one
    {A C : ℝ} {n k : ℕ} (hAC : A < C)
    (hAD : A ≤ prefixScale n k) (hDC : prefixScale n k ≤ C) :
    0 ≤ prefixFraction A C n k ∧ prefixFraction A C n k ≤ 1 := by
  have hden : 0 < C - A := sub_pos.mpr hAC
  constructor
  · exact div_nonneg (sub_nonneg.mpr hAD) hden.le
  · apply (div_le_one hden).2
    linarith

theorem paperMarkedMain_moving_eq_fullDensity_mul_prefix
    (P : Pattern) {A C : ℝ} (hAC : A < C)
    {n k d : ℕ} (hd : 0 < d) :
    paperMarkedMain P A (prefixScale n k) n d =
      (paperCellDensity P A C * (n : ℝ)) *
        prefixFraction A C n k * paperDivisibilityMain n d := by
  rw [paperMarkedMain_eq_density_mul_divisibility P A
    (prefixScale n k) hd]
  unfold paperCellDensity prefixFraction
  have hden : C - A ≠ 0 := ne_of_gt (sub_pos.mpr hAC)
  field_simp [hden]

/-- Uniform joint divisor/prefix probability for the genuine counting law
on the full fixed physical cell.  The estimate is simultaneous in every
integer prefix and every admissible four-mark modulus. -/
theorem exists_uniform_movingPrefix_uniformAverage_divInd_bound
    (P : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n k d : ℕ},
      N₀ ≤ n → physicalBound A n < k → k ≤ physicalBound C n →
      0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      let S := structuredCell P (physicalBound A n)
        (physicalBound C n) (yNat n)
      S.Nonempty ∧
        |DivisibilityMomentBounds.uniformAverage S
            (fun m ↦ divInd d m * if m ≤ k then 1 else 0) -
          prefixFraction A C n k * paperDivisibilityMain n d| ≤
            K / ((d : ℝ) * Scale.L n) := by
  obtain ⟨Kmove, hKmove, Nmove, hmove⟩ :=
    exists_uniform_movingUpper_markedCell_paper_main_bound P hA hAC
  obtain ⟨Kfull, hKfull, Nfull, hfull⟩ :=
    exists_uniform_markedCell_paper_main_bound P hA hAC
  obtain ⟨Ndensity, hdensity⟩ :=
    exists_structuredCell_density_lower_bound P hA hAC
  let c : ℝ := paperCellDensity P A C
  have hc : 0 < c := paperCellDensity_pos P hAC
  have hrho : 0 < DickmanBasic.rho DickmanBasic.U :=
    DickmanBasic.rho_U_pos
  let K : ℝ :=
    2 * (Kmove + Kfull / DickmanBasic.rho DickmanBasic.U) / c
  have hK : 0 < K := by
    dsimp only [K]
    exact div_pos
      (mul_pos (by norm_num) (add_pos_of_pos_of_nonneg hKmove
        (div_nonneg hKfull.le hrho.le))) hc
  let N₀ := max 2 (max Nmove (max Nfull Ndensity))
  refine ⟨K, hK, N₀, ?_⟩
  intro n k d hN hlow hhigh hd hd4 hdsmooth hcop
  dsimp only
  have hNmove : Nmove ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNfull : Nfull ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNdensity : Ndensity ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hn : 1 < n := by
    dsimp only [N₀] at hN
    omega
  have hnpos : 0 < n := by omega
  have hL : 0 < Scale.L n := Scale.L_pos hn
  let S : Finset ℕ := structuredCell P (physicalBound A n)
    (physicalBound C n) (yNat n)
  let q : ℝ := c * (n : ℝ)
  let r : ℝ := prefixFraction A C n k
  let t : ℝ := paperDivisibilityMain n d
  let x : ℝ := ((markedCell P (physicalBound A n) k (yNat n) d).card : ℝ)
  let ycard : ℝ := (S.card : ℝ)
  have hq : 0 < q := by
    dsimp only [q]
    exact mul_pos hc (by exact_mod_cast hnpos)
  have hhalf : q / 2 ≤ ycard := by
    dsimp only [q, ycard, c, S]
    exact hdensity hNdensity
  have hSposR : 0 < (S.card : ℝ) := (half_pos hq).trans_le hhalf
  have hS : S.Nonempty := by
    exact Finset.card_pos.mp (by exact_mod_cast hSposR)
  have hfracCompact := prefixScale_mem_compact
    (hA.trans hAC).le hnpos hlow hhigh
  have hrange : 0 ≤ r ∧ r ≤ 1 := by
    dsimp only [r]
    exact prefixFraction_nonneg_le_one hAC hfracCompact.1.le
      hfracCompact.2
  have htRange := paperDivisibilityMain_nonneg_le hn hd hd4
  have ht0 : 0 ≤ t := by simpa only [t] using htRange.1
  have hz0 : 0 ≤ r * t := mul_nonneg hrange.1 ht0
  have hzUpper : r * t ≤
      1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) := by
    calc
      r * t ≤ 1 * t := mul_le_mul_of_nonneg_right hrange.2 ht0
      _ = t := one_mul t
      _ ≤ 1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) := by
        simpa only [t] using htRange.2
  have hx : |x - q * (r * t)| ≤
      Kmove * (n : ℝ) / ((d : ℝ) * Scale.L n) := by
    have hm := hmove hNmove hlow hhigh hd hd4 hdsmooth hcop
    have hmain := paperMarkedMain_moving_eq_fullDensity_mul_prefix
      P hAC (n := n) (k := k) (d := d) hd
    dsimp only [x, q, r, t, c]
    rw [show
      paperCellDensity P A C * (n : ℝ) *
          (prefixFraction A C n k * paperDivisibilityMain n d) =
        (paperCellDensity P A C * (n : ℝ)) *
          prefixFraction A C n k * paperDivisibilityMain n d by ring]
    rw [← hmain]
    exact hm
  have hOneLe : 1 ≤ yNat n ^ 4 := (show 1 ≤ d by omega).trans hd4
  have hy : |ycard - q| ≤ Kfull * (n : ℝ) / Scale.L n := by
    have hf := hfull (n := n) (d := 1) hNfull (by omega) hOneLe
      (by simp [Nat.mem_smoothNumbers]) (by simp)
    dsimp only [ycard, q, S, c]
    simpa [markedCell, paperMarkedMain_one] using hf
  have hratio := abs_normalized_ratio_sub_le hq hhalf hx hy hz0
  have hE0 : 0 ≤ Kmove * (n : ℝ) /
      ((d : ℝ) * Scale.L n) := by positivity
  have hF0 : 0 ≤ Kfull * (n : ℝ) / Scale.L n := by positivity
  have hzF : (r * t) * (Kfull * (n : ℝ) / Scale.L n) ≤
      (1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ))) *
        (Kfull * (n : ℝ) / Scale.L n) :=
    mul_le_mul_of_nonneg_right hzUpper hF0
  have hbound : 2 *
      (Kmove * (n : ℝ) / ((d : ℝ) * Scale.L n) +
        (r * t) * (Kfull * (n : ℝ) / Scale.L n)) / q ≤
      K / ((d : ℝ) * Scale.L n) := by
    calc
      _ ≤ 2 *
          (Kmove * (n : ℝ) / ((d : ℝ) * Scale.L n) +
            (1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ))) *
              (Kfull * (n : ℝ) / Scale.L n)) / q := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            (add_le_add (le_refl _) hzF) (by norm_num))
          hq.le
      _ = K / ((d : ℝ) * Scale.L n) := by
        dsimp only [K, q, c]
        have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hnpos.ne'
        have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
        field_simp [hc.ne', hrho.ne', hnR, hdR, hL.ne']
  refine ⟨by simpa only [S] using hS, ?_⟩
  rw [uniformAverage_divInd_mul_prefix_eq_markedCell_ratio P hhigh]
  change |x / ycard - r * t| ≤ _
  exact hratio.trans hbound

/-- Uniform centered divisor/prefix covariance for the un-tilted structured
cell.  The main terms from the moving prefix, the full divisor profile, and
the prefix mass cancel exactly; the remaining loss retains `1/d`. -/
theorem exists_uniform_movingPrefix_divInd_centered_bound
    (P : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n k d : ℕ},
      N₀ ≤ n → physicalBound A n < k → k ≤ physicalBound C n →
      0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      let S := structuredCell P (physicalBound A n)
        (physicalBound C n) (yNat n)
      |DivisibilityMomentBounds.uniformAverage S
          (fun m ↦ divInd d m * if m ≤ k then 1 else 0) -
        DivisibilityMomentBounds.uniformAverage S (divInd d) *
          DivisibilityMomentBounds.uniformAverage S
            (fun m ↦ if m ≤ k then 1 else 0)| ≤
        K / ((d : ℝ) * Scale.L n) := by
  obtain ⟨Kjoint, hKjoint, Nj, hjoint⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  obtain ⟨Kdiv, hKdiv, Nd, hdiv⟩ :=
    exists_uniform_uniformAverage_divInd_paper_bound P hA hAC
  have hLTop : Filter.Tendsto Scale.L Filter.atTop Filter.atTop := by
    simpa [Scale.L] using
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLEvent : ∀ᶠ n : ℕ in Filter.atTop, (1 : ℝ) ≤ Scale.L n :=
    hLTop.eventually (Filter.eventually_ge_atTop (1 : ℝ))
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.mp hLEvent
  let Adiv : ℝ := Kdiv + 1 / DickmanBasic.rho DickmanBasic.U
  let K : ℝ := Kjoint + Kdiv + Adiv * Kjoint
  have hrho : 0 < DickmanBasic.rho DickmanBasic.U :=
    DickmanBasic.rho_U_pos
  have hAdiv : 0 < Adiv := by
    dsimp only [Adiv]
    exact add_pos_of_pos_of_nonneg hKdiv (one_div_nonneg.mpr hrho.le)
  have hK : 0 < K := by
    dsimp only [K]
    positivity
  let N₀ := max Nj (max Nd NL)
  refine ⟨K, hK, N₀, ?_⟩
  intro n k d hN hlow hhigh hd hd4 hdsmooth hcop
  dsimp only
  have hNj : Nj ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNd : Nd ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hNl : NL ≤ n := by
    dsimp only [N₀] at hN
    omega
  have hL1 : (1 : ℝ) ≤ Scale.L n := hNL n hNl
  have hn : 1 < n := by
    by_contra hnle
    have hLle : Scale.L n ≤ 0 := by
      unfold Scale.L
      rw [Real.log_nonpos_iff (by positivity)]
      exact_mod_cast Nat.le_of_not_gt hnle
    linarith
  have hL : 0 < Scale.L n := Scale.L_pos hn
  let S : Finset ℕ := structuredCell P (physicalBound A n)
    (physicalBound C n) (yNat n)
  let J : ℝ := DivisibilityMomentBounds.uniformAverage S
    (fun m ↦ divInd d m * if m ≤ k then 1 else 0)
  let a : ℝ := DivisibilityMomentBounds.uniformAverage S (divInd d)
  let b : ℝ := DivisibilityMomentBounds.uniformAverage S
    (fun m ↦ if m ≤ k then 1 else 0)
  let r : ℝ := prefixFraction A C n k
  let t : ℝ := paperDivisibilityMain n d
  have hjRaw := hjoint hNj hlow hhigh hd hd4 hdsmooth hcop
  have hJ : |J - r * t| ≤ Kjoint / ((d : ℝ) * Scale.L n) := by
    dsimp only [J, r, t, S]
    exact hjRaw.2
  have ha : |a - t| ≤ Kdiv / ((d : ℝ) * Scale.L n) := by
    dsimp only [a, t, S]
    exact (hdiv hNd hd hd4 hdsmooth hcop).2
  have hOneLe : 1 ≤ yNat n ^ 4 := (show 1 ≤ d by omega).trans hd4
  have hbRaw := hjoint (n := n) (k := k) (d := 1) hNj hlow hhigh
    (by omega) hOneLe (by simp [Nat.mem_smoothNumbers]) (by simp)
  have hb : |b - r| ≤ Kjoint / Scale.L n := by
    dsimp only [b, r, S]
    simpa [paperDivisibilityMain_one, divInd] using hbRaw.2
  have hrange : 0 ≤ r ∧ r ≤ 1 := by
    dsimp only [r]
    have hcompact := prefixScale_mem_compact
      (hA.trans hAC).le (by omega : 0 < n) hlow hhigh
    exact prefixFraction_nonneg_le_one hAC hcompact.1.le hcompact.2
  have htRange := paperDivisibilityMain_nonneg_le hn hd hd4
  have ht0 : 0 ≤ t := by simpa only [t] using htRange.1
  have ha0 : 0 ≤ a := by
    dsimp only [a, DivisibilityMomentBounds.uniformAverage]
    exact div_nonneg (Finset.sum_nonneg fun m hm ↦ divInd_nonneg d m)
      (by positivity)
  have hdivL : Kdiv / ((d : ℝ) * Scale.L n) ≤ Kdiv / (d : ℝ) := by
    have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    have hden : (d : ℝ) ≤ (d : ℝ) * Scale.L n := by
      calc
        (d : ℝ) = (d : ℝ) * 1 := by ring
        _ ≤ (d : ℝ) * Scale.L n :=
          mul_le_mul_of_nonneg_left hL1 hdR.le
    exact div_le_div_of_nonneg_left hKdiv.le hdR hden
  have haUpper : a ≤ Adiv / (d : ℝ) := by
    have hdiff : a - t ≤ |a - t| := le_abs_self (a - t)
    have htUpper : t ≤
        1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) := by
      simpa only [t] using htRange.2
    calc
      a = (a - t) + t := by ring
      _ ≤ |a - t| + t := by linarith
      _ ≤ Kdiv / ((d : ℝ) * Scale.L n) +
          1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) :=
        add_le_add ha htUpper
      _ ≤ Kdiv / (d : ℝ) +
          1 / (DickmanBasic.rho DickmanBasic.U * (d : ℝ)) :=
        add_le_add hdivL (le_refl _)
      _ = Adiv / (d : ℝ) := by
        dsimp only [Adiv]
        field_simp [hrho.ne', (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]
  have hidentity : J - a * b =
      (J - r * t) + r * (t - a) + a * (r - b) := by ring
  rw [hidentity]
  have htri :
      |(J - r * t) + r * (t - a) + a * (r - b)| ≤
        |J - r * t| + r * |t - a| + a * |r - b| := by
    calc
      _ ≤ |(J - r * t) + r * (t - a)| + |a * (r - b)| :=
        abs_add_le _ _
      _ ≤ (|J - r * t| + |r * (t - a)|) + |a * (r - b)| :=
        add_le_add (abs_add_le _ _) (le_refl _)
      _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg hrange.1,
        abs_of_nonneg ha0]
  refine htri.trans ?_
  have hta : |t - a| ≤ Kdiv / ((d : ℝ) * Scale.L n) := by
    simpa only [abs_sub_comm t] using ha
  have hrb : |r - b| ≤ Kjoint / Scale.L n := by
    simpa only [abs_sub_comm r] using hb
  have hscaleDiv : 0 ≤ Kdiv / ((d : ℝ) * Scale.L n) := by positivity
  have hscaleJoint : 0 ≤ Kjoint / Scale.L n := by positivity
  calc
    |J - r * t| + r * |t - a| + a * |r - b| ≤
        Kjoint / ((d : ℝ) * Scale.L n) +
          r * (Kdiv / ((d : ℝ) * Scale.L n)) +
          a * (Kjoint / Scale.L n) := by
      exact add_le_add
        (add_le_add hJ (mul_le_mul_of_nonneg_left hta hrange.1))
        (mul_le_mul_of_nonneg_left hrb ha0)
    _ ≤ Kjoint / ((d : ℝ) * Scale.L n) +
          Kdiv / ((d : ℝ) * Scale.L n) +
          (Adiv / (d : ℝ)) * (Kjoint / Scale.L n) := by
      exact add_le_add
        (add_le_add (le_refl _)
          (mul_le_of_le_one_left hscaleDiv hrange.2))
        (mul_le_mul_of_nonneg_right haUpper hscaleJoint)
    _ = K / ((d : ℝ) * Scale.L n) := by
      dsimp only [K]
      field_simp [hL.ne', (by exact_mod_cast hd.ne' : (d : ℝ) ≠ 0)]

/-- Finite-probability form of the preceding centered estimate, with the
actual nonemptiness witness returned explicitly. -/
theorem exists_uniform_movingPrefix_divInd_covariance_bound
    (P : Pattern) {A C : ℝ} (hA : 0 < A) (hAC : A < C) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ {n k d : ℕ},
      N₀ ≤ n → physicalBound A n < k → k ≤ physicalBound C n →
      0 < d → d ≤ yNat n ^ 4 →
      d ∈ Nat.smoothNumbers (yNat n + 1) →
      Nat.Coprime d P.modulus →
      let S := structuredCell P (physicalBound A n)
        (physicalBound C n) (yNat n)
      ∃ hS : S.Nonempty,
        |(FiniteProbability.uniformOnFinset S hS).covariance
            (fun m : S ↦ divInd d (m : ℕ))
            (fun m : S ↦ if (m : ℕ) ≤ k then 1 else 0)| ≤
          K / ((d : ℝ) * Scale.L n) := by
  obtain ⟨K, hK, Nc, hc⟩ :=
    exists_uniform_movingPrefix_divInd_centered_bound P hA hAC
  obtain ⟨Kj, hKj, Nj, hj⟩ :=
    exists_uniform_movingPrefix_uniformAverage_divInd_bound P hA hAC
  refine ⟨K, hK, max Nc Nj, ?_⟩
  intro n k d hN hlow hhigh hd hd4 hdsmooth hcop
  dsimp only
  have hNc : Nc ≤ n := by omega
  have hNj : Nj ≤ n := by omega
  have hjoint := hj hNj hlow hhigh hd hd4 hdsmooth hcop
  let S : Finset ℕ := structuredCell P (physicalBound A n)
    (physicalBound C n) (yNat n)
  have hS : S.Nonempty := by simpa only [S] using hjoint.1
  refine ⟨hS, ?_⟩
  rw [uniformOnFinset_covariance_divInd_prefix_eq]
  simpa only [S] using hc hNc hlow hhigh hd hd4 hdsmooth hcop

end

end Erdos390.Full.PaperMovingPrefixMarkedCell
