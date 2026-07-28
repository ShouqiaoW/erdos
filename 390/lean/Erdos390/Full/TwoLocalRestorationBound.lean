import Erdos390.Full.OmittedTiltFallback

/-!
# Quantitative error of the exact two-local restoration

This file bounds every nonconstant term in the exact `N_{r,s}` numerator
using the arbitrary-modulus reciprocal fallback.  The result retains the
paper's weighted coefficient tails in both local coordinates; in particular,
it does not replace them by the cardinality of the exponent cutoff.
-/

open scoped BigOperators

namespace Erdos390.Full.TwoLocalRestorationBound

open ArithmeticModel FiniteProbability LocalFugacity LocalFugacityBounds
open OmittedTiltPairChamber

noncomputable section

variable {Omega : Type*} [Fintype Omega]

/-- The exact restored numerator `N_{r,s}` under an arbitrary finite law. -/
def pairRestoredNumerator (nu : FiniteProbability Omega)
    (value : Omega → ℕ) (p q Ap Aq : ℕ) (etaP etaQ L : ℝ)
    (r s : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 0 Ap, ∑ b ∈ Finset.Icc 0 Aq,
    coefficient (Real.exp (etaP / L)) a *
      coefficient (Real.exp (etaQ / L)) b *
        nu.expect (fun omega ↦
          divInd (pairPower p q (max r a) (max s b)) (value omega))

/-- The explicit reciprocal majorant for the nonconstant restoration
terms. -/
def pairRestorationError (p q Ap Aq r s : ℕ)
    (etaP etaQ L G : ℝ) : ℝ :=
  G * coefficientTail p Ap r etaP L * (1 / (q : ℝ) ^ s) +
  G * (1 / (p : ℝ) ^ r) * coefficientTail q Aq s etaQ L +
  G * coefficientTail p Ap r etaP L * coefficientTail q Aq s etaQ L

theorem pairRestorationError_nonneg (p q Ap Aq r s : ℕ)
    (etaP etaQ L G : ℝ) (hG : 0 ≤ G) :
    0 ≤ pairRestorationError p q Ap Aq r s etaP etaQ L G := by
  have hpTail := coefficientTail_nonneg p Ap r etaP L
  have hqTail := coefficientTail_nonneg q Aq s etaQ L
  have hpInv : 0 ≤ 1 / (p : ℝ) ^ r := by positivity
  have hqInv : 0 ≤ 1 / (q : ℝ) ^ s := by positivity
  unfold pairRestorationError
  exact add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hG hpTail) hqInv)
      (mul_nonneg (mul_nonneg hG hpInv) hqTail))
    (mul_nonneg (mul_nonneg hG hpTail) hqTail)

private theorem Icc_zero_eq_insert (A : ℕ) :
    Finset.Icc 0 A = insert 0 (Finset.Icc 1 A) := by
  ext a
  simp only [Finset.mem_Icc, Finset.mem_insert]
  omega

private theorem sum_Icc_zero_eq (A : ℕ) (f : ℕ → ℝ) :
    (∑ a ∈ Finset.Icc 0 A, f a) =
      f 0 + ∑ a ∈ Finset.Icc 1 A, f a := by
  rw [Icc_zero_eq_insert]
  have hzero : 0 ∉ Finset.Icc 1 A := by simp
  rw [Finset.sum_insert hzero]

/-- Exact separation of the constant, one-local, and two-local pieces. -/
theorem pairRestoredNumerator_decomposition
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    (p q Ap Aq : ℕ) (etaP etaQ L : ℝ) (r s : ℕ) :
    pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s =
      nu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega)) +
      (∑ a ∈ Finset.Icc 1 Ap,
        coefficient (Real.exp (etaP / L)) a *
          nu.expect (fun omega ↦
            divInd (pairPower p q (max r a) s) (value omega))) +
      (∑ b ∈ Finset.Icc 1 Aq,
        coefficient (Real.exp (etaQ / L)) b *
          nu.expect (fun omega ↦
            divInd (pairPower p q r (max s b)) (value omega))) +
      (∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
        coefficient (Real.exp (etaP / L)) a *
          coefficient (Real.exp (etaQ / L)) b *
            nu.expect (fun omega ↦
              divInd (pairPower p q (max r a) (max s b))
                (value omega))) := by
  unfold pairRestoredNumerator
  rw [sum_Icc_zero_eq]
  simp_rw [sum_Icc_zero_eq]
  simp only [coefficient_zero, max_eq_left (Nat.zero_le _), one_mul]
  rw [Finset.sum_add_distrib]
  ring_nf

private theorem abs_sum_mul_expect_le
    (nu : FiniteProbability Omega) (T : Finset ℕ)
    (c : ℕ → ℝ) (A : ℕ → Omega → ℝ)
    (hA : ∀ i ∈ T, ∀ omega, 0 ≤ A i omega) :
    |∑ i ∈ T, c i * nu.expect (A i)| ≤
      ∑ i ∈ T, |c i| * nu.expect (A i) := by
  calc
    |∑ i ∈ T, c i * nu.expect (A i)| ≤
        ∑ i ∈ T, |c i * nu.expect (A i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ T, |c i| * nu.expect (A i) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_mul, abs_of_nonneg (nu.expect_nonneg (A i) (hA i hi))]

/-- All restoration terms are controlled by the exact weighted coefficient
tails.  `G` is the reciprocal-event constant supplied by the arbitrary
modulus fallback. -/
theorem abs_pairRestoredNumerator_sub_expect_le
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q Ap Aq r s : ℕ} {etaP etaQ L G : ℝ}
    (hprob : ∀ u v : ℕ,
      nu.expect (fun omega ↦ divInd (pairPower p q u v) (value omega)) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v)) :
    |pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s -
        nu.expect (fun omega ↦ divInd (pairPower p q r s) (value omega))| ≤
      pairRestorationError p q Ap Aq r s etaP etaQ L G := by
  let EP : ℕ → ℝ := fun a ↦ nu.expect (fun omega ↦
    divInd (pairPower p q (max r a) s) (value omega))
  let EQ : ℕ → ℝ := fun b ↦ nu.expect (fun omega ↦
    divInd (pairPower p q r (max s b)) (value omega))
  let EPQ : ℕ → ℕ → ℝ := fun a b ↦ nu.expect (fun omega ↦
    divInd (pairPower p q (max r a) (max s b)) (value omega))
  let cp : ℕ → ℝ := fun a ↦ coefficient (Real.exp (etaP / L)) a
  let cq : ℕ → ℝ := fun b ↦ coefficient (Real.exp (etaQ / L)) b
  let SP : ℝ := ∑ a ∈ Finset.Icc 1 Ap, cp a * EP a
  let SQ : ℝ := ∑ b ∈ Finset.Icc 1 Aq, cq b * EQ b
  let SPQ : ℝ := ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
    cp a * cq b * EPQ a b
  have hdecomp :
      pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s -
          nu.expect (fun omega ↦
            divInd (pairPower p q r s) (value omega)) = SP + SQ + SPQ := by
    rw [pairRestoredNumerator_decomposition]
    dsimp only [SP, SQ, SPQ, EP, EQ, EPQ, cp, cq]
    ring
  have hEP0 : ∀ a, 0 ≤ EP a := by
    intro a
    exact nu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hEQ0 : ∀ b, 0 ≤ EQ b := by
    intro b
    exact nu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hEPQ0 : ∀ a b, 0 ≤ EPQ a b := by
    intro a b
    exact nu.expect_nonneg _ fun omega ↦ divInd_nonneg _ _
  have hSP : |SP| ≤
      G * coefficientTail p Ap r etaP L * (1 / (q : ℝ) ^ s) := by
    calc
      |SP| ≤ ∑ a ∈ Finset.Icc 1 Ap, |cp a| * EP a := by
        dsimp only [SP]
        exact abs_sum_mul_expect_le nu (Finset.Icc 1 Ap) cp
          (fun a omega ↦ divInd (pairPower p q (max r a) s) (value omega))
          (fun a ha omega ↦ divInd_nonneg _ _)
      _ ≤ ∑ a ∈ Finset.Icc 1 Ap,
          |cp a| * (G / ((p : ℝ) ^ max r a * (q : ℝ) ^ s)) := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (hprob (max r a) s) (abs_nonneg _)
      _ = G * coefficientTail p Ap r etaP L * (1 / (q : ℝ) ^ s) := by
        unfold coefficientTail
        dsimp only [cp]
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a ha
        norm_num only [Nat.cast_pow]
        ring
  have hSQ : |SQ| ≤
      G * (1 / (p : ℝ) ^ r) * coefficientTail q Aq s etaQ L := by
    calc
      |SQ| ≤ ∑ b ∈ Finset.Icc 1 Aq, |cq b| * EQ b := by
        dsimp only [SQ]
        exact abs_sum_mul_expect_le nu (Finset.Icc 1 Aq) cq
          (fun b omega ↦ divInd (pairPower p q r (max s b)) (value omega))
          (fun b hb omega ↦ divInd_nonneg _ _)
      _ ≤ ∑ b ∈ Finset.Icc 1 Aq,
          |cq b| * (G / ((p : ℝ) ^ r * (q : ℝ) ^ max s b)) := by
        apply Finset.sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left (hprob r (max s b)) (abs_nonneg _)
      _ = G * (1 / (p : ℝ) ^ r) * coefficientTail q Aq s etaQ L := by
        unfold coefficientTail
        dsimp only [cq]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b hb
        norm_num only [Nat.cast_pow]
        ring
  have hSPQ : |SPQ| ≤
      G * coefficientTail p Ap r etaP L *
        coefficientTail q Aq s etaQ L := by
    calc
      |SPQ| ≤ ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
          |cp a * cq b * EPQ a b| := by
        dsimp only [SPQ]
        calc
          |∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
              cp a * cq b * EPQ a b| ≤
              ∑ a ∈ Finset.Icc 1 Ap,
                |∑ b ∈ Finset.Icc 1 Aq, cp a * cq b * EPQ a b| :=
            Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
              |cp a * cq b * EPQ a b| := by
            apply Finset.sum_le_sum
            intro a ha
            exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
          |cp a| * |cq b| * EPQ a b := by
        apply Finset.sum_congr rfl
        intro a ha
        apply Finset.sum_congr rfl
        intro b hb
        rw [abs_mul, abs_mul, abs_of_nonneg (hEPQ0 a b)]
      _ ≤ ∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
          |cp a| * |cq b| *
            (G / ((p : ℝ) ^ max r a * (q : ℝ) ^ max s b)) := by
        apply Finset.sum_le_sum
        intro a ha
        apply Finset.sum_le_sum
        intro b hb
        exact mul_le_mul_of_nonneg_left (hprob (max r a) (max s b))
          (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = G * coefficientTail p Ap r etaP L *
          coefficientTail q Aq s etaQ L := by
        unfold coefficientTail
        dsimp only [cp, cq]
        calc
          (∑ a ∈ Finset.Icc 1 Ap, ∑ b ∈ Finset.Icc 1 Aq,
              |coefficient (Real.exp (etaP / L)) a| *
                |coefficient (Real.exp (etaQ / L)) b| *
                (G / ((p : ℝ) ^ max r a * (q : ℝ) ^ max s b))) =
              ∑ a ∈ Finset.Icc 1 Ap,
                (G * (|coefficient (Real.exp (etaP / L)) a| /
                  (p : ℝ) ^ max r a)) *
                  (∑ b ∈ Finset.Icc 1 Aq,
                    |coefficient (Real.exp (etaQ / L)) b| /
                      (q : ℝ) ^ max s b) := by
            apply Finset.sum_congr rfl
            intro a ha
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro b hb
            ring
          _ = G *
              (∑ a ∈ Finset.Icc 1 Ap,
                |coefficient (Real.exp (etaP / L)) a| /
                  (p : ℝ) ^ max r a) *
              (∑ b ∈ Finset.Icc 1 Aq,
                |coefficient (Real.exp (etaQ / L)) b| /
                  (q : ℝ) ^ max s b) := by
            conv_lhs =>
              rw [← Finset.sum_mul]
              congr
              rw [← Finset.mul_sum]
        norm_num only [Nat.cast_pow]
  rw [hdecomp]
  exact (abs_add_three SP SQ SPQ).trans (by
    simpa only [pairRestorationError] using add_le_add_three hSP hSQ hSPQ)

/-- The restored normalizer differs from one by the same explicit
coefficient-tail ledger at `(r,s)=(0,0)`. -/
theorem abs_pairRestoredNormalizer_sub_one_le
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q Ap Aq : ℕ} {etaP etaQ L G : ℝ}
    (hprob : ∀ u v : ℕ,
      nu.expect (fun omega ↦ divInd (pairPower p q u v) (value omega)) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v)) :
    |pairRestoredNumerator nu value p q Ap Aq etaP etaQ L 0 0 - 1| ≤
      pairRestorationError p q Ap Aq 0 0 etaP etaQ L G := by
  have h := abs_pairRestoredNumerator_sub_expect_le
    (nu := nu) (value := value) (p := p) (q := q) (Ap := Ap) (Aq := Aq)
    (r := 0) (s := 0) (etaP := etaP) (etaQ := etaQ) (L := L) (G := G)
    hprob
  have hone : nu.expect (fun omega ↦
      divInd (pairPower p q 0 0) (value omega)) = 1 := by
    unfold pairPower divInd FiniteProbability.expect
    simp [nu.mass_sum]
  rwa [hone] at h

/-- Elementary normalized-quotient perturbation with an explicit stable
denominator. -/
theorem abs_div_sub_le_of_abs_den_sub_one_le_half
    {N P D M deltaN deltaP deltaD : ℝ}
    (hdeltaN : 0 ≤ deltaN) (hdeltaP : 0 ≤ deltaP)
    (hdeltaD : 0 ≤ deltaD)
    (hN : |N - P| ≤ deltaN) (hP : |P - M| ≤ deltaP)
    (hD : |D - 1| ≤ deltaD) (hhalf : deltaD ≤ 1 / 2) :
    |N / D - M| ≤ 2 * (deltaN + deltaP + |M| * deltaD) := by
  have hDone : |D - 1| ≤ 1 / 2 := hD.trans hhalf
  have hDpos : 0 < D := by
    have hneg := neg_abs_le (D - 1)
    linarith
  have hDne : D ≠ 0 := ne_of_gt hDpos
  have hinv : 1 / D ≤ 2 := by
    apply (div_le_iff₀ hDpos).2
    linarith [neg_abs_le (D - 1)]
  have hnum : |(N - P) + (P - M) + M * (1 - D)| ≤
      deltaN + deltaP + |M| * deltaD := by
    calc
      |(N - P) + (P - M) + M * (1 - D)| ≤
          |N - P| + |P - M| + |M * (1 - D)| := abs_add_three _ _ _
      _ = |N - P| + |P - M| + |M| * |D - 1| := by
        rw [abs_mul]
        congr 2
        exact abs_sub_comm 1 D
      _ ≤ deltaN + deltaP + |M| * deltaD := by
        exact add_le_add_three hN hP
          (mul_le_mul_of_nonneg_left hD (abs_nonneg M))
  have htarget0 : 0 ≤ deltaN + deltaP + |M| * deltaD := by positivity
  have hid : N / D - M = ((N - P) + (P - M) + M * (1 - D)) / D := by
    field_simp [hDne]
    ring
  rw [hid, abs_div, abs_of_pos hDpos]
  calc
    |(N - P) + (P - M) + M * (1 - D)| / D ≤
        (deltaN + deltaP + |M| * deltaD) / D :=
      div_le_div_of_nonneg_right hnum hDpos.le
    _ = (deltaN + deltaP + |M| * deltaD) * (1 / D) := by ring
    _ ≤ (deltaN + deltaP + |M| * deltaD) * 2 :=
      mul_le_mul_of_nonneg_left hinv htarget0
    _ = 2 * (deltaN + deltaP + |M| * deltaD) := by ring

/-- Combining the sharp omitted-law main term with the exact local
restoration gives a normalized full-law approximation.  This theorem is the
finite quotient step; the four-mark module supplies `hmain`, while the
coefficient and tail modules bound the displayed errors. -/
theorem abs_pairRestoredQuotient_sub_main_le
    (nu : FiniteProbability Omega) (value : Omega → ℕ)
    {p q Ap Aq r s : ℕ} {etaP etaQ L G main epsilon : ℝ}
    (hprob : ∀ u v : ℕ,
      nu.expect (fun omega ↦ divInd (pairPower p q u v) (value omega)) ≤
        G / ((p : ℝ) ^ u * (q : ℝ) ^ v))
    (hG : 0 ≤ G)
    (hmain : |nu.expect (fun omega ↦
        divInd (pairPower p q r s) (value omega)) - main| ≤ epsilon)
    (hepsilon : 0 ≤ epsilon)
    (hhalf : pairRestorationError p q Ap Aq 0 0 etaP etaQ L G ≤ 1 / 2) :
    |pairRestoredNumerator nu value p q Ap Aq etaP etaQ L r s /
        pairRestoredNumerator nu value p q Ap Aq etaP etaQ L 0 0 - main| ≤
      2 * (pairRestorationError p q Ap Aq r s etaP etaQ L G + epsilon +
        |main| * pairRestorationError p q Ap Aq 0 0 etaP etaQ L G) := by
  have hrestore := abs_pairRestoredNumerator_sub_expect_le
    (nu := nu) (value := value) (p := p) (q := q) (Ap := Ap) (Aq := Aq)
    (r := r) (s := s) (etaP := etaP) (etaQ := etaQ) (L := L) (G := G)
    hprob
  have hnormalizer := abs_pairRestoredNormalizer_sub_one_le
    (nu := nu) (value := value) (p := p) (q := q) (Ap := Ap) (Aq := Aq)
    (etaP := etaP) (etaQ := etaQ) (L := L) (G := G) hprob
  exact abs_div_sub_le_of_abs_den_sub_one_le_half
    (pairRestorationError_nonneg p q Ap Aq r s etaP etaQ L G hG)
    hepsilon
    (pairRestorationError_nonneg p q Ap Aq 0 0 etaP etaQ L G hG)
    hrestore hmain hnormalizer hhalf

end

end Erdos390.Full.TwoLocalRestorationBound
