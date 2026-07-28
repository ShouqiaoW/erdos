import Erdos390.WholePaper.BankPaperFourFiveOrderedLastPrimeExpansion
import Erdos390.WholePaper.BankPaperFourFiveProductMeasureTelescope
import Mathlib.Data.Nat.Find

/-!
# Moving-face mass and bounded-variation certificates

For fixed values of all but one logarithmic prime coordinate, the simplex
kernel is increasing until the moving face and is zero afterwards.  Its
height is at most one because the omitted last-prime coordinate has
logarithmic size at least one.  Thus its right-endpoint-plus-variation norm
is at most two: at most one unit while increasing and at most one unit for
the unique cutoff jump.

This file proves that finite statement first for an abstract monotone
sequence, then instantiates it for the literal logarithmic moving-face
kernel.  The one-, two-, and three-coordinate kernels are finally fed into
the product-measure telescope with `V = 2`.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeSums

/-! ## A finite one-jump BV lemma -/

/-- A sequence which agrees with `g` on `(A,R]` and is zero elsewhere. -/
def fourFiveCutoffSequence
    (A R : Nat) (g : Nat -> Real) (n : Nat) : Real :=
  if A < n ∧ n <= R then g n else 0

/-- The right discrete BV norm only depends on the endpoint and the adjacent
differences appearing in its definition. -/
theorem fourFiveRightDiscreteBVNorm_congr
    {f g : Nat -> Real} {A Y : Nat}
    (hY : f Y = g Y)
    (hstep : ∀ n ∈ Finset.Ioc A (Y - 1),
      f (n + 1) - f n = g (n + 1) - g n) :
    fourFiveRightDiscreteBVNorm f A Y =
      fourFiveRightDiscreteBVNorm g A Y := by
  unfold fourFiveRightDiscreteBVNorm
  rw [hY]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [hstep n hn]

/-- An increasing sequence bounded between zero and one, stopped after a
single natural cutoff, has paper BV norm at most two. -/
theorem fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
    (g : Nat -> Real) {A R Y : Nat} (hAY : A <= Y)
    (hmono : ∀ a ∈ Finset.Icc A Y,
      ∀ b ∈ Finset.Icc A Y, a <= b -> g a <= g b)
    (hnonneg : ∀ n ∈ Finset.Icc A Y, 0 <= g n)
    (hone : ∀ n ∈ Finset.Icc A Y, g n <= 1) :
    fourFiveRightDiscreteBVNorm
        (fourFiveCutoffSequence A R g) A Y <= 2 := by
  by_cases hAYlt : A < Y
  · have hsuccAY : A + 1 <= Y := by omega
    have hinterval : Finset.Ioc A (Y - 1) = Finset.Ico (A + 1) Y := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hA1mem : A + 1 ∈ Finset.Icc A Y :=
      Finset.mem_Icc.mpr ⟨by omega, hsuccAY⟩
    have hYmem : Y ∈ Finset.Icc A Y :=
      Finset.mem_Icc.mpr ⟨hAY, le_rfl⟩
    by_cases hYR : Y <= R
    · have hvariation :
          (∑ n ∈ Finset.Ioc A (Y - 1),
            |fourFiveCutoffSequence A R g (n + 1) -
              fourFiveCutoffSequence A R g n|) =
            g Y - g (A + 1) := by
        rw [hinterval]
        calc
          (∑ n ∈ Finset.Ico (A + 1) Y,
              |fourFiveCutoffSequence A R g (n + 1) -
                fourFiveCutoffSequence A R g n|) =
              ∑ n ∈ Finset.Ico (A + 1) Y,
                (g (n + 1) - g n) := by
            apply Finset.sum_congr rfl
            intro n hn
            have hnData := Finset.mem_Ico.mp hn
            have hnMem : n ∈ Finset.Icc A Y :=
              Finset.mem_Icc.mpr ⟨by omega, hnData.2.le⟩
            have hn1Mem : n + 1 ∈ Finset.Icc A Y :=
              Finset.mem_Icc.mpr ⟨by omega, by omega⟩
            have hnR : n <= R := hnData.2.le.trans hYR
            have hn1R : n + 1 <= R := by omega
            have hnActive : A < n ∧ n <= R := by
              exact ⟨by omega, hnR⟩
            have hn1Active : A < n + 1 ∧ n + 1 <= R := by
              exact ⟨by omega, hn1R⟩
            have hcutn : fourFiveCutoffSequence A R g n = g n := by
              rw [fourFiveCutoffSequence, if_pos hnActive]
            have hcutn1 :
                fourFiveCutoffSequence A R g (n + 1) = g (n + 1) := by
              rw [fourFiveCutoffSequence, if_pos hn1Active]
            have hdiff : 0 <= g (n + 1) - g n :=
              sub_nonneg.mpr (hmono n hnMem (n + 1) hn1Mem (by omega))
            rw [hcutn1, hcutn, abs_of_nonneg hdiff]
          _ = g Y - g (A + 1) :=
            Finset.sum_Ico_sub g hsuccAY
      unfold fourFiveRightDiscreteBVNorm
      rw [hvariation]
      have hcutY : fourFiveCutoffSequence A R g Y = g Y := by
        simp [fourFiveCutoffSequence, hAYlt, hYR]
      rw [hcutY, abs_of_nonneg (hnonneg Y hYmem)]
      linarith [hone Y hYmem, hnonneg (A + 1) hA1mem]
    · have hstep : ∀ n ∈ Finset.Ioc A (Y - 1),
          |fourFiveCutoffSequence A R g (n + 1) -
              fourFiveCutoffSequence A R g n| <=
            (g (n + 1) - g n) +
              (if n = R then 1 else 0) := by
        intro n hn
        have hnData := Finset.mem_Ioc.mp hn
        have hnMem : n ∈ Finset.Icc A Y :=
          Finset.mem_Icc.mpr ⟨hnData.1.le, by omega⟩
        have hn1Mem : n + 1 ∈ Finset.Icc A Y :=
          Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have hgnMono : g n <= g (n + 1) :=
          hmono n hnMem (n + 1) hn1Mem (by omega)
        by_cases hnR : n <= R
        · by_cases hn1R : n + 1 <= R
          · have hnNe : n ≠ R := by omega
            have hnActive : A < n ∧ n <= R :=
              ⟨hnData.1, hnR⟩
            have hn1Active : A < n + 1 ∧ n + 1 <= R :=
              ⟨by omega, hn1R⟩
            have hcutn : fourFiveCutoffSequence A R g n = g n := by
              rw [fourFiveCutoffSequence, if_pos hnActive]
            have hcutn1 :
                fourFiveCutoffSequence A R g (n + 1) = g (n + 1) := by
              rw [fourFiveCutoffSequence, if_pos hn1Active]
            rw [hcutn1, hcutn, if_neg hnNe,
              abs_of_nonneg (sub_nonneg.mpr hgnMono), add_zero]
          · have hnEq : n = R := by omega
            subst n
            have hRMem : R ∈ Finset.Icc A Y := hnMem
            have hR1Mem : R + 1 ∈ Finset.Icc A Y := hn1Mem
            have hRActive : A < R ∧ R <= R :=
              ⟨hnData.1, le_rfl⟩
            have hR1Inactive : ¬(A < R + 1 ∧ R + 1 <= R) := by
              omega
            have hcutR : fourFiveCutoffSequence A R g R = g R := by
              rw [fourFiveCutoffSequence, if_pos hRActive]
            have hcutR1 :
                fourFiveCutoffSequence A R g (R + 1) = 0 := by
              rw [fourFiveCutoffSequence, if_neg hR1Inactive]
            rw [hcutR1, hcutR, if_pos rfl, zero_sub, abs_neg,
              abs_of_nonneg (hnonneg R hRMem)]
            linarith [hone R hRMem,
              hmono R hRMem (R + 1) hR1Mem (by omega)]
        · have hn1R : ¬n + 1 <= R := by omega
          have hnNe : n ≠ R := by omega
          have hnInactive : ¬(A < n ∧ n <= R) := by
            intro h
            exact hnR h.2
          have hn1Inactive : ¬(A < n + 1 ∧ n + 1 <= R) := by
            intro h
            exact hn1R h.2
          have hcutn : fourFiveCutoffSequence A R g n = 0 := by
            rw [fourFiveCutoffSequence, if_neg hnInactive]
          have hcutn1 :
              fourFiveCutoffSequence A R g (n + 1) = 0 := by
            rw [fourFiveCutoffSequence, if_neg hn1Inactive]
          rw [hcutn1, hcutn, sub_self, abs_zero, if_neg hnNe, add_zero]
          exact sub_nonneg.mpr hgnMono
      have hboundary :
          (∑ n ∈ Finset.Ioc A (Y - 1),
            (if n = R then (1 : Real) else 0)) <= 1 := by
        classical
        rw [Finset.sum_ite_eq']
        split_ifs <;> norm_num
      have hvariation :
          (∑ n ∈ Finset.Ioc A (Y - 1),
            |fourFiveCutoffSequence A R g (n + 1) -
              fourFiveCutoffSequence A R g n|) <= 2 := by
        calc
          (∑ n ∈ Finset.Ioc A (Y - 1),
              |fourFiveCutoffSequence A R g (n + 1) -
                fourFiveCutoffSequence A R g n|) <=
              ∑ n ∈ Finset.Ioc A (Y - 1),
                ((g (n + 1) - g n) +
                  (if n = R then 1 else 0)) := by
            apply Finset.sum_le_sum
            intro n hn
            exact hstep n hn
          _ = (g Y - g (A + 1)) +
              ∑ n ∈ Finset.Ioc A (Y - 1),
                (if n = R then 1 else 0) := by
            rw [Finset.sum_add_distrib, hinterval,
              Finset.sum_Ico_sub g hsuccAY]
          _ <= 2 := by
            linarith [hone Y hYmem, hnonneg (A + 1) hA1mem,
              hboundary]
      unfold fourFiveRightDiscreteBVNorm
      have hcutY : fourFiveCutoffSequence A R g Y = 0 := by
        simp [fourFiveCutoffSequence, show ¬Y <= R by omega]
      rw [hcutY, abs_zero, zero_add]
      exact hvariation
  · have hYA : Y = A := le_antisymm (not_lt.mp hAYlt) hAY
    subst Y
    unfold fourFiveRightDiscreteBVNorm
    have hempty : Finset.Ioc A (A - 1) = ∅ := by
      exact Finset.Ioc_eq_empty_of_le (by omega)
    rw [hempty]
    simp [fourFiveCutoffSequence]

/-! ## The literal logarithmic moving face -/

/-- Logarithmic prime coordinate `log n / log y`. -/
def fourFiveLogCoordinate (y n : Nat) : Real :=
  Real.log (n : Real) / Real.log (y : Real)

/-- The literal one-dimensional conditional simplex kernel.  The first
condition centers it on the anchored interval `(A,Y]`; the second is the
strict moving face. -/
def fourFiveMovingFaceKernel
    (A y : Nat) (u c : Real) (n : Nat) : Real :=
  if A < n ∧ fourFiveLogCoordinate y n < u - c - 1 then
    (u - c - fourFiveLogCoordinate y n)⁻¹
  else 0

/-- Greatest active integer at or below `Y`. -/
def fourFiveMovingFaceCutoff
    (A Y y : Nat) (u c : Real) : Nat :=
  Nat.findGreatest
    (fun n => A < n ∧ fourFiveLogCoordinate y n < u - c - 1) Y

/-- Freeze the reciprocal kernel at the cutoff.  This gives a genuinely
monotone bounded extension on the whole finite interval. -/
def fourFiveMovingFaceMonotoneExtension
    (A Y y : Nat) (u c : Real) (n : Nat) : Real :=
  let R := fourFiveMovingFaceCutoff A Y y u c
  (u - c - fourFiveLogCoordinate y (min n R))⁻¹

theorem fourFiveLogCoordinate_mono
    {y a b : Nat} (hy : 2 <= y) (ha : 1 <= a) (hab : a <= b) :
    fourFiveLogCoordinate y a <= fourFiveLogCoordinate y b := by
  have hylog : 0 < Real.log (y : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have halog : Real.log (a : Real) <= Real.log (b : Real) := by
    apply Real.log_le_log
    · exact_mod_cast (show 0 < a by omega)
    · exact_mod_cast hab
  unfold fourFiveLogCoordinate
  exact (div_le_div_iff_of_pos_right hylog).mpr halog

/-- On `(A,Y]`, membership under the logarithmic face is exactly membership
below the greatest active integer. -/
theorem fourFiveMovingFace_active_iff_le_cutoff
    {A Y y n : Nat} {u c : Real} (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    (fourFiveLogCoordinate y n < u - c - 1) ↔
      n <= fourFiveMovingFaceCutoff A Y y u c := by
  let P : Nat -> Prop :=
    fun k => A < k ∧ fourFiveLogCoordinate y k < u - c - 1
  let R := Nat.findGreatest P Y
  have hnData := Finset.mem_Ioc.mp hn
  constructor
  · intro hface
    exact Nat.le_findGreatest hnData.2 ⟨hnData.1, hface⟩
  · intro hnR
    have hRpos : 0 < R :=
      lt_of_le_of_lt (Nat.zero_le A) (hnData.1.trans_le hnR)
    have hPR : P R := Nat.findGreatest_of_ne_zero rfl hRpos.ne'
    have hnOne : 1 <= n := by omega
    have hscale := fourFiveLogCoordinate_mono hy hnOne hnR
    exact hscale.trans_lt hPR.2

/-- The literal face kernel agrees on every relevant coordinate with the
single-cutoff sequence built from its monotone extension. -/
theorem fourFiveMovingFaceKernel_eq_cutoffSequence
    {A Y y n : Nat} {u c : Real} (hy : 2 <= y) (hyA : y <= A)
    (hn : n ∈ Finset.Ioc A Y) :
    fourFiveMovingFaceKernel A y u c n =
      fourFiveCutoffSequence A
        (fourFiveMovingFaceCutoff A Y y u c)
        (fourFiveMovingFaceMonotoneExtension A Y y u c) n := by
  have hnData := Finset.mem_Ioc.mp hn
  have hiff := fourFiveMovingFace_active_iff_le_cutoff
    (u := u) (c := c) hy hyA hn
  by_cases hface : fourFiveLogCoordinate y n < u - c - 1
  · have hnR := hiff.mp hface
    simp [fourFiveMovingFaceKernel, fourFiveCutoffSequence,
      fourFiveMovingFaceMonotoneExtension, hface, hnData.1, hnR]
  · have hnR : ¬n <= fourFiveMovingFaceCutoff A Y y u c :=
      mt hiff.mpr hface
    simp [fourFiveMovingFaceKernel, fourFiveCutoffSequence,
      hface, hnData.1, hnR]

/-- The frozen reciprocal kernel is increasing and lies in `[0,1]` on the
finite coordinate interval. -/
theorem fourFiveMovingFaceMonotoneExtension_certificate
    {A Y y : Nat} {u c : Real} (hy : 2 <= y) (hyA : y <= A)
    (_hAY : A <= Y)
    (hAR : A <= fourFiveMovingFaceCutoff A Y y u c) :
    (∀ a ∈ Finset.Icc A Y,
      ∀ b ∈ Finset.Icc A Y, a <= b ->
        fourFiveMovingFaceMonotoneExtension A Y y u c a <=
          fourFiveMovingFaceMonotoneExtension A Y y u c b) ∧
    (∀ n ∈ Finset.Icc A Y,
      0 <= fourFiveMovingFaceMonotoneExtension A Y y u c n) ∧
    (∀ n ∈ Finset.Icc A Y,
      fourFiveMovingFaceMonotoneExtension A Y y u c n <= 1) := by
  let R := fourFiveMovingFaceCutoff A Y y u c
  have hAR' : A <= R := hAR
  have hAone : 1 <= A := by omega
  have hRpos : 0 < R := by omega
  have hPR : A < R ∧
      fourFiveLogCoordinate y R < u - c - 1 :=
    Nat.findGreatest_of_ne_zero rfl hRpos.ne'
  have hminBounds : ∀ n ∈ Finset.Icc A Y,
      A <= min n R ∧ min n R <= R := by
    intro n hn
    have hnData := Finset.mem_Icc.mp hn
    exact ⟨le_min hnData.1 hAR', min_le_right _ _⟩
  have hden : ∀ n ∈ Finset.Icc A Y,
      1 <= u - c - fourFiveLogCoordinate y (min n R) := by
    intro n hn
    have hcoord := fourFiveLogCoordinate_mono hy
      (hAone.trans (hminBounds n hn).1) (hminBounds n hn).2
    linarith [hcoord, hPR.2]
  refine ⟨?_, ?_, ?_⟩
  · intro a ha b hb hab
    have hminab : min a R <= min b R := min_le_min_right R hab
    have hcoord := fourFiveLogCoordinate_mono hy
      (hAone.trans (hminBounds a ha).1) hminab
    have hdenA : 0 < u - c - fourFiveLogCoordinate y (min a R) :=
      lt_of_lt_of_le zero_lt_one (hden a ha)
    have hdenB : 0 < u - c - fourFiveLogCoordinate y (min b R) :=
      lt_of_lt_of_le zero_lt_one (hden b hb)
    unfold fourFiveMovingFaceMonotoneExtension
    exact (inv_le_inv₀ hdenA hdenB).mpr (by linarith)
  · intro n hn
    unfold fourFiveMovingFaceMonotoneExtension
    exact inv_nonneg.mpr (by linarith [hden n hn])
  · intro n hn
    unfold fourFiveMovingFaceMonotoneExtension
    have hdenPos : 0 <
        u - c - fourFiveLogCoordinate y
          (min n (fourFiveMovingFaceCutoff A Y y u c)) :=
      lt_of_lt_of_le zero_lt_one (hden n hn)
    simpa only [inv_one] using
      (inv_le_inv₀ hdenPos zero_lt_one).mpr (hden n hn)

/-!
The preceding certificate has an irrelevant `R < A` branch: the stopped
sequence is identically zero there.  Splitting that case first gives the
clean unconditional BV statement actually used below.
-/

/-- Every logarithmic moving-face kernel has right discrete BV norm at most
two, uniformly in the moving endpoint and in the conditioned coordinates. -/
theorem fourFiveRightDiscreteBVNorm_movingFace_le_two
    {A Y y : Nat} {u c : Real} (hy : 2 <= y) (hyA : y <= A)
    (hAY : A <= Y) :
    fourFiveRightDiscreteBVNorm
        (fourFiveMovingFaceKernel A y u c) A Y <= 2 := by
  let R := fourFiveMovingFaceCutoff A Y y u c
  let g := fourFiveMovingFaceMonotoneExtension A Y y u c
  by_cases hRA : R < A
  · have hzero : ∀ n ∈ Finset.Ioc A Y,
        fourFiveMovingFaceKernel A y u c n = 0 := by
      intro n hn
      have hiff := fourFiveMovingFace_active_iff_le_cutoff
        (u := u) (c := c) hy hyA hn
      unfold fourFiveMovingFaceKernel
      rw [if_neg]
      intro hactive
      have hnR := hiff.mp hactive.2
      have hnA := (Finset.mem_Ioc.mp hn).1
      omega
    unfold fourFiveRightDiscreteBVNorm
    by_cases hAYeq : A = Y
    · subst Y
      simp [fourFiveMovingFaceKernel]
    · have hAYlt : A < Y := lt_of_le_of_ne hAY hAYeq
      have hYzero := hzero Y (Finset.mem_Ioc.mpr ⟨hAYlt, le_rfl⟩)
      rw [hYzero, abs_zero, zero_add]
      have hsum :
          (∑ n ∈ Finset.Ioc A (Y - 1),
            |fourFiveMovingFaceKernel A y u c (n + 1) -
              fourFiveMovingFaceKernel A y u c n|) = 0 := by
        apply Finset.sum_eq_zero
        intro n hn
        have hnData := Finset.mem_Ioc.mp hn
        have hnMem : n ∈ Finset.Ioc A Y :=
          Finset.mem_Ioc.mpr ⟨hnData.1, by omega⟩
        have hn1Mem : n + 1 ∈ Finset.Ioc A Y :=
          Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        rw [hzero n hnMem, hzero (n + 1) hn1Mem]
        simp
      rw [hsum]
      norm_num
  · have hcert := fourFiveMovingFaceMonotoneExtension_certificate
      (u := u) (c := c) hy hyA hAY (le_of_not_gt hRA)
    have hcut := fourFiveRightDiscreteBVNorm_cutoffSequence_le_two
      (R := R) g hAY hcert.1 hcert.2.1 hcert.2.2
    have hnorm :
        fourFiveRightDiscreteBVNorm
            (fourFiveMovingFaceKernel A y u c) A Y =
          fourFiveRightDiscreteBVNorm
            (fourFiveCutoffSequence A R g) A Y := by
      apply fourFiveRightDiscreteBVNorm_congr
      · by_cases hAYeq : A = Y
        · subst Y
          simp [fourFiveMovingFaceKernel, fourFiveCutoffSequence]
        · exact fourFiveMovingFaceKernel_eq_cutoffSequence hy hyA
            (Finset.mem_Ioc.mpr ⟨lt_of_le_of_ne hAY hAYeq, le_rfl⟩)
      · intro n hn
        have hnData := Finset.mem_Ioc.mp hn
        have hnMem : n ∈ Finset.Ioc A Y :=
          Finset.mem_Ioc.mpr ⟨hnData.1, by omega⟩
        have hn1Mem : n + 1 ∈ Finset.Ioc A Y :=
          Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        rw [fourFiveMovingFaceKernel_eq_cutoffSequence hy hyA hnMem,
          fourFiveMovingFaceKernel_eq_cutoffSequence hy hyA hn1Mem]
    rw [hnorm]
    exact hcut

/-! ## Compact reciprocal-mass bounds -/

/-- The paper's common mass cap on logarithmic coordinates up to `4.8`. -/
def fourFiveCompactReciprocalMass : Real :=
  1 + Real.log ((24 : Real) / 5)

theorem fourFiveCompactReciprocalMass_pos :
    0 < fourFiveCompactReciprocalMass := by
  unfold fourFiveCompactReciprocalMass
  have hlog : 0 <= Real.log ((24 : Real) / 5) :=
    Real.log_nonneg (by norm_num)
  linarith

theorem fourFiveAnchoredReciprocalPrimeAtom_nonneg
    (A n : Nat) :
    0 <= fourFiveAnchoredReciprocalPrimeAtom A n := by
  unfold fourFiveAnchoredReciprocalPrimeAtom fourFiveReciprocalPrimeAtom
  split_ifs <;> positivity

theorem fourFiveAnchoredLogLogCellAtom_nonneg
    {A n : Nat} (hA : 2 <= A) :
    0 <= fourFiveAnchoredLogLogCellAtom A n := by
  unfold fourFiveAnchoredLogLogCellAtom
  by_cases hAn : A < n
  · rw [if_pos hAn]
    have hnSub : 1 < n - 1 := by omega
    have hsubPos : (0 : Real) < (n - 1 : Nat) := by
      exact_mod_cast (show 0 < n - 1 by omega)
    have hcastLe : ((n - 1 : Nat) : Real) <= (n : Real) := by
      exact_mod_cast Nat.sub_le n 1
    have hinnerPos : 0 < Real.log ((n - 1 : Nat) : Real) :=
      Real.log_pos (by exact_mod_cast hnSub)
    have hinnerLe :
        Real.log ((n - 1 : Nat) : Real) <= Real.log (n : Real) :=
      Real.log_le_log hsubPos hcastLe
    unfold fourFiveLogLogPrimitive
    exact sub_nonneg.mpr (Real.log_le_log hinnerPos hinnerLe)
  · rw [if_neg hAn]

/-- Exact total actual reciprocal-prime mass on `(A,Y]`. -/
theorem sum_Ioc_fourFiveAnchoredReciprocalPrimeAtom
    {A Y : Nat} (hAY : A <= Y) :
    (∑ n ∈ Finset.Ioc A Y,
      fourFiveAnchoredReciprocalPrimeAtom A n) =
      fullReciprocalSum Y - fullReciprocalSum A := by
  have hsubset : Finset.Ioc A Y ⊆ Finset.range (Y + 1) := by
    intro n hn
    have hnData := Finset.mem_Ioc.mp hn
    exact Finset.mem_range.mpr (by omega)
  have heq :
      (∑ n ∈ Finset.Ioc A Y,
          fourFiveAnchoredReciprocalPrimeAtom A n) =
        ∑ n ∈ Finset.range (Y + 1),
          fourFiveAnchoredReciprocalPrimeAtom A n := by
    apply Finset.sum_subset hsubset
    intro n hnRange hnNot
    have hnY : n <= Y := by
      have := Finset.mem_range.mp hnRange
      omega
    have hnA : n <= A := by
      by_contra hnot
      exact hnNot (Finset.mem_Ioc.mpr ⟨by omega, hnY⟩)
    simp [fourFiveAnchoredReciprocalPrimeAtom, show ¬A < n by omega]
  rw [heq, sum_range_fourFiveAnchoredReciprocalPrimeAtom hAY]

/-- Exact total continuum log-log cell mass on `(A,Y]`. -/
theorem sum_Ioc_fourFiveAnchoredLogLogCellAtom
    {A Y : Nat} (hAY : A <= Y) :
    (∑ n ∈ Finset.Ioc A Y,
      fourFiveAnchoredLogLogCellAtom A n) =
      fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A := by
  have hsubset : Finset.Ioc A Y ⊆ Finset.range (Y + 1) := by
    intro n hn
    have hnData := Finset.mem_Ioc.mp hn
    exact Finset.mem_range.mpr (by omega)
  have heq :
      (∑ n ∈ Finset.Ioc A Y,
          fourFiveAnchoredLogLogCellAtom A n) =
        ∑ n ∈ Finset.range (Y + 1),
          fourFiveAnchoredLogLogCellAtom A n := by
    apply Finset.sum_subset hsubset
    intro n hnRange hnNot
    have hnY : n <= Y := by
      have := Finset.mem_range.mp hnRange
      omega
    have hnA : n <= A := by
      by_contra hnot
      exact hnNot (Finset.mem_Ioc.mpr ⟨by omega, hnY⟩)
    simp [fourFiveAnchoredLogLogCellAtom, show ¬A < n by omega]
  rw [heq, sum_range_fourFiveAnchoredLogLogCellAtom hAY]

/-- The absolute actual mass is its two-endpoint reciprocal-prime sum. -/
theorem sum_abs_fourFiveAnchoredReciprocalPrimeAtom
    {A Y : Nat} (hAY : A <= Y) :
    (∑ n ∈ Finset.Ioc A Y,
      |fourFiveAnchoredReciprocalPrimeAtom A n|) =
      fullReciprocalSum Y - fullReciprocalSum A := by
  calc
    (∑ n ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A n|) =
        ∑ n ∈ Finset.Ioc A Y,
          fourFiveAnchoredReciprocalPrimeAtom A n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [abs_of_nonneg (fourFiveAnchoredReciprocalPrimeAtom_nonneg A n)]
    _ = fullReciprocalSum Y - fullReciprocalSum A :=
      sum_Ioc_fourFiveAnchoredReciprocalPrimeAtom hAY

/-- The absolute continuum-cell mass telescopes to the log-log increment. -/
theorem sum_abs_fourFiveAnchoredLogLogCellAtom
    {A Y : Nat} (hA : 2 <= A) (hAY : A <= Y) :
    (∑ n ∈ Finset.Ioc A Y,
      |fourFiveAnchoredLogLogCellAtom A n|) =
      fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A := by
  calc
    (∑ n ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A n|) =
        ∑ n ∈ Finset.Ioc A Y,
          fourFiveAnchoredLogLogCellAtom A n := by
      apply Finset.sum_congr rfl
      intro n _hn
      rw [abs_of_nonneg (fourFiveAnchoredLogLogCellAtom_nonneg hA)]
    _ = fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A :=
      sum_Ioc_fourFiveAnchoredLogLogCellAtom hAY

/-- Once the log-log span is at most `log 4.8` and the uniform discrepancy
is at most one, both untouched measures have the paper mass cap
`M0 = 1 + log 4.8`. -/
theorem fourFive_actual_and_continuum_mass_le_compact
    {A Y : Nat} (hA : fourFiveReciprocalBVSafeCutoff <= A)
    (hAY : A <= Y)
    (hspan : fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A <=
      Real.log ((24 : Real) / 5))
    (herror : fourFiveReciprocalBVError A <= 1) :
    (∑ n ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A n|) <=
        fourFiveCompactReciprocalMass ∧
      (∑ n ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A n|) <=
        fourFiveCompactReciprocalMass := by
  have hA2 : 2 <= A :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hA
  have hdisc := abs_fourFiveReciprocalPrimeDiscrepancy_le_uniform hA hAY
  have hactual :
      fullReciprocalSum Y - fullReciprocalSum A <=
        (fourFiveLogLogPrimitive Y - fourFiveLogLogPrimitive A) + 1 := by
    unfold fourFiveReciprocalPrimeDiscrepancy at hdisc
    unfold fourFiveReciprocalBVError at herror
    have hup := le_of_abs_le hdisc
    linarith
  constructor
  · rw [sum_abs_fourFiveAnchoredReciprocalPrimeAtom hAY]
    unfold fourFiveCompactReciprocalMass
    linarith
  · rw [sum_abs_fourFiveAnchoredLogLogCellAtom hA2 hAY]
    unfold fourFiveCompactReciprocalMass
    linarith

/-! ## One, two, and three moving-simplex coordinates -/

def fourFiveMovingSimplexKernelOne
    (A y : Nat) (u : Real) (p : Nat) : Real :=
  fourFiveMovingFaceKernel A y u 0 p

def fourFiveMovingSimplexKernelTwo
    (A y : Nat) (u : Real) (p q : Nat) : Real :=
  if A < p ∧ A < q ∧
      fourFiveLogCoordinate y p + fourFiveLogCoordinate y q < u - 1 then
    (u - fourFiveLogCoordinate y p - fourFiveLogCoordinate y q)⁻¹
  else 0

def fourFiveMovingSimplexKernelThree
    (A y : Nat) (u : Real) (p q r : Nat) : Real :=
  if A < p ∧ A < q ∧ A < r ∧
      fourFiveLogCoordinate y p + fourFiveLogCoordinate y q +
        fourFiveLogCoordinate y r < u - 1 then
    (u - fourFiveLogCoordinate y p - fourFiveLogCoordinate y q -
      fourFiveLogCoordinate y r)⁻¹
  else 0

theorem fourFiveMovingSimplexKernelTwo_eq_face_first
    {A Y y p q : Nat} {u : Real} (hq : q ∈ Finset.Ioc A Y) :
    fourFiveMovingSimplexKernelTwo A y u p q =
      fourFiveMovingFaceKernel A y u (fourFiveLogCoordinate y q) p := by
  have hqA := (Finset.mem_Ioc.mp hq).1
  unfold fourFiveMovingSimplexKernelTwo fourFiveMovingFaceKernel
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveMovingSimplexKernelTwo_eq_face_second
    {A Y y p q : Nat} {u : Real} (hp : p ∈ Finset.Ioc A Y) :
    fourFiveMovingSimplexKernelTwo A y u p q =
      fourFiveMovingFaceKernel A y u (fourFiveLogCoordinate y p) q := by
  have hpA := (Finset.mem_Ioc.mp hp).1
  unfold fourFiveMovingSimplexKernelTwo fourFiveMovingFaceKernel
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRightDiscreteBVNorm_movingSimplexTwo_first_le_two
    {A Y y q : Nat} {u : Real} (hy : 2 <= y) (hyA : y <= A)
    (hAY : A <= Y) (hq : q ∈ Finset.Ioc A Y) :
    fourFiveRightDiscreteBVNorm
        (fun p => fourFiveMovingSimplexKernelTwo A y u p q) A Y <= 2 := by
  have heq :
      (fun p => fourFiveMovingSimplexKernelTwo A y u p q) =
        fourFiveMovingFaceKernel A y u (fourFiveLogCoordinate y q) := by
    funext p
    exact fourFiveMovingSimplexKernelTwo_eq_face_first hq
  rw [heq]
  exact fourFiveRightDiscreteBVNorm_movingFace_le_two hy hyA hAY

theorem fourFiveRightDiscreteBVNorm_movingSimplexTwo_second_le_two
    {A Y y p : Nat} {u : Real} (hy : 2 <= y) (hyA : y <= A)
    (hAY : A <= Y) (hp : p ∈ Finset.Ioc A Y) :
    fourFiveRightDiscreteBVNorm
        (fourFiveMovingSimplexKernelTwo A y u p) A Y <= 2 := by
  have heq : fourFiveMovingSimplexKernelTwo A y u p =
      fourFiveMovingFaceKernel A y u (fourFiveLogCoordinate y p) := by
    funext q
    exact fourFiveMovingSimplexKernelTwo_eq_face_second hp
  rw [heq]
  exact fourFiveRightDiscreteBVNorm_movingFace_le_two hy hyA hAY

theorem fourFiveMovingSimplexKernelThree_eq_face_first
    {A Y y p q r : Nat} {u : Real}
    (hq : q ∈ Finset.Ioc A Y) (hr : r ∈ Finset.Ioc A Y) :
    fourFiveMovingSimplexKernelThree A y u p q r =
      fourFiveMovingFaceKernel A y u
        (fourFiveLogCoordinate y q + fourFiveLogCoordinate y r) p := by
  have hqA := (Finset.mem_Ioc.mp hq).1
  have hrA := (Finset.mem_Ioc.mp hr).1
  unfold fourFiveMovingSimplexKernelThree fourFiveMovingFaceKernel
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveMovingSimplexKernelThree_eq_face_second
    {A Y y p q r : Nat} {u : Real}
    (hp : p ∈ Finset.Ioc A Y) (hr : r ∈ Finset.Ioc A Y) :
    fourFiveMovingSimplexKernelThree A y u p q r =
      fourFiveMovingFaceKernel A y u
        (fourFiveLogCoordinate y p + fourFiveLogCoordinate y r) q := by
  have hpA := (Finset.mem_Ioc.mp hp).1
  have hrA := (Finset.mem_Ioc.mp hr).1
  unfold fourFiveMovingSimplexKernelThree fourFiveMovingFaceKernel
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveMovingSimplexKernelThree_eq_face_third
    {A Y y p q r : Nat} {u : Real}
    (hp : p ∈ Finset.Ioc A Y) (hq : q ∈ Finset.Ioc A Y) :
    fourFiveMovingSimplexKernelThree A y u p q r =
      fourFiveMovingFaceKernel A y u
        (fourFiveLogCoordinate y p + fourFiveLogCoordinate y q) r := by
  have hpA := (Finset.mem_Ioc.mp hp).1
  have hqA := (Finset.mem_Ioc.mp hq).1
  unfold fourFiveMovingSimplexKernelThree fourFiveMovingFaceKernel
  split_ifs <;> simp_all <;> ring_nf at * <;> linarith

theorem fourFiveRightDiscreteBVNorm_movingSimplexThree_first_le_two
    {A Y y q r : Nat} {u : Real} (hy : 2 <= y) (hyA : y <= A)
    (hAY : A <= Y) (hq : q ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    fourFiveRightDiscreteBVNorm
        (fun p => fourFiveMovingSimplexKernelThree A y u p q r) A Y <= 2 := by
  have heq :
      (fun p => fourFiveMovingSimplexKernelThree A y u p q r) =
        fourFiveMovingFaceKernel A y u
          (fourFiveLogCoordinate y q + fourFiveLogCoordinate y r) := by
    funext p
    exact fourFiveMovingSimplexKernelThree_eq_face_first hq hr
  rw [heq]
  exact fourFiveRightDiscreteBVNorm_movingFace_le_two hy hyA hAY

theorem fourFiveRightDiscreteBVNorm_movingSimplexThree_second_le_two
    {A Y y p r : Nat} {u : Real} (hy : 2 <= y) (hyA : y <= A)
    (hAY : A <= Y) (hp : p ∈ Finset.Ioc A Y)
    (hr : r ∈ Finset.Ioc A Y) :
    fourFiveRightDiscreteBVNorm
        (fun q => fourFiveMovingSimplexKernelThree A y u p q r) A Y <= 2 := by
  have heq :
      (fun q => fourFiveMovingSimplexKernelThree A y u p q r) =
        fourFiveMovingFaceKernel A y u
          (fourFiveLogCoordinate y p + fourFiveLogCoordinate y r) := by
    funext q
    exact fourFiveMovingSimplexKernelThree_eq_face_second hp hr
  rw [heq]
  exact fourFiveRightDiscreteBVNorm_movingFace_le_two hy hyA hAY

theorem fourFiveRightDiscreteBVNorm_movingSimplexThree_third_le_two
    {A Y y p q : Nat} {u : Real} (hy : 2 <= y) (hyA : y <= A)
    (hAY : A <= Y) (hp : p ∈ Finset.Ioc A Y)
    (hq : q ∈ Finset.Ioc A Y) :
    fourFiveRightDiscreteBVNorm
        (fourFiveMovingSimplexKernelThree A y u p q) A Y <= 2 := by
  have heq : fourFiveMovingSimplexKernelThree A y u p q =
      fourFiveMovingFaceKernel A y u
        (fourFiveLogCoordinate y p + fourFiveLogCoordinate y q) := by
    funext r
    exact fourFiveMovingSimplexKernelThree_eq_face_third hp hq
  rw [heq]
  exact fourFiveRightDiscreteBVNorm_movingFace_le_two hy hyA hAY

/-! ## Literal product-telescope instantiations -/

theorem abs_fourFiveMovingSimplexProductOne_sub_continuum_le
    {A Y y : Nat} {u : Real} (hy : 2 <= y) (hyA : y <= A)
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y) :
    |fourFiveActualReciprocalProductOne
        (fourFiveMovingSimplexKernelOne A y u) A Y -
      fourFiveContinuumLogLogProductOne
        (fourFiveMovingSimplexKernelOne A y u) A Y| <=
      2 * fourFiveReciprocalBVError A := by
  have hV : fourFiveRightDiscreteBVNorm
      (fourFiveMovingSimplexKernelOne A y u) A Y <= 2 := by
    exact fourFiveRightDiscreteBVNorm_movingFace_le_two hy hyA hAY
  have h := abs_fourFiveActualReciprocalProductOne_sub_continuum_le
    (fourFiveMovingSimplexKernelOne A y u) hA hAY hV
  simpa [mul_comm] using h

theorem abs_fourFiveMovingSimplexProductTwo_sub_continuum_le
    {A Y y : Nat} {u M : Real} (hy : 2 <= y) (hyA : y <= A)
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A i|) <= M) :
    |fourFiveActualReciprocalProductTwo
        (fourFiveMovingSimplexKernelTwo A y u) A Y -
      fourFiveContinuumLogLogProductTwo
        (fourFiveMovingSimplexKernelTwo A y u) A Y| <=
      4 * fourFiveReciprocalBVError A * M := by
  have h := abs_fourFiveActualReciprocalProductTwo_sub_continuum_le
    (fourFiveMovingSimplexKernelTwo A y u) hA hAY
    hactualMass hcontinuumMass
    (fun q hq =>
      fourFiveRightDiscreteBVNorm_movingSimplexTwo_first_le_two
        hy hyA hAY hq)
    (fun p hp =>
      fourFiveRightDiscreteBVNorm_movingSimplexTwo_second_le_two
        hy hyA hAY hp)
    (by norm_num : (0 : Real) <= 2)
  convert h using 1; ring

theorem abs_fourFiveMovingSimplexProductThree_sub_continuum_le
    {A Y y : Nat} {u M : Real} (hy : 2 <= y) (hyA : y <= A)
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A i|) <= M) :
    |fourFiveActualReciprocalProductThree
        (fourFiveMovingSimplexKernelThree A y u) A Y -
      fourFiveContinuumLogLogProductThree
        (fourFiveMovingSimplexKernelThree A y u) A Y| <=
      6 * fourFiveReciprocalBVError A * M ^ 2 := by
  have h := abs_fourFiveActualReciprocalProductThree_sub_continuum_le
    (fourFiveMovingSimplexKernelThree A y u) hA hAY
    hactualMass hcontinuumMass
    (fun q hq r hr =>
      fourFiveRightDiscreteBVNorm_movingSimplexThree_first_le_two
        hy hyA hAY hq hr)
    (fun p hp r hr =>
      fourFiveRightDiscreteBVNorm_movingSimplexThree_second_le_two
        hy hyA hAY hp hr)
    (fun p hp q hq =>
      fourFiveRightDiscreteBVNorm_movingSimplexThree_third_le_two
        hy hyA hAY hp hq)
    (by norm_num : (0 : Real) <= 2)
  convert h using 1; ring

end Erdos390.WholePaper.BankPaperRealization
