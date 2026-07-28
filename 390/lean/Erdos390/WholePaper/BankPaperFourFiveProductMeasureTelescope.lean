import Erdos390.WholePaper.BankPaperFourFiveReciprocalPrimeBV

/-!
# The finite product-measure telescope in the four/five chamber

The ordered-prime argument replaces at most three reciprocal-prime
coordinates by their continuum log-log cell masses.  This file carries out
that replacement literally on the finite cell set `(A,Y]`.

There are two separate ingredients.

* `fourFiveFiniteProductOne/Two/Three` record the one-, two-, and
  three-coordinate product pairings.  Their subtraction identities are
  purely algebraic telescopes.
* The specializations to reciprocal-prime and log-log cell weights identify
  every telescope summand with the one-dimensional BV defect proved in
  `BankPaperFourFiveReciprocalPrimeBV`.  Absolute outer mass and discrete BV
  norms then give the losses `M^0`, `M^1`, and `M^2` for one, two, and three
  coordinates respectively.

No independence, positivity, smoothness, or analytic hypothesis is hidden in
the telescope identities.  The quantitative theorems ask only for the
displayed finite mass and conditional discrete-BV bounds.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.WholePaper.BankPaperRealization

open Erdos390.Full.PrimeBandQuadrature

/-! ## Generic finite product pairings and exact telescopes -/

/-- A one-coordinate finite product-measure pairing. -/
def fourFiveFiniteProductOne {ι : Type*}
    (S : Finset ι) (w : ι -> Real) (K : ι -> Real) : Real :=
  ∑ i ∈ S, w i * K i

/-- A two-coordinate finite product-measure pairing. -/
def fourFiveFiniteProductTwo {ι : Type*}
    (S : Finset ι) (w : ι -> Real) (K : ι -> ι -> Real) : Real :=
  ∑ i ∈ S, w i * (∑ j ∈ S, w j * K i j)

/-- A three-coordinate finite product-measure pairing. -/
def fourFiveFiniteProductThree {ι : Type*}
    (S : Finset ι) (w : ι -> Real)
    (K : ι -> ι -> ι -> Real) : Real :=
  ∑ i ∈ S, w i *
    (∑ j ∈ S, w j * (∑ k ∈ S, w k * K i j k))

/-- The one-coordinate product difference is one signed replacement. -/
theorem fourFiveFiniteProductOne_sub
    {ι : Type*} (S : Finset ι) (a b : ι -> Real)
    (K : ι -> Real) :
    fourFiveFiniteProductOne S a K -
        fourFiveFiniteProductOne S b K =
      ∑ i ∈ S, (a i - b i) * K i := by
  unfold fourFiveFiniteProductOne
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- The literal two-term telescope replacing the first coordinate and then
the second coordinate. -/
theorem fourFiveFiniteProductTwo_sub
    {ι : Type*} (S : Finset ι) (a b : ι -> Real)
    (K : ι -> ι -> Real) :
    fourFiveFiniteProductTwo S a K -
        fourFiveFiniteProductTwo S b K =
      (∑ i ∈ S, (a i - b i) *
        (∑ j ∈ S, a j * K i j)) +
      ∑ i ∈ S, b i *
        (∑ j ∈ S, (a j - b j) * K i j) := by
  unfold fourFiveFiniteProductTwo
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i ∈ S,
        (a i * (∑ j ∈ S, a j * K i j) -
          b i * (∑ j ∈ S, b j * K i j))) =
        ∑ i ∈ S,
          ((a i - b i) * (∑ j ∈ S, a j * K i j) +
            b i * ((∑ j ∈ S, a j * K i j) -
              ∑ j ∈ S, b j * K i j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i ∈ S,
          ((a i - b i) * (∑ j ∈ S, a j * K i j) +
            b i * (∑ j ∈ S, (a j - b j) * K i j)) := by
      apply Finset.sum_congr rfl
      intro i _hi
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply congrArg (fun z : Real => b i * z)
      apply Finset.sum_congr rfl
      intro j _hj
      ring
    _ = (∑ i ∈ S, (a i - b i) *
          (∑ j ∈ S, a j * K i j)) +
        ∑ i ∈ S, b i *
          (∑ j ∈ S, (a j - b j) * K i j) :=
      Finset.sum_add_distrib

/-- The literal three-term telescope replacing the three coordinates from
left to right. -/
theorem fourFiveFiniteProductThree_sub
    {ι : Type*} (S : Finset ι) (a b : ι -> Real)
    (K : ι -> ι -> ι -> Real) :
    fourFiveFiniteProductThree S a K -
        fourFiveFiniteProductThree S b K =
      (∑ i ∈ S, (a i - b i) *
        (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k))) +
      (∑ i ∈ S, b i *
        (∑ j ∈ S, (a j - b j) *
          (∑ k ∈ S, a k * K i j k))) +
      ∑ i ∈ S, b i *
        (∑ j ∈ S, b j *
          (∑ k ∈ S, (a k - b k) * K i j k)) := by
  unfold fourFiveFiniteProductThree
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ i ∈ S,
        (a i * (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) -
          b i * (∑ j ∈ S, b j * (∑ k ∈ S, b k * K i j k)))) =
        ∑ i ∈ S,
          ((a i - b i) *
              (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) +
            b i *
              ((∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) -
                ∑ j ∈ S, b j * (∑ k ∈ S, b k * K i j k))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    _ = ∑ i ∈ S,
          ((a i - b i) *
              (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) +
            b i *
              ((∑ j ∈ S, (a j - b j) *
                  (∑ k ∈ S, a k * K i j k)) +
                ∑ j ∈ S, b j *
                  (∑ k ∈ S, (a k - b k) * K i j k))) := by
      apply Finset.sum_congr rfl
      intro i _hi
      have htwo :
          (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k)) -
              ∑ j ∈ S, b j * (∑ k ∈ S, b k * K i j k) =
            (∑ j ∈ S, (a j - b j) *
              (∑ k ∈ S, a k * K i j k)) +
              ∑ j ∈ S, b j *
                (∑ k ∈ S, (a k - b k) * K i j k) := by
        simpa only [fourFiveFiniteProductTwo] using
          fourFiveFiniteProductTwo_sub S a b (K i)
      rw [htwo]
    _ = (∑ i ∈ S, (a i - b i) *
          (∑ j ∈ S, a j * (∑ k ∈ S, a k * K i j k))) +
        (∑ i ∈ S, b i *
          (∑ j ∈ S, (a j - b j) *
            (∑ k ∈ S, a k * K i j k))) +
        ∑ i ∈ S, b i *
          (∑ j ∈ S, b j *
            (∑ k ∈ S, (a k - b k) * K i j k)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      ring

/-! ## Two elementary norm ledgers -/

/-- A finite outer measure of absolute mass at most `M` carries a uniformly
bounded family at cost `M`. -/
theorem abs_fourFiveFiniteWeightedSum_le_mass_mul
    {ι : Type*} (S : Finset ι) (w g : ι -> Real)
    {M R : Real} (hmass : (∑ i ∈ S, |w i|) <= M)
    (hR : ∀ i ∈ S, |g i| <= R) (hR0 : 0 <= R) :
    |∑ i ∈ S, w i * g i| <= M * R := by
  calc
    |∑ i ∈ S, w i * g i| <=
        ∑ i ∈ S, |w i * g i| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i ∈ S, |w i| * |g i| := by
      apply Finset.sum_congr rfl
      intro i _hi
      rw [abs_mul]
    _ <= ∑ i ∈ S, |w i| * R := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hR i hi) (abs_nonneg _)
    _ = (∑ i ∈ S, |w i|) * R := by
      rw [Finset.sum_mul]
    _ <= M * R := mul_le_mul_of_nonneg_right hmass hR0

/-- Discrete right-BV is subadditive under a finite weighted family.  This
is the finite analogue of integrating conditional BV norms against total
variation. -/
theorem fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le
    {ι : Type*} (S : Finset ι) (w : ι -> Real)
    (f : ι -> Nat -> Real) {A Y : Nat} {V : Real}
    (hV : ∀ i ∈ S,
      fourFiveRightDiscreteBVNorm (f i) A Y <= V)
    (_hV0 : 0 <= V) :
    fourFiveRightDiscreteBVNorm
        (fun n => ∑ i ∈ S, w i * f i n) A Y <=
      (∑ i ∈ S, |w i|) * V := by
  let D : Finset Nat := Finset.Ioc A (Y - 1)
  have hendpoint :
      |∑ i ∈ S, w i * f i Y| <=
        ∑ i ∈ S, |w i| * |f i Y| := by
    calc
      |∑ i ∈ S, w i * f i Y| <=
          ∑ i ∈ S, |w i * f i Y| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |w i| * |f i Y| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul]
  have hvariation :
      (∑ m ∈ D,
          |(∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m|) <=
        ∑ m ∈ D,
          ∑ i ∈ S, |w i| * |f i (m + 1) - f i m| := by
    apply Finset.sum_le_sum
    intro m _hm
    have hdiff :
        (∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m =
          ∑ i ∈ S, w i * (f i (m + 1) - f i m) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _hi
      ring
    rw [hdiff]
    calc
      |∑ i ∈ S, w i * (f i (m + 1) - f i m)| <=
          ∑ i ∈ S, |w i * (f i (m + 1) - f i m)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = ∑ i ∈ S, |w i| * |f i (m + 1) - f i m| := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [abs_mul]
  unfold fourFiveRightDiscreteBVNorm
  change
    |∑ i ∈ S, w i * f i Y| +
        ∑ m ∈ D,
          |(∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m| <=
      (∑ i ∈ S, |w i|) * V
  calc
    |∑ i ∈ S, w i * f i Y| +
        ∑ m ∈ D,
          |(∑ i ∈ S, w i * f i (m + 1)) -
            ∑ i ∈ S, w i * f i m| <=
        (∑ i ∈ S, |w i| * |f i Y|) +
          ∑ m ∈ D,
            ∑ i ∈ S, |w i| * |f i (m + 1) - f i m| :=
      add_le_add hendpoint hvariation
    _ = ∑ i ∈ S, |w i| *
          (|f i Y| +
            ∑ m ∈ D, |f i (m + 1) - f i m|) := by
      simp_rw [mul_add, Finset.mul_sum]
      rw [Finset.sum_add_distrib]
      congr 1
      rw [Finset.sum_comm]
    _ <= ∑ i ∈ S, |w i| * V := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact hV i hi
    _ = (∑ i ∈ S, |w i|) * V := by
      rw [Finset.sum_mul]

/-- The preceding BV ledger with an externally supplied mass bound. -/
theorem fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
    {ι : Type*} (S : Finset ι) (w : ι -> Real)
    (f : ι -> Nat -> Real) {A Y : Nat} {M V : Real}
    (hmass : (∑ i ∈ S, |w i|) <= M)
    (hV : ∀ i ∈ S,
      fourFiveRightDiscreteBVNorm (f i) A Y <= V)
    (hV0 : 0 <= V) :
    fourFiveRightDiscreteBVNorm
        (fun n => ∑ i ∈ S, w i * f i n) A Y <= M * V := by
  exact (fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le
    S w f hV hV0).trans
      (mul_le_mul_of_nonneg_right hmass hV0)

/-! ## Reciprocal-prime specialization -/

/-- The uniform one-dimensional discrepancy factor used below. -/
noncomputable def fourFiveReciprocalBVError (A : Nat) : Real :=
  5 * fullReciprocalSumUniformConstant /
    Real.log (A : Real) ^ 3

theorem fourFiveReciprocalBVError_pos
    {A : Nat} (hA : fourFiveReciprocalBVSafeCutoff <= A) :
    0 < fourFiveReciprocalBVError A := by
  have hA2 : 2 <= A :=
    fourFiveReciprocalBVSafeCutoff_ge_two.trans hA
  have hlogA : 0 < Real.log (A : Real) :=
    Real.log_pos (by exact_mod_cast (show 1 < A by omega))
  unfold fourFiveReciprocalBVError
  exact div_pos
    (mul_pos (by norm_num) fullReciprocalSumUniformConstant_pos)
    (pow_pos hlogA 3)

/-- Actual reciprocal-prime product pairing in one coordinate. -/
def fourFiveActualReciprocalProductOne
    (K : Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductOne (Finset.Ioc A Y)
    (fourFiveAnchoredReciprocalPrimeAtom A) K

/-- Continuum log-log cell product pairing in one coordinate. -/
def fourFiveContinuumLogLogProductOne
    (K : Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductOne (Finset.Ioc A Y)
    (fourFiveAnchoredLogLogCellAtom A) K

/-- Actual reciprocal-prime product pairing in two coordinates. -/
def fourFiveActualReciprocalProductTwo
    (K : Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductTwo (Finset.Ioc A Y)
    (fourFiveAnchoredReciprocalPrimeAtom A) K

/-- Continuum log-log cell product pairing in two coordinates. -/
def fourFiveContinuumLogLogProductTwo
    (K : Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductTwo (Finset.Ioc A Y)
    (fourFiveAnchoredLogLogCellAtom A) K

/-- Actual reciprocal-prime product pairing in three coordinates. -/
def fourFiveActualReciprocalProductThree
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductThree (Finset.Ioc A Y)
    (fourFiveAnchoredReciprocalPrimeAtom A) K

/-- Continuum log-log cell product pairing in three coordinates. -/
def fourFiveContinuumLogLogProductThree
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) : Real :=
  fourFiveFiniteProductThree (Finset.Ioc A Y)
    (fourFiveAnchoredLogLogCellAtom A) K

/-- Exact one-coordinate reciprocal-prime/log-log telescope. -/
theorem fourFiveActualReciprocalProductOne_sub_continuum
    (K : Nat -> Real) (A Y : Nat) :
    fourFiveActualReciprocalProductOne K A Y -
      fourFiveContinuumLogLogProductOne K A Y =
      fourFiveReciprocalPrimeBVDefect K A Y := by
  unfold fourFiveActualReciprocalProductOne
    fourFiveContinuumLogLogProductOne
  rw [fourFiveFiniteProductOne_sub]
  unfold
    fourFiveReciprocalPrimeBVDefect
    fourFiveReciprocalPrimeSignedCell
  apply Finset.sum_congr rfl
  intro i _hi
  ring

/-- Exact two-coordinate telescope, displayed as two applications of the
one-dimensional signed-cell functional. -/
theorem fourFiveActualReciprocalProductTwo_sub_continuum
    (K : Nat -> Nat -> Real) (A Y : Nat) :
    fourFiveActualReciprocalProductTwo K A Y -
        fourFiveContinuumLogLogProductTwo K A Y =
      fourFiveReciprocalPrimeBVDefect
        (fun i => ∑ j ∈ Finset.Ioc A Y,
          fourFiveAnchoredReciprocalPrimeAtom A j * K i j) A Y +
      ∑ i ∈ Finset.Ioc A Y,
        fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect (K i) A Y := by
  unfold fourFiveActualReciprocalProductTwo
    fourFiveContinuumLogLogProductTwo
  rw [fourFiveFiniteProductTwo_sub]
  unfold
    fourFiveReciprocalPrimeBVDefect
    fourFiveReciprocalPrimeSignedCell
  apply congrArg₂ (· + ·)
  · apply Finset.sum_congr rfl
    intro i _hi
    ring
  · apply Finset.sum_congr rfl
    intro i _hi
    apply congrArg (fun z : Real =>
      fourFiveAnchoredLogLogCellAtom A i * z)
    apply Finset.sum_congr rfl
    intro j _hj
    ring

/-- Exact three-coordinate telescope, displayed as three applications of
the one-dimensional signed-cell functional. -/
theorem fourFiveActualReciprocalProductThree_sub_continuum
    (K : Nat -> Nat -> Nat -> Real) (A Y : Nat) :
    fourFiveActualReciprocalProductThree K A Y -
        fourFiveContinuumLogLogProductThree K A Y =
      fourFiveReciprocalPrimeBVDefect
        (fun i => ∑ j ∈ Finset.Ioc A Y,
          fourFiveAnchoredReciprocalPrimeAtom A j *
            (∑ k ∈ Finset.Ioc A Y,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y +
      (∑ i ∈ Finset.Ioc A Y,
        fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect
            (fun j => ∑ k ∈ Finset.Ioc A Y,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y) +
      ∑ i ∈ Finset.Ioc A Y,
        fourFiveAnchoredLogLogCellAtom A i *
          (∑ j ∈ Finset.Ioc A Y,
            fourFiveAnchoredLogLogCellAtom A j *
              fourFiveReciprocalPrimeBVDefect (K i j) A Y) := by
  unfold fourFiveActualReciprocalProductThree
    fourFiveContinuumLogLogProductThree
  rw [fourFiveFiniteProductThree_sub]
  unfold
    fourFiveReciprocalPrimeBVDefect
    fourFiveReciprocalPrimeSignedCell
  apply congrArg₂ (· + ·)
  · apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i _hi
      ring
    · apply Finset.sum_congr rfl
      intro i _hi
      apply congrArg (fun z : Real =>
        fourFiveAnchoredLogLogCellAtom A i * z)
      apply Finset.sum_congr rfl
      intro j _hj
      ring
  · apply Finset.sum_congr rfl
    intro i _hi
    apply congrArg (fun z : Real =>
      fourFiveAnchoredLogLogCellAtom A i * z)
    apply Finset.sum_congr rfl
    intro j _hj
    apply congrArg (fun z : Real =>
      fourFiveAnchoredLogLogCellAtom A j * z)
    apply Finset.sum_congr rfl
    intro k _hk
    ring

/-! ## Quantitative one-, two-, and three-coordinate transfer -/

/-- One-coordinate product transfer. -/
theorem abs_fourFiveActualReciprocalProductOne_sub_continuum_le
    (K : Nat -> Real) {A Y : Nat} {V : Real}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y)
    (hV : fourFiveRightDiscreteBVNorm K A Y <= V) :
    |fourFiveActualReciprocalProductOne K A Y -
        fourFiveContinuumLogLogProductOne K A Y| <=
      fourFiveReciprocalBVError A * V := by
  rw [fourFiveActualReciprocalProductOne_sub_continuum]
  exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform K hA hAY).trans
    (mul_le_mul_of_nonneg_left hV
      (fourFiveReciprocalBVError_pos hA).le)

/-- Two-coordinate product transfer.  Every one-variable conditional kernel
has right-BV norm at most `V`, and both untouched measures have absolute mass
at most `M`. -/
theorem abs_fourFiveActualReciprocalProductTwo_sub_continuum_le
    (K : Nat -> Nat -> Real) {A Y : Nat} {M V : Real}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A i|) <= M)
    (hVfirst : ∀ j ∈ Finset.Ioc A Y,
      fourFiveRightDiscreteBVNorm (fun i => K i j) A Y <= V)
    (hVsecond : ∀ i ∈ Finset.Ioc A Y,
      fourFiveRightDiscreteBVNorm (K i) A Y <= V)
    (hV0 : 0 <= V) :
    |fourFiveActualReciprocalProductTwo K A Y -
        fourFiveContinuumLogLogProductTwo K A Y| <=
      2 * fourFiveReciprocalBVError A * M * V := by
  let S : Finset Nat := Finset.Ioc A Y
  let E : Real := fourFiveReciprocalBVError A
  have hE0 : 0 <= E := (fourFiveReciprocalBVError_pos hA).le
  have hM0 : 0 <= M := by
    exact (Finset.sum_nonneg fun i _hi => abs_nonneg
      (fourFiveAnchoredReciprocalPrimeAtom A i)).trans hactualMass
  have hfirstNorm :
      fourFiveRightDiscreteBVNorm
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j * K i j) A Y <=
        M * V := by
    apply fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
      S (fourFiveAnchoredReciprocalPrimeAtom A)
        (fun j i => K i j) hactualMass
    · exact hVfirst
    · exact hV0
  have hfirst :
      |fourFiveReciprocalPrimeBVDefect
        (fun i => ∑ j ∈ S,
          fourFiveAnchoredReciprocalPrimeAtom A j * K i j) A Y| <=
        E * (M * V) := by
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform _ hA hAY).trans
      (mul_le_mul_of_nonneg_left hfirstNorm hE0)
  have hinner : ∀ i ∈ S,
      |fourFiveReciprocalPrimeBVDefect (K i) A Y| <= E * V := by
    intro i hi
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform (K i) hA hAY).trans
      (mul_le_mul_of_nonneg_left (hVsecond i hi) hE0)
  have hsecond :
      |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect (K i) A Y| <=
        M * (E * V) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul S
      (fourFiveAnchoredLogLogCellAtom A)
      (fun i => fourFiveReciprocalPrimeBVDefect (K i) A Y)
      hcontinuumMass hinner (mul_nonneg hE0 hV0)
  rw [fourFiveActualReciprocalProductTwo_sub_continuum]
  calc
    |fourFiveReciprocalPrimeBVDefect
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j * K i j) A Y +
        ∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect (K i) A Y| <=
        |fourFiveReciprocalPrimeBVDefect
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j * K i j) A Y| +
        |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect (K i) A Y| := abs_add_le _ _
    _ <= E * (M * V) + M * (E * V) := add_le_add hfirst hsecond
    _ = 2 * fourFiveReciprocalBVError A * M * V := by
      dsimp [E]
      ring

/-- Three-coordinate product transfer.  This is the largest product
telescope needed in the four-to-five chamber. -/
theorem abs_fourFiveActualReciprocalProductThree_sub_continuum_le
    (K : Nat -> Nat -> Nat -> Real) {A Y : Nat} {M V : Real}
    (hA : fourFiveReciprocalBVSafeCutoff <= A) (hAY : A <= Y)
    (hactualMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredReciprocalPrimeAtom A i|) <= M)
    (hcontinuumMass :
      (∑ i ∈ Finset.Ioc A Y,
        |fourFiveAnchoredLogLogCellAtom A i|) <= M)
    (hVfirst : ∀ j ∈ Finset.Ioc A Y,
      ∀ k ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (fun i => K i j k) A Y <= V)
    (hVsecond : ∀ i ∈ Finset.Ioc A Y,
      ∀ k ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (fun j => K i j k) A Y <= V)
    (hVthird : ∀ i ∈ Finset.Ioc A Y,
      ∀ j ∈ Finset.Ioc A Y,
        fourFiveRightDiscreteBVNorm (K i j) A Y <= V)
    (hV0 : 0 <= V) :
    |fourFiveActualReciprocalProductThree K A Y -
        fourFiveContinuumLogLogProductThree K A Y| <=
      3 * fourFiveReciprocalBVError A * M ^ 2 * V := by
  let S : Finset Nat := Finset.Ioc A Y
  let E : Real := fourFiveReciprocalBVError A
  have hE0 : 0 <= E := (fourFiveReciprocalBVError_pos hA).le
  have hM0 : 0 <= M := by
    exact (Finset.sum_nonneg fun i _hi => abs_nonneg
      (fourFiveAnchoredReciprocalPrimeAtom A i)).trans hactualMass
  have hfirstInner (j : Nat) (hj : j ∈ S) :
      fourFiveRightDiscreteBVNorm
          (fun i => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y <=
        M * V := by
    apply fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
      S (fourFiveAnchoredReciprocalPrimeAtom A)
        (fun k i => K i j k) hactualMass
    · intro k hk
      exact hVfirst j hj k hk
    · exact hV0
  have hfirstNorm :
      fourFiveRightDiscreteBVNorm
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y <=
        M ^ 2 * V := by
    have hraw :=
      fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
        S (fourFiveAnchoredReciprocalPrimeAtom A)
          (fun j i => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)
          hactualMass hfirstInner (mul_nonneg hM0 hV0)
    calc
      fourFiveRightDiscreteBVNorm
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y <=
          M * (M * V) := hraw
      _ = M ^ 2 * V := by ring
  have hfirst :
      |fourFiveReciprocalPrimeBVDefect
        (fun i => ∑ j ∈ S,
          fourFiveAnchoredReciprocalPrimeAtom A j *
            (∑ k ∈ S,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y| <=
        E * (M ^ 2 * V) := by
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform _ hA hAY).trans
      (mul_le_mul_of_nonneg_left hfirstNorm hE0)
  have hsecondNorm (i : Nat) (hi : i ∈ S) :
      fourFiveRightDiscreteBVNorm
          (fun j => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y <=
        M * V := by
    apply fourFiveRightDiscreteBVNorm_finiteWeightedFamily_le_mass_mul
      S (fourFiveAnchoredReciprocalPrimeAtom A)
        (fun k j => K i j k) hactualMass
    · intro k hk
      exact hVsecond i hi k hk
    · exact hV0
  have hsecondInner (i : Nat) (hi : i ∈ S) :
      |fourFiveReciprocalPrimeBVDefect
        (fun j => ∑ k ∈ S,
          fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y| <=
        E * (M * V) := by
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform _ hA hAY).trans
      (mul_le_mul_of_nonneg_left (hsecondNorm i hi) hE0)
  have hsecond :
      |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
        fourFiveReciprocalPrimeBVDefect
          (fun j => ∑ k ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y| <=
        M * (E * (M * V)) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul S
      (fourFiveAnchoredLogLogCellAtom A)
      (fun i => fourFiveReciprocalPrimeBVDefect
        (fun j => ∑ k ∈ S,
          fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y)
      hcontinuumMass hsecondInner
      (mul_nonneg hE0 (mul_nonneg hM0 hV0))
  have hthirdInner (i : Nat) (hi : i ∈ S)
      (j : Nat) (hj : j ∈ S) :
      |fourFiveReciprocalPrimeBVDefect (K i j) A Y| <= E * V := by
    exact (abs_fourFiveReciprocalPrimeBVDefect_le_uniform (K i j) hA hAY).trans
      (mul_le_mul_of_nonneg_left (hVthird i hi j hj) hE0)
  have hthirdMiddle (i : Nat) (hi : i ∈ S) :
      |∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
          fourFiveReciprocalPrimeBVDefect (K i j) A Y| <=
        M * (E * V) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul S
      (fourFiveAnchoredLogLogCellAtom A)
      (fun j => fourFiveReciprocalPrimeBVDefect (K i j) A Y)
      hcontinuumMass (hthirdInner i hi) (mul_nonneg hE0 hV0)
  have hthird :
      |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
        (∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
          fourFiveReciprocalPrimeBVDefect (K i j) A Y)| <=
        M * (M * (E * V)) := by
    exact abs_fourFiveFiniteWeightedSum_le_mass_mul S
      (fourFiveAnchoredLogLogCellAtom A)
      (fun i => ∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
        fourFiveReciprocalPrimeBVDefect (K i j) A Y)
      hcontinuumMass hthirdMiddle
      (mul_nonneg hM0 (mul_nonneg hE0 hV0))
  rw [fourFiveActualReciprocalProductThree_sub_continuum]
  calc
    |fourFiveReciprocalPrimeBVDefect
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y +
        (∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect
            (fun j => ∑ k ∈ S,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y) +
        ∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          (∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
            fourFiveReciprocalPrimeBVDefect (K i j) A Y)| <=
        |fourFiveReciprocalPrimeBVDefect
          (fun i => ∑ j ∈ S,
            fourFiveAnchoredReciprocalPrimeAtom A j *
              (∑ k ∈ S,
                fourFiveAnchoredReciprocalPrimeAtom A k * K i j k)) A Y| +
        |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          fourFiveReciprocalPrimeBVDefect
            (fun j => ∑ k ∈ S,
              fourFiveAnchoredReciprocalPrimeAtom A k * K i j k) A Y| +
        |∑ i ∈ S, fourFiveAnchoredLogLogCellAtom A i *
          (∑ j ∈ S, fourFiveAnchoredLogLogCellAtom A j *
            fourFiveReciprocalPrimeBVDefect (K i j) A Y)| := by
      exact (abs_add_three _ _ _)
    _ <= E * (M ^ 2 * V) + M * (E * (M * V)) +
        M * (M * (E * V)) := by
      exact add_le_add (add_le_add hfirst hsecond) hthird
    _ = 3 * fourFiveReciprocalBVError A * M ^ 2 * V := by
      dsimp [E]
      ring

end Erdos390.WholePaper.BankPaperRealization
