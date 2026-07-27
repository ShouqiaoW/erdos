import Erdos536.CubeMaximum
import Erdos536.FiveStateCubeLaw

/-!
# Balance for conditioned five-state cube laws

For a five-state configuration, the support represented by state `s`
contains the common part and the two petals other than `s`.  Thus its
product, multiplied by the product of the omitted petal `s`, is the product
of the entire active support.  This identity turns pairwise control of the
three petal log-sums into multiplicative balance of the represented words.
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- The event-level multiplicative balance condition on the three supports
represented by an accepted five-state configuration. -/
def FiveEventMultiplicativelyBalanced
    (R : Finset ℕ) (B : FiveConfiguration R → Bool) (δ : ℝ) : Prop :=
  ∀ c, B c → ∀ s t : Fin 3,
    (primeProduct (underlyingValues (fiveStateSupport R t c)) : ℝ) ≤
      (1 + δ) *
        (primeProduct (underlyingValues (fiveStateSupport R s c)) : ℝ)

/-- An event-level balance condition stated using the logarithmic masses of
the three petals. -/
noncomputable def fivePetalLogSum
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) : ℝ :=
  ∑ p ∈ fivePetalValues R c s, Real.log (p : ℝ)

def FiveEventPetalLogBalanced
    (R : Finset ℕ) (B : FiveConfiguration R → Bool) (η : ℝ) : Prop :=
  ∀ c, B c → ∀ s t : Fin 3,
    |fivePetalLogSum R c s - fivePetalLogSum R c t| ≤ η

/-- The active (non-unused) part of a five-state configuration. -/
def fiveActiveSubtype (R : Finset ℕ) (c : FiveConfiguration R) :
    Finset ↥R :=
  Finset.univ.filter fun p ↦ c p ≠ 0

/-- The active part after forgetting subtype proofs. -/
def fiveActiveValues (R : Finset ℕ) (c : FiveConfiguration R) :
    Finset ℕ :=
  underlyingValues (fiveActiveSubtype R c)

@[simp]
theorem mem_fiveActiveSubtype
    (R : Finset ℕ) (c : FiveConfiguration R) (p : ↥R) :
    p ∈ fiveActiveSubtype R c ↔ c p ≠ 0 := by
  simp [fiveActiveSubtype]

theorem underlyingValues_union {R : Finset ℕ} (S T : Finset ↥R) :
    underlyingValues (S ∪ T) = underlyingValues S ∪ underlyingValues T := by
  exact Finset.image_union S T

/-- A represented support together with its omitted petal is precisely the
active support. -/
theorem fiveStateSupport_union_omittedPetal
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) :
    fiveStateSupport R s c ∪ fivePetalSubtype R c s =
      fiveActiveSubtype R c := by
  ext p
  rw [mem_union, mem_fiveStateSupport, mem_fivePetalSubtype,
    mem_fiveActiveSubtype]
  fin_cases s <;>
    generalize hl : c p = l <;>
    fin_cases l <;>
    simp [fiveLabelIncluded, petalLabel]

theorem fiveStateValues_union_omittedPetal
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) :
    underlyingValues (fiveStateSupport R s c) ∪ fivePetalValues R c s =
      fiveActiveValues R c := by
  rw [fivePetalValues, fiveActiveValues, ← underlyingValues_union,
    fiveStateSupport_union_omittedPetal]

theorem fiveStateValues_disjoint_omittedPetal
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) :
    Disjoint (underlyingValues (fiveStateSupport R s c))
      (fivePetalValues R c s) := by
  rw [Finset.disjoint_left]
  intro p hpS hpP
  rw [underlyingValues, mem_image] at hpS
  rw [fivePetalValues, underlyingValues, mem_image] at hpP
  obtain ⟨q, hqS, hqp⟩ := hpS
  obtain ⟨u, huP, hup⟩ := hpP
  have hqu : q = u := Subtype.ext (hqp.trans hup.symm)
  subst u
  have hincluded :
      fiveLabelIncluded s (c q) :=
    (mem_fiveStateSupport R s c q).mp hqS
  have hpetal : c q = petalLabel s :=
    (mem_fivePetalSubtype R c s q).mp huP
  rw [hpetal] at hincluded
  fin_cases s <;>
    simp [fiveLabelIncluded, petalLabel] at hincluded

/-- The product of a represented support and its omitted petal is the
product of the whole active part. -/
theorem primeProduct_fiveStateValues_mul_omittedPetal
    (R : Finset ℕ) (c : FiveConfiguration R) (s : Fin 3) :
    (primeProduct (underlyingValues (fiveStateSupport R s c)) : ℝ) *
        (primeProduct (fivePetalValues R c s) : ℝ) =
      (primeProduct (fiveActiveValues R c) : ℝ) := by
  have hnat :
      primeProduct (underlyingValues (fiveStateSupport R s c)) *
          primeProduct (fivePetalValues R c s) =
        primeProduct (fiveActiveValues R c) := by
    unfold primeProduct
    rw [← Finset.prod_union
      (fiveStateValues_disjoint_omittedPetal R c s)]
    rw [fiveStateValues_union_omittedPetal]
  exact_mod_cast hnat

/-- Exponentiating a petal log-sum recovers its squarefree prime product. -/
theorem exp_fivePetalLogSum
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (c : FiveConfiguration R) (s : Fin 3) :
    Real.exp (fivePetalLogSum R c s) =
      (primeProduct (fivePetalValues R c s) : ℝ) := by
  have hpetalSupport : IsPrimeSupport (fivePetalValues R c s) :=
    isPrimeSupport_mono hR (underlyingValues_subset _)
  have hprodPos :
      (0 : ℝ) < (primeProduct (fivePetalValues R c s) : ℕ) := by
    exact_mod_cast primeProduct_pos hpetalSupport
  have hlog :
      Real.log (primeProduct (fivePetalValues R c s) : ℝ) =
        fivePetalLogSum R c s := by
    rw [primeProduct, Nat.cast_prod, Real.log_prod]
    · rfl
    · intro p hp
      have hpPrime := hpetalSupport p hp
      exact_mod_cast hpPrime.ne_zero
  rw [← hlog, Real.exp_log hprodPos]

/-- Pointwise logarithmic balance of the omitted petals gives
multiplicative balance of the represented supports. -/
theorem fiveStateValues_le_exp_of_petalLogBalanced
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    (c : FiveConfiguration R) {η : ℝ}
    (hlog : ∀ s t : Fin 3,
      |fivePetalLogSum R c s - fivePetalLogSum R c t| ≤ η)
    (s t : Fin 3) :
    (primeProduct (underlyingValues (fiveStateSupport R t c)) : ℝ) ≤
      Real.exp η *
        (primeProduct (underlyingValues (fiveStateSupport R s c)) : ℝ) := by
  have hlogs :
      fivePetalLogSum R c s ≤ η + fivePetalLogSum R c t := by
    have hdiff :
        fivePetalLogSum R c s - fivePetalLogSum R c t ≤ η :=
      (le_abs_self
        (fivePetalLogSum R c s - fivePetalLogSum R c t)).trans
          (hlog s t)
    linarith
  have hpetals :
      (primeProduct (fivePetalValues R c s) : ℝ) ≤
        Real.exp η * (primeProduct (fivePetalValues R c t) : ℝ) := by
    have hexp := Real.exp_le_exp.mpr hlogs
    rw [Real.exp_add, exp_fivePetalLogSum hR,
      exp_fivePetalLogSum hR] at hexp
    exact hexp
  have hpetalTSupport : IsPrimeSupport (fivePetalValues R c t) :=
    isPrimeSupport_mono hR (underlyingValues_subset _)
  have hpetalTPos :
      (0 : ℝ) < (primeProduct (fivePetalValues R c t) : ℕ) := by
    exact_mod_cast primeProduct_pos hpetalTSupport
  have hrepresentedSNonneg :
      (0 : ℝ) ≤
        (primeProduct
          (underlyingValues (fiveStateSupport R s c)) : ℕ) := by
    positivity
  have hmul :
      (primeProduct
            (underlyingValues (fiveStateSupport R t c)) : ℝ) *
          (primeProduct (fivePetalValues R c t) : ℝ) ≤
        (Real.exp η *
            (primeProduct
              (underlyingValues (fiveStateSupport R s c)) : ℝ)) *
          (primeProduct (fivePetalValues R c t) : ℝ) := by
    calc
      (primeProduct
              (underlyingValues (fiveStateSupport R t c)) : ℝ) *
            (primeProduct (fivePetalValues R c t) : ℝ) =
          (primeProduct (fiveActiveValues R c) : ℝ) :=
        primeProduct_fiveStateValues_mul_omittedPetal R c t
      _ =
          (primeProduct
              (underlyingValues (fiveStateSupport R s c)) : ℝ) *
            (primeProduct (fivePetalValues R c s) : ℝ) :=
        (primeProduct_fiveStateValues_mul_omittedPetal R c s).symm
      _ ≤
          (primeProduct
              (underlyingValues (fiveStateSupport R s c)) : ℝ) *
            (Real.exp η *
              (primeProduct (fivePetalValues R c t) : ℝ)) :=
        mul_le_mul_of_nonneg_left hpetals hrepresentedSNonneg
      _ =
          (Real.exp η *
              (primeProduct
                (underlyingValues (fiveStateSupport R s c)) : ℝ)) *
            (primeProduct (fivePetalValues R c t) : ℝ) := by
        ring
  exact le_of_mul_le_mul_right hmul hpetalTPos

/-- The petal-log event is a sufficient criterion for multiplicative
balance with factor `exp η`, equivalently with error `exp η - 1`. -/
theorem fiveEventMultiplicativelyBalanced_exp_sub_one
    {R : Finset ℕ} (hR : IsPrimeSupport R)
    {B : FiveConfiguration R → Bool} {η : ℝ}
    (hlog : FiveEventPetalLogBalanced R B η) :
    FiveEventMultiplicativelyBalanced R B (Real.exp η - 1) := by
  intro c hc s t
  have h :=
    fiveStateValues_le_exp_of_petalLogBalanced hR c
      (hlog c hc) s t
  rw [show 1 + (Real.exp η - 1) = Real.exp η by ring]
  exact h

/-- Event-level balance passes directly to the conditioned finite cube
law. -/
theorem conditionedFiveCubeLaw_multiplicativelyBalanced
    {R : Finset ℕ} {r : ℕ → ℝ}
    {B : FiveConfiguration R → Bool}
    (hpetals : FiveEventHasPetals R B)
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr : ∀ p ∈ R, r p ≤ 3 / 4)
    (hB : 0 < fiveEventMass R r B)
    {δ : ℝ} (hbalance : FiveEventMultiplicativelyBalanced R B δ) :
    FiniteCubeLaw.MultiplicativelyBalanced
      (conditionedFiveCubeLaw R r B hpetals hr0 hr hB) δ := by
  intro c _hc ω τ
  have hω :
      ω = fiveStateWord (zmodThreeToFin (ω 0)) := by
    funext i
    apply ZMod.val_injective
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [fiveStateWord, zmodThreeToFin]
  have hτ :
      τ = fiveStateWord (zmodThreeToFin (τ 0)) := by
    funext i
    apply ZMod.val_injective
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp [fiveStateWord, zmodThreeToFin]
  change
    (primeProduct
        ((fiveConfigurationCube R B hpetals c).wordSupport τ) : ℝ) ≤
      (1 + δ) *
        (primeProduct
          ((fiveConfigurationCube R B hpetals c).wordSupport ω) : ℝ)
  rw [hω, hτ, fiveConfigurationCube_wordSupport,
    fiveConfigurationCube_wordSupport]
  exact hbalance c.1 c.2
    (zmodThreeToFin (ω 0)) (zmodThreeToFin (τ 0))

/-- In particular, a conditioned five-state law satisfying the petal-log
criterion is balanced with error `exp η - 1`. -/
theorem conditionedFiveCubeLaw_multiplicativelyBalanced_exp_sub_one
    {R : Finset ℕ} (hR : IsPrimeSupport R) {r : ℕ → ℝ}
    {B : FiveConfiguration R → Bool}
    (hpetals : FiveEventHasPetals R B)
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr : ∀ p ∈ R, r p ≤ 3 / 4)
    (hB : 0 < fiveEventMass R r B)
    {η : ℝ} (hlog : FiveEventPetalLogBalanced R B η) :
    FiniteCubeLaw.MultiplicativelyBalanced
      (conditionedFiveCubeLaw R r B hpetals hr0 hr hB)
      (Real.exp η - 1) := by
  apply conditionedFiveCubeLaw_multiplicativelyBalanced
    hpetals hr0 hr hB
  exact fiveEventMultiplicativelyBalanced_exp_sub_one hR hlog

end Erdos536
