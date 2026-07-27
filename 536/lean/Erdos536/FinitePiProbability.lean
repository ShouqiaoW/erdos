import Erdos536.AlternativeBandFlattening

/-!
# Explicit finite product laws on dependent function spaces
-/

open scoped BigOperators
open Finset

namespace Erdos536

/-- Product mass on a finite dependent function space. -/
def finitePiWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    (μ : (i : ι) → Ω i → ℝ) (x : (i : ι) → Ω i) : ℝ :=
  ∏ i, μ i (x i)

theorem sum_finitePiWeight
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    (μ : (i : ι) → Ω i → ℝ)
    (hmass : ∀ i, ∑ x, μ i x = 1) :
    (∑ x, finitePiWeight μ x) = 1 := by
  classical
  simp only [finitePiWeight]
  rw [← Fintype.prod_sum]
  simp [hmass]

theorem finitePiWeight_nonneg
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    {μ : (i : ι) → Ω i → ℝ}
    (hμ : ∀ i x, 0 ≤ μ i x) (x : (i : ι) → Ω i) :
    0 ≤ finitePiWeight μ x := by
  exact Finset.prod_nonneg fun i _hi => hμ i (x i)

/-- A finite product expectation factors across an arbitrary partition of
the coordinate type.  This is the exact finite independence statement
used to separate shallow buffer restrictions from the deep profile. -/
theorem finitePiExpectation_split
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    (q : ι → Prop) [DecidablePred q]
    (μ : (i : ι) → Ω i → ℝ)
    (F : ((i : {i // q i}) → Ω i) → ℝ)
    (G : ((i : {i // ¬q i}) → Ω i) → ℝ) :
    (∑ x : ((i : ι) → Ω i),
        finitePiWeight μ x *
          F (fun i ↦ x i) * G (fun i ↦ x i)) =
      (∑ u : ((i : {i // q i}) → Ω i),
          (∏ i : {i // q i}, μ i.1 (u i)) * F u) *
        ∑ v : ((i : {i // ¬q i}) → Ω i),
          (∏ i : {i // ¬q i}, μ i.1 (v i)) * G v := by
  classical
  let e :=
    Equiv.piEquivPiSubtypeProd q Ω
  calc
    (∑ x : ((i : ι) → Ω i),
        finitePiWeight μ x *
          F (fun i ↦ x i) * G (fun i ↦ x i)) =
      ∑ y :
          (((i : {i // q i}) → Ω i) ×
            ((i : {i // ¬q i}) → Ω i)),
        ((∏ i : {i // q i}, μ i.1 (y.1 i)) * F y.1) *
          ((∏ i : {i // ¬q i}, μ i.1 (y.2 i)) * G y.2) := by
      apply Fintype.sum_equiv e
      intro x
      dsimp only [e, Equiv.piEquivPiSubtypeProd_apply,
        finitePiWeight]
      rw [← Fintype.prod_subtype_mul_prod_subtype q
        (fun i ↦ μ i (x i))]
      ring
    _ =
      (∑ u : ((i : {i // q i}) → Ω i),
          (∏ i : {i // q i}, μ i.1 (u i)) * F u) *
        ∑ v : ((i : {i // ¬q i}) → Ω i),
          (∏ i : {i // ¬q i}, μ i.1 (v i)) * G v := by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]

/-- Event-mass form of `finitePiExpectation_split`. -/
theorem finitePiEventMass_split
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    (q : ι → Prop) [DecidablePred q]
    (μ : (i : ι) → Ω i → ℝ)
    (E : ((i : {i // q i}) → Ω i) → Prop)
    (D : ((i : {i // ¬q i}) → Ω i) → Prop)
    [DecidablePred E] [DecidablePred D] :
    (∑ x : ((i : ι) → Ω i),
        if E (fun i ↦ x i) ∧ D (fun i ↦ x i)
        then finitePiWeight μ x else 0) =
      (∑ u : ((i : {i // q i}) → Ω i),
          if E u
          then ∏ i : {i // q i}, μ i.1 (u i) else 0) *
        ∑ v : ((i : {i // ¬q i}) → Ω i),
          if D v
          then ∏ i : {i // ¬q i}, μ i.1 (v i) else 0 := by
  have h :=
    finitePiExpectation_split q μ
      (fun u ↦ if E u then 1 else 0)
      (fun v ↦ if D v then 1 else 0)
  have h' :
      (∑ x : ((i : ι) → Ω i),
          if D (fun i ↦ x i)
          then if E (fun i ↦ x i)
            then finitePiWeight μ x else 0
          else 0) =
        (∑ u : ((i : {i // q i}) → Ω i),
            if E u
            then ∏ i : {i // q i}, μ i.1 (u i) else 0) *
          ∑ v : ((i : {i // ¬q i}) → Ω i),
            if D v
            then ∏ i : {i // ¬q i}, μ i.1 (v i) else 0 := by
    simpa only [mul_ite, mul_one, mul_zero, ite_mul,
      one_mul, zero_mul] using h
  rw [← h']
  apply Finset.sum_congr rfl
  intro x _hx
  by_cases hE : E (fun i ↦ x i) <;>
    by_cases hD : D (fun i ↦ x i) <;>
    simp [hE, hD]

/-- Marginalize all coordinates satisfying `q`; an event depending only on
the complementary restriction has exactly its complementary product
mass. -/
theorem finitePiEventMass_complRestriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    (q : ι → Prop) [DecidablePred q]
    (μ : (i : ι) → Ω i → ℝ)
    (hmass : ∀ i, ∑ x, μ i x = 1)
    (D : ((i : {i // ¬q i}) → Ω i) → Prop)
    [DecidablePred D] :
    (∑ x : ((i : ι) → Ω i),
        if D (fun i ↦ x i) then finitePiWeight μ x else 0) =
      ∑ v : ((i : {i // ¬q i}) → Ω i),
        if D v
        then ∏ i : {i // ¬q i}, μ i.1 (v i) else 0 := by
  have h :=
    finitePiEventMass_split q μ
      (fun _u ↦ True) D
  have hq :
      (∑ u : ((i : {i // q i}) → Ω i),
          ∏ i : {i // q i}, μ i.1 (u i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hmass]
  simpa only [true_and, if_true, hq, one_mul] using h

/-- Symmetric marginalization form for an event depending only on the
coordinates satisfying `q`. -/
theorem finitePiEventMass_restriction
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    (q : ι → Prop) [DecidablePred q]
    (μ : (i : ι) → Ω i → ℝ)
    (hmass : ∀ i, ∑ x, μ i x = 1)
    (E : ((i : {i // q i}) → Ω i) → Prop)
    [DecidablePred E] :
    (∑ x : ((i : ι) → Ω i),
        if E (fun i ↦ x i) then finitePiWeight μ x else 0) =
      ∑ u : ((i : {i // q i}) → Ω i),
        if E u
        then ∏ i : {i // q i}, μ i.1 (u i) else 0 := by
  have h :=
    finitePiEventMass_split q μ E
      (fun _v ↦ True)
  have hnotq :
      (∑ v : ((i : {i // ¬q i}) → Ω i),
          ∏ i : {i // ¬q i}, μ i.1 (v i)) = 1 := by
    rw [← Fintype.prod_sum]
    simp [hmass]
  simpa only [and_true, if_true, hnotq, mul_one] using h

/-- Expectation of a product of coordinate observables factors. -/
theorem finitePiExpectation_product
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    [(i : ι) → DecidableEq (Ω i)]
    (μ X : (i : ι) → Ω i → ℝ) :
    finiteExpectation Finset.univ (finitePiWeight μ)
        (fun x => ∏ i, X i (x i)) =
      ∏ i, ∑ y, μ i y * X i y := by
  classical
  change
    (∑ x : ((i : ι) → Ω i),
      finitePiWeight μ x * ∏ i, X i (x i)) =
      ∏ i, ∑ y, μ i y * X i y
  calc
    (∑ x : ((i : ι) → Ω i),
        finitePiWeight μ x * ∏ i, X i (x i)) =
        ∑ x : ((i : ι) → Ω i),
          ∏ i, (μ i (x i) * X i (x i)) := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [finitePiWeight]
      symm
      exact Finset.prod_mul_distrib
    _ = ∏ i, ∑ y, μ i y * X i y :=
      (Fintype.prod_sum (fun i y => μ i y * X i y)).symm

/-- Lift one coordinate density to the full product space. -/
def finitePiCoordinateDensity
    {ι : Type*} {Ω : ι → Type*}
    (g : (i : ι) → Ω i → ℝ) (j : ι)
    (x : (i : ι) → Ω i) : ℝ :=
  g j (x j)

private theorem prod_coordinateObservable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} (g : (i : ι) → Ω i → ℝ)
    (j : ι) (x : (i : ι) → Ω i) :
    (∏ i, if i = j then g i (x i) else 1) =
      finitePiCoordinateDensity g j x := by
  rw [Finset.prod_eq_single j]
  · simp [finitePiCoordinateDensity]
  · intro i _hi hij
    simp [hij]
  · simp

theorem finitePiCoordinateDensity_mean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    [(i : ι) → DecidableEq (Ω i)]
    (μ g : (i : ι) → Ω i → ℝ)
    (hmass : ∀ i, ∑ x, μ i x = 1)
    (hmean : ∀ i, ∑ x, μ i x * g i x = 1)
    (j : ι) :
    finiteExpectation Finset.univ (finitePiWeight μ)
        (finitePiCoordinateDensity g j) = 1 := by
  classical
  let X : (i : ι) → Ω i → ℝ :=
    fun i x => if i = j then g i x else 1
  have hfun :
      finitePiCoordinateDensity g j =
        fun x => ∏ i, X i (x i) := by
    funext x
    exact (prod_coordinateObservable g j x).symm
  rw [hfun]
  rw [finitePiExpectation_product μ X]
  apply Finset.prod_eq_one
  intro i _hi
  by_cases hij : i = j
  · simp [X, hij, hmean]
  · simp [X, hij, hmass]

private theorem prod_twoCoordinateObservable
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} (g : (i : ι) → Ω i → ℝ)
    {i j : ι} (hij : i ≠ j) (x : (k : ι) → Ω k) :
    (∏ k, if k = i then g k (x k)
      else if k = j then g k (x k) else 1) =
      finitePiCoordinateDensity g i x *
        finitePiCoordinateDensity g j x := by
  classical
  rw [Finset.prod_eq_mul_prod_diff_singleton
    (Finset.mem_univ i)]
  rw [if_pos rfl]
  rw [Finset.prod_eq_single j]
  · rw [if_neg hij.symm, if_pos rfl]
    rfl
  · intro k hk hkj
    have hki : k ≠ i := by
      have hknot : k ∉ ({i} : Finset ι) :=
        (Finset.mem_sdiff.mp hk).2
      simpa using hknot
    simp [hki, hkj]
  · intro hjnot
    exfalso
    exact hjnot (Finset.mem_sdiff.mpr
      ⟨Finset.mem_univ _, by simpa using hij.symm⟩)

theorem finitePiCoordinateDensity_pairwiseFactorizes
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    [(i : ι) → DecidableEq (Ω i)]
    (μ g : (i : ι) → Ω i → ℝ)
    (hmass : ∀ i, ∑ x, μ i x = 1)
    (hmean : ∀ i, ∑ x, μ i x * g i x = 1) :
    PairwiseFactorizesUnder Finset.univ (finitePiWeight μ)
      (finitePiCoordinateDensity g) := by
  classical
  intro i j hij
  let X : (k : ι) → Ω k → ℝ :=
    fun k x => if k = i then g k x
      else if k = j then g k x else 1
  have hfun :
      (fun x =>
        finitePiCoordinateDensity g i x *
          finitePiCoordinateDensity g j x) =
        fun x => ∏ k, X k (x k) := by
    funext x
    exact (prod_twoCoordinateObservable g hij x).symm
  rw [hfun]
  rw [finitePiExpectation_product μ X]
  have hprod : (∏ k, ∑ y, μ k y * X k y) = 1 := by
    apply Finset.prod_eq_one
    intro k _hk
    by_cases hki : k = i
    · subst k
      simp [X, hmean]
    · by_cases hkj : k = j
      · subst k
        simp [X, hki, hmean]
      · simp [X, hki, hkj, hmass]
  rw [hprod, finitePiCoordinateDensity_mean μ g hmass hmean,
    finitePiCoordinateDensity_mean μ g hmass hmean, one_mul]

theorem finitePiCoordinateDensity_secondMoment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [(i : ι) → Fintype (Ω i)]
    [(i : ι) → DecidableEq (Ω i)]
    (μ g : (i : ι) → Ω i → ℝ)
    (hmass : ∀ i, ∑ x, μ i x = 1)
    (j : ι) :
    finiteSecondMoment Finset.univ (finitePiWeight μ)
        (finitePiCoordinateDensity g j) =
      ∑ x, μ j x * (g j x) ^ 2 := by
  classical
  change
    (∑ x, finitePiWeight μ x *
      (finitePiCoordinateDensity g j x) ^ 2) =
      ∑ x, μ j x * (g j x) ^ 2
  let X : (i : ι) → Ω i → ℝ :=
    fun i x => if i = j then (g i x) ^ 2 else 1
  rw [show
      (∑ x, finitePiWeight μ x *
        (finitePiCoordinateDensity g j x) ^ 2) =
      finiteExpectation Finset.univ (finitePiWeight μ)
        (fun x => ∏ i, X i (x i)) by
      rw [finiteExpectation]
      apply Finset.sum_congr rfl
      intro x _hx
      rw [prod_coordinateObservable (fun i y => (g i y) ^ 2) j]
      rfl]
  rw [finitePiExpectation_product μ X]
  rw [Finset.prod_eq_single j]
  · simp [X]
  · intro i _hi hij
    simp [X, hij, hmass]
  · simp

end Erdos536
