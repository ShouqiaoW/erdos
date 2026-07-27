import Erdos536.BalancedCubeCutoff

/-!
# Tensor products of finite cube laws

Two cube laws carried by disjoint prime supports can be sampled
independently.  Their common parts and corresponding petals are united,
and their coordinates are concatenated.
-/

open scoped BigOperators
open Finset

namespace Erdos536

private theorem disjoint_of_subset_of_subset
    {A B R S : Finset ℕ} (hA : A ⊆ R) (hB : B ⊆ S)
    (hRS : Disjoint R S) : Disjoint A B := by
  rw [Finset.disjoint_left]
  intro p hpA hpB
  exact Finset.disjoint_left.mp hRS (hA hpA) (hB hpB)

theorem FiniteCubeLaw.common_subset
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) {a : α} (ha : a ∈ L.samples) :
    (L.cube a).common ⊆ R := by
  intro p hp
  apply L.wordSupport_subset a ha (fun _ ↦ 0)
  simp [PairProductCube.wordSupport, hp]

theorem FiniteCubeLaw.petal_subset
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) {a : α} (ha : a ∈ L.samples)
    (i : Fin H) (s : ZMod 3) :
    (L.cube a).petal i s ⊆ R := by
  let ω : Fin H → ZMod 3 := fun _ ↦ s + 1
  have hs : s ≠ ω i := by
    intro h
    have hzero : (0 : ZMod 3) = 1 := by
      calc
        (0 : ZMod 3) = s - s := by simp
        _ = (s + 1) - s := congrArg (fun z : ZMod 3 ↦ z - s) h
        _ = 1 := by ring
    exact zero_ne_one hzero
  intro p hp
  exact L.wordSupport_subset a ha ω
    ((L.cube a).selectedPetal_subset_wordSupport ω hs hp)

/-- Concatenation of two pair-product cubes whose pieces lie in disjoint
ambient supports. -/
def PairProductCube.tensor
    {H K : ℕ} {R S : Finset ℕ}
    (c : PairProductCube H) (d : PairProductCube K)
    (hRS : Disjoint R S)
    (hcCommon : c.common ⊆ R)
    (hcPetal : ∀ i s, c.petal i s ⊆ R)
    (hdCommon : d.common ⊆ S)
    (hdPetal : ∀ i s, d.petal i s ⊆ S) :
    PairProductCube (H + K) where
  common := c.common ∪ d.common
  petal := Fin.append c.petal d.petal
  petal_nonempty := by
    intro i s
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simpa using c.petal_nonempty j s
    · simpa using d.petal_nonempty j s
  common_disjoint := by
    intro i s
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
    · simp only [Fin.append_left]
      rw [Finset.disjoint_union_left]
      exact ⟨c.common_disjoint j s,
        disjoint_of_subset_of_subset hdCommon (hcPetal j s) hRS.symm⟩
    · simp only [Fin.append_right]
      rw [Finset.disjoint_union_left]
      exact ⟨disjoint_of_subset_of_subset hcCommon (hdPetal j s) hRS,
        d.common_disjoint j s⟩
  petal_disjoint := by
    intro i
    induction i using Fin.addCases with
    | left i' =>
        intro s j
        induction j using Fin.addCases with
        | left j' =>
            intro t hne
            simp only [Fin.append_left]
            apply c.petal_disjoint i' s j' t
            intro heq
            apply hne
            exact congrArg
              (fun z : Fin H × ZMod 3 ↦
                (Fin.castAdd K z.1, z.2)) heq
        | right j' =>
            intro t _hne
            simp only [Fin.append_left, Fin.append_right]
            exact disjoint_of_subset_of_subset
              (hcPetal i' s) (hdPetal j' t) hRS
    | right i' =>
        intro s j
        induction j using Fin.addCases with
        | left j' =>
            intro t _hne
            simp only [Fin.append_right, Fin.append_left]
            exact disjoint_of_subset_of_subset
              (hdPetal i' s) (hcPetal j' t) hRS.symm
        | right j' =>
            intro t hne
            simp only [Fin.append_right]
            apply d.petal_disjoint i' s j' t
            intro heq
            apply hne
            exact congrArg
              (fun z : Fin K × ZMod 3 ↦
                (Fin.natAdd H z.1, z.2)) heq

/-- Each word of a tensor cube is exactly the union of the two restricted
component words. -/
theorem PairProductCube.tensor_wordSupport
    {H K : ℕ} {R S : Finset ℕ}
    (c : PairProductCube H) (d : PairProductCube K)
    (hRS : Disjoint R S)
    (hcCommon : c.common ⊆ R)
    (hcPetal : ∀ i s, c.petal i s ⊆ R)
    (hdCommon : d.common ⊆ S)
    (hdPetal : ∀ i s, d.petal i s ⊆ S)
    (ω : Fin (H + K) → ZMod 3) :
    (c.tensor d hRS hcCommon hcPetal hdCommon hdPetal).wordSupport ω =
      c.wordSupport (fun i ↦ ω (Fin.castAdd K i)) ∪
        d.wordSupport (fun j ↦ ω (Fin.natAdd H j)) := by
  ext p
  constructor
  · intro hp
    rcases
        ((c.tensor d hRS hcCommon hcPetal hdCommon hdPetal).mem_wordSupport_iff
          ω p).mp hp with
      hcommon | ⟨i, s, hs, hpetal⟩
    · rcases Finset.mem_union.mp hcommon with hc | hd
      · exact Finset.mem_union_left _
          ((c.mem_wordSupport_iff _ p).mpr (Or.inl hc))
      · exact Finset.mem_union_right _
          ((d.mem_wordSupport_iff _ p).mpr (Or.inl hd))
    · induction i using Fin.addCases with
      | left i' =>
          simp only [PairProductCube.tensor, Fin.append_left] at hpetal
          apply Finset.mem_union_left
          exact (c.mem_wordSupport_iff _ p).mpr
            (Or.inr ⟨i', s, hs, hpetal⟩)
      | right j' =>
          simp only [PairProductCube.tensor, Fin.append_right] at hpetal
          apply Finset.mem_union_right
          exact (d.mem_wordSupport_iff _ p).mpr
            (Or.inr ⟨j', s, hs, hpetal⟩)
  · intro hp
    rcases Finset.mem_union.mp hp with hc | hd
    · rcases (c.mem_wordSupport_iff _ p).mp hc with
        hcommon | ⟨i, s, hs, hpetal⟩
      · exact
          (c.tensor d hRS hcCommon hcPetal hdCommon hdPetal
            |>.mem_wordSupport_iff ω p).mpr
            (Or.inl (Finset.mem_union_left _ hcommon))
      · exact
          (c.tensor d hRS hcCommon hcPetal hdCommon hdPetal
            |>.mem_wordSupport_iff ω p).mpr
            (Or.inr ⟨Fin.castAdd K i, s, hs,
              by simpa [PairProductCube.tensor] using hpetal⟩)
    · rcases (d.mem_wordSupport_iff _ p).mp hd with
        hcommon | ⟨j, s, hs, hpetal⟩
      · exact
          (c.tensor d hRS hcCommon hcPetal hdCommon hdPetal
            |>.mem_wordSupport_iff ω p).mpr
            (Or.inl (Finset.mem_union_right _ hcommon))
      · exact
          (c.tensor d hRS hcCommon hcPetal hdCommon hdPetal
            |>.mem_wordSupport_iff ω p).mpr
            (Or.inr ⟨Fin.natAdd H j, s, hs,
              by simpa [PairProductCube.tensor] using hpetal⟩)

private theorem FiniteCubeLaw.subtype_mass_sum
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) :
    ∑ a : ↥L.samples, L.mass a = 1 := by
  simpa only [Finset.sum_coe_sort] using L.mass_sum

/-- The independent product of two finite cube laws on disjoint supports.
The sample type records membership in each original finite sample space. -/
noncomputable def FiniteCubeLaw.tensor
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hRS : Disjoint R S) :
    FiniteCubeLaw (↥L.samples × ↥M.samples) (H + K) (R ∪ S) where
  samples := Finset.univ
  mass := fun ab ↦ L.mass ab.1 * M.mass ab.2
  cube := fun ab ↦
    PairProductCube.tensor (L.cube ab.1) (M.cube ab.2) hRS
      (L.common_subset ab.1.property)
      (L.petal_subset ab.1.property)
      (M.common_subset ab.2.property)
      (M.petal_subset ab.2.property)
  mass_nonneg := by
    intro ab _hab
    exact mul_nonneg
      (L.mass_nonneg ab.1 ab.1.property)
      (M.mass_nonneg ab.2 ab.2.property)
  mass_sum := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [M.subtype_mass_sum]
    simp_rw [mul_one]
    exact L.subtype_mass_sum
  wordSupport_subset := by
    intro ab _hab ω
    rw [PairProductCube.tensor_wordSupport]
    exact Finset.union_subset_union
      (L.wordSupport_subset ab.1 ab.1.property
        (fun i ↦ ω (Fin.castAdd K i)))
      (M.wordSupport_subset ab.2 ab.2.property
        (fun j ↦ ω (Fin.natAdd H j)))

@[simp]
theorem FiniteCubeLaw.tensor_samples
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hRS : Disjoint R S) :
    (L.tensor M hRS).samples = Finset.univ := rfl

@[simp]
theorem FiniteCubeLaw.tensor_mass
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hRS : Disjoint R S) (ab : ↥L.samples × ↥M.samples) :
    (L.tensor M hRS).mass ab = L.mass ab.1 * M.mass ab.2 := rfl

/-- The word-support decomposition specialized to the tensor law. -/
theorem FiniteCubeLaw.tensor_wordSupport
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    {H K : ℕ} {R S : Finset ℕ}
    (L : FiniteCubeLaw α H R) (M : FiniteCubeLaw β K S)
    (hRS : Disjoint R S)
    (ab : ↥L.samples × ↥M.samples)
    (ω : Fin (H + K) → ZMod 3) :
    ((L.tensor M hRS).cube ab).wordSupport ω =
      (L.cube ab.1).wordSupport
          (fun i ↦ ω (Fin.castAdd K i)) ∪
        (M.cube ab.2).wordSupport
          (fun j ↦ ω (Fin.natAdd H j)) := by
  exact PairProductCube.tensor_wordSupport
    (L.cube ab.1) (M.cube ab.2) hRS
    (L.common_subset ab.1.property)
    (L.petal_subset ab.1.property)
    (M.common_subset ab.2.property)
    (M.petal_subset ab.2.property) ω

end Erdos536
