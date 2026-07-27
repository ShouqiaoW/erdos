import Erdos536.JointPrefix

/-!
# From balanced cube laws to joint cutoff laws

The continuous geometric-mean construction in the manuscript has a simpler
finite equivalent.  For a sampled cube let `D` be an upper bound for all of
its word products.  Conditional on that cube, give cutoff `n ≥ D` mass

`D * squarefreeCutoffWeight R n`.

The cutoff weights telescope, so this is a probability law.  If every word
product is within a multiplicative factor `1 + δ` of `D`, this common-cutoff
kernel differs from the canonical kernel of each word by `O(δ)`.
-/

open scoped BigOperators
open Finset Nat

namespace Erdos536

/-- An explicitly weighted finite law on pair-product cubes. -/
structure FiniteCubeLaw (α : Type*) [DecidableEq α]
    (H : ℕ) (R : Finset ℕ) where
  samples : Finset α
  mass : α → ℝ
  cube : α → PairProductCube H
  mass_nonneg : ∀ a ∈ samples, 0 ≤ mass a
  mass_sum : ∑ a ∈ samples, mass a = 1
  wordSupport_subset :
    ∀ a ∈ samples, ∀ ω : Fin H → ZMod 3,
      (cube a).wordSupport ω ⊆ R

/-- Marginal mass of one word support. -/
noncomputable def FiniteCubeLaw.wordSupportMass
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (ω : Fin H → ZMod 3)
    (S : Finset ℕ) : ℝ :=
  ∑ a ∈ L.samples,
    if (L.cube a).wordSupport ω = S then L.mass a else 0

/-- `L¹` distance of one support marginal from the squarefree Bernoulli
law `S ↦ 1 / (Z_R * primeProduct S)`. -/
noncomputable def FiniteCubeLaw.wordSupportDistance
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (ω : Fin H → ZMod 3) : ℝ :=
  ∑ S ∈ R.powerset,
    |L.wordSupportMass ω S -
      1 / (squarefreeZ R * (primeProduct S : ℝ))|

private theorem sum_cutoffWeight_tail
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    {d : ℕ} (hd : 1 ≤ d) (hdR : d ≤ primeProduct R) :
    (∑ n ∈ squarefreeCutoffs R,
        if d ≤ n then squarefreeCutoffWeight R n else 0) =
      (d : ℝ)⁻¹ := by
  let D := primeProduct R
  have hD : 1 ≤ D := primeProduct_pos hR
  rw [squarefreeCutoffs, Finset.Icc_eq_cons_Ico hD, Finset.sum_cons]
  · have hfilter :
        (∑ n ∈ Ico 1 D,
            if d ≤ n then squarefreeCutoffWeight R n else 0) =
          ∑ n ∈ Ico d D, reciprocalStep n := by
        rw [← Finset.sum_filter]
        apply Finset.sum_congr
        · ext n
          simp only [mem_filter, mem_Ico]
          omega
        · intro n hn
          have hnD : n ≠ D := _root_.ne_of_lt (mem_Ico.mp hn).2
          simp [squarefreeCutoffWeight, D, hnD]
    rw [hfilter, if_pos hdR]
    simp only [squarefreeCutoffWeight, D, if_pos]
    simpa [add_comm] using sum_reciprocalStep_Ico hdR

/-- The canonical conditional cutoff kernel for a support of product `d`. -/
noncomputable def cutoffKernel (R : Finset ℕ) (d n : ℕ) : ℝ :=
  if d ≤ n then (d : ℝ) * squarefreeCutoffWeight R n else 0

theorem sum_cutoffKernel
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    {d : ℕ} (hd : 1 ≤ d) (hdR : d ≤ primeProduct R) :
    ∑ n ∈ squarefreeCutoffs R, cutoffKernel R d n = 1 := by
  simp_rw [cutoffKernel]
  have hfactor :
      (∑ n ∈ squarefreeCutoffs R,
          if d ≤ n then
            (d : ℝ) * squarefreeCutoffWeight R n
          else 0) =
        (d : ℝ) * ∑ n ∈ squarefreeCutoffs R,
          if d ≤ n then squarefreeCutoffWeight R n else 0 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hdn : d ≤ n <;> simp [hdn]
  rw [hfactor]
  rw [sum_cutoffWeight_tail R hR hd hdR]
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  exact mul_inv_cancel₀ hdpos.ne'

/-- Exact `L¹` distance between two nested conditional cutoff kernels. -/
theorem cutoffKernel_distance_eq
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    {d D : ℕ} (hd : 1 ≤ d) (hdD : d ≤ D)
    (hDR : D ≤ primeProduct R) :
    (∑ n ∈ squarefreeCutoffs R,
        |cutoffKernel R D n - cutoffKernel R d n|) =
      2 * (((D : ℝ) - (d : ℝ)) / (D : ℝ)) := by
  have hD1 : 1 ≤ D := hd.trans hdD
  have hdR : d ≤ primeProduct R := hdD.trans hDR
  have htaild :
      (∑ n ∈ squarefreeCutoffs R,
          if d ≤ n then squarefreeCutoffWeight R n else 0) =
        (d : ℝ)⁻¹ :=
    sum_cutoffWeight_tail R hR hd hdR
  have htailD :
      (∑ n ∈ squarefreeCutoffs R,
          if D ≤ n then squarefreeCutoffWeight R n else 0) =
        (D : ℝ)⁻¹ :=
    sum_cutoffWeight_tail R hR hD1 hDR
  have hmiddle :
      (∑ n ∈ squarefreeCutoffs R,
          if d ≤ n then
            if D ≤ n then 0 else squarefreeCutoffWeight R n
          else 0) =
        (d : ℝ)⁻¹ - (D : ℝ)⁻¹ := by
    have hsplit :
        (∑ n ∈ squarefreeCutoffs R,
            if d ≤ n then squarefreeCutoffWeight R n else 0) =
          (∑ n ∈ squarefreeCutoffs R,
              if d ≤ n then
                if D ≤ n then 0 else squarefreeCutoffWeight R n
              else 0) +
            ∑ n ∈ squarefreeCutoffs R,
              if D ≤ n then squarefreeCutoffWeight R n else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro n _hn
      by_cases hdn : d ≤ n
      · by_cases hDn : D ≤ n <;> simp [hdn, hDn]
      · have hDn : ¬D ≤ n := fun h ↦ hdn (hdD.trans h)
        simp [hdn, hDn]
    linarith
  have habs :
      ∀ n ∈ squarefreeCutoffs R,
        |cutoffKernel R D n - cutoffKernel R d n| =
          if d ≤ n then
            if D ≤ n then
              ((D : ℝ) - (d : ℝ)) * squarefreeCutoffWeight R n
            else
              (d : ℝ) * squarefreeCutoffWeight R n
          else 0 := by
    intro n hn
    have hw : 0 ≤ squarefreeCutoffWeight R n :=
      squarefreeCutoffWeight_nonneg R hn
    by_cases hdn : d ≤ n
    · by_cases hDn : D ≤ n
      · simp only [cutoffKernel, if_pos hdn, if_pos hDn]
        rw [← sub_mul, abs_of_nonneg]
        exact mul_nonneg
          (sub_nonneg.mpr (by exact_mod_cast hdD)) hw
      · simp only [cutoffKernel, if_pos hdn, if_neg hDn, zero_sub]
        rw [abs_neg, abs_of_nonneg]
        exact mul_nonneg (Nat.cast_nonneg _) hw
    · have hDn : ¬D ≤ n := fun h ↦ hdn (hdD.trans h)
      simp [cutoffKernel, hdn, hDn]
  calc
    (∑ n ∈ squarefreeCutoffs R,
        |cutoffKernel R D n - cutoffKernel R d n|) =
        ∑ n ∈ squarefreeCutoffs R,
          if d ≤ n then
            if D ≤ n then
              ((D : ℝ) - (d : ℝ)) * squarefreeCutoffWeight R n
            else
              (d : ℝ) * squarefreeCutoffWeight R n
          else 0 := by
            apply Finset.sum_congr rfl
            exact habs
    _ = (d : ℝ) *
          (∑ n ∈ squarefreeCutoffs R,
            if d ≤ n then
              if D ≤ n then 0 else squarefreeCutoffWeight R n
            else 0) +
        ((D : ℝ) - (d : ℝ)) *
          (∑ n ∈ squarefreeCutoffs R,
            if D ≤ n then squarefreeCutoffWeight R n else 0) := by
          rw [Finset.mul_sum, Finset.mul_sum,
            ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro n _hn
          by_cases hdn : d ≤ n
          · by_cases hDn : D ≤ n <;> simp [hdn, hDn]
          · have hDn : ¬D ≤ n := fun h ↦ hdn (hdD.trans h)
            simp [hdn, hDn]
    _ = (d : ℝ) * ((d : ℝ)⁻¹ - (D : ℝ)⁻¹) +
        ((D : ℝ) - (d : ℝ)) * (D : ℝ)⁻¹ := by
          rw [hmiddle, htailD]
    _ = 2 * (((D : ℝ) - (d : ℝ)) / (D : ℝ)) := by
          have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
          have hDpos : (0 : ℝ) < D := by exact_mod_cast hD1
          field_simp
          ring

/-- Multiplicatively balanced products give close cutoff kernels. -/
theorem cutoffKernel_distance_le
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    {d D : ℕ} {δ : ℝ} (hd : 1 ≤ d) (hdD : d ≤ D)
    (hDR : D ≤ primeProduct R) (hδ : 0 ≤ δ)
    (hbalance : (D : ℝ) ≤ (1 + δ) * (d : ℝ)) :
    (∑ n ∈ squarefreeCutoffs R,
        |cutoffKernel R D n - cutoffKernel R d n|) ≤ 2 * δ := by
  rw [cutoffKernel_distance_eq R hR hd hdD hDR]
  have hDpos : (0 : ℝ) < D := by
    exact_mod_cast hd.trans hdD
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  rw [div_le_iff₀ hDpos]
  have hdDreal : (d : ℝ) ≤ D := by exact_mod_cast hdD
  have hdnonneg : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  nlinarith

/-- The samples in the common-cutoff construction. -/
def balancedCutoffSamples
    {α : Type*} [DecidableEq α] (R : Finset ℕ)
    (Lsamples : Finset α) (D : α → ℕ) : Finset (α × ℕ) :=
  (Lsamples ×ˢ squarefreeCutoffs R).filter fun an ↦ D an.1 ≤ an.2

@[simp]
theorem mem_balancedCutoffSamples
    {α : Type*} [DecidableEq α] {R : Finset ℕ}
    {Lsamples : Finset α} {D : α → ℕ} {an : α × ℕ} :
    an ∈ balancedCutoffSamples R Lsamples D ↔
      an.1 ∈ Lsamples ∧ an.2 ∈ squarefreeCutoffs R ∧ D an.1 ≤ an.2 := by
  simp only [balancedCutoffSamples, mem_filter, mem_product]
  tauto

/-- Mass of one cube/cutoff pair in the common-cutoff construction. -/
noncomputable def balancedCutoffMass
    {α : Type*} [DecidableEq α] (R : Finset ℕ)
    (mass : α → ℝ) (D : α → ℕ) (an : α × ℕ) : ℝ :=
  mass an.1 * (D an.1 : ℝ) * squarefreeCutoffWeight R an.2

private theorem sum_balancedCutoffMass
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    (D : α → ℕ)
    (hD1 : ∀ a ∈ L.samples, 1 ≤ D a)
    (hDR : ∀ a ∈ L.samples, D a ≤ primeProduct R) :
    ∑ an ∈ balancedCutoffSamples R L.samples D,
        balancedCutoffMass R L.mass D an = 1 := by
  classical
  rw [balancedCutoffSamples, Finset.sum_filter]
  rw [Finset.sum_product]
  calc
    (∑ a ∈ L.samples, ∑ n ∈ squarefreeCutoffs R,
        if D a ≤ n then balancedCutoffMass R L.mass D (a, n) else 0) =
        ∑ a ∈ L.samples, L.mass a := by
          apply Finset.sum_congr rfl
          intro a ha
          simp only [balancedCutoffMass]
          calc
            (∑ n ∈ squarefreeCutoffs R,
                if D a ≤ n then
                  L.mass a * (D a : ℝ) * squarefreeCutoffWeight R n
                else 0) =
                (L.mass a * (D a : ℝ)) *
                  ∑ n ∈ squarefreeCutoffs R,
                    if D a ≤ n then squarefreeCutoffWeight R n else 0 := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro n _hn
                      by_cases hDn : D a ≤ n <;> simp [hDn]
            _ = (L.mass a * (D a : ℝ)) * ((D a : ℝ)⁻¹) := by
                  rw [sum_cutoffWeight_tail R hR (hD1 a ha) (hDR a ha)]
            _ = L.mass a := by
                  have hDpos : (0 : ℝ) < D a := by
                    exact_mod_cast hD1 a ha
                  field_simp
    _ = 1 := L.mass_sum

/-- Turn a balanced cube law into a genuine finite cube/cutoff law.
The function `D` may be the maximum word product; only its displayed
bounding properties are used. -/
noncomputable def FiniteCubeLaw.toCutoffLaw
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    (D : α → ℕ)
    (hD1 : ∀ a ∈ L.samples, 1 ≤ D a)
    (hDR : ∀ a ∈ L.samples, D a ≤ primeProduct R)
    (hwordD : ∀ a ∈ L.samples, ∀ ω : Fin H → ZMod 3,
      primeProduct ((L.cube a).wordSupport ω) ≤ D a) :
    FiniteCubeCutoffLaw (α × ℕ) H R where
  samples := balancedCutoffSamples R L.samples D
  mass := balancedCutoffMass R L.mass D
  cube := fun an ↦ L.cube an.1
  cutoff := Prod.snd
  mass_nonneg := by
    intro an han
    have hdata := mem_balancedCutoffSamples.mp han
    have ha := hdata.1
    have hn := hdata.2.1
    exact mul_nonneg
      (mul_nonneg (L.mass_nonneg an.1 ha) (Nat.cast_nonneg _))
      (squarefreeCutoffWeight_nonneg R hn)
  mass_sum := sum_balancedCutoffMass L hR D hD1 hDR
  cutoff_mem := by
    intro an han
    exact (mem_balancedCutoffSamples.mp han).2.1
  word_mem_prefix := by
    intro an han ω
    have hdata := mem_balancedCutoffSamples.mp han
    have ha := hdata.1
    have hDn := hdata.2.2
    exact mem_squarefreePrefix_iff.mpr
      ⟨L.wordSupport_subset an.1 ha ω, (hwordD an.1 ha ω).trans hDn⟩

/-- The joint marginal obtained by first sampling a cube and then using its
common cutoff kernel. -/
noncomputable def FiniteCubeLaw.commonWordMarginal
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (D : α → ℕ)
    (ω : Fin H → ZMod 3) (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ a ∈ L.samples,
    if (L.cube a).wordSupport ω = S then
      L.mass a * cutoffKernel R (D a) n
    else 0

/-- The joint marginal obtained by giving each sampled word its own
canonical support-product cutoff kernel. -/
noncomputable def FiniteCubeLaw.idealWordMarginal
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R)
    (ω : Fin H → ZMod 3) (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∑ a ∈ L.samples,
    if (L.cube a).wordSupport ω = S then
      L.mass a *
        cutoffKernel R
          (primeProduct ((L.cube a).wordSupport ω)) n
    else 0

theorem FiniteCubeLaw.toCutoffLaw_wordMarginal
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    (D : α → ℕ)
    (hD1 : ∀ a ∈ L.samples, 1 ≤ D a)
    (hDR : ∀ a ∈ L.samples, D a ≤ primeProduct R)
    (hwordD : ∀ a ∈ L.samples, ∀ ω : Fin H → ZMod 3,
      primeProduct ((L.cube a).wordSupport ω) ≤ D a)
    (ω : Fin H → ZMod 3) (S : Finset ℕ) {n : ℕ}
    (hn : n ∈ squarefreeCutoffs R) :
    (L.toCutoffLaw hR D hD1 hDR hwordD).wordMarginal ω S n =
      L.commonWordMarginal D ω S n := by
  classical
  rw [FiniteCubeCutoffLaw.wordMarginal,
    FiniteCubeLaw.commonWordMarginal]
  simp only [FiniteCubeLaw.toCutoffLaw]
  rw [balancedCutoffSamples, Finset.sum_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [Finset.sum_eq_single n]
  · by_cases hsupport : (L.cube a).wordSupport ω = S
    · by_cases hDn : D a ≤ n
      · simp [hsupport, hDn, balancedCutoffMass, cutoffKernel, mul_assoc]
      · simp [hsupport, hDn, cutoffKernel]
    · simp [hsupport]
  · intro m _hm hmn
    simp [hmn]
  · exact fun hn' ↦ (hn' hn).elim

theorem canonicalPrefixMass_eq_supportMass_mul_kernel
    (R : Finset ℕ) (hR : IsPrimeSupport R)
    {S : Finset ℕ} (hS : S ∈ R.powerset) (n : ℕ) :
    canonicalPrefixMass R S n =
      (1 / (squarefreeZ R * (primeProduct S : ℝ))) *
        cutoffKernel R (primeProduct S) n := by
  have hSR : S ⊆ R := mem_powerset.mp hS
  have hdpos : 0 < primeProduct S :=
    primeProduct_pos (isPrimeSupport_mono hR hSR)
  have hdreal : (primeProduct S : ℝ) ≠ 0 := by exact_mod_cast hdpos.ne'
  by_cases hdn : primeProduct S ≤ n
  · rw [canonicalPrefixMass, if_pos
      (mem_squarefreePrefix_iff.mpr ⟨hSR, hdn⟩)]
    simp only [cutoffKernel, if_pos hdn]
    have hZne : squarefreeZ R ≠ 0 := (squarefreeZ_pos R hR).ne'
    field_simp
  · rw [canonicalPrefixMass, if_neg]
    · simp [cutoffKernel, hdn]
    · intro hmem
      exact hdn (mem_squarefreePrefix_iff.mp hmem).2

theorem FiniteCubeLaw.idealWordMarginal_eq
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (ω : Fin H → ZMod 3)
    (S : Finset ℕ) (n : ℕ) :
    L.idealWordMarginal ω S n =
      L.wordSupportMass ω S *
        cutoffKernel R (primeProduct S) n := by
  classical
  rw [FiniteCubeLaw.idealWordMarginal,
    FiniteCubeLaw.wordSupportMass, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hsupport : (L.cube a).wordSupport ω = S
  · simp [hsupport]
  · simp [hsupport]

private theorem sum_support_indicator
    {α : Type*} [DecidableEq α]
    (A : Finset α) (B : Finset (Finset ℕ))
    (support : α → Finset ℕ)
    (hsupport : ∀ a ∈ A, support a ∈ B)
    (g : α → ℝ) :
    (∑ S ∈ B, ∑ a ∈ A,
        if support a = S then g a else 0) =
      ∑ a ∈ A, g a := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_eq_single (support a)]
  · simp
  · intro S _hS hSne
    simp [hSne.symm]
  · exact fun hnot ↦ (hnot (hsupport a ha)).elim

private theorem common_sub_ideal_eq
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (D : α → ℕ)
    (ω : Fin H → ZMod 3) (S : Finset ℕ) (n : ℕ) :
    L.commonWordMarginal D ω S n -
        L.idealWordMarginal ω S n =
      ∑ a ∈ L.samples,
        if (L.cube a).wordSupport ω = S then
          L.mass a *
            (cutoffKernel R (D a) n -
              cutoffKernel R
                (primeProduct ((L.cube a).wordSupport ω)) n)
        else 0 := by
  classical
  rw [FiniteCubeLaw.commonWordMarginal,
    FiniteCubeLaw.idealWordMarginal, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hsupport : (L.cube a).wordSupport ω = S
  · simp only [hsupport, if_true]
    ring
  · simp [hsupport]

/-- Averaging balanced common kernels over a cube law costs at most
`2 * δ` in joint `L¹` distance from the wordwise canonical kernels. -/
theorem FiniteCubeLaw.common_ideal_distance_le
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    (D : α → ℕ) (ω : Fin H → ZMod 3) {δ : ℝ}
    (hDR : ∀ a ∈ L.samples, D a ≤ primeProduct R)
    (hwordD : ∀ a ∈ L.samples,
      primeProduct ((L.cube a).wordSupport ω) ≤ D a)
    (hδ : 0 ≤ δ)
    (hbalance : ∀ a ∈ L.samples,
      (D a : ℝ) ≤
        (1 + δ) *
          (primeProduct ((L.cube a).wordSupport ω) : ℝ)) :
    (∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
        |L.commonWordMarginal D ω S n -
          L.idealWordMarginal ω S n|) ≤
      2 * δ := by
  classical
  let support : α → Finset ℕ :=
    fun a ↦ (L.cube a).wordSupport ω
  have hsupport_mem :
      ∀ a ∈ L.samples, support a ∈ R.powerset := by
    intro a ha
    exact mem_powerset.mpr (L.wordSupport_subset a ha ω)
  have hd1 :
      ∀ a ∈ L.samples, 1 ≤ primeProduct (support a) := by
    intro a ha
    exact primeProduct_pos
      (isPrimeSupport_mono hR
        (L.wordSupport_subset a ha ω))
  calc
    (∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
        |L.commonWordMarginal D ω S n -
          L.idealWordMarginal ω S n|) ≤
        ∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
          ∑ a ∈ L.samples,
            if support a = S then
              L.mass a *
                |cutoffKernel R (D a) n -
                  cutoffKernel R (primeProduct (support a)) n|
            else 0 := by
          apply Finset.sum_le_sum
          intro n _hn
          apply Finset.sum_le_sum
          intro S _hS
          rw [common_sub_ideal_eq L D ω S n]
          calc
            |∑ a ∈ L.samples,
                if support a = S then
                  L.mass a *
                    (cutoffKernel R (D a) n -
                      cutoffKernel R (primeProduct (support a)) n)
                else 0| ≤
                ∑ a ∈ L.samples,
                  |if support a = S then
                    L.mass a *
                      (cutoffKernel R (D a) n -
                        cutoffKernel R (primeProduct (support a)) n)
                  else 0| :=
              Finset.abs_sum_le_sum_abs _ _
            _ = ∑ a ∈ L.samples,
                if support a = S then
                  L.mass a *
                    |cutoffKernel R (D a) n -
                      cutoffKernel R (primeProduct (support a)) n|
                else 0 := by
                  apply Finset.sum_congr rfl
                  intro a ha
                  by_cases has : support a = S
                  · simp only [has, if_true, abs_mul]
                    rw [abs_of_nonneg (L.mass_nonneg a ha)]
                  · simp [has]
    _ = ∑ n ∈ squarefreeCutoffs R, ∑ a ∈ L.samples,
          L.mass a *
            |cutoffKernel R (D a) n -
              cutoffKernel R (primeProduct (support a)) n| := by
          apply Finset.sum_congr rfl
          intro n _hn
          exact sum_support_indicator L.samples R.powerset support
            hsupport_mem
            (fun a ↦ L.mass a *
              |cutoffKernel R (D a) n -
                cutoffKernel R (primeProduct (support a)) n|)
    _ = ∑ a ∈ L.samples, L.mass a *
          (∑ n ∈ squarefreeCutoffs R,
            |cutoffKernel R (D a) n -
              cutoffKernel R (primeProduct (support a)) n|) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro a _ha
          rw [Finset.mul_sum]
    _ ≤ ∑ a ∈ L.samples, L.mass a * (2 * δ) := by
          apply Finset.sum_le_sum
          intro a ha
          apply mul_le_mul_of_nonneg_left _ (L.mass_nonneg a ha)
          exact cutoffKernel_distance_le R hR (hd1 a ha)
            (hwordD a ha) (hDR a ha) hδ (hbalance a ha)
    _ = 2 * δ := by
          rw [← Finset.sum_mul, L.mass_sum, one_mul]

theorem cutoffKernel_nonneg
    (R : Finset ℕ) {d n : ℕ} (hn : n ∈ squarefreeCutoffs R) :
    0 ≤ cutoffKernel R d n := by
  rw [cutoffKernel]
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _)
      (squarefreeCutoffWeight_nonneg R hn)
  · exact le_rfl

/-- The ideal joint marginal has exactly the support-marginal `L¹`
distance from the canonical squarefree law. -/
theorem FiniteCubeLaw.ideal_canonical_distance_eq
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    (ω : Fin H → ZMod 3) :
    (∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
        |L.idealWordMarginal ω S n -
          canonicalPrefixMass R S n|) =
      L.wordSupportDistance ω := by
  classical
  have hperSupport :
      ∀ S ∈ R.powerset,
        (∑ n ∈ squarefreeCutoffs R,
          |L.idealWordMarginal ω S n -
            canonicalPrefixMass R S n|) =
          |L.wordSupportMass ω S -
            1 / (squarefreeZ R * (primeProduct S : ℝ))| := by
    intro S hS
    have hSR : S ⊆ R := mem_powerset.mp hS
    have hd1 : 1 ≤ primeProduct S :=
      primeProduct_pos (isPrimeSupport_mono hR hSR)
    have hdR : primeProduct S ≤ primeProduct R :=
      primeProduct_le_total hR hSR
    calc
      (∑ n ∈ squarefreeCutoffs R,
          |L.idealWordMarginal ω S n -
            canonicalPrefixMass R S n|) =
          ∑ n ∈ squarefreeCutoffs R,
            |(L.wordSupportMass ω S -
                1 / (squarefreeZ R * (primeProduct S : ℝ))) *
              cutoffKernel R (primeProduct S) n| := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [L.idealWordMarginal_eq ω S n,
              canonicalPrefixMass_eq_supportMass_mul_kernel
                R hR hS n, sub_mul]
      _ = |L.wordSupportMass ω S -
              1 / (squarefreeZ R * (primeProduct S : ℝ))| *
            ∑ n ∈ squarefreeCutoffs R,
              cutoffKernel R (primeProduct S) n := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro n hn
            rw [abs_mul,
              abs_of_nonneg (cutoffKernel_nonneg R hn)]
      _ = |L.wordSupportMass ω S -
            1 / (squarefreeZ R * (primeProduct S : ℝ))| := by
            rw [sum_cutoffKernel R hR hd1 hdR, mul_one]
  rw [FiniteCubeLaw.wordSupportDistance, Finset.sum_comm]
  apply Finset.sum_congr rfl
  exact hperSupport

/-- A balanced law of pair-product cubes gives a joint-prefix law whose
word marginal differs from the canonical law by the support error plus
`2 * δ`. -/
theorem FiniteCubeLaw.toCutoffLaw_wordPrefixDistance_le
    {α : Type*} [DecidableEq α] {H : ℕ} {R : Finset ℕ}
    (L : FiniteCubeLaw α H R) (hR : IsPrimeSupport R)
    (D : α → ℕ)
    (hD1 : ∀ a ∈ L.samples, 1 ≤ D a)
    (hDR : ∀ a ∈ L.samples, D a ≤ primeProduct R)
    (hwordD : ∀ a ∈ L.samples, ∀ ω : Fin H → ZMod 3,
      primeProduct ((L.cube a).wordSupport ω) ≤ D a)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbalance : ∀ a ∈ L.samples, ∀ ω : Fin H → ZMod 3,
      (D a : ℝ) ≤
        (1 + δ) *
          (primeProduct ((L.cube a).wordSupport ω) : ℝ))
    (ω : Fin H → ZMod 3) :
    (L.toCutoffLaw hR D hD1 hDR hwordD).wordPrefixDistance ω ≤
      L.wordSupportDistance ω + 2 * δ := by
  classical
  rw [FiniteCubeCutoffLaw.wordPrefixDistance]
  calc
    (∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
        |(L.toCutoffLaw hR D hD1 hDR hwordD).wordMarginal ω S n -
          canonicalPrefixMass R S n|) =
        ∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
          |L.commonWordMarginal D ω S n -
            canonicalPrefixMass R S n| := by
          apply Finset.sum_congr rfl
          intro n hn
          apply Finset.sum_congr rfl
          intro S _hS
          rw [L.toCutoffLaw_wordMarginal hR D hD1 hDR hwordD
            ω S hn]
    _ ≤
        (∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
          |L.commonWordMarginal D ω S n -
            L.idealWordMarginal ω S n|) +
        ∑ n ∈ squarefreeCutoffs R, ∑ S ∈ R.powerset,
          |L.idealWordMarginal ω S n -
            canonicalPrefixMass R S n| := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro n _hn
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_le_sum
          intro S _hS
          exact abs_sub_le _ _ _
    _ ≤ 2 * δ + L.wordSupportDistance ω := by
          apply _root_.add_le_add
          · exact L.common_ideal_distance_le hR D ω hDR
              (fun a ha ↦ hwordD a ha ω) hδ
              (fun a ha ↦ hbalance a ha ω)
          · exact le_of_eq (L.ideal_canonical_distance_eq hR ω)
    _ = L.wordSupportDistance ω + 2 * δ := add_comm _ _

end Erdos536
