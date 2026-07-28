import Erdos390.Full.PoissonMass

/-!
# Exact shell self-similarity

The tail below a logarithmic shell cutoff is a scaled copy of the whole
scale-invariant Poisson construction.  Both the pointwise mass scaling and
the law invariance of the shifted iid shell sequence are proved here.  These
are the probability-theoretic ingredients behind the remaining
compound-Poisson/Dickman self-decomposition identity.
-/

open Filter Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Erdos390.Full.PoissonSelfSimilarity

open MeasureTheory ProbabilityTheory Real
open ConditionedPoisson

/-- Drop the first `K` logarithmic shells. -/
def shiftShells (K : ℕ) (omega : GlobalSample) : GlobalSample :=
  fun k ↦ omega (K + k)

/-- The finite block of shells strictly before `K`. -/
def prefixShells (K : ℕ) (omega : GlobalSample) : Fin K → Sample :=
  fun k ↦ omega k

lemma measurable_prefixShells (K : ℕ) : Measurable (prefixShells K) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply (X := fun _ : ℕ ↦ Sample) k.val

lemma measurable_shiftShells (K : ℕ) : Measurable (shiftShells K) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply (K + k)

/-- The shell shift is measure preserving because the shell coordinates are
iid. -/
lemma shiftShells_map (K : ℕ) :
    globalLaw.map (shiftShells K) = globalLaw := by
  let I : Set ℕ := Ici K
  let e : ℕ ≃ I :=
    { toFun := fun n ↦ ⟨K + n, by simp [I]⟩
      invFun := fun n ↦ n.1 - K
      left_inv := by
        intro n
        simp
      right_inv := by
        intro n
        apply Subtype.ext
        dsimp
        have hn := n.property
        change K ≤ n.1 at hn
        omega }
  let reindex : (I → Sample) → GlobalSample :=
    MeasurableEquiv.piCongrLeft (fun _ : ℕ ↦ Sample) e.symm
  have hreindex : Measurable reindex := by
    exact (MeasurableEquiv.piCongrLeft (fun _ : ℕ ↦ Sample) e.symm).measurable
  have hrestrict : Measurable (I.restrict : GlobalSample → I → Sample) := by
    fun_prop
  have hcomp : shiftShells K = reindex ∘ I.restrict := by
    funext omega
    funext k
    simp [shiftShells, reindex, e, I, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft_apply]
  rw [hcomp, ← Measure.map_map hreindex hrestrict]
  unfold globalLaw
  rw [Measure.infinitePi_map_restrict']
  exact Measure.infinitePi_map_piCongrLeft
    (μ := fun _ : ℕ ↦ shellLaw) e.symm

/-- The initial finite shell block and the reindexed infinite tail are
independent.  This is proved from the actual product measure `globalLaw`, not
postulated as a Poisson-process property. -/
lemma prefixShells_indep_shiftShells (K : ℕ) :
    IndepFun (prefixShells K) (shiftShells K) globalLaw := by
  let Z : ℕ → GlobalSample → Sample := fun n omega ↦ omega n
  have hZ : iIndepFun Z globalLaw := by
    unfold globalLaw
    exact iIndepFun_infinitePi
      (P := fun _ : ℕ ↦ shellLaw) (X := fun _ : ℕ ↦ id)
      (fun _ ↦ measurable_id)
  have hprocess :
      IndepFun (fun omega (i : Fin K) ↦ omega i.val)
        (fun omega (j : ℕ) ↦ omega (K + j)) globalLaw := by
    apply IndepFun.process_indepFun_process
      (fun _ ↦ measurable_pi_apply _) (fun _ ↦ measurable_pi_apply _)
    intro I J
    classical
    let A : Finset ℕ := I.image (fun i : Fin K ↦ i.val)
    let B : Finset ℕ := J.image (fun j : ℕ ↦ K + j)
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro n hnA hnB
      obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.mp hnA
      obtain ⟨j, hjJ, hij⟩ := Finset.mem_image.mp hnB
      have hi_lt : i.val < K := i.isLt
      omega
    have hfinite := hZ.indepFun_finset A B hAB
      (fun n ↦ measurable_pi_apply n)
    let reindexA : (A → Sample) → (I → Sample) := fun x i ↦
      x ⟨i.1.val, Finset.mem_image.mpr ⟨i.1, i.2, rfl⟩⟩
    let reindexB : (B → Sample) → (J → Sample) := fun x j ↦
      x ⟨K + j.1, Finset.mem_image.mpr ⟨j.1, j.2, rfl⟩⟩
    have hreindexA : Measurable reindexA := by
      apply measurable_pi_lambda
      intro i
      exact measurable_pi_apply _
    have hreindexB : Measurable reindexB := by
      apply measurable_pi_lambda
      intro j
      exact measurable_pi_apply _
    have hcomposed := hfinite.comp hreindexA hreindexB
    simpa only [Z, Function.id_def, reindexA, reindexB] using hcomposed
  simpa only [prefixShells, shiftShells] using hprocess

/-- Total mass contributed by the first `K` shells. -/
def prefixMass (K : ℕ) (omega : GlobalSample) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range K, shellMass k (omega k)

lemma measurable_prefixMass (K : ℕ) : Measurable (prefixMass K) := by
  unfold prefixMass
  apply Finset.measurable_sum
  intro k _hk
  exact (measurable_shellMass k).comp (measurable_pi_apply k)

lemma shellAtom_add (K k : ℕ) (u : ℝ) :
    shellAtom (K + k) u = exp (-(K : ℝ)) * shellAtom k u := by
  unfold shellAtom
  rw [← exp_add]
  congr 1
  push_cast
  ring

private lemma shellMassTerm_add (K k i : ℕ) (omega : Sample) :
    shellMassTerm (K + k) i omega =
      ENNReal.ofReal (exp (-(K : ℝ))) * shellMassTerm k i omega := by
  unfold shellMassTerm
  split_ifs with hi
  · rw [shellAtom_add, ENNReal.ofReal_mul (exp_pos _).le]
  · simp

/-- Exact mass scaling for one shell. -/
lemma shellMass_add (K k : ℕ) (omega : Sample) :
    shellMass (K + k) omega =
      ENNReal.ofReal (exp (-(K : ℝ))) * shellMass k omega := by
  unfold shellMass
  simp_rw [shellMassTerm_add]
  rw [ENNReal.tsum_mul_left]

/-- Total mass in all shells at index at least `K`. -/
def tailMass (K : ℕ) (omega : GlobalSample) : ℝ≥0∞ :=
  ∑' k : ℕ, shellMass (K + k) (omega (K + k))

lemma measurable_tailMass (K : ℕ) : Measurable (tailMass K) := by
  apply Measurable.ennreal_tsum
  intro k
  exact (measurable_shellMass (K + k)).comp (measurable_pi_apply (K + k))

/-- Pointwise self-similarity of the infinite tail mass. -/
lemma tailMass_eq_scaled (K : ℕ) (omega : GlobalSample) :
    tailMass K omega =
      ENNReal.ofReal (exp (-(K : ℝ))) *
        globalTotalMass (shiftShells K omega) := by
  unfold tailMass globalTotalMass shiftShells
  simp_rw [shellMass_add]
  rw [ENNReal.tsum_mul_left]

/-- Exact pointwise decomposition into the finite prefix and infinite tail.
The identity is valid even on the null set on which one of the extended-real
masses might be infinite. -/
lemma prefixMass_add_tailMass (K : ℕ) (omega : GlobalSample) :
    prefixMass K omega + tailMass K omega = globalTotalMass omega := by
  let e : ℕ ≃ {k : ℕ // k ∉ Finset.range K} :=
    { toFun := fun k ↦ ⟨K + k, by simp⟩
      invFun := fun k ↦ k.1 - K
      left_inv := by
        intro k
        simp
      right_inv := by
        intro k
        apply Subtype.ext
        have hk : K ≤ k.1 := by simpa [Finset.mem_range] using k.2
        dsimp
        omega }
  have htail :
      (∑' k : ℕ, shellMass (K + k) (omega (K + k))) =
        ∑' k : {k : ℕ // k ∉ Finset.range K}, shellMass k.1 (omega k.1) := by
    simpa only [e] using
      (Equiv.tsum_eq e (fun k : {k : ℕ // k ∉ Finset.range K} ↦
        shellMass k.1 (omega k.1)))
  unfold prefixMass tailMass globalTotalMass
  rw [htail]
  exact ENNReal.sum_add_tsum_compl (Finset.range K)
    (fun k ↦ shellMass k (omega k))

/-- The finite prefix mass and the infinite tail mass are independent. -/
lemma prefixMass_indep_tailMass (K : ℕ) :
    IndepFun (prefixMass K) (tailMass K) globalLaw := by
  let blockMass : (Fin K → Sample) → ℝ≥0∞ := fun x ↦
    ∑ k : Fin K, shellMass k.val (x k)
  let scaledMass : GlobalSample → ℝ≥0∞ := fun omega ↦
    ENNReal.ofReal (exp (-(K : ℝ))) * globalTotalMass omega
  have hblock : Measurable blockMass := by
    dsimp [blockMass]
    apply Finset.measurable_sum
    intro k _hk
    exact (measurable_shellMass k.val).comp (measurable_pi_apply k)
  have hscaled : Measurable scaledMass := by
    exact measurable_const.mul measurable_globalTotalMass
  have hcomp := (prefixShells_indep_shiftShells K).comp hblock hscaled
  have hleft : blockMass ∘ prefixShells K = prefixMass K := by
    funext omega
    change (∑ k : Fin K, shellMass k.val (omega k.val)) =
      ∑ k ∈ Finset.range K, shellMass k (omega k)
    exact Fin.sum_univ_eq_sum_range (fun k ↦ shellMass k (omega k)) K
  have hright : scaledMass ∘ shiftShells K = tailMass K := by
    funext omega
    exact (tailMass_eq_scaled K omega).symm
  simpa only [hleft, hright] using hcomp

/-- The exact convolution self-decomposition of the total-mass law at every
integer logarithmic cutoff. -/
lemma globalTotalMass_map_conv (K : ℕ) :
    globalLaw.map globalTotalMass =
      (globalLaw.map (prefixMass K)).conv (globalLaw.map (tailMass K)) := by
  have hconv := (prefixMass_indep_tailMass K).map_add_eq_map_conv_map
    (measurable_prefixMass K) (measurable_tailMass K)
  rw [← hconv]
  congr 1
  funext omega
  exact (prefixMass_add_tailMass K omega).symm

/-- Consequently the tail mass has the law of an exact deterministic scaling
of the full total mass. -/
lemma tailMass_map (K : ℕ) :
    globalLaw.map (tailMass K) =
      globalLaw.map (fun omega ↦
        ENNReal.ofReal (exp (-(K : ℝ))) * globalTotalMass omega) := by
  have htail : tailMass K =
      (fun omega ↦ ENNReal.ofReal (exp (-(K : ℝ))) *
        globalTotalMass omega) ∘ shiftShells K := by
    funext omega
    exact tailMass_eq_scaled K omega
  rw [htail, ← Measure.map_map]
  · rw [shiftShells_map]
  · exact measurable_const.mul measurable_globalTotalMass
  · exact measurable_shiftShells K

end Erdos390.Full.PoissonSelfSimilarity
