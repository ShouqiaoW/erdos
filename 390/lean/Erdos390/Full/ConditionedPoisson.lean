import Mathlib

/-!
# Finite scale-invariant Poisson configurations and the conditioned bridge

This file starts the probability-theoretic construction used in the
Poisson--Dickman part of the paper.  The construction is deliberately made
from elementary probability measures rather than assuming the existence of a
Poisson point process or a Palm formula.

For a cutoff `eps`, logarithmic coordinates identify `(eps,1]`, equipped with
`dt/t`, with an interval of length `-log eps`.  We sample a Poisson number of
independent uniform logarithmic coordinates and map them back by the
exponential.  An infinite iid coordinate sequence is used only as a convenient
ambient sample space; the active configuration consists of its first `N`
coordinates and is finite.

The exact layer completed below comprises:

* the finite-cutoff probability law and its normalization;
* its Poisson count and iid coordinate marginals;
* the Poisson size-bias recurrence and the resulting Janossy
  Campbell--Mecke identity;
* a cofinal shell construction whose finite restrictions are literally
  projectively compatible as the cutoff decreases to zero.

What is not yet claimed here is the paper's canonical conditional law at an
exact total mass `u`.  Reaching that statement still requires formalizing the
continuous density of the infinite small-atom mass (the Dickman density), its
convolution identity, and the density-weighted consistency calculation.  In
particular, no regular conditional law, Palm identity, covariance formula, or
kernel conclusion is postulated as a hypothesis in this file.
-/

open Filter Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace Erdos390.Full.ConditionedPoisson

open MeasureTheory ProbabilityTheory Real

/-- A genuine cutoff strictly between zero and one. -/
structure Cutoff where
  eps : ℝ
  eps_pos : 0 < eps
  eps_lt_one : eps < 1

/-- Length of the cutoff interval in logarithmic coordinates. -/
def Cutoff.logLength (c : Cutoff) : ℝ := -log c.eps

lemma Cutoff.logLength_pos (c : Cutoff) : 0 < c.logLength := by
  rw [Cutoff.logLength, neg_pos]
  exact log_neg c.eps_pos c.eps_lt_one

/-- The Poisson rate corresponding to the intensity `dt/t` on `(eps,1]`. -/
def Cutoff.rate (c : Cutoff) : ℝ≥0 :=
  ⟨c.logLength, c.logLength_pos.le⟩

@[simp] lemma Cutoff.rate_toReal (c : Cutoff) : c.rate.toReal = c.logLength := rfl

/-- Uniform probability measure on `(0,1]`.  Endpoints are immaterial, but
`Ioc` is convenient for exact volume normalization. -/
def unitLaw : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)

instance unitLaw_isProbability : IsProbabilityMeasure unitLaw := by
  constructor
  simp [unitLaw]

lemma unitLaw_ae_mem : ∀ᵐ x ∂unitLaw, x ∈ Ioc (0 : ℝ) 1 := by
  exact ae_restrict_mem measurableSet_Ioc

/-- An iid supply of uniform logarithmic coordinates. -/
def coordinateLaw : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ : ℕ => unitLaw)

instance coordinateLaw_isProbability : IsProbabilityMeasure coordinateLaw := by
  unfold coordinateLaw
  infer_instance

/-- Ambient sample: a Poisson count and an independent iid sequence. -/
abbrev Sample := ℕ × (ℕ → ℝ)

/-- The elementary finite-cutoff Poisson configuration law. -/
def finiteLaw (c : Cutoff) : Measure Sample :=
  (poissonMeasure c.rate).prod coordinateLaw

instance finiteLaw_isProbability (c : Cutoff) : IsProbabilityMeasure (finiteLaw c) := by
  unfold finiteLaw
  infer_instance

lemma finiteLaw_normalized (c : Cutoff) : finiteLaw c univ = 1 := by
  exact measure_univ

/-- Map one uniform logarithmic coordinate back to `(eps,1]`. -/
def atom (c : Cutoff) (u : ℝ) : ℝ := exp (-(c.logLength * u))

lemma atom_pos (c : Cutoff) (u : ℝ) : 0 < atom c u := by
  exact exp_pos _

lemma atom_le_one (c : Cutoff) {u : ℝ} (hu : 0 ≤ u) : atom c u ≤ 1 := by
  rw [atom, exp_le_one_iff]
  exact neg_nonpos.mpr (mul_nonneg c.logLength_pos.le hu)

lemma cutoff_le_atom (c : Cutoff) {u : ℝ} (hu : u ≤ 1) : c.eps ≤ atom c u := by
  have hlog : log c.eps = -c.logLength := by simp [Cutoff.logLength]
  rw [← exp_log c.eps_pos, hlog, atom, exp_le_exp]
  have hL := c.logLength_pos.le
  nlinarith

/-- The active finite list of atoms.  It is a concrete configuration; the
ordering is auxiliary and is forgotten by every symmetric Janossy test. -/
def activeAtoms (c : Cutoff) (omega : Sample) : List ℝ :=
  List.ofFn fun i : Fin omega.1 => atom c (omega.2 i.val)

@[simp] lemma activeAtoms_length (c : Cutoff) (omega : Sample) :
    (activeAtoms c omega).length = omega.1 := by
  simp [activeAtoms]

/-- The count marginal is exactly Poisson. -/
lemma finiteLaw_map_count (c : Cutoff) :
    (finiteLaw c).map Prod.fst = poissonMeasure c.rate := by
  exact measurePreserving_fst.map_eq

/-- Every coordinate has the declared uniform marginal. -/
lemma finiteLaw_map_coordinate (c : Cutoff) (i : ℕ) :
    (finiteLaw c).map (fun omega => omega.2 i) = unitLaw := by
  have hsnd : MeasurePreserving Prod.snd (finiteLaw c) coordinateLaw :=
    measurePreserving_snd
  have heval : MeasurePreserving (Function.eval i) coordinateLaw unitLaw := by
    exact measurePreserving_eval_infinitePi (fun _ : ℕ => unitLaw) i
  exact (heval.comp hsnd).map_eq

lemma finiteLaw_ae_active_atoms_in_cutoff (c : Cutoff) :
    ∀ᵐ omega ∂finiteLaw c, ∀ i : Fin omega.1,
      atom c (omega.2 i.val) ∈ Icc c.eps 1 := by
  have hcoord (i : ℕ) : ∀ᵐ omega ∂finiteLaw c, omega.2 i ∈ Ioc (0 : ℝ) 1 := by
    have hsnd : MeasurePreserving Prod.snd (finiteLaw c) coordinateLaw :=
      measurePreserving_snd
    have heval : MeasurePreserving (Function.eval i) coordinateLaw unitLaw :=
      measurePreserving_eval_infinitePi (fun _ : ℕ => unitLaw) i
    exact (heval.comp hsnd).quasiMeasurePreserving.tendsto_ae unitLaw_ae_mem
  have hall : ∀ᵐ omega ∂finiteLaw c, ∀ i : ℕ,
      omega.2 i ∈ Ioc (0 : ℝ) 1 := by
    exact ae_all_iff.mpr hcoord
  filter_upwards [hall] with omega homega i
  exact ⟨cutoff_le_atom c (homega i.val).2,
    atom_le_one c (homega i.val).1.le⟩

/-! ## The Janossy count identity -/

/-- Elementary Poisson size-bias recurrence in real form. -/
lemma poissonPMFReal_succ_size_bias (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) * poissonPMFReal r (n + 1) =
      (r : ℝ) * poissonPMFReal r n := by
  rw [poissonPMFReal, poissonPMFReal, Nat.factorial_succ]
  push_cast
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  have hfac : (n.factorial : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The same recurrence for the actual `ENNReal`-valued Poisson PMF. -/
lemma poissonPMF_succ_size_bias (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 1) =
      (r : ℝ≥0∞) * poissonPMF r n := by
  change ((n + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r (n + 1)) =
    (r : ℝ≥0∞) * ENNReal.ofReal (poissonPMFReal r n)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg (n + 1)),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (NNReal.coe_nonneg r),
    poissonPMFReal_succ_size_bias]

/-- Unmarked Janossy expectation: the Poisson mixture of an arbitrary
nonnegative functional indexed by the number of residual points. -/
def janossyExpectation (r : ℝ≥0) (A : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, poissonPMF r n * A n

/-- Mark one point in an `(n+1)`-point Janossy density.  The factor `n+1`
is the exact sum over the possible distinguished atoms. -/
def markedJanossyExpectation (r : ℝ≥0) (A : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 1) * A n

/-- Campbell--Mecke at the count/Janossy level, derived solely from the
Poisson recurrence.  Substituting for `A n` the product integral of a test
function over one marked point and `n` residual iid points is precisely the
finite-cutoff Palm formula. -/
lemma markedJanossy_eq_rate_mul (r : ℝ≥0) (A : ℕ → ℝ≥0∞) :
    markedJanossyExpectation r A = (r : ℝ≥0∞) * janossyExpectation r A := by
  unfold markedJanossyExpectation janossyExpectation
  simp_rw [poissonPMF_succ_size_bias, mul_assoc]
  exact ENNReal.tsum_mul_left

/-- The preceding identity at the scale-invariant cutoff rate. -/
lemma cutoff_markedJanossy_eq (c : Cutoff) (A : ℕ → ℝ≥0∞) :
    markedJanossyExpectation c.rate A =
      ENNReal.ofReal c.logLength * janossyExpectation c.rate A := by
  rw [markedJanossy_eq_rate_mul]
  congr 1
  rw [← c.rate_toReal]
  exact ENNReal.ofReal_coe_nnreal.symm

/-- Two-point factorial size-bias recurrence. -/
lemma poissonPMF_two_succ_size_bias (r : ℝ≥0) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ≥0∞) * ((n + 2 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 2) =
      (r : ℝ≥0∞) * (r : ℝ≥0∞) * poissonPMF r n := by
  calc
    ((n + 1 : ℕ) : ℝ≥0∞) * ((n + 2 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 2) =
        ((n + 1 : ℕ) : ℝ≥0∞) *
          (((n + 2 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 2)) := by ring
    _ = ((n + 1 : ℕ) : ℝ≥0∞) * ((r : ℝ≥0∞) * poissonPMF r (n + 1)) := by
      rw [poissonPMF_succ_size_bias r (n + 1)]
    _ = (r : ℝ≥0∞) *
        (((n + 1 : ℕ) : ℝ≥0∞) * poissonPMF r (n + 1)) := by ring
    _ = (r : ℝ≥0∞) * ((r : ℝ≥0∞) * poissonPMF r n) := by
      rw [poissonPMF_succ_size_bias r n]
    _ = (r : ℝ≥0∞) * (r : ℝ≥0∞) * poissonPMF r n := by ring

/-- Janossy functional with an ordered pair of distinct marked atoms. -/
def twoMarkedJanossyExpectation (r : ℝ≥0) (A : ℕ → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * ((n + 2 : ℕ) : ℝ≥0∞) *
    poissonPMF r (n + 2) * A n

/-- Two-point Campbell--Mecke identity at the count/Janossy level. -/
lemma twoMarkedJanossy_eq_rate_sq_mul (r : ℝ≥0) (A : ℕ → ℝ≥0∞) :
    twoMarkedJanossyExpectation r A =
      (r : ℝ≥0∞) * (r : ℝ≥0∞) * janossyExpectation r A := by
  unfold twoMarkedJanossyExpectation janossyExpectation
  simp_rw [poissonPMF_two_succ_size_bias, mul_assoc]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]

lemma janossyExpectation_one (r : ℝ≥0) :
    janossyExpectation r (fun _ => 1) = 1 := by
  simp [janossyExpectation, PMF.tsum_coe]

lemma markedJanossyExpectation_one (r : ℝ≥0) :
    markedJanossyExpectation r (fun _ => 1) = (r : ℝ≥0∞) := by
  rw [markedJanossy_eq_rate_mul, janossyExpectation_one, mul_one]

/-! ## Spatial Janossy coefficients and the finite Palm formula -/

lemma measurable_atom (c : Cutoff) : Measurable (atom c) := by
  unfold atom
  fun_prop

/-- Law of one atom under normalized logarithmic intensity. -/
def pointLaw (c : Cutoff) : Measure ℝ := unitLaw.map (atom c)

instance pointLaw_isProbability (c : Cutoff) : IsProbabilityMeasure (pointLaw c) := by
  unfold pointLaw
  exact Measure.isProbabilityMeasure_map (measurable_atom c).aemeasurable

lemma pointLaw_normalized (c : Cutoff) : pointLaw c univ = 1 := measure_univ

lemma pointLaw_ae_mem_cutoff (c : Cutoff) :
    ∀ᵐ x ∂pointLaw c, x ∈ Icc c.eps 1 := by
  unfold pointLaw
  apply (ae_map_iff (μ := unitLaw) (p := fun x => x ∈ Icc c.eps 1)
    (measurable_atom c).aemeasurable (by
      show MeasurableSet (Icc c.eps (1 : ℝ))
      exact measurableSet_Icc)).2
  filter_upwards [unitLaw_ae_mem] with u hu
  exact ⟨cutoff_le_atom c hu.2, atom_le_one c hu.1.le⟩

/-- The finite scale-invariant intensity, represented exactly as logarithmic
length times its normalized point law. -/
def scaleIntensity (c : Cutoff) : Measure ℝ :=
  ENNReal.ofReal c.logLength • pointLaw c

lemma scaleIntensity_univ (c : Cutoff) :
    scaleIntensity c univ = ENNReal.ofReal c.logLength := by
  simp [scaleIntensity]

lemma scaleIntensity_ae_mem_cutoff (c : Cutoff) :
    ∀ᵐ x ∂scaleIntensity c, x ∈ Icc c.eps 1 := by
  have h := pointLaw_ae_mem_cutoff c
  exact Measure.ae_smul_measure h (ENNReal.ofReal c.logLength)

/-- Product law of `n` residual atoms. -/
def residualLaw (c : Cutoff) (n : ℕ) : Measure (Fin n → ℝ) :=
  Measure.pi fun _ : Fin n => pointLaw c

instance residualLaw_isProbability (c : Cutoff) (n : ℕ) :
    IsProbabilityMeasure (residualLaw c n) := by
  unfold residualLaw
  infer_instance

lemma residualLaw_normalized (c : Cutoff) (n : ℕ) : residualLaw c n univ = 1 :=
  measure_univ

/-- Spatial coefficient of a nonnegative Palm test: integrate the marked atom
and the `n` residual atoms independently under their normalized laws. -/
def palmCoefficient (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, Phi n x y ∂residualLaw c n ∂pointLaw c

/-- Spatial coefficient for two distinct marked atoms and `n` residual
atoms. -/
def twoPalmCoefficient (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → ℝ → (Fin n → ℝ) → ℝ≥0∞) (n : ℕ) : ℝ≥0∞ :=
  ∫⁻ x, ∫⁻ y, ∫⁻ z, Phi n x y z ∂residualLaw c n ∂pointLaw c ∂pointLaw c

/-- The finite-configuration Campbell functional written in Janossy form. -/
def finiteCampbellFunctional (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  markedJanossyExpectation c.rate (palmCoefficient c Phi)

/-- The Palm side: intensity of the marked atom times the independent
Poisson Janossy law of the residual configuration. -/
def finitePalmFunctional (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal c.logLength * janossyExpectation c.rate (palmCoefficient c Phi)

/-- Exact finite-cutoff Campbell--Mecke/Palm identity.  It is a theorem of the
explicit Janossy construction, not a field of a process structure. -/
lemma finite_campbell_mecke (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → (Fin n → ℝ) → ℝ≥0∞) :
    finiteCampbellFunctional c Phi = finitePalmFunctional c Phi := by
  exact cutoff_markedJanossy_eq c (palmCoefficient c Phi)

/-- The two-point finite Campbell functional. -/
def finiteTwoCampbellFunctional (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → ℝ → (Fin n → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  twoMarkedJanossyExpectation c.rate (twoPalmCoefficient c Phi)

/-- The two-point Palm side. -/
def finiteTwoPalmFunctional (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → ℝ → (Fin n → ℝ) → ℝ≥0∞) : ℝ≥0∞ :=
  ENNReal.ofReal c.logLength * ENNReal.ofReal c.logLength *
    janossyExpectation c.rate (twoPalmCoefficient c Phi)

/-- Exact two-point Campbell--Mecke identity for ordered distinct marks. -/
lemma finite_two_point_campbell_mecke (c : Cutoff)
    (Phi : (n : ℕ) → ℝ → ℝ → (Fin n → ℝ) → ℝ≥0∞) :
    finiteTwoCampbellFunctional c Phi = finiteTwoPalmFunctional c Phi := by
  unfold finiteTwoCampbellFunctional finiteTwoPalmFunctional
  rw [twoMarkedJanossy_eq_rate_sq_mul]
  have hr : (c.rate : ℝ≥0∞) = ENNReal.ofReal c.logLength := by
    rw [← c.rate_toReal]
    exact ENNReal.ofReal_coe_nnreal.symm
  rw [hr]

/-- Taking the test identically one recovers the total intensity. -/
lemma finite_campbell_mass (c : Cutoff) :
    finiteCampbellFunctional c (fun _ _ _ => 1) = ENNReal.ofReal c.logLength := by
  rw [finite_campbell_mecke]
  have hcoeff : palmCoefficient c (fun _ _ _ => 1) = fun _ => 1 := by
    funext n
    simp [palmCoefficient]
  rw [finitePalmFunctional, hcoeff, janossyExpectation_one, mul_one]

/-! ## A cofinal projective construction as the cutoff decreases -/

/-- One logarithmic shell has unit intensity. -/
def shellLaw : Measure Sample :=
  (poissonMeasure (1 : ℝ≥0)).prod coordinateLaw

instance shellLaw_isProbability : IsProbabilityMeasure shellLaw := by
  unfold shellLaw
  infer_instance

/-- Independent configurations in all logarithmic shells. -/
abbrev GlobalSample := ℕ → Sample

def globalLaw : Measure GlobalSample :=
  Measure.infinitePi fun _ : ℕ => shellLaw

instance globalLaw_isProbability : IsProbabilityMeasure globalLaw := by
  unfold globalLaw
  infer_instance

lemma globalLaw_normalized : globalLaw univ = 1 := measure_univ

lemma globalLaw_map_shell (k : ℕ) :
    globalLaw.map (Function.eval k) = shellLaw := by
  exact (measurePreserving_eval_infinitePi (fun _ : ℕ => shellLaw) k).map_eq

/-- Raw restriction to the first `K` shells.  Each shell still carries its
Poisson count and iid coordinate supply. -/
def rawRestriction (K : ℕ) (omega : GlobalSample) : Fin K → Sample :=
  fun k => omega k.val

lemma measurable_rawRestriction (K : ℕ) : Measurable (rawRestriction K) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply k.val

def rawRestrictionLaw (K : ℕ) : Measure (Fin K → Sample) :=
  globalLaw.map (rawRestriction K)

instance rawRestrictionLaw_isProbability (K : ℕ) :
    IsProbabilityMeasure (rawRestrictionLaw K) := by
  unfold rawRestrictionLaw
  exact Measure.isProbabilityMeasure_map (measurable_rawRestriction K).aemeasurable

lemma rawRestrictionLaw_normalized (K : ℕ) : rawRestrictionLaw K univ = 1 :=
  measure_univ

/-- Restrict an `L`-shell sample to its first `K` shells. -/
def restrictShells {alpha : Type*} {K L : ℕ} (hKL : K ≤ L)
    (omega : Fin L → alpha) : Fin K → alpha :=
  fun k => omega ⟨k.val, lt_of_lt_of_le k.isLt hKL⟩

lemma measurable_restrictShells {alpha : Type*} [MeasurableSpace alpha]
    {K L : ℕ} (hKL : K ≤ L) :
    Measurable (restrictShells (alpha := alpha) hKL) := by
  apply measurable_pi_lambda
  intro k
  exact measurable_pi_apply (⟨k.val, lt_of_lt_of_le k.isLt hKL⟩ : Fin L)

lemma restrictShells_rawRestriction {K L : ℕ} (hKL : K ≤ L)
    (omega : GlobalSample) :
    restrictShells hKL (rawRestriction L omega) = rawRestriction K omega := by
  rfl

/-- The finite restriction laws form an exact projective family. -/
lemma rawRestrictionLaw_projective {K L : ℕ} (hKL : K ≤ L) :
    (rawRestrictionLaw L).map (restrictShells (alpha := Sample) hKL) =
      rawRestrictionLaw K := by
  unfold rawRestrictionLaw
  rw [Measure.map_map (measurable_restrictShells hKL)
    (measurable_rawRestriction L)]
  congr 1

/-- Map a coordinate in shell `k` back to the physical scale. -/
def shellAtom (k : ℕ) (u : ℝ) : ℝ := exp (-((k : ℝ) + u))

lemma shellAtom_pos (k : ℕ) (u : ℝ) : 0 < shellAtom k u := exp_pos _

lemma shellAtom_bounds (k : ℕ) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    exp (-((k : ℝ) + 1)) ≤ shellAtom k u ∧ shellAtom k u ≤ exp (-(k : ℝ)) := by
  constructor <;> rw [shellAtom, exp_le_exp] <;> linarith [hu.1, hu.2]

/-- Concrete finite atom list in one logarithmic shell. -/
def activeShellAtoms (k : ℕ) (omega : Sample) : List ℝ :=
  List.ofFn fun i : Fin omega.1 => shellAtom k (omega.2 i.val)

@[simp] lemma activeShellAtoms_length (k : ℕ) (omega : Sample) :
    (activeShellAtoms k omega).length = omega.1 := by
  simp [activeShellAtoms]

/-- The actual finite configurations in the first `K` shells. -/
def finiteShellConfiguration (K : ℕ) (omega : GlobalSample) : Fin K → List ℝ :=
  fun k => activeShellAtoms k.val (omega k.val)

/-- Projective compatibility holds pointwise, before passing to laws. -/
lemma finiteShellConfiguration_projective {K L : ℕ} (hKL : K ≤ L)
    (omega : GlobalSample) :
    restrictShells hKL (fun k : Fin L => activeShellAtoms k.val (omega k.val)) =
      finiteShellConfiguration K omega := by
  rfl

/-- A cofinal cutoff sequence, with shell indices `0,...,K`. -/
def cofinalCutoff (K : ℕ) : Cutoff where
  eps := exp (-((K : ℝ) + 1))
  eps_pos := exp_pos _
  eps_lt_one := by
    rw [exp_lt_one_iff]
    have hK : 0 < (K : ℝ) + 1 := by positivity
    linarith

@[simp] lemma cofinalCutoff_eps (K : ℕ) :
    (cofinalCutoff K).eps = exp (-((K : ℝ) + 1)) := rfl

lemma cofinalCutoff_logLength (K : ℕ) :
    (cofinalCutoff K).logLength = (K : ℝ) + 1 := by
  rw [Cutoff.logLength, cofinalCutoff_eps, log_exp]
  ring

lemma tendsto_cofinalCutoff_zero :
    Tendsto (fun K : ℕ => (cofinalCutoff K).eps) atTop (nhds 0) := by
  have hnat : Tendsto (fun K : ℕ => (K : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1
      (tendsto_natCast_atTop_atTop (R := ℝ))
  exact Real.tendsto_exp_neg_atTop_nhds_zero.comp hnat

/-! ## Compatible window-conditioned restrictions -/

/-- One active atom, expressed as an `ENNReal` summand. -/
def shellMassTerm (k i : ℕ) (omega : Sample) : ℝ≥0∞ :=
  if i < omega.1 then ENNReal.ofReal (shellAtom k (omega.2 i)) else 0

lemma measurable_shellAtom (k : ℕ) : Measurable (shellAtom k) := by
  unfold shellAtom
  fun_prop

lemma measurable_shellMassTerm (k i : ℕ) : Measurable (shellMassTerm k i) := by
  unfold shellMassTerm
  apply Measurable.ite
  · exact measurableSet_lt measurable_const measurable_fst
  · apply ENNReal.measurable_ofReal.comp
    exact (measurable_shellAtom k).comp ((measurable_pi_apply i).comp measurable_snd)
  · exact measurable_const

/-- Total mass in one shell.  Only finitely many summands are nonzero on
every sample, although the `tsum` representation makes measurability direct. -/
def shellMass (k : ℕ) (omega : Sample) : ℝ≥0∞ :=
  ∑' i : ℕ, shellMassTerm k i omega

lemma measurable_shellMass (k : ℕ) : Measurable (shellMass k) := by
  exact Measurable.ennreal_tsum fun i => measurable_shellMassTerm k i

/-- Total mass of the full projective shell configuration. -/
def globalTotalMass (omega : GlobalSample) : ℝ≥0∞ :=
  ∑' k : ℕ, shellMass k (omega k)

lemma measurable_globalTotalMass : Measurable globalTotalMass := by
  apply Measurable.ennreal_tsum
  intro k
  exact (measurable_shellMass k).comp (measurable_pi_apply k)

/-- A positive-width conditioning window around a target mass.  This is the
honest event used below; no conditioning on a probability-zero singleton is
silently chosen. -/
def massWindow (u delta : ℝ≥0∞) : Set GlobalSample :=
  {omega | u - delta < globalTotalMass omega ∧ globalTotalMass omega < u + delta}

lemma measurableSet_massWindow (u delta : ℝ≥0∞) : MeasurableSet (massWindow u delta) := by
  unfold massWindow
  exact (measurableSet_lt measurable_const measurable_globalTotalMass).inter
    (measurableSet_lt measurable_globalTotalMass measurable_const)

/-- Global law conditioned on a nonzero-width total-mass window. -/
def windowBridge (u delta : ℝ≥0∞) : Measure GlobalSample :=
  ProbabilityTheory.cond globalLaw (massWindow u delta)

lemma windowBridge_normalized {u delta : ℝ≥0∞}
    (hpos : globalLaw (massWindow u delta) ≠ 0) :
    windowBridge u delta univ = 1 := by
  letI : IsProbabilityMeasure (windowBridge u delta) := by
    unfold windowBridge
    exact cond_isProbabilityMeasure hpos
  exact measure_univ

/-- The `K`-shell marginal of the same window-conditioned global law. -/
def windowRestrictionLaw (u delta : ℝ≥0∞) (K : ℕ) : Measure (Fin K → Sample) :=
  (windowBridge u delta).map (rawRestriction K)

lemma windowRestrictionLaw_projective (u delta : ℝ≥0∞) {K L : ℕ} (hKL : K ≤ L) :
    (windowRestrictionLaw u delta L).map (restrictShells (alpha := Sample) hKL) =
      windowRestrictionLaw u delta K := by
  unfold windowRestrictionLaw
  rw [Measure.map_map (measurable_restrictShells hKL) (measurable_rawRestriction L)]
  congr 1

lemma windowRestrictionLaw_normalized {u delta : ℝ≥0∞}
    (hpos : globalLaw (massWindow u delta) ≠ 0) (K : ℕ) :
    windowRestrictionLaw u delta K univ = 1 := by
  have hbridge : windowBridge u delta univ = 1 := windowBridge_normalized hpos
  rw [windowRestrictionLaw, Measure.map_apply_of_aemeasurable
    (measurable_rawRestriction K).aemeasurable MeasurableSet.univ]
  exact hbridge

/-!
The family `windowRestrictionLaw u delta K` is therefore an actual compatible
projective conditioned family for every positive-width window having nonzero
probability, and the physical cutoff tends to zero by
`tendsto_cofinalCutoff_zero`.  The remaining step needed for the paper is not
hidden here: one must prove that these laws have a canonical limit as
`delta ↓ 0`, identify it with the Dickman-density bridge, and establish the
density-weighted one- and two-point Palm disintegrations.  Those statements are
not assumed in the present file.
-/

end Erdos390.Full.ConditionedPoisson
