import Erdos390.Full.FiniteGraphQuotientInverse
import Erdos390.Full.StableInverse

/-!
# Stable inversion on the actual finite gauge

The graph edge geometry proved at the continuum level is turned here into a
linear equivalence on the *actual* weighted gauge.  Its inverse and inverse
bound are conclusions of the maximum/minimum theorem.  A sufficiently small
operator error is then transferred by `StableInverse`; the perturbed inverse
is never assumed.
-/

open scoped BigOperators

noncomputable section

namespace Erdos390.Full.FiniteGraphStableInverse

open FiniteGraphQuotientInverse

variable {Band : Type*} [Fintype Band]

def gaugeFunctional (omega : Band → ℝ) :
    (Band → ℝ) →ₗ[ℝ] ℝ where
  toFun q := ∑ i, omega i * q i
  map_add' q r := by
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  map_smul' c q := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    calc
      (∑ i, omega i * (c * q i)) =
          ∑ i, c * (omega i * q i) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = ∑ i, (omega i * q i) * c := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, omega i * q i) * c :=
        (Finset.sum_mul Finset.univ (fun i => omega i * q i) c).symm
      _ = c * ∑ i, omega i * q i := by ring

def gaugeSubmodule (omega : Band → ℝ) : Submodule ℝ (Band → ℝ) :=
  LinearMap.ker (gaugeFunctional omega)

abbrev GaugeSpace (omega : Band → ℝ) := gaugeSubmodule omega

lemma mem_gaugeSubmodule_iff (omega q : Band → ℝ) :
    q ∈ gaugeSubmodule omega ↔ ∑ i, omega i * q i = 0 := by
  rfl

lemma weighted_sum_meanProjection
    (omega x : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    ∑ i, omega i * meanProjection omega x i = 0 := by
  unfold meanProjection weightedMean weightTotal
  calc
    (∑ i, omega i *
        (x i - (∑ j, omega j * x j) / ∑ j, omega j)) =
        (∑ i, omega i * x i) -
          (∑ i, omega i) *
            ((∑ j, omega j * x j) / ∑ j, omega j) := by
      calc
        (∑ i, omega i *
            (x i - (∑ j, omega j * x j) / ∑ j, omega j)) =
            (∑ i, omega i * x i) -
              ∑ i, omega i *
                ((∑ j, omega j * x j) / ∑ j, omega j) := by
          rw [← Finset.sum_sub_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          ring
        _ = _ := by
          rw [← Finset.sum_mul]
    _ = 0 := by
      field_simp [hTotal]
      ring

lemma graphOperator_add (edge : Band → Band → ℝ)
    (q r : Band → ℝ) (i : Band) :
    graphOperator edge (q + r) i =
      graphOperator edge q i + graphOperator edge r i := by
  unfold graphOperator
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.add_apply]
  ring

lemma graphOperator_smul (edge : Band → Band → ℝ)
    (c : ℝ) (q : Band → ℝ) (i : Band) :
    graphOperator edge (c • q) i = c * graphOperator edge q i := by
  unfold graphOperator
  calc
    (∑ j, edge i j * ((c • q) i - (c • q) j)) =
        ∑ j, c * (edge i j * (q i - q j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = ∑ j, (edge i j * (q i - q j)) * c := by
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = (∑ j, edge i j * (q i - q j)) * c :=
      (Finset.sum_mul Finset.univ
        (fun j => edge i j * (q i - q j)) c).symm
    _ = c * ∑ j, edge i j * (q i - q j) := by ring

lemma weightedMean_add (omega x y : Band → ℝ) :
    weightedMean omega (x + y) =
      weightedMean omega x + weightedMean omega y := by
  unfold weightedMean weightTotal
  have hsum :
      (∑ i, omega i * (x + y) i) =
        (∑ i, omega i * x i) + ∑ i, omega i * y i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.add_apply]
    ring
  rw [hsum]
  ring

lemma weightedMean_smul (omega : Band → ℝ) (c : ℝ) (x : Band → ℝ) :
    weightedMean omega (c • x) = c * weightedMean omega x := by
  unfold weightedMean weightTotal
  have hsum :
      (∑ i, omega i * (c • x) i) =
        c * ∑ i, omega i * x i := by
    calc
      (∑ i, omega i * (c • x) i) =
          ∑ i, c * (omega i * x i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [Pi.smul_apply, smul_eq_mul]
        ring
      _ = ∑ i, (omega i * x i) * c := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = (∑ i, omega i * x i) * c :=
        (Finset.sum_mul Finset.univ (fun i => omega i * x i) c).symm
      _ = c * ∑ i, omega i * x i := by ring
  rw [hsum]
  ring

lemma meanProjection_add (omega x y : Band → ℝ) (i : Band) :
    meanProjection omega (x + y) i =
      meanProjection omega x i + meanProjection omega y i := by
  unfold meanProjection
  rw [weightedMean_add]
  simp only [Pi.add_apply]
  ring

lemma meanProjection_smul (omega : Band → ℝ) (c : ℝ)
    (x : Band → ℝ) (i : Band) :
    meanProjection omega (c • x) i =
      c * meanProjection omega x i := by
  unfold meanProjection
  rw [weightedMean_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

def projectedGraphLinearMap
    (edge : Band → Band → ℝ) (omega : Band → ℝ)
    (hTotal : (∑ i, omega i) ≠ 0) :
    GaugeSpace omega →ₗ[ℝ] GaugeSpace omega where
  toFun q :=
    ⟨meanProjection omega (graphOperator edge q.1),
      weighted_sum_meanProjection omega (graphOperator edge q.1) hTotal⟩
  map_add' q r := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (graphOperator edge ((q : Band → ℝ) + (r : Band → ℝ))) i =
      meanProjection omega (graphOperator edge (q : Band → ℝ)) i +
        meanProjection omega (graphOperator edge (r : Band → ℝ)) i
    rw [show graphOperator edge
        ((q : Band → ℝ) + (r : Band → ℝ)) =
        graphOperator edge (q : Band → ℝ) +
          graphOperator edge (r : Band → ℝ) by
      funext j
      exact graphOperator_add edge (q : Band → ℝ) (r : Band → ℝ) j]
    exact meanProjection_add omega _ _ i
  map_smul' c q := by
    apply Subtype.ext
    funext i
    change meanProjection omega
        (graphOperator edge (c • (q : Band → ℝ))) i =
      c * meanProjection omega (graphOperator edge (q : Band → ℝ)) i
    rw [show graphOperator edge (c • (q : Band → ℝ)) =
        c • graphOperator edge (q : Band → ℝ) by
      funext j
      exact graphOperator_smul edge c (q : Band → ℝ) j]
    exact meanProjection_smul omega c _ i

/-- Edge domination proves injectivity on the actual weighted gauge. -/
theorem projectedGraphLinearMap_injective
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    Function.Injective
      (projectedGraphLinearMap edge omega (ne_of_gt homegaTotal)) := by
  intro q r hqr
  have hzero : projectedGraphLinearMap edge omega (ne_of_gt homegaTotal)
      (q - r) = 0 := by
    rw [map_sub, hqr, sub_self]
  have hgauge : ∑ i, omega i * ((q - r : GaugeSpace omega).1 i) = 0 :=
    (q - r : GaugeSpace omega).2
  have hprojected (i : Band) :
      |meanProjection omega
        (graphOperator edge (q - r : GaugeSpace omega).1) i| ≤ 0 := by
    have happ := congrArg
      (fun x : GaugeSpace omega => (x : Band → ℝ) i) hzero
    have habs :
        |meanProjection omega
          (graphOperator edge (q - r : GaugeSpace omega).1) i| = 0 := by
      simpa only [projectedGraphLinearMap, Submodule.coe_zero,
        Pi.zero_apply, abs_zero] using congrArg abs happ
    exact habs.le
  have hbound := abs_le_of_gauge_projectedGraph_bound
    edge anchor omega (q - r : GaugeSpace omega).1
    (kappa := kappa) (G := 0) hedge hdom hkappa hanchorTotal
    homega homegaTotal hgauge hprojected
  have hfun : (q - r : GaugeSpace omega).1 = 0 := by
    funext i
    have hi := hbound i
    simp only [zero_div, mul_zero, abs_nonpos_iff] at hi
    exact hi
  apply sub_eq_zero.mp
  exact Subtype.ext hfun

/-- The reference graph equivalence.  It is constructed from injectivity in
finite dimension, not stored as mesh data. -/
def referenceGraphEquiv
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    GaugeSpace omega ≃L[ℝ] GaugeSpace omega :=
  (LinearEquiv.ofInjectiveEndo
    (projectedGraphLinearMap edge omega (ne_of_gt homegaTotal))
    (projectedGraphLinearMap_injective edge anchor omega hedge hdom
      hkappa hanchorTotal homega homegaTotal)).toContinuousLinearEquiv

def referenceGraphCLM
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    GaugeSpace omega →L[ℝ] GaugeSpace omega :=
  (referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal).toContinuousLinearMap

def referenceGraphInvCLM
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i) :
    GaugeSpace omega →L[ℝ] GaugeSpace omega :=
  (referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal).symm.toContinuousLinearMap

theorem referenceGraphInvCLM_left
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (q : GaugeSpace omega) :
    referenceGraphInvCLM edge anchor omega hedge hdom hkappa
      hanchorTotal homega homegaTotal
      (referenceGraphCLM edge anchor omega hedge hdom hkappa
        hanchorTotal homega homegaTotal q) = q := by
  exact (referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal).symm_apply_apply q

/-- Quantitative inverse bound derived from the graph maximum principle. -/
theorem referenceGraphInvCLM_bound
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (v : GaugeSpace omega) :
    ‖referenceGraphInvCLM edge anchor omega hedge hdom hkappa
        hanchorTotal homega homegaTotal v‖ ≤
      (4 / (kappa * ∑ j, anchor j)) * ‖v‖ := by
  let e := referenceGraphEquiv edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal
  let q : GaugeSpace omega := e.symm v
  have happ : e q = v := e.apply_symm_apply v
  have hgauge : ∑ i, omega i * (q : Band → ℝ) i = 0 := q.2
  have hprojected (i : Band) :
      |meanProjection omega (graphOperator edge (q : Band → ℝ)) i| ≤ ‖v‖ := by
    have hcoord :
        meanProjection omega (graphOperator edge (q : Band → ℝ)) i =
          (v : Band → ℝ) i := by
      have hi := congrArg (fun x : GaugeSpace omega => (x : Band → ℝ) i) happ
      simpa only [e, referenceGraphEquiv, projectedGraphLinearMap] using hi
    rw [hcoord, ← Real.norm_eq_abs]
    exact norm_le_pi_norm (v : Band → ℝ) i
  have hpoint := abs_le_of_gauge_projectedGraph_bound
    edge anchor omega (q : Band → ℝ)
    (kappa := kappa) (G := ‖v‖) hedge hdom hkappa hanchorTotal
    homega homegaTotal hgauge hprojected
  change ‖(q : Band → ℝ)‖ ≤
    (4 / (kappa * ∑ j, anchor j)) * ‖v‖
  have hconstant : 0 ≤ (4 / (kappa * ∑ j, anchor j)) * ‖v‖ := by
    positivity
  rw [pi_norm_le_iff_of_nonneg hconstant]
  intro i
  rw [Real.norm_eq_abs]
  calc
    |(q : Band → ℝ) i| ≤
        4 * ‖v‖ / (kappa * ∑ j, anchor j) := hpoint i
    _ = (4 / (kappa * ∑ j, anchor j)) * ‖v‖ := by ring

/-- Stable inversion of an actual arithmetic-gauge operator from a proved
graph reference and an explicit operator error. -/
theorem exists_actualGaugeEquiv_of_graph_error
    [Nonempty Band]
    (edge : Band → Band → ℝ) (anchor omega : Band → ℝ)
    {kappa delta : ℝ}
    (hedge : ∀ i j, 0 ≤ edge i j)
    (hdom : ∀ i j, kappa * anchor j ≤ edge i j)
    (hkappa : 0 < kappa)
    (hanchorTotal : 0 < ∑ j, anchor j)
    (homega : ∀ i, 0 ≤ omega i)
    (homegaTotal : 0 < ∑ i, omega i)
    (actual : GaugeSpace omega →L[ℝ] GaugeSpace omega)
    (hsmall : (4 / (kappa * ∑ j, anchor j)) * delta < 1)
    (herror : ∀ q,
      ‖(actual - referenceGraphCLM edge anchor omega hedge hdom hkappa
        hanchorTotal homega homegaTotal) q‖ ≤ delta * ‖q‖) :
    ∃ actualEquiv : GaugeSpace omega ≃L[ℝ] GaugeSpace omega,
      (∀ q, actualEquiv q = actual q) ∧
      ∀ v, ‖actualEquiv.symm v‖ ≤
        ((4 / (kappa * ∑ j, anchor j)) /
          (1 - (4 / (kappa * ∑ j, anchor j)) * delta)) * ‖v‖ := by
  let reference := referenceGraphCLM edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal
  let referenceInv := referenceGraphInvCLM edge anchor omega hedge hdom hkappa
    hanchorTotal homega homegaTotal
  let E := actual - reference
  let C := 4 / (kappa * ∑ j, anchor j)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hleft : ∀ q, referenceInv (reference q) = q := by
    intro q
    exact referenceGraphInvCLM_left edge anchor omega hedge hdom hkappa
      hanchorTotal homega homegaTotal q
  have hinv : ∀ v, ‖referenceInv v‖ ≤ C * ‖v‖ := by
    intro v
    exact referenceGraphInvCLM_bound edge anchor omega hedge hdom hkappa
      hanchorTotal homega homegaTotal v
  have hE : ∀ q, ‖E q‖ ≤ delta * ‖q‖ := by
    simpa only [E, reference] using herror
  let actualEquiv := StableInverse.perturbedEquiv
    reference referenceInv E C delta hC hsmall hleft hinv hE
  refine ⟨actualEquiv, ?_, ?_⟩
  · intro q
    rw [show actualEquiv q = (reference + E) q by
      exact StableInverse.perturbedEquiv_apply
        reference referenceInv E C delta hC hsmall hleft hinv hE q]
    simp only [E, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply]
    abel
  · intro v
    exact StableInverse.perturbed_inverse_bound
      reference referenceInv E C delta hC hsmall hleft hinv hE v

end Erdos390.Full.FiniteGraphStableInverse
