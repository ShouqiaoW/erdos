import Erdos390.Full.PoissonSelfSimilarity
import Mathlib.Probability.Independence.CharacteristicFunction

/-!
# Characteristic-function uniqueness for the Poisson--Dickman law

This file turns the extended-real shell decomposition into an honest
real-valued convolution identity.  It then proves a contractive uniqueness
principle: two probability laws with the same finite-prefix factor and a
tail scaled by `c_K -> 0` are equal.  The proof uses characteristic functions,
their continuity at zero, and their injectivity; no moment-determinacy or
unproved tightness assertion is used.

For the actual scale-invariant shell construction we prove the exact
characteristic-function recursion at every integer logarithmic cutoff.  Thus
identifying a proposed Dickman density is reduced to verifying that it obeys
the same finite-prefix recursion; uniqueness of the resulting law is no
longer an additional probabilistic gap.
-/

open Filter Set
open scoped ENNReal NNReal BigOperators
noncomputable section
open MeasureTheory ProbabilityTheory Real
namespace Erdos390.Full.PoissonLawUniqueness

open ConditionedPoisson PoissonMass PoissonSelfSimilarity

lemma continuous_charFun_finite (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Continuous (charFun mu) := by
  have hbase : Continuous
      (VectorFourier.fourierIntegral probChar mu (innerₗ ℝ) (1 : ℝ → ℂ)) := by
    apply VectorFourier.fourierIntegral_continuous
    · exact continuous_probChar
    · exact continuous_inner
    · exact integrable_const 1
  have hneg := hbase.comp continuous_neg
  convert hneg using 1
  funext t
  rw [Function.comp_apply, charFun_eq_fourierIntegral]

theorem common_contract_charFun_unique
    (mu nu : Measure ℝ) [IsProbabilityMeasure mu] [IsProbabilityMeasure nu]
    (c : ℕ → ℝ) (alpha : ℕ → Measure ℝ)
    (halpha : ∀ K, IsProbabilityMeasure (alpha K))
    (hc : Tendsto c atTop (nhds 0))
    (hmu : ∀ K t, charFun mu t =
      charFun (alpha K) t * charFun mu (c K * t))
    (hnu : ∀ K t, charFun nu t =
      charFun (alpha K) t * charFun nu (c K * t)) :
    mu = nu := by
  apply Measure.ext_of_charFun
  funext t
  have hct : Tendsto (fun K => c K * t) atTop (nhds 0) := by
    simpa using hc.mul_const t
  have hmulim : Tendsto (fun K => charFun mu (c K * t)) atTop (nhds 1) := by
    have h := (continuous_charFun_finite mu).continuousAt.tendsto.comp hct
    simpa using h
  have hnulim : Tendsto (fun K => charFun nu (c K * t)) atTop (nhds 1) := by
    have h := (continuous_charFun_finite nu).continuousAt.tendsto.comp hct
    simpa using h
  have hdiff : Tendsto
      (fun K => charFun mu (c K * t) - charFun nu (c K * t))
      atTop (nhds 0) := by
    simpa using hmulim.sub hnulim
  have hprod : Tendsto
      (fun K => charFun (alpha K) t *
        (charFun mu (c K * t) - charFun nu (c K * t)))
      atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero (fun _K => norm_nonneg _) (fun K => ?_)
      (tendsto_zero_iff_norm_tendsto_zero.mp hdiff)
    letI : IsProbabilityMeasure (alpha K) := halpha K
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (norm_charFun_le_one t)
      (norm_nonneg _)).trans_eq (one_mul _)
  have heq (K : ℕ) :
      charFun mu t - charFun nu t =
        charFun (alpha K) t *
          (charFun mu (c K * t) - charFun nu (c K * t)) := by
    rw [hmu K t, hnu K t]
    ring
  have hconst : Tendsto (fun _K : ℕ => charFun mu t - charFun nu t)
      atTop (nhds 0) := by
    apply hprod.congr'
    exact Filter.Eventually.of_forall fun K => (heq K).symm
  have hsame : charFun mu t - charFun nu t = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  exact sub_eq_zero.mp hsame

/-! ## The real-valued law of the actual shell construction -/

def globalTotalReal (omega : GlobalSample) : ℝ :=
  (globalTotalMass omega).toReal

def prefixMassReal (K : ℕ) (omega : GlobalSample) : ℝ :=
  (prefixMass K omega).toReal

def tailMassReal (K : ℕ) (omega : GlobalSample) : ℝ :=
  (tailMass K omega).toReal

lemma measurable_globalTotalReal : Measurable globalTotalReal :=
  ENNReal.measurable_toReal.comp measurable_globalTotalMass

lemma measurable_prefixMassReal (K : ℕ) : Measurable (prefixMassReal K) :=
  ENNReal.measurable_toReal.comp (measurable_prefixMass K)

lemma measurable_tailMassReal (K : ℕ) : Measurable (tailMassReal K) :=
  ENNReal.measurable_toReal.comp (measurable_tailMass K)

lemma globalTotalReal_ae_add (K : ℕ) :
    ∀ᵐ omega ∂globalLaw,
      globalTotalReal omega = prefixMassReal K omega + tailMassReal K omega := by
  filter_upwards [globalTotalMass_ae_lt_top] with omega hfinite
  have hglobal : globalTotalMass omega ≠ ∞ := ne_of_lt hfinite
  have hprefix : prefixMass K omega ≠ ∞ := by
    intro hp
    have hsplit := prefixMass_add_tailMass K omega
    rw [hp, top_add] at hsplit
    exact hglobal hsplit.symm
  have htail : tailMass K omega ≠ ∞ := by
    intro ht
    have hsplit := prefixMass_add_tailMass K omega
    rw [ht, add_top] at hsplit
    exact hglobal hsplit.symm
  unfold globalTotalReal prefixMassReal tailMassReal
  rw [← prefixMass_add_tailMass K omega, ENNReal.toReal_add hprefix htail]

lemma prefixMassReal_indep_tailMassReal (K : ℕ) :
    IndepFun (prefixMassReal K) (tailMassReal K) globalLaw := by
  have h := (prefixMass_indep_tailMass K).comp
    ENNReal.measurable_toReal ENNReal.measurable_toReal
  simpa only [prefixMassReal, tailMassReal, Function.comp_def] using h

lemma tailMassReal_eq_scaled (K : ℕ) (omega : GlobalSample) :
    tailMassReal K omega =
      exp (-(K : ℝ)) * globalTotalReal (shiftShells K omega) := by
  unfold tailMassReal globalTotalReal
  rw [tailMass_eq_scaled, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (exp_pos (-(K : ℝ))).le]

lemma tailMassReal_map_scaled (K : ℕ) :
    globalLaw.map (tailMassReal K) =
      (globalLaw.map globalTotalReal).map (exp (-(K : ℝ)) * ·) := by
  have htail : tailMassReal K =
      (fun omega => exp (-(K : ℝ)) * globalTotalReal omega) ∘ shiftShells K := by
    funext omega
    exact tailMassReal_eq_scaled K omega
  rw [htail, ← Measure.map_map]
  · rw [shiftShells_map, Measure.map_map]
    · rfl
    · fun_prop
    · exact measurable_globalTotalReal
  · exact measurable_const.mul measurable_globalTotalReal
  · exact measurable_shiftShells K

instance globalTotalRealLaw_isProbability :
    IsProbabilityMeasure (globalLaw.map globalTotalReal) :=
  Measure.isProbabilityMeasure_map measurable_globalTotalReal.aemeasurable

instance prefixMassRealLaw_isProbability (K : ℕ) :
    IsProbabilityMeasure (globalLaw.map (prefixMassReal K)) :=
  Measure.isProbabilityMeasure_map (measurable_prefixMassReal K).aemeasurable

lemma globalTotalReal_charFun_contract (K : ℕ) (t : ℝ) :
    charFun (globalLaw.map globalTotalReal) t =
      charFun (globalLaw.map (prefixMassReal K)) t *
        charFun (globalLaw.map globalTotalReal) (exp (-(K : ℝ)) * t) := by
  have hchar := (prefixMassReal_indep_tailMassReal K).charFun_map_add_eq_mul
    (measurable_prefixMassReal K).aemeasurable
    (measurable_tailMassReal K).aemeasurable
  have hmap : globalLaw.map globalTotalReal =
      globalLaw.map (prefixMassReal K + tailMassReal K) :=
    Measure.map_congr (globalTotalReal_ae_add K)
  have hcharAt := congrFun hchar t
  rw [← hmap] at hcharAt
  rw [tailMassReal_map_scaled K] at hcharAt
  simp only [Pi.mul_apply] at hcharAt
  rw [charFun_map_mul] at hcharAt
  exact hcharAt

theorem eq_globalTotalRealLaw_of_prefix_contract
    (nu : Measure ℝ) [IsProbabilityMeasure nu]
    (hnu : ∀ K t, charFun nu t =
      charFun (globalLaw.map (prefixMassReal K)) t *
        charFun nu (exp (-(K : ℝ)) * t)) :
    nu = globalLaw.map globalTotalReal := by
  have hc : Tendsto (fun K : ℕ => exp (-(K : ℝ))) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  apply (common_contract_charFun_unique
    (globalLaw.map globalTotalReal) nu
    (fun K : ℕ => exp (-(K : ℝ)))
    (fun K => globalLaw.map (prefixMassReal K))
    (fun K => prefixMassRealLaw_isProbability K)
    hc globalTotalReal_charFun_contract hnu).symm

end Erdos390.Full.PoissonLawUniqueness
