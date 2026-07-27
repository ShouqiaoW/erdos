import Erdos536.AlternativeBandParameters
import Erdos536.AlternativeBandOneCube
import Erdos536.FiveStateRooted
import Erdos536.PrimeBandTimeChange
import Erdos536.UniformLocalPrimeBand

/-!
# Quadratically parametrized prime bands

For analytic scale `T²`, the lower prime cutoff is the polynomial `T⁶`.
Thus the normalized depth horizon is asymptotic to `log (T²)`, while the
sum of local coupling errors `O(∑ p⁻²)` is `O(T⁻⁶)`, smaller than the
`T⁻⁴` scale of the two-anchor first moment.
-/

namespace Erdos536

open PrimeSums
open Filter Topology

noncomputable section

/-- Polynomial lower cutoff used by the corrected quadratic band. -/
def quadraticLowerCutoff (T : ℕ) : ℕ := T ^ 6

/-- Prime band `T⁶ < p ≤ exp(a*T²)`. -/
def quadraticPrimeBand (T : ℕ) (a : ℝ) : Finset ℕ :=
  primesUpTo (expEndpoint a (T ^ 2)) \
    primesUpTo (quadraticLowerCutoff T)

@[simp]
theorem mem_quadraticPrimeBand {T p : ℕ} {a : ℝ} :
    p ∈ quadraticPrimeBand T a ↔
      p.Prime ∧ quadraticLowerCutoff T < p ∧
        p ≤ expEndpoint a (T ^ 2) := by
  constructor
  · intro hp
    have hpDiff := Finset.mem_sdiff.mp hp
    have hpUpper :
        p ≤ expEndpoint a (T ^ 2) ∧ p.Prime := by
      simpa [quadraticPrimeBand, primesUpTo] using hpDiff.1
    have hpNotLower : ¬p ≤ quadraticLowerCutoff T := by
      intro hpLower
      apply hpDiff.2
      simp [primesUpTo, hpUpper.2, hpLower]
    exact ⟨hpUpper.2, lt_of_not_ge hpNotLower, hpUpper.1⟩
  · rintro ⟨hpPrime, hpLower, hpUpper⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simp [primesUpTo, hpPrime, hpUpper]
    · intro hp
      have hpLe : p ≤ quadraticLowerCutoff T := by
        simpa [primesUpTo, hpPrime] using hp
      omega

theorem quadraticPrimeBand_prime (T : ℕ) (a : ℝ) :
    IsPrimeSupport (quadraticPrimeBand T a) := by
  intro p hp
  exact (mem_quadraticPrimeBand.mp hp).1

theorem nat_le_quadraticLowerCutoff (T : ℕ) :
    T ≤ quadraticLowerCutoff T := by
  unfold quadraticLowerCutoff
  exact Nat.le_pow (by norm_num)

theorem quadraticScale_le_lowerCutoff
    {T : ℕ} (hT : 1 ≤ T) :
    T ^ 2 ≤ quadraticLowerCutoff T := by
  unfold quadraticLowerCutoff
  exact pow_le_pow_right₀ hT (by omega)

/-- Every fixed positive normalized endpoint eventually lies above the
polynomial lower cutoff. -/
theorem eventually_quadraticLowerCutoff_le_expEndpoint
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ T : ℕ in Filter.atTop,
      quadraticLowerCutoff T ≤ expEndpoint r (T ^ 2) := by
  have hpowNat :
      Tendsto (fun T : ℕ => T ^ 2)
        Filter.atTop Filter.atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpowReal :
      Tendsto (fun T : ℕ => ((T ^ 2 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  have hgrowth :
      Tendsto
        (fun T : ℕ =>
          Real.exp
              (r * ((T ^ 2 : ℕ) : ℝ)) /
            (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℝ)))
        Filter.atTop Filter.atTop := by
    have h :=
      tendsto_exp_mul_div_rpow_atTop 3 r hr
    exact h.comp hpowReal
  filter_upwards [
      hgrowth.eventually (eventually_ge_atTop 1),
      eventually_gt_atTop 0] with T hratio hT
  have hNR : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := by
    positivity
  have hden :
      0 < (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℝ)) :=
    Real.rpow_pos_of_pos hNR _
  have hmul := (le_div_iff₀ hden).mp hratio
  have hrpow :
      (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℝ)) =
        (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℕ)) := by
    exact Real.rpow_natCast _ 3
  rw [hrpow] at hmul
  have hreal :
      (quadraticLowerCutoff T : ℝ) ≤
        Real.exp (((T ^ 2 : ℕ) : ℝ) * r) := by
    unfold quadraticLowerCutoff
    norm_num [Nat.cast_pow] at hmul ⊢
    calc
      (T : ℝ) ^ 6 =
          (((T : ℝ) ^ 2) ^ 3) := by ring
      _ ≤ Real.exp
          (r * ((T : ℝ) ^ 2)) := by
        simpa only [one_mul] using hmul
      _ = Real.exp
          (((T : ℝ) ^ 2) * r) := by
        congr 1
        ring
  exact_mod_cast hreal.trans (Nat.le_ceil _)

/-! ## Separated finite placement -/

def nextQuadraticPrimeBandScale (a : ℝ) (T : ℕ) : ℕ :=
  max (T + 1) (expEndpoint a (T ^ 2) + 1)

def placedQuadraticPrimeBandScale
    (A : ℕ) (a : ℝ) : ℕ → ℕ
  | 0 => A + 1
  | n + 1 =>
      nextQuadraticPrimeBandScale a
        (placedQuadraticPrimeBandScale A a n)

@[simp]
theorem placedQuadraticPrimeBandScale_zero
    (A : ℕ) (a : ℝ) :
    placedQuadraticPrimeBandScale A a 0 = A + 1 :=
  rfl

@[simp]
theorem placedQuadraticPrimeBandScale_succ
    (A : ℕ) (a : ℝ) (n : ℕ) :
    placedQuadraticPrimeBandScale A a (n + 1) =
      nextQuadraticPrimeBandScale a
        (placedQuadraticPrimeBandScale A a n) :=
  rfl

theorem placedQuadraticPrimeBandScale_lt_succ
    (A : ℕ) (a : ℝ) (n : ℕ) :
    placedQuadraticPrimeBandScale A a n <
      placedQuadraticPrimeBandScale A a (n + 1) := by
  rw [placedQuadraticPrimeBandScale_succ,
    nextQuadraticPrimeBandScale]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem placedQuadraticPrimeBandScale_strictMono
    (A : ℕ) (a : ℝ) :
    StrictMono (placedQuadraticPrimeBandScale A a) :=
  strictMono_nat_of_lt_succ
    (placedQuadraticPrimeBandScale_lt_succ A a)

theorem placedQuadraticPrimeBandScale_above
    (A : ℕ) (a : ℝ) (n : ℕ) :
    A < placedQuadraticPrimeBandScale A a n := by
  calc
    A < placedQuadraticPrimeBandScale A a 0 := by simp
    _ ≤ placedQuadraticPrimeBandScale A a n :=
      (placedQuadraticPrimeBandScale_strictMono A a).monotone
        (Nat.zero_le n)

theorem quadraticUpper_lt_nextPlacedScale
    (A : ℕ) (a : ℝ) (n : ℕ) :
    expEndpoint a
        ((placedQuadraticPrimeBandScale A a n) ^ 2) <
      placedQuadraticPrimeBandScale A a (n + 1) := by
  rw [placedQuadraticPrimeBandScale_succ,
    nextQuadraticPrimeBandScale]
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

theorem quadraticUpper_lt_placedScale_of_lt
    (A : ℕ) (a : ℝ) {i j : ℕ} (hij : i < j) :
    expEndpoint a
        ((placedQuadraticPrimeBandScale A a i) ^ 2) <
      placedQuadraticPrimeBandScale A a j := by
  exact (quadraticUpper_lt_nextPlacedScale A a i).trans_le
    ((placedQuadraticPrimeBandScale_strictMono A a).monotone
      (Nat.succ_le_iff.mpr hij))

def placedQuadraticPrimeBands
    (A M : ℕ) (a : ℝ) (j : Fin M) : Finset ℕ :=
  quadraticPrimeBand
    (placedQuadraticPrimeBandScale A a j.1) a

theorem placedQuadraticPrimeBands_prime
    (A M : ℕ) (a : ℝ) :
    ∀ j, IsPrimeSupport (placedQuadraticPrimeBands A M a j) := by
  intro j
  exact quadraticPrimeBand_prime _ _

theorem placedQuadraticPrimeBands_above
    (A M : ℕ) (a : ℝ) :
    ∀ j p, p ∈ placedQuadraticPrimeBands A M a j → A < p := by
  intro j p hp
  have hpLower := (mem_quadraticPrimeBand.mp hp).2.1
  have hscaleOne :
      1 ≤ placedQuadraticPrimeBandScale A a j.1 := by
    have habove :=
      placedQuadraticPrimeBandScale_above A a j.1
    omega
  exact (placedQuadraticPrimeBandScale_above A a j.1).trans_le
    ((nat_le_quadraticLowerCutoff _).trans_lt hpLower).le

theorem placedQuadraticPrimeBands_disjoint
    (A M : ℕ) (a : ℝ) :
    PairwiseDisjointBands (placedQuadraticPrimeBands A M a) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hij' | hji'
  · have hi := mem_quadraticPrimeBand.mp hpi
    have hj := mem_quadraticPrimeBand.mp hpj
    have hsep :=
      quadraticUpper_lt_placedScale_of_lt A a hij'
    have hlower :
        placedQuadraticPrimeBandScale A a j.1 ≤
          quadraticLowerCutoff
            (placedQuadraticPrimeBandScale A a j.1) :=
      nat_le_quadraticLowerCutoff _
    omega
  · have hi := mem_quadraticPrimeBand.mp hpi
    have hj := mem_quadraticPrimeBand.mp hpj
    have hsep :=
      quadraticUpper_lt_placedScale_of_lt A a hji'
    have hlower :
        placedQuadraticPrimeBandScale A a i.1 ≤
          quadraticLowerCutoff
            (placedQuadraticPrimeBandScale A a i.1) :=
      nat_le_quadraticLowerCutoff _
    omega

/-! ## Uniform local reservoirs inside the quadratic band -/

theorem localPrimeBand_square_subset_quadraticPrimeBand
    {T : ℕ} {a r₀ t r₁ h : ℝ}
    (hT : 0 < T) (hr₀ : 0 < r₀)
    (hr₀t : r₀ ≤ t) (htr₁ : t ≤ r₁)
    (hlowerEndpoint :
      quadraticLowerCutoff T ≤
        LocalPrimeBand.localLowerEndpoint (T ^ 2) t)
    (hupperScale :
      h + 1 ≤ ((T ^ 2 : ℕ) : ℝ) * (a - r₁)) :
    LocalPrimeBand.localPrimeBand (T ^ 2) t h ⊆
      quadraticPrimeBand T a := by
  intro p hp
  have hpLocal := LocalPrimeBand.mem_localPrimeBand.mp hp
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have ht : 0 < t := hr₀.trans_le hr₀t
  let A := LocalPrimeBand.localLowerEndpoint (T ^ 2) t
  have hApos : (0 : ℝ) < A := by
    exact_mod_cast LocalPrimeBand.localLowerEndpoint_pos (T ^ 2) t
  have hx0 :
      0 ≤ (((T ^ 2 : ℕ) : ℝ) * t) := by positivity
  have hAupper :
      (A : ℝ) ≤
        2 * Real.exp (((T ^ 2 : ℕ) : ℝ) * t) := by
    have hceil :
        (A : ℝ) <
          Real.exp (((T ^ 2 : ℕ) : ℝ) * t) + 1 := by
      exact_mod_cast Nat.ceil_lt_add_one
        (Real.exp_nonneg (((T ^ 2 : ℕ) : ℝ) * t))
    have hexpone :
        1 ≤ Real.exp (((T ^ 2 : ℕ) : ℝ) * t) :=
      Real.one_le_exp hx0
    linarith
  have htwoexp : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num at h ⊢
    exact h
  have hrealUpper :
      Real.exp h * (A : ℝ) ≤
        Real.exp (((T ^ 2 : ℕ) : ℝ) * a) := by
    calc
      Real.exp h * (A : ℝ) ≤
          Real.exp h *
            (2 * Real.exp (((T ^ 2 : ℕ) : ℝ) * t)) :=
        mul_le_mul_of_nonneg_left hAupper (Real.exp_nonneg h)
      _ ≤ Real.exp h *
            (Real.exp 1 *
              Real.exp (((T ^ 2 : ℕ) : ℝ) * t)) := by
        gcongr
      _ =
          Real.exp
            (h + 1 + ((T ^ 2 : ℕ) : ℝ) * t) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (((T ^ 2 : ℕ) : ℝ) * a) := by
        rw [Real.exp_le_exp]
        have hscaleNonneg :
            0 ≤ ((T ^ 2 : ℕ) : ℝ) := by positivity
        have htBound :
            ((T ^ 2 : ℕ) : ℝ) * t ≤
              ((T ^ 2 : ℕ) : ℝ) * r₁ :=
          mul_le_mul_of_nonneg_left htr₁ hscaleNonneg
        nlinarith
  have hupperEndpoint :
      LocalPrimeBand.localUpperEndpoint (T ^ 2) t h ≤
        expEndpoint a (T ^ 2) := by
    unfold LocalPrimeBand.localUpperEndpoint expEndpoint
    exact Nat.ceil_mono hrealUpper
  exact mem_quadraticPrimeBand.mpr
    ⟨hpLocal.1,
      hlowerEndpoint.trans_lt hpLocal.2.1,
      hpLocal.2.2.trans hupperEndpoint⟩

theorem eventually_localPrimeBand_square_subset_quadraticPrimeBand
    {a r₀ r₁ h : ℝ}
    (hr₀ : 0 < r₀) (hr₁a : r₁ < a) :
    ∀ᶠ T : ℕ in Filter.atTop,
      ∀ t : ℝ, r₀ ≤ t → t ≤ r₁ →
        LocalPrimeBand.localPrimeBand (T ^ 2) t h ⊆
          quadraticPrimeBand T a := by
  have hpowNat :
      Tendsto (fun T : ℕ => T ^ 2)
        Filter.atTop Filter.atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  have hpowReal :
      Tendsto (fun T : ℕ => ((T ^ 2 : ℕ) : ℝ))
        Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hpowNat
  have hcutoffGrowth :
      Tendsto
        (fun T : ℕ =>
          Real.exp
              (r₀ * ((T ^ 2 : ℕ) : ℝ)) /
            (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℝ)))
        Filter.atTop Filter.atTop := by
    have h :=
      tendsto_exp_mul_div_rpow_atTop 3 r₀ hr₀
    exact h.comp hpowReal
  have hgap :
      Tendsto
        (fun T : ℕ =>
          ((T ^ 2 : ℕ) : ℝ) * (a - r₁))
        Filter.atTop Filter.atTop := by
    have h :=
      hpowReal.const_mul_atTop (sub_pos.mpr hr₁a)
    simpa only [mul_comm] using h
  filter_upwards [
      hcutoffGrowth.eventually (eventually_ge_atTop 1),
      hgap.eventually (eventually_ge_atTop (h + 1)),
      eventually_gt_atTop 0] with T hcutoff hupper hT
  intro t hr₀t htr₁
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  have hNR : (0 : ℝ) < (T ^ 2 : ℕ) := by positivity
  have hNR' : (0 : ℝ) < ((T ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast hNR
  have hden :
      0 < (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℝ)) :=
    Real.rpow_pos_of_pos hNR' _
  have hrealCutoff :
      (quadraticLowerCutoff T : ℝ) ≤
        Real.exp
          (((T ^ 2 : ℕ) : ℝ) * r₀) := by
    have hmul := (le_div_iff₀ hden).mp hcutoff
    have hrpow :
        (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℝ)) =
          (((T ^ 2 : ℕ) : ℝ) ^ (3 : ℕ)) := by
      exact Real.rpow_natCast _ 3
    rw [hrpow] at hmul
    unfold quadraticLowerCutoff
    norm_num [Nat.cast_pow] at hmul ⊢
    calc
      (T : ℝ) ^ 6 =
          (((T : ℝ) ^ 2) ^ 3) := by ring
      _ ≤ Real.exp
          (r₀ * ((T : ℝ) ^ 2)) := by
        simpa only [one_mul] using hmul
      _ = Real.exp
          (((T : ℝ) ^ 2) * r₀) := by
        congr 1
        ring
  have hlowerAtBase :
      quadraticLowerCutoff T ≤
        LocalPrimeBand.localLowerEndpoint (T ^ 2) r₀ := by
    unfold LocalPrimeBand.localLowerEndpoint
    exact_mod_cast hrealCutoff.trans (Nat.le_ceil _)
  have hlower :
      quadraticLowerCutoff T ≤
        LocalPrimeBand.localLowerEndpoint (T ^ 2) t := by
    apply hlowerAtBase.trans
    unfold LocalPrimeBand.localLowerEndpoint
    apply Nat.ceil_mono
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hr₀t
      (by positivity)
  exact localPrimeBand_square_subset_quadraticPrimeBand
    hT hr₀ hr₀t htr₁ hlower hupper

theorem eventually_uniform_quadraticLocalBand_lower
    {r₀ r₁ c₀ η : ℝ}
    (hr₀ : 0 < r₀) (hr₀r₁ : r₀ ≤ r₁)
    (hc₀ : 0 < c₀) (hη : 0 < η) :
    ∀ᶠ T : ℕ in Filter.atTop, ∀ t : ℝ, r₀ ≤ t → t ≤ r₁ →
      c₀ * (η / (((T ^ 2 : ℕ) : ℝ))) / (8 * r₁) ≤
        LocalPrimeBand.localBandShiftedReciprocalMass
          (T ^ 2) t (c₀ * η) := by
  have hbase :=
    LocalPrimeBand.eventually_uniform_normalizedLocalBand_lower
      hr₀ hr₀r₁ hc₀ hη
  have hpow :
      Tendsto (fun T : ℕ => T ^ 2)
        Filter.atTop Filter.atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  exact hpow.eventually hbase

theorem eventually_uniform_quadraticLocalBand_upper
    {r₀ c₀ η : ℝ}
    (hr₀ : 0 < r₀) (hc₀ : 0 < c₀) (hη : 0 < η) :
    ∀ᶠ T : ℕ in Filter.atTop, ∀ t : ℝ, r₀ ≤ t →
      LocalPrimeBand.localBandShiftedReciprocalMass
          (T ^ 2) t (c₀ * η) ≤
        (Real.log (Real.exp (c₀ * η) + 1) + 1) /
          (((T ^ 2 : ℕ) : ℝ) * r₀) := by
  have hbase :=
    LocalPrimeBand.eventually_uniform_normalizedLocalBand_upper
      hr₀ hc₀ hη
  have hpow :
      Tendsto (fun T : ℕ => T ^ 2)
        Filter.atTop Filter.atTop :=
    tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)
  exact hpow.eventually hbase

/-! ## Moment endpoint and final assembly -/

/-- Uniform analytic moment bounds on quadratically parametrized bands. -/
def HasEventuallyUniformQuadraticPrimeBandMomentBounds : Prop :=
  ∀ (η : ℝ), 0 < η →
    ∃ (a c C : ℝ) (T₀ : ℕ),
      0 < c ∧ 0 ≤ C ∧
      ∀ T : ℕ, T₀ ≤ T →
        ∃ (w : ℝ)
          (B : FiveConfiguration (quadraticPrimeBand T a) → Bool),
          0 < w ∧
          FiveEventHasPetals (quadraticPrimeBand T a) B ∧
          FiveEventPetalLogBalanced
            (quadraticPrimeBand T a) B η ∧
          c * w ^ 2 ≤
            fiveEventMass
              (quadraticPrimeBand T a) reciprocalBernoulli B ∧
          ∀ s : Fin 3,
            fiveRootCollision
              (quadraticPrimeBand T a) reciprocalBernoulli B s ≤
                C * w ^ 4

private theorem quadraticConditionedRoot_secondMoment_le
    {T : ℕ} {a c C w : ℝ}
    {B : FiveConfiguration (quadraticPrimeBand T a) → Bool}
    (hc : 0 < c) (hw : 0 < w)
    (hmass : c * w ^ 2 ≤
      fiveEventMass
        (quadraticPrimeBand T a) reciprocalBernoulli B)
    (hcollision : ∀ s : Fin 3,
      fiveRootCollision
        (quadraticPrimeBand T a) reciprocalBernoulli B s ≤
          C * w ^ 4) :
    ∀ s : Fin 3,
      rootedSecondMoment Finset.univ
        (subtypeBernoulliWeight
          (quadraticPrimeBand T a) reciprocalBernoulli)
        (rootedBayesDensity
          (fiveEventMass
            (quadraticPrimeBand T a) reciprocalBernoulli B)
          (fiveRootLikelihood
            (quadraticPrimeBand T a) reciprocalBernoulli B s)) ≤
        C / c ^ 2 := by
  intro s
  have hP := quadraticPrimeBand_prime T a
  apply fiveConditionedRootDensity_secondMoment_le_of_scale
    (fun p _hp ↦ reciprocalBernoulli_nonneg p)
    (fun p hp ↦
      (reciprocalBernoulli_lt_one (hP p hp).pos).le)
    (fun S ↦
      (subtypeBernoulliWeight_pos
        (fun _p _hp ↦ reciprocalBernoulli_pos)
        (fun p hp ↦ reciprocalBernoulli_lt_one
          (hP p hp).pos) S).ne')
    hc hw hmass (hcollision s)

theorem alternativeBandCertificates_of_quadraticMomentBounds
    (hmoment : HasEventuallyUniformQuadraticPrimeBandMomentBounds) :
    HasArbitrarilyGoodAlternativeBandCertificates := by
  intro A ε δ hε hδ
  obtain ⟨η, hη, hηδ⟩ :=
    exists_logTolerance_exp_sub_one_eq hδ
  obtain ⟨a, c, C, T₀, hc, hC, hmomentη⟩ :=
    hmoment η hη
  let K : ℝ := C / c ^ 2
  have hK : 0 ≤ K := div_nonneg hC (sq_nonneg c)
  obtain ⟨M, hM, hMK⟩ :=
    exists_alternativeCount_sqrt_div_lt hK hε
  let A' : ℕ := max A T₀
  have hAA' : A ≤ A' := Nat.le_max_left _ _
  have hT₀A' : T₀ ≤ A' := Nat.le_max_right _ _
  have hscale (j : Fin M) :
      T₀ ≤ placedQuadraticPrimeBandScale A' a j.1 :=
    hT₀A'.trans
      (placedQuadraticPrimeBandScale_above A' a j.1).le
  let w (j : Fin M) : ℝ :=
    Classical.choose
      (hmomentη
        (placedQuadraticPrimeBandScale A' a j.1)
        (hscale j))
  let B :
      ∀ j : Fin M,
        FiveConfiguration
          (placedQuadraticPrimeBands A' M a j) → Bool :=
    fun j ↦ Classical.choose
      (Classical.choose_spec
        (hmomentη
          (placedQuadraticPrimeBandScale A' a j.1)
          (hscale j)))
  have hanalytic (j : Fin M) :
      0 < w j ∧
      FiveEventHasPetals
        (placedQuadraticPrimeBands A' M a j) (B j) ∧
      FiveEventPetalLogBalanced
        (placedQuadraticPrimeBands A' M a j) (B j) η ∧
      c * (w j) ^ 2 ≤
        fiveEventMass
          (placedQuadraticPrimeBands A' M a j)
          reciprocalBernoulli (B j) ∧
      ∀ s : Fin 3,
        fiveRootCollision
          (placedQuadraticPrimeBands A' M a j)
          reciprocalBernoulli (B j) s ≤
            C * (w j) ^ 4 := by
    exact Classical.choose_spec
      (Classical.choose_spec
        (hmomentη
          (placedQuadraticPrimeBandScale A' a j.1)
          (hscale j)))
  have hpositive (j : Fin M) :
      0 < fiveEventMass
        (placedQuadraticPrimeBands A' M a j)
        reciprocalBernoulli (B j) := by
    have hcw : 0 < c * (w j) ^ 2 :=
      mul_pos hc (sq_pos_of_pos (hanalytic j).1)
    exact hcw.trans_le (hanalytic j).2.2.2.1
  let C' : AlternativeBandCertificate A' M η K :=
    { M_pos := hM
      bands := placedQuadraticPrimeBands A' M a
      events := B
      bands_prime := placedQuadraticPrimeBands_prime A' M a
      bands_above := placedQuadraticPrimeBands_above A' M a
      bands_disjoint := placedQuadraticPrimeBands_disjoint A' M a
      events_havePetals := fun j ↦ (hanalytic j).2.1
      events_positive := hpositive
      events_logBalanced := fun j ↦ (hanalytic j).2.2.1
      K_nonneg := hK
      rooted_secondMoment := by
        intro j
        exact quadraticConditionedRoot_secondMoment_le
          hc (hanalytic j).1 (hanalytic j).2.2.2.1
            (hanalytic j).2.2.2.2 }
  let Cert : AlternativeBandCertificate A M η K :=
    C'.lowerCutoff_mono hAA'
  exact ⟨M, η, K, ⟨Cert⟩, hMK.le, hηδ.le⟩

theorem mainTheorem_of_quadraticPrimeBandMomentBounds
    (hmoment : HasEventuallyUniformQuadraticPrimeBandMomentBounds) :
    MainTheorem :=
  mainTheorem_of_alternativeBandCertificates
    (alternativeBandCertificates_of_quadraticMomentBounds hmoment)

end

end Erdos536
