import Erdos536.AlternativeBandOneCube
import Erdos536.AlternativeBandParameters
import Erdos536.PrimeBandEvent
import Erdos536.PrimeBandTimeChange

/-!
# Finite placement of alternative prime bands

The analytic prime-band estimates are local in a scale parameter.  This
file supplies the elementary finite placement layer needed to use finitely
many such estimates at once.

Starting above a prescribed cutoff, each new scale is chosen beyond both
the preceding scale and the upper endpoint of the preceding broad band.
Consequently the resulting broad prime bands are pairwise disjoint.  The
last two constructions package uniform event estimates on these placed
bands into an `AlternativeBandCertificate`; none of the hard first- or
second-moment estimates is assumed implicitly.
-/

open scoped BigOperators

noncomputable section

namespace Erdos536

open PrimeBandTimeChange
open PrimeSums

/-! ## Separated scales and bands -/

/-- Advance beyond both the current scale and its exponential endpoint. -/
def nextPrimeBandScale (a : ℝ) (T : ℕ) : ℕ :=
  max (T + 1) (expEndpoint a T + 1)

/-- Recursively placed scales, starting strictly above `A`. -/
def placedPrimeBandScale (A : ℕ) (a : ℝ) : ℕ → ℕ
  | 0 => A + 1
  | n + 1 => nextPrimeBandScale a (placedPrimeBandScale A a n)

@[simp]
theorem placedPrimeBandScale_zero (A : ℕ) (a : ℝ) :
    placedPrimeBandScale A a 0 = A + 1 :=
  rfl

@[simp]
theorem placedPrimeBandScale_succ (A : ℕ) (a : ℝ) (n : ℕ) :
    placedPrimeBandScale A a (n + 1) =
      nextPrimeBandScale a (placedPrimeBandScale A a n) :=
  rfl

theorem placedPrimeBandScale_lt_succ (A : ℕ) (a : ℝ) (n : ℕ) :
    placedPrimeBandScale A a n <
      placedPrimeBandScale A a (n + 1) := by
  rw [placedPrimeBandScale_succ, nextPrimeBandScale]
  exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)

theorem placedPrimeBandScale_strictMono (A : ℕ) (a : ℝ) :
    StrictMono (placedPrimeBandScale A a) :=
  strictMono_nat_of_lt_succ (placedPrimeBandScale_lt_succ A a)

theorem placedPrimeBandScale_above (A : ℕ) (a : ℝ) (n : ℕ) :
    A < placedPrimeBandScale A a n := by
  calc
    A < placedPrimeBandScale A a 0 := by simp
    _ ≤ placedPrimeBandScale A a n :=
      (placedPrimeBandScale_strictMono A a).monotone (Nat.zero_le n)

theorem expEndpoint_lt_next_placedPrimeBandScale
    (A : ℕ) (a : ℝ) (n : ℕ) :
    expEndpoint a (placedPrimeBandScale A a n) <
      placedPrimeBandScale A a (n + 1) := by
  rw [placedPrimeBandScale_succ, nextPrimeBandScale]
  exact (Nat.lt_succ_self _).trans_le (le_max_right _ _)

theorem expEndpoint_lt_placedPrimeBandScale_of_lt
    (A : ℕ) (a : ℝ) {i j : ℕ} (hij : i < j) :
    expEndpoint a (placedPrimeBandScale A a i) <
      placedPrimeBandScale A a j := by
  exact
    (expEndpoint_lt_next_placedPrimeBandScale A a i).trans_le
      ((placedPrimeBandScale_strictMono A a).monotone
        (Nat.succ_le_iff.mpr hij))

/-- The finite family of broad bands at the recursively separated scales. -/
def placedPrimeBands (A M : ℕ) (a : ℝ) (j : Fin M) : Finset ℕ :=
  broadPrimeBand (placedPrimeBandScale A a j.1) a

theorem placedPrimeBands_prime (A M : ℕ) (a : ℝ) :
    ∀ j, IsPrimeSupport (placedPrimeBands A M a j) := by
  intro j p hp
  exact (mem_broadPrimeBand.mp hp).1

theorem placedPrimeBands_above (A M : ℕ) (a : ℝ) :
    ∀ j p, p ∈ placedPrimeBands A M a j → A < p := by
  intro j p hp
  exact
    (placedPrimeBandScale_above A a j.1).trans
      (mem_broadPrimeBand.mp hp).2.1

theorem placedPrimeBands_disjoint (A M : ℕ) (a : ℝ) :
    PairwiseDisjointBands (placedPrimeBands A M a) := by
  intro i j hij
  rw [Finset.disjoint_left]
  intro p hpi hpj
  have hval : i.1 ≠ j.1 := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hij' | hji'
  · have hi := mem_broadPrimeBand.mp hpi
    have hj := mem_broadPrimeBand.mp hpj
    have hsep :=
      expEndpoint_lt_placedPrimeBandScale_of_lt A a hij'
    omega
  · have hi := mem_broadPrimeBand.mp hpi
    have hj := mem_broadPrimeBand.mp hpj
    have hsep :=
      expEndpoint_lt_placedPrimeBandScale_of_lt A a hji'
    omega

theorem placedPrimeBandScales_strictMono (A M : ℕ) (a : ℝ) :
    StrictMono (fun j : Fin M ↦ placedPrimeBandScale A a j.1) := by
  intro i j hij
  exact placedPrimeBandScale_strictMono A a hij

/-- Existence form of finite prime-band placement.  It records the scales,
their strict increase, primality, the lower cutoff, and pairwise
disjointness in one statement. -/
theorem exists_placedPrimeBands (A M : ℕ) (a : ℝ) :
    ∃ (T : Fin M → ℕ) (R : Fin M → Finset ℕ),
      StrictMono T ∧
      (∀ j, R j = broadPrimeBand (T j) a) ∧
      (∀ j, IsPrimeSupport (R j)) ∧
      (∀ j p, p ∈ R j → A < p) ∧
      PairwiseDisjointBands R := by
  refine
    ⟨fun j ↦ placedPrimeBandScale A a j.1,
      placedPrimeBands A M a,
      placedPrimeBandScales_strictMono A M a, ?_, ?_, ?_, ?_⟩
  · intro j
    rfl
  · exact placedPrimeBands_prime A M a
  · exact placedPrimeBands_above A M a
  · exact placedPrimeBands_disjoint A M a

/-! ## The common logarithmic window -/

/-- The manuscript's choice `w_j = η / T_j` on a placed band. -/
def placedPrimeBandWindow
    (A M : ℕ) (a η : ℝ) (j : Fin M) : ℝ :=
  η / (placedPrimeBandScale A a j.1 : ℝ)

theorem placedPrimeBandScale_mul_window
    (A M : ℕ) (a η : ℝ) (j : Fin M) :
    (placedPrimeBandScale A a j.1 : ℝ) *
        placedPrimeBandWindow A M a η j = η := by
  have hscale : (placedPrimeBandScale A a j.1 : ℝ) ≠ 0 := by
    exact_mod_cast
      ((Nat.zero_le A).trans_lt
        (placedPrimeBandScale_above A a j.1)).ne'
  rw [placedPrimeBandWindow]
  exact mul_div_cancel₀ η hscale

theorem placedPrimeBandScale_mul_window_le
    (A M : ℕ) (a η : ℝ) :
    ∀ j, (placedPrimeBandScale A a j.1 : ℝ) *
        placedPrimeBandWindow A M a η j ≤ η := by
  intro j
  rw [placedPrimeBandScale_mul_window]

/-! ## Packaging uniform estimates -/

/-- Uniform estimates for arbitrary events on the placed bands give an
alternative-band certificate.  The geometric fields of the certificate
are supplied by the placement theorems above. -/
def alternativeBandCertificateOfPlacedBands
    {A M : ℕ} {a η K : ℝ}
    (hM : 0 < M)
    (events :
      ∀ j, FiveConfiguration (placedPrimeBands A M a j) → Bool)
    (heventsHavePetals :
      ∀ j, FiveEventHasPetals (placedPrimeBands A M a j) (events j))
    (heventsPositive :
      ∀ j, 0 <
        fiveEventMass (placedPrimeBands A M a j)
          reciprocalBernoulli (events j))
    (heventsLogBalanced :
      ∀ j, FiveEventPetalLogBalanced
        (placedPrimeBands A M a j) (events j) η)
    (hK : 0 ≤ K)
    (hroot :
      ∀ j (s : Fin 3),
        rootedSecondMoment Finset.univ
          (subtypeBernoulliWeight
            (placedPrimeBands A M a j) reciprocalBernoulli)
          (rootedBayesDensity
            (fiveEventMass (placedPrimeBands A M a j)
              reciprocalBernoulli (events j))
            (fiveRootLikelihood (placedPrimeBands A M a j)
              reciprocalBernoulli (events j) s)) ≤ K) :
    AlternativeBandCertificate A M η K where
  M_pos := hM
  bands := placedPrimeBands A M a
  events := events
  bands_prime := placedPrimeBands_prime A M a
  bands_above := placedPrimeBands_above A M a
  bands_disjoint := placedPrimeBands_disjoint A M a
  events_havePetals := heventsHavePetals
  events_positive := heventsPositive
  events_logBalanced := heventsLogBalanced
  K_nonneg := hK
  rooted_secondMoment := hroot

/-! ## The explicit symmetric five-state events -/

/-- The target five-state event on each recursively placed band. -/
noncomputable def placedFivePrimeBandEvents
    (A M : ℕ) (a lower upper : ℝ) (w : Fin M → ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (j : Fin M) :
    FiveConfiguration (placedPrimeBands A M a j) → Bool :=
  fivePrimeBandEvent
    (placedPrimeBands A M a j)
    (placedPrimeBandScale A a j.1 : ℝ)
    lower upper (w j) depths threshold

theorem placedFivePrimeBandEvents_havePetals
    {A M : ℕ} {a lower upper : ℝ} {w : Fin M → ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀) :
    ∀ j, FiveEventHasPetals
      (placedPrimeBands A M a j)
      (placedFivePrimeBandEvents
        A M a lower upper w depths threshold j) := by
  intro j
  exact fivePrimeBandEvent_hasPetals hd₀ hthreshold

theorem placedFivePrimeBandEvents_logBalanced
    {A M : ℕ} {a lower upper η : ℝ} {w : Fin M → ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    (hw :
      ∀ j, (placedPrimeBandScale A a j.1 : ℝ) * w j ≤ η) :
    ∀ j, FiveEventPetalLogBalanced
      (placedPrimeBands A M a j)
      (placedFivePrimeBandEvents
        A M a lower upper w depths threshold j) η := by
  intro j c hc s t
  have hscale : 0 < (placedPrimeBandScale A a j.1 : ℝ) := by
    exact_mod_cast
      (Nat.zero_le A).trans_lt
        (placedPrimeBandScale_above A a j.1)
  exact
    (fivePrimeBandEvent_petalLogBalanced hscale c hc s t).trans
      (hw j)

/-- The concrete placement constructor.  Event positivity and the uniform
rooted second-moment estimate are precisely the two analytic inputs left as
hypotheses.  The prefix hypothesis supplies nonempty petals, while
`T_j w_j ≤ η` supplies the uniform logarithmic balance. -/
noncomputable def placedFivePrimeBandCertificate
    {A M : ℕ} {a lower upper η K : ℝ}
    (hM : 0 < M) (w : Fin M → ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    {d₀ : ℝ} (hd₀ : d₀ ∈ depths)
    (hthreshold : 1 ≤ threshold d₀)
    (hw :
      ∀ j, (placedPrimeBandScale A a j.1 : ℝ) * w j ≤ η)
    (hpositive :
      ∀ j, 0 <
        fiveEventMass (placedPrimeBands A M a j)
          reciprocalBernoulli
          (placedFivePrimeBandEvents
            A M a lower upper w depths threshold j))
    (hK : 0 ≤ K)
    (hroot :
      ∀ j (s : Fin 3),
        rootedSecondMoment Finset.univ
          (subtypeBernoulliWeight
            (placedPrimeBands A M a j) reciprocalBernoulli)
          (rootedBayesDensity
            (fiveEventMass (placedPrimeBands A M a j)
              reciprocalBernoulli
              (placedFivePrimeBandEvents
                A M a lower upper w depths threshold j))
            (fiveRootLikelihood (placedPrimeBands A M a j)
              reciprocalBernoulli
              (placedFivePrimeBandEvents
                A M a lower upper w depths threshold j) s)) ≤ K) :
    AlternativeBandCertificate A M η K :=
  alternativeBandCertificateOfPlacedBands hM
    (placedFivePrimeBandEvents
      A M a lower upper w depths threshold)
    (placedFivePrimeBandEvents_havePetals hd₀ hthreshold)
    hpositive
    (placedFivePrimeBandEvents_logBalanced hw)
    hK hroot

end Erdos536
