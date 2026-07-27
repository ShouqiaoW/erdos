import Erdos536.FiveStateChernoff
import Erdos536.FiniteUnionBound
import Erdos536.PrimeBandTimeChange

/-!
# Finite categorical prefix-profile estimates

The target prime-band event asks each of its four active labels to contain
enough points in every checked depth prefix.  This file proves that the
total mass of all prefix failures is controlled directly in the finite
five-state product law.

The first theorem is an exact finite-grid union/Chernoff bound.  The second
packages the usual time-change input as two affine inequalities: prefix
intensity grows at rate `rho`, while the requested count grows at rate
`sigma`.  Whenever the Chernoff gap is positive, summing over an arbitrary
finite set of integer checks costs only a convergent geometric series.  In
particular, the estimate is independent of the depth horizon.
-/

open scoped BigOperators
open Finset
open Filter

namespace Erdos536

/-- The points of `R` lying in the depth prefix ending at `d`. -/
noncomputable def fiveDepthPrefixCarrier
    {α : Type*} [DecidableEq α]
    (R : Finset α) (depth : α → ℝ) (d : ℝ) : Finset ↥R :=
  Finset.univ.filter fun p ↦ depth p.1 ≤ d

@[simp]
theorem mem_fiveDepthPrefixCarrier
    {α : Type*} [DecidableEq α]
    {R : Finset α} {depth : α → ℝ} {d : ℝ} {p : ↥R} :
    p ∈ fiveDepthPrefixCarrier R depth d ↔ depth p.1 ≤ d := by
  simp [fiveDepthPrefixCarrier]

/-- Counting a label on the abstract depth carrier agrees with the
concrete prefix count used by `fivePrimeBandEvent`. -/
theorem fiveActiveLabelCountOn_depthPrefix
    (R : Finset ℕ) (T : ℝ) (c : FiveConfiguration R)
    (l : ActiveFiveLabel) (d : ℝ) :
    fiveActiveLabelCountOn
        (fiveDepthPrefixCarrier R (normalizedLogDepth T) d) l c =
      fiveLabelPrefixCount R T c l d := by
  rw [fiveActiveLabelCountOn, fiveLabelPrefixCount]
  congr 1
  ext p
  simp [fiveDepthPrefixCarrier, fiveLabelDepthPrefix, and_comm]

/-- Failure of one checked lower-prefix requirement. -/
noncomputable def fivePrefixFailureAt
    (R : Finset ℕ) (T : ℝ) (threshold : ℝ → ℕ)
    (l : ActiveFiveLabel) (d : ℝ)
    (c : FiveConfiguration R) : Bool :=
  decide (fiveLabelPrefixCount R T c l d < threshold d)

/-- Failure of at least one label/depth requirement on a finite grid. -/
noncomputable def fivePrefixProfileFailure
    (R : Finset ℕ) (T : ℝ)
    (depths : Finset ℝ) (threshold : ℝ → ℕ)
    (c : FiveConfiguration R) : Bool :=
  decide (∃ l : ActiveFiveLabel, ∃ d : ↥depths,
    fiveLabelPrefixCount R T c l d.1 < threshold d.1)

@[simp]
theorem fivePrefixFailureAt_iff
    {R : Finset ℕ} {T : ℝ} {threshold : ℝ → ℕ}
    {l : ActiveFiveLabel} {d : ℝ} {c : FiveConfiguration R} :
    fivePrefixFailureAt R T threshold l d c ↔
      fiveLabelPrefixCount R T c l d < threshold d := by
  simp [fivePrefixFailureAt]

@[simp]
theorem fivePrefixProfileFailure_iff
    {R : Finset ℕ} {T : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    {c : FiveConfiguration R} :
    fivePrefixProfileFailure R T depths threshold c ↔
      ∃ l : ActiveFiveLabel, ∃ d : ↥depths,
        fiveLabelPrefixCount R T c l d.1 < threshold d.1 := by
  simp [fivePrefixProfileFailure]

private theorem fiveConfigurationWeight_nonneg_of_bounds
    {α : Type*} [DecidableEq α]
    {R : Finset α} {r : α → ℝ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (c : FiveConfiguration R) :
    0 ≤ fiveConfigurationWeight R r c := by
  rw [fiveConfigurationWeight]
  apply Finset.prod_nonneg
  intro p _hp
  exact fiveLabelWeight_nonneg
    (hr0 p.1 p.2) (hr1 p.1 p.2) (c p)

private theorem fivePrefixFailureAt_mass_eq_lowerTail
    {R : Finset ℕ} {r : ℕ → ℝ} {T : ℝ}
    {threshold : ℝ → ℕ} {l : ActiveFiveLabel} {d : ℝ}
    (hthreshold : 0 < threshold d) :
    finiteBoolEventMass
        (Finset.univ : Finset (FiveConfiguration R))
        (fiveConfigurationWeight R r)
        (fivePrefixFailureAt R T threshold l d) =
      fiveActiveLabelLowerTailMass R r
        (fiveDepthPrefixCarrier R (normalizedLogDepth T) d)
        l (threshold d - 1) := by
  rw [finiteBoolEventMass, fiveActiveLabelLowerTailMass]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [fiveActiveLabelCountOn_depthPrefix]
  by_cases hfail :
      fiveLabelPrefixCount R T c l d < threshold d
  · have htail :
        fiveLabelPrefixCount R T c l d ≤ threshold d - 1 := by
      omega
    simp [fivePrefixFailureAt, hfail, htail]
  · have htail :
        ¬fiveLabelPrefixCount R T c l d ≤ threshold d - 1 := by
      omega
    simp [fivePrefixFailureAt, hfail, htail]

/-- Exact finite-grid union/Chernoff estimate for failure of the lower
prefix profile.  The right side has one explicit exponential term for
each of the four active labels and each checked depth. -/
theorem fivePrefixProfileFailureMass_le
    {R : Finset ℕ} {r : ℕ → ℝ} {T t : ℝ}
    {depths : Finset ℝ} {threshold : ℝ → ℕ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (ht : 0 ≤ t)
    (hthreshold : ∀ d ∈ depths, 0 < threshold d) :
    fiveEventMass R r
        (fivePrefixProfileFailure R T depths threshold) ≤
      ∑ i : ActiveFiveLabel × ↥depths,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) i.2.1,
                r p.1 / 3) := by
  classical
  let I : Finset (ActiveFiveLabel × ↥depths) := Finset.univ
  let E : (ActiveFiveLabel × ↥depths) →
      FiveConfiguration R → Bool :=
    fun i ↦ fivePrefixFailureAt R T threshold i.1 i.2.1
  have hunion :
      finiteBoolEventUnion I E =
        fivePrefixProfileFailure R T depths threshold := by
    funext c
    apply Bool.eq_iff_iff.mpr
    simp [I, E, fivePrefixProfileFailure,
      fivePrefixFailureAt, finiteBoolEventUnion]
  have hmass :
      finiteBoolEventMass
          (Finset.univ : Finset (FiveConfiguration R))
          (fiveConfigurationWeight R r)
          (finiteBoolEventUnion I E) ≤
        ∑ i ∈ I,
          finiteBoolEventMass
            (Finset.univ : Finset (FiveConfiguration R))
            (fiveConfigurationWeight R r) (E i) :=
    finiteBoolEventUnion_mass_le_sum I Finset.univ
      (fiveConfigurationWeight R r) E
      (fun c _hc ↦
        fiveConfigurationWeight_nonneg_of_bounds hr0 hr1 c)
  rw [hunion] at hmass
  have hleft :
      finiteBoolEventMass
          (Finset.univ : Finset (FiveConfiguration R))
          (fiveConfigurationWeight R r)
          (fivePrefixProfileFailure R T depths threshold) =
        fiveEventMass R r
          (fivePrefixProfileFailure R T depths threshold) := by
    rw [finiteBoolEventMass, fiveEventMass]
  rw [hleft] at hmass
  calc
    fiveEventMass R r
        (fivePrefixProfileFailure R T depths threshold) ≤
      ∑ i ∈ I,
        finiteBoolEventMass
          (Finset.univ : Finset (FiveConfiguration R))
          (fiveConfigurationWeight R r) (E i) :=
      hmass
    _ ≤ ∑ i ∈ I,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) i.2.1,
                r p.1 / 3) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [show E i =
          fivePrefixFailureAt R T threshold i.1 i.2.1 by rfl]
      rw [fivePrefixFailureAt_mass_eq_lowerTail
        (hthreshold i.2.1 i.2.2)]
      exact fiveActiveLabelLowerTailMass_le hr0 hr1 ht
    _ = ∑ i : ActiveFiveLabel × ↥depths,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) i.2.1,
                r p.1 / 3) := by
      simp [I]

/-! ## Integer grids and a horizon-uniform geometric bound -/

/-- Failure on a finite collection of integer-indexed depth checks. -/
noncomputable def fiveIndexedPrefixProfileFailure
    (R : Finset ℕ) (T : ℝ) (checks : Finset ℕ)
    (depth : ℕ → ℝ) (threshold : ℕ → ℕ)
    (c : FiveConfiguration R) : Bool :=
  decide (∃ l : ActiveFiveLabel, ∃ n ∈ checks,
    fiveLabelPrefixCount R T c l (depth n) < threshold n)

/-- The complementary event in which every indexed prefix check
survives. -/
noncomputable def fiveIndexedPrefixProfileSuccess
    (R : Finset ℕ) (T : ℝ) (checks : Finset ℕ)
    (depth : ℕ → ℝ) (threshold : ℕ → ℕ)
    (c : FiveConfiguration R) : Bool :=
  !(fiveIndexedPrefixProfileFailure
    R T checks depth threshold c)

@[simp]
theorem fiveIndexedPrefixProfileFailure_iff
    {R : Finset ℕ} {T : ℝ} {checks : Finset ℕ}
    {depth : ℕ → ℝ} {threshold : ℕ → ℕ}
    {c : FiveConfiguration R} :
    fiveIndexedPrefixProfileFailure
        R T checks depth threshold c ↔
      ∃ l : ActiveFiveLabel, ∃ n ∈ checks,
        fiveLabelPrefixCount R T c l (depth n) < threshold n := by
  simp [fiveIndexedPrefixProfileFailure]

@[simp]
theorem fiveIndexedPrefixProfileSuccess_iff
    {R : Finset ℕ} {T : ℝ} {checks : Finset ℕ}
    {depth : ℕ → ℝ} {threshold : ℕ → ℕ}
    {c : FiveConfiguration R} :
    fiveIndexedPrefixProfileSuccess
        R T checks depth threshold c ↔
      ∀ l : ActiveFiveLabel, ∀ n ∈ checks,
        threshold n ≤
          fiveLabelPrefixCount R T c l (depth n) := by
  constructor
  · intro hsuccess l n hn
    apply Nat.le_of_not_gt
    intro hbad
    have hfailure :
        fiveIndexedPrefixProfileFailure
          R T checks depth threshold c :=
      fiveIndexedPrefixProfileFailure_iff.mpr
        ⟨l, n, hn, hbad⟩
    have hnot :
        ¬fiveIndexedPrefixProfileSuccess
          R T checks depth threshold c := by
      simp [fiveIndexedPrefixProfileSuccess, hfailure]
    exact hnot hsuccess
  · intro hall
    by_cases hfailure :
        fiveIndexedPrefixProfileFailure
          R T checks depth threshold c
    · obtain ⟨l, n, hn, hbad⟩ :=
        fiveIndexedPrefixProfileFailure_iff.mp hfailure
      exact False.elim ((Nat.not_lt_of_ge (hall l n hn)) hbad)
    · simp [fiveIndexedPrefixProfileSuccess, hfailure]

private theorem fiveEventMass_complement
    {α : Type*} [DecidableEq α]
    (R : Finset α) (r : α → ℝ)
    (B : FiveConfiguration R → Bool) :
    fiveEventMass R r (fun c ↦ !(B c)) =
      1 - fiveEventMass R r B := by
  rw [fiveEventMass, fiveEventMass,
    ← sum_fiveConfigurationWeight R r,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _hc
  cases hB : B c <;> simp

private theorem fiveIndexedPrefixFailureAt_mass_eq_lowerTail
    {R : Finset ℕ} {r : ℕ → ℝ} {T : ℝ}
    {depth : ℕ → ℝ} {threshold : ℕ → ℕ}
    {l : ActiveFiveLabel} {n : ℕ}
    (hthreshold : 0 < threshold n) :
    finiteBoolEventMass
        (Finset.univ : Finset (FiveConfiguration R))
        (fiveConfigurationWeight R r)
        (fun c ↦ decide
          (fiveLabelPrefixCount R T c l (depth n) < threshold n)) =
      fiveActiveLabelLowerTailMass R r
        (fiveDepthPrefixCarrier R
          (normalizedLogDepth T) (depth n))
        l (threshold n - 1) := by
  rw [finiteBoolEventMass, fiveActiveLabelLowerTailMass]
  apply Finset.sum_congr rfl
  intro c _hc
  rw [fiveActiveLabelCountOn_depthPrefix]
  by_cases hfail :
      fiveLabelPrefixCount R T c l (depth n) < threshold n
  · have htail :
        fiveLabelPrefixCount R T c l (depth n) ≤
          threshold n - 1 := by
      omega
    simp [hfail, htail]
  · have htail :
        ¬fiveLabelPrefixCount R T c l (depth n) ≤
          threshold n - 1 := by
      omega
    simp [hfail, htail]

private theorem fiveIndexedPrefixProfileFailureMass_le
    {R : Finset ℕ} {r : ℕ → ℝ} {T t : ℝ}
    {checks : Finset ℕ} {depth : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (ht : 0 ≤ t)
    (hthreshold : ∀ n ∈ checks, 0 < threshold n) :
    fiveEventMass R r
        (fiveIndexedPrefixProfileFailure
          R T checks depth threshold) ≤
      ∑ i : ActiveFiveLabel × ↥checks,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) (depth i.2.1),
                r p.1 / 3) := by
  classical
  let I : Finset (ActiveFiveLabel × ↥checks) := Finset.univ
  let E : (ActiveFiveLabel × ↥checks) →
      FiveConfiguration R → Bool :=
    fun i c ↦
      decide
        (fiveLabelPrefixCount R T c i.1 (depth i.2.1) <
          threshold i.2.1)
  have hunion :
      finiteBoolEventUnion I E =
        fiveIndexedPrefixProfileFailure
          R T checks depth threshold := by
    funext c
    apply Bool.eq_iff_iff.mpr
    simp [I, E, fiveIndexedPrefixProfileFailure,
      finiteBoolEventUnion]
  have hmass :=
    finiteBoolEventUnion_mass_le_sum I
      (Finset.univ : Finset (FiveConfiguration R))
      (fiveConfigurationWeight R r) E
      (fun c _hc ↦
        fiveConfigurationWeight_nonneg_of_bounds hr0 hr1 c)
  rw [hunion] at hmass
  have hleft :
      finiteBoolEventMass
          (Finset.univ : Finset (FiveConfiguration R))
          (fiveConfigurationWeight R r)
          (fiveIndexedPrefixProfileFailure
            R T checks depth threshold) =
        fiveEventMass R r
          (fiveIndexedPrefixProfileFailure
            R T checks depth threshold) := by
    rw [finiteBoolEventMass, fiveEventMass]
  rw [hleft] at hmass
  calc
    fiveEventMass R r
        (fiveIndexedPrefixProfileFailure
          R T checks depth threshold) ≤
      ∑ i ∈ I,
        finiteBoolEventMass
          (Finset.univ : Finset (FiveConfiguration R))
          (fiveConfigurationWeight R r) (E i) :=
      hmass
    _ ≤ ∑ i ∈ I,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) (depth i.2.1),
                r p.1 / 3) := by
      apply Finset.sum_le_sum
      intro i hi
      have hpos := hthreshold i.2.1 i.2.2
      rw [show E i = fun c ↦ decide
          (fiveLabelPrefixCount R T c i.1 (depth i.2.1) <
            threshold i.2.1) by rfl]
      rw [fiveIndexedPrefixFailureAt_mass_eq_lowerTail hpos]
      exact fiveActiveLabelLowerTailMass_le hr0 hr1 ht
    _ = ∑ i : ActiveFiveLabel × ↥checks,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) (depth i.2.1),
                r p.1 / 3) := by
      simp [I]

/-- An affine lower bound for the time-changed prefix intensity, together
with an affine upper bound for the requested prefix count, gives a
geometric failure estimate independent of the finite check horizon.

`buffer` is the fixed stock of points installed before the growing part
of the profile.  Increasing it improves the bound by `exp (-t*buffer)`.
-/
theorem fivePrefixProfileFailureMass_le_geometric
    {R : Finset ℕ} {r : ℕ → ℝ} {T : ℝ}
    {checks : Finset ℕ} {depth : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    {t rho sigma epsilon buffer gamma : ℝ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (ht : 0 ≤ t)
    (hgamma : 0 < gamma)
    (hthreshold : ∀ n ∈ checks, 0 < threshold n)
    (hintensity : ∀ n ∈ checks,
      rho * (n : ℝ) - epsilon ≤
        ∑ p ∈ fiveDepthPrefixCarrier R
            (normalizedLogDepth T) (depth n),
          r p.1 / 3)
    (hrequest : ∀ n ∈ checks,
      ((threshold n - 1 : ℕ) : ℝ) ≤
        sigma * (n : ℝ) - buffer)
    (hgap :
      gamma ≤ (1 - Real.exp (-t)) * rho - t * sigma) :
    fiveEventMass R r
        (fiveIndexedPrefixProfileFailure
          R T checks depth threshold) ≤
      4 * Real.exp
          (-t * buffer + (1 - Real.exp (-t)) * epsilon) /
        (1 - Real.exp (-gamma)) := by
  classical
  have htheta : 0 ≤ 1 - Real.exp (-t) := by
    rw [sub_nonneg, Real.exp_le_one_iff]
    linarith
  have hbase :=
    fiveIndexedPrefixProfileFailureMass_le
      (T := T) (depth := depth) hr0 hr1 ht hthreshold
  let C : ℝ :=
    Real.exp
      (-t * buffer + (1 - Real.exp (-t)) * epsilon)
  let q : ℝ := Real.exp (-gamma)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hterm (n : ↥checks) :
      Real.exp
          (t * ((threshold n.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) (depth n.1),
                r p.1 / 3) ≤
        C * q ^ n.1 := by
    have hi := hintensity n.1 n.2
    have hk := hrequest n.1 n.2
    have hn : (0 : ℝ) ≤ n.1 := by positivity
    have hexponent :
        t * ((threshold n.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) (depth n.1),
                r p.1 / 3 ≤
          -t * buffer +
            (1 - Real.exp (-t)) * epsilon -
              gamma * (n.1 : ℝ) := by
      have hgapn :
          (t * sigma -
              (1 - Real.exp (-t)) * rho) * (n.1 : ℝ) ≤
            -gamma * (n.1 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hn
        linarith
      calc
        t * ((threshold n.1 - 1 : ℕ) : ℝ) +
              (Real.exp (-t) - 1) *
                ∑ p ∈ fiveDepthPrefixCarrier R
                    (normalizedLogDepth T) (depth n.1),
                  r p.1 / 3 =
            t * ((threshold n.1 - 1 : ℕ) : ℝ) -
              (1 - Real.exp (-t)) *
                ∑ p ∈ fiveDepthPrefixCarrier R
                    (normalizedLogDepth T) (depth n.1),
                  r p.1 / 3 := by ring
        _ ≤ t * (sigma * (n.1 : ℝ) - buffer) -
              (1 - Real.exp (-t)) *
                (rho * (n.1 : ℝ) - epsilon) := by
          gcongr
        _ =
            -t * buffer +
              (1 - Real.exp (-t)) * epsilon +
                (t * sigma -
                  (1 - Real.exp (-t)) * rho) *
                    (n.1 : ℝ) := by ring
        _ ≤ -t * buffer +
              (1 - Real.exp (-t)) * epsilon -
                gamma * (n.1 : ℝ) := by
          linarith
    calc
      Real.exp
          (t * ((threshold n.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) (depth n.1),
                r p.1 / 3) ≤
          Real.exp
            (-t * buffer +
              (1 - Real.exp (-t)) * epsilon -
                gamma * (n.1 : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = C * q ^ n.1 := by
        dsimp [C, q]
        rw [show
          -t * buffer + (1 - Real.exp (-t)) * epsilon -
                gamma * (n.1 : ℝ) =
            (-t * buffer + (1 - Real.exp (-t)) * epsilon) +
              (n.1 : ℝ) * (-gamma) by ring,
          Real.exp_add, Real.exp_nat_mul]
  have hfinite :
      (∑ n : ↥checks, q ^ n.1) ≤ (1 - q)⁻¹ := by
    have hs : Summable (fun n : ℕ ↦ q ^ n) :=
      summable_geometric_of_lt_one hq0 hq1
    calc
      (∑ n : ↥checks, q ^ n.1) =
          ∑ n ∈ checks, q ^ n := by
        rw [Finset.univ_eq_attach, Finset.sum_attach]
      _ ≤ ∑' n : ℕ, q ^ n :=
        hs.sum_le_tsum checks (fun n _hn ↦ pow_nonneg hq0 n)
      _ = (1 - q)⁻¹ :=
        tsum_geometric_of_lt_one hq0 hq1
  calc
    fiveEventMass R r
        (fiveIndexedPrefixProfileFailure
          R T checks depth threshold) ≤
      ∑ i : ActiveFiveLabel × ↥checks,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ fiveDepthPrefixCarrier R
                  (normalizedLogDepth T) (depth i.2.1),
                r p.1 / 3) :=
      hbase
    _ ≤ ∑ i : ActiveFiveLabel × ↥checks,
        C * q ^ i.2.1 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hterm i.2
    _ = 4 * (C * ∑ n : ↥checks, q ^ n.1) := by
      rw [Fintype.sum_prod_type]
      simp
      rw [Finset.mul_sum]
    _ ≤ 4 * (C * (1 - q)⁻¹) := by
      have hC : 0 ≤ C := (Real.exp_pos _).le
      gcongr
    _ =
      4 * Real.exp
          (-t * buffer + (1 - Real.exp (-t)) * epsilon) /
        (1 - Real.exp (-gamma)) := by
      dsimp [C, q]
      rw [div_eq_mul_inv]
      ring

/-- Survival form of `fivePrefixProfileFailureMass_le_geometric`.
It gives a positive, horizon-independent lower bound as soon as the
displayed geometric error is less than one. -/
theorem fivePrefixProfileSuccessMass_ge_geometric
    {R : Finset ℕ} {r : ℕ → ℝ} {T : ℝ}
    {checks : Finset ℕ} {depth : ℕ → ℝ}
    {threshold : ℕ → ℕ}
    {t rho sigma epsilon buffer gamma : ℝ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (ht : 0 ≤ t)
    (hgamma : 0 < gamma)
    (hthreshold : ∀ n ∈ checks, 0 < threshold n)
    (hintensity : ∀ n ∈ checks,
      rho * (n : ℝ) - epsilon ≤
        ∑ p ∈ fiveDepthPrefixCarrier R
            (normalizedLogDepth T) (depth n),
          r p.1 / 3)
    (hrequest : ∀ n ∈ checks,
      ((threshold n - 1 : ℕ) : ℝ) ≤
        sigma * (n : ℝ) - buffer)
    (hgap :
      gamma ≤ (1 - Real.exp (-t)) * rho - t * sigma) :
    1 -
        4 * Real.exp
          (-t * buffer + (1 - Real.exp (-t)) * epsilon) /
            (1 - Real.exp (-gamma)) ≤
      fiveEventMass R r
        (fiveIndexedPrefixProfileSuccess
          R T checks depth threshold) := by
  change
    1 -
        4 * Real.exp
          (-t * buffer + (1 - Real.exp (-t)) * epsilon) /
            (1 - Real.exp (-gamma)) ≤
      fiveEventMass R r
        (fun c ↦
          !(fiveIndexedPrefixProfileFailure
            R T checks depth threshold c))
  rw [fiveEventMass_complement]
  have hfailure :=
    fivePrefixProfileFailureMass_le_geometric
      (T := T) (depth := depth)
      hr0 hr1 ht hgamma hthreshold
      hintensity hrequest hgap
  linarith

/-! ## The manuscript's numerical slopes -/

/-- Exact numerical gap for the tilt `1/50`, intensity rate `1/3`, and
profile slope `8/25`.  A convenient smaller gap `1/10000` is retained
for the geometric series. -/
theorem numericalFivePrefixChernoffGap :
    (1 / 10000 : ℝ) ≤
      (1 - Real.exp (-(1 / 50 : ℝ))) * (1 / 3 : ℝ) -
        (1 / 50 : ℝ) * (8 / 25 : ℝ) := by
  have hexp :
      (1 : ℝ) + 1 / 50 ≤ Real.exp (1 / 50 : ℝ) :=
    by simpa [add_comm] using Real.add_one_le_exp (1 / 50 : ℝ)
  have hinv :
      Real.exp (-(1 / 50 : ℝ)) ≤
        1 / ((1 : ℝ) + 1 / 50) := by
    rw [Real.exp_neg]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by norm_num) hexp
  norm_num at hinv ⊢
  linarith

/-- Numerical horizon-uniform failure estimate matching the lower-profile
constants in the manuscript. -/
theorem fivePrefixProfileFailureMass_le_numerical
    {R : Finset ℕ} {r : ℕ → ℝ} {T : ℝ}
    {checks : Finset ℕ} {depth : ℕ → ℝ}
    {threshold : ℕ → ℕ} {epsilon buffer : ℝ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (hthreshold : ∀ n ∈ checks, 0 < threshold n)
    (hintensity : ∀ n ∈ checks,
      (1 / 3 : ℝ) * (n : ℝ) - epsilon ≤
        ∑ p ∈ fiveDepthPrefixCarrier R
            (normalizedLogDepth T) (depth n),
          r p.1 / 3)
    (hrequest : ∀ n ∈ checks,
      ((threshold n - 1 : ℕ) : ℝ) ≤
        (8 / 25 : ℝ) * (n : ℝ) - buffer) :
    fiveEventMass R r
        (fiveIndexedPrefixProfileFailure
          R T checks depth threshold) ≤
      4 * Real.exp
          (-(1 / 50 : ℝ) * buffer +
            (1 - Real.exp (-(1 / 50 : ℝ))) * epsilon) /
        (1 - Real.exp (-(1 / 10000 : ℝ))) := by
  exact fivePrefixProfileFailureMass_le_geometric
    (T := T) (depth := depth)
    hr0 hr1 (by norm_num) (by norm_num)
    hthreshold hintensity hrequest numericalFivePrefixChernoffGap

/-- Eventual scale-uniform version of the numerical estimate.  The prime
band, checked horizon, and thresholds may all vary with the scale `N`;
the upper bound does not. -/
theorem eventually_fivePrefixProfileFailureMass_le_numerical
    {R : ℕ → Finset ℕ} {r : ℕ → ℝ}
    {scale : ℕ → ℝ} {checks : ℕ → Finset ℕ}
    {depth : ℕ → ℕ → ℝ} {threshold : ℕ → ℕ → ℕ}
    {epsilon buffer : ℝ}
    (hr0 : ∀ (N p : ℕ), p ∈ R N → 0 ≤ r p)
    (hr1 : ∀ (N p : ℕ), p ∈ R N → r p ≤ 3 / 4)
    (hthreshold : ∀ᶠ N : ℕ in atTop,
      ∀ n ∈ checks N, 0 < threshold N n)
    (hintensity : ∀ᶠ N : ℕ in atTop,
      ∀ n ∈ checks N,
        (1 / 3 : ℝ) * (n : ℝ) - epsilon ≤
          ∑ p ∈ fiveDepthPrefixCarrier (R N)
              (normalizedLogDepth (scale N)) (depth N n),
            r p.1 / 3)
    (hrequest : ∀ᶠ N : ℕ in atTop,
      ∀ n ∈ checks N,
        ((threshold N n - 1 : ℕ) : ℝ) ≤
          (8 / 25 : ℝ) * (n : ℝ) - buffer) :
    ∀ᶠ N : ℕ in atTop,
      fiveEventMass (R N) r
          (fiveIndexedPrefixProfileFailure
            (R N) (scale N) (checks N)
              (depth N) (threshold N)) ≤
        4 * Real.exp
            (-(1 / 50 : ℝ) * buffer +
              (1 - Real.exp (-(1 / 50 : ℝ))) * epsilon) /
          (1 - Real.exp (-(1 / 10000 : ℝ))) := by
  filter_upwards [hthreshold, hintensity, hrequest] with
    N hthresholdN hintensityN hrequestN
  exact fivePrefixProfileFailureMass_le_numerical
    (T := scale N) (depth := depth N)
    (hr0 N) (hr1 N) hthresholdN hintensityN hrequestN

/-! ## Arbitrary carriers

The residual tail after installing a fixed buffer is most naturally
described by a family of finite carriers rather than by full depth
prefixes.  The same proof applies verbatim to these carriers.
-/

/-- Failure of an indexed lower-count profile on arbitrary carriers. -/
noncomputable def fiveIndexedCarrierProfileFailure
    (R : Finset ℕ) (checks : Finset ℕ)
    (carrier : ℕ → Finset ↥R) (threshold : ℕ → ℕ)
    (c : FiveConfiguration R) : Bool :=
  decide (∃ l : ActiveFiveLabel, ∃ n ∈ checks,
    fiveActiveLabelCountOn (carrier n) l c < threshold n)

@[simp]
theorem fiveIndexedCarrierProfileFailure_iff
    {R : Finset ℕ} {checks : Finset ℕ}
    {carrier : ℕ → Finset ↥R} {threshold : ℕ → ℕ}
    {c : FiveConfiguration R} :
    fiveIndexedCarrierProfileFailure
        R checks carrier threshold c ↔
      ∃ l : ActiveFiveLabel, ∃ n ∈ checks,
        fiveActiveLabelCountOn (carrier n) l c < threshold n := by
  simp [fiveIndexedCarrierProfileFailure]

private theorem fiveCarrierFailureAt_mass_eq_lowerTail
    {R : Finset ℕ} {r : ℕ → ℝ}
    {carrier : ℕ → Finset ↥R} {threshold : ℕ → ℕ}
    {l : ActiveFiveLabel} {n : ℕ}
    (hthreshold : 0 < threshold n) :
    finiteBoolEventMass
        (Finset.univ : Finset (FiveConfiguration R))
        (fiveConfigurationWeight R r)
        (fun c ↦ decide
          (fiveActiveLabelCountOn (carrier n) l c < threshold n)) =
      fiveActiveLabelLowerTailMass R r
        (carrier n) l (threshold n - 1) := by
  rw [finiteBoolEventMass, fiveActiveLabelLowerTailMass]
  apply Finset.sum_congr rfl
  intro c _hc
  by_cases hfail :
      fiveActiveLabelCountOn (carrier n) l c < threshold n
  · have htail :
        fiveActiveLabelCountOn (carrier n) l c ≤
          threshold n - 1 := by
      omega
    simp [hfail, htail]
  · have htail :
        ¬fiveActiveLabelCountOn (carrier n) l c ≤
          threshold n - 1 := by
      omega
    simp [hfail, htail]

/-- Exact finite union/Chernoff estimate on arbitrary carriers. -/
theorem fiveCarrierProfileFailureMass_le
    {R : Finset ℕ} {r : ℕ → ℝ} {t : ℝ}
    {checks : Finset ℕ} {carrier : ℕ → Finset ↥R}
    {threshold : ℕ → ℕ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (ht : 0 ≤ t)
    (hthreshold : ∀ n ∈ checks, 0 < threshold n) :
    fiveEventMass R r
        (fiveIndexedCarrierProfileFailure
          R checks carrier threshold) ≤
      ∑ i : ActiveFiveLabel × ↥checks,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ carrier i.2.1, r p.1 / 3) := by
  classical
  let I : Finset (ActiveFiveLabel × ↥checks) := Finset.univ
  let E : (ActiveFiveLabel × ↥checks) →
      FiveConfiguration R → Bool :=
    fun i c ↦ decide
      (fiveActiveLabelCountOn (carrier i.2.1) i.1 c <
        threshold i.2.1)
  have hunion :
      finiteBoolEventUnion I E =
        fiveIndexedCarrierProfileFailure
          R checks carrier threshold := by
    funext c
    apply Bool.eq_iff_iff.mpr
    simp [I, E, fiveIndexedCarrierProfileFailure,
      finiteBoolEventUnion]
  have hmass :=
    finiteBoolEventUnion_mass_le_sum I
      (Finset.univ : Finset (FiveConfiguration R))
      (fiveConfigurationWeight R r) E
      (fun c _hc ↦
        fiveConfigurationWeight_nonneg_of_bounds hr0 hr1 c)
  rw [hunion] at hmass
  have hleft :
      finiteBoolEventMass
          (Finset.univ : Finset (FiveConfiguration R))
          (fiveConfigurationWeight R r)
          (fiveIndexedCarrierProfileFailure
            R checks carrier threshold) =
        fiveEventMass R r
          (fiveIndexedCarrierProfileFailure
            R checks carrier threshold) := by
    rw [finiteBoolEventMass, fiveEventMass]
  rw [hleft] at hmass
  calc
    fiveEventMass R r
        (fiveIndexedCarrierProfileFailure
          R checks carrier threshold) ≤
      ∑ i ∈ I,
        finiteBoolEventMass
          (Finset.univ : Finset (FiveConfiguration R))
          (fiveConfigurationWeight R r) (E i) :=
      hmass
    _ ≤ ∑ i ∈ I,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ carrier i.2.1, r p.1 / 3) := by
      apply Finset.sum_le_sum
      intro i hi
      have hpos := hthreshold i.2.1 i.2.2
      rw [show E i = fun c ↦ decide
          (fiveActiveLabelCountOn (carrier i.2.1) i.1 c <
            threshold i.2.1) by rfl]
      rw [fiveCarrierFailureAt_mass_eq_lowerTail hpos]
      exact fiveActiveLabelLowerTailMass_le hr0 hr1 ht
    _ = ∑ i : ActiveFiveLabel × ↥checks,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ carrier i.2.1, r p.1 / 3) := by
      simp [I]

/-- Horizon-uniform geometric bound for arbitrary carriers. -/
theorem fiveCarrierProfileFailureMass_le_geometric
    {R : Finset ℕ} {r : ℕ → ℝ}
    {checks : Finset ℕ} {carrier : ℕ → Finset ↥R}
    {threshold : ℕ → ℕ}
    {t rho sigma epsilon buffer gamma : ℝ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (ht : 0 ≤ t)
    (hgamma : 0 < gamma)
    (hthreshold : ∀ n ∈ checks, 0 < threshold n)
    (hintensity : ∀ n ∈ checks,
      rho * (n : ℝ) - epsilon ≤
        ∑ p ∈ carrier n, r p.1 / 3)
    (hrequest : ∀ n ∈ checks,
      ((threshold n - 1 : ℕ) : ℝ) ≤
        sigma * (n : ℝ) - buffer)
    (hgap :
      gamma ≤ (1 - Real.exp (-t)) * rho - t * sigma) :
    fiveEventMass R r
        (fiveIndexedCarrierProfileFailure
          R checks carrier threshold) ≤
      4 * Real.exp
          (-t * buffer + (1 - Real.exp (-t)) * epsilon) /
        (1 - Real.exp (-gamma)) := by
  classical
  have htheta : 0 ≤ 1 - Real.exp (-t) := by
    rw [sub_nonneg, Real.exp_le_one_iff]
    linarith
  have hbase :=
    fiveCarrierProfileFailureMass_le
      (carrier := carrier) hr0 hr1 ht hthreshold
  let C : ℝ :=
    Real.exp
      (-t * buffer + (1 - Real.exp (-t)) * epsilon)
  let q : ℝ := Real.exp (-gamma)
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := by
    dsimp [q]
    rw [Real.exp_lt_one_iff]
    linarith
  have hterm (n : ↥checks) :
      Real.exp
          (t * ((threshold n.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ carrier n.1, r p.1 / 3) ≤
        C * q ^ n.1 := by
    have hi := hintensity n.1 n.2
    have hk := hrequest n.1 n.2
    have hn : (0 : ℝ) ≤ n.1 := by positivity
    have hexponent :
        t * ((threshold n.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ carrier n.1, r p.1 / 3 ≤
          -t * buffer +
            (1 - Real.exp (-t)) * epsilon -
              gamma * (n.1 : ℝ) := by
      have hgapn :
          (t * sigma -
              (1 - Real.exp (-t)) * rho) * (n.1 : ℝ) ≤
            -gamma * (n.1 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ hn
        linarith
      calc
        t * ((threshold n.1 - 1 : ℕ) : ℝ) +
              (Real.exp (-t) - 1) *
                ∑ p ∈ carrier n.1, r p.1 / 3 =
            t * ((threshold n.1 - 1 : ℕ) : ℝ) -
              (1 - Real.exp (-t)) *
                ∑ p ∈ carrier n.1, r p.1 / 3 := by ring
        _ ≤ t * (sigma * (n.1 : ℝ) - buffer) -
              (1 - Real.exp (-t)) *
                (rho * (n.1 : ℝ) - epsilon) := by
          gcongr
        _ =
            -t * buffer +
              (1 - Real.exp (-t)) * epsilon +
                (t * sigma -
                  (1 - Real.exp (-t)) * rho) *
                    (n.1 : ℝ) := by ring
        _ ≤ -t * buffer +
              (1 - Real.exp (-t)) * epsilon -
                gamma * (n.1 : ℝ) := by
          linarith
    calc
      Real.exp
          (t * ((threshold n.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ carrier n.1, r p.1 / 3) ≤
          Real.exp
            (-t * buffer +
              (1 - Real.exp (-t)) * epsilon -
                gamma * (n.1 : ℝ)) :=
        Real.exp_le_exp.mpr hexponent
      _ = C * q ^ n.1 := by
        dsimp [C, q]
        rw [show
          -t * buffer + (1 - Real.exp (-t)) * epsilon -
                gamma * (n.1 : ℝ) =
            (-t * buffer + (1 - Real.exp (-t)) * epsilon) +
              (n.1 : ℝ) * (-gamma) by ring,
          Real.exp_add, Real.exp_nat_mul]
  have hfinite :
      (∑ n : ↥checks, q ^ n.1) ≤ (1 - q)⁻¹ := by
    have hs : Summable (fun n : ℕ ↦ q ^ n) :=
      summable_geometric_of_lt_one hq0 hq1
    calc
      (∑ n : ↥checks, q ^ n.1) =
          ∑ n ∈ checks, q ^ n := by
        rw [Finset.univ_eq_attach, Finset.sum_attach]
      _ ≤ ∑' n : ℕ, q ^ n :=
        hs.sum_le_tsum checks (fun n _hn ↦ pow_nonneg hq0 n)
      _ = (1 - q)⁻¹ :=
        tsum_geometric_of_lt_one hq0 hq1
  calc
    fiveEventMass R r
        (fiveIndexedCarrierProfileFailure
          R checks carrier threshold) ≤
      ∑ i : ActiveFiveLabel × ↥checks,
        Real.exp
          (t * ((threshold i.2.1 - 1 : ℕ) : ℝ) +
            (Real.exp (-t) - 1) *
              ∑ p ∈ carrier i.2.1, r p.1 / 3) :=
      hbase
    _ ≤ ∑ i : ActiveFiveLabel × ↥checks,
        C * q ^ i.2.1 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact hterm i.2
    _ = 4 * (C * ∑ n : ↥checks, q ^ n.1) := by
      rw [Fintype.sum_prod_type]
      simp
      rw [Finset.mul_sum]
    _ ≤ 4 * (C * (1 - q)⁻¹) := by
      have hC : 0 ≤ C := (Real.exp_pos _).le
      gcongr
    _ =
      4 * Real.exp
          (-t * buffer + (1 - Real.exp (-t)) * epsilon) /
        (1 - Real.exp (-gamma)) := by
      dsimp [C, q]
      rw [div_eq_mul_inv]
      ring

/-- Numerical arbitrary-carrier specialization. -/
theorem fiveCarrierProfileFailureMass_le_numerical
    {R : Finset ℕ} {r : ℕ → ℝ}
    {checks : Finset ℕ} {carrier : ℕ → Finset ↥R}
    {threshold : ℕ → ℕ} {epsilon buffer : ℝ}
    (hr0 : ∀ p ∈ R, 0 ≤ r p)
    (hr1 : ∀ p ∈ R, r p ≤ 3 / 4)
    (hthreshold : ∀ n ∈ checks, 0 < threshold n)
    (hintensity : ∀ n ∈ checks,
      (1 / 3 : ℝ) * (n : ℝ) - epsilon ≤
        ∑ p ∈ carrier n, r p.1 / 3)
    (hrequest : ∀ n ∈ checks,
      ((threshold n - 1 : ℕ) : ℝ) ≤
        (8 / 25 : ℝ) * (n : ℝ) - buffer) :
    fiveEventMass R r
        (fiveIndexedCarrierProfileFailure
          R checks carrier threshold) ≤
      4 * Real.exp
          (-(1 / 50 : ℝ) * buffer +
            (1 - Real.exp (-(1 / 50 : ℝ))) * epsilon) /
        (1 - Real.exp (-(1 / 10000 : ℝ))) := by
  exact fiveCarrierProfileFailureMass_le_geometric
    hr0 hr1 (by norm_num) (by norm_num)
    hthreshold hintensity hrequest numericalFivePrefixChernoffGap

end Erdos536
