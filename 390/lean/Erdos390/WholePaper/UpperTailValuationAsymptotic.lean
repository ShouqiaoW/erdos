import Erdos390.WholePaper.TailValuationTwoSided
import Erdos390.WholePaper.UpperScale

/-!
# Fixed-prime upper-tail valuation asymptotics

The paper's tail has length `ceil (c n / log n)` above `2n`.  The exact
integer two-sided Legendre bounds squeeze its valuation at every fixed prime.
The logarithmic remainder is discharged by `UpperScale`; no valuation limit
is assumed as an input.
-/

open Filter Topology

namespace Erdos390.WholePaper

noncomputable section

/-- The actual `p`-adic valuation contributed by the factorial tail
`(2n, 2n + upperTailLength c n]`. -/
def upperTailValuation (c : ℝ) (n p : ℕ) : ℕ :=
  (upperEndpoint n (upperTailLength c n)).factorial.factorization p -
    (2 * n).factorial.factorization p

/-- Real-cast form of the exact integer squeeze, with one common logarithmic
error valid whenever the tail length is at most `n`. -/
theorem upperTailValuation_cast_bounds
    {c : ℝ} {n p : ℕ} (hp : p.Prime)
    (htail : upperTailLength c n ≤ n) :
    (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) -
          ((Nat.log2 (3 * n) : ℝ) + 1) ≤
        (upperTailValuation c n p : ℝ) ∧
      (upperTailValuation c n p : ℝ) ≤
        (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) +
          ((Nat.log2 (3 * n) : ℝ) + 1) := by
  have htwo := factorialValuationSub_twoSided
    (a := 2 * n) (h := upperTailLength c n) (p := p) hp
  have hlowerNat :
      upperTailLength c n ≤ (p - 1) *
        (upperTailValuation c n p +
          Nat.log2 (upperTailLength c n) + 1) := by
    simpa only [upperTailValuation, upperEndpoint] using htwo.1
  have hupperNat :
      upperTailValuation c n p ≤
        upperTailLength c n / (p - 1) +
          Nat.log2 (upperEndpoint n (upperTailLength c n)) := by
    simpa only [upperTailValuation, upperEndpoint] using htwo.2
  have htailThree : upperTailLength c n ≤ 3 * n := by
    omega
  have hendpointThree :
      upperEndpoint n (upperTailLength c n) ≤ 3 * n :=
    upperEndpoint_le_three_mul htail
  have hlogTail :
      Nat.log2 (upperTailLength c n) ≤ Nat.log2 (3 * n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right htailThree
  have hlogEndpoint :
      Nat.log2 (upperEndpoint n (upperTailLength c n)) ≤
        Nat.log2 (3 * n) := by
    rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
    exact Nat.log_mono_right hendpointThree
  have hpredPosNat : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast hpredPosNat
  have hlowerCast :
      (upperTailLength c n : ℝ) ≤ ((p - 1 : ℕ) : ℝ) *
        ((upperTailValuation c n p : ℝ) +
          (Nat.log2 (upperTailLength c n) : ℝ) + 1) := by
    exact_mod_cast hlowerNat
  have hbaseLower :
      (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) ≤
        (upperTailValuation c n p : ℝ) +
          (Nat.log2 (upperTailLength c n) : ℝ) + 1 := by
    apply (div_le_iff₀ hpredPos).2
    simpa only [mul_comm] using hlowerCast
  have hlogTailCast :
      (Nat.log2 (upperTailLength c n) : ℝ) ≤
        (Nat.log2 (3 * n) : ℝ) := by
    exact_mod_cast hlogTail
  have hupperCast :
      (upperTailValuation c n p : ℝ) ≤
        (upperTailLength c n / (p - 1) : ℕ) +
          (Nat.log2 (upperEndpoint n (upperTailLength c n)) : ℝ) := by
    exact_mod_cast hupperNat
  have hdivCast :
      ((upperTailLength c n / (p - 1) : ℕ) : ℝ) ≤
        (upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) :=
    Nat.cast_div_le
  have hlogEndpointCast :
      (Nat.log2 (upperEndpoint n (upperTailLength c n)) : ℝ) ≤
        (Nat.log2 (3 * n) : ℝ) := by
    exact_mod_cast hlogEndpoint
  constructor <;> linarith

/-- Divide the finite squeeze by a positive second-order scale. -/
theorem upperTailValuation_normalized_bounds
    {c : ℝ} {n p : ℕ} (hp : p.Prime)
    (htail : upperTailLength c n ≤ n)
    (hscale : 0 < secondOrderScale n) :
    (upperTailLength c n : ℝ) / secondOrderScale n /
          ((p - 1 : ℕ) : ℝ) -
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n ≤
      (upperTailValuation c n p : ℝ) / secondOrderScale n ∧
    (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
      (upperTailLength c n : ℝ) / secondOrderScale n /
          ((p - 1 : ℕ) : ℝ) +
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
  have hbounds := upperTailValuation_cast_bounds hp htail
  have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt hp.one_lt
  constructor
  · calc
      (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ) -
          ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n =
        ((upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1)) /
          secondOrderScale n := by
            field_simp [hscale.ne', hpredPos.ne']
      _ ≤ (upperTailValuation c n p : ℝ) / secondOrderScale n :=
        div_le_div_of_nonneg_right hbounds.1 hscale.le
  · calc
      (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
          ((upperTailLength c n : ℝ) / ((p - 1 : ℕ) : ℝ) +
              ((Nat.log2 (3 * n) : ℝ) + 1)) /
            secondOrderScale n :=
        div_le_div_of_nonneg_right hbounds.2 hscale.le
      _ = (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ) +
          ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
            field_simp [hscale.ne', hpredPos.ne']

/-- The common binary-logarithmic error in the squeeze is negligible. -/
theorem upperTailLogError_normalized_tendsto_zero :
    Tendsto
      (fun n : ℕ ↦
        ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
      atTop (nhds 0) := by
  have hone :
      Tendsto (fun n : ℕ ↦ (1 : ℝ) / secondOrderScale n)
        atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop secondOrderScale_tendsto_atTop
  simpa only [add_div, add_zero] using
    log2_three_mul_normalized_tendsto_zero.add hone

/-- Paper (4.12): at every fixed prime, the actual factorial-tail valuation
has main term `c/(p-1)` on the scale `n/log n`. -/
theorem upperTailValuation_normalized_tendsto
    {c : ℝ} (hc : 0 < c) {p : ℕ} (hp : p.Prime) :
    Tendsto
      (fun n : ℕ ↦
        (upperTailValuation c n p : ℝ) / secondOrderScale n)
      atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
  have hmain :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
            ((p - 1 : ℕ) : ℝ))
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) :=
    (upperTailLength_normalized_tendsto hc).div_const
      ((p - 1 : ℕ) : ℝ)
  have hlower :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
    simpa only [sub_zero] using
      hmain.sub upperTailLogError_normalized_tendsto_zero
  have hupper :
      Tendsto
        (fun n : ℕ ↦
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) +
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n)
        atTop (nhds (c / ((p - 1 : ℕ) : ℝ))) := by
    simpa only [add_zero] using
      hmain.add upperTailLogError_normalized_tendsto_zero
  have hbounds :
      ∀ᶠ n : ℕ in atTop,
        (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) -
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n ≤
          (upperTailValuation c n p : ℝ) / secondOrderScale n ∧
        (upperTailValuation c n p : ℝ) / secondOrderScale n ≤
          (upperTailLength c n : ℝ) / secondOrderScale n /
              ((p - 1 : ℕ) : ℝ) +
            ((Nat.log2 (3 * n) : ℝ) + 1) / secondOrderScale n := by
    filter_upwards [eventually_upperTailLength_le hc,
      eventually_secondOrderScale_pos] with n htail hscale
    exact upperTailValuation_normalized_bounds hp htail hscale
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
    hlower hupper (hbounds.mono fun _ h ↦ h.1)
      (hbounds.mono fun _ h ↦ h.2)

/-- A finite set of fixed primes receives its prescribed strict lower reserve
simultaneously. -/
theorem eventually_upperTailValuation_normalized_ge_on_finset
    {c : ℝ} (hc : 0 < c) (primes : Finset ℕ) (reserve : ℕ → ℝ)
    (hprime : ∀ p ∈ primes, p.Prime)
    (hreserve : ∀ p ∈ primes,
      reserve p < c / ((p - 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      reserve p ≤
        (upperTailValuation c n p : ℝ) / secondOrderScale n := by
  rw [Finset.eventually_all]
  intro p hpMem
  exact (upperTailValuation_normalized_tendsto hc (hprime p hpMem)).eventually
    (eventually_ge_nhds (hreserve p hpMem))

/-- Equivalent finite-prime reserve after multiplying by the positive scale. -/
theorem eventually_upperTailValuation_ge_mul_scale_on_finset
    {c : ℝ} (hc : 0 < c) (primes : Finset ℕ) (reserve : ℕ → ℝ)
    (hprime : ∀ p ∈ primes, p.Prime)
    (hreserve : ∀ p ∈ primes,
      reserve p < c / ((p - 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      reserve p * secondOrderScale n ≤
        (upperTailValuation c n p : ℝ) := by
  have hratio := eventually_upperTailValuation_normalized_ge_on_finset
    hc primes reserve hprime hreserve
  filter_upwards [hratio, eventually_secondOrderScale_pos] with n hn hscale
  intro p hpMem
  exact (le_div_iff₀ hscale).mp (hn p hpMem)

/-- Natural-number form of the simultaneous reserve, suitable for direct
comparison with valuation demands. -/
theorem eventually_natCeil_reserve_le_upperTailValuation_on_finset
    {c : ℝ} (hc : 0 < c) (primes : Finset ℕ) (reserve : ℕ → ℝ)
    (hprime : ∀ p ∈ primes, p.Prime)
    (hreserve : ∀ p ∈ primes,
      reserve p < c / ((p - 1 : ℕ) : ℝ)) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      Nat.ceil (reserve p * secondOrderScale n) ≤
        upperTailValuation c n p := by
  have hreal := eventually_upperTailValuation_ge_mul_scale_on_finset
    hc primes reserve hprime hreserve
  filter_upwards [hreal] with n hn
  intro p hpMem
  exact Nat.ceil_le.mpr (hn p hpMem)

/-- A uniform positive slack `ε` gives a positive integral reserve
`ceil (((c-ε)/(p-1)) n/log n)` at every prime in a fixed finite set. -/
theorem eventually_positive_natCeil_sub_slack_reserve_le_on_finset
    {c ε : ℝ} (hc : 0 < c) (hε : 0 < ε) (hεc : ε < c)
    (primes : Finset ℕ) (hprime : ∀ p ∈ primes, p.Prime) :
    ∀ᶠ n : ℕ in atTop, ∀ p ∈ primes,
      0 < Nat.ceil
          (((c - ε) / ((p - 1 : ℕ) : ℝ)) * secondOrderScale n) ∧
        Nat.ceil
            (((c - ε) / ((p - 1 : ℕ) : ℝ)) * secondOrderScale n) ≤
          upperTailValuation c n p := by
  have hreserve : ∀ p ∈ primes,
      (c - ε) / ((p - 1 : ℕ) : ℝ) <
        c / ((p - 1 : ℕ) : ℝ) := by
    intro p hpMem
    have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_pos_of_lt (hprime p hpMem).one_lt
    exact div_lt_div_of_pos_right (sub_lt_self c hε) hpredPos
  have hle := eventually_natCeil_reserve_le_upperTailValuation_on_finset
    hc primes (fun p ↦ (c - ε) / ((p - 1 : ℕ) : ℝ)) hprime hreserve
  filter_upwards [hle, eventually_secondOrderScale_pos] with n hn hscale
  intro p hpMem
  have hpredPos : 0 < ((p - 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt (hprime p hpMem).one_lt
  have hcoefficientPos :
      0 < (c - ε) / ((p - 1 : ℕ) : ℝ) :=
    div_pos (sub_pos.mpr hεc) hpredPos
  exact ⟨Nat.ceil_pos.mpr (mul_pos hcoefficientPos hscale), hn p hpMem⟩

end

end Erdos390.WholePaper
