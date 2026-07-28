import Erdos390.WholePaper.RoughHeadCompatibleFinitePoint

/-!
# Fixed-modulus reduced-residue counts

This file proves the elementary `O_W(1)` input used in the rough selector
and in the tangent-list census.  A reduced-residue predicate is counted on
literal finite intervals by splitting the interval into complete periods
and one remainder.  Multiples of a number coprime to the fixed modulus are
then reindexed exactly by division.

There is no prime-number theorem, smooth-number estimate, or asymptotic
hypothesis in this module.  The final CRT-style error constant is the
explicit number `M + 1`, independent of the multiplier and the interval.
-/

namespace Erdos390.WholePaper

noncomputable section

/-- Reduced residues in a half-open segment `[start,start+length)`. -/
def reducedResidueSegment
    (M start length : ℕ) : Finset ℕ :=
  (Finset.Ico start (start + length)).filter
    (fun a ↦ Nat.Coprime a M)

/-- Reduced residues in the paper's physical interval `(lo,hi]`. -/
def reducedResidueIoc
    (M lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter (fun a ↦ Nat.Coprime a M)

/-- Integers in `(lo,hi]` which are both divisible by `D` and coprime to
the fixed modulus `M`. -/
def coprimeMultipleIoc
    (M D lo hi : ℕ) : Finset ℕ :=
  (Finset.Ioc lo hi).filter
    (fun a ↦ D ∣ a ∧ Nat.Coprime a M)

/-- The exact reduced-residue density `phi(M)/M`. -/
def fixedModulusReducedResidueDensity (M : ℕ) : ℝ :=
  (M.totient : ℝ) / (M : ℝ)

/-! ## Exact periodic decomposition -/

/-- Splitting a segment after `first` tokens splits the finite set itself. -/
theorem reducedResidueSegment_add
    (M start first second : ℕ) :
    reducedResidueSegment M start (first + second) =
      reducedResidueSegment M start first ∪
        reducedResidueSegment M (start + first) second := by
  ext a
  simp only [reducedResidueSegment, Finset.mem_filter,
    Finset.mem_Ico, Finset.mem_union]
  omega

/-- The two pieces in `reducedResidueSegment_add` are disjoint. -/
theorem reducedResidueSegment_disjoint
    (M start first second : ℕ) :
    Disjoint (reducedResidueSegment M start first)
      (reducedResidueSegment M (start + first) second) := by
  rw [Finset.disjoint_left]
  intro a haFirst haSecond
  simp only [reducedResidueSegment, Finset.mem_filter,
    Finset.mem_Ico] at haFirst haSecond
  omega

/-- Cardinalities add under the literal segment split. -/
theorem reducedResidueSegment_card_add
    (M start first second : ℕ) :
    (reducedResidueSegment M start (first + second)).card =
      (reducedResidueSegment M start first).card +
        (reducedResidueSegment M (start + first) second).card := by
  rw [reducedResidueSegment_add,
    Finset.card_union_of_disjoint
      (reducedResidueSegment_disjoint M start first second)]

/-- Every complete interval of length `M` contains exactly `phi(M)`
reduced residues, regardless of its starting point. -/
theorem reducedResidueSegment_card_period
    (M start : ℕ) :
    (reducedResidueSegment M start M).card = M.totient := by
  simpa only [reducedResidueSegment, Nat.coprime_comm] using
    Nat.filter_coprime_Ico_eq_totient M start

/-- `q` complete periods contain exactly `q * phi(M)` reduced residues. -/
theorem reducedResidueSegment_card_fullBlocks
    (M start q : ℕ) :
    (reducedResidueSegment M start (q * M)).card =
      q * M.totient := by
  induction q generalizing start with
  | zero => simp [reducedResidueSegment]
  | succ q ih =>
      calc
        (reducedResidueSegment M start ((q + 1) * M)).card =
            (reducedResidueSegment M start (q * M)).card +
              (reducedResidueSegment M (start + q * M) M).card := by
          rw [Nat.succ_mul, reducedResidueSegment_card_add]
        _ = q * M.totient + M.totient := by
          rw [ih, reducedResidueSegment_card_period]
        _ = (q + 1) * M.totient := by ring

/-- Exact quotient-and-remainder formula for every finite segment. -/
theorem reducedResidueSegment_card_eq_fullBlocks_add_remainder
    (M start length : ℕ) :
    (reducedResidueSegment M start length).card =
      (length / M) * M.totient +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card := by
  have hlength :
      length = (length / M) * M + length % M := by
    calc
      length = length % M + M * (length / M) :=
        (Nat.mod_add_div length M).symm
      _ = (length / M) * M + length % M := by ac_rfl
  calc
    (reducedResidueSegment M start length).card =
        (reducedResidueSegment M start
          ((length / M) * M + length % M)).card :=
      congrArg (fun segmentLength ↦
        (reducedResidueSegment M start segmentLength).card) hlength
    _ = (reducedResidueSegment M start ((length / M) * M)).card +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card :=
      reducedResidueSegment_card_add M start
        ((length / M) * M) (length % M)
    _ = (length / M) * M.totient +
        (reducedResidueSegment M
          (start + (length / M) * M) (length % M)).card := by
      rw [reducedResidueSegment_card_fullBlocks]

/-- A filtered segment contains at most its literal number of tokens. -/
theorem reducedResidueSegment_card_le_length
    (M start length : ℕ) :
    (reducedResidueSegment M start length).card ≤ length := by
  unfold reducedResidueSegment
  calc
    ((Finset.Ico start (start + length)).filter
        (fun a ↦ Nat.Coprime a M)).card ≤
      (Finset.Ico start (start + length)).card :=
        Finset.card_filter_le _ _
    _ = length := by simp

/-- A physical `(lo,hi]` interval is literally the corresponding shifted
half-open segment. -/
theorem reducedResidueIoc_eq_segment
    {M lo hi : ℕ} (hlohi : lo ≤ hi) :
    reducedResidueIoc M lo hi =
      reducedResidueSegment M (lo + 1) (hi - lo) := by
  ext a
  simp only [reducedResidueIoc, reducedResidueSegment,
    Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Ico]
  omega

/-! ## Explicit fixed-period error -/

/-- The exact endpoint error is bounded by the length of the incomplete
period, not merely by an unspecified modulus-dependent constant. -/
theorem reducedResidueSegment_card_error_le_mod
    {M : ℕ} (hM : 0 < M) (start length : ℕ) :
    |((reducedResidueSegment M start length).card : ℝ) -
        fixedModulusReducedResidueDensity M * (length : ℝ)| ≤
      ((length % M : ℕ) : ℝ) := by
  let q := length / M
  let r := length % M
  let remainderCard :=
    (reducedResidueSegment M (start + q * M) r).card
  have hcount :
      (reducedResidueSegment M start length).card =
        q * M.totient + remainderCard := by
    simpa only [q, r, remainderCard] using
      reducedResidueSegment_card_eq_fullBlocks_add_remainder
        M start length
  have hlength : length = q * M + r := by
    dsimp only [q, r]
    calc
      length = length % M + M * (length / M) :=
        (Nat.mod_add_div length M).symm
      _ = (length / M) * M + length % M := by ac_rfl
  have hremainderLeNat : remainderCard ≤ r := by
    dsimp only [remainderCard]
    exact reducedResidueSegment_card_le_length M (start + q * M) r
  have hremainderLe : (remainderCard : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast hremainderLeNat
  have hMRealPos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hM
  have hMReal : (M : ℝ) ≠ 0 := hMRealPos.ne'
  have htotientLe : (M.totient : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.totient_le M
  have hdensityNonneg :
      0 ≤ fixedModulusReducedResidueDensity M := by
    exact div_nonneg (Nat.cast_nonneg _) hMRealPos.le
  have hdensityLeOne :
      fixedModulusReducedResidueDensity M ≤ 1 := by
    rw [fixedModulusReducedResidueDensity]
    exact (div_le_one hMRealPos).2 htotientLe
  have hmainNonneg :
      0 ≤ fixedModulusReducedResidueDensity M * (r : ℝ) :=
    mul_nonneg hdensityNonneg (Nat.cast_nonneg _)
  have hmainLe :
      fixedModulusReducedResidueDensity M * (r : ℝ) ≤ (r : ℝ) := by
    calc
      fixedModulusReducedResidueDensity M * (r : ℝ) ≤
          1 * (r : ℝ) :=
        mul_le_mul_of_nonneg_right hdensityLeOne (Nat.cast_nonneg _)
      _ = (r : ℝ) := one_mul _
  have herror :
      ((reducedResidueSegment M start length).card : ℝ) -
          fixedModulusReducedResidueDensity M * (length : ℝ) =
        (remainderCard : ℝ) -
          fixedModulusReducedResidueDensity M * (r : ℝ) := by
    rw [hcount, hlength]
    simp only [fixedModulusReducedResidueDensity, Nat.cast_add,
      Nat.cast_mul]
    field_simp [hMReal]
    ring
  have hremainderNonneg : (0 : ℝ) ≤ (remainderCard : ℝ) := by
    exact Nat.cast_nonneg remainderCard
  rw [herror, abs_le]
  constructor <;> linarith

/-- Physical-interval form of the exact remainder bound. -/
theorem reducedResidueIoc_card_error_le_mod
    {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((reducedResidueIoc M lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M * ((hi - lo : ℕ) : ℝ)| ≤
      (((hi - lo) % M : ℕ) : ℝ) := by
  rw [reducedResidueIoc_eq_segment hlohi]
  exact reducedResidueSegment_card_error_le_mod hM (lo + 1) (hi - lo)

/-- Coarser but convenient `O_M(1)` form with the explicit constant `M`. -/
theorem reducedResidueIoc_card_error_le_modulus
    {M lo hi : ℕ} (hM : 0 < M) (hlohi : lo ≤ hi) :
    |((reducedResidueIoc M lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M * ((hi - lo : ℕ) : ℝ)| ≤
      (M : ℝ) := by
  exact (reducedResidueIoc_card_error_le_mod hM hlohi).trans
    (by exact_mod_cast (Nat.mod_lt (hi - lo) hM).le)

/-! ## Exact CRT reindexing and multiplier-independent error -/

/-- Multiplication by `D` gives an exact bijection between coprime
multiples in `(lo,hi]` and reduced residues in `(lo/D,hi/D]`. -/
theorem coprimeMultipleIoc_card_eq_reducedResidueIoc
    {M D lo hi : ℕ} (hD : 0 < D) (hDM : Nat.Coprime D M) :
    (coprimeMultipleIoc M D lo hi).card =
      (reducedResidueIoc M (lo / D) (hi / D)).card := by
  apply Finset.card_bij (fun a _ha ↦ a / D)
  · intro a ha
    simp only [coprimeMultipleIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha
    obtain ⟨haInterval, hDvd, hcoprime⟩ := ha
    simp only [reducedResidueIoc, Finset.mem_filter,
      Finset.mem_Ioc]
    refine ⟨⟨(Nat.div_lt_iff_lt_mul hD).mpr ?_,
      (Nat.le_div_iff_mul_le hD).mpr ?_⟩, ?_⟩
    · simpa [Nat.div_mul_cancel hDvd] using haInterval.1
    · simpa [Nat.div_mul_cancel hDvd] using haInterval.2
    · rw [← Nat.div_mul_cancel hDvd] at hcoprime
      exact (Nat.coprime_mul_iff_left.mp hcoprime).1
  · intro a₁ ha₁ a₂ ha₂ heq
    simp only [coprimeMultipleIoc, Finset.mem_filter,
      Finset.mem_Ioc] at ha₁ ha₂
    calc
      a₁ = a₁ / D * D := (Nat.div_mul_cancel ha₁.2.1).symm
      _ = a₂ / D * D := by rw [heq]
      _ = a₂ := Nat.div_mul_cancel ha₂.2.1
  · intro b hb
    simp only [reducedResidueIoc, Finset.mem_filter,
      Finset.mem_Ioc] at hb
    refine ⟨b * D, ?_, ?_⟩
    · simp only [coprimeMultipleIoc, Finset.mem_filter,
        Finset.mem_Ioc]
      refine ⟨⟨(Nat.div_lt_iff_lt_mul hD).mp hb.1.1,
        (Nat.le_div_iff_mul_le hD).mp hb.1.2⟩, by simp, ?_⟩
      exact Nat.coprime_mul_iff_left.mpr ⟨hb.2, hDM⟩
    · exact Nat.mul_div_left b hD

/-- Integer quotient lengths differ from real division by less than one.
This is the only extra endpoint cost after the exact multiplication
reindexing. -/
theorem quotientIocLength_sub_realLengthDiv_abs_lt_one
    {D lo hi : ℕ} (hD : 0 < D) (hlohi : lo ≤ hi) :
    |(((hi / D - lo / D : ℕ) : ℝ)) -
        ((hi - lo : ℕ) : ℝ) / (D : ℝ)| < 1 := by
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  have hDRealPos : (0 : ℝ) < (D : ℝ) := by
    exact_mod_cast hD
  have hDReal : (D : ℝ) ≠ 0 := hDRealPos.ne'
  have hhi := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div hi D)
  have hlo := congrArg (fun z : ℕ ↦ (z : ℝ)) (Nat.mod_add_div lo D)
  simp only [Nat.cast_add, Nat.cast_mul] at hhi hlo
  have herror :
      (((hi / D - lo / D : ℕ) : ℝ)) -
          ((hi - lo : ℕ) : ℝ) / (D : ℝ) =
        ((lo % D : ℕ) : ℝ) / (D : ℝ) -
          ((hi % D : ℕ) : ℝ) / (D : ℝ) := by
    rw [Nat.cast_sub hquotient, Nat.cast_sub hlohi]
    field_simp [hDReal]
    nlinarith [hhi, hlo]
  have hloMod : ((lo % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt lo hD
  have hhiMod : ((hi % D : ℕ) : ℝ) / (D : ℝ) < 1 := by
    apply (div_lt_one hDRealPos).2
    exact_mod_cast Nat.mod_lt hi hD
  have hloModNonneg :
      0 ≤ ((lo % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  have hhiModNonneg :
      0 ≤ ((hi % D : ℕ) : ℝ) / (D : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hDRealPos.le
  rw [herror, abs_lt]
  constructor <;> linarith

/-- CRT-style interval count with an explicit error independent of `D`:
for `D` coprime to `M`, the error is at most `M+1`. -/
theorem coprimeMultipleIoc_card_error_le
    {M D lo hi : ℕ} (hM : 0 < M) (hD : 0 < D)
    (hDM : Nat.Coprime D M) (hlohi : lo ≤ hi) :
    |((coprimeMultipleIoc M D lo hi).card : ℝ) -
        fixedModulusReducedResidueDensity M *
          (((hi - lo : ℕ) : ℝ) / (D : ℝ))| ≤
      (M : ℝ) + 1 := by
  rw [coprimeMultipleIoc_card_eq_reducedResidueIoc hD hDM]
  have hquotient : lo / D ≤ hi / D := Nat.div_le_div_right hlohi
  let quotientLength := hi / D - lo / D
  have hresidue := reducedResidueIoc_card_error_le_modulus
    hM hquotient
  have hresidue' :
      |((reducedResidueIoc M (lo / D) (hi / D)).card : ℝ) -
          fixedModulusReducedResidueDensity M *
            (quotientLength : ℝ)| ≤ (M : ℝ) := by
    simpa only [quotientLength] using hresidue
  have hfloor := quotientIocLength_sub_realLengthDiv_abs_lt_one hD hlohi
  have hMRealPos : (0 : ℝ) < (M : ℝ) := by
    exact_mod_cast hM
  have htotientLe : (M.totient : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast Nat.totient_le M
  have hdensityNonneg :
      0 ≤ fixedModulusReducedResidueDensity M :=
    div_nonneg (Nat.cast_nonneg _) hMRealPos.le
  have hdensityLeOne :
      fixedModulusReducedResidueDensity M ≤ 1 := by
    rw [fixedModulusReducedResidueDensity]
    exact (div_le_one hMRealPos).2 htotientLe
  have hscale :
      |fixedModulusReducedResidueDensity M *
          ((quotientLength : ℝ) -
            ((hi - lo : ℕ) : ℝ) / (D : ℝ))| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hdensityNonneg]
    calc
      fixedModulusReducedResidueDensity M *
          |(quotientLength : ℝ) -
            ((hi - lo : ℕ) : ℝ) / (D : ℝ)| ≤
          1 * 1 :=
        mul_le_mul hdensityLeOne
          (by simpa only [quotientLength] using hfloor.le)
          (abs_nonneg _) zero_le_one
      _ = 1 := mul_one _
  have hsplit :
      ((reducedResidueIoc M (lo / D) (hi / D)).card : ℝ) -
          fixedModulusReducedResidueDensity M *
            (((hi - lo : ℕ) : ℝ) / (D : ℝ)) =
        (((reducedResidueIoc M (lo / D) (hi / D)).card : ℝ) -
          fixedModulusReducedResidueDensity M *
            (quotientLength : ℝ)) +
        fixedModulusReducedResidueDensity M *
          ((quotientLength : ℝ) -
            ((hi - lo : ℕ) : ℝ) / (D : ℝ)) := by
    ring
  rw [hsplit]
  exact (abs_add_le _ _).trans (add_le_add hresidue' hscale)

/-! ## Paper-head specializations -/

/-- The fixed-head reduced-residue count with explicit error
`roughHeadModulus W`. -/
theorem roughHeadFree_Ioc_card_error_le
    {W lo hi : ℕ} (hlohi : lo ≤ hi) :
    |((roughHeadFree W (Finset.Ioc lo hi)).card : ℝ) -
        roughHeadDensity W * ((hi - lo : ℕ) : ℝ)| ≤
      (roughHeadModulus W : ℝ) := by
  simpa only [roughHeadFree, reducedResidueIoc,
    roughHeadDensity, fixedModulusReducedResidueDensity] using
    reducedResidueIoc_card_error_le_modulus
      (roughHeadModulus_pos W) hlohi

/-- The exact `O_W(1)` CRT estimate used for `p^k` multiples in Section 6
and fixed-head multiplier lists in Section 9. -/
theorem roughHeadCoprimeMultipleIoc_card_error_le
    {W D lo hi : ℕ} (hD : 0 < D)
    (hDHead : Nat.Coprime D (roughHeadModulus W))
    (hlohi : lo ≤ hi) :
    |((coprimeMultipleIoc (roughHeadModulus W) D lo hi).card : ℝ) -
        roughHeadDensity W *
          (((hi - lo : ℕ) : ℝ) / (D : ℝ))| ≤
      (roughHeadModulus W : ℝ) + 1 := by
  simpa only [roughHeadDensity, fixedModulusReducedResidueDensity] using
    coprimeMultipleIoc_card_error_le
      (roughHeadModulus_pos W) hD hDHead hlohi

/-- A prime strictly above the cutoff is coprime to the product of every
head prime at or below the cutoff. -/
theorem prime_coprime_roughHeadModulus_of_cutoff_lt
    {W p : ℕ} (hp : p.Prime) (hWp : W < p) :
    Nat.Coprime p (roughHeadModulus W) := by
  rw [roughHeadModulus, Nat.coprime_prod_right_iff]
  intro q hq
  have hqData := mem_primesUpTo.mp hq
  exact (Nat.coprime_primes hp hqData.1).mpr (by omega)

/-- Literal form of the Section 6 estimate
`#{a in I : p^k | a, (a,P_hd)=1} = delta_hd |I|/p^k + O_W(1)`.
The displayed bound `P_hd + 1` is valid for every exponent `k`. -/
theorem roughHeadPrimePowerMultipleIoc_card_error_le
    {W p k lo hi : ℕ} (hp : p.Prime) (hWp : W < p)
    (hlohi : lo ≤ hi) :
    |((coprimeMultipleIoc (roughHeadModulus W) (p ^ k) lo hi).card : ℝ) -
        roughHeadDensity W *
          (((hi - lo : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ))| ≤
      (roughHeadModulus W : ℝ) + 1 := by
  apply roughHeadCoprimeMultipleIoc_card_error_le
  · exact pow_pos hp.pos k
  · exact (prime_coprime_roughHeadModulus_of_cutoff_lt hp hWp).pow_left k
  · exact hlohi

end

end Erdos390.WholePaper
