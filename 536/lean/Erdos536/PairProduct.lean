import Erdos536.Definitions

/-!
# Pair-product form of an LCM triangle

This file formalizes the elementary structural lemma from the manuscript.
For positive integers, equality of the three pairwise least common
multiples is equivalent to a common factor times the three pair-products
of pairwise coprime positive integers.
-/

open Finset Nat

namespace Erdos536

/-- The pair-product representation used throughout the manuscript. -/
def PairProductForm (a b c : ℕ) : Prop :=
  ∃ t x y z : ℕ,
    0 < t ∧ 0 < x ∧ 0 < y ∧ 0 < z ∧
      x.Coprime y ∧ x.Coprime z ∧ y.Coprime z ∧
      a = t * x * y ∧ b = t * x * z ∧ c = t * y * z

private theorem gcd_gcd_same_left (a b c : ℕ) :
    (a.gcd b).gcd (a.gcd c) = a.gcd (b.gcd c) := by
  apply Nat.dvd_antisymm
  · apply Nat.dvd_gcd
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    · apply Nat.dvd_gcd
      · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  · apply Nat.dvd_gcd
    · apply Nat.dvd_gcd
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
    · apply Nat.dvd_gcd
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)

private theorem triple_gcd_swap_left (a b c : ℕ) :
    b.gcd (a.gcd c) = a.gcd (b.gcd c) := by
  rw [← Nat.gcd_assoc, Nat.gcd_comm b a, Nat.gcd_assoc]

private theorem triple_gcd_rotate (a b c : ℕ) :
    c.gcd (a.gcd b) = a.gcd (b.gcd c) := by
  rw [← Nat.gcd_assoc, Nat.gcd_comm c a, Nat.gcd_assoc,
    Nat.gcd_comm c b]

/-- Pair-product form. Positivity is the only ambient assumption needed for
the structural equivalence; pairwise distinctness enters in
`isLcmTriangle_iff_pairProduct` below. -/
theorem equal_pairwise_lcm_iff_pairProduct
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (a.lcm b = a.lcm c ∧ a.lcm c = b.lcm c) ↔
      PairProductForm a b c := by
  constructor
  · rintro ⟨hab, hac⟩
    have ha0 : a ≠ 0 := Nat.ne_of_gt ha
    have hb0 : b ≠ 0 := Nat.ne_of_gt hb
    have hc0 : c ≠ 0 := Nat.ne_of_gt hc
    let t := a.gcd (b.gcd c)
    let gx := a.gcd b
    let gy := a.gcd c
    let gz := b.gcd c
    let x := gx / t
    let y := gy / t
    let z := gz / t
    have hgbc_pos : 0 < b.gcd c := Nat.gcd_pos_of_pos_left c hb
    have ht_pos : 0 < t := by
      dsimp [t]
      exact Nat.gcd_pos_of_pos_left _ ha
    have hgx_pos : 0 < gx := by
      dsimp [gx]
      exact Nat.gcd_pos_of_pos_left _ ha
    have hgy_pos : 0 < gy := by
      dsimp [gy]
      exact Nat.gcd_pos_of_pos_left _ ha
    have hgz_pos : 0 < gz := by
      dsimp [gz]
      exact Nat.gcd_pos_of_pos_left _ hb
    have htx : t ∣ gx := by
      dsimp [t, gx]
      exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
    have hty : t ∣ gy := by
      dsimp [t, gy]
      exact Nat.dvd_gcd (Nat.gcd_dvd_left _ _)
        ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
    have htz : t ∣ gz := by
      dsimp [t, gz]
      exact Nat.dvd_gcd
        ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _))
        ((Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _))
    have hx_pos : 0 < x := by
      exact Nat.div_pos (Nat.le_of_dvd hgx_pos htx) ht_pos
    have hy_pos : 0 < y := by
      exact Nat.div_pos (Nat.le_of_dvd hgy_pos hty) ht_pos
    have hz_pos : 0 < z := by
      exact Nat.div_pos (Nat.le_of_dvd hgz_pos htz) ht_pos
    have hgxy : gx.gcd gy = t := by
      dsimp [gx, gy, t]
      exact gcd_gcd_same_left a b c
    have hgxz : gx.gcd gz = t := by
      dsimp [gx, gz, t]
      calc
        (a.gcd b).gcd (b.gcd c) =
            (b.gcd a).gcd (b.gcd c) := by rw [Nat.gcd_comm a b]
        _ = b.gcd (a.gcd c) := gcd_gcd_same_left b a c
        _ = a.gcd (b.gcd c) := triple_gcd_swap_left a b c
    have hgyz : gy.gcd gz = t := by
      dsimp [gy, gz, t]
      calc
        (a.gcd c).gcd (b.gcd c) =
            (c.gcd a).gcd (c.gcd b) := by
              rw [Nat.gcd_comm a c, Nat.gcd_comm b c]
        _ = c.gcd (a.gcd b) := gcd_gcd_same_left c a b
        _ = a.gcd (b.gcd c) := triple_gcd_rotate a b c
    have hxy : x.Coprime y := by
      have h := Nat.coprime_div_gcd_div_gcd
        (show 0 < gx.gcd gy from hgxy.symm ▸ ht_pos)
      simpa [x, y, hgxy] using h
    have hxz : x.Coprime z := by
      have h := Nat.coprime_div_gcd_div_gcd
        (show 0 < gx.gcd gz from hgxz.symm ▸ ht_pos)
      simpa [x, z, hgxz] using h
    have hyz : y.Coprime z := by
      have h := Nat.coprime_div_gcd_div_gcd
        (show 0 < gy.gcd gz from hgyz.symm ▸ ht_pos)
      simpa [y, z, hgyz] using h
    have hfac_t :
        t.factorization =
          a.factorization ⊓ (b.factorization ⊓ c.factorization) := by
      dsimp [t]
      rw [Nat.factorization_gcd ha0 (Nat.ne_of_gt hgbc_pos),
        Nat.factorization_gcd hb0 hc0]
    have hfac_gx :
        gx.factorization = a.factorization ⊓ b.factorization := by
      exact Nat.factorization_gcd ha0 hb0
    have hfac_gy :
        gy.factorization = a.factorization ⊓ c.factorization := by
      exact Nat.factorization_gcd ha0 hc0
    have hfac_gz :
        gz.factorization = b.factorization ⊓ c.factorization := by
      exact Nat.factorization_gcd hb0 hc0
    have hmax₁ (p : ℕ) :
        max (a.factorization p) (b.factorization p) =
          max (a.factorization p) (c.factorization p) := by
      have h := congrArg (fun n : ℕ => n.factorization p) hab
      simpa [Nat.factorization_lcm ha0 hb0,
        Nat.factorization_lcm ha0 hc0, Pi.sup_apply] using h
    have hmax₂ (p : ℕ) :
        max (a.factorization p) (c.factorization p) =
          max (b.factorization p) (c.factorization p) := by
      have h := congrArg (fun n : ℕ => n.factorization p) hac
      simpa [Nat.factorization_lcm ha0 hc0,
        Nat.factorization_lcm hb0 hc0, Pi.sup_apply] using h
    have ha_eq : a = t * x * y := by
      apply Nat.factorization_inj ha0
        (mul_ne_zero (mul_ne_zero (Nat.ne_of_gt ht_pos)
          (Nat.ne_of_gt hx_pos)) (Nat.ne_of_gt hy_pos))
      ext p
      rw [Nat.factorization_mul
        (mul_ne_zero (Nat.ne_of_gt ht_pos) (Nat.ne_of_gt hx_pos))
        (Nat.ne_of_gt hy_pos)]
      rw [Nat.factorization_mul (Nat.ne_of_gt ht_pos) (Nat.ne_of_gt hx_pos)]
      rw [Nat.factorization_div htx, Nat.factorization_div hty]
      rw [hfac_t, hfac_gx, hfac_gy]
      simp only [Finsupp.inf_apply, Finsupp.add_apply, Finsupp.tsub_apply]
      have h₁ := hmax₁ p
      have h₂ := hmax₂ p
      omega
    have hb_eq : b = t * x * z := by
      apply Nat.factorization_inj hb0
        (mul_ne_zero (mul_ne_zero (Nat.ne_of_gt ht_pos)
          (Nat.ne_of_gt hx_pos)) (Nat.ne_of_gt hz_pos))
      ext p
      rw [Nat.factorization_mul
        (mul_ne_zero (Nat.ne_of_gt ht_pos) (Nat.ne_of_gt hx_pos))
        (Nat.ne_of_gt hz_pos)]
      rw [Nat.factorization_mul (Nat.ne_of_gt ht_pos) (Nat.ne_of_gt hx_pos)]
      rw [Nat.factorization_div htx, Nat.factorization_div htz]
      rw [hfac_t, hfac_gx, hfac_gz]
      simp only [Finsupp.inf_apply, Finsupp.add_apply, Finsupp.tsub_apply]
      have h₁ := hmax₁ p
      have h₂ := hmax₂ p
      omega
    have hc_eq : c = t * y * z := by
      apply Nat.factorization_inj hc0
        (mul_ne_zero (mul_ne_zero (Nat.ne_of_gt ht_pos)
          (Nat.ne_of_gt hy_pos)) (Nat.ne_of_gt hz_pos))
      ext p
      rw [Nat.factorization_mul
        (mul_ne_zero (Nat.ne_of_gt ht_pos) (Nat.ne_of_gt hy_pos))
        (Nat.ne_of_gt hz_pos)]
      rw [Nat.factorization_mul (Nat.ne_of_gt ht_pos) (Nat.ne_of_gt hy_pos)]
      rw [Nat.factorization_div hty, Nat.factorization_div htz]
      rw [hfac_t, hfac_gy, hfac_gz]
      simp only [Finsupp.inf_apply, Finsupp.add_apply, Finsupp.tsub_apply]
      have h₁ := hmax₁ p
      have h₂ := hmax₂ p
      omega
    exact ⟨t, x, y, z, ht_pos, hx_pos, hy_pos, hz_pos,
      hxy, hxz, hyz, ha_eq, hb_eq, hc_eq⟩
  · rintro ⟨t, x, y, z, _ht, _hx, _hy, _hz,
      hxy, hxz, hyz, rfl, rfl, rfl⟩
    have hab :
        (t * x * y).lcm (t * x * z) = t * x * y * z := by
      rw [Nat.lcm_mul_left, hyz.lcm_eq_mul]
      simp only [mul_assoc]
    have hac :
        (t * x * y).lcm (t * y * z) = t * x * y * z := by
      calc
        (t * x * y).lcm (t * y * z) =
            t * (x * y).lcm (y * z) := by
              simp only [mul_assoc, Nat.lcm_mul_left]
        _ = t * (y * x).lcm (y * z) := by rw [mul_comm x y]
        _ = t * (y * (x.lcm z)) := by rw [Nat.lcm_mul_left]
        _ = t * (y * (x * z)) := by rw [hxz.lcm_eq_mul]
        _ = t * x * y * z := by ac_rfl
    have hbc :
        (t * x * z).lcm (t * y * z) = t * x * y * z := by
      calc
        (t * x * z).lcm (t * y * z) =
            t * (x * z).lcm (y * z) := by
              simp only [mul_assoc, Nat.lcm_mul_left]
        _ = t * ((x.lcm y) * z) := by rw [Nat.lcm_mul_right]
        _ = t * ((x * y) * z) := by rw [hxy.lcm_eq_mul]
        _ = t * x * y * z := by ac_rfl
    exact ⟨hab.trans hac.symm, hac.trans hbc.symm⟩

/-- The manuscript's pair-product lemma stated for positive, pairwise
distinct integers and the project's literal forbidden-triangle predicate. -/
theorem isLcmTriangle_iff_pairProduct
    {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    IsLcmTriangle a b c ↔ PairProductForm a b c := by
  rw [← equal_pairwise_lcm_iff_pairProduct ha hb hc]
  constructor
  · rintro ⟨_, habc, hbca⟩
    exact ⟨habc.trans hbca, hbca.symm⟩
  · rintro ⟨habc, hacbc⟩
    exact ⟨by simp [hab, hac, hbc], habc.trans hacbc, hacbc.symm⟩

end Erdos536
