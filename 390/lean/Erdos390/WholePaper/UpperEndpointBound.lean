import Erdos390.WholePaper.CentralAnchorAssembly
import Erdos390.WholePaper.UpperScale

/-!
# Turning an exact assembled endpoint into an upper bound for `f`

The hard construction ends once an admissible endpoint has been produced.
This file records the remaining pointwise order and normalization algebra,
including a specialization to the actual full central-anchor set.
-/

namespace Erdos390.WholePaper

noncomputable section

theorem f_le_two_mul_add_of_admissible
    {n h : ℕ} (hn : 3 ≤ n)
    (hadmissible : IsAdmissibleEndpoint n (2 * n + h)) :
    f n ≤ 2 * n + h :=
  f_le_of_admissible hn hadmissible

/-- Pointwise normalized upper bound contributed by an endpoint shift `h`. -/
theorem mainError_normalized_le_of_admissible
    {n h : ℕ} (hn : 3 ≤ n)
    (hadmissible : IsAdmissibleEndpoint n (2 * n + h)) :
    mainError n / secondOrderScale n ≤
      (h : ℝ) / secondOrderScale n - C0 := by
  have hscale : 0 < secondOrderScale n :=
    secondOrderScale_pos (by omega)
  have hfNat := f_le_two_mul_add_of_admissible hn hadmissible
  have hfReal : (f n : ℝ) ≤ 2 * (n : ℝ) + (h : ℝ) := by
    exact_mod_cast hfNat
  have hshift : (f n : ℝ) - 2 * (n : ℝ) ≤ (h : ℝ) := by
    linarith
  have hnormalized :
      ((f n : ℝ) - 2 * (n : ℝ)) / secondOrderScale n ≤
        (h : ℝ) / secondOrderScale n :=
    (div_le_div_iff_of_pos_right hscale).2 hshift
  calc
    mainError n / secondOrderScale n =
        ((f n : ℝ) - 2 * (n : ℝ)) / secondOrderScale n - C0 := by
      rw [mainError]
      field_simp [hscale.ne']
      ring
    _ ≤ (h : ℝ) / secondOrderScale n - C0 :=
      sub_le_sub_right hnormalized C0

theorem f_le_of_fullCentralAnchors
    {n X h : ℕ} {q : ℕ → ℕ} (hn : 3 ≤ n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q)
    {tail : Finset ℕ}
    (htailSubset : tail ⊆ factorInterval (2 * n) (2 * n + h))
    (htailProd : tail.prod id * centralAnchorDivisor n X q =
      centralTailProduct n h) :
    f n ≤ 2 * n + h := by
  apply f_le_two_mul_add_of_admissible hn
  exact isAdmissibleEndpoint_of_fullCentralAnchors (by omega)
    hXTwo hXsq hq htailSubset htailProd

theorem mainError_normalized_le_of_fullCentralAnchors
    {n X h : ℕ} {q : ℕ → ℕ} (hn : 3 ≤ n) (hXTwo : 2 ≤ X)
    (hXsq : 2 * n < X ^ 2)
    (hq : IsLargeCentralCofactorChoice n X q)
    {tail : Finset ℕ}
    (htailSubset : tail ⊆ factorInterval (2 * n) (2 * n + h))
    (htailProd : tail.prod id * centralAnchorDivisor n X q =
      centralTailProduct n h) :
    mainError n / secondOrderScale n ≤
      (h : ℝ) / secondOrderScale n - C0 := by
  apply mainError_normalized_le_of_admissible hn
  exact isAdmissibleEndpoint_of_fullCentralAnchors (by omega)
    hXTwo hXsq hq htailSubset htailProd

end

end Erdos390.WholePaper
