import Erdos390.WholePaper.CompleteRoughDecomposition

/-! # Expanded statement audit for complete rough decomposition -/

namespace Erdos390.WholePaper

noncomputable section

example (y a : ℕ) :
    completeSmoothPart y a = a / completeRoughLabel y a := rfl

example (y a : ℕ) :
    0 < completeRoughLabel y a ∧ completeRoughLabel y a ∣ a :=
  ⟨completeRoughLabel_pos y a, completeRoughLabel_dvd y a⟩

example (y a : ℕ) :
    a = completeRoughLabel y a * completeSmoothPart y a :=
  completeRough_decomposition y a

example (y a p : ℕ) :
    (completeRoughLabel y a).factorization p =
      if y < p then a.factorization p else 0 :=
  completeRoughLabel_factorization_apply y a p

example (y a p : ℕ) :
    (completeSmoothPart y a).factorization p =
      if p ≤ y then a.factorization p else 0 :=
  completeSmoothPart_factorization_apply y a p

example {y a p : ℕ} (hp : p.Prime)
    (hpDvd : p ∣ completeRoughLabel y a) : y < p :=
  prime_dvd_completeRoughLabel_gt hp hpDvd

example {y a : ℕ} (ha : 0 < a) :
    0 < completeSmoothPart y a ∧
      completeSmoothPart y a ∈ Nat.smoothNumbers (y + 1) :=
  ⟨completeSmoothPart_pos ha,
    completeSmoothPart_mem_smoothNumbers ha⟩

example {y a rough smooth : ℕ}
    (hrough : rough ≠ 0) (hsmooth : smooth ≠ 0)
    (hproduct : a = rough * smooth)
    (hroughSupport : ∀ p, rough.factorization p ≠ 0 → y < p)
    (hsmoothSupport : ∀ p, smooth.factorization p ≠ 0 → p ≤ y) :
    rough = completeRoughLabel y a ∧
      smooth = completeSmoothPart y a :=
  completeRoughDecomposition_unique hrough hsmooth hproduct
    hroughSupport hsmoothSupport

example {y a : ℕ} (ha : 0 < a) :
    completeRoughLabel y a = 1 ↔
      a ∈ Nat.smoothNumbers (y + 1) :=
  completeRoughLabel_eq_one_iff_mem_smoothNumbers ha

example (y a : ℕ) :
    completeRoughLabel y a = 1 ↔
      a = 0 ∨ a ∈ Nat.smoothNumbers (y + 1) :=
  completeRoughLabel_eq_one_iff_eq_zero_or_mem_smoothNumbers y a

end

end Erdos390.WholePaper
