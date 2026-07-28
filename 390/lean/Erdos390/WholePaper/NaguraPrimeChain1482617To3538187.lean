import Erdos390.WholePaper.Nagura

namespace Erdos390.WholePaper

theorem exists_prime_nagura_1482617_to_3538187 {n : ℕ}
    (hnLower : 1482617 ≤ n) (hnUpper : n < 3538187) : HasNaguraPrime n := by
  by_cases h1764319 : n < 1764319
  · exact ⟨1764319, by norm_num, h1764319, by omega⟩
  by_cases h2099543 : n < 2099543
  · exact ⟨2099543, by norm_num, h2099543, by omega⟩
  by_cases h2498521 : n < 2498521
  · exact ⟨2498521, by norm_num, h2498521, by omega⟩
  by_cases h2973251 : n < 2973251
  · exact ⟨2973251, by norm_num, h2973251, by omega⟩
  exact ⟨3538187, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper
