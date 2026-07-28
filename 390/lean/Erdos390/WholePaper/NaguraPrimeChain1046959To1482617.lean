import Erdos390.WholePaper.Nagura

namespace Erdos390.WholePaper

theorem exists_prime_nagura_1046959_to_1482617 {n : ℕ}
    (hnLower : 1046959 ≤ n) (hnUpper : n < 1482617) : HasNaguraPrime n := by
  by_cases h1245883 : n < 1245883
  · exact ⟨1245883, by norm_num, h1245883, by omega⟩
  exact ⟨1482617, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper
