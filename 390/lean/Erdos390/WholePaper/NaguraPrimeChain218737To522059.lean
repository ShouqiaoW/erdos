import Erdos390.WholePaper.Nagura

namespace Erdos390.WholePaper

theorem exists_prime_nagura_218737_to_522059 {n : ℕ}
    (hnLower : 218737 ≤ n) (hnUpper : n < 522059) : HasNaguraPrime n := by
  by_cases h260317 : n < 260317
  · exact ⟨260317, by norm_num, h260317, by omega⟩
  by_cases h309779 : n < 309779
  · exact ⟨309779, by norm_num, h309779, by omega⟩
  by_cases h368647 : n < 368647
  · exact ⟨368647, by norm_num, h368647, by omega⟩
  by_cases h438701 : n < 438701
  · exact ⟨438701, by norm_num, h438701, by omega⟩
  exact ⟨522059, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper
