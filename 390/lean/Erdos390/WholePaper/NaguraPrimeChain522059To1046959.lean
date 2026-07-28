import Erdos390.WholePaper.Nagura

namespace Erdos390.WholePaper

theorem exists_prime_nagura_522059_to_1046959 {n : ℕ}
    (hnLower : 522059 ≤ n) (hnUpper : n < 1046959) : HasNaguraPrime n := by
  by_cases h621259 : n < 621259
  · exact ⟨621259, by norm_num, h621259, by omega⟩
  by_cases h739301 : n < 739301
  · exact ⟨739301, by norm_num, h739301, by omega⟩
  by_cases h879797 : n < 879797
  · exact ⟨879797, by norm_num, h879797, by omega⟩
  exact ⟨1046959, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper
