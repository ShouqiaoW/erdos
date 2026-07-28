import Erdos390.WholePaper.Nagura

namespace Erdos390.WholePaper

theorem exists_prime_nagura_91639_to_218737 {n : ℕ}
    (hnLower : 91639 ≤ n) (hnUpper : n < 218737) : HasNaguraPrime n := by
  by_cases h109063 : n < 109063
  · exact ⟨109063, by norm_num, h109063, by omega⟩
  by_cases h129793 : n < 129793
  · exact ⟨129793, by norm_num, h129793, by omega⟩
  by_cases h154459 : n < 154459
  · exact ⟨154459, by norm_num, h154459, by omega⟩
  by_cases h183809 : n < 183809
  · exact ⟨183809, by norm_num, h183809, by omega⟩
  exact ⟨218737, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper
