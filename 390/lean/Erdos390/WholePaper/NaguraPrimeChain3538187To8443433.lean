import Erdos390.WholePaper.Nagura

namespace Erdos390.WholePaper

theorem exists_prime_nagura_3538187_to_8443433 {n : ℕ}
    (hnLower : 3538187 ≤ n) (hnUpper : n < 8443433) : HasNaguraPrime n := by
  by_cases h4210447 : n < 4210447
  · exact ⟨4210447, by norm_num, h4210447, by omega⟩
  by_cases h5010449 : n < 5010449
  · exact ⟨5010449, by norm_num, h5010449, by omega⟩
  by_cases h5962441 : n < 5962441
  · exact ⟨5962441, by norm_num, h5962441, by omega⟩
  by_cases h7095313 : n < 7095313
  · exact ⟨7095313, by norm_num, h7095313, by omega⟩
  exact ⟨8443433, by norm_num, hnUpper, by omega⟩

end Erdos390.WholePaper
