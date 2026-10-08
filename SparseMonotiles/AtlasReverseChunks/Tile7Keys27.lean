module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk27

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_27_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk27) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_864_mem : IndexedData7.key864.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_864]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_865_mem : IndexedData7.key865.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_865]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_866_mem : IndexedData7.key866.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_866]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_867_mem : IndexedData7.key867.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_867]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_868_mem : IndexedData7.key868.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_868]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_869_mem : IndexedData7.key869.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_869]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_870_mem : IndexedData7.key870.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_870]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_871_mem : IndexedData7.key871.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_871]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_872_mem : IndexedData7.key872.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_872]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_873_mem : IndexedData7.key873.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_873]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_874_mem : IndexedData7.key874.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_874]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_875_mem : IndexedData7.key875.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_875]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_876_mem : IndexedData7.key876.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_876]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_877_mem : IndexedData7.key877.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_877]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_878_mem : IndexedData7.key878.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_878]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_879_mem : IndexedData7.key879.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_879]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_880_mem : IndexedData7.key880.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_880]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_881_mem : IndexedData7.key881.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_881]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_882_mem : IndexedData7.key882.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_882]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_883_mem : IndexedData7.key883.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_883]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_884_mem : IndexedData7.key884.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_884]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_885_mem : IndexedData7.key885.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_885]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_886_mem : IndexedData7.key886.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_886]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_887_mem : IndexedData7.key887.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_887]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_888_mem : IndexedData7.key888.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_888]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_889_mem : IndexedData7.key889.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_889]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_890_mem : IndexedData7.key890.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_890]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_891_mem : IndexedData7.key891.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_891]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_892_mem : IndexedData7.key892.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_892]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_893_mem : IndexedData7.key893.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_893]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_894_mem : IndexedData7.key894.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_894]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_895_mem : IndexedData7.key895.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_895]
  exact reverseChunk7_27_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_27_subset_keys
#print axioms indexedKey7_864_mem
end SparseMonotiles.Canonical
