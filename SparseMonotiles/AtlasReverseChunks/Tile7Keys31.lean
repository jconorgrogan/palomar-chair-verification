module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk31

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_31_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk31) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_992_mem : IndexedData7.key992.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_992]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_993_mem : IndexedData7.key993.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_993]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_994_mem : IndexedData7.key994.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_994]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_995_mem : IndexedData7.key995.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_995]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_996_mem : IndexedData7.key996.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_996]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_997_mem : IndexedData7.key997.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_997]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_998_mem : IndexedData7.key998.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_998]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_999_mem : IndexedData7.key999.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_999]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1000_mem : IndexedData7.key1000.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1000]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1001_mem : IndexedData7.key1001.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1001]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1002_mem : IndexedData7.key1002.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1002]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1003_mem : IndexedData7.key1003.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1003]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1004_mem : IndexedData7.key1004.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1004]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1005_mem : IndexedData7.key1005.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1005]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1006_mem : IndexedData7.key1006.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1006]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1007_mem : IndexedData7.key1007.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1007]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1008_mem : IndexedData7.key1008.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1008]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1009_mem : IndexedData7.key1009.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1009]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1010_mem : IndexedData7.key1010.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1010]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1011_mem : IndexedData7.key1011.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1011]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1012_mem : IndexedData7.key1012.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1012]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1013_mem : IndexedData7.key1013.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1013]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1014_mem : IndexedData7.key1014.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1014]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1015_mem : IndexedData7.key1015.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1015]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1016_mem : IndexedData7.key1016.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1016]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1017_mem : IndexedData7.key1017.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1017]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1018_mem : IndexedData7.key1018.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1018]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1019_mem : IndexedData7.key1019.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1019]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1020_mem : IndexedData7.key1020.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1020]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1021_mem : IndexedData7.key1021.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1021]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1022_mem : IndexedData7.key1022.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1022]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_1023_mem : IndexedData7.key1023.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_1023]
  exact reverseChunk7_31_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_31_subset_keys
#print axioms indexedKey7_992_mem
end SparseMonotiles.Canonical
