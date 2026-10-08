module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk28

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_28_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk28) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_896_mem : IndexedData7.key896.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_896]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_897_mem : IndexedData7.key897.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_897]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_898_mem : IndexedData7.key898.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_898]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_899_mem : IndexedData7.key899.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_899]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_900_mem : IndexedData7.key900.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_900]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_901_mem : IndexedData7.key901.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_901]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_902_mem : IndexedData7.key902.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_902]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_903_mem : IndexedData7.key903.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_903]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_904_mem : IndexedData7.key904.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_904]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_905_mem : IndexedData7.key905.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_905]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_906_mem : IndexedData7.key906.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_906]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_907_mem : IndexedData7.key907.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_907]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_908_mem : IndexedData7.key908.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_908]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_909_mem : IndexedData7.key909.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_909]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_910_mem : IndexedData7.key910.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_910]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_911_mem : IndexedData7.key911.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_911]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_912_mem : IndexedData7.key912.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_912]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_913_mem : IndexedData7.key913.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_913]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_914_mem : IndexedData7.key914.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_914]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_915_mem : IndexedData7.key915.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_915]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_916_mem : IndexedData7.key916.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_916]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_917_mem : IndexedData7.key917.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_917]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_918_mem : IndexedData7.key918.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_918]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_919_mem : IndexedData7.key919.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_919]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_920_mem : IndexedData7.key920.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_920]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_921_mem : IndexedData7.key921.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_921]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_922_mem : IndexedData7.key922.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_922]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_923_mem : IndexedData7.key923.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_923]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_924_mem : IndexedData7.key924.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_924]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_925_mem : IndexedData7.key925.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_925]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_926_mem : IndexedData7.key926.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_926]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_927_mem : IndexedData7.key927.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_927]
  exact reverseChunk7_28_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_28_subset_keys
#print axioms indexedKey7_896_mem
end SparseMonotiles.Canonical
