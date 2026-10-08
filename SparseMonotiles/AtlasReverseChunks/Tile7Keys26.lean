module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk26

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_26_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk26) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_832_mem : IndexedData7.key832.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_832]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_833_mem : IndexedData7.key833.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_833]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_834_mem : IndexedData7.key834.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_834]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_835_mem : IndexedData7.key835.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_835]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_836_mem : IndexedData7.key836.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_836]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_837_mem : IndexedData7.key837.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_837]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_838_mem : IndexedData7.key838.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_838]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_839_mem : IndexedData7.key839.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_839]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_840_mem : IndexedData7.key840.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_840]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_841_mem : IndexedData7.key841.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_841]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_842_mem : IndexedData7.key842.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_842]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_843_mem : IndexedData7.key843.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_843]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_844_mem : IndexedData7.key844.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_844]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_845_mem : IndexedData7.key845.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_845]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_846_mem : IndexedData7.key846.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_846]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_847_mem : IndexedData7.key847.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_847]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_848_mem : IndexedData7.key848.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_848]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_849_mem : IndexedData7.key849.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_849]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_850_mem : IndexedData7.key850.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_850]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_851_mem : IndexedData7.key851.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_851]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_852_mem : IndexedData7.key852.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_852]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_853_mem : IndexedData7.key853.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_853]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_854_mem : IndexedData7.key854.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_854]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_855_mem : IndexedData7.key855.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_855]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_856_mem : IndexedData7.key856.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_856]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_857_mem : IndexedData7.key857.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_857]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_858_mem : IndexedData7.key858.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_858]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_859_mem : IndexedData7.key859.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_859]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_860_mem : IndexedData7.key860.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_860]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_861_mem : IndexedData7.key861.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_861]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_862_mem : IndexedData7.key862.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_862]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_863_mem : IndexedData7.key863.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_863]
  exact reverseChunk7_26_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_26_subset_keys
#print axioms indexedKey7_832_mem
end SparseMonotiles.Canonical
