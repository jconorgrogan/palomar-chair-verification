module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk25

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_25_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk25) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_800_mem : IndexedData7.key800.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_800]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_801_mem : IndexedData7.key801.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_801]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_802_mem : IndexedData7.key802.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_802]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_803_mem : IndexedData7.key803.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_803]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_804_mem : IndexedData7.key804.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_804]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_805_mem : IndexedData7.key805.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_805]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_806_mem : IndexedData7.key806.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_806]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_807_mem : IndexedData7.key807.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_807]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_808_mem : IndexedData7.key808.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_808]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_809_mem : IndexedData7.key809.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_809]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_810_mem : IndexedData7.key810.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_810]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_811_mem : IndexedData7.key811.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_811]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_812_mem : IndexedData7.key812.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_812]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_813_mem : IndexedData7.key813.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_813]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_814_mem : IndexedData7.key814.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_814]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_815_mem : IndexedData7.key815.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_815]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_816_mem : IndexedData7.key816.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_816]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_817_mem : IndexedData7.key817.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_817]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_818_mem : IndexedData7.key818.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_818]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_819_mem : IndexedData7.key819.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_819]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_820_mem : IndexedData7.key820.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_820]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_821_mem : IndexedData7.key821.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_821]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_822_mem : IndexedData7.key822.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_822]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_823_mem : IndexedData7.key823.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_823]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_824_mem : IndexedData7.key824.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_824]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_825_mem : IndexedData7.key825.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_825]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_826_mem : IndexedData7.key826.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_826]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_827_mem : IndexedData7.key827.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_827]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_828_mem : IndexedData7.key828.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_828]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_829_mem : IndexedData7.key829.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_829]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_830_mem : IndexedData7.key830.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_830]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_831_mem : IndexedData7.key831.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_831]
  exact reverseChunk7_25_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_25_subset_keys
#print axioms indexedKey7_800_mem
end SparseMonotiles.Canonical
