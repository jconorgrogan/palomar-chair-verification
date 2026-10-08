module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk22

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_22_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk22) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_704_mem : IndexedData7.key704.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_704]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_705_mem : IndexedData7.key705.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_705]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_706_mem : IndexedData7.key706.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_706]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_707_mem : IndexedData7.key707.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_707]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_708_mem : IndexedData7.key708.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_708]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_709_mem : IndexedData7.key709.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_709]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_710_mem : IndexedData7.key710.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_710]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_711_mem : IndexedData7.key711.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_711]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_712_mem : IndexedData7.key712.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_712]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_713_mem : IndexedData7.key713.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_713]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_714_mem : IndexedData7.key714.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_714]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_715_mem : IndexedData7.key715.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_715]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_716_mem : IndexedData7.key716.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_716]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_717_mem : IndexedData7.key717.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_717]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_718_mem : IndexedData7.key718.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_718]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_719_mem : IndexedData7.key719.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_719]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_720_mem : IndexedData7.key720.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_720]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_721_mem : IndexedData7.key721.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_721]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_722_mem : IndexedData7.key722.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_722]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_723_mem : IndexedData7.key723.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_723]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_724_mem : IndexedData7.key724.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_724]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_725_mem : IndexedData7.key725.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_725]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_726_mem : IndexedData7.key726.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_726]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_727_mem : IndexedData7.key727.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_727]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_728_mem : IndexedData7.key728.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_728]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_729_mem : IndexedData7.key729.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_729]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_730_mem : IndexedData7.key730.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_730]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_731_mem : IndexedData7.key731.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_731]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_732_mem : IndexedData7.key732.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_732]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_733_mem : IndexedData7.key733.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_733]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_734_mem : IndexedData7.key734.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_734]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_735_mem : IndexedData7.key735.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_735]
  exact reverseChunk7_22_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_22_subset_keys
#print axioms indexedKey7_704_mem
end SparseMonotiles.Canonical
