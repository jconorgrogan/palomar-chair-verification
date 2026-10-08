module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk23

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_23_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk23) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_736_mem : IndexedData7.key736.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_736]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_737_mem : IndexedData7.key737.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_737]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_738_mem : IndexedData7.key738.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_738]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_739_mem : IndexedData7.key739.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_739]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_740_mem : IndexedData7.key740.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_740]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_741_mem : IndexedData7.key741.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_741]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_742_mem : IndexedData7.key742.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_742]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_743_mem : IndexedData7.key743.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_743]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_744_mem : IndexedData7.key744.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_744]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_745_mem : IndexedData7.key745.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_745]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_746_mem : IndexedData7.key746.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_746]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_747_mem : IndexedData7.key747.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_747]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_748_mem : IndexedData7.key748.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_748]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_749_mem : IndexedData7.key749.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_749]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_750_mem : IndexedData7.key750.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_750]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_751_mem : IndexedData7.key751.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_751]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_752_mem : IndexedData7.key752.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_752]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_753_mem : IndexedData7.key753.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_753]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_754_mem : IndexedData7.key754.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_754]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_755_mem : IndexedData7.key755.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_755]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_756_mem : IndexedData7.key756.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_756]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_757_mem : IndexedData7.key757.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_757]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_758_mem : IndexedData7.key758.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_758]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_759_mem : IndexedData7.key759.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_759]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_760_mem : IndexedData7.key760.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_760]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_761_mem : IndexedData7.key761.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_761]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_762_mem : IndexedData7.key762.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_762]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_763_mem : IndexedData7.key763.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_763]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_764_mem : IndexedData7.key764.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_764]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_765_mem : IndexedData7.key765.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_765]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_766_mem : IndexedData7.key766.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_766]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_767_mem : IndexedData7.key767.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_767]
  exact reverseChunk7_23_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_23_subset_keys
#print axioms indexedKey7_736_mem
end SparseMonotiles.Canonical
