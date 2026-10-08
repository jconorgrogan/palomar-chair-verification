module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk21

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_21_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk21) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_672_mem : IndexedData7.key672.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_672]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_673_mem : IndexedData7.key673.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_673]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_674_mem : IndexedData7.key674.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_674]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_675_mem : IndexedData7.key675.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_675]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_676_mem : IndexedData7.key676.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_676]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_677_mem : IndexedData7.key677.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_677]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_678_mem : IndexedData7.key678.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_678]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_679_mem : IndexedData7.key679.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_679]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_680_mem : IndexedData7.key680.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_680]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_681_mem : IndexedData7.key681.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_681]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_682_mem : IndexedData7.key682.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_682]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_683_mem : IndexedData7.key683.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_683]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_684_mem : IndexedData7.key684.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_684]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_685_mem : IndexedData7.key685.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_685]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_686_mem : IndexedData7.key686.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_686]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_687_mem : IndexedData7.key687.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_687]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_688_mem : IndexedData7.key688.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_688]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_689_mem : IndexedData7.key689.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_689]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_690_mem : IndexedData7.key690.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_690]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_691_mem : IndexedData7.key691.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_691]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_692_mem : IndexedData7.key692.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_692]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_693_mem : IndexedData7.key693.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_693]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_694_mem : IndexedData7.key694.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_694]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_695_mem : IndexedData7.key695.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_695]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_696_mem : IndexedData7.key696.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_696]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_697_mem : IndexedData7.key697.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_697]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_698_mem : IndexedData7.key698.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_698]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_699_mem : IndexedData7.key699.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_699]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_700_mem : IndexedData7.key700.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_700]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_701_mem : IndexedData7.key701.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_701]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_702_mem : IndexedData7.key702.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_702]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_703_mem : IndexedData7.key703.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_703]
  exact reverseChunk7_21_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_21_subset_keys
#print axioms indexedKey7_672_mem
end SparseMonotiles.Canonical
