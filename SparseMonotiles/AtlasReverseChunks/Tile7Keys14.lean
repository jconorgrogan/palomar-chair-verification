module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk14

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_14_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk14) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_448_mem : IndexedData7.key448.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_448]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_449_mem : IndexedData7.key449.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_449]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_450_mem : IndexedData7.key450.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_450]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_451_mem : IndexedData7.key451.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_451]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_452_mem : IndexedData7.key452.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_452]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_453_mem : IndexedData7.key453.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_453]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_454_mem : IndexedData7.key454.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_454]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_455_mem : IndexedData7.key455.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_455]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_456_mem : IndexedData7.key456.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_456]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_457_mem : IndexedData7.key457.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_457]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_458_mem : IndexedData7.key458.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_458]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_459_mem : IndexedData7.key459.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_459]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_460_mem : IndexedData7.key460.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_460]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_461_mem : IndexedData7.key461.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_461]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_462_mem : IndexedData7.key462.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_462]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_463_mem : IndexedData7.key463.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_463]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_464_mem : IndexedData7.key464.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_464]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_465_mem : IndexedData7.key465.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_465]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_466_mem : IndexedData7.key466.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_466]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_467_mem : IndexedData7.key467.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_467]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_468_mem : IndexedData7.key468.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_468]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_469_mem : IndexedData7.key469.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_469]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_470_mem : IndexedData7.key470.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_470]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_471_mem : IndexedData7.key471.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_471]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_472_mem : IndexedData7.key472.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_472]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_473_mem : IndexedData7.key473.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_473]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_474_mem : IndexedData7.key474.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_474]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_475_mem : IndexedData7.key475.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_475]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_476_mem : IndexedData7.key476.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_476]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_477_mem : IndexedData7.key477.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_477]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_478_mem : IndexedData7.key478.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_478]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_479_mem : IndexedData7.key479.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_479]
  exact reverseChunk7_14_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_14_subset_keys
#print axioms indexedKey7_448_mem
end SparseMonotiles.Canonical
