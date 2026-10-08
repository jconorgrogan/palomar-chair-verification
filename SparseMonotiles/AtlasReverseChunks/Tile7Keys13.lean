module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk13

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_13_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk13) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_416_mem : IndexedData7.key416.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_416]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_417_mem : IndexedData7.key417.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_417]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_418_mem : IndexedData7.key418.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_418]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_419_mem : IndexedData7.key419.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_419]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_420_mem : IndexedData7.key420.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_420]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_421_mem : IndexedData7.key421.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_421]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_422_mem : IndexedData7.key422.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_422]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_423_mem : IndexedData7.key423.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_423]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_424_mem : IndexedData7.key424.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_424]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_425_mem : IndexedData7.key425.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_425]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_426_mem : IndexedData7.key426.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_426]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_427_mem : IndexedData7.key427.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_427]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_428_mem : IndexedData7.key428.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_428]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_429_mem : IndexedData7.key429.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_429]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_430_mem : IndexedData7.key430.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_430]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_431_mem : IndexedData7.key431.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_431]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_432_mem : IndexedData7.key432.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_432]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_433_mem : IndexedData7.key433.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_433]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_434_mem : IndexedData7.key434.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_434]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_435_mem : IndexedData7.key435.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_435]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_436_mem : IndexedData7.key436.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_436]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_437_mem : IndexedData7.key437.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_437]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_438_mem : IndexedData7.key438.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_438]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_439_mem : IndexedData7.key439.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_439]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_440_mem : IndexedData7.key440.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_440]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_441_mem : IndexedData7.key441.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_441]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_442_mem : IndexedData7.key442.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_442]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_443_mem : IndexedData7.key443.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_443]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_444_mem : IndexedData7.key444.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_444]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_445_mem : IndexedData7.key445.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_445]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_446_mem : IndexedData7.key446.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_446]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_447_mem : IndexedData7.key447.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_447]
  exact reverseChunk7_13_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_13_subset_keys
#print axioms indexedKey7_416_mem
end SparseMonotiles.Canonical
