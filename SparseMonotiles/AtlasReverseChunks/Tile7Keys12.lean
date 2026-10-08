module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk12

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_12_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk12) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_384_mem : IndexedData7.key384.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_384]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_385_mem : IndexedData7.key385.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_385]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_386_mem : IndexedData7.key386.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_386]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_387_mem : IndexedData7.key387.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_387]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_388_mem : IndexedData7.key388.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_388]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_389_mem : IndexedData7.key389.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_389]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_390_mem : IndexedData7.key390.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_390]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_391_mem : IndexedData7.key391.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_391]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_392_mem : IndexedData7.key392.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_392]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_393_mem : IndexedData7.key393.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_393]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_394_mem : IndexedData7.key394.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_394]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_395_mem : IndexedData7.key395.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_395]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_396_mem : IndexedData7.key396.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_396]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_397_mem : IndexedData7.key397.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_397]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_398_mem : IndexedData7.key398.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_398]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_399_mem : IndexedData7.key399.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_399]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_400_mem : IndexedData7.key400.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_400]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_401_mem : IndexedData7.key401.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_401]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_402_mem : IndexedData7.key402.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_402]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_403_mem : IndexedData7.key403.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_403]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_404_mem : IndexedData7.key404.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_404]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_405_mem : IndexedData7.key405.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_405]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_406_mem : IndexedData7.key406.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_406]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_407_mem : IndexedData7.key407.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_407]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_408_mem : IndexedData7.key408.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_408]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_409_mem : IndexedData7.key409.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_409]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_410_mem : IndexedData7.key410.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_410]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_411_mem : IndexedData7.key411.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_411]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_412_mem : IndexedData7.key412.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_412]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_413_mem : IndexedData7.key413.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_413]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_414_mem : IndexedData7.key414.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_414]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_415_mem : IndexedData7.key415.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_415]
  exact reverseChunk7_12_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_12_subset_keys
#print axioms indexedKey7_384_mem
end SparseMonotiles.Canonical
