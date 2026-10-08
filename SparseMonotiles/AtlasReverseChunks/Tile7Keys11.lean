module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk11

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_11_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk11) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_352_mem : IndexedData7.key352.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_352]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_353_mem : IndexedData7.key353.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_353]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_354_mem : IndexedData7.key354.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_354]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_355_mem : IndexedData7.key355.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_355]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_356_mem : IndexedData7.key356.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_356]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_357_mem : IndexedData7.key357.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_357]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_358_mem : IndexedData7.key358.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_358]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_359_mem : IndexedData7.key359.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_359]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_360_mem : IndexedData7.key360.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_360]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_361_mem : IndexedData7.key361.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_361]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_362_mem : IndexedData7.key362.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_362]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_363_mem : IndexedData7.key363.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_363]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_364_mem : IndexedData7.key364.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_364]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_365_mem : IndexedData7.key365.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_365]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_366_mem : IndexedData7.key366.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_366]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_367_mem : IndexedData7.key367.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_367]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_368_mem : IndexedData7.key368.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_368]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_369_mem : IndexedData7.key369.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_369]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_370_mem : IndexedData7.key370.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_370]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_371_mem : IndexedData7.key371.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_371]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_372_mem : IndexedData7.key372.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_372]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_373_mem : IndexedData7.key373.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_373]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_374_mem : IndexedData7.key374.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_374]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_375_mem : IndexedData7.key375.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_375]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_376_mem : IndexedData7.key376.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_376]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_377_mem : IndexedData7.key377.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_377]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_378_mem : IndexedData7.key378.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_378]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_379_mem : IndexedData7.key379.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_379]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_380_mem : IndexedData7.key380.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_380]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_381_mem : IndexedData7.key381.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_381]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_382_mem : IndexedData7.key382.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_382]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_383_mem : IndexedData7.key383.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_383]
  exact reverseChunk7_11_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_11_subset_keys
#print axioms indexedKey7_352_mem
end SparseMonotiles.Canonical
