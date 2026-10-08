module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk10

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_10_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk10) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_320_mem : IndexedData7.key320.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_320]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_321_mem : IndexedData7.key321.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_321]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_322_mem : IndexedData7.key322.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_322]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_323_mem : IndexedData7.key323.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_323]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_324_mem : IndexedData7.key324.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_324]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_325_mem : IndexedData7.key325.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_325]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_326_mem : IndexedData7.key326.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_326]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_327_mem : IndexedData7.key327.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_327]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_328_mem : IndexedData7.key328.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_328]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_329_mem : IndexedData7.key329.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_329]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_330_mem : IndexedData7.key330.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_330]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_331_mem : IndexedData7.key331.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_331]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_332_mem : IndexedData7.key332.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_332]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_333_mem : IndexedData7.key333.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_333]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_334_mem : IndexedData7.key334.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_334]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_335_mem : IndexedData7.key335.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_335]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_336_mem : IndexedData7.key336.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_336]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_337_mem : IndexedData7.key337.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_337]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_338_mem : IndexedData7.key338.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_338]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_339_mem : IndexedData7.key339.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_339]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_340_mem : IndexedData7.key340.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_340]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_341_mem : IndexedData7.key341.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_341]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_342_mem : IndexedData7.key342.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_342]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_343_mem : IndexedData7.key343.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_343]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_344_mem : IndexedData7.key344.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_344]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_345_mem : IndexedData7.key345.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_345]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_346_mem : IndexedData7.key346.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_346]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_347_mem : IndexedData7.key347.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_347]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_348_mem : IndexedData7.key348.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_348]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_349_mem : IndexedData7.key349.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_349]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_350_mem : IndexedData7.key350.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_350]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_351_mem : IndexedData7.key351.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_351]
  exact reverseChunk7_10_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_10_subset_keys
#print axioms indexedKey7_320_mem
end SparseMonotiles.Canonical
