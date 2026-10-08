module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk9

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_9_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk9) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_288_mem : IndexedData7.key288.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_288]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_289_mem : IndexedData7.key289.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_289]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_290_mem : IndexedData7.key290.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_290]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_291_mem : IndexedData7.key291.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_291]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_292_mem : IndexedData7.key292.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_292]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_293_mem : IndexedData7.key293.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_293]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_294_mem : IndexedData7.key294.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_294]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_295_mem : IndexedData7.key295.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_295]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_296_mem : IndexedData7.key296.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_296]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_297_mem : IndexedData7.key297.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_297]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_298_mem : IndexedData7.key298.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_298]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_299_mem : IndexedData7.key299.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_299]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_300_mem : IndexedData7.key300.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_300]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_301_mem : IndexedData7.key301.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_301]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_302_mem : IndexedData7.key302.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_302]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_303_mem : IndexedData7.key303.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_303]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_304_mem : IndexedData7.key304.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_304]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_305_mem : IndexedData7.key305.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_305]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_306_mem : IndexedData7.key306.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_306]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_307_mem : IndexedData7.key307.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_307]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_308_mem : IndexedData7.key308.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_308]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_309_mem : IndexedData7.key309.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_309]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_310_mem : IndexedData7.key310.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_310]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_311_mem : IndexedData7.key311.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_311]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_312_mem : IndexedData7.key312.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_312]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_313_mem : IndexedData7.key313.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_313]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_314_mem : IndexedData7.key314.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_314]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_315_mem : IndexedData7.key315.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_315]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_316_mem : IndexedData7.key316.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_316]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_317_mem : IndexedData7.key317.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_317]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_318_mem : IndexedData7.key318.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_318]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_319_mem : IndexedData7.key319.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_319]
  exact reverseChunk7_9_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_9_subset_keys
#print axioms indexedKey7_288_mem
end SparseMonotiles.Canonical
