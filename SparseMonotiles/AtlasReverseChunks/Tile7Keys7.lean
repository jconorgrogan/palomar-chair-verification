module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk7

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_7_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk7) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_224_mem : IndexedData7.key224.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_224]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_225_mem : IndexedData7.key225.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_225]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_226_mem : IndexedData7.key226.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_226]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_227_mem : IndexedData7.key227.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_227]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_228_mem : IndexedData7.key228.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_228]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_229_mem : IndexedData7.key229.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_229]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_230_mem : IndexedData7.key230.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_230]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_231_mem : IndexedData7.key231.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_231]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_232_mem : IndexedData7.key232.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_232]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_233_mem : IndexedData7.key233.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_233]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_234_mem : IndexedData7.key234.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_234]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_235_mem : IndexedData7.key235.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_235]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_236_mem : IndexedData7.key236.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_236]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_237_mem : IndexedData7.key237.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_237]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_238_mem : IndexedData7.key238.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_238]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_239_mem : IndexedData7.key239.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_239]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_240_mem : IndexedData7.key240.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_240]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_241_mem : IndexedData7.key241.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_241]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_242_mem : IndexedData7.key242.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_242]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_243_mem : IndexedData7.key243.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_243]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_244_mem : IndexedData7.key244.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_244]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_245_mem : IndexedData7.key245.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_245]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_246_mem : IndexedData7.key246.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_246]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_247_mem : IndexedData7.key247.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_247]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_248_mem : IndexedData7.key248.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_248]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_249_mem : IndexedData7.key249.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_249]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_250_mem : IndexedData7.key250.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_250]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_251_mem : IndexedData7.key251.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_251]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_252_mem : IndexedData7.key252.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_252]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_253_mem : IndexedData7.key253.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_253]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_254_mem : IndexedData7.key254.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_254]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_255_mem : IndexedData7.key255.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_255]
  exact reverseChunk7_7_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_7_subset_keys
#print axioms indexedKey7_224_mem
end SparseMonotiles.Canonical
