module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk8

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_8_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk8) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_256_mem : IndexedData7.key256.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_256]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_257_mem : IndexedData7.key257.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_257]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_258_mem : IndexedData7.key258.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_258]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_259_mem : IndexedData7.key259.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_259]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_260_mem : IndexedData7.key260.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_260]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_261_mem : IndexedData7.key261.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_261]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_262_mem : IndexedData7.key262.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_262]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_263_mem : IndexedData7.key263.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_263]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_264_mem : IndexedData7.key264.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_264]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_265_mem : IndexedData7.key265.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_265]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_266_mem : IndexedData7.key266.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_266]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_267_mem : IndexedData7.key267.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_267]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_268_mem : IndexedData7.key268.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_268]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_269_mem : IndexedData7.key269.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_269]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_270_mem : IndexedData7.key270.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_270]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_271_mem : IndexedData7.key271.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_271]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_272_mem : IndexedData7.key272.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_272]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_273_mem : IndexedData7.key273.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_273]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_274_mem : IndexedData7.key274.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_274]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_275_mem : IndexedData7.key275.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_275]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_276_mem : IndexedData7.key276.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_276]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_277_mem : IndexedData7.key277.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_277]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_278_mem : IndexedData7.key278.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_278]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_279_mem : IndexedData7.key279.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_279]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_280_mem : IndexedData7.key280.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_280]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_281_mem : IndexedData7.key281.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_281]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_282_mem : IndexedData7.key282.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_282]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_283_mem : IndexedData7.key283.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_283]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_284_mem : IndexedData7.key284.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_284]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_285_mem : IndexedData7.key285.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_285]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_286_mem : IndexedData7.key286.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_286]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_287_mem : IndexedData7.key287.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_287]
  exact reverseChunk7_8_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_8_subset_keys
#print axioms indexedKey7_256_mem
end SparseMonotiles.Canonical
