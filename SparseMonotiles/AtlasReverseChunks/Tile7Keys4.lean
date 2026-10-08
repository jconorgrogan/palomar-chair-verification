module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk4

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_4_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk4) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_128_mem : IndexedData7.key128.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_128]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_129_mem : IndexedData7.key129.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_129]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_130_mem : IndexedData7.key130.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_130]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_131_mem : IndexedData7.key131.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_131]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_132_mem : IndexedData7.key132.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_132]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_133_mem : IndexedData7.key133.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_133]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_134_mem : IndexedData7.key134.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_134]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_135_mem : IndexedData7.key135.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_135]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_136_mem : IndexedData7.key136.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_136]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_137_mem : IndexedData7.key137.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_137]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_138_mem : IndexedData7.key138.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_138]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_139_mem : IndexedData7.key139.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_139]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_140_mem : IndexedData7.key140.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_140]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_141_mem : IndexedData7.key141.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_141]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_142_mem : IndexedData7.key142.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_142]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_143_mem : IndexedData7.key143.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_143]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_144_mem : IndexedData7.key144.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_144]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_145_mem : IndexedData7.key145.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_145]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_146_mem : IndexedData7.key146.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_146]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_147_mem : IndexedData7.key147.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_147]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_148_mem : IndexedData7.key148.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_148]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_149_mem : IndexedData7.key149.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_149]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_150_mem : IndexedData7.key150.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_150]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_151_mem : IndexedData7.key151.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_151]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_152_mem : IndexedData7.key152.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_152]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_153_mem : IndexedData7.key153.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_153]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_154_mem : IndexedData7.key154.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_154]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_155_mem : IndexedData7.key155.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_155]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_156_mem : IndexedData7.key156.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_156]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_157_mem : IndexedData7.key157.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_157]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_158_mem : IndexedData7.key158.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_158]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_159_mem : IndexedData7.key159.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_159]
  exact reverseChunk7_4_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_4_subset_keys
#print axioms indexedKey7_128_mem
end SparseMonotiles.Canonical
