module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk5

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_5_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk5) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_160_mem : IndexedData7.key160.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_160]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_161_mem : IndexedData7.key161.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_161]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_162_mem : IndexedData7.key162.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_162]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_163_mem : IndexedData7.key163.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_163]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_164_mem : IndexedData7.key164.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_164]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_165_mem : IndexedData7.key165.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_165]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_166_mem : IndexedData7.key166.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_166]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_167_mem : IndexedData7.key167.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_167]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_168_mem : IndexedData7.key168.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_168]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_169_mem : IndexedData7.key169.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_169]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_170_mem : IndexedData7.key170.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_170]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_171_mem : IndexedData7.key171.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_171]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_172_mem : IndexedData7.key172.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_172]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_173_mem : IndexedData7.key173.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_173]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_174_mem : IndexedData7.key174.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_174]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_175_mem : IndexedData7.key175.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_175]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_176_mem : IndexedData7.key176.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_176]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_177_mem : IndexedData7.key177.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_177]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_178_mem : IndexedData7.key178.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_178]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_179_mem : IndexedData7.key179.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_179]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_180_mem : IndexedData7.key180.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_180]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_181_mem : IndexedData7.key181.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_181]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_182_mem : IndexedData7.key182.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_182]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_183_mem : IndexedData7.key183.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_183]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_184_mem : IndexedData7.key184.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_184]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_185_mem : IndexedData7.key185.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_185]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_186_mem : IndexedData7.key186.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_186]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_187_mem : IndexedData7.key187.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_187]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_188_mem : IndexedData7.key188.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_188]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_189_mem : IndexedData7.key189.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_189]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_190_mem : IndexedData7.key190.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_190]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_191_mem : IndexedData7.key191.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_191]
  exact reverseChunk7_5_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_5_subset_keys
#print axioms indexedKey7_160_mem
end SparseMonotiles.Canonical
