module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk6

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_6_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk6) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_192_mem : IndexedData7.key192.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_192]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_193_mem : IndexedData7.key193.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_193]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_194_mem : IndexedData7.key194.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_194]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_195_mem : IndexedData7.key195.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_195]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_196_mem : IndexedData7.key196.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_196]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_197_mem : IndexedData7.key197.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_197]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_198_mem : IndexedData7.key198.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_198]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_199_mem : IndexedData7.key199.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_199]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_200_mem : IndexedData7.key200.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_200]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_201_mem : IndexedData7.key201.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_201]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_202_mem : IndexedData7.key202.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_202]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_203_mem : IndexedData7.key203.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_203]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_204_mem : IndexedData7.key204.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_204]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_205_mem : IndexedData7.key205.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_205]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_206_mem : IndexedData7.key206.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_206]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_207_mem : IndexedData7.key207.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_207]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_208_mem : IndexedData7.key208.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_208]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_209_mem : IndexedData7.key209.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_209]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_210_mem : IndexedData7.key210.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_210]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_211_mem : IndexedData7.key211.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_211]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_212_mem : IndexedData7.key212.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_212]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_213_mem : IndexedData7.key213.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_213]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_214_mem : IndexedData7.key214.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_214]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_215_mem : IndexedData7.key215.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_215]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_216_mem : IndexedData7.key216.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_216]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_217_mem : IndexedData7.key217.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_217]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_218_mem : IndexedData7.key218.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_218]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_219_mem : IndexedData7.key219.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_219]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_220_mem : IndexedData7.key220.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_220]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_221_mem : IndexedData7.key221.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_221]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_222_mem : IndexedData7.key222.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_222]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_223_mem : IndexedData7.key223.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_223]
  exact reverseChunk7_6_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_6_subset_keys
#print axioms indexedKey7_192_mem
end SparseMonotiles.Canonical
