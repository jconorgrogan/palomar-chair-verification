module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk29

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_29_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk29) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_928_mem : IndexedData7.key928.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_928]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_929_mem : IndexedData7.key929.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_929]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_930_mem : IndexedData7.key930.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_930]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_931_mem : IndexedData7.key931.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_931]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_932_mem : IndexedData7.key932.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_932]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_933_mem : IndexedData7.key933.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_933]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_934_mem : IndexedData7.key934.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_934]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_935_mem : IndexedData7.key935.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_935]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_936_mem : IndexedData7.key936.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_936]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_937_mem : IndexedData7.key937.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_937]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_938_mem : IndexedData7.key938.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_938]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_939_mem : IndexedData7.key939.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_939]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_940_mem : IndexedData7.key940.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_940]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_941_mem : IndexedData7.key941.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_941]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_942_mem : IndexedData7.key942.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_942]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_943_mem : IndexedData7.key943.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_943]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_944_mem : IndexedData7.key944.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_944]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_945_mem : IndexedData7.key945.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_945]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_946_mem : IndexedData7.key946.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_946]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_947_mem : IndexedData7.key947.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_947]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_948_mem : IndexedData7.key948.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_948]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_949_mem : IndexedData7.key949.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_949]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_950_mem : IndexedData7.key950.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_950]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_951_mem : IndexedData7.key951.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_951]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_952_mem : IndexedData7.key952.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_952]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_953_mem : IndexedData7.key953.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_953]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_954_mem : IndexedData7.key954.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_954]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_955_mem : IndexedData7.key955.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_955]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_956_mem : IndexedData7.key956.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_956]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_957_mem : IndexedData7.key957.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_957]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_958_mem : IndexedData7.key958.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_958]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_959_mem : IndexedData7.key959.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_959]
  exact reverseChunk7_29_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_29_subset_keys
#print axioms indexedKey7_928_mem
end SparseMonotiles.Canonical
