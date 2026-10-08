module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk24

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_24_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk24) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_768_mem : IndexedData7.key768.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_768]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_769_mem : IndexedData7.key769.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_769]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_770_mem : IndexedData7.key770.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_770]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_771_mem : IndexedData7.key771.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_771]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_772_mem : IndexedData7.key772.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_772]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_773_mem : IndexedData7.key773.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_773]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_774_mem : IndexedData7.key774.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_774]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_775_mem : IndexedData7.key775.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_775]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_776_mem : IndexedData7.key776.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_776]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_777_mem : IndexedData7.key777.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_777]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_778_mem : IndexedData7.key778.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_778]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_779_mem : IndexedData7.key779.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_779]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_780_mem : IndexedData7.key780.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_780]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_781_mem : IndexedData7.key781.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_781]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_782_mem : IndexedData7.key782.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_782]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_783_mem : IndexedData7.key783.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_783]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_784_mem : IndexedData7.key784.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_784]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_785_mem : IndexedData7.key785.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_785]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_786_mem : IndexedData7.key786.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_786]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_787_mem : IndexedData7.key787.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_787]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_788_mem : IndexedData7.key788.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_788]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_789_mem : IndexedData7.key789.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_789]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_790_mem : IndexedData7.key790.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_790]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_791_mem : IndexedData7.key791.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_791]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_792_mem : IndexedData7.key792.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_792]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_793_mem : IndexedData7.key793.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_793]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_794_mem : IndexedData7.key794.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_794]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_795_mem : IndexedData7.key795.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_795]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_796_mem : IndexedData7.key796.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_796]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_797_mem : IndexedData7.key797.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_797]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_798_mem : IndexedData7.key798.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_798]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_799_mem : IndexedData7.key799.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_799]
  exact reverseChunk7_24_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_24_subset_keys
#print axioms indexedKey7_768_mem
end SparseMonotiles.Canonical
