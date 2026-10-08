module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk15

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_15_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk15) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_480_mem : IndexedData7.key480.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_480]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_481_mem : IndexedData7.key481.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_481]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_482_mem : IndexedData7.key482.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_482]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_483_mem : IndexedData7.key483.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_483]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_484_mem : IndexedData7.key484.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_484]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_485_mem : IndexedData7.key485.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_485]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_486_mem : IndexedData7.key486.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_486]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_487_mem : IndexedData7.key487.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_487]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_488_mem : IndexedData7.key488.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_488]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_489_mem : IndexedData7.key489.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_489]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_490_mem : IndexedData7.key490.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_490]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_491_mem : IndexedData7.key491.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_491]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_492_mem : IndexedData7.key492.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_492]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_493_mem : IndexedData7.key493.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_493]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_494_mem : IndexedData7.key494.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_494]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_495_mem : IndexedData7.key495.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_495]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_496_mem : IndexedData7.key496.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_496]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_497_mem : IndexedData7.key497.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_497]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_498_mem : IndexedData7.key498.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_498]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_499_mem : IndexedData7.key499.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_499]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_500_mem : IndexedData7.key500.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_500]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_501_mem : IndexedData7.key501.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_501]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_502_mem : IndexedData7.key502.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_502]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_503_mem : IndexedData7.key503.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_503]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_504_mem : IndexedData7.key504.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_504]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_505_mem : IndexedData7.key505.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_505]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_506_mem : IndexedData7.key506.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_506]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_507_mem : IndexedData7.key507.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_507]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_508_mem : IndexedData7.key508.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_508]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_509_mem : IndexedData7.key509.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_509]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_510_mem : IndexedData7.key510.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_510]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_511_mem : IndexedData7.key511.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_511]
  exact reverseChunk7_15_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_15_subset_keys
#print axioms indexedKey7_480_mem
end SparseMonotiles.Canonical
