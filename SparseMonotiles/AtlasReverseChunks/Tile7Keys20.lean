module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk20

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_20_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk20) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_640_mem : IndexedData7.key640.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_640]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_641_mem : IndexedData7.key641.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_641]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_642_mem : IndexedData7.key642.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_642]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_643_mem : IndexedData7.key643.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_643]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_644_mem : IndexedData7.key644.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_644]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_645_mem : IndexedData7.key645.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_645]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_646_mem : IndexedData7.key646.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_646]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_647_mem : IndexedData7.key647.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_647]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_648_mem : IndexedData7.key648.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_648]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_649_mem : IndexedData7.key649.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_649]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_650_mem : IndexedData7.key650.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_650]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_651_mem : IndexedData7.key651.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_651]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_652_mem : IndexedData7.key652.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_652]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_653_mem : IndexedData7.key653.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_653]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_654_mem : IndexedData7.key654.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_654]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_655_mem : IndexedData7.key655.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_655]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_656_mem : IndexedData7.key656.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_656]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_657_mem : IndexedData7.key657.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_657]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_658_mem : IndexedData7.key658.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_658]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_659_mem : IndexedData7.key659.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_659]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_660_mem : IndexedData7.key660.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_660]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_661_mem : IndexedData7.key661.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_661]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_662_mem : IndexedData7.key662.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_662]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_663_mem : IndexedData7.key663.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_663]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_664_mem : IndexedData7.key664.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_664]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_665_mem : IndexedData7.key665.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_665]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_666_mem : IndexedData7.key666.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_666]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_667_mem : IndexedData7.key667.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_667]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_668_mem : IndexedData7.key668.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_668]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_669_mem : IndexedData7.key669.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_669]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_670_mem : IndexedData7.key670.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_670]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_671_mem : IndexedData7.key671.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_671]
  exact reverseChunk7_20_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_20_subset_keys
#print axioms indexedKey7_640_mem
end SparseMonotiles.Canonical
