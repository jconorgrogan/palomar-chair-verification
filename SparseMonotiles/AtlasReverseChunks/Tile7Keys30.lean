module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk30

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_30_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk30) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_960_mem : IndexedData7.key960.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_960]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_961_mem : IndexedData7.key961.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_961]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_962_mem : IndexedData7.key962.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_962]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_963_mem : IndexedData7.key963.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_963]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_964_mem : IndexedData7.key964.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_964]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_965_mem : IndexedData7.key965.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_965]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_966_mem : IndexedData7.key966.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_966]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_967_mem : IndexedData7.key967.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_967]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_968_mem : IndexedData7.key968.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_968]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_969_mem : IndexedData7.key969.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_969]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_970_mem : IndexedData7.key970.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_970]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_971_mem : IndexedData7.key971.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_971]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_972_mem : IndexedData7.key972.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_972]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_973_mem : IndexedData7.key973.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_973]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_974_mem : IndexedData7.key974.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_974]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_975_mem : IndexedData7.key975.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_975]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_976_mem : IndexedData7.key976.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_976]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_977_mem : IndexedData7.key977.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_977]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_978_mem : IndexedData7.key978.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_978]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_979_mem : IndexedData7.key979.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_979]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_980_mem : IndexedData7.key980.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_980]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_981_mem : IndexedData7.key981.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_981]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_982_mem : IndexedData7.key982.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_982]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_983_mem : IndexedData7.key983.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_983]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_984_mem : IndexedData7.key984.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_984]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_985_mem : IndexedData7.key985.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_985]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_986_mem : IndexedData7.key986.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_986]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_987_mem : IndexedData7.key987.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_987]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_988_mem : IndexedData7.key988.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_988]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_989_mem : IndexedData7.key989.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_989]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_990_mem : IndexedData7.key990.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_990]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_991_mem : IndexedData7.key991.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_991]
  exact reverseChunk7_30_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_30_subset_keys
#print axioms indexedKey7_960_mem
end SparseMonotiles.Canonical
