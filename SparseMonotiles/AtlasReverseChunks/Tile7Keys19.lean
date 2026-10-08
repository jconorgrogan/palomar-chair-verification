module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk19

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_19_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk19) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_608_mem : IndexedData7.key608.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_608]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_609_mem : IndexedData7.key609.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_609]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_610_mem : IndexedData7.key610.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_610]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_611_mem : IndexedData7.key611.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_611]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_612_mem : IndexedData7.key612.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_612]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_613_mem : IndexedData7.key613.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_613]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_614_mem : IndexedData7.key614.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_614]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_615_mem : IndexedData7.key615.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_615]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_616_mem : IndexedData7.key616.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_616]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_617_mem : IndexedData7.key617.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_617]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_618_mem : IndexedData7.key618.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_618]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_619_mem : IndexedData7.key619.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_619]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_620_mem : IndexedData7.key620.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_620]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_621_mem : IndexedData7.key621.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_621]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_622_mem : IndexedData7.key622.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_622]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_623_mem : IndexedData7.key623.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_623]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_624_mem : IndexedData7.key624.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_624]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_625_mem : IndexedData7.key625.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_625]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_626_mem : IndexedData7.key626.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_626]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_627_mem : IndexedData7.key627.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_627]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_628_mem : IndexedData7.key628.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_628]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_629_mem : IndexedData7.key629.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_629]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_630_mem : IndexedData7.key630.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_630]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_631_mem : IndexedData7.key631.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_631]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_632_mem : IndexedData7.key632.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_632]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_633_mem : IndexedData7.key633.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_633]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_634_mem : IndexedData7.key634.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_634]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_635_mem : IndexedData7.key635.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_635]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_636_mem : IndexedData7.key636.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_636]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_637_mem : IndexedData7.key637.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_637]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_638_mem : IndexedData7.key638.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_638]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_639_mem : IndexedData7.key639.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_639]
  exact reverseChunk7_19_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_19_subset_keys
#print axioms indexedKey7_608_mem
end SparseMonotiles.Canonical
