module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk17

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_17_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk17) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_544_mem : IndexedData7.key544.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_544]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_545_mem : IndexedData7.key545.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_545]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_546_mem : IndexedData7.key546.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_546]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_547_mem : IndexedData7.key547.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_547]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_548_mem : IndexedData7.key548.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_548]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_549_mem : IndexedData7.key549.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_549]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_550_mem : IndexedData7.key550.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_550]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_551_mem : IndexedData7.key551.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_551]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_552_mem : IndexedData7.key552.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_552]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_553_mem : IndexedData7.key553.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_553]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_554_mem : IndexedData7.key554.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_554]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_555_mem : IndexedData7.key555.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_555]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_556_mem : IndexedData7.key556.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_556]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_557_mem : IndexedData7.key557.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_557]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_558_mem : IndexedData7.key558.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_558]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_559_mem : IndexedData7.key559.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_559]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_560_mem : IndexedData7.key560.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_560]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_561_mem : IndexedData7.key561.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_561]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_562_mem : IndexedData7.key562.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_562]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_563_mem : IndexedData7.key563.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_563]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_564_mem : IndexedData7.key564.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_564]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_565_mem : IndexedData7.key565.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_565]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_566_mem : IndexedData7.key566.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_566]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_567_mem : IndexedData7.key567.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_567]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_568_mem : IndexedData7.key568.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_568]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_569_mem : IndexedData7.key569.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_569]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_570_mem : IndexedData7.key570.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_570]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_571_mem : IndexedData7.key571.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_571]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_572_mem : IndexedData7.key572.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_572]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_573_mem : IndexedData7.key573.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_573]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_574_mem : IndexedData7.key574.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_574]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_575_mem : IndexedData7.key575.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_575]
  exact reverseChunk7_17_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_17_subset_keys
#print axioms indexedKey7_544_mem
end SparseMonotiles.Canonical
