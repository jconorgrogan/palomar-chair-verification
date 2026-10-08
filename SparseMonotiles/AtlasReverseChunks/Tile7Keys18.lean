module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk18

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_18_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk18) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_576_mem : IndexedData7.key576.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_576]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_577_mem : IndexedData7.key577.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_577]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_578_mem : IndexedData7.key578.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_578]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_579_mem : IndexedData7.key579.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_579]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_580_mem : IndexedData7.key580.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_580]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_581_mem : IndexedData7.key581.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_581]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_582_mem : IndexedData7.key582.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_582]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_583_mem : IndexedData7.key583.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_583]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_584_mem : IndexedData7.key584.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_584]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_585_mem : IndexedData7.key585.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_585]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_586_mem : IndexedData7.key586.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_586]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_587_mem : IndexedData7.key587.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_587]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_588_mem : IndexedData7.key588.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_588]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_589_mem : IndexedData7.key589.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_589]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_590_mem : IndexedData7.key590.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_590]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_591_mem : IndexedData7.key591.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_591]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_592_mem : IndexedData7.key592.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_592]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_593_mem : IndexedData7.key593.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_593]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_594_mem : IndexedData7.key594.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_594]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_595_mem : IndexedData7.key595.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_595]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_596_mem : IndexedData7.key596.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_596]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_597_mem : IndexedData7.key597.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_597]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_598_mem : IndexedData7.key598.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_598]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_599_mem : IndexedData7.key599.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_599]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_600_mem : IndexedData7.key600.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_600]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_601_mem : IndexedData7.key601.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_601]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_602_mem : IndexedData7.key602.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_602]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_603_mem : IndexedData7.key603.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_603]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_604_mem : IndexedData7.key604.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_604]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_605_mem : IndexedData7.key605.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_605]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_606_mem : IndexedData7.key606.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_606]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_607_mem : IndexedData7.key607.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_607]
  exact reverseChunk7_18_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_18_subset_keys
#print axioms indexedKey7_576_mem
end SparseMonotiles.Canonical
