module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk16

@[expose] public section

namespace SparseMonotiles.Canonical
open Contact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Shared list inclusion avoids repeating the 32-chunk disjunction after each decode. -/
theorem reverseChunk7_16_subset_keys (k : KeyData 7)
    (hk : k ∈ keys7Chunk16) : k ∈ keys7 := by
  simp only [keys7, List.mem_append]
  tauto

theorem indexedKey7_512_mem : IndexedData7.key512.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_512]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_513_mem : IndexedData7.key513.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_513]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_514_mem : IndexedData7.key514.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_514]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_515_mem : IndexedData7.key515.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_515]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_516_mem : IndexedData7.key516.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_516]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_517_mem : IndexedData7.key517.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_517]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_518_mem : IndexedData7.key518.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_518]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_519_mem : IndexedData7.key519.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_519]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_520_mem : IndexedData7.key520.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_520]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_521_mem : IndexedData7.key521.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_521]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_522_mem : IndexedData7.key522.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_522]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_523_mem : IndexedData7.key523.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_523]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_524_mem : IndexedData7.key524.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_524]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_525_mem : IndexedData7.key525.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_525]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_526_mem : IndexedData7.key526.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_526]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_527_mem : IndexedData7.key527.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_527]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_528_mem : IndexedData7.key528.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_528]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_529_mem : IndexedData7.key529.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_529]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_530_mem : IndexedData7.key530.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_530]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_531_mem : IndexedData7.key531.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_531]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_532_mem : IndexedData7.key532.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_532]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_533_mem : IndexedData7.key533.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_533]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_534_mem : IndexedData7.key534.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_534]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_535_mem : IndexedData7.key535.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_535]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_536_mem : IndexedData7.key536.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_536]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_537_mem : IndexedData7.key537.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_537]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_538_mem : IndexedData7.key538.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_538]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_539_mem : IndexedData7.key539.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_539]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_540_mem : IndexedData7.key540.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_540]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_541_mem : IndexedData7.key541.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_541]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_542_mem : IndexedData7.key542.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_542]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

theorem indexedKey7_543_mem : IndexedData7.key543.toKeyData 188160 ∈ keys7 := by
  rw [indexedKeyDecode7_543]
  exact reverseChunk7_16_subset_keys _ (List.get_mem _ _)

#print axioms reverseChunk7_16_subset_keys
#print axioms indexedKey7_512_mem
end SparseMonotiles.Canonical
