module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk11

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk11_aligned : ∀ k ∈ keys7Chunk11,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk11, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨308, by decide⟩, IndexedData7.key352, by decide, canonicalPose7_352, canonicalMatch7_352, indexedKeyDecode7_352⟩
  · exact ⟨⟨309, by decide⟩, IndexedData7.key353, by decide, canonicalPose7_353, canonicalMatch7_353, indexedKeyDecode7_353⟩
  · exact ⟨⟨310, by decide⟩, IndexedData7.key354, by decide, canonicalPose7_354, canonicalMatch7_354, indexedKeyDecode7_354⟩
  · exact ⟨⟨311, by decide⟩, IndexedData7.key355, by decide, canonicalPose7_355, canonicalMatch7_355, indexedKeyDecode7_355⟩
  · exact ⟨⟨312, by decide⟩, IndexedData7.key356, by decide, canonicalPose7_356, canonicalMatch7_356, indexedKeyDecode7_356⟩
  · exact ⟨⟨313, by decide⟩, IndexedData7.key357, by decide, canonicalPose7_357, canonicalMatch7_357, indexedKeyDecode7_357⟩
  · exact ⟨⟨313, by decide⟩, IndexedData7.key358, by decide, canonicalPose7_358, canonicalMatch7_358, indexedKeyDecode7_358⟩
  · exact ⟨⟨314, by decide⟩, IndexedData7.key359, by decide, canonicalPose7_359, canonicalMatch7_359, indexedKeyDecode7_359⟩
  · exact ⟨⟨315, by decide⟩, IndexedData7.key360, by decide, canonicalPose7_360, canonicalMatch7_360, indexedKeyDecode7_360⟩
  · exact ⟨⟨315, by decide⟩, IndexedData7.key361, by decide, canonicalPose7_361, canonicalMatch7_361, indexedKeyDecode7_361⟩
  · exact ⟨⟨316, by decide⟩, IndexedData7.key362, by decide, canonicalPose7_362, canonicalMatch7_362, indexedKeyDecode7_362⟩
  · exact ⟨⟨317, by decide⟩, IndexedData7.key363, by decide, canonicalPose7_363, canonicalMatch7_363, indexedKeyDecode7_363⟩
  · exact ⟨⟨318, by decide⟩, IndexedData7.key364, by decide, canonicalPose7_364, canonicalMatch7_364, indexedKeyDecode7_364⟩
  · exact ⟨⟨319, by decide⟩, IndexedData7.key365, by decide, canonicalPose7_365, canonicalMatch7_365, indexedKeyDecode7_365⟩
  · exact ⟨⟨320, by decide⟩, IndexedData7.key366, by decide, canonicalPose7_366, canonicalMatch7_366, indexedKeyDecode7_366⟩
  · exact ⟨⟨321, by decide⟩, IndexedData7.key367, by decide, canonicalPose7_367, canonicalMatch7_367, indexedKeyDecode7_367⟩
  · exact ⟨⟨322, by decide⟩, IndexedData7.key368, by decide, canonicalPose7_368, canonicalMatch7_368, indexedKeyDecode7_368⟩
  · exact ⟨⟨323, by decide⟩, IndexedData7.key369, by decide, canonicalPose7_369, canonicalMatch7_369, indexedKeyDecode7_369⟩
  · exact ⟨⟨324, by decide⟩, IndexedData7.key370, by decide, canonicalPose7_370, canonicalMatch7_370, indexedKeyDecode7_370⟩
  · exact ⟨⟨325, by decide⟩, IndexedData7.key371, by decide, canonicalPose7_371, canonicalMatch7_371, indexedKeyDecode7_371⟩
  · exact ⟨⟨326, by decide⟩, IndexedData7.key372, by decide, canonicalPose7_372, canonicalMatch7_372, indexedKeyDecode7_372⟩
  · exact ⟨⟨327, by decide⟩, IndexedData7.key373, by decide, canonicalPose7_373, canonicalMatch7_373, indexedKeyDecode7_373⟩
  · exact ⟨⟨327, by decide⟩, IndexedData7.key374, by decide, canonicalPose7_374, canonicalMatch7_374, indexedKeyDecode7_374⟩
  · exact ⟨⟨328, by decide⟩, IndexedData7.key375, by decide, canonicalPose7_375, canonicalMatch7_375, indexedKeyDecode7_375⟩
  · exact ⟨⟨329, by decide⟩, IndexedData7.key376, by decide, canonicalPose7_376, canonicalMatch7_376, indexedKeyDecode7_376⟩
  · exact ⟨⟨330, by decide⟩, IndexedData7.key377, by decide, canonicalPose7_377, canonicalMatch7_377, indexedKeyDecode7_377⟩
  · exact ⟨⟨330, by decide⟩, IndexedData7.key378, by decide, canonicalPose7_378, canonicalMatch7_378, indexedKeyDecode7_378⟩
  · exact ⟨⟨331, by decide⟩, IndexedData7.key379, by decide, canonicalPose7_379, canonicalMatch7_379, indexedKeyDecode7_379⟩
  · exact ⟨⟨332, by decide⟩, IndexedData7.key380, by decide, canonicalPose7_380, canonicalMatch7_380, indexedKeyDecode7_380⟩
  · exact ⟨⟨333, by decide⟩, IndexedData7.key381, by decide, canonicalPose7_381, canonicalMatch7_381, indexedKeyDecode7_381⟩
  · exact ⟨⟨334, by decide⟩, IndexedData7.key382, by decide, canonicalPose7_382, canonicalMatch7_382, indexedKeyDecode7_382⟩
  · exact ⟨⟨335, by decide⟩, IndexedData7.key383, by decide, canonicalPose7_383, canonicalMatch7_383, indexedKeyDecode7_383⟩

#print axioms keys7Chunk11_aligned

end SparseMonotiles.Canonical
