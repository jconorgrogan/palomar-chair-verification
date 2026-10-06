module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk13

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk13_aligned : ∀ k ∈ keys7Chunk13,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk13, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨364, by decide⟩, IndexedData7.key416, by decide, canonicalPose7_416, canonicalMatch7_416, indexedKeyDecode7_416⟩
  · exact ⟨⟨364, by decide⟩, IndexedData7.key417, by decide, canonicalPose7_417, canonicalMatch7_417, indexedKeyDecode7_417⟩
  · exact ⟨⟨365, by decide⟩, IndexedData7.key418, by decide, canonicalPose7_418, canonicalMatch7_418, indexedKeyDecode7_418⟩
  · exact ⟨⟨366, by decide⟩, IndexedData7.key419, by decide, canonicalPose7_419, canonicalMatch7_419, indexedKeyDecode7_419⟩
  · exact ⟨⟨367, by decide⟩, IndexedData7.key420, by decide, canonicalPose7_420, canonicalMatch7_420, indexedKeyDecode7_420⟩
  · exact ⟨⟨368, by decide⟩, IndexedData7.key421, by decide, canonicalPose7_421, canonicalMatch7_421, indexedKeyDecode7_421⟩
  · exact ⟨⟨369, by decide⟩, IndexedData7.key422, by decide, canonicalPose7_422, canonicalMatch7_422, indexedKeyDecode7_422⟩
  · exact ⟨⟨370, by decide⟩, IndexedData7.key423, by decide, canonicalPose7_423, canonicalMatch7_423, indexedKeyDecode7_423⟩
  · exact ⟨⟨371, by decide⟩, IndexedData7.key424, by decide, canonicalPose7_424, canonicalMatch7_424, indexedKeyDecode7_424⟩
  · exact ⟨⟨372, by decide⟩, IndexedData7.key425, by decide, canonicalPose7_425, canonicalMatch7_425, indexedKeyDecode7_425⟩
  · exact ⟨⟨373, by decide⟩, IndexedData7.key426, by decide, canonicalPose7_426, canonicalMatch7_426, indexedKeyDecode7_426⟩
  · exact ⟨⟨374, by decide⟩, IndexedData7.key427, by decide, canonicalPose7_427, canonicalMatch7_427, indexedKeyDecode7_427⟩
  · exact ⟨⟨375, by decide⟩, IndexedData7.key428, by decide, canonicalPose7_428, canonicalMatch7_428, indexedKeyDecode7_428⟩
  · exact ⟨⟨376, by decide⟩, IndexedData7.key429, by decide, canonicalPose7_429, canonicalMatch7_429, indexedKeyDecode7_429⟩
  · exact ⟨⟨376, by decide⟩, IndexedData7.key430, by decide, canonicalPose7_430, canonicalMatch7_430, indexedKeyDecode7_430⟩
  · exact ⟨⟨377, by decide⟩, IndexedData7.key431, by decide, canonicalPose7_431, canonicalMatch7_431, indexedKeyDecode7_431⟩
  · exact ⟨⟨378, by decide⟩, IndexedData7.key432, by decide, canonicalPose7_432, canonicalMatch7_432, indexedKeyDecode7_432⟩
  · exact ⟨⟨379, by decide⟩, IndexedData7.key433, by decide, canonicalPose7_433, canonicalMatch7_433, indexedKeyDecode7_433⟩
  · exact ⟨⟨380, by decide⟩, IndexedData7.key434, by decide, canonicalPose7_434, canonicalMatch7_434, indexedKeyDecode7_434⟩
  · exact ⟨⟨381, by decide⟩, IndexedData7.key435, by decide, canonicalPose7_435, canonicalMatch7_435, indexedKeyDecode7_435⟩
  · exact ⟨⟨381, by decide⟩, IndexedData7.key436, by decide, canonicalPose7_436, canonicalMatch7_436, indexedKeyDecode7_436⟩
  · exact ⟨⟨382, by decide⟩, IndexedData7.key437, by decide, canonicalPose7_437, canonicalMatch7_437, indexedKeyDecode7_437⟩
  · exact ⟨⟨383, by decide⟩, IndexedData7.key438, by decide, canonicalPose7_438, canonicalMatch7_438, indexedKeyDecode7_438⟩
  · exact ⟨⟨384, by decide⟩, IndexedData7.key439, by decide, canonicalPose7_439, canonicalMatch7_439, indexedKeyDecode7_439⟩
  · exact ⟨⟨385, by decide⟩, IndexedData7.key440, by decide, canonicalPose7_440, canonicalMatch7_440, indexedKeyDecode7_440⟩
  · exact ⟨⟨386, by decide⟩, IndexedData7.key441, by decide, canonicalPose7_441, canonicalMatch7_441, indexedKeyDecode7_441⟩
  · exact ⟨⟨387, by decide⟩, IndexedData7.key442, by decide, canonicalPose7_442, canonicalMatch7_442, indexedKeyDecode7_442⟩
  · exact ⟨⟨388, by decide⟩, IndexedData7.key443, by decide, canonicalPose7_443, canonicalMatch7_443, indexedKeyDecode7_443⟩
  · exact ⟨⟨389, by decide⟩, IndexedData7.key444, by decide, canonicalPose7_444, canonicalMatch7_444, indexedKeyDecode7_444⟩
  · exact ⟨⟨390, by decide⟩, IndexedData7.key445, by decide, canonicalPose7_445, canonicalMatch7_445, indexedKeyDecode7_445⟩
  · exact ⟨⟨390, by decide⟩, IndexedData7.key446, by decide, canonicalPose7_446, canonicalMatch7_446, indexedKeyDecode7_446⟩
  · exact ⟨⟨391, by decide⟩, IndexedData7.key447, by decide, canonicalPose7_447, canonicalMatch7_447, indexedKeyDecode7_447⟩

#print axioms keys7Chunk13_aligned

end SparseMonotiles.Canonical
