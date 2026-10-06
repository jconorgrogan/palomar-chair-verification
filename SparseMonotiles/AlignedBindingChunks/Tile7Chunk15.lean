module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk15

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk15_aligned : ∀ k ∈ keys7Chunk15,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk15, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨420, by decide⟩, IndexedData7.key480, by decide, canonicalPose7_480, canonicalMatch7_480, indexedKeyDecode7_480⟩
  · exact ⟨⟨421, by decide⟩, IndexedData7.key481, by decide, canonicalPose7_481, canonicalMatch7_481, indexedKeyDecode7_481⟩
  · exact ⟨⟨422, by decide⟩, IndexedData7.key482, by decide, canonicalPose7_482, canonicalMatch7_482, indexedKeyDecode7_482⟩
  · exact ⟨⟨423, by decide⟩, IndexedData7.key483, by decide, canonicalPose7_483, canonicalMatch7_483, indexedKeyDecode7_483⟩
  · exact ⟨⟨424, by decide⟩, IndexedData7.key484, by decide, canonicalPose7_484, canonicalMatch7_484, indexedKeyDecode7_484⟩
  · exact ⟨⟨425, by decide⟩, IndexedData7.key485, by decide, canonicalPose7_485, canonicalMatch7_485, indexedKeyDecode7_485⟩
  · exact ⟨⟨426, by decide⟩, IndexedData7.key486, by decide, canonicalPose7_486, canonicalMatch7_486, indexedKeyDecode7_486⟩
  · exact ⟨⟨426, by decide⟩, IndexedData7.key487, by decide, canonicalPose7_487, canonicalMatch7_487, indexedKeyDecode7_487⟩
  · exact ⟨⟨427, by decide⟩, IndexedData7.key488, by decide, canonicalPose7_488, canonicalMatch7_488, indexedKeyDecode7_488⟩
  · exact ⟨⟨428, by decide⟩, IndexedData7.key489, by decide, canonicalPose7_489, canonicalMatch7_489, indexedKeyDecode7_489⟩
  · exact ⟨⟨429, by decide⟩, IndexedData7.key490, by decide, canonicalPose7_490, canonicalMatch7_490, indexedKeyDecode7_490⟩
  · exact ⟨⟨430, by decide⟩, IndexedData7.key491, by decide, canonicalPose7_491, canonicalMatch7_491, indexedKeyDecode7_491⟩
  · exact ⟨⟨431, by decide⟩, IndexedData7.key492, by decide, canonicalPose7_492, canonicalMatch7_492, indexedKeyDecode7_492⟩
  · exact ⟨⟨432, by decide⟩, IndexedData7.key493, by decide, canonicalPose7_493, canonicalMatch7_493, indexedKeyDecode7_493⟩
  · exact ⟨⟨433, by decide⟩, IndexedData7.key494, by decide, canonicalPose7_494, canonicalMatch7_494, indexedKeyDecode7_494⟩
  · exact ⟨⟨433, by decide⟩, IndexedData7.key495, by decide, canonicalPose7_495, canonicalMatch7_495, indexedKeyDecode7_495⟩
  · exact ⟨⟨434, by decide⟩, IndexedData7.key496, by decide, canonicalPose7_496, canonicalMatch7_496, indexedKeyDecode7_496⟩
  · exact ⟨⟨435, by decide⟩, IndexedData7.key497, by decide, canonicalPose7_497, canonicalMatch7_497, indexedKeyDecode7_497⟩
  · exact ⟨⟨436, by decide⟩, IndexedData7.key498, by decide, canonicalPose7_498, canonicalMatch7_498, indexedKeyDecode7_498⟩
  · exact ⟨⟨437, by decide⟩, IndexedData7.key499, by decide, canonicalPose7_499, canonicalMatch7_499, indexedKeyDecode7_499⟩
  · exact ⟨⟨437, by decide⟩, IndexedData7.key500, by decide, canonicalPose7_500, canonicalMatch7_500, indexedKeyDecode7_500⟩
  · exact ⟨⟨438, by decide⟩, IndexedData7.key501, by decide, canonicalPose7_501, canonicalMatch7_501, indexedKeyDecode7_501⟩
  · exact ⟨⟨439, by decide⟩, IndexedData7.key502, by decide, canonicalPose7_502, canonicalMatch7_502, indexedKeyDecode7_502⟩
  · exact ⟨⟨440, by decide⟩, IndexedData7.key503, by decide, canonicalPose7_503, canonicalMatch7_503, indexedKeyDecode7_503⟩
  · exact ⟨⟨441, by decide⟩, IndexedData7.key504, by decide, canonicalPose7_504, canonicalMatch7_504, indexedKeyDecode7_504⟩
  · exact ⟨⟨441, by decide⟩, IndexedData7.key505, by decide, canonicalPose7_505, canonicalMatch7_505, indexedKeyDecode7_505⟩
  · exact ⟨⟨442, by decide⟩, IndexedData7.key506, by decide, canonicalPose7_506, canonicalMatch7_506, indexedKeyDecode7_506⟩
  · exact ⟨⟨442, by decide⟩, IndexedData7.key507, by decide, canonicalPose7_507, canonicalMatch7_507, indexedKeyDecode7_507⟩
  · exact ⟨⟨443, by decide⟩, IndexedData7.key508, by decide, canonicalPose7_508, canonicalMatch7_508, indexedKeyDecode7_508⟩
  · exact ⟨⟨444, by decide⟩, IndexedData7.key509, by decide, canonicalPose7_509, canonicalMatch7_509, indexedKeyDecode7_509⟩
  · exact ⟨⟨445, by decide⟩, IndexedData7.key510, by decide, canonicalPose7_510, canonicalMatch7_510, indexedKeyDecode7_510⟩
  · exact ⟨⟨446, by decide⟩, IndexedData7.key511, by decide, canonicalPose7_511, canonicalMatch7_511, indexedKeyDecode7_511⟩

#print axioms keys7Chunk15_aligned

end SparseMonotiles.Canonical
