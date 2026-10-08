module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk16

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk16_aligned : ∀ k ∈ keys7Chunk16,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk16, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨447, by decide⟩, IndexedData7.key512, by decide, canonicalPose7_512, canonicalMatch7_512, indexedKeyDecode7_512⟩
  · exact ⟨⟨448, by decide⟩, IndexedData7.key513, by decide, canonicalPose7_513, canonicalMatch7_513, indexedKeyDecode7_513⟩
  · exact ⟨⟨449, by decide⟩, IndexedData7.key514, by decide, canonicalPose7_514, canonicalMatch7_514, indexedKeyDecode7_514⟩
  · exact ⟨⟨449, by decide⟩, IndexedData7.key515, by decide, canonicalPose7_515, canonicalMatch7_515, indexedKeyDecode7_515⟩
  · exact ⟨⟨450, by decide⟩, IndexedData7.key516, by decide, canonicalPose7_516, canonicalMatch7_516, indexedKeyDecode7_516⟩
  · exact ⟨⟨451, by decide⟩, IndexedData7.key517, by decide, canonicalPose7_517, canonicalMatch7_517, indexedKeyDecode7_517⟩
  · exact ⟨⟨452, by decide⟩, IndexedData7.key518, by decide, canonicalPose7_518, canonicalMatch7_518, indexedKeyDecode7_518⟩
  · exact ⟨⟨453, by decide⟩, IndexedData7.key519, by decide, canonicalPose7_519, canonicalMatch7_519, indexedKeyDecode7_519⟩
  · exact ⟨⟨454, by decide⟩, IndexedData7.key520, by decide, canonicalPose7_520, canonicalMatch7_520, indexedKeyDecode7_520⟩
  · exact ⟨⟨455, by decide⟩, IndexedData7.key521, by decide, canonicalPose7_521, canonicalMatch7_521, indexedKeyDecode7_521⟩
  · exact ⟨⟨456, by decide⟩, IndexedData7.key522, by decide, canonicalPose7_522, canonicalMatch7_522, indexedKeyDecode7_522⟩
  · exact ⟨⟨457, by decide⟩, IndexedData7.key523, by decide, canonicalPose7_523, canonicalMatch7_523, indexedKeyDecode7_523⟩
  · exact ⟨⟨458, by decide⟩, IndexedData7.key524, by decide, canonicalPose7_524, canonicalMatch7_524, indexedKeyDecode7_524⟩
  · exact ⟨⟨459, by decide⟩, IndexedData7.key525, by decide, canonicalPose7_525, canonicalMatch7_525, indexedKeyDecode7_525⟩
  · exact ⟨⟨459, by decide⟩, IndexedData7.key526, by decide, canonicalPose7_526, canonicalMatch7_526, indexedKeyDecode7_526⟩
  · exact ⟨⟨460, by decide⟩, IndexedData7.key527, by decide, canonicalPose7_527, canonicalMatch7_527, indexedKeyDecode7_527⟩
  · exact ⟨⟨461, by decide⟩, IndexedData7.key528, by decide, canonicalPose7_528, canonicalMatch7_528, indexedKeyDecode7_528⟩
  · exact ⟨⟨462, by decide⟩, IndexedData7.key529, by decide, canonicalPose7_529, canonicalMatch7_529, indexedKeyDecode7_529⟩
  · exact ⟨⟨463, by decide⟩, IndexedData7.key530, by decide, canonicalPose7_530, canonicalMatch7_530, indexedKeyDecode7_530⟩
  · exact ⟨⟨464, by decide⟩, IndexedData7.key531, by decide, canonicalPose7_531, canonicalMatch7_531, indexedKeyDecode7_531⟩
  · exact ⟨⟨465, by decide⟩, IndexedData7.key532, by decide, canonicalPose7_532, canonicalMatch7_532, indexedKeyDecode7_532⟩
  · exact ⟨⟨466, by decide⟩, IndexedData7.key533, by decide, canonicalPose7_533, canonicalMatch7_533, indexedKeyDecode7_533⟩
  · exact ⟨⟨467, by decide⟩, IndexedData7.key534, by decide, canonicalPose7_534, canonicalMatch7_534, indexedKeyDecode7_534⟩
  · exact ⟨⟨468, by decide⟩, IndexedData7.key535, by decide, canonicalPose7_535, canonicalMatch7_535, indexedKeyDecode7_535⟩
  · exact ⟨⟨469, by decide⟩, IndexedData7.key536, by decide, canonicalPose7_536, canonicalMatch7_536, indexedKeyDecode7_536⟩
  · exact ⟨⟨469, by decide⟩, IndexedData7.key537, by decide, canonicalPose7_537, canonicalMatch7_537, indexedKeyDecode7_537⟩
  · exact ⟨⟨470, by decide⟩, IndexedData7.key538, by decide, canonicalPose7_538, canonicalMatch7_538, indexedKeyDecode7_538⟩
  · exact ⟨⟨471, by decide⟩, IndexedData7.key539, by decide, canonicalPose7_539, canonicalMatch7_539, indexedKeyDecode7_539⟩
  · exact ⟨⟨472, by decide⟩, IndexedData7.key540, by decide, canonicalPose7_540, canonicalMatch7_540, indexedKeyDecode7_540⟩
  · exact ⟨⟨473, by decide⟩, IndexedData7.key541, by decide, canonicalPose7_541, canonicalMatch7_541, indexedKeyDecode7_541⟩
  · exact ⟨⟨474, by decide⟩, IndexedData7.key542, by decide, canonicalPose7_542, canonicalMatch7_542, indexedKeyDecode7_542⟩
  · exact ⟨⟨475, by decide⟩, IndexedData7.key543, by decide, canonicalPose7_543, canonicalMatch7_543, indexedKeyDecode7_543⟩

#print axioms keys7Chunk16_aligned

end SparseMonotiles.Canonical
