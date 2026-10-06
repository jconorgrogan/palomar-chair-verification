module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk17

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk17_aligned : ∀ k ∈ keys7Chunk17,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk17, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨476, by decide⟩, IndexedData7.key544, by decide, canonicalPose7_544, canonicalMatch7_544, indexedKeyDecode7_544⟩
  · exact ⟨⟨476, by decide⟩, IndexedData7.key545, by decide, canonicalPose7_545, canonicalMatch7_545, indexedKeyDecode7_545⟩
  · exact ⟨⟨477, by decide⟩, IndexedData7.key546, by decide, canonicalPose7_546, canonicalMatch7_546, indexedKeyDecode7_546⟩
  · exact ⟨⟨478, by decide⟩, IndexedData7.key547, by decide, canonicalPose7_547, canonicalMatch7_547, indexedKeyDecode7_547⟩
  · exact ⟨⟨479, by decide⟩, IndexedData7.key548, by decide, canonicalPose7_548, canonicalMatch7_548, indexedKeyDecode7_548⟩
  · exact ⟨⟨479, by decide⟩, IndexedData7.key549, by decide, canonicalPose7_549, canonicalMatch7_549, indexedKeyDecode7_549⟩
  · exact ⟨⟨480, by decide⟩, IndexedData7.key550, by decide, canonicalPose7_550, canonicalMatch7_550, indexedKeyDecode7_550⟩
  · exact ⟨⟨481, by decide⟩, IndexedData7.key551, by decide, canonicalPose7_551, canonicalMatch7_551, indexedKeyDecode7_551⟩
  · exact ⟨⟨482, by decide⟩, IndexedData7.key552, by decide, canonicalPose7_552, canonicalMatch7_552, indexedKeyDecode7_552⟩
  · exact ⟨⟨483, by decide⟩, IndexedData7.key553, by decide, canonicalPose7_553, canonicalMatch7_553, indexedKeyDecode7_553⟩
  · exact ⟨⟨484, by decide⟩, IndexedData7.key554, by decide, canonicalPose7_554, canonicalMatch7_554, indexedKeyDecode7_554⟩
  · exact ⟨⟨485, by decide⟩, IndexedData7.key555, by decide, canonicalPose7_555, canonicalMatch7_555, indexedKeyDecode7_555⟩
  · exact ⟨⟨485, by decide⟩, IndexedData7.key556, by decide, canonicalPose7_556, canonicalMatch7_556, indexedKeyDecode7_556⟩
  · exact ⟨⟨486, by decide⟩, IndexedData7.key557, by decide, canonicalPose7_557, canonicalMatch7_557, indexedKeyDecode7_557⟩
  · exact ⟨⟨487, by decide⟩, IndexedData7.key558, by decide, canonicalPose7_558, canonicalMatch7_558, indexedKeyDecode7_558⟩
  · exact ⟨⟨488, by decide⟩, IndexedData7.key559, by decide, canonicalPose7_559, canonicalMatch7_559, indexedKeyDecode7_559⟩
  · exact ⟨⟨489, by decide⟩, IndexedData7.key560, by decide, canonicalPose7_560, canonicalMatch7_560, indexedKeyDecode7_560⟩
  · exact ⟨⟨490, by decide⟩, IndexedData7.key561, by decide, canonicalPose7_561, canonicalMatch7_561, indexedKeyDecode7_561⟩
  · exact ⟨⟨491, by decide⟩, IndexedData7.key562, by decide, canonicalPose7_562, canonicalMatch7_562, indexedKeyDecode7_562⟩
  · exact ⟨⟨492, by decide⟩, IndexedData7.key563, by decide, canonicalPose7_563, canonicalMatch7_563, indexedKeyDecode7_563⟩
  · exact ⟨⟨493, by decide⟩, IndexedData7.key564, by decide, canonicalPose7_564, canonicalMatch7_564, indexedKeyDecode7_564⟩
  · exact ⟨⟨494, by decide⟩, IndexedData7.key565, by decide, canonicalPose7_565, canonicalMatch7_565, indexedKeyDecode7_565⟩
  · exact ⟨⟨494, by decide⟩, IndexedData7.key566, by decide, canonicalPose7_566, canonicalMatch7_566, indexedKeyDecode7_566⟩
  · exact ⟨⟨495, by decide⟩, IndexedData7.key567, by decide, canonicalPose7_567, canonicalMatch7_567, indexedKeyDecode7_567⟩
  · exact ⟨⟨496, by decide⟩, IndexedData7.key568, by decide, canonicalPose7_568, canonicalMatch7_568, indexedKeyDecode7_568⟩
  · exact ⟨⟨497, by decide⟩, IndexedData7.key569, by decide, canonicalPose7_569, canonicalMatch7_569, indexedKeyDecode7_569⟩
  · exact ⟨⟨498, by decide⟩, IndexedData7.key570, by decide, canonicalPose7_570, canonicalMatch7_570, indexedKeyDecode7_570⟩
  · exact ⟨⟨499, by decide⟩, IndexedData7.key571, by decide, canonicalPose7_571, canonicalMatch7_571, indexedKeyDecode7_571⟩
  · exact ⟨⟨500, by decide⟩, IndexedData7.key572, by decide, canonicalPose7_572, canonicalMatch7_572, indexedKeyDecode7_572⟩
  · exact ⟨⟨500, by decide⟩, IndexedData7.key573, by decide, canonicalPose7_573, canonicalMatch7_573, indexedKeyDecode7_573⟩
  · exact ⟨⟨501, by decide⟩, IndexedData7.key574, by decide, canonicalPose7_574, canonicalMatch7_574, indexedKeyDecode7_574⟩
  · exact ⟨⟨502, by decide⟩, IndexedData7.key575, by decide, canonicalPose7_575, canonicalMatch7_575, indexedKeyDecode7_575⟩

#print axioms keys7Chunk17_aligned

end SparseMonotiles.Canonical
