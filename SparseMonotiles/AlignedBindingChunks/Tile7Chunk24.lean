module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk24

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk24_aligned : ∀ k ∈ keys7Chunk24,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk24, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨671, by decide⟩, IndexedData7.key768, by decide, canonicalPose7_768, canonicalMatch7_768, indexedKeyDecode7_768⟩
  · exact ⟨⟨672, by decide⟩, IndexedData7.key769, by decide, canonicalPose7_769, canonicalMatch7_769, indexedKeyDecode7_769⟩
  · exact ⟨⟨673, by decide⟩, IndexedData7.key770, by decide, canonicalPose7_770, canonicalMatch7_770, indexedKeyDecode7_770⟩
  · exact ⟨⟨674, by decide⟩, IndexedData7.key771, by decide, canonicalPose7_771, canonicalMatch7_771, indexedKeyDecode7_771⟩
  · exact ⟨⟨675, by decide⟩, IndexedData7.key772, by decide, canonicalPose7_772, canonicalMatch7_772, indexedKeyDecode7_772⟩
  · exact ⟨⟨676, by decide⟩, IndexedData7.key773, by decide, canonicalPose7_773, canonicalMatch7_773, indexedKeyDecode7_773⟩
  · exact ⟨⟨677, by decide⟩, IndexedData7.key774, by decide, canonicalPose7_774, canonicalMatch7_774, indexedKeyDecode7_774⟩
  · exact ⟨⟨678, by decide⟩, IndexedData7.key775, by decide, canonicalPose7_775, canonicalMatch7_775, indexedKeyDecode7_775⟩
  · exact ⟨⟨678, by decide⟩, IndexedData7.key776, by decide, canonicalPose7_776, canonicalMatch7_776, indexedKeyDecode7_776⟩
  · exact ⟨⟨679, by decide⟩, IndexedData7.key777, by decide, canonicalPose7_777, canonicalMatch7_777, indexedKeyDecode7_777⟩
  · exact ⟨⟨680, by decide⟩, IndexedData7.key778, by decide, canonicalPose7_778, canonicalMatch7_778, indexedKeyDecode7_778⟩
  · exact ⟨⟨681, by decide⟩, IndexedData7.key779, by decide, canonicalPose7_779, canonicalMatch7_779, indexedKeyDecode7_779⟩
  · exact ⟨⟨681, by decide⟩, IndexedData7.key780, by decide, canonicalPose7_780, canonicalMatch7_780, indexedKeyDecode7_780⟩
  · exact ⟨⟨682, by decide⟩, IndexedData7.key781, by decide, canonicalPose7_781, canonicalMatch7_781, indexedKeyDecode7_781⟩
  · exact ⟨⟨683, by decide⟩, IndexedData7.key782, by decide, canonicalPose7_782, canonicalMatch7_782, indexedKeyDecode7_782⟩
  · exact ⟨⟨684, by decide⟩, IndexedData7.key783, by decide, canonicalPose7_783, canonicalMatch7_783, indexedKeyDecode7_783⟩
  · exact ⟨⟨685, by decide⟩, IndexedData7.key784, by decide, canonicalPose7_784, canonicalMatch7_784, indexedKeyDecode7_784⟩
  · exact ⟨⟨686, by decide⟩, IndexedData7.key785, by decide, canonicalPose7_785, canonicalMatch7_785, indexedKeyDecode7_785⟩
  · exact ⟨⟨687, by decide⟩, IndexedData7.key786, by decide, canonicalPose7_786, canonicalMatch7_786, indexedKeyDecode7_786⟩
  · exact ⟨⟨688, by decide⟩, IndexedData7.key787, by decide, canonicalPose7_787, canonicalMatch7_787, indexedKeyDecode7_787⟩
  · exact ⟨⟨689, by decide⟩, IndexedData7.key788, by decide, canonicalPose7_788, canonicalMatch7_788, indexedKeyDecode7_788⟩
  · exact ⟨⟨690, by decide⟩, IndexedData7.key789, by decide, canonicalPose7_789, canonicalMatch7_789, indexedKeyDecode7_789⟩
  · exact ⟨⟨690, by decide⟩, IndexedData7.key790, by decide, canonicalPose7_790, canonicalMatch7_790, indexedKeyDecode7_790⟩
  · exact ⟨⟨691, by decide⟩, IndexedData7.key791, by decide, canonicalPose7_791, canonicalMatch7_791, indexedKeyDecode7_791⟩
  · exact ⟨⟨692, by decide⟩, IndexedData7.key792, by decide, canonicalPose7_792, canonicalMatch7_792, indexedKeyDecode7_792⟩
  · exact ⟨⟨693, by decide⟩, IndexedData7.key793, by decide, canonicalPose7_793, canonicalMatch7_793, indexedKeyDecode7_793⟩
  · exact ⟨⟨694, by decide⟩, IndexedData7.key794, by decide, canonicalPose7_794, canonicalMatch7_794, indexedKeyDecode7_794⟩
  · exact ⟨⟨695, by decide⟩, IndexedData7.key795, by decide, canonicalPose7_795, canonicalMatch7_795, indexedKeyDecode7_795⟩
  · exact ⟨⟨696, by decide⟩, IndexedData7.key796, by decide, canonicalPose7_796, canonicalMatch7_796, indexedKeyDecode7_796⟩
  · exact ⟨⟨697, by decide⟩, IndexedData7.key797, by decide, canonicalPose7_797, canonicalMatch7_797, indexedKeyDecode7_797⟩
  · exact ⟨⟨698, by decide⟩, IndexedData7.key798, by decide, canonicalPose7_798, canonicalMatch7_798, indexedKeyDecode7_798⟩
  · exact ⟨⟨698, by decide⟩, IndexedData7.key799, by decide, canonicalPose7_799, canonicalMatch7_799, indexedKeyDecode7_799⟩

#print axioms keys7Chunk24_aligned

end SparseMonotiles.Canonical
