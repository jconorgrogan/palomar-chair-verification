module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk4

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk4_aligned : ∀ k ∈ keys7Chunk4,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk4, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨112, by decide⟩, IndexedData7.key128, by decide, canonicalPose7_128, canonicalMatch7_128, indexedKeyDecode7_128⟩
  · exact ⟨⟨113, by decide⟩, IndexedData7.key129, by decide, canonicalPose7_129, canonicalMatch7_129, indexedKeyDecode7_129⟩
  · exact ⟨⟨114, by decide⟩, IndexedData7.key130, by decide, canonicalPose7_130, canonicalMatch7_130, indexedKeyDecode7_130⟩
  · exact ⟨⟨114, by decide⟩, IndexedData7.key131, by decide, canonicalPose7_131, canonicalMatch7_131, indexedKeyDecode7_131⟩
  · exact ⟨⟨115, by decide⟩, IndexedData7.key132, by decide, canonicalPose7_132, canonicalMatch7_132, indexedKeyDecode7_132⟩
  · exact ⟨⟨116, by decide⟩, IndexedData7.key133, by decide, canonicalPose7_133, canonicalMatch7_133, indexedKeyDecode7_133⟩
  · exact ⟨⟨117, by decide⟩, IndexedData7.key134, by decide, canonicalPose7_134, canonicalMatch7_134, indexedKeyDecode7_134⟩
  · exact ⟨⟨118, by decide⟩, IndexedData7.key135, by decide, canonicalPose7_135, canonicalMatch7_135, indexedKeyDecode7_135⟩
  · exact ⟨⟨119, by decide⟩, IndexedData7.key136, by decide, canonicalPose7_136, canonicalMatch7_136, indexedKeyDecode7_136⟩
  · exact ⟨⟨120, by decide⟩, IndexedData7.key137, by decide, canonicalPose7_137, canonicalMatch7_137, indexedKeyDecode7_137⟩
  · exact ⟨⟨121, by decide⟩, IndexedData7.key138, by decide, canonicalPose7_138, canonicalMatch7_138, indexedKeyDecode7_138⟩
  · exact ⟨⟨122, by decide⟩, IndexedData7.key139, by decide, canonicalPose7_139, canonicalMatch7_139, indexedKeyDecode7_139⟩
  · exact ⟨⟨123, by decide⟩, IndexedData7.key140, by decide, canonicalPose7_140, canonicalMatch7_140, indexedKeyDecode7_140⟩
  · exact ⟨⟨123, by decide⟩, IndexedData7.key141, by decide, canonicalPose7_141, canonicalMatch7_141, indexedKeyDecode7_141⟩
  · exact ⟨⟨124, by decide⟩, IndexedData7.key142, by decide, canonicalPose7_142, canonicalMatch7_142, indexedKeyDecode7_142⟩
  · exact ⟨⟨125, by decide⟩, IndexedData7.key143, by decide, canonicalPose7_143, canonicalMatch7_143, indexedKeyDecode7_143⟩
  · exact ⟨⟨126, by decide⟩, IndexedData7.key144, by decide, canonicalPose7_144, canonicalMatch7_144, indexedKeyDecode7_144⟩
  · exact ⟨⟨126, by decide⟩, IndexedData7.key145, by decide, canonicalPose7_145, canonicalMatch7_145, indexedKeyDecode7_145⟩
  · exact ⟨⟨127, by decide⟩, IndexedData7.key146, by decide, canonicalPose7_146, canonicalMatch7_146, indexedKeyDecode7_146⟩
  · exact ⟨⟨128, by decide⟩, IndexedData7.key147, by decide, canonicalPose7_147, canonicalMatch7_147, indexedKeyDecode7_147⟩
  · exact ⟨⟨129, by decide⟩, IndexedData7.key148, by decide, canonicalPose7_148, canonicalMatch7_148, indexedKeyDecode7_148⟩
  · exact ⟨⟨130, by decide⟩, IndexedData7.key149, by decide, canonicalPose7_149, canonicalMatch7_149, indexedKeyDecode7_149⟩
  · exact ⟨⟨131, by decide⟩, IndexedData7.key150, by decide, canonicalPose7_150, canonicalMatch7_150, indexedKeyDecode7_150⟩
  · exact ⟨⟨132, by decide⟩, IndexedData7.key151, by decide, canonicalPose7_151, canonicalMatch7_151, indexedKeyDecode7_151⟩
  · exact ⟨⟨133, by decide⟩, IndexedData7.key152, by decide, canonicalPose7_152, canonicalMatch7_152, indexedKeyDecode7_152⟩
  · exact ⟨⟨134, by decide⟩, IndexedData7.key153, by decide, canonicalPose7_153, canonicalMatch7_153, indexedKeyDecode7_153⟩
  · exact ⟨⟨135, by decide⟩, IndexedData7.key154, by decide, canonicalPose7_154, canonicalMatch7_154, indexedKeyDecode7_154⟩
  · exact ⟨⟨135, by decide⟩, IndexedData7.key155, by decide, canonicalPose7_155, canonicalMatch7_155, indexedKeyDecode7_155⟩
  · exact ⟨⟨136, by decide⟩, IndexedData7.key156, by decide, canonicalPose7_156, canonicalMatch7_156, indexedKeyDecode7_156⟩
  · exact ⟨⟨137, by decide⟩, IndexedData7.key157, by decide, canonicalPose7_157, canonicalMatch7_157, indexedKeyDecode7_157⟩
  · exact ⟨⟨138, by decide⟩, IndexedData7.key158, by decide, canonicalPose7_158, canonicalMatch7_158, indexedKeyDecode7_158⟩
  · exact ⟨⟨139, by decide⟩, IndexedData7.key159, by decide, canonicalPose7_159, canonicalMatch7_159, indexedKeyDecode7_159⟩

#print axioms keys7Chunk4_aligned

end SparseMonotiles.Canonical
