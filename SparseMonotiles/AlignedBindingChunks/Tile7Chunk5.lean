module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk5

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk5_aligned : ∀ k ∈ keys7Chunk5,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk5, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨140, by decide⟩, IndexedData7.key160, by decide, canonicalPose7_160, canonicalMatch7_160, indexedKeyDecode7_160⟩
  · exact ⟨⟨141, by decide⟩, IndexedData7.key161, by decide, canonicalPose7_161, canonicalMatch7_161, indexedKeyDecode7_161⟩
  · exact ⟨⟨142, by decide⟩, IndexedData7.key162, by decide, canonicalPose7_162, canonicalMatch7_162, indexedKeyDecode7_162⟩
  · exact ⟨⟨143, by decide⟩, IndexedData7.key163, by decide, canonicalPose7_163, canonicalMatch7_163, indexedKeyDecode7_163⟩
  · exact ⟨⟨143, by decide⟩, IndexedData7.key164, by decide, canonicalPose7_164, canonicalMatch7_164, indexedKeyDecode7_164⟩
  · exact ⟨⟨144, by decide⟩, IndexedData7.key165, by decide, canonicalPose7_165, canonicalMatch7_165, indexedKeyDecode7_165⟩
  · exact ⟨⟨145, by decide⟩, IndexedData7.key166, by decide, canonicalPose7_166, canonicalMatch7_166, indexedKeyDecode7_166⟩
  · exact ⟨⟨146, by decide⟩, IndexedData7.key167, by decide, canonicalPose7_167, canonicalMatch7_167, indexedKeyDecode7_167⟩
  · exact ⟨⟨147, by decide⟩, IndexedData7.key168, by decide, canonicalPose7_168, canonicalMatch7_168, indexedKeyDecode7_168⟩
  · exact ⟨⟨148, by decide⟩, IndexedData7.key169, by decide, canonicalPose7_169, canonicalMatch7_169, indexedKeyDecode7_169⟩
  · exact ⟨⟨149, by decide⟩, IndexedData7.key170, by decide, canonicalPose7_170, canonicalMatch7_170, indexedKeyDecode7_170⟩
  · exact ⟨⟨150, by decide⟩, IndexedData7.key171, by decide, canonicalPose7_171, canonicalMatch7_171, indexedKeyDecode7_171⟩
  · exact ⟨⟨151, by decide⟩, IndexedData7.key172, by decide, canonicalPose7_172, canonicalMatch7_172, indexedKeyDecode7_172⟩
  · exact ⟨⟨151, by decide⟩, IndexedData7.key173, by decide, canonicalPose7_173, canonicalMatch7_173, indexedKeyDecode7_173⟩
  · exact ⟨⟨152, by decide⟩, IndexedData7.key174, by decide, canonicalPose7_174, canonicalMatch7_174, indexedKeyDecode7_174⟩
  · exact ⟨⟨153, by decide⟩, IndexedData7.key175, by decide, canonicalPose7_175, canonicalMatch7_175, indexedKeyDecode7_175⟩
  · exact ⟨⟨154, by decide⟩, IndexedData7.key176, by decide, canonicalPose7_176, canonicalMatch7_176, indexedKeyDecode7_176⟩
  · exact ⟨⟨155, by decide⟩, IndexedData7.key177, by decide, canonicalPose7_177, canonicalMatch7_177, indexedKeyDecode7_177⟩
  · exact ⟨⟨156, by decide⟩, IndexedData7.key178, by decide, canonicalPose7_178, canonicalMatch7_178, indexedKeyDecode7_178⟩
  · exact ⟨⟨157, by decide⟩, IndexedData7.key179, by decide, canonicalPose7_179, canonicalMatch7_179, indexedKeyDecode7_179⟩
  · exact ⟨⟨158, by decide⟩, IndexedData7.key180, by decide, canonicalPose7_180, canonicalMatch7_180, indexedKeyDecode7_180⟩
  · exact ⟨⟨159, by decide⟩, IndexedData7.key181, by decide, canonicalPose7_181, canonicalMatch7_181, indexedKeyDecode7_181⟩
  · exact ⟨⟨160, by decide⟩, IndexedData7.key182, by decide, canonicalPose7_182, canonicalMatch7_182, indexedKeyDecode7_182⟩
  · exact ⟨⟨160, by decide⟩, IndexedData7.key183, by decide, canonicalPose7_183, canonicalMatch7_183, indexedKeyDecode7_183⟩
  · exact ⟨⟨161, by decide⟩, IndexedData7.key184, by decide, canonicalPose7_184, canonicalMatch7_184, indexedKeyDecode7_184⟩
  · exact ⟨⟨162, by decide⟩, IndexedData7.key185, by decide, canonicalPose7_185, canonicalMatch7_185, indexedKeyDecode7_185⟩
  · exact ⟨⟨163, by decide⟩, IndexedData7.key186, by decide, canonicalPose7_186, canonicalMatch7_186, indexedKeyDecode7_186⟩
  · exact ⟨⟨164, by decide⟩, IndexedData7.key187, by decide, canonicalPose7_187, canonicalMatch7_187, indexedKeyDecode7_187⟩
  · exact ⟨⟨165, by decide⟩, IndexedData7.key188, by decide, canonicalPose7_188, canonicalMatch7_188, indexedKeyDecode7_188⟩
  · exact ⟨⟨166, by decide⟩, IndexedData7.key189, by decide, canonicalPose7_189, canonicalMatch7_189, indexedKeyDecode7_189⟩
  · exact ⟨⟨167, by decide⟩, IndexedData7.key190, by decide, canonicalPose7_190, canonicalMatch7_190, indexedKeyDecode7_190⟩
  · exact ⟨⟨167, by decide⟩, IndexedData7.key191, by decide, canonicalPose7_191, canonicalMatch7_191, indexedKeyDecode7_191⟩

#print axioms keys7Chunk5_aligned

end SparseMonotiles.Canonical
