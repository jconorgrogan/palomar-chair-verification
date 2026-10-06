module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk5

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk5_aligned : ∀ k ∈ keys5Chunk5,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk5, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨100, by decide⟩, IndexedData5.key160, by decide, canonicalPose5_160, canonicalMatch5_160, indexedKeyDecode5_160⟩
  · exact ⟨⟨100, by decide⟩, IndexedData5.key161, by decide, canonicalPose5_161, canonicalMatch5_161, indexedKeyDecode5_161⟩
  · exact ⟨⟨100, by decide⟩, IndexedData5.key162, by decide, canonicalPose5_162, canonicalMatch5_162, indexedKeyDecode5_162⟩
  · exact ⟨⟨100, by decide⟩, IndexedData5.key163, by decide, canonicalPose5_163, canonicalMatch5_163, indexedKeyDecode5_163⟩
  · exact ⟨⟨101, by decide⟩, IndexedData5.key164, by decide, canonicalPose5_164, canonicalMatch5_164, indexedKeyDecode5_164⟩
  · exact ⟨⟨102, by decide⟩, IndexedData5.key165, by decide, canonicalPose5_165, canonicalMatch5_165, indexedKeyDecode5_165⟩
  · exact ⟨⟨102, by decide⟩, IndexedData5.key166, by decide, canonicalPose5_166, canonicalMatch5_166, indexedKeyDecode5_166⟩
  · exact ⟨⟨102, by decide⟩, IndexedData5.key167, by decide, canonicalPose5_167, canonicalMatch5_167, indexedKeyDecode5_167⟩
  · exact ⟨⟨102, by decide⟩, IndexedData5.key168, by decide, canonicalPose5_168, canonicalMatch5_168, indexedKeyDecode5_168⟩
  · exact ⟨⟨103, by decide⟩, IndexedData5.key169, by decide, canonicalPose5_169, canonicalMatch5_169, indexedKeyDecode5_169⟩
  · exact ⟨⟨104, by decide⟩, IndexedData5.key170, by decide, canonicalPose5_170, canonicalMatch5_170, indexedKeyDecode5_170⟩
  · exact ⟨⟨105, by decide⟩, IndexedData5.key171, by decide, canonicalPose5_171, canonicalMatch5_171, indexedKeyDecode5_171⟩
  · exact ⟨⟨106, by decide⟩, IndexedData5.key172, by decide, canonicalPose5_172, canonicalMatch5_172, indexedKeyDecode5_172⟩
  · exact ⟨⟨107, by decide⟩, IndexedData5.key173, by decide, canonicalPose5_173, canonicalMatch5_173, indexedKeyDecode5_173⟩
  · exact ⟨⟨108, by decide⟩, IndexedData5.key174, by decide, canonicalPose5_174, canonicalMatch5_174, indexedKeyDecode5_174⟩
  · exact ⟨⟨108, by decide⟩, IndexedData5.key175, by decide, canonicalPose5_175, canonicalMatch5_175, indexedKeyDecode5_175⟩
  · exact ⟨⟨108, by decide⟩, IndexedData5.key176, by decide, canonicalPose5_176, canonicalMatch5_176, indexedKeyDecode5_176⟩
  · exact ⟨⟨108, by decide⟩, IndexedData5.key177, by decide, canonicalPose5_177, canonicalMatch5_177, indexedKeyDecode5_177⟩
  · exact ⟨⟨109, by decide⟩, IndexedData5.key178, by decide, canonicalPose5_178, canonicalMatch5_178, indexedKeyDecode5_178⟩
  · exact ⟨⟨110, by decide⟩, IndexedData5.key179, by decide, canonicalPose5_179, canonicalMatch5_179, indexedKeyDecode5_179⟩
  · exact ⟨⟨111, by decide⟩, IndexedData5.key180, by decide, canonicalPose5_180, canonicalMatch5_180, indexedKeyDecode5_180⟩
  · exact ⟨⟨111, by decide⟩, IndexedData5.key181, by decide, canonicalPose5_181, canonicalMatch5_181, indexedKeyDecode5_181⟩
  · exact ⟨⟨111, by decide⟩, IndexedData5.key182, by decide, canonicalPose5_182, canonicalMatch5_182, indexedKeyDecode5_182⟩
  · exact ⟨⟨111, by decide⟩, IndexedData5.key183, by decide, canonicalPose5_183, canonicalMatch5_183, indexedKeyDecode5_183⟩
  · exact ⟨⟨112, by decide⟩, IndexedData5.key184, by decide, canonicalPose5_184, canonicalMatch5_184, indexedKeyDecode5_184⟩
  · exact ⟨⟨113, by decide⟩, IndexedData5.key185, by decide, canonicalPose5_185, canonicalMatch5_185, indexedKeyDecode5_185⟩
  · exact ⟨⟨114, by decide⟩, IndexedData5.key186, by decide, canonicalPose5_186, canonicalMatch5_186, indexedKeyDecode5_186⟩
  · exact ⟨⟨115, by decide⟩, IndexedData5.key187, by decide, canonicalPose5_187, canonicalMatch5_187, indexedKeyDecode5_187⟩
  · exact ⟨⟨116, by decide⟩, IndexedData5.key188, by decide, canonicalPose5_188, canonicalMatch5_188, indexedKeyDecode5_188⟩
  · exact ⟨⟨117, by decide⟩, IndexedData5.key189, by decide, canonicalPose5_189, canonicalMatch5_189, indexedKeyDecode5_189⟩
  · exact ⟨⟨117, by decide⟩, IndexedData5.key190, by decide, canonicalPose5_190, canonicalMatch5_190, indexedKeyDecode5_190⟩
  · exact ⟨⟨117, by decide⟩, IndexedData5.key191, by decide, canonicalPose5_191, canonicalMatch5_191, indexedKeyDecode5_191⟩

#print axioms keys5Chunk5_aligned

end SparseMonotiles.Canonical
