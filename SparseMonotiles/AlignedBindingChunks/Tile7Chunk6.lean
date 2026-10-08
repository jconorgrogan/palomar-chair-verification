module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk6

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk6_aligned : ∀ k ∈ keys7Chunk6,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk6, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨168, by decide⟩, IndexedData7.key192, by decide, canonicalPose7_192, canonicalMatch7_192, indexedKeyDecode7_192⟩
  · exact ⟨⟨169, by decide⟩, IndexedData7.key193, by decide, canonicalPose7_193, canonicalMatch7_193, indexedKeyDecode7_193⟩
  · exact ⟨⟨170, by decide⟩, IndexedData7.key194, by decide, canonicalPose7_194, canonicalMatch7_194, indexedKeyDecode7_194⟩
  · exact ⟨⟨171, by decide⟩, IndexedData7.key195, by decide, canonicalPose7_195, canonicalMatch7_195, indexedKeyDecode7_195⟩
  · exact ⟨⟨172, by decide⟩, IndexedData7.key196, by decide, canonicalPose7_196, canonicalMatch7_196, indexedKeyDecode7_196⟩
  · exact ⟨⟨173, by decide⟩, IndexedData7.key197, by decide, canonicalPose7_197, canonicalMatch7_197, indexedKeyDecode7_197⟩
  · exact ⟨⟨174, by decide⟩, IndexedData7.key198, by decide, canonicalPose7_198, canonicalMatch7_198, indexedKeyDecode7_198⟩
  · exact ⟨⟨174, by decide⟩, IndexedData7.key199, by decide, canonicalPose7_199, canonicalMatch7_199, indexedKeyDecode7_199⟩
  · exact ⟨⟨175, by decide⟩, IndexedData7.key200, by decide, canonicalPose7_200, canonicalMatch7_200, indexedKeyDecode7_200⟩
  · exact ⟨⟨176, by decide⟩, IndexedData7.key201, by decide, canonicalPose7_201, canonicalMatch7_201, indexedKeyDecode7_201⟩
  · exact ⟨⟨177, by decide⟩, IndexedData7.key202, by decide, canonicalPose7_202, canonicalMatch7_202, indexedKeyDecode7_202⟩
  · exact ⟨⟨178, by decide⟩, IndexedData7.key203, by decide, canonicalPose7_203, canonicalMatch7_203, indexedKeyDecode7_203⟩
  · exact ⟨⟨179, by decide⟩, IndexedData7.key204, by decide, canonicalPose7_204, canonicalMatch7_204, indexedKeyDecode7_204⟩
  · exact ⟨⟨180, by decide⟩, IndexedData7.key205, by decide, canonicalPose7_205, canonicalMatch7_205, indexedKeyDecode7_205⟩
  · exact ⟨⟨181, by decide⟩, IndexedData7.key206, by decide, canonicalPose7_206, canonicalMatch7_206, indexedKeyDecode7_206⟩
  · exact ⟨⟨181, by decide⟩, IndexedData7.key207, by decide, canonicalPose7_207, canonicalMatch7_207, indexedKeyDecode7_207⟩
  · exact ⟨⟨182, by decide⟩, IndexedData7.key208, by decide, canonicalPose7_208, canonicalMatch7_208, indexedKeyDecode7_208⟩
  · exact ⟨⟨183, by decide⟩, IndexedData7.key209, by decide, canonicalPose7_209, canonicalMatch7_209, indexedKeyDecode7_209⟩
  · exact ⟨⟨183, by decide⟩, IndexedData7.key210, by decide, canonicalPose7_210, canonicalMatch7_210, indexedKeyDecode7_210⟩
  · exact ⟨⟨184, by decide⟩, IndexedData7.key211, by decide, canonicalPose7_211, canonicalMatch7_211, indexedKeyDecode7_211⟩
  · exact ⟨⟨185, by decide⟩, IndexedData7.key212, by decide, canonicalPose7_212, canonicalMatch7_212, indexedKeyDecode7_212⟩
  · exact ⟨⟨186, by decide⟩, IndexedData7.key213, by decide, canonicalPose7_213, canonicalMatch7_213, indexedKeyDecode7_213⟩
  · exact ⟨⟨187, by decide⟩, IndexedData7.key214, by decide, canonicalPose7_214, canonicalMatch7_214, indexedKeyDecode7_214⟩
  · exact ⟨⟨188, by decide⟩, IndexedData7.key215, by decide, canonicalPose7_215, canonicalMatch7_215, indexedKeyDecode7_215⟩
  · exact ⟨⟨189, by decide⟩, IndexedData7.key216, by decide, canonicalPose7_216, canonicalMatch7_216, indexedKeyDecode7_216⟩
  · exact ⟨⟨190, by decide⟩, IndexedData7.key217, by decide, canonicalPose7_217, canonicalMatch7_217, indexedKeyDecode7_217⟩
  · exact ⟨⟨191, by decide⟩, IndexedData7.key218, by decide, canonicalPose7_218, canonicalMatch7_218, indexedKeyDecode7_218⟩
  · exact ⟨⟨192, by decide⟩, IndexedData7.key219, by decide, canonicalPose7_219, canonicalMatch7_219, indexedKeyDecode7_219⟩
  · exact ⟨⟨193, by decide⟩, IndexedData7.key220, by decide, canonicalPose7_220, canonicalMatch7_220, indexedKeyDecode7_220⟩
  · exact ⟨⟨193, by decide⟩, IndexedData7.key221, by decide, canonicalPose7_221, canonicalMatch7_221, indexedKeyDecode7_221⟩
  · exact ⟨⟨194, by decide⟩, IndexedData7.key222, by decide, canonicalPose7_222, canonicalMatch7_222, indexedKeyDecode7_222⟩
  · exact ⟨⟨195, by decide⟩, IndexedData7.key223, by decide, canonicalPose7_223, canonicalMatch7_223, indexedKeyDecode7_223⟩

#print axioms keys7Chunk6_aligned

end SparseMonotiles.Canonical
