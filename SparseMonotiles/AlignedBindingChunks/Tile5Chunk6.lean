module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk6

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk6_aligned : ∀ k ∈ keys5Chunk6,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk6, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨117, by decide⟩, IndexedData5.key192, by decide, canonicalPose5_192, canonicalMatch5_192, indexedKeyDecode5_192⟩
  · exact ⟨⟨118, by decide⟩, IndexedData5.key193, by decide, canonicalPose5_193, canonicalMatch5_193, indexedKeyDecode5_193⟩
  · exact ⟨⟨119, by decide⟩, IndexedData5.key194, by decide, canonicalPose5_194, canonicalMatch5_194, indexedKeyDecode5_194⟩
  · exact ⟨⟨120, by decide⟩, IndexedData5.key195, by decide, canonicalPose5_195, canonicalMatch5_195, indexedKeyDecode5_195⟩
  · exact ⟨⟨121, by decide⟩, IndexedData5.key196, by decide, canonicalPose5_196, canonicalMatch5_196, indexedKeyDecode5_196⟩
  · exact ⟨⟨122, by decide⟩, IndexedData5.key197, by decide, canonicalPose5_197, canonicalMatch5_197, indexedKeyDecode5_197⟩
  · exact ⟨⟨123, by decide⟩, IndexedData5.key198, by decide, canonicalPose5_198, canonicalMatch5_198, indexedKeyDecode5_198⟩
  · exact ⟨⟨124, by decide⟩, IndexedData5.key199, by decide, canonicalPose5_199, canonicalMatch5_199, indexedKeyDecode5_199⟩
  · exact ⟨⟨125, by decide⟩, IndexedData5.key200, by decide, canonicalPose5_200, canonicalMatch5_200, indexedKeyDecode5_200⟩
  · exact ⟨⟨125, by decide⟩, IndexedData5.key201, by decide, canonicalPose5_201, canonicalMatch5_201, indexedKeyDecode5_201⟩
  · exact ⟨⟨125, by decide⟩, IndexedData5.key202, by decide, canonicalPose5_202, canonicalMatch5_202, indexedKeyDecode5_202⟩
  · exact ⟨⟨125, by decide⟩, IndexedData5.key203, by decide, canonicalPose5_203, canonicalMatch5_203, indexedKeyDecode5_203⟩
  · exact ⟨⟨126, by decide⟩, IndexedData5.key204, by decide, canonicalPose5_204, canonicalMatch5_204, indexedKeyDecode5_204⟩
  · exact ⟨⟨127, by decide⟩, IndexedData5.key205, by decide, canonicalPose5_205, canonicalMatch5_205, indexedKeyDecode5_205⟩
  · exact ⟨⟨127, by decide⟩, IndexedData5.key206, by decide, canonicalPose5_206, canonicalMatch5_206, indexedKeyDecode5_206⟩
  · exact ⟨⟨127, by decide⟩, IndexedData5.key207, by decide, canonicalPose5_207, canonicalMatch5_207, indexedKeyDecode5_207⟩
  · exact ⟨⟨127, by decide⟩, IndexedData5.key208, by decide, canonicalPose5_208, canonicalMatch5_208, indexedKeyDecode5_208⟩
  · exact ⟨⟨128, by decide⟩, IndexedData5.key209, by decide, canonicalPose5_209, canonicalMatch5_209, indexedKeyDecode5_209⟩
  · exact ⟨⟨129, by decide⟩, IndexedData5.key210, by decide, canonicalPose5_210, canonicalMatch5_210, indexedKeyDecode5_210⟩
  · exact ⟨⟨130, by decide⟩, IndexedData5.key211, by decide, canonicalPose5_211, canonicalMatch5_211, indexedKeyDecode5_211⟩
  · exact ⟨⟨131, by decide⟩, IndexedData5.key212, by decide, canonicalPose5_212, canonicalMatch5_212, indexedKeyDecode5_212⟩
  · exact ⟨⟨132, by decide⟩, IndexedData5.key213, by decide, canonicalPose5_213, canonicalMatch5_213, indexedKeyDecode5_213⟩
  · exact ⟨⟨133, by decide⟩, IndexedData5.key214, by decide, canonicalPose5_214, canonicalMatch5_214, indexedKeyDecode5_214⟩
  · exact ⟨⟨134, by decide⟩, IndexedData5.key215, by decide, canonicalPose5_215, canonicalMatch5_215, indexedKeyDecode5_215⟩
  · exact ⟨⟨135, by decide⟩, IndexedData5.key216, by decide, canonicalPose5_216, canonicalMatch5_216, indexedKeyDecode5_216⟩
  · exact ⟨⟨135, by decide⟩, IndexedData5.key217, by decide, canonicalPose5_217, canonicalMatch5_217, indexedKeyDecode5_217⟩
  · exact ⟨⟨135, by decide⟩, IndexedData5.key218, by decide, canonicalPose5_218, canonicalMatch5_218, indexedKeyDecode5_218⟩
  · exact ⟨⟨135, by decide⟩, IndexedData5.key219, by decide, canonicalPose5_219, canonicalMatch5_219, indexedKeyDecode5_219⟩
  · exact ⟨⟨136, by decide⟩, IndexedData5.key220, by decide, canonicalPose5_220, canonicalMatch5_220, indexedKeyDecode5_220⟩
  · exact ⟨⟨137, by decide⟩, IndexedData5.key221, by decide, canonicalPose5_221, canonicalMatch5_221, indexedKeyDecode5_221⟩
  · exact ⟨⟨138, by decide⟩, IndexedData5.key222, by decide, canonicalPose5_222, canonicalMatch5_222, indexedKeyDecode5_222⟩
  · exact ⟨⟨139, by decide⟩, IndexedData5.key223, by decide, canonicalPose5_223, canonicalMatch5_223, indexedKeyDecode5_223⟩

#print axioms keys5Chunk6_aligned

end SparseMonotiles.Canonical
