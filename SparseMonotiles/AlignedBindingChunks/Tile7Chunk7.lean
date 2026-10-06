module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk7

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk7_aligned : ∀ k ∈ keys7Chunk7,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk7, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨196, by decide⟩, IndexedData7.key224, by decide, canonicalPose7_224, canonicalMatch7_224, indexedKeyDecode7_224⟩
  · exact ⟨⟨197, by decide⟩, IndexedData7.key225, by decide, canonicalPose7_225, canonicalMatch7_225, indexedKeyDecode7_225⟩
  · exact ⟨⟨198, by decide⟩, IndexedData7.key226, by decide, canonicalPose7_226, canonicalMatch7_226, indexedKeyDecode7_226⟩
  · exact ⟨⟨199, by decide⟩, IndexedData7.key227, by decide, canonicalPose7_227, canonicalMatch7_227, indexedKeyDecode7_227⟩
  · exact ⟨⟨199, by decide⟩, IndexedData7.key228, by decide, canonicalPose7_228, canonicalMatch7_228, indexedKeyDecode7_228⟩
  · exact ⟨⟨200, by decide⟩, IndexedData7.key229, by decide, canonicalPose7_229, canonicalMatch7_229, indexedKeyDecode7_229⟩
  · exact ⟨⟨201, by decide⟩, IndexedData7.key230, by decide, canonicalPose7_230, canonicalMatch7_230, indexedKeyDecode7_230⟩
  · exact ⟨⟨202, by decide⟩, IndexedData7.key231, by decide, canonicalPose7_231, canonicalMatch7_231, indexedKeyDecode7_231⟩
  · exact ⟨⟨203, by decide⟩, IndexedData7.key232, by decide, canonicalPose7_232, canonicalMatch7_232, indexedKeyDecode7_232⟩
  · exact ⟨⟨204, by decide⟩, IndexedData7.key233, by decide, canonicalPose7_233, canonicalMatch7_233, indexedKeyDecode7_233⟩
  · exact ⟨⟨205, by decide⟩, IndexedData7.key234, by decide, canonicalPose7_234, canonicalMatch7_234, indexedKeyDecode7_234⟩
  · exact ⟨⟨205, by decide⟩, IndexedData7.key235, by decide, canonicalPose7_235, canonicalMatch7_235, indexedKeyDecode7_235⟩
  · exact ⟨⟨206, by decide⟩, IndexedData7.key236, by decide, canonicalPose7_236, canonicalMatch7_236, indexedKeyDecode7_236⟩
  · exact ⟨⟨207, by decide⟩, IndexedData7.key237, by decide, canonicalPose7_237, canonicalMatch7_237, indexedKeyDecode7_237⟩
  · exact ⟨⟨208, by decide⟩, IndexedData7.key238, by decide, canonicalPose7_238, canonicalMatch7_238, indexedKeyDecode7_238⟩
  · exact ⟨⟨209, by decide⟩, IndexedData7.key239, by decide, canonicalPose7_239, canonicalMatch7_239, indexedKeyDecode7_239⟩
  · exact ⟨⟨210, by decide⟩, IndexedData7.key240, by decide, canonicalPose7_240, canonicalMatch7_240, indexedKeyDecode7_240⟩
  · exact ⟨⟨210, by decide⟩, IndexedData7.key241, by decide, canonicalPose7_241, canonicalMatch7_241, indexedKeyDecode7_241⟩
  · exact ⟨⟨211, by decide⟩, IndexedData7.key242, by decide, canonicalPose7_242, canonicalMatch7_242, indexedKeyDecode7_242⟩
  · exact ⟨⟨212, by decide⟩, IndexedData7.key243, by decide, canonicalPose7_243, canonicalMatch7_243, indexedKeyDecode7_243⟩
  · exact ⟨⟨213, by decide⟩, IndexedData7.key244, by decide, canonicalPose7_244, canonicalMatch7_244, indexedKeyDecode7_244⟩
  · exact ⟨⟨214, by decide⟩, IndexedData7.key245, by decide, canonicalPose7_245, canonicalMatch7_245, indexedKeyDecode7_245⟩
  · exact ⟨⟨215, by decide⟩, IndexedData7.key246, by decide, canonicalPose7_246, canonicalMatch7_246, indexedKeyDecode7_246⟩
  · exact ⟨⟨216, by decide⟩, IndexedData7.key247, by decide, canonicalPose7_247, canonicalMatch7_247, indexedKeyDecode7_247⟩
  · exact ⟨⟨217, by decide⟩, IndexedData7.key248, by decide, canonicalPose7_248, canonicalMatch7_248, indexedKeyDecode7_248⟩
  · exact ⟨⟨218, by decide⟩, IndexedData7.key249, by decide, canonicalPose7_249, canonicalMatch7_249, indexedKeyDecode7_249⟩
  · exact ⟨⟨219, by decide⟩, IndexedData7.key250, by decide, canonicalPose7_250, canonicalMatch7_250, indexedKeyDecode7_250⟩
  · exact ⟨⟨220, by decide⟩, IndexedData7.key251, by decide, canonicalPose7_251, canonicalMatch7_251, indexedKeyDecode7_251⟩
  · exact ⟨⟨221, by decide⟩, IndexedData7.key252, by decide, canonicalPose7_252, canonicalMatch7_252, indexedKeyDecode7_252⟩
  · exact ⟨⟨221, by decide⟩, IndexedData7.key253, by decide, canonicalPose7_253, canonicalMatch7_253, indexedKeyDecode7_253⟩
  · exact ⟨⟨222, by decide⟩, IndexedData7.key254, by decide, canonicalPose7_254, canonicalMatch7_254, indexedKeyDecode7_254⟩
  · exact ⟨⟨223, by decide⟩, IndexedData7.key255, by decide, canonicalPose7_255, canonicalMatch7_255, indexedKeyDecode7_255⟩

#print axioms keys7Chunk7_aligned

end SparseMonotiles.Canonical
