module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk7

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk7_aligned : ∀ k ∈ keys5Chunk7,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk7, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨139, by decide⟩, IndexedData5.key224, by decide, canonicalPose5_224, canonicalMatch5_224, indexedKeyDecode5_224⟩
  · exact ⟨⟨139, by decide⟩, IndexedData5.key225, by decide, canonicalPose5_225, canonicalMatch5_225, indexedKeyDecode5_225⟩
  · exact ⟨⟨139, by decide⟩, IndexedData5.key226, by decide, canonicalPose5_226, canonicalMatch5_226, indexedKeyDecode5_226⟩
  · exact ⟨⟨140, by decide⟩, IndexedData5.key227, by decide, canonicalPose5_227, canonicalMatch5_227, indexedKeyDecode5_227⟩
  · exact ⟨⟨141, by decide⟩, IndexedData5.key228, by decide, canonicalPose5_228, canonicalMatch5_228, indexedKeyDecode5_228⟩
  · exact ⟨⟨142, by decide⟩, IndexedData5.key229, by decide, canonicalPose5_229, canonicalMatch5_229, indexedKeyDecode5_229⟩
  · exact ⟨⟨143, by decide⟩, IndexedData5.key230, by decide, canonicalPose5_230, canonicalMatch5_230, indexedKeyDecode5_230⟩
  · exact ⟨⟨144, by decide⟩, IndexedData5.key231, by decide, canonicalPose5_231, canonicalMatch5_231, indexedKeyDecode5_231⟩
  · exact ⟨⟨144, by decide⟩, IndexedData5.key232, by decide, canonicalPose5_232, canonicalMatch5_232, indexedKeyDecode5_232⟩
  · exact ⟨⟨144, by decide⟩, IndexedData5.key233, by decide, canonicalPose5_233, canonicalMatch5_233, indexedKeyDecode5_233⟩
  · exact ⟨⟨144, by decide⟩, IndexedData5.key234, by decide, canonicalPose5_234, canonicalMatch5_234, indexedKeyDecode5_234⟩
  · exact ⟨⟨145, by decide⟩, IndexedData5.key235, by decide, canonicalPose5_235, canonicalMatch5_235, indexedKeyDecode5_235⟩
  · exact ⟨⟨146, by decide⟩, IndexedData5.key236, by decide, canonicalPose5_236, canonicalMatch5_236, indexedKeyDecode5_236⟩
  · exact ⟨⟨147, by decide⟩, IndexedData5.key237, by decide, canonicalPose5_237, canonicalMatch5_237, indexedKeyDecode5_237⟩
  · exact ⟨⟨148, by decide⟩, IndexedData5.key238, by decide, canonicalPose5_238, canonicalMatch5_238, indexedKeyDecode5_238⟩
  · exact ⟨⟨149, by decide⟩, IndexedData5.key239, by decide, canonicalPose5_239, canonicalMatch5_239, indexedKeyDecode5_239⟩
  · exact ⟨⟨150, by decide⟩, IndexedData5.key240, by decide, canonicalPose5_240, canonicalMatch5_240, indexedKeyDecode5_240⟩
  · exact ⟨⟨151, by decide⟩, IndexedData5.key241, by decide, canonicalPose5_241, canonicalMatch5_241, indexedKeyDecode5_241⟩
  · exact ⟨⟨151, by decide⟩, IndexedData5.key242, by decide, canonicalPose5_242, canonicalMatch5_242, indexedKeyDecode5_242⟩
  · exact ⟨⟨151, by decide⟩, IndexedData5.key243, by decide, canonicalPose5_243, canonicalMatch5_243, indexedKeyDecode5_243⟩
  · exact ⟨⟨151, by decide⟩, IndexedData5.key244, by decide, canonicalPose5_244, canonicalMatch5_244, indexedKeyDecode5_244⟩
  · exact ⟨⟨152, by decide⟩, IndexedData5.key245, by decide, canonicalPose5_245, canonicalMatch5_245, indexedKeyDecode5_245⟩
  · exact ⟨⟨153, by decide⟩, IndexedData5.key246, by decide, canonicalPose5_246, canonicalMatch5_246, indexedKeyDecode5_246⟩
  · exact ⟨⟨154, by decide⟩, IndexedData5.key247, by decide, canonicalPose5_247, canonicalMatch5_247, indexedKeyDecode5_247⟩
  · exact ⟨⟨155, by decide⟩, IndexedData5.key248, by decide, canonicalPose5_248, canonicalMatch5_248, indexedKeyDecode5_248⟩
  · exact ⟨⟨156, by decide⟩, IndexedData5.key249, by decide, canonicalPose5_249, canonicalMatch5_249, indexedKeyDecode5_249⟩
  · exact ⟨⟨157, by decide⟩, IndexedData5.key250, by decide, canonicalPose5_250, canonicalMatch5_250, indexedKeyDecode5_250⟩
  · exact ⟨⟨158, by decide⟩, IndexedData5.key251, by decide, canonicalPose5_251, canonicalMatch5_251, indexedKeyDecode5_251⟩
  · exact ⟨⟨158, by decide⟩, IndexedData5.key252, by decide, canonicalPose5_252, canonicalMatch5_252, indexedKeyDecode5_252⟩
  · exact ⟨⟨158, by decide⟩, IndexedData5.key253, by decide, canonicalPose5_253, canonicalMatch5_253, indexedKeyDecode5_253⟩
  · exact ⟨⟨158, by decide⟩, IndexedData5.key254, by decide, canonicalPose5_254, canonicalMatch5_254, indexedKeyDecode5_254⟩
  · exact ⟨⟨159, by decide⟩, IndexedData5.key255, by decide, canonicalPose5_255, canonicalMatch5_255, indexedKeyDecode5_255⟩

#print axioms keys5Chunk7_aligned

end SparseMonotiles.Canonical
