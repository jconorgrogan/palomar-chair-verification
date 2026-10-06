module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk8

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk8_aligned : ∀ k ∈ keys7Chunk8,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk8, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨224, by decide⟩, IndexedData7.key256, by decide, canonicalPose7_256, canonicalMatch7_256, indexedKeyDecode7_256⟩
  · exact ⟨⟨225, by decide⟩, IndexedData7.key257, by decide, canonicalPose7_257, canonicalMatch7_257, indexedKeyDecode7_257⟩
  · exact ⟨⟨225, by decide⟩, IndexedData7.key258, by decide, canonicalPose7_258, canonicalMatch7_258, indexedKeyDecode7_258⟩
  · exact ⟨⟨226, by decide⟩, IndexedData7.key259, by decide, canonicalPose7_259, canonicalMatch7_259, indexedKeyDecode7_259⟩
  · exact ⟨⟨227, by decide⟩, IndexedData7.key260, by decide, canonicalPose7_260, canonicalMatch7_260, indexedKeyDecode7_260⟩
  · exact ⟨⟨228, by decide⟩, IndexedData7.key261, by decide, canonicalPose7_261, canonicalMatch7_261, indexedKeyDecode7_261⟩
  · exact ⟨⟨229, by decide⟩, IndexedData7.key262, by decide, canonicalPose7_262, canonicalMatch7_262, indexedKeyDecode7_262⟩
  · exact ⟨⟨230, by decide⟩, IndexedData7.key263, by decide, canonicalPose7_263, canonicalMatch7_263, indexedKeyDecode7_263⟩
  · exact ⟨⟨231, by decide⟩, IndexedData7.key264, by decide, canonicalPose7_264, canonicalMatch7_264, indexedKeyDecode7_264⟩
  · exact ⟨⟨231, by decide⟩, IndexedData7.key265, by decide, canonicalPose7_265, canonicalMatch7_265, indexedKeyDecode7_265⟩
  · exact ⟨⟨232, by decide⟩, IndexedData7.key266, by decide, canonicalPose7_266, canonicalMatch7_266, indexedKeyDecode7_266⟩
  · exact ⟨⟨233, by decide⟩, IndexedData7.key267, by decide, canonicalPose7_267, canonicalMatch7_267, indexedKeyDecode7_267⟩
  · exact ⟨⟨234, by decide⟩, IndexedData7.key268, by decide, canonicalPose7_268, canonicalMatch7_268, indexedKeyDecode7_268⟩
  · exact ⟨⟨235, by decide⟩, IndexedData7.key269, by decide, canonicalPose7_269, canonicalMatch7_269, indexedKeyDecode7_269⟩
  · exact ⟨⟨236, by decide⟩, IndexedData7.key270, by decide, canonicalPose7_270, canonicalMatch7_270, indexedKeyDecode7_270⟩
  · exact ⟨⟨237, by decide⟩, IndexedData7.key271, by decide, canonicalPose7_271, canonicalMatch7_271, indexedKeyDecode7_271⟩
  · exact ⟨⟨238, by decide⟩, IndexedData7.key272, by decide, canonicalPose7_272, canonicalMatch7_272, indexedKeyDecode7_272⟩
  · exact ⟨⟨239, by decide⟩, IndexedData7.key273, by decide, canonicalPose7_273, canonicalMatch7_273, indexedKeyDecode7_273⟩
  · exact ⟨⟨240, by decide⟩, IndexedData7.key274, by decide, canonicalPose7_274, canonicalMatch7_274, indexedKeyDecode7_274⟩
  · exact ⟨⟨241, by decide⟩, IndexedData7.key275, by decide, canonicalPose7_275, canonicalMatch7_275, indexedKeyDecode7_275⟩
  · exact ⟨⟨241, by decide⟩, IndexedData7.key276, by decide, canonicalPose7_276, canonicalMatch7_276, indexedKeyDecode7_276⟩
  · exact ⟨⟨242, by decide⟩, IndexedData7.key277, by decide, canonicalPose7_277, canonicalMatch7_277, indexedKeyDecode7_277⟩
  · exact ⟨⟨243, by decide⟩, IndexedData7.key278, by decide, canonicalPose7_278, canonicalMatch7_278, indexedKeyDecode7_278⟩
  · exact ⟨⟨244, by decide⟩, IndexedData7.key279, by decide, canonicalPose7_279, canonicalMatch7_279, indexedKeyDecode7_279⟩
  · exact ⟨⟨245, by decide⟩, IndexedData7.key280, by decide, canonicalPose7_280, canonicalMatch7_280, indexedKeyDecode7_280⟩
  · exact ⟨⟨246, by decide⟩, IndexedData7.key281, by decide, canonicalPose7_281, canonicalMatch7_281, indexedKeyDecode7_281⟩
  · exact ⟨⟨247, by decide⟩, IndexedData7.key282, by decide, canonicalPose7_282, canonicalMatch7_282, indexedKeyDecode7_282⟩
  · exact ⟨⟨248, by decide⟩, IndexedData7.key283, by decide, canonicalPose7_283, canonicalMatch7_283, indexedKeyDecode7_283⟩
  · exact ⟨⟨249, by decide⟩, IndexedData7.key284, by decide, canonicalPose7_284, canonicalMatch7_284, indexedKeyDecode7_284⟩
  · exact ⟨⟨249, by decide⟩, IndexedData7.key285, by decide, canonicalPose7_285, canonicalMatch7_285, indexedKeyDecode7_285⟩
  · exact ⟨⟨250, by decide⟩, IndexedData7.key286, by decide, canonicalPose7_286, canonicalMatch7_286, indexedKeyDecode7_286⟩
  · exact ⟨⟨251, by decide⟩, IndexedData7.key287, by decide, canonicalPose7_287, canonicalMatch7_287, indexedKeyDecode7_287⟩

#print axioms keys7Chunk8_aligned

end SparseMonotiles.Canonical
