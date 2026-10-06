module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk1

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk1_aligned : ∀ k ∈ keys7Chunk1,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨28, by decide⟩, IndexedData7.key32, by decide, canonicalPose7_32, canonicalMatch7_32, indexedKeyDecode7_32⟩
  · exact ⟨⟨29, by decide⟩, IndexedData7.key33, by decide, canonicalPose7_33, canonicalMatch7_33, indexedKeyDecode7_33⟩
  · exact ⟨⟨30, by decide⟩, IndexedData7.key34, by decide, canonicalPose7_34, canonicalMatch7_34, indexedKeyDecode7_34⟩
  · exact ⟨⟨31, by decide⟩, IndexedData7.key35, by decide, canonicalPose7_35, canonicalMatch7_35, indexedKeyDecode7_35⟩
  · exact ⟨⟨32, by decide⟩, IndexedData7.key36, by decide, canonicalPose7_36, canonicalMatch7_36, indexedKeyDecode7_36⟩
  · exact ⟨⟨32, by decide⟩, IndexedData7.key37, by decide, canonicalPose7_37, canonicalMatch7_37, indexedKeyDecode7_37⟩
  · exact ⟨⟨33, by decide⟩, IndexedData7.key38, by decide, canonicalPose7_38, canonicalMatch7_38, indexedKeyDecode7_38⟩
  · exact ⟨⟨34, by decide⟩, IndexedData7.key39, by decide, canonicalPose7_39, canonicalMatch7_39, indexedKeyDecode7_39⟩
  · exact ⟨⟨35, by decide⟩, IndexedData7.key40, by decide, canonicalPose7_40, canonicalMatch7_40, indexedKeyDecode7_40⟩
  · exact ⟨⟨36, by decide⟩, IndexedData7.key41, by decide, canonicalPose7_41, canonicalMatch7_41, indexedKeyDecode7_41⟩
  · exact ⟨⟨37, by decide⟩, IndexedData7.key42, by decide, canonicalPose7_42, canonicalMatch7_42, indexedKeyDecode7_42⟩
  · exact ⟨⟨38, by decide⟩, IndexedData7.key43, by decide, canonicalPose7_43, canonicalMatch7_43, indexedKeyDecode7_43⟩
  · exact ⟨⟨39, by decide⟩, IndexedData7.key44, by decide, canonicalPose7_44, canonicalMatch7_44, indexedKeyDecode7_44⟩
  · exact ⟨⟨40, by decide⟩, IndexedData7.key45, by decide, canonicalPose7_45, canonicalMatch7_45, indexedKeyDecode7_45⟩
  · exact ⟨⟨40, by decide⟩, IndexedData7.key46, by decide, canonicalPose7_46, canonicalMatch7_46, indexedKeyDecode7_46⟩
  · exact ⟨⟨41, by decide⟩, IndexedData7.key47, by decide, canonicalPose7_47, canonicalMatch7_47, indexedKeyDecode7_47⟩
  · exact ⟨⟨42, by decide⟩, IndexedData7.key48, by decide, canonicalPose7_48, canonicalMatch7_48, indexedKeyDecode7_48⟩
  · exact ⟨⟨43, by decide⟩, IndexedData7.key49, by decide, canonicalPose7_49, canonicalMatch7_49, indexedKeyDecode7_49⟩
  · exact ⟨⟨43, by decide⟩, IndexedData7.key50, by decide, canonicalPose7_50, canonicalMatch7_50, indexedKeyDecode7_50⟩
  · exact ⟨⟨44, by decide⟩, IndexedData7.key51, by decide, canonicalPose7_51, canonicalMatch7_51, indexedKeyDecode7_51⟩
  · exact ⟨⟨45, by decide⟩, IndexedData7.key52, by decide, canonicalPose7_52, canonicalMatch7_52, indexedKeyDecode7_52⟩
  · exact ⟨⟨46, by decide⟩, IndexedData7.key53, by decide, canonicalPose7_53, canonicalMatch7_53, indexedKeyDecode7_53⟩
  · exact ⟨⟨47, by decide⟩, IndexedData7.key54, by decide, canonicalPose7_54, canonicalMatch7_54, indexedKeyDecode7_54⟩
  · exact ⟨⟨48, by decide⟩, IndexedData7.key55, by decide, canonicalPose7_55, canonicalMatch7_55, indexedKeyDecode7_55⟩
  · exact ⟨⟨49, by decide⟩, IndexedData7.key56, by decide, canonicalPose7_56, canonicalMatch7_56, indexedKeyDecode7_56⟩
  · exact ⟨⟨50, by decide⟩, IndexedData7.key57, by decide, canonicalPose7_57, canonicalMatch7_57, indexedKeyDecode7_57⟩
  · exact ⟨⟨51, by decide⟩, IndexedData7.key58, by decide, canonicalPose7_58, canonicalMatch7_58, indexedKeyDecode7_58⟩
  · exact ⟨⟨52, by decide⟩, IndexedData7.key59, by decide, canonicalPose7_59, canonicalMatch7_59, indexedKeyDecode7_59⟩
  · exact ⟨⟨53, by decide⟩, IndexedData7.key60, by decide, canonicalPose7_60, canonicalMatch7_60, indexedKeyDecode7_60⟩
  · exact ⟨⟨54, by decide⟩, IndexedData7.key61, by decide, canonicalPose7_61, canonicalMatch7_61, indexedKeyDecode7_61⟩
  · exact ⟨⟨54, by decide⟩, IndexedData7.key62, by decide, canonicalPose7_62, canonicalMatch7_62, indexedKeyDecode7_62⟩
  · exact ⟨⟨55, by decide⟩, IndexedData7.key63, by decide, canonicalPose7_63, canonicalMatch7_63, indexedKeyDecode7_63⟩

#print axioms keys7Chunk1_aligned

end SparseMonotiles.Canonical
