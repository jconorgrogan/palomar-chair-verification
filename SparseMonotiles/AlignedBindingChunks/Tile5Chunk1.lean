module

public import SparseMonotiles.AtlasBindingChunks.Tile5Chunk1

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys5Chunk1_aligned : ∀ k ∈ keys5Chunk1,
    ∃ i : Fin 160, ∃ b ∈ IndexedData5.geometry.profile i, ∃ p : Pose 5,
      p.boxKey 19200 (referenceBox5 (!b.bump)) = b ∧ b.toKeyData 19200 = k := by
  intro k hk
  simp only [keys5Chunk1, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨20, by decide⟩, IndexedData5.key32, by decide, canonicalPose5_32, canonicalMatch5_32, indexedKeyDecode5_32⟩
  · exact ⟨⟨21, by decide⟩, IndexedData5.key33, by decide, canonicalPose5_33, canonicalMatch5_33, indexedKeyDecode5_33⟩
  · exact ⟨⟨22, by decide⟩, IndexedData5.key34, by decide, canonicalPose5_34, canonicalMatch5_34, indexedKeyDecode5_34⟩
  · exact ⟨⟨22, by decide⟩, IndexedData5.key35, by decide, canonicalPose5_35, canonicalMatch5_35, indexedKeyDecode5_35⟩
  · exact ⟨⟨22, by decide⟩, IndexedData5.key36, by decide, canonicalPose5_36, canonicalMatch5_36, indexedKeyDecode5_36⟩
  · exact ⟨⟨22, by decide⟩, IndexedData5.key37, by decide, canonicalPose5_37, canonicalMatch5_37, indexedKeyDecode5_37⟩
  · exact ⟨⟨23, by decide⟩, IndexedData5.key38, by decide, canonicalPose5_38, canonicalMatch5_38, indexedKeyDecode5_38⟩
  · exact ⟨⟨24, by decide⟩, IndexedData5.key39, by decide, canonicalPose5_39, canonicalMatch5_39, indexedKeyDecode5_39⟩
  · exact ⟨⟨25, by decide⟩, IndexedData5.key40, by decide, canonicalPose5_40, canonicalMatch5_40, indexedKeyDecode5_40⟩
  · exact ⟨⟨26, by decide⟩, IndexedData5.key41, by decide, canonicalPose5_41, canonicalMatch5_41, indexedKeyDecode5_41⟩
  · exact ⟨⟨27, by decide⟩, IndexedData5.key42, by decide, canonicalPose5_42, canonicalMatch5_42, indexedKeyDecode5_42⟩
  · exact ⟨⟨28, by decide⟩, IndexedData5.key43, by decide, canonicalPose5_43, canonicalMatch5_43, indexedKeyDecode5_43⟩
  · exact ⟨⟨28, by decide⟩, IndexedData5.key44, by decide, canonicalPose5_44, canonicalMatch5_44, indexedKeyDecode5_44⟩
  · exact ⟨⟨28, by decide⟩, IndexedData5.key45, by decide, canonicalPose5_45, canonicalMatch5_45, indexedKeyDecode5_45⟩
  · exact ⟨⟨28, by decide⟩, IndexedData5.key46, by decide, canonicalPose5_46, canonicalMatch5_46, indexedKeyDecode5_46⟩
  · exact ⟨⟨29, by decide⟩, IndexedData5.key47, by decide, canonicalPose5_47, canonicalMatch5_47, indexedKeyDecode5_47⟩
  · exact ⟨⟨30, by decide⟩, IndexedData5.key48, by decide, canonicalPose5_48, canonicalMatch5_48, indexedKeyDecode5_48⟩
  · exact ⟨⟨30, by decide⟩, IndexedData5.key49, by decide, canonicalPose5_49, canonicalMatch5_49, indexedKeyDecode5_49⟩
  · exact ⟨⟨30, by decide⟩, IndexedData5.key50, by decide, canonicalPose5_50, canonicalMatch5_50, indexedKeyDecode5_50⟩
  · exact ⟨⟨30, by decide⟩, IndexedData5.key51, by decide, canonicalPose5_51, canonicalMatch5_51, indexedKeyDecode5_51⟩
  · exact ⟨⟨31, by decide⟩, IndexedData5.key52, by decide, canonicalPose5_52, canonicalMatch5_52, indexedKeyDecode5_52⟩
  · exact ⟨⟨32, by decide⟩, IndexedData5.key53, by decide, canonicalPose5_53, canonicalMatch5_53, indexedKeyDecode5_53⟩
  · exact ⟨⟨33, by decide⟩, IndexedData5.key54, by decide, canonicalPose5_54, canonicalMatch5_54, indexedKeyDecode5_54⟩
  · exact ⟨⟨34, by decide⟩, IndexedData5.key55, by decide, canonicalPose5_55, canonicalMatch5_55, indexedKeyDecode5_55⟩
  · exact ⟨⟨35, by decide⟩, IndexedData5.key56, by decide, canonicalPose5_56, canonicalMatch5_56, indexedKeyDecode5_56⟩
  · exact ⟨⟨36, by decide⟩, IndexedData5.key57, by decide, canonicalPose5_57, canonicalMatch5_57, indexedKeyDecode5_57⟩
  · exact ⟨⟨37, by decide⟩, IndexedData5.key58, by decide, canonicalPose5_58, canonicalMatch5_58, indexedKeyDecode5_58⟩
  · exact ⟨⟨38, by decide⟩, IndexedData5.key59, by decide, canonicalPose5_59, canonicalMatch5_59, indexedKeyDecode5_59⟩
  · exact ⟨⟨38, by decide⟩, IndexedData5.key60, by decide, canonicalPose5_60, canonicalMatch5_60, indexedKeyDecode5_60⟩
  · exact ⟨⟨38, by decide⟩, IndexedData5.key61, by decide, canonicalPose5_61, canonicalMatch5_61, indexedKeyDecode5_61⟩
  · exact ⟨⟨38, by decide⟩, IndexedData5.key62, by decide, canonicalPose5_62, canonicalMatch5_62, indexedKeyDecode5_62⟩
  · exact ⟨⟨39, by decide⟩, IndexedData5.key63, by decide, canonicalPose5_63, canonicalMatch5_63, indexedKeyDecode5_63⟩

#print axioms keys5Chunk1_aligned

end SparseMonotiles.Canonical
