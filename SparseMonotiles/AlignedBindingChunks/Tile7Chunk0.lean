module

public import SparseMonotiles.AtlasBindingChunks.Tile7Chunk0

@[expose] public section

namespace SparseMonotiles.Canonical

open SparseMonotiles.Contact

theorem keys7Chunk0_aligned : ∀ k ∈ keys7Chunk0,
    ∃ i : Fin 896, ∃ b ∈ IndexedData7.geometry.profile i, ∃ p : Pose 7,
      p.boxKey 188160 (referenceBox7 (!b.bump)) = b ∧ b.toKeyData 188160 = k := by
  intro k hk
  simp only [keys7Chunk0, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨⟨0, by decide⟩, IndexedData7.key0, by decide, canonicalPose7_0, canonicalMatch7_0, indexedKeyDecode7_0⟩
  · exact ⟨⟨0, by decide⟩, IndexedData7.key1, by decide, canonicalPose7_1, canonicalMatch7_1, indexedKeyDecode7_1⟩
  · exact ⟨⟨1, by decide⟩, IndexedData7.key2, by decide, canonicalPose7_2, canonicalMatch7_2, indexedKeyDecode7_2⟩
  · exact ⟨⟨2, by decide⟩, IndexedData7.key3, by decide, canonicalPose7_3, canonicalMatch7_3, indexedKeyDecode7_3⟩
  · exact ⟨⟨3, by decide⟩, IndexedData7.key4, by decide, canonicalPose7_4, canonicalMatch7_4, indexedKeyDecode7_4⟩
  · exact ⟨⟨4, by decide⟩, IndexedData7.key5, by decide, canonicalPose7_5, canonicalMatch7_5, indexedKeyDecode7_5⟩
  · exact ⟨⟨5, by decide⟩, IndexedData7.key6, by decide, canonicalPose7_6, canonicalMatch7_6, indexedKeyDecode7_6⟩
  · exact ⟨⟨6, by decide⟩, IndexedData7.key7, by decide, canonicalPose7_7, canonicalMatch7_7, indexedKeyDecode7_7⟩
  · exact ⟨⟨7, by decide⟩, IndexedData7.key8, by decide, canonicalPose7_8, canonicalMatch7_8, indexedKeyDecode7_8⟩
  · exact ⟨⟨8, by decide⟩, IndexedData7.key9, by decide, canonicalPose7_9, canonicalMatch7_9, indexedKeyDecode7_9⟩
  · exact ⟨⟨9, by decide⟩, IndexedData7.key10, by decide, canonicalPose7_10, canonicalMatch7_10, indexedKeyDecode7_10⟩
  · exact ⟨⟨10, by decide⟩, IndexedData7.key11, by decide, canonicalPose7_11, canonicalMatch7_11, indexedKeyDecode7_11⟩
  · exact ⟨⟨11, by decide⟩, IndexedData7.key12, by decide, canonicalPose7_12, canonicalMatch7_12, indexedKeyDecode7_12⟩
  · exact ⟨⟨12, by decide⟩, IndexedData7.key13, by decide, canonicalPose7_13, canonicalMatch7_13, indexedKeyDecode7_13⟩
  · exact ⟨⟨13, by decide⟩, IndexedData7.key14, by decide, canonicalPose7_14, canonicalMatch7_14, indexedKeyDecode7_14⟩
  · exact ⟨⟨13, by decide⟩, IndexedData7.key15, by decide, canonicalPose7_15, canonicalMatch7_15, indexedKeyDecode7_15⟩
  · exact ⟨⟨14, by decide⟩, IndexedData7.key16, by decide, canonicalPose7_16, canonicalMatch7_16, indexedKeyDecode7_16⟩
  · exact ⟨⟨15, by decide⟩, IndexedData7.key17, by decide, canonicalPose7_17, canonicalMatch7_17, indexedKeyDecode7_17⟩
  · exact ⟨⟨16, by decide⟩, IndexedData7.key18, by decide, canonicalPose7_18, canonicalMatch7_18, indexedKeyDecode7_18⟩
  · exact ⟨⟨17, by decide⟩, IndexedData7.key19, by decide, canonicalPose7_19, canonicalMatch7_19, indexedKeyDecode7_19⟩
  · exact ⟨⟨18, by decide⟩, IndexedData7.key20, by decide, canonicalPose7_20, canonicalMatch7_20, indexedKeyDecode7_20⟩
  · exact ⟨⟨19, by decide⟩, IndexedData7.key21, by decide, canonicalPose7_21, canonicalMatch7_21, indexedKeyDecode7_21⟩
  · exact ⟨⟨19, by decide⟩, IndexedData7.key22, by decide, canonicalPose7_22, canonicalMatch7_22, indexedKeyDecode7_22⟩
  · exact ⟨⟨20, by decide⟩, IndexedData7.key23, by decide, canonicalPose7_23, canonicalMatch7_23, indexedKeyDecode7_23⟩
  · exact ⟨⟨21, by decide⟩, IndexedData7.key24, by decide, canonicalPose7_24, canonicalMatch7_24, indexedKeyDecode7_24⟩
  · exact ⟨⟨22, by decide⟩, IndexedData7.key25, by decide, canonicalPose7_25, canonicalMatch7_25, indexedKeyDecode7_25⟩
  · exact ⟨⟨23, by decide⟩, IndexedData7.key26, by decide, canonicalPose7_26, canonicalMatch7_26, indexedKeyDecode7_26⟩
  · exact ⟨⟨23, by decide⟩, IndexedData7.key27, by decide, canonicalPose7_27, canonicalMatch7_27, indexedKeyDecode7_27⟩
  · exact ⟨⟨24, by decide⟩, IndexedData7.key28, by decide, canonicalPose7_28, canonicalMatch7_28, indexedKeyDecode7_28⟩
  · exact ⟨⟨25, by decide⟩, IndexedData7.key29, by decide, canonicalPose7_29, canonicalMatch7_29, indexedKeyDecode7_29⟩
  · exact ⟨⟨26, by decide⟩, IndexedData7.key30, by decide, canonicalPose7_30, canonicalMatch7_30, indexedKeyDecode7_30⟩
  · exact ⟨⟨27, by decide⟩, IndexedData7.key31, by decide, canonicalPose7_31, canonicalMatch7_31, indexedKeyDecode7_31⟩

#print axioms keys7Chunk0_aligned

end SparseMonotiles.Canonical
